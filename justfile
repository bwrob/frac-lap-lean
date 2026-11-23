export PATH := env_var("HOME") + "/.elan/bin:" + env_var("HOME") + "/.local/bin:" + env_var("PATH")

default: verify-all

# Download precompiled Mathlib .olean cache (run before `just build` after updates)
cache:
    lake exe cache get

# Compile the Lean 4 project
build:
    lake build

# Run Lean 4 Batteries/Mathlib linters across FracLap
lint-lean:
    lake lint

# Audit all FracLap.* declarations for disallowed axioms (including sorryAx)
check-axioms:
    lake env lean --run scripts/check_axioms.lean

# Audit compiled FracLap declarations for uninstantiated structures, tautologies, and abstract gaps
audit-gaps *args="":
    lake env lean --run scripts/audit_spec_gaps.lean {{ args }}

# Run the spec-gap audit in strict zero-gap mode (used by verification gates)
audit-gaps-strict:
    lake env lean --run scripts/audit_spec_gaps.lean --strict

# Verify every module under FracLap/ is imported in FracLap.lean
check-imports:
    uv run python scripts/check_imports.py

# Run a scratch Lean file against the up-to-date library (builds the root target first so that
# `import FracLap` never sees stale oleans)
scratch file:
    lake build FracLap
    lake env lean {{ file }}

# Search Mathlib and the Lean core sources for a declaration name or pattern (API drift helper)
lean-grep pattern:
    @grep -rn --include='*.lean' -E "{{ pattern }}" .lake/packages/mathlib/Mathlib \
        "$(lake env printenv LEAN_SYSROOT)/src/lean/Lean" | head -40

# Fast style pre-check (line length, `show`, deprecated names, docstrings) without building
lint-quick *files:
    uv run python scripts/lean_style_check.py {{ files }}

# Scaffold FracLap/<Path>.lean + blueprint chapter + test module and register all of them
new-module path title="":
    uv run python scripts/new_module.py {{ path }} {{ if title != "" { "--title '" + title + "'" } else { "" } }}

# Replay compiled FracLap/**/*.lean modules through the Lean kernel checker
check-kernel:
    @find FracLap -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g' | \
        xargs -P "$(nproc)" -I{} lake env leanchecker {}

# Replay compiled FracLap/**/*.lean modules into a completely fresh kernel environment
check-kernel-fresh:
    @set -e; for f in $(find FracLap -name '*.lean' | sort); do \
        mod=$(echo "${f%.lean}" | tr '/' '.'); \
        lake env leanchecker --fresh "$mod"; \
    done

# Check FracLap inside a bwrap sandbox via leanexport and the default kernel
check-external:
    lake check

# Check FracLap inside bwrap across all 6 bundled kernels (including con-leche and nanoda)
check-paranoid:
    lake check --paranoid

# Export compiled FracLap declarations to an NDJSON kernel stream
export-ndjson out=".lake/build/fraclap.ndjson":
    @mkdir -p "$(dirname "{{ out }}")"
    lake env leanexport FracLap > "{{ out }}"

# Verify an exported FracLap NDJSON stream using the formally verified con-leche checker
check-con-leche file=".lake/build/fraclap.ndjson":
    @if [ ! -f "{{ file }}" ]; then just export-ndjson "{{ file }}"; fi
    lake env con-leche --verified --progress=10000 "{{ file }}"

# Judge FracLap's flagship theorems against comparator.json inside a bwrap sandbox
check-comparator *args="":
    lake comparator --config comparator.json {{ args }}

# Judge comparator.json across all 6 bundled external kernels
check-comparator-paranoid:
    lake comparator --config comparator.json --paranoid

# Suggest minimal imports across FracLap modules
shake:
    lake shake

# Compile anti-vacuity and sanity-check examples in FracLapTest
test-lean:
    lake build FracLapTest

# Display Lean formalization and blueprint progress summary
status *args="":
    uv run python scripts/formalization_status.py {{ args }}

# Lint blueprint LaTeX sources with chktex
lint-tex:
    find blueprint/src -name '*.tex' | sort | xargs chktex -l .chktexrc -q -e all -n 1 -n 3 -n 8 -n 22 -n 24 -n 36 -n 46

# Build HTML blueprint, PDF blueprint, Lean project, and check declarations
blueprint:
    leanblueprint all

# Build only HTML blueprint and dependency graph
blueprint-web:
    leanblueprint web

# Build only printable PDF blueprint
blueprint-pdf:
    leanblueprint pdf

# Verify every \lean{...} tag in blueprint/ matches compiled Lean declarations
blueprint-check:
    leanblueprint checkdecls

# Serve compiled blueprint locally on http://localhost:8000
blueprint-serve:
    leanblueprint serve

# Scaffold a new workspace skill in .agents/skills/
new-skill name desc="":
    uv run python .agents/skills/skill-creator/scripts/scaffold_skill.py {{ name }} {{ if desc != "" { "--description \"" + desc + "\"" } else { "" } }}

# Lint, typecheck, and check cognitive complexity of Python helpers and tests
lint-py:
    uv run ruff check scripts/ tests/ .agents/skills/
    uv run ruff format --check scripts/ tests/ .agents/skills/
    uv run pyrefly check
    uv run complexipy

# Auto-format Python scripts and tests
format-py:
    uv run ruff format scripts/ tests/ .agents/skills/
    uv run ruff check --fix scripts/ tests/ .agents/skills/

# Run Python unit and integration tests
test:
    uv run pytest -v

# Run all Lean, Blueprint, LaTeX, Resource Parity, and Python checks
verify-serial: lint-quick build lint-lean test-lean check-imports check-axioms audit-gaps-strict check-kernel blueprint-pdf blueprint-web blueprint-check lint-tex lint-py test

# Same checks as `verify-serial`, but the independent stages run concurrently after the build.
# Logs of each stage are kept in `.verify_logs/`; the logs of failing stages are printed.
verify-all:
    #!/usr/bin/env bash
    set -uo pipefail
    just lint-quick && just build && just test-lean || exit 1
    mkdir -p .verify_logs
    rm -f .verify_logs/*.log
    declare -A pids
    run() { local name=$1; shift; ( "$@" ) > ".verify_logs/$name.log" 2>&1 & pids[$name]=$!; }
    run lean-lint just lint-lean
    run axioms just check-axioms
    run gaps just audit-gaps-strict
    run kernel just check-kernel
    run blueprint bash -c 'just blueprint-pdf && just blueprint-web && just blueprint-check && just lint-tex'
    run python bash -c 'just check-imports && just lint-py && just test'
    status=0
    failed=()
    for name in "${!pids[@]}"; do
        if wait "${pids[$name]}"; then
            echo "ok    $name"
        else
            echo "FAIL  $name"; status=1; failed+=("$name")
        fi
    done
    for n in "${failed[@]}"; do
        echo "=== $n ==="; tail -40 ".verify_logs/$n.log"
    done
    exit $status

# Run all prek pre-commit hooks across all files
check:
    uv run prek run --all-files

# Run prek pre-push hooks (fast incremental build, test, imports, axioms & gap audit)
check-push:
    uv run prek run --all-files --hook-stage pre-push

# Run on-request manual prek hooks (full verify-all and paranoid multi-kernel/comparator suite)
check-manual *args="":
    uv run prek run --all-files --hook-stage manual {{ args }}

# Install prek pre-commit and pre-push Git hooks
setup-hooks:
    uv run prek install

# Regenerate docs/knowledge/ (blueprint + Lean pages) and the generated nav block of zensical.toml
docs-gen:
    uv run python scripts/gen_docs.py

# Strict build of the documentation site into site/
docs-build: docs-gen
    uv run zensical build --clean --strict

# Live preview of the documentation site
docs-serve: docs-gen
    uv run zensical serve
