# FracLap Repository Guidelines

This repository pairs **Lean 4 + Mathlib** formalizations (`FracLap/`) with a 1-to-1 human-readable **LaTeX blueprint** (`blueprint/src/content.tex`) and anti-vacuity checks (`FracLapTest/`). It is the public library of a split: unpublished research lives in a separate private repository that depends on this one, never the other way round.

## Core Rules

1. **Mathlib-Only Foundation & Cache**:
   - All Lean formalizations in `FracLap/` and tests in `FracLapTest/` must depend **strictly on Lean 4 + Mathlib** (no external third-party Lean library dependencies in `lakefile.toml`; only `mathlib` and standard verification tooling such as `checkdecls`). Adapt or prove any needed results directly on Mathlib.
   - Always run `lake exe cache get` (or `just cache`) after toolchain or Mathlib updates before `lake build`, and never build Mathlib locally.
2. **1-to-1 Blueprint Synchronization**:
   - **1-to-1 Multi-File Hierarchy** (enforced by `scripts/check_imports.py` / `just check-imports`): Every Lean module `FracLap/<Path>.lean` must have a matching LaTeX file `blueprint/src/<Path>.tex`, and `blueprint/src/content.tex` must act solely as the root `\input{<Path>}` aggregator (mirroring `FracLap.lean`) with no inline theorem/definition blocks.
   - Every definition, lemma, and theorem in `blueprint/src/<Path>.tex` should declare `\lean{FracLap.<name>}` and `\uses{...}` dependencies.
   - Place `\leanok` inside a theorem/definition block once its formal statement type-checks in Lean, and place `\leanok` inside `\begin{proof}...\end{proof}` **only** when the Lean proof has zero `sorry`s.
   - Mirror theorem structure in Lean using structured `have` steps and `calc` blocks so Lean proofs align paragraph-by-paragraph with the LaTeX proof.
3. **Spec-Locking & High-Signal Tests**:
   - **Never silently weaken or alter** a target theorem statement, hypothesis, or core definition signature to close a `sorry`. If a statement appears unprovable as written, stop and confirm with the maintainer before changing its specification.
   - Pair every new core definition and major theorem in `FracLap/` with **high-signal tests** in `FracLapTest/` (`just test-lean`): concrete non-trivial instantiations with closed-form operator/generator/resolvent evaluations, boundary/round-trip checks, and negative counterexamples ruling out vacuous definitions or broken hypotheses.
4. **Strict Lean Linting, Kernel Replay & Zero `sorry`**:
   - Strict mode is enabled in `lakefile.toml` (`warningAsError = true`, `autoImplicit = false`, `relaxedAutoImplicit = false`, `weak.linter.mathlibStandardSet = true`, `weak.linter.missingDocs = true`, `weak.linter.style.header = true`, `weak.linter.style.longLine = true`, `lintDriver = "batteries/runLinter"`).
   - Run `just verify-all` (builds `FracLap` & `FracLapTest`, runs `lake lint`, checks root imports in `FracLap.lean`, audits axioms with `scripts/check_axioms.lean`, audits structural/abstract/tautology gaps plus soundness checks with `scripts/audit_spec_gaps.lean`, replays `.olean`s with `leanchecker`, checks `leanblueprint checkdecls`, lints `.tex` with `chktex`, and runs `ruff` + `pyrefly` + `complexipy` + `pytest`). Use `just audit-gaps --strict` as a zero-gap gate.
   - For on-request / large-milestone verification run `just check-external`, `just check-paranoid`, `just check-con-leche`, `just check-comparator` (`lake comparator --config comparator.json`), and `just shake` (import minimization).
   - Run `just status` to inspect formalization and blueprint `\leanok` progress, and run `.agents/skills/lean-review/SKILL.md` after closing major proofs.
   - **Xena Project Trustworthiness Rules (5-Question Audit)**: (1) *statement fidelity* (no weakened hypotheses, trivialized definitions or vacuous spaces), (2) *reproducible compilation* (`just build && just test-lean`), (3) *actual target theorems proved* (`just blueprint-check`, `comparator.json`), (4) *standard axioms only* (`propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, `native_decide`, custom `axiom`, `opaque`, `partial`/`unsafe`, `@[implemented_by]`, `@[extern]`), (5) *independent kernel soundness* (`just check-paranoid`, weekly in `.github/workflows/paranoid.yml`).
5. **Git & Commit Hygiene (Commit Often)**:
   - Make small, atomic, verified commits after each coherent milestone (a lemma group, a blueprint section, a tooling step).
   - **Commit message standard** (enforced by the `prek` `commit-msg` hook): Conventional Commits `<type>(<scope>): <imperative summary <= 72 chars>` with type in `feat|fix|refactor|docs|test|chore|ci|perf|style|build` and a domain scope (e.g. `lean`, `blueprint`, `docs`, `ci`, `setup`). Never bypass hooks with `--no-verify`.
6. **Academic LaTeX Authoring**: follow `.agents/skills/latex-authoring/SKILL.md` for crisp academic prose and `just lint-tex` compliance. The bibliography is `blueprint/src/references.bib`.
7. **Tooling & Periodic Progress Updates**:
   - **Explain what you are doing periodically** before and between multi-step formalization or verification passes, and **explain the mathematical intuition** (why the statement is true, why the chosen route works) before each lemma group and in the blueprint proof sketch. The explanation is a running commentary, not a checkpoint.
   - Use **`lean-lsp`** (`.mcp.json`) to inspect goal states and search Mathlib; search Mathlib (`lean_local_search`, `just lean-grep`) before writing any helper lemma. Ground statements in the literature and cite the source in the module docstring or the blueprint.

## Workflow Conventions

- **Before building**: run `just lint-quick [files]` (line length, `show`→`change`, deprecated Mathlib names, `haveI`, missing docstrings). Use `just lean-grep '<name>'` instead of guessing Mathlib or core names.
- **New modules**: always `just new-module <Dir/Name>`. It creates the Lean file, blueprint chapter and `FracLapTest/<Name>Test.lean`, and registers all of them. Tests mirror modules: one test file per module. Place the module in `docs/provenance.toml` on creation.
- **Blueprint prose never cites library lemma names**: state standard analysis facts once, in words, as `\mathlibok` nodes in `blueprint/src/StandardResults.tex`, and cite them through `\ref{thm:std_...}` and `\uses{...}`. chktex rejects half-open intervals such as `(0, 1]` and sized braces: write sets as inequalities.
- **Verification cadence** (`prek`): pre-commit (fast: format, parity, `chktex`, `lint-quick`, incremental build), pre-push (`lint-quick`, `build`, `test-lean`, `check-imports`, `check-axioms`, `audit-gaps --strict`), on-request (`just verify-all`, `just check-manual`).
- **Claim discipline**: docstrings, blueprint text and test comments may state only what the Lean code proves. When you add a concrete instance of a structure over a function space, prove an `exists_...` witness theorem that the space is nontrivial and register it in `scripts/audit_spec_gaps.lean`.
- **Docs & provenance**: the site (`zensical.toml`, `docs/`) is generated from the blueprint and Lean sources by `scripts/gen_docs.py` (`just docs-gen`, `just docs-build`, `just docs-serve`). The public site claims only what Lean proves.
- **Logging**: every Python entry point calls `init_logging(__file__)` first in its `__main__` block (`from logsetup import init as init_logging`). Each run writes a rotating, git-ignored `.logs/<script>.log`; `FRACLAP_NO_LOG=1` disables it.
- **Never push without being asked.**
