---
name: finalize
description: >-
  Multi-stage verification and PR pipeline for FracLap formalizations: builds Lean 4,
  audits axioms for sorryAx, compiles leanblueprint web + PDF, checks 1-to-1 sync and
  resource parity, commits, pushes, creates PR, and monitors CI. Never merges without
  explicit user confirmation.
---

# Formalization Finalization & Quality Gatekeeping (`finalize`)

Automated quality gate before committing, pushing, or opening a PR in `frac-lap-lean`.

## Strict Operational Invariants

1. **Halt on Any Failure**: Stop immediately if Lean compilation, axiom auditing, `leanblueprint`, or Python checks fail.
2. **No `sorry` or Unsound Axioms on `main`**: Every declaration in `FracLap.*` must pass `scripts/check_axioms.lean`, and `\leanok` inside `\begin{proof}` is permitted only when zero `sorry`s remain.
3. **Xena Project 5-Question Audit**: Every milestone must satisfy statement fidelity (`blueprint/` + `FracLapTest/` + non-vacuity witnesses), full-repo compilation (`just build && just test-lean`), actual target theorem checking (`just blueprint-check` + `comparator.json`), standard axioms & full transparency (`just check-axioms` + `just audit-gaps --strict`), and milestone multi-kernel replay (`just check-paranoid` / `just check-con-leche`).
4. **Never Merge Without Explicit Confirmation**: Stop after confirming PR CI checks pass; never run `gh pr merge` unprompted.

---

## 6-Stage Pipeline

1. **Lean Build, Lint & Anti-Vacuity**: Run `just build && just lint-lean && just test-lean` (`lake build` with `warningAsError = true` and `mathlibStandardSet`, `lake lint`, and `FracLapTest`; never build Mathlib locally without `just cache`).
2. **Zero `sorry`, Imports, Axioms, Spec-Gaps & Kernel Replay**: Check `grep -rn '\bsorry\b' FracLap/` is empty and run `just check-imports && just check-axioms && just audit-gaps --strict && just check-kernel` (`audit-gaps --strict` verifies concrete structure inhabitation, zero tautologies, non-vacuity witnesses, and Xena/SafeVerify soundness & transparency: no custom `axiom`, `opaque`, `partial`/`unsafe`, `@[implemented_by]`, or `@[extern]` in `FracLap.*`).
3. **Proof Review & Blueprint Sync**: Run the `lean-review` checklist, verify `just check-imports && just lint-tex && just blueprint && just status` (1-to-1 `FracLap/<Path>.lean` ↔ `blueprint/src/<Path>.tex` file parity + `chktex` + `leanblueprint all` + dashboard), and confirm `\lean{...}`, `\uses{...}`, `\leanok` tags match across `blueprint/src/**/*.tex`.
4. **Python & `prek` Checks**: Run `just lint-py && just test && just check`.
5. **Atomic Conventional Commit, Push & Milestone Paranoid Gate**: Commit often using Conventional Commits (enforced by `prek` `commit-msg` hook; template in [resources/commit_template.txt](./resources/commit_template.txt)) and push branch (`prek` `pre-push` hook runs the fast incremental Lean gate: `lint-quick`, `build`, `test-lean`, `check-imports`, `check-axioms`, `audit-gaps --strict`). When requested or after a large chunk of work, run the heavy milestone checks via `just check-manual` (`just verify-all` plus `just check-paranoid` and `just check-comparator`) or `just check-con-leche` (also scheduled weekly in `.github/workflows/paranoid.yml`).
6. **Pull Request & CI Watch**: Open PR using [resources/pr_template.md](./resources/pr_template.md) via `gh pr create`, monitor with `gh pr checks --watch`, and **STOP** for user merge approval.
