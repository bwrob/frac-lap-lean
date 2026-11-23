---
name: lean-review
description: >-
  Post-green Lean 4 proof review and cleanup pass: tightens simp calls to simp only, removes
  redundant have/import boilerplate, checks 1-to-1 blueprint alignment and FracLapTest
  anti-vacuity coverage, and runs kernel/axiom verification before committing. Use after closing
  a theorem or before finalizing a formalization milestone.
---

# Lean 4 Proof Review & Cleanup (`lean-review`)

Structured post-green pass to keep `FracLap/` idiomatic, fast to elaborate, and strictly aligned with `blueprint/src/` and `FracLapTest/`.

---

## Review Workflow

1. **Follow the Review Checklist**: Audit the diff against [resources/review_checklist.md](./resources/review_checklist.md).
2. **Tighten Proofs & Imports**:
   - Replace bare non-terminal `simp` with `simp only [...]` (via `simp?`) and remove unused `open`, `variable`, or `have` bindings.
   - Check `#min_imports` (or `just shake` across modules) to trim unnecessary Mathlib imports.
   - Confirm `have` and `calc` steps still mirror the corresponding proof paragraphs in `blueprint/src/<Path>.tex` (with 1-to-1 file parity between `FracLap/<Path>.lean` and `blueprint/src/<Path>.tex`, and `blueprint/src/content.tex` acting strictly as the `\input{<Path>}` aggregator).
3. **Verify Mathlib-Only Dependencies, High-Signal Tests & Xena Trustworthiness Gate**:
   - Confirm `lakefile.toml` contains no third-party Lean library dependencies (strictly Mathlib + tooling).
   - Confirm new definitions and major theorems have high-signal coverage in `FracLapTest/`: non-trivial concrete instantiations, closed-form checks, and negative counterexamples.
   - Run `just audit-gaps --strict` (checking `scripts/audit_spec_gaps.lean` for uninhabited/combinator-only structures, direct-projection tautologies, missing non-vacuity witnesses, conditional `WholeLine`/`HalfLine` theorems, and Xena/SafeVerify soundness & transparency: no custom `axiom`, `opaque`, `partial`/`unsafe`, `@[implemented_by]`, or `@[extern]`), `just verify-all`, and `just status`. At large milestones or on request, also run `just check-manual` (`just verify-all` + `just check-paranoid` + `just check-comparator`) or `just check-con-leche`, then make a clean Conventional Commit.

---

## External Checklist

- **Review Checklist**: [resources/review_checklist.md](./resources/review_checklist.md)
