# Lean 4 Proof Review Checklist

1. **Spec Fidelity (Spec-Locking & 1-to-1 File Structure)**:
   - [ ] Target theorem and definition signatures match the blueprint statement in the corresponding 1-to-1 chapter file `blueprint/src/<Path>.tex` (matching `FracLap/<Path>.lean`, included via `\input{<Path>}` in `blueprint/src/content.tex`) without weakened hypotheses.
   - [ ] `lakefile.toml` depends strictly on Lean 4 + Mathlib (no third-party Lean library packages).
   - [ ] New definitions and major theorems have high-signal `FracLapTest/` suites (non-trivial concrete instantiations, closed-form evaluations, and negative counterexamples).
2. **Proof Hygiene & Elaboration Speed**:
   - [ ] No non-terminal `simp` (use `simp only [...]` or terminal `simp`).
   - [ ] Long proofs are decomposed into clear `have` anchors and `calc` blocks mirroring LaTeX.
   - [ ] Imports are minimal (`#min_imports`) and all submodules are imported in `FracLap.lean` (`just check-imports`).
3. **Strict Linters, Blueprint & Xena Project 5-Question Audit**:
   - [ ] **Q1 (Statement fidelity)**: Target statements match `blueprint/src/<Path>.tex` without weakened hypotheses or vacuous spaces; `FracLapTest/` covers concrete evaluations and negative counterexamples; `just audit-gaps --strict` reports zero missing witnesses, zero tautologies, and zero unbridged conditional gaps.
   - [ ] **Q2 (Whole-repo compilation)**: Zero `sorry`s, zero warnings (`warningAsError = true`), full-repo `just build && just test-lean` and `just lint-lean` pass.
   - [ ] **Q3 (Actual target theorems proved)**: `just blueprint-check` and `just status` pass with `\lean{...}`, `\uses{...}`, and `\leanok` aligned; new flagship milestone theorems are registered in `comparator.json` and pass `just check-comparator`.
   - [ ] **Q4 (Standard axioms & transparency)**: `just check-axioms` passes (`propext`, `Classical.choice`, `Quot.sound` only; no `sorryAx` or `Lean.trustCompiler`); `just audit-gaps --strict` Section 5 reports zero custom `axiom`, `opaque`, `partial`/`unsafe`, `@[implemented_by]`, or `@[extern]` in `FracLap.*`.
   - [ ] **Q5 (Independent kernel soundness)**: `just check-kernel` passes on every review; at large milestones or on request, multi-kernel verification passes via `just check-paranoid`, `just check-con-leche`, and `just check-comparator-paranoid`.
4. **Commit Often**:
   - [ ] Changes are committed atomically with a valid Conventional Commit subject (`<= 72` chars, validated by `prek` `commit-msg` hook).
