---
name: lean-formalization
description: >-
  Bounded 4-stage workflow for formalizing fractional PDE and analysis results in Lean 4 + Mathlib
  with 1-to-1 leanblueprint synchronization, literature grounding, anti-vacuity checks, and
  lean-lsp goal inspection. Use whenever drafting definitions, lemmas, theorems, or proofs in
  FracLap/ and blueprint/src/.
---

# Lean 4 + Blueprint Formalization Skill (`lean-formalization`)

Guides literature-grounded, spec-locked, 1-to-1 formalization across `FracLap/`, `FracLapTest/`, and `blueprint/src/content.tex` using a bounded 4-stage loop.

---

## Bounded 4-Stage Formalization Loop

1. **Search-First & Explain Progress (literature + `lean-lsp`)**:
   - **Mathlib-Only Dependency Policy**: Keep `lakefile.toml` strictly grounded on Lean 4 + Mathlib (no third-party Lean library dependencies); adapt or prove needed results directly on Mathlib.
   - **Explain your progress**: Periodically summarize what you are doing and which mathematical gap or module you are tackling so the user has clear visibility into the workflow.
   - **Check `.temp/` for active plans & notes**: Read `.temp/` (gitignored) for existing roadmaps, literature harvests, and partial writeups, and store new plans, writeups, or partial work there.
   - **Ground every statement in the literature**: take hypotheses, normalization constants and proof steps from the cited source, and cite it in the module docstring or the blueprint (`blueprint/src/references.bib`).
   - Query `lean_local_search`, `lean_loogle`, and `lean_leansearch` via `lean-lsp` before writing new helper lemmas so existing Mathlib results are reused.
2. **Statement + High-Signal Tests (`FracLap/` + `FracLapTest/` + `blueprint/src/`)**:
   - **1-to-1 Multi-File Hierarchy**: Mirror module files 1-to-1 between `FracLap/<Path>.lean` (imported in `FracLap.lean`) and `blueprint/src/<Path>.tex` (included via `\input{<Path>}` in `blueprint/src/content.tex`, which must remain a pure `\input{...}` aggregator without inline theorem blocks; verified by `just check-imports`), using [resources/lean_module_template.lean](./resources/lean_module_template.lean) and [resources/blueprint_chapter_template.tex](./resources/blueprint_chapter_template.tex).
   - Pair every new core definition and major theorem with **high-signal tests** in `FracLapTest/` (`just test-lean`): non-trivial concrete models, closed-form identities, round-trip checks, and negative counterexamples ruling out vacuity.
   - Mark `\leanok` inside `\begin{definition|lemma|theorem}` once the Lean statement type-checks; omit `\leanok` inside `\begin{proof}` while `sorry` remains.
3. **Bounded Proof Repair (Spec-Locked)**:
   - **Spec-Locking Invariant**: Never silently weaken hypotheses or change target theorem signatures to close a `sorry`; ask the user explicitly if a statement needs revision.
   - Inspect live goals and diagnostics via `lean-lsp` (`lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`).
   - Fix type mismatches before downstream tactic errors; structure proofs with named `have` steps and `calc` chains mirroring LaTeX `align*` blocks; use `exact?`, `apply?`, `aesop`, `grind`, and `omega` on routine subgoals.
   - If a tactic block fails after 3–5 attempts, factor out an intermediate `have` or private helper lemma rather than thrashing.
4. **Verify, Review & Commit Often**:
   - Before the first build run `just lint-quick`; consult [references/lean-pitfalls.md](./references/lean-pitfalls.md) for linter traps, Mathlib renames and elaboration pitfalls. Scaffold modules with `just new-module <Dir/Name>`; prototype with `just scratch <file>`; look up names with `just lean-grep '<name>'`.
   - Docstrings, blueprint text and test comments must state only what the Lean code proves; for every concrete instance over a function space add a non-vacuity witness theorem and register it in `scripts/audit_spec_gaps.lean`.
   - Never build Mathlib locally: run `just cache` after toolchain/Mathlib updates.
   - `lakefile.toml` enforces `warningAsError = true`, `weak.linter.mathlibStandardSet = true`, `weak.linter.missingDocs = true`, 100-char lines, `autoImplicit = false`, and `batteries/runLinter`.
   - Run `just verify-all` (`lake build`, `lake lint`, `test-lean`, `check-imports`, `check-axioms`, `check-kernel`, `leanblueprint checkdecls`, `lint-tex`, `lint-py`, `test`).
   - Run the `lean-review` cleanup pass and create a small, atomic Conventional Commit (`<type>(<scope>): <summary>`) after each verified milestone.
