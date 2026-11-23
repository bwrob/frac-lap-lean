---
name: latex-authoring
description: >-
  Academic mathematical LaTeX authoring guidelines and templates (AMS, mathtools, cleveref,
  microtype, Halmos/Higham/Tao prose standards) for papers and leanblueprint chapters. Use
  whenever writing, editing, or reviewing .tex files in blueprint/src/ or manuscripts.
---

# Academic Mathematical LaTeX Authoring (`latex-authoring`)

Standards and templates for writing crisp, publication-grade mathematical LaTeX in `blueprint/src/` and standalone manuscripts.

---

## Core Workflow

1. **Mathematical Prose Craft (Halmos / Higham / Tao)**:
   - **Prose first, symbols second**: Equations are grammatical parts of sentences and must be punctuated with commas or periods.
   - **Never start a sentence with a symbol**: Write *"Let $u \in H^s(\mathbb{R}^d)$..."* instead of *"$u \in H^s(\mathbb{R}^d)$ satisfies..."*.
   - **No shorthand in running text**: Write *"for all"*, *"there exists"*, *"such that"*, *"that is"*, *"for example"* instead of `$\forall$`, `$\exists$`, `s.t.`, `i.e.`, `e.g.`.
   - **Motivate before formalizing**: Briefly state the role of each definition/lemma and sketch non-obvious proof ideas before technical estimates.
   - **Explicit dependencies**: State regularity assumptions, domain hypotheses, and constant dependencies (e.g., $C = C(d, s, p) > 0$) upfront.
2. **Typesetting & Macro Discipline**:
   - Use `amsmath`, `amssymb`, `amsthm`, `mathtools`, and `microtype`.
   - Prefer `\DeclarePairedDelimiter` (`\abs`, `\norm`, `\inner`) and `\coloneqq` over raw `\left`/`\right` or `:=`.
   - Use `\DeclareMathOperator` for named operators (`\supp`, `\dist`, `\pv`) and `\mathop{}\!\mathrm{d}x` for differentials.
   - Place equation numbers on the right (`reqno`), use `\qedhere` if a proof ends with display math, and use `~` before `\ref` / `\eqref` / `\cite` (and `\cref` / `\Cref` in standalone `amsart` papers; in `blueprint/src/`, stick to plasTeX-compatible `~\ref{...}` / `\eqref{...}`).
3. **Blueprint Synchronization (1-to-1 Multi-File Hierarchy)**:
   - Every Lean module `FracLap/<Path>.lean` maps 1-to-1 to a dedicated LaTeX file `blueprint/src/<Path>.tex`, while `blueprint/src/content.tex` contains only `\input{<Path>}` lines mirroring `FracLap.lean` (verified by `just check-imports`).
   - Place shared math macros in [blueprint/src/macros/common.tex](../../../blueprint/src/macros/common.tex) so both `pdflatex` and `leanblueprint web` (plasTeX) render identically.
4. **Blueprint Conventions & chktex Gotchas**:
   - **Never cite library lemma names** (Mathlib or Lean core) in blueprint prose. State each standard analysis fact once, in words, as a `\mathlibok` node in `blueprint/src/StandardResults.tex` and refer to it with `Theorem~\ref{thm:std_...}` plus `\uses{thm:std_...}`; add a new node there when a proof needs a new standard fact.
   - chktex (`just lint-tex`) rejects half-open intervals such as `(0, 1]` and unbalanced-looking delimiters, and flags `\{ \}` in running text: write sets as inequalities (`$0 < h \le 1$`, `for all $x \le \delta$`) and avoid `\bigl\{` in definitions.
   - Run `just blueprint-pdf` twice-clean: forward references to the appendix appear as undefined only on the first pass; the final `latexmk` pass must report none.
5. **Verify Formatting & Compilation**:
   - Run `just lint-tex` (`chktex`) and `just blueprint` (`leanblueprint all`) to ensure zero warnings, zero undefined references, and clean PDF/HTML output.

---

## External References & Templates

- **Detailed Style Manual**: [references/style-guide.md](./references/style-guide.md)
- **Standalone AMS Paper Template**: [resources/ams_paper_template.tex](./resources/ams_paper_template.tex)
- **Blueprint Section Template**: [resources/blueprint_section_template.tex](./resources/blueprint_section_template.tex)
