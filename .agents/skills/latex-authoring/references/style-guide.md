# Academic Mathematical LaTeX Style Guide

Synthesized from Paul Halmos (*How to Write Mathematics*), Nicholas J. Higham (*Handbook of Writing for the Mathematical Sciences*), Terence Tao (*Advice on Mathematical Writing*), and the AMS *Short Math Guide for LaTeX*.

---

## 1. Prose & Sentence Mechanics

1. **Equations as Parts of Speech**:
   - Every displayed equation belongs to a grammatical sentence. End displayed formulas with `,` or `.` as required by the surrounding clause.
   - Do not stack unrelated clauses around displayed math without connective prose (*"Then"*, *"Hence"*, *"Substituting this into \eqref{eq:energy} yields"*).
2. **No Sentence-Initial Symbols**:
   - Wrong: *"$f$ is continuous on $\mathbb{R}^d$."*
   - Right: *"The function $f$ is continuous on $\mathbb{R}^d$."* or *"Let $f \in C(\mathbb{R}^d)$."*
3. **Avoid Quantifier Soup in Running Text**:
   - Write out *"for every"*, *"there exists"*, *"such that"* in prose; reserve `$\forall$` and `$\exists$` for symbolic formulas or displayed statements.
4. **Symbol Hygiene**:
   - Never reuse the same symbol for two roles in the same section, and avoid adjacent mathematical tokens separated only by space (write *"For $k \ge 1$, the sequence..."* instead of *"For $k \ge 1$ $a_k$..."*).
5. **Motivation & Signposting**:
   - Introduce each theorem or lemma with a sentence explaining what it accomplishes, and give a one-sentence roadmap before long multi-step proofs.

---

## 2. AMS & `mathtools` Typesetting Rules

- **Delimiters**: Define paired delimiters with `\DeclarePairedDelimiter`:
  ```latex
  \DeclarePairedDelimiter{\abs}{\lvert}{\rvert}
  \DeclarePairedDelimiter{\norm}{\lVert}{\rVert}
  \DeclarePairedDelimiterX{\inner}[2]{\langle}{\rangle}{#1, #2}
  ```
  Use `\norm{u}_{H^s}` for inline formulas and `\norm*{...}` only when tall fractions/integrals require automatic scaling.
- **Definitions**: Use `\coloneqq` (from `mathtools`) for definitional equality, never bare `:=`.
- **Differentials & Operators**: Define `\newcommand{\dd}{\mathop{}\!\mathrm{d}}` so `\int_{\mathbb{R}^d} u(x) \dd x` has proper thin spacing and upright `d`. Define operators with `\DeclareMathOperator` (`\supp`, `\dist`, `\pv`, `\osc`).
- **Ellipses**: Use `\dots` (AMS auto-selects `\ldots` vs `\cdots` based on surrounding binary/comma tokens), or explicit `\dotsc` / `\dotsb` when ambiguous.
- **Cross-References**:
  - In standalone `amsart` papers: use `\usepackage[capitalize,nameinlink]{cleveref}` with `\cref{...}` / `\Cref{...}` and `\eqref{...}`.
  - In `blueprint/src/*.tex`: use `Definition~\ref{...}`, `Theorem~\ref{...}`, `Lemma~\ref{...}`, and `\eqref{...}` so both `pdflatex` and `plasTeX` render cleanly.
- **Proof Endings**: When a proof ends in a displayed equation, put `\qedhere` inside the math environment so the QED tombstone does not drop onto a blank trailing line.

---

## 3. PDE & Fractional Calculus Conventions

- State the order $s \in (0, 1)$, spatial dimension $d \ge 1$, and function space ($C_c^\infty(\mathbb{R}^d)$, $\mathcal{S}(\mathbb{R}^d)$, $H^s(\mathbb{R}^d)$, $\dot{H}^s(\mathbb{R}^d)$) explicitly in every lemma/theorem statement.
- Keep normalization constants $c_{d,s}$ explicit in singular-integral definitions of $(-\Delta)^s$:
  $$(-\Delta)^s u(x) \coloneqq c_{d,s} \operatorname{p.v.} \int_{\mathbb{R}^d} \frac{u(x) - u(y)}{\abs{x - y}^{d + 2s}} \dd y.$$
- Track generic constants explicitly ($C = C(d, s, p) > 0$) when proving energy or commutator estimates, especially when aligning with Lean `have` hypotheses.

---

## 4. `chktex` Verification

Run `just lint-tex` before committing. Fix genuine syntax/spacing issues (`~` before `\ref`/`\cite`, `{...}` around multi-character sub/superscripts, `amsmath` environments instead of `$$...$$` or `eqnarray`) rather than suppressing warnings inline.
