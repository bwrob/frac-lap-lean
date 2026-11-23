# FracLap

**A machine-checked, human-readable body of knowledge on the fractional Laplacian.**

This project formalizes, in [Lean 4](https://lean-lang.org/) on top of [Mathlib](https://leanprover-community.github.io/), the theory of the fractional Laplacian $(-\Delta)^{\alpha/2}$, $0<\alpha<2$: its definitions on the whole line and on the half-line, the stable heat kernel and semigroup, the associated Dirichlet forms, maximum principles, and a growing toolbox of functional inequalities (Nash, Bernstein, Stroock–Varopoulos, Hardy–Littlewood, ...). The starting point is the author's 2016 master's thesis, *Anomalous Diffusion Equation on the Half-Line*.

Every result has two faces that are kept in strict 1-to-1 correspondence:

- a **blueprint** statement and proof sketch in LaTeX, written for people;
- a **Lean** declaration that the proof assistant has checked, written for the machine.

!!! tip "Switch between mathematics and code"
    On every page of the [Knowledge](knowledge/index.md) section, each statement has three tabs:
    **Blueprint** (rendered LaTeX), **Lean** (the checked declaration) and **LaTeX source**.
    The tabs are linked: pick *Lean* once and the whole site switches.

## Where to start

| I want to... | Go to |
|---|---|
| read the mathematics and see the Lean next to it | [Knowledge](knowledge/index.md) |
| understand how the repository is organised and verified | [Repository setup](setup.md) |
| understand how the work is done day to day (including the role of AI assistance) | [How the work is done](workflow.md) |
| browse the interactive dependency graph | [Blueprint graph](blueprint/index.html) |
| find the source literature | [Bibliography](knowledge/bibliography.md) |

## Honesty about scope

- A statement is called *formalized* only if Lean accepts it; a proof is marked formalized only if it has no `sorry` ([details](setup.md#what-formalized-means)).
- Known gaps are listed in the chapters themselves. For example, several whole-line results are currently stated for Schwartz data only, and the half-line semigroup is **not** claimed to be holomorphic.
