# Repository setup

The repository couples a Lean library, a LaTeX blueprint, a test suite and a set of audits. The blueprint records the statements and proof sketches alongside their Lean declarations.

## Layout

```text
FracLap/            Lean 4 library (one module per topic: Core, WholeLine, HalfLine, Tools)
FracLapTest/        anti-vacuity tests, one test module per library module
blueprint/src/      LaTeX blueprint, one chapter per Lean module (same path)
scripts/            checks, scaffolding, documentation generator
docs/               this site (narrative pages; the Knowledge section is generated)
```

## 1-to-1 correspondence

Every Lean module `FracLap/<Path>.lean` has exactly one blueprint chapter `blueprint/src/<Path>.tex` and one test module `FracLapTest/<Name>Test.lean`. `just new-module <Path>` creates and registers all three, and `just check-imports` fails if they drift apart. In the blueprint, each definition, lemma and theorem carries

- `\lean{...}`: the Lean declarations that formalize it,
- `\uses{...}`: the nodes it depends on (this produces the dependency graph),
- `\leanok`: placed in the statement once it type-checks in Lean, and in the proof only when the Lean proof contains no `sorry`.

The [Knowledge](knowledge/index.md) pages of this site are generated from exactly these annotations.

## What "formalized" means {#what-formalized-means}

1. **Mathlib only.** The library depends on Lean 4 and Mathlib and nothing else. Standard analysis facts that Mathlib provides are stated once, in words, as `\mathlibok` nodes in the blueprint appendix and cited from proofs.
2. **No `sorry`, no custom axioms.** All declarations must depend only on `propext`, `Classical.choice` and `Quot.sound`; no `native_decide`, `axiom`, `opaque`, `partial`, `unsafe`, `implemented_by` or `extern` in the library.
3. **Spec-locking.** A target statement is never weakened to make a proof go through. If a statement looks unprovable, the work stops and the specification question is raised explicitly.
4. **Claim discipline.** Docstrings, blueprint text and tests may only state what the Lean code proves.

## Tests that guard against vacuity

A theorem about an empty or trivial structure proves nothing. `FracLapTest/` therefore contains, for every new definition and major theorem, concrete non-trivial instantiations (closed-form evaluations, round-trips), negative counterexamples that show hypotheses are not vacuous, and *witness* theorems (for instance, that a concrete Dirichlet form or semigroup lives on a non-trivial function space). A registry of such witnesses is audited automatically.

## Verification tiers

| Tier | When | What runs |
|---|---|---|
| Pre-commit | every `git commit` | formatting, import parity, `chktex` on the blueprint, fast style lint, and an incremental `lake build` plus tests whenever Lean files change |
| Pre-push | every `git push` | build, tests, root-import and blueprint parity, axiom audit, structure-inhabitation and tautology audit (`audit-gaps --strict`) |
| Full / milestone | on request | full build with the strict linters, `lake lint`, `leanchecker` kernel replay, `leanblueprint checkdecls`, independent kernels (`lean4lean`, `nanoda`, `con-leche`), and `comparator` against the locked flagship statements in `comparator.json` |

**GitHub CI** mirrors the light tiers: parallel jobs for Lean (build, `lake lint`, axiom and gap audit, blueprint declarations), LaTeX lint and Python, each skipped when its files are untouched, with superseded runs cancelled. The heavy kernel replay (`leanchecker` per module, multi-kernel and `comparator` audits) runs weekly and on demand in a separate workflow.

The audit follows Kevin Buzzard's five questions for trustworthy formalizations: statement fidelity, reproducible compilation, the actual target theorems proved, standard axioms only, and independent kernel replay.

## This site

The narrative pages are hand-written Markdown. The Knowledge section is produced by `scripts/gen_docs.py` from the blueprint and the Lean sources, and the site is built with [Zensical](https://zensical.org/) and published to GitHub Pages by the `Docs` workflow on every push to `main`. The interactive blueprint (dependency graph, produced by `leanblueprint`) is built in the same workflow and published under `/blueprint/`.

```bash
just docs-gen     # regenerate docs/knowledge/ and the nav in zensical.toml
just docs-serve   # live preview
just docs-build   # strict build into site/
```
