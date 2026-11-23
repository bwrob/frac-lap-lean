# Lean pitfalls for this repository

Every item below caused a failed build or a lost iteration. Check them before building
(`just lint-quick` automates the mechanical ones).

## Strict linters (warnings are errors)

| Symptom | Fix |
|---|---|
| line exceeds 100 characters | wrap the line; `lint-quick` reports the exact line |
| `show` changed the goal | use `change` (term-mode `show ... from`/`by` inside `rw [...]` is fine) |
| deprecated name | see the rename table below |
| `haveI` for a proposition | use `have` |
| unused simp argument / unused variable | delete it or rename it `_x` |
| tactic block starts with N goals and ends with M | bullet (`·`) every goal |
| `simpa using h` where `simp` already closes | use plain `simp` |
| `missingDocs` | every `def`, `abbrev`, `structure`, `class` in a public section needs a docstring |

## Renames in the pinned Mathlib / Lean (4.36)

`Measurable.enorm`→`eNorm`, `Continuous.enorm`→`eNorm`, `enorm_ne_top`→`eNorm_ne_top`,
`enorm_mul`→`eNorm_mul`, `Lp.enorm_def`→`Lp.eNorm_def`, `ofReal_norm_eq_enorm`→`ofReal_norm`,
`Real.enorm_eq_ofReal`→`Real.eNorm_eq_ofReal`, `push_neg`→`push Not`, `coe_nnnorm`→`coe_nnNorm`,
`lipschitzWith_of_nnnorm_fderiv_le`→`lipschitzWith_of_nnNorm_fderiv_le`,
`Isometry.antilipschitz`→`Isometry.antilipschitzWith`.
`MemLp f p μ` is definitionally `eLpNorm f p μ < ∞` (no separate measurability field).

## Elaboration traps

- `import FracLap` loads `FracLap.olean`; if only a submodule was rebuilt it is stale. Use
  `just scratch`, or `lake build FracLap` first.
- `rw` with a literal `2` rewrites every `2` in the goal, including `Lp ℂ 2 μ`; prove the
  numeric fact as a separate `have` and rewrite that.
- `lintegral_withDensity_eq_lintegral_mul` needs the measurable function as an explicit,
  correctly typed hypothesis (beta-reduced); `unfold gagliardoMeasure` breaks dependent types, so
  state the rewrite as a `have key : ∀ G, Measurable G → ∫⁻ ... ∂gagliardoMeasure α = ...`.
- `Measurable.const_mul` (not `measurable_const.mul`) matches `lintegral_add_left` patterns.
- Abstract an `Lp` element with `obtain ⟨G, hG⟩ : ∃ G, G = ... := ⟨_, rfl⟩` before heavy
  unification; coercion chains can time out `isDefEq`.
- Library helpers (`CollectAxioms.State`, ...) are private in `module` files; use the public API.
- `∞` is ambiguous between `ENNReal` and smoothness; `open scoped ContDiff` and write
  `ContDiff ℝ ∞ f` only in files that do not need `ℝ≥0∞`'s `∞`, or use `(⊤ : ℕ∞)`.

## Workflow

`just new-module`, `just scratch`, `just lean-grep`, `just lint-quick`, `just verify-all`.
