/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# FracLap.Tools.ChainRule

The convex chain rule for nonlocal operators (Garofalo, `(−Δ)^s φ(u) ≤ φ'(u) (−Δ)^s u` for convex
`φ`) and the Córdoba--Córdoba inequality `Λ(u²) ≤ 2 u Λu` (`φ(t) = t²`), at the level of an
arbitrary jump measure: for each fixed `x`, integrating the tangent-line inequality in `y`.

- `convex_tangent`: `φ a + φ'(a)(b - a) ≤ φ b` for convex differentiable `φ`.
- `chain_rule_two_point`, `chain_rule_integral`: the convex chain rule.
- `cordoba_two_point`, `cordoba_integral`: the Córdoba--Córdoba inequality.
-/

namespace FracLap

open MeasureTheory

@[expose] public section

/-- **Tangent-line inequality** for a convex differentiable `φ : ℝ → ℝ`. -/
theorem convex_tangent {φ φ' : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ φ)
    (hd : ∀ x, HasDerivAt φ (φ' x) x) (a b : ℝ) : φ a + φ' a * (b - a) ≤ φ b := by
  rcases lt_trichotomy a b with h | rfl | h
  · have := hc.le_slope_of_hasDerivAt (Set.mem_univ a) (Set.mem_univ b) h (hd a)
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at this
    linarith
  · simp
  · have := hc.slope_le_of_hasDerivWithinAt_Iio (Set.mem_univ b) (Set.mem_univ a) h
      (hd a).hasDerivWithinAt
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at this
    nlinarith

/-- **Convex chain rule, two-point form**: `φ(u x) - φ(u y) ≤ φ'(u x)(u x - u y)`. -/
theorem chain_rule_two_point {φ φ' : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ φ)
    (hd : ∀ x, HasDerivAt φ (φ' x) x) (a b : ℝ) : φ a - φ b ≤ φ' a * (a - b) := by
  have := convex_tangent hc hd a b
  nlinarith

/-- **Convex chain rule for a nonlocal operator.** For every jump measure `μ` and every point `x`,
if both integrands are integrable,
`∫ (φ(u x) - φ(u y)) dμ(y) ≤ φ'(u x) ∫ (u x - u y) dμ(y)`: the operator `L v(x) = ∫(v x - v y)dμ(y)`
satisfies `L (φ ∘ u) (x) ≤ φ'(u x) · L u (x)`. -/
theorem chain_rule_integral {X : Type*} [MeasurableSpace X] {φ φ' : ℝ → ℝ}
    (hc : ConvexOn ℝ Set.univ φ) (hd : ∀ x, HasDerivAt φ (φ' x) x) (μ : Measure X) (u : X → ℝ)
    (x : X) (h1 : Integrable (fun y => φ (u x) - φ (u y)) μ)
    (h2 : Integrable (fun y => u x - u y) μ) :
    ∫ y, (φ (u x) - φ (u y)) ∂μ ≤ φ' (u x) * ∫ y, (u x - u y) ∂μ := by
  rw [← integral_const_mul]
  exact integral_mono h1 (h2.const_mul _) fun y => chain_rule_two_point hc hd _ _

/-- **Córdoba--Córdoba, two-point form**: `a² - b² ≤ 2 a (a - b)`. -/
theorem cordoba_two_point (a b : ℝ) : a ^ 2 - b ^ 2 ≤ 2 * a * (a - b) := by
  nlinarith [sq_nonneg (a - b)]

/-- **Córdoba--Córdoba inequality for a nonlocal operator**: `L(u²)(x) ≤ 2 u(x) L u(x)`. -/
theorem cordoba_integral {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : X → ℝ) (x : X)
    (h1 : Integrable (fun y => u x ^ 2 - u y ^ 2) μ) (h2 : Integrable (fun y => u x - u y) μ) :
    ∫ y, (u x ^ 2 - u y ^ 2) ∂μ ≤ 2 * u x * ∫ y, (u x - u y) ∂μ := by
  rw [← integral_const_mul]
  exact integral_mono h1 (h2.const_mul _) fun y => cordoba_two_point _ _

end

end FracLap
