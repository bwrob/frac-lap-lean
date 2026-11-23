/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.GagliardoSymbolExact

/-!
# FracLap.Tools.Bernstein

Bernstein inequalities for band-limited functions in `L²(ℝ; ℂ)` (Danchin, Abidi--Hmidi).

If `𝓕 f` vanishes almost everywhere outside `{ξ : |ξ| ≤ R}` then
`E_α(f) ≤ (2π R)^α ‖f‖²` (`bernstein_upper`); if it vanishes almost everywhere inside
`{ξ : |ξ| < r}` then `(2π r)^α ‖f‖² ≤ E_α(f)` (`bernstein_lower`). Both follow from the exact
symbol `Λ_α(ξ) = |2π ξ|^α` and Plancherel.
-/

namespace FracLap

open Complex Filter FourierTransform MeasureTheory Real Set Topology
open scoped ENNReal NNReal

@[expose] public section

/-- `∫⁻ ‖𝓕 f‖² = ‖f‖²` (Plancherel, lintegral form). -/
theorem lintegral_enorm_sq_fourier (f : L2C) :
    ∫⁻ ξ, ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) = ‖f‖ₑ ^ (2 : ℝ) := by
  have hnorm : ‖(𝓕 f : L2C)‖ₑ = ‖f‖ₑ := by
    have := (Lp.fourierTransformₗᵢ ℝ ℂ).norm_map f
    rw [← ofReal_norm, ← ofReal_norm]
    exact congrArg ENNReal.ofReal this
  rw [lintegral_enorm_sq_eq_measure (𝓕 f : L2C), hnorm]

/-- **Bernstein upper inequality**: a function with `𝓕 f` supported in `|ξ| ≤ R` has
`E_α(f) ≤ (2π R)^α ‖f‖²`. -/
theorem bernstein_upper {α : ℝ} (hα : FractionalExponent α) (f : L2C) {R : ℝ}
    (hsupp : ∀ᵐ ξ : ℝ, R < |ξ| → ((𝓕 f : L2C) : ℝ → ℂ) ξ = 0) :
    gagliardoEnergyC α f ≤ ENNReal.ofReal ((2 * π * R) ^ α) * ‖f‖ₑ ^ (2 : ℝ) := by
  rw [gagliardoEnergyC_eq_lintegral hα, ← lintegral_enorm_sq_fourier f,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [hsupp] with ξ hξ
  by_cases h : R < |ξ|
  · rw [hξ h]; simp
  · push Not at h
    have h0 : 0 ≤ R := le_trans (abs_nonneg _) h
    have hpow : |2 * π * ξ| ^ α ≤ (2 * π * R) ^ α := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      exact Real.rpow_le_rpow (by positivity) (by nlinarith [abs_nonneg ξ, Real.pi_pos]) hα.1.le
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hpow) bot_le

/-- **Bernstein lower inequality**: a function with `𝓕 f` supported in `|ξ| ≥ r` has
`(2π r)^α ‖f‖² ≤ E_α(f)`. -/
theorem bernstein_lower {α : ℝ} (hα : FractionalExponent α) (f : L2C) {r : ℝ} (hr : 0 ≤ r)
    (hsupp : ∀ᵐ ξ : ℝ, |ξ| < r → ((𝓕 f : L2C) : ℝ → ℂ) ξ = 0) :
    ENNReal.ofReal ((2 * π * r) ^ α) * ‖f‖ₑ ^ (2 : ℝ) ≤ gagliardoEnergyC α f := by
  rw [gagliardoEnergyC_eq_lintegral hα, ← lintegral_enorm_sq_fourier f,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [hsupp] with ξ hξ
  by_cases h : |ξ| < r
  · rw [hξ h]; simp
  · push Not at h
    have hpow : (2 * π * r) ^ α ≤ |2 * π * ξ| ^ α := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      exact Real.rpow_le_rpow (by positivity) (by nlinarith [Real.pi_pos]) hα.1.le
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hpow) bot_le

end

end FracLap
