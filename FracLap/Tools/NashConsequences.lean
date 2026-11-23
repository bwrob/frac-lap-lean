/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.Nash
public import FracLap.WholeLine.GagliardoSymbolExact

/-!
# FracLap.Tools.NashConsequences

Consequences of the exact Fourier symbol `Λ_α(ξ) = |2π ξ|^α` (`gagliardoSymbol_exact`):

- `gagliardoSymbol_one_eq`: `Λ_α(1) = (2π)^α`.
- `fractional_nash_explicit`: the fractional Nash inequality with the fully explicit constant
  `3^(1+α) (2π)^(-α)`.
- `poincare_friedrichs`: for `f ∈ L²(ℝ; ℂ)` vanishing outside a set `Ω` of finite measure,
  `‖f‖₂² ≤ 2 (2 |Ω| / π)^α E_α(f)` (fractional Friedrichs--Poincaré inequality, whole-space energy).
-/

namespace FracLap

open Complex FourierTransform MeasureTheory Real Set
open scoped ENNReal

@[expose] public section

/-- `Λ_α(1) = (2π)^α`. -/
theorem gagliardoSymbol_one_eq {α : ℝ} (hα : FractionalExponent α) :
    gagliardoSymbol α 1 = ENNReal.ofReal ((2 * π) ^ α) := by
  rw [gagliardoSymbol_exact hα, mul_one, abs_of_pos (by positivity)]

/-- **Fractional Nash inequality with explicit constant** (`d = 1`, `0 < α < 2`):
`(‖f‖₂²)^(1+α) ≤ 3^(1+α) (2π)^(-α) E_α(f) (‖f‖₁²)^α`. -/
theorem fractional_nash_explicit {α : ℝ} (hα : FractionalExponent α) (f : L2C)
    (hf1 : Integrable (f : ℝ → ℂ)) (hE : gagliardoEnergyC α f ≠ ∞) :
    (‖f‖ ^ 2) ^ (1 + α) ≤ 3 ^ (1 + α) * (((2 * π) ^ α)⁻¹ * (gagliardoEnergyC α f).toReal) *
      ((∫ x, ‖(f : ℝ → ℂ) x‖) ^ 2) ^ α := by
  have h := fractional_nash hα f hf1 hE
  rwa [gagliardoSymbol_one_eq hα, ENNReal.toReal_ofReal (by positivity)] at h

/-- **Cauchy--Schwarz for lower integrals**: `(∫⁻ g)² ≤ μ(univ) ∫⁻ g²`. -/
theorem lintegral_rpow_two_le {X : Type*} [MeasurableSpace X] (μ : Measure X) {g : X → ℝ≥0∞}
    (hg : AEMeasurable g μ) :
    (∫⁻ x, g x ∂μ) ^ (2 : ℝ) ≤ μ univ * ∫⁻ x, g x ^ (2 : ℝ) ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hg
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  calc (∫⁻ x, g x ∂μ) ^ (2 : ℝ)
      ≤ ((∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) * μ univ ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = μ univ * ∫⁻ x, g x ^ (2 : ℝ) ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num
        ring

/-- **Fractional Friedrichs--Poincaré inequality** (whole-space energy). If `f ∈ L²(ℝ; ℂ)` vanishes
almost everywhere outside a measurable set `Ω` of finite measure, then for `0 < α < 2`,
`‖f‖₂² ≤ 2 (2 |Ω| / π)^α E_α(f)`. -/
theorem poincare_friedrichs {α : ℝ} (hα : FractionalExponent α) (f : L2C) {Ω : Set ℝ}
    (hΩm : MeasurableSet Ω) (hΩ : volume Ω < ∞) (hf0 : ∀ᵐ x, x ∉ Ω → (f : ℝ → ℂ) x = 0) :
    ‖f‖ₑ ^ (2 : ℝ) ≤ 2 * ENNReal.ofReal ((2 * (volume Ω).toReal / π) ^ α) *
      gagliardoEnergyC α f := by
  set V := (volume Ω).toReal with hV
  have hS : ‖f‖ₑ ^ (2 : ℝ) = ∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) := (lintegral_enorm_sq_eq f).symm
  have hSfin : ‖f‖ₑ ^ (2 : ℝ) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) eNorm_ne_top
  by_cases hV0 : V = 0
  · -- `Ω` is null, so `f = 0` almost everywhere
    have hnull : volume Ω = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).mp hV0 with h | h
      · exact h
      · exact absurd h hΩ.ne
    have hae : ∀ᵐ x : ℝ, x ∉ Ω := measure_eq_zero_iff_ae_notMem.mp hnull
    have h0 : ∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hf0, hae] with x hx hxΩ
      simp [hx hxΩ]
    rw [hS, h0]
    simp
  have hVpos : 0 < V := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hV0)
  set R : ℝ := 1 / (4 * V) with hR
  have hRpos : 0 < R := by positivity
  -- `L¹` norm by Cauchy--Schwarz on `Ω`
  have hmeas : Measurable fun x => ‖(f : ℝ → ℂ) x‖ₑ :=
    (Lp.stronglyMeasurable f).measurable.eNorm
  have hN1 : ∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ = ∫⁻ x in Ω, ‖(f : ℝ → ℂ) x‖ₑ := by
    rw [← lintegral_indicator hΩm]
    refine lintegral_congr_ae ?_
    filter_upwards [hf0] with x hx
    by_cases hxΩ : x ∈ Ω
    · simp [hxΩ]
    · simp [hxΩ, hx hxΩ]
  have hCS := lintegral_rpow_two_le (volume.restrict Ω) hmeas.aemeasurable
  rw [Measure.restrict_apply_univ] at hCS
  have hS' : ∫⁻ x in Ω, ‖(f : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) ≤ ‖f‖ₑ ^ (2 : ℝ) := by
    rw [hS]
    exact setLIntegral_le_lintegral _ _
  have hN1sq : (∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ) ^ (2 : ℝ) ≤ ENNReal.ofReal V * ‖f‖ₑ ^ (2 : ℝ) := by
    rw [hN1]
    refine hCS.trans ?_
    rw [hV, ENNReal.ofReal_toReal hΩ.ne]
    exact mul_le_mul_right hS' _
  have hN1fin : ∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ≠ ∞ := by
    intro h
    rw [h, ENNReal.top_rpow_of_pos (by norm_num)] at hN1sq
    exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSfin) (top_le_iff.mp hN1sq)
  have hf1 : Integrable (f : ℝ → ℂ) :=
    ⟨(Lp.stronglyMeasurable f).aestronglyMeasurable, hN1fin.lt_top⟩
  have hcut := nash_cut hα hRpos f hf1
  rw [gagliardoSymbol_one_eq hα] at hcut
  -- absorb the `L¹` term
  have hhalf : ENNReal.ofReal (2 * R) * (∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ) ^ (2 : ℝ) ≤
      2⁻¹ * ‖f‖ₑ ^ (2 : ℝ) := by
    calc ENNReal.ofReal (2 * R) * (∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ) ^ (2 : ℝ)
        ≤ ENNReal.ofReal (2 * R) * (ENNReal.ofReal V * ‖f‖ₑ ^ (2 : ℝ)) :=
          mul_le_mul_right hN1sq _
      _ = ENNReal.ofReal (2 * R * V) * ‖f‖ₑ ^ (2 : ℝ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      _ = 2⁻¹ * ‖f‖ₑ ^ (2 : ℝ) := by
          congr 1
          have : 2 * R * V = 1 / 2 := by rw [hR]; field_simp; ring
          rw [this, ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
            show ENNReal.ofReal 2 = 2 by simp, one_div]
  set T := (ENNReal.ofReal (R ^ α) * ENNReal.ofReal ((2 * π) ^ α))⁻¹ * gagliardoEnergyC α f
  have hle : ‖f‖ₑ ^ (2 : ℝ) ≤ 2⁻¹ * ‖f‖ₑ ^ (2 : ℝ) + T := hcut.trans (add_le_add hhalf le_rfl)
  have hSdiv : ‖f‖ₑ ^ (2 : ℝ) = 2⁻¹ * ‖f‖ₑ ^ (2 : ℝ) + 2⁻¹ * ‖f‖ₑ ^ (2 : ℝ) := by
    rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
  have h2 : 2⁻¹ * ‖f‖ₑ ^ (2 : ℝ) ≤ T := by
    have hne : 2⁻¹ * ‖f‖ₑ ^ (2 : ℝ) ≠ ∞ :=
      ENNReal.mul_ne_top (by simp) hSfin
    have hh : 2⁻¹ * ‖f‖ₑ ^ (2 : ℝ) + 2⁻¹ * ‖f‖ₑ ^ (2 : ℝ) ≤ 2⁻¹ * ‖f‖ₑ ^ (2 : ℝ) + T :=
      hSdiv.symm.le.trans hle
    exact (ENNReal.add_le_add_iff_left hne).mp hh
  have hconst : (ENNReal.ofReal (R ^ α) * ENNReal.ofReal ((2 * π) ^ α))⁻¹ =
      ENNReal.ofReal ((2 * V / π) ^ α) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow hRpos.le (by positivity),
      ← ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    rw [← Real.inv_rpow (by positivity)]
    congr 1
    rw [hR]
    field_simp
    norm_num
  calc ‖f‖ₑ ^ (2 : ℝ) = 2 * (2⁻¹ * ‖f‖ₑ ^ (2 : ℝ)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ 2 * T := mul_le_mul_right h2 _
    _ = 2 * ENNReal.ofReal ((2 * V / π) ^ α) * gagliardoEnergyC α f := by
        simp only [T, hconst]
        ring

end

end FracLap
