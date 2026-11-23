/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.GagliardoSymbolExact

/-!
# FracLap.Tools.Interpolation

Interpolation of fractional energies (Lisini--Mainini--Segatti, `‖u‖_{H^{r₁}} ≤ ‖u‖^{1-θ}_{H^{r₀}}
‖u‖^θ_{H^{r₂}}` in homogeneous form): for `0 < a, c < 2`, `θ ∈ [0, 1]` and `b = (1-θ) a + θ c`,
`E_b(f) ≤ E_a(f)^(1-θ) E_c(f)^θ` for every `f ∈ L²(ℝ; ℂ)`.

- `lintegral_interpolation`: Hölder interpolation for weighted lower integrals.
- `gagliardoEnergyC_interpolation`: the energy interpolation inequality.
-/

namespace FracLap

open Complex FourierTransform MeasureTheory Real Set
open scoped ENNReal

@[expose] public section

/-- **Hölder interpolation for weighted lower integrals**: if `w₁ ≤ w₀^(1-θ) w₂^θ` pointwise then
`∫ w₁ F ≤ (∫ w₀ F)^(1-θ) (∫ w₂ F)^θ` for `θ ∈ [0, 1]`. -/
theorem lintegral_interpolation {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {w₀ w₁ w₂ F : X → ℝ≥0∞} (hw₀ : AEMeasurable w₀ μ) (hw₂ : AEMeasurable w₂ μ)
    (hF : AEMeasurable F μ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hw : ∀ x, w₁ x ≤ w₀ x ^ (1 - θ) * w₂ x ^ θ) :
    ∫⁻ x, w₁ x * F x ∂μ ≤
      (∫⁻ x, w₀ x * F x ∂μ) ^ (1 - θ) * (∫⁻ x, w₂ x * F x ∂μ) ^ θ := by
  rcases hθ0.eq_or_lt with rfl | hθpos
  · simp only [sub_zero, ENNReal.rpow_one, ENNReal.rpow_zero, mul_one] at hw ⊢
    exact lintegral_mono fun x => mul_le_mul_of_nonneg_right (hw x) bot_le
  rcases hθ1.eq_or_lt with rfl | hθlt
  · simp only [sub_self, ENNReal.rpow_zero, ENNReal.rpow_one, one_mul] at hw ⊢
    exact lintegral_mono fun x => mul_le_mul_of_nonneg_right (hw x) bot_le
  have h1θ : 0 < 1 - θ := by linarith
  have hp : (1 / (1 - θ)).HolderConjugate (1 / θ) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ h1θ]
      linarith
    · field_simp
      ring
  have hpt : ∀ x, w₁ x * F x ≤ (w₀ x * F x) ^ (1 - θ) * (w₂ x * F x) ^ θ := by
    intro x
    calc w₁ x * F x ≤ (w₀ x ^ (1 - θ) * w₂ x ^ θ) * F x :=
          mul_le_mul_of_nonneg_right (hw x) bot_le
      _ = (w₀ x * F x) ^ (1 - θ) * (w₂ x * F x) ^ θ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ h1θ.le, ENNReal.mul_rpow_of_nonneg _ _ hθpos.le]
          have : F x = F x ^ (1 - θ) * F x ^ θ := by
            rw [← ENNReal.rpow_add_of_nonneg _ _ h1θ.le hθpos.le]
            simp
          calc w₀ x ^ (1 - θ) * w₂ x ^ θ * F x
              = w₀ x ^ (1 - θ) * w₂ x ^ θ * (F x ^ (1 - θ) * F x ^ θ) := by rw [← this]
            _ = _ := by ring
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hp
    (f := fun x => (w₀ x * F x) ^ (1 - θ)) (g := fun x => (w₂ x * F x) ^ θ)
    ((hw₀.mul hF).pow_const _) ((hw₂.mul hF).pow_const _)
  have e1 : ∀ x, ((w₀ x * F x) ^ (1 - θ)) ^ (1 / (1 - θ)) = w₀ x * F x := by
    intro x
    rw [← ENNReal.rpow_mul]
    have : (1 - θ) * (1 / (1 - θ)) = 1 := by field_simp
    rw [this, ENNReal.rpow_one]
  have e2 : ∀ x, ((w₂ x * F x) ^ θ) ^ (1 / θ) = w₂ x * F x := by
    intro x
    rw [← ENNReal.rpow_mul]
    have : θ * (1 / θ) = 1 := by field_simp
    rw [this, ENNReal.rpow_one]
  simp only [Pi.mul_apply, e1, e2, one_div_one_div] at hHolder
  exact (lintegral_mono hpt).trans hHolder

/-- **Interpolation of fractional energies**: for `0 < a, c < 2`, `θ ∈ [0, 1]` and
`b = (1 - θ) a + θ c`, `E_b(f) ≤ E_a(f)^(1-θ) E_c(f)^θ` for every `f ∈ L²(ℝ; ℂ)`. -/
theorem gagliardoEnergyC_interpolation {a b c θ : ℝ} (ha : FractionalExponent a)
    (hb : FractionalExponent b) (hc : FractionalExponent c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hbθ : b = (1 - θ) * a + θ * c) (f : L2C) :
    gagliardoEnergyC b f ≤ gagliardoEnergyC a f ^ (1 - θ) * gagliardoEnergyC c f ^ θ := by
  rw [gagliardoEnergyC_eq_lintegral hb, gagliardoEnergyC_eq_lintegral ha,
    gagliardoEnergyC_eq_lintegral hc]
  have hFm : Measurable fun ξ : ℝ => ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) :=
    ((Lp.stronglyMeasurable (𝓕 f : L2C)).measurable.eNorm).pow_const _
  have hwm : ∀ r : ℝ, Measurable fun ξ : ℝ => ENNReal.ofReal (|2 * π * ξ| ^ r) := fun r =>
    ENNReal.measurable_ofReal.comp
      (((continuous_abs.comp (continuous_const.mul continuous_id)).measurable).pow_const r)
  refine lintegral_interpolation (volume : Measure ℝ) (w₀ := fun ξ => ENNReal.ofReal
    (|2 * π * ξ| ^ a)) (w₂ := fun ξ => ENNReal.ofReal (|2 * π * ξ| ^ c))
    (F := fun ξ => ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ)) (hwm a).aemeasurable
    (hwm c).aemeasurable hFm.aemeasurable hθ0 hθ1 fun ξ => ?_
  have hnn : 0 ≤ |2 * π * ξ| := abs_nonneg _
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hnn _) (by linarith),
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hnn _) hθ0,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.rpow_nonneg hnn _) _)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rcases eq_or_lt_of_le hnn with h0 | hpos
  · rw [← h0]
    have hb0 : 0 < b := hb.1
    rw [Real.zero_rpow hb0.ne']
    rcases hθ0.eq_or_lt with rfl | hθpos
    · simp [Real.zero_rpow ha.1.ne']
    · rcases hθ1.eq_or_lt with rfl | hθlt
      · simp [Real.zero_rpow hc.1.ne']
      · rw [Real.zero_rpow ha.1.ne', Real.zero_rpow hc.1.ne',
          Real.zero_rpow (by linarith : (1 - θ) ≠ 0), Real.zero_rpow hθpos.ne', zero_mul]
  · rw [← Real.rpow_mul hpos.le, ← Real.rpow_mul hpos.le, ← Real.rpow_add hpos, hbθ]
    congr 1
    ring

end

end FracLap
