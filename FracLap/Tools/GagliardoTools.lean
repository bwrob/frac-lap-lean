/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.HalfLine.RestrictedDirichlet
public import FracLap.Tools.StroockVaropoulos

/-!
# FracLap.Tools.GagliardoTools

The nonlocal tools of `FracLap.Tools` specialized to the Gagliardo jump measure
`(C(α) / (2 |x - y|^(1 + α))) dx dy` of the fractional Laplacian:

- `gagliardoMeasure_swap`: the Gagliardo measure is invariant under `(x, y) ↦ (y, x)`.
- `gagliardo_sv_lintegral`: Stroock--Varopoulos for the Gagliardo energy (lower-integral form).
- `gagliardo_sv_integral`: Stroock--Varopoulos for the Gagliardo measure (real form).
- `gagliardo_dissipation_nonneg`: dissipativity of monotone functions of `u` along the fractional
  Laplacian, `∬ (u x - u y) φ(u x) dμ_α ≥ 0`.
-/

namespace FracLap

open MeasureTheory
open scoped ENNReal

@[expose] public section

/-- The Gagliardo weight is symmetric. -/
theorem gagliardoWeight_swap (α : ℝ) (p : ℝ × ℝ) :
    gagliardoWeight α p.swap = gagliardoWeight α p := by
  unfold gagliardoWeight
  simp only [Prod.fst_swap, Prod.snd_swap, abs_sub_comm p.2 p.1]

/-- **The Gagliardo measure is swap-invariant.** -/
theorem gagliardoMeasure_swap (α : ℝ) :
    MeasurePreserving Prod.swap (gagliardoMeasure α) (gagliardoMeasure α) := by
  refine ⟨measurable_swap, Measure.ext fun s hs => ?_⟩
  have hpre : MeasurableSet (Prod.swap ⁻¹' s) := measurable_swap hs
  rw [Measure.map_apply measurable_swap hs]
  unfold gagliardoMeasure
  rw [withDensity_apply _ hpre, withDensity_apply _ hs]
  have hmp : MeasurePreserving (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ))
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) :=
    Measure.measurePreserving_swap
  have := hmp.setLIntegral_comp_preimage_emb (MeasurableEquiv.prodComm.measurableEmbedding)
    (gagliardoWeight α) s
  have e : (⇑(MeasurableEquiv.prodComm (α := ℝ) (β := ℝ))) = Prod.swap := rfl
  rw [e] at this
  simp only [gagliardoWeight_swap] at this
  exact this

/-- **Stroock--Varopoulos for the Gagliardo energy** (lower-integral form), for `q > 1`. -/
theorem gagliardo_sv_lintegral (α : ℝ) {q : ℝ} (hq : 1 < q) (u : ℝ → ℝ) :
    ENNReal.ofReal (4 * (q - 1) / q ^ 2) *
        ∫⁻ z : ℝ × ℝ, gagliardoWeight α z *
          ENNReal.ofReal ((spow (q / 2) (u z.1) - spow (q / 2) (u z.2)) ^ 2)
          ∂((volume : Measure ℝ).prod volume) ≤
      ∫⁻ z : ℝ × ℝ, gagliardoWeight α z * ENNReal.ofReal
        ((u z.1 - u z.2) * (spow (q - 1) (u z.1) - spow (q - 1) (u z.2)))
          ∂((volume : Measure ℝ).prod volume) :=
  sv_lintegral hq _ _ u

/-- **Stroock--Varopoulos for the Gagliardo measure** (real form). -/
theorem gagliardo_sv_integral (α : ℝ) {q : ℝ} (hq : 1 < q) (u : ℝ → ℝ)
    (h1 : Integrable (fun z : ℝ × ℝ => (u z.1 - u z.2) * spow (q - 1) (u z.1))
      (gagliardoMeasure α))
    (h2 : Integrable (fun z : ℝ × ℝ => (u z.1 - u z.2) * spow (q - 1) (u z.2))
      (gagliardoMeasure α))
    (h3 : Integrable
      (fun z : ℝ × ℝ => (spow (q / 2) (u z.1) - spow (q / 2) (u z.2)) ^ 2)
      (gagliardoMeasure α)) :
    2 * (q - 1) / q ^ 2 *
        ∫ z, (spow (q / 2) (u z.1) - spow (q / 2) (u z.2)) ^ 2 ∂(gagliardoMeasure α) ≤
      ∫ z, (u z.1 - u z.2) * spow (q - 1) (u z.1) ∂(gagliardoMeasure α) :=
  sv_integral hq (gagliardoMeasure_swap α) u h1 h2 h3

/-- **Dissipativity of monotone functions of `u` along the fractional Laplacian.** -/
theorem gagliardo_dissipation_nonneg (α : ℝ) (u : ℝ → ℝ) {φ : ℝ → ℝ} (hφ : Monotone φ)
    (h1 : Integrable (fun z : ℝ × ℝ => (u z.1 - u z.2) * φ (u z.1)) (gagliardoMeasure α))
    (h2 : Integrable (fun z : ℝ × ℝ => (u z.1 - u z.2) * φ (u z.2)) (gagliardoMeasure α)) :
    0 ≤ ∫ z, (u z.1 - u z.2) * φ (u z.1) ∂(gagliardoMeasure α) :=
  integral_sub_mul_comp_nonneg (gagliardoMeasure_swap α) u hφ h1 h2

end

end FracLap
