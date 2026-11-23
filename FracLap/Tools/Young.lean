/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.NashUltracontractivity
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# FracLap.Tools.Young

Young's convolution inequality `‖K ⋆ f‖_p ≤ ‖K‖₁ ‖f‖_p` for `1 < p < ∞` (the endpoint `p = 1` is
`lintegral_enorm_convolution_le`). The proof is Hölder's inequality with respect to the
finite measure `|K| dy` followed by Tonelli.
-/

namespace FracLap

open MeasureTheory Set Real
open scoped ENNReal Convolution

@[expose] public section

/-- **Young's inequality**, lower-integral form: for `p > 1`, `K ∈ L¹`,
`∫⁻ ‖K ⋆ f‖ₑ^p ≤ (∫⁻ ‖K‖ₑ)^p ∫⁻ ‖f‖ₑ^p`. -/
theorem lintegral_rpow_convolution_le {p : ℝ} (hp : 1 < p) {K f : ℝ → ℂ}
    (hK : AEStronglyMeasurable K volume) (hf : AEStronglyMeasurable f volume)
    (hA : ∫⁻ y, ‖K y‖ₑ ≠ ⊤) :
    ∫⁻ x, ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖ₑ ^ p ≤
      (∫⁻ y, ‖K y‖ₑ) ^ p * ∫⁻ x, ‖f x‖ₑ ^ p := by
  obtain ⟨q, hpq⟩ : ∃ q : ℝ, p.HolderConjugate q := ⟨_, Real.HolderConjugate.conjExponent hp⟩
  have hq1 : 1 < q := hpq.symm.lt
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hsum : 1 / p + 1 / q = 1 := by
    have := hpq.inv_add_inv_eq_one
    simpa [one_div] using this
  have hpq' : p / q = p - 1 := by
    have : 1 / q = 1 - 1 / p := by linarith
    field_simp at this ⊢
    nlinarith [this]
  set A : ℝ≥0∞ := ∫⁻ y, ‖K y‖ₑ with hAdef
  have hKm : AEMeasurable (fun y => ‖K y‖ₑ) volume := hK.aemeasurable.eNorm
  have key : ∀ x : ℝ, ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖ₑ ^ p ≤
      A ^ (p / q) * ∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ^ p := by
    intro x
    have h1 : ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖ₑ ≤ ∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ := by
      refine (eNorm_integral_le_lintegral_eNorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun y => ?_
      simp [eNorm_mul]
    have hfx : AEMeasurable (fun y => ‖f (x - y)‖ₑ) volume :=
      (hf.comp_quasiMeasurePreserving
        (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving).aemeasurable.eNorm
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq
      (f := fun y => ‖f (x - y)‖ₑ * ‖K y‖ₑ ^ (1 / p)) (g := fun y => ‖K y‖ₑ ^ (1 / q))
      (hfx.mul (hKm.pow_const _)) (hKm.pow_const _)
    have e1 : ∀ y : ℝ, (‖f (x - y)‖ₑ * ‖K y‖ₑ ^ (1 / p)) * ‖K y‖ₑ ^ (1 / q) =
        ‖K y‖ₑ * ‖f (x - y)‖ₑ := fun y => by
      rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hsum,
        ENNReal.rpow_one, mul_comm]
    have e2 : ∀ y : ℝ, (‖f (x - y)‖ₑ * ‖K y‖ₑ ^ (1 / p)) ^ p = ‖K y‖ₑ * ‖f (x - y)‖ₑ ^ p :=
      fun y => by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
          ENNReal.rpow_one, mul_comm]
    have e3 : ∀ y : ℝ, (‖K y‖ₑ ^ (1 / q)) ^ q = ‖K y‖ₑ := fun y => by
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
    simp only [Pi.mul_apply, e1, e2, e3] at hH
    have hΨ : (∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ) ^ p ≤
        ((∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ^ p) ^ (1 / p) * A ^ (1 / q)) ^ p :=
      ENNReal.rpow_le_rpow hH hp0.le
    calc ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖ₑ ^ p
        ≤ (∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ) ^ p := ENNReal.rpow_le_rpow h1 hp0.le
      _ ≤ _ := hΨ
      _ = A ^ (p / q) * ∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          one_div_mul_cancel hp0.ne', ENNReal.rpow_one, mul_comm]
        congr 2
        field_simp
  calc ∫⁻ x, ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖ₑ ^ p
      ≤ ∫⁻ x, A ^ (p / q) * ∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ^ p := lintegral_mono key
    _ = A ^ (p / q) * ∫⁻ x, ∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ^ p := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) hA)]
    _ = A ^ (p / q) * (A * ∫⁻ x, ‖f x‖ₑ ^ p) := by
        congr 1
        have hmeas : AEMeasurable (Function.uncurry fun (x y : ℝ) => ‖K y‖ₑ * ‖f (x - y)‖ₑ ^ p)
            (volume.prod volume) := by
          have h1 : AEMeasurable (fun q : ℝ × ℝ => ‖K q.2‖ₑ) (volume.prod volume) :=
            (hKm.comp_quasiMeasurePreserving
              (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)))
          have h2 : AEMeasurable (fun q : ℝ × ℝ => ‖f (q.1 - q.2)‖ₑ ^ p) (volume.prod volume) :=
            ((hf.comp_quasiMeasurePreserving
              (quasiMeasurePreserving_sub volume volume)).aemeasurable.eNorm).pow_const _
          exact h1.mul h2
        rw [lintegral_lintegral_swap hmeas]
        have : ∀ y : ℝ, ∫⁻ x, ‖K y‖ₑ * ‖f (x - y)‖ₑ ^ p = ‖K y‖ₑ * ∫⁻ x, ‖f x‖ₑ ^ p := fun y => by
          rw [lintegral_const_mul' _ _ eNorm_ne_top]
          congr 1
          exact lintegral_sub_right_eq_self (fun x => ‖f x‖ₑ ^ p) y
        simp_rw [this]
        rw [lintegral_mul_const'' _ hKm]
    _ = A ^ p * ∫⁻ x, ‖f x‖ₑ ^ p := by
        have h := ENNReal.rpow_add_of_nonneg (x := A) (p - 1) 1 (by linarith : (0 : ℝ) ≤ p - 1)
          (by norm_num : (0 : ℝ) ≤ 1)
        rw [← mul_assoc, hpq']
        have e : A ^ (p - 1) * A = A ^ p := by
          calc A ^ (p - 1) * A = A ^ (p - 1) * A ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
            _ = A ^ (p - 1 + 1) := h.symm
            _ = A ^ p := by rw [sub_add_cancel]
        rw [e]

/-- Young's inequality for `1 ≤ p < ∞` (the case `p = 1` is `lintegral_enorm_convolution_le`). -/
theorem lintegral_rpow_convolution_le' {p : ℝ} (hp : 1 ≤ p) {K f : ℝ → ℂ}
    (hK : AEStronglyMeasurable K volume) (hf : AEStronglyMeasurable f volume)
    (hA : ∫⁻ y, ‖K y‖ₑ ≠ ⊤) :
    ∫⁻ x, ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖ₑ ^ p ≤
      (∫⁻ y, ‖K y‖ₑ) ^ p * ∫⁻ x, ‖f x‖ₑ ^ p := by
  rcases hp.eq_or_lt with h | h
  · subst h
    simpa using lintegral_enorm_convolution_le hK hf
  · exact lintegral_rpow_convolution_le h hK hf hA

end

end FracLap
