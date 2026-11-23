/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.StableKernel
public import FracLap.WholeLine.StableLevy

/-!
# FracLap.WholeLine.StableKernelPositivity

Positivity and radial monotonicity of the stable kernel, proved by Fourier inversion from the
Gaussian monotonicity of the symbol `exp (-t |ω|^α)` (`isGaussMonotone_stableSymbol`).

- `integrable_stableSymbol`: the symbol is integrable on `ℝ`.
- `stableKernel_eq_integral`: `P_α(x, t) = (2π)⁻¹ ∫_ℝ exp (-t |ω|^α) cos (x ω) dω`.
- `tendsto_gaussCos_stableSymbol`: the Gaussian regularization converges to the cosine transform.
- `stableKernel_nonneg`, `stableKernel_antitone`: positivity and radial monotonicity for
  `0 < α < 2`.
-/

namespace FracLap

open MeasureTheory Set Filter Topology Real

@[expose] public section

/-- The stable symbol `ω ↦ exp (-t |ω|^α)` is integrable on `ℝ`. -/
theorem integrable_stableSymbol {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    Integrable fun ω : ℝ => exp (-t * |ω| ^ α) := by
  have h0 : IntegrableOn (fun ω : ℝ => exp (-t * ω ^ α)) (Ioi 0) := integrableOn_stableSymbol hα ht
  have hu : Integrable ((Ioi (0 : ℝ)).indicator fun ω : ℝ => exp (-t * ω ^ α)) :=
    (integrable_indicator_iff measurableSet_Ioi).2 h0
  have hv := hu.comp_neg
  refine (hu.add hv).congr ?_
  have hne : ∀ᵐ ω : ℝ, ω ≠ 0 := by simp [ae_iff]
  filter_upwards [hne] with ω hω
  rcases lt_or_gt_of_ne hω with h | h
  · have e1 : (Ioi (0 : ℝ)).indicator (fun ω : ℝ => exp (-t * ω ^ α)) ω = 0 :=
      indicator_of_notMem (by simpa using h.le) _
    have e2 : (Ioi (0 : ℝ)).indicator (fun ω : ℝ => exp (-t * ω ^ α)) (-ω) =
        exp (-t * (-ω) ^ α) := indicator_of_mem (mem_Ioi.2 (neg_pos.2 h)) _
    simp only [Pi.add_apply, e1, e2, zero_add, abs_of_neg h]
  · have e1 : (Ioi (0 : ℝ)).indicator (fun ω : ℝ => exp (-t * ω ^ α)) ω =
        exp (-t * ω ^ α) := indicator_of_mem (mem_Ioi.2 h) _
    have e2 : (Ioi (0 : ℝ)).indicator (fun ω : ℝ => exp (-t * ω ^ α)) (-ω) = 0 :=
      indicator_of_notMem (by simpa using h.le) _
    simp only [Pi.add_apply, e1, e2, add_zero, abs_of_pos h]

/-- `P_α(x, t) = (2π)⁻¹ ∫_ℝ cos (x ω) exp (-t |ω|^α) dω`. -/
theorem stableKernel_eq_integral {α : ℝ} (x t : ℝ) :
    stableKernel α x t = (2 * π)⁻¹ * ∫ ω : ℝ, cos (x * ω) * exp (-t * |ω| ^ α) := by
  have h := integral_comp_abs (f := fun y : ℝ => exp (-t * y ^ α) * cos (x * y))
  have hcos : ∀ ω : ℝ, cos (x * |ω|) = cos (x * ω) := by
    intro ω
    rcases abs_choice ω with h | h
    · rw [h]
    · rw [h, mul_neg, cos_neg]
  have h2 : ∫ ω : ℝ, cos (x * ω) * exp (-t * |ω| ^ α) =
      2 * ∫ y in Ioi (0 : ℝ), exp (-t * y ^ α) * cos (x * y) := by
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hcos]
    ring
  rw [h2]
  unfold stableKernel
  have : (2 * π) ≠ 0 := by positivity
  field_simp

/-- The Gaussian regularization converges to the cosine transform of the symbol. -/
theorem tendsto_gaussCos_stableSymbol {α t : ℝ} (hα : 0 < α) (ht : 0 < t) (a : ℝ) :
    Tendsto (fun n : ℕ => gaussCos (1 / ((n : ℝ) + 1)) a fun ω => exp (-t * |ω| ^ α)) atTop
      (𝓝 (∫ ω : ℝ, cos (a * ω) * exp (-t * |ω| ^ α))) := by
  have hΦ := integrable_stableSymbol hα ht
  unfold gaussCos
  have hlim : ∀ ω : ℝ, Tendsto (fun n : ℕ => exp (-(1 / ((n : ℝ) + 1)) * ω ^ 2) * cos (a * ω) *
      exp (-t * |ω| ^ α)) atTop (𝓝 (cos (a * ω) * exp (-t * |ω| ^ α))) := by
    intro ω
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun n : ℕ => exp (-(1 / ((n : ℝ) + 1)) * ω ^ 2)) atTop
        (𝓝 (exp (-0 * ω ^ 2))) :=
      (Real.continuous_exp.tendsto _).comp ((h0.neg).mul_const _)
    have h2 := (h1.mul_const (cos (a * ω))).mul_const (exp (-t * |ω| ^ α))
    simpa using h2
  refine tendsto_integral_of_dominated_convergence (fun ω => exp (-t * |ω| ^ α)) (fun n => ?_)
    hΦ (fun n => ?_) (Filter.Eventually.of_forall hlim)
  · exact ((by fun_prop : Continuous fun ω : ℝ => exp (-(1 / ((n : ℝ) + 1)) * ω ^ 2) *
      cos (a * ω)).aestronglyMeasurable).mul hΦ.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (exp_pos _), abs_of_pos (exp_pos _)]
    have h1 : exp (-(1 / ((n : ℝ) + 1)) * ω ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      nlinarith [sq_nonneg ω]
    have h2 := abs_cos_le_one (a * ω)
    have h3 := exp_pos (-t * |ω| ^ α)
    calc exp (-(1 / ((n : ℝ) + 1)) * ω ^ 2) * |cos (a * ω)| * exp (-t * |ω| ^ α)
        ≤ 1 * 1 * exp (-t * |ω| ^ α) := by gcongr
      _ = exp (-t * |ω| ^ α) := by ring

/-- The stable kernel depends only on `|x|`. -/
theorem stableKernel_abs (α x t : ℝ) : stableKernel α |x| t = stableKernel α x t := by
  rcases abs_choice x with h | h
  · rw [h]
  · rw [h, stableKernel_neg]

/-- **Positivity of the stable kernel** for `0 < α < 2`. -/
theorem stableKernel_nonneg {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ stableKernel α x t := by
  rw [← stableKernel_abs, stableKernel_eq_integral]
  refine mul_nonneg (by positivity) ?_
  refine ge_of_tendsto' (tendsto_gaussCos_stableSymbol hα0 ht |x|) fun n => ?_
  exact (isGaussMonotone_stableSymbol hα0 hα2 ht (1 / ((n : ℝ) + 1)) 0 |x| (by positivity)
    le_rfl (abs_nonneg x)).1

/-- **Radial monotonicity of the stable kernel** for `0 < α < 2`: `P_α(b, t) ≤ P_α(a, t)` whenever
`|a| ≤ |b|`. -/
theorem stableKernel_antitone {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {t : ℝ} (ht : 0 < t)
    {a b : ℝ} (hab : |a| ≤ |b|) : stableKernel α b t ≤ stableKernel α a t := by
  rw [← stableKernel_abs α b, ← stableKernel_abs α a, stableKernel_eq_integral,
    stableKernel_eq_integral]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_of_tendsto_of_tendsto' (tendsto_gaussCos_stableSymbol hα0 ht |b|)
    (tendsto_gaussCos_stableSymbol hα0 ht |a|) fun n => ?_
  exact (isGaussMonotone_stableSymbol hα0 hα2 ht (1 / ((n : ℝ) + 1)) |a| |b| (by positivity)
    (abs_nonneg a) hab).2

end

end FracLap
