/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.HardyLittlewood
public import FracLap.WholeLine.NashUltracontractivity

/-!
# FracLap.WholeLine.SteinMaximal

Stein's maximal inequality for the fractional heat semigroup on Schwartz data: for
`u ∈ 𝓢(ℝ; ℂ)`, `1 < p < ∞`,
`∫ (sup_{t > 0} |P_α(·, t) ⋆ u|)^p ≤ C_p ∫ |u|^p`, with `C_p = 10 p 2^(p-1) / (p-1)`.

The proof dominates every convolution with the radially decreasing, unit-mass kernel `P_α(·, t)`
by the Hardy--Littlewood maximal function (`lintegral_mul_le_hlMax`) and applies the strong type
`(p, p)` bound `hlMax_strong_type`.
-/

namespace FracLap

open Complex MeasureTheory Real Set
open scoped ENNReal NNReal SchwartzMap Convolution

@[expose] public section

/-- The stable kernel `y ↦ P_α(y, t)` is measurable (radially decreasing). -/
theorem measurable_stableKernel {α : ℝ} (hα : FractionalExponent α) {t : ℝ} (ht : 0 < t) :
    Measurable fun y : ℝ => (stableHeatKernel α hα).P y t := by
  have h : ∀ y : ℝ, (stableHeatKernel α hα).P y t =
      (fun r : ℝ => (stableHeatKernel α hα).P (max r 0) t) |y| := fun y => by
    have h1 := (stableHeatKernel α hα).radial_antitone y |y| t ht (by rw [abs_abs])
    have h2 := (stableHeatKernel α hα).radial_antitone |y| y t ht (by rw [abs_abs])
    have : max |y| 0 = |y| := max_eq_left (abs_nonneg y)
    simp only [this]
    exact le_antisymm h2 h1
  have hanti : Antitone fun r : ℝ => (stableHeatKernel α hα).P (max r 0) t := fun a b hab => by
    refine (stableHeatKernel α hα).radial_antitone _ _ t ht ?_
    rw [abs_of_nonneg (le_max_right _ _), abs_of_nonneg (le_max_right _ _)]
    exact max_le_max hab le_rfl
  have : (fun y : ℝ => (stableHeatKernel α hα).P y t) =
      (fun r : ℝ => (stableHeatKernel α hα).P (max r 0) t) ∘ (fun y => |y|) := funext h
  rw [this]
  exact hanti.measurable.comp continuous_abs.measurable

/-- **Pointwise domination**: `‖(P_α(·, t) ⋆ u)(x)‖ ≤ M(‖u‖)(x)` for every `t > 0`, `x ∈ ℝ`. -/
theorem norm_stable_conv_le_hlMax {α : ℝ} (hα : FractionalExponent α) {t : ℝ} (ht : 0 < t)
    (u : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖((fun y : ℝ => (((stableHeatKernel α hα).P y t : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (u : ℝ → ℂ)) x‖ₑ ≤ hlMax (fun y => ‖(u : ℝ → ℂ) y‖ₑ) x := by
  have hnn := (stableHeatKernel α hα).nonneg
  have hKm := measurable_stableKernel hα ht
  have hone : ∫⁻ y, ENNReal.ofReal ((stableHeatKernel α hα).P y t) = 1 := by
    have := lintegral_enorm_stableKernel hα ht
    simpa [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hnn _ t ht)] using this
  have hg : Measurable fun y : ℝ => ‖(u : ℝ → ℂ) y‖ₑ := u.continuous.measurable.eNorm
  have h1 : ‖((fun y : ℝ => (((stableHeatKernel α hα).P y t : ℝ) : ℂ)) ⋆[
      ContinuousLinearMap.mul ℂ ℂ] (u : ℝ → ℂ)) x‖ₑ ≤
      ∫⁻ y, ENNReal.ofReal ((stableHeatKernel α hα).P y t) * ‖(u : ℝ → ℂ) (x - y)‖ₑ := by
    refine (eNorm_integral_le_lintegral_eNorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    simp only [ContinuousLinearMap.mul_apply', eNorm_mul]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hnn y t ht)]
  refine h1.trans ?_
  have h2 := lintegral_mul_le_hlMax (K := fun y => (stableHeatKernel α hα).P y t) hKm
    (fun y => hnn y t ht) (fun a b hab => (stableHeatKernel α hα).radial_antitone a b t ht hab)
    (by rw [hone]; exact ENNReal.one_ne_top) hg x
  rwa [hone, one_mul] at h2

/-- **Stein's maximal inequality** for the fractional heat semigroup (Schwartz data), `p > 1`:
`∫ (sup_{t > 0} |P_α(·, t) ⋆ u|)^p ≤ (10 p 2^(p-1) / (p-1)) ∫ |u|^p`. -/
theorem stein_maximal {α : ℝ} (hα : FractionalExponent α) {p : ℝ} (hp : 1 < p) (u : 𝓢(ℝ, ℂ)) :
    ∫⁻ x, (⨆ t : {t : ℝ // 0 < t},
        ‖((fun y : ℝ => (((stableHeatKernel α hα).P y t.1 : ℝ) : ℂ)) ⋆[
          ContinuousLinearMap.mul ℂ ℂ] (u : ℝ → ℂ)) x‖ₑ) ^ p ≤
      ENNReal.ofReal (10 * p * 2 ^ (p - 1) / (p - 1)) * ∫⁻ y, ‖(u : ℝ → ℂ) y‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have hg : ∀ y : ℝ, ‖(u : ℝ → ℂ) y‖ₑ = ENNReal.ofReal ‖(u : ℝ → ℂ) y‖ := fun y =>
    (ofReal_norm _).symm
  have hdom : ∀ x : ℝ, (⨆ t : {t : ℝ // 0 < t},
      ‖((fun y : ℝ => (((stableHeatKernel α hα).P y t.1 : ℝ) : ℂ)) ⋆[
        ContinuousLinearMap.mul ℂ ℂ] (u : ℝ → ℂ)) x‖ₑ) ≤
      hlMax (fun y => ENNReal.ofReal ‖(u : ℝ → ℂ) y‖) x := fun x => by
    refine iSup_le fun t => ?_
    have := norm_stable_conv_le_hlMax hα t.2 u x
    simpa only [hg] using this
  have hint : ∫⁻ y, ENNReal.ofReal ‖(u : ℝ → ℂ) y‖ ≠ ⊤ := by
    simp_rw [← hg]
    exact u.integrable.hasFiniteIntegral.ne
  calc ∫⁻ x, (⨆ t : {t : ℝ // 0 < t},
        ‖((fun y : ℝ => (((stableHeatKernel α hα).P y t.1 : ℝ) : ℂ)) ⋆[
          ContinuousLinearMap.mul ℂ ℂ] (u : ℝ → ℂ)) x‖ₑ) ^ p
      ≤ ∫⁻ x, hlMax (fun y => ENNReal.ofReal ‖(u : ℝ → ℂ) y‖) x ^ p :=
        lintegral_mono fun x => ENNReal.rpow_le_rpow (hdom x) hp0.le
    _ ≤ ENNReal.ofReal (10 * p * 2 ^ (p - 1) / (p - 1)) *
          ∫⁻ y, ENNReal.ofReal ‖(u : ℝ → ℂ) y‖ ^ p :=
        hlMax_strong_type hp u.continuous.measurable.norm (fun x => norm_nonneg _) hint
    _ = _ := by simp_rw [← hg]

end

end FracLap
