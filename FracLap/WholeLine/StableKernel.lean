/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# FracLap.WholeLine.StableKernel

The symmetric `α`-stable heat kernel, defined analytically by Fourier inversion of the symbol
`exp (-t |ω|^α)` in angular frequency `ω`:
`P_α(x, t) = (1/π) ∫_{ω > 0} exp (-t ω^α) cos (x ω) dω`.
This is the inversion of the multiplier `exp (-t |2π ξ|^α)` used in `FourierSemigroup`.

This file contains the elementary properties (milestone M1):
- `stableKernel`: the definition.
- `integrableOn_stableSymbol`: integrability of `ω ↦ exp (-t ω^α)` on `(0, ∞)`.
- `stableKernel_neg`: spatial evenness.
- `stableKernel_self_similar`: `P(x, t) = t^(-1/α) P(x t^(-1/α), 1)`.
- `abs_stableKernel_le`: the uniform bound `|P(x, t)| ≤ P(0, t)`, with `P(0, t)` given in terms
  of the Gamma function.
-/

namespace FracLap

open MeasureTheory Real Set

@[expose] public section

/-- The symmetric `α`-stable heat kernel `P_α(x, t) = (1/π) ∫_{ω > 0} exp (-t ω^α) cos (x ω) dω`,
obtained by Fourier inversion of the symbol `exp (-t |ω|^α)`. -/
noncomputable def stableKernel (α x t : ℝ) : ℝ :=
  π⁻¹ * ∫ ω in Ioi (0 : ℝ), exp (-t * ω ^ α) * cos (x * ω)

/-- The symbol `ω ↦ exp (-t ω^α)` is integrable on `(0, ∞)` for `α, t > 0`. -/
theorem integrableOn_stableSymbol {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    IntegrableOn (fun ω : ℝ => exp (-t * ω ^ α)) (Ioi 0) := by
  simpa only [rpow_zero, one_mul] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (p := α) (b := t) (by norm_num) hα ht

/-- Spatial evenness of the stable kernel. -/
theorem stableKernel_neg (α x t : ℝ) : stableKernel α (-x) t = stableKernel α x t := by
  unfold stableKernel
  simp only [neg_mul, cos_neg]

/-- Self-similar scaling `P_α(x, t) = t^(-1/α) P_α(x t^(-1/α), 1)`. -/
theorem stableKernel_self_similar {α : ℝ} (hα : 0 < α) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    stableKernel α x t = t ^ (-1 / α) * stableKernel α (x * t ^ (-1 / α)) 1 := by
  set b : ℝ := t ^ (1 / α) with hb
  have hbpos : 0 < b := rpow_pos_of_pos ht _
  have hbinv : b⁻¹ = t ^ (-1 / α) := by
    rw [hb, ← rpow_neg_one, ← rpow_mul ht.le]
    congr 1
    ring
  have hbα : b ^ α = t := by
    rw [hb, ← rpow_mul ht.le, one_div, inv_mul_cancel₀ hα.ne', rpow_one]
  unfold stableKernel
  have key : ∫ ω in Ioi (0 : ℝ), exp (-t * ω ^ α) * cos (x * ω) =
      b⁻¹ * ∫ u in Ioi (0 : ℝ), exp (-1 * u ^ α) * cos (x * b⁻¹ * u) := by
    have h := integral_comp_mul_left_Ioi
      (fun u : ℝ => exp (-1 * u ^ α) * cos (x * b⁻¹ * u)) 0 hbpos
    rw [mul_zero, smul_eq_mul] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun ω hω => ?_
    have hω0 : 0 ≤ ω := le_of_lt hω
    rw [mul_rpow hbpos.le hω0, hbα]
    congr 2
    · ring
    · field_simp
  rw [key, hbinv]
  ring

/-- Uniform bound `|P_α(x, t)| ≤ P_α(0, t)`-type estimate in integral form. -/
theorem abs_stableKernel_le {α : ℝ} (hα : 0 < α) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    |stableKernel α x t| ≤ π⁻¹ * ∫ ω in Ioi (0 : ℝ), exp (-t * ω ^ α) := by
  unfold stableKernel
  rw [abs_mul, abs_of_pos (inv_pos.mpr pi_pos)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr pi_pos).le
  have := norm_integral_le_of_norm_le (integrableOn_stableSymbol hα ht)
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun ω : ℝ => exp (-t * ω ^ α) * cos (x * ω))
    (Filter.Eventually.of_forall fun ω => by
      simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact mul_le_of_le_one_right (exp_pos _).le (abs_cos_le_one _))
  simpa [Real.norm_eq_abs] using this

end

end FracLap
