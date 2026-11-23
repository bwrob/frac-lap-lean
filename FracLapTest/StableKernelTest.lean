/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.ClassicalKernels
public import FracLap.WholeLine.StableKernel
import Mathlib.Tactic.Positivity

/-!
# FracLapTest.StableKernelTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.WholeLine.StableKernel`.
-/

namespace FracLapTest

open FracLap MeasureTheory Real Set

/-- Closed form at the origin for `α = 1`: `P₁(0, 1) = 1 / π`, the Cauchy value. -/
example : stableKernel 1 0 1 = cauchyHeatKernel.P 0 1 := by
  have h : ∫ ω in Ioi (0 : ℝ), exp (-1 * ω ^ (1 : ℝ)) = 1 := by
    simpa only [rpow_one, neg_mul, one_mul] using integral_exp_neg_Ioi_zero
  have hc : cauchyHeatKernel.P 0 1 = 1 / π := by
    simp [cauchyHeatKernel]
  simp only [stableKernel, zero_mul, cos_zero, mul_one, h, hc]
  ring

/-- Closed form at the origin for `α = 2`: `P₂(0, 1) = 1 / (2 √π)`, the Gaussian value. -/
example : stableKernel 2 0 1 = gaussianHeatKernel.P 0 1 := by
  have h : ∫ ω in Ioi (0 : ℝ), exp (-1 * ω ^ (2 : ℝ)) = √π / 2 := by
    have := integral_gaussian_Ioi 1
    simpa only [rpow_two, neg_mul, one_mul, div_one] using this
  have hs : √(4 * π) = 2 * √π := by
    rw [show (4 : ℝ) * π = 2 ^ 2 * π by ring, sqrt_mul (by positivity), sqrt_sq (by norm_num)]
  have hπ : (0 : ℝ) < √π := sqrt_pos.mpr pi_pos
  have hsq : √π * √π = π := mul_self_sqrt pi_pos.le
  simp only [stableKernel, zero_mul, cos_zero, mul_one, h, gaussianHeatKernel, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div, exp_zero]
  rw [hs]
  field_simp
  nlinarith [hsq]

/-- Self-similarity is not vacuous: the scaled value differs from the unscaled one in general,
so the exponent `-1 / α` genuinely matters at `α = 1`, `x = 0`, `t = 4`. -/
example : stableKernel 1 0 4 = (1 / 4 : ℝ) * stableKernel 1 0 1 := by
  rw [stableKernel_self_similar one_pos 0 (by norm_num : (0 : ℝ) < 4)]
  simp [rpow_neg_one]

end FracLapTest
