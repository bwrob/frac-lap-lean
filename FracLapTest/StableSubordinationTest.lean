/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.StableSubordination
import Mathlib.Tactic.Positivity

/-!
# FracLapTest.StableSubordinationTest

Closed-form evaluations and negative counterexamples for `FracLap.WholeLine.StableSubordination`:
the Gaussian-regularized transform of the constant mixture, preservation of Gaussian monotonicity
under products, and a function that is not Gaussian monotone.
-/

namespace FracLapTest

open FracLap MeasureTheory Real

/-- The constant mixture `1` is the mixture of the unit point mass at `0`. -/
example : gaussMixture (Measure.dirac (0 : NNReal)) 3 = 1 := gaussMixture_dirac_zero 3

/-- Closed form: the regularized transform of the constant `1` is a Gaussian in `a`. -/
example (σ a : ℝ) (hσ : 0 < σ) :
    gaussCos σ a (fun _ => 1) = √(π / σ) * exp (-a ^ 2 / (4 * σ)) := by
  unfold gaussCos
  simpa only [mul_one] using integral_exp_neg_mul_sq_mul_cos hσ a

/-- Products of constant mixtures are Gaussian monotone. -/
example : IsGaussMonotone fun _ => (2 : ℝ) * 3 :=
  ((IsGaussMix.const (by norm_num : (0 : ℝ) ≤ 2)).mul
    (IsGaussMix.const (by norm_num : (0 : ℝ) ≤ 3))).isGaussMonotone

/-- Negative counterexample: the constant `-1` is not Gaussian monotone, so the nonnegativity
requirement is not vacuous. -/
example : ¬ IsGaussMonotone fun _ => (-1 : ℝ) := by
  intro h
  have h0 := (h 1 0 0 one_pos le_rfl le_rfl).1
  unfold gaussCos at h0
  have := integral_exp_neg_mul_sq_mul_cos (b := 1) one_pos 0
  have hneg : ∫ ξ : ℝ, exp (-1 * ξ ^ 2) * cos (0 * ξ) * (-1 : ℝ) =
      -(√(π / 1) * exp (-0 ^ 2 / (4 * 1))) := by
    rw [← this, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp
  rw [hneg] at h0
  have hp : 0 < √(π / 1) * exp (-0 ^ 2 / (4 * 1)) := by positivity
  linarith

end FracLapTest
