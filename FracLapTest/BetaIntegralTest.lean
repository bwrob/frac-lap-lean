/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.BetaIntegral

/-!
# FracLapTest.BetaIntegralTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.Tools.BetaIntegral`.
-/

namespace FracLapTest

open FracLap Real

/-- `B(1, 1) = 1`. -/
example : ∫ x in (0 : ℝ)..1, x ^ ((1 : ℝ) - 1) * (1 - x) ^ ((1 : ℝ) - 1) = 1 := by
  rw [beta_integral_real one_pos one_pos]
  norm_num [Real.Gamma_one, Real.Gamma_two]

/-- `B(1/2, 1/2) = π`. -/
example : ∫ x in (0 : ℝ)..1, x ^ ((1 / 2 : ℝ) - 1) * (1 - x) ^ ((1 / 2 : ℝ) - 1) = π := by
  rw [beta_integral_real (by norm_num) (by norm_num)]
  have h : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  rw [h, Real.Gamma_one, Real.Gamma_one_half_eq]
  have := Real.pi_pos
  rw [mul_self_sqrt this.le]; ring

/-- Subtracted form at `a = 1`, `b = 2`: `∫₀¹ ((1-x) - 1) dx = -1/2 = B(1,2) - 1`. -/
example : ∫ x in (0 : ℝ)..1, x ^ ((1 : ℝ) - 1) * ((1 - x) ^ ((2 : ℝ) - 1) - 1) = -(1 / 2) := by
  rw [beta_integral_subtracted one_pos two_pos]
  norm_num [Real.Gamma_one, Real.Gamma_two]

/-- Negative check: the subtracted integrand is *not* the Beta integrand — dropping the
subtraction changes the value by exactly `1/a`. -/
example : ∫ x in (0 : ℝ)..1, x ^ ((1 : ℝ) - 1) * ((1 - x) ^ ((2 : ℝ) - 1) - 1) ≠
    ∫ x in (0 : ℝ)..1, x ^ ((1 : ℝ) - 1) * (1 - x) ^ ((2 : ℝ) - 1) := by
  rw [beta_integral_subtracted one_pos two_pos, beta_integral_real one_pos two_pos]
  intro h
  have : (1 : ℝ) / 1 = 0 := by linarith
  norm_num at this

/-- Continuation at `a = -1/2`, `b = 1`: `∫₀¹ y^(-3/2) · 0 = 0` and
`Γ(-1/2) Γ(1) / Γ(1/2) − 1/(−1/2) = −2 + 2 = 0`. -/
example : ∫ x in (0 : ℝ)..1, x ^ ((-1 / 2 : ℝ) - 1) * ((1 - x) ^ ((1 : ℝ) - 1) - 1) = 0 := by
  simp

/-- The continued formula agrees with the closed form at `a = -1/2`, `b = 1`. -/
example : Gamma (-1 / 2 : ℝ) * Gamma 1 / Gamma (-1 / 2 + 1) - 1 / (-1 / 2 : ℝ) = 0 := by
  have h : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  have hg : Gamma (1 / 2 : ℝ) = (-1 / 2) * Gamma (-1 / 2) := by
    rw [← h]; exact Real.Gamma_add_one (by norm_num)
  have hpos : 0 < Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  rw [h, Real.Gamma_one]
  have hne : Gamma (1 / 2 : ℝ) ≠ 0 := hpos.ne'
  field_simp
  linarith

/-- Instance of the continuation with a nonzero integrand: `a = -1/2`, `b = 2` gives
`∫₀¹ y^(-3/2) (-y) dy = -2`, and the formula returns the same value. -/
example : ∫ x in (0 : ℝ)..1, x ^ ((-1 / 2 : ℝ) - 1) * ((1 - x) ^ ((2 : ℝ) - 1) - 1) =
    Gamma (-1 / 2 : ℝ) * Gamma 2 / Gamma (-1 / 2 + 2) - 1 / (-1 / 2 : ℝ) :=
  beta_integral_subtracted_neg (by norm_num) (by norm_num) two_pos

/-- Negative check: for `a = -1/2` the continued subtracted integral is *not* the Beta integral
formula without the `-1/a` correction. -/
example : Gamma (-1 / 2 : ℝ) * Gamma 2 / Gamma (-1 / 2 + 2) - 1 / (-1 / 2 : ℝ) ≠
    Gamma (-1 / 2 : ℝ) * Gamma 2 / Gamma (-1 / 2 + 2) := by
  intro h
  have : (1 / (-1 / 2 : ℝ)) = 0 := by linarith
  norm_num at this

end FracLapTest
