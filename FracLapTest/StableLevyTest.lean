/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.StableLevy
import Mathlib.Tactic.Positivity

/-!
# FracLapTest.StableLevyTest

Closed-form evaluations of the Lévy integral at `β = 1 / 2` (where `Γ(1/2) = √π`), the Lévy
constant, finiteness of the truncated measures, and the Gaussian monotonicity of the symbol at the
Cauchy exponent `α = 1`.
-/

namespace FracLapTest

open FracLap MeasureTheory Real Set

/-- At `β = 1 / 2` the basic Lévy integral equals `2 √π`. -/
example : ∫ u in Ioi (0 : ℝ), (1 - exp (-u)) * u ^ (-1 - (1 / 2 : ℝ)) = 2 * √π := by
  rw [integral_one_sub_exp_mul_rpow (by norm_num) (by norm_num)]
  have : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [this, Real.Gamma_one_half_eq]
  ring

/-- The Lévy constant at `β = 1 / 2` is `1 / (2 √π)`. -/
example : levyConst (1 / 2) = 1 / (2 * √π) := by
  unfold levyConst
  have : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [this, Real.Gamma_one_half_eq]
  have hπ : 0 < √π := sqrt_pos.mpr pi_pos
  field_simp

/-- The scaled Lévy integral at `λ = 4`, `β = 1 / 2` gives `4^(1/2) · 2 √π = 4 √π`. -/
example : ∫ s in Ioi (0 : ℝ), (1 - exp (-(4 * s))) * s ^ (-1 - (1 / 2 : ℝ)) = 4 * √π := by
  rw [integral_one_sub_exp_scaled (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 4)]
  have h1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have h2 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h1, Real.Gamma_one_half_eq, h2]
  ring

/-- Truncated Lévy measures are finite. -/
example : IsFiniteMeasure (levyMeasure (1 / 2) (1 / 3)) :=
  levyMeasure_isFiniteMeasure (by norm_num) (by norm_num)

/-- The Cauchy symbol `exp (-|ξ|)` is Gaussian monotone. -/
example : IsGaussMonotone fun ξ : ℝ => exp (-1 * |ξ| ^ (1 : ℝ)) :=
  isGaussMonotone_stableSymbol one_pos one_lt_two one_pos

end FracLapTest
