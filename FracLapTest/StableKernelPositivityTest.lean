/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.StableKernelPositivity
import Mathlib.Tactic.Positivity

/-!
# FracLapTest.StableKernelPositivityTest

Instantiations of positivity and radial monotonicity of the stable kernel at several exponents,
and the evenness reduction.
-/

namespace FracLapTest

open FracLap Real

/-- Positivity at the Cauchy exponent. -/
example (x : ℝ) : 0 ≤ stableKernel 1 x 1 := stableKernel_nonneg one_pos one_lt_two one_pos x

/-- Positivity at a non-classical exponent `α = 3 / 2`. -/
example (x : ℝ) : 0 ≤ stableKernel (3 / 2) x 2 :=
  stableKernel_nonneg (by norm_num) (by norm_num) (by norm_num) x

/-- Radial monotonicity at `α = 3 / 2`: `P(3, t) ≤ P(-1, t)` since `|-1| ≤ |3|`. -/
example : stableKernel (3 / 2) 3 1 ≤ stableKernel (3 / 2) (-1) 1 :=
  stableKernel_antitone (by norm_num) (by norm_num) one_pos (by norm_num)

/-- The regularization limit is a genuine identity: at `α = 1`, `x = 0`, `t = 1` the integral form
agrees with the definition. -/
example : stableKernel 1 0 1 = (2 * π)⁻¹ * ∫ ω : ℝ, cos (0 * ω) * exp (-1 * |ω| ^ (1 : ℝ)) :=
  stableKernel_eq_integral 0 1

end FracLapTest
