/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.GagliardoScaling
import Mathlib.Tactic.NormNum

/-!
# FracLapTest.GagliardoScalingTest

Instantiations of the exact homogeneity of the Fourier-side Gagliardo weight at the Cauchy exponent.
-/

namespace FracLapTest

open FracLap

/-- `Λ_1(2) = 2 Λ_1(1)`. -/
example : gagliardoSymbol 1 2 = ENNReal.ofReal 2 * gagliardoSymbol 1 1 := by
  have h := gagliardoSymbol_scale (α := 1) one_pos (ξ := 2) (by norm_num)
  rwa [Real.rpow_one] at h

/-- The weight is even: `Λ_{1/2}(-3) = Λ_{1/2}(3)`. -/
example : gagliardoSymbol (1 / 2) (-3) = gagliardoSymbol (1 / 2) 3 :=
  gagliardoSymbol_neg _ _

/-- The unit-frequency constant is a genuine positive finite number at `α = 1`. -/
example : 0 < gagliardoSymbol 1 1 ∧ gagliardoSymbol 1 1 < ⊤ :=
  ⟨gagliardoSymbol_one_pos fractionalExponent_one,
    gagliardoSymbol_one_lt_top fractionalExponent_one⟩

/-- Homogeneity transfers a frequency ratio: `Λ_{1/2}(4) = 2 Λ_{1/2}(1)` since `4^(1/2) = 2`. -/
example : gagliardoSymbol (1 / 2) 4 = ENNReal.ofReal 2 * gagliardoSymbol (1 / 2) 1 := by
  have h := gagliardoSymbol_scale (α := 1 / 2) (by norm_num) (ξ := 4) (by norm_num)
  have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  rwa [h4] at h

end FracLapTest
