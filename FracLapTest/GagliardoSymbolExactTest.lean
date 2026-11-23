/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.GagliardoSymbolExact
import Mathlib.Tactic.NormNum

/-!
# FracLapTest.GagliardoSymbolExactTest

The exact Fourier symbol of the Gagliardo energy at concrete exponents.
-/

namespace FracLapTest

open FracLap

/-- At the Cauchy exponent, `Λ_1(ξ) = 2π |ξ|`. -/
example (ξ : ℝ) : gagliardoSymbol 1 ξ = ENNReal.ofReal (|2 * Real.pi * ξ| ^ (1 : ℝ)) :=
  gagliardoSymbol_exact fractionalExponent_one ξ

/-- The symbol vanishes at the origin (no constant mode costs energy). -/
example : gagliardoSymbol (3 / 2) 0 = 0 := by
  rw [gagliardoSymbol_exact ⟨by norm_num, by norm_num⟩]
  simp [Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]

/-- The symbol is exactly `α`-homogeneous: `Λ_{1/2}(4) = 2 Λ_{1/2}(1)`, now with the constants
`(2π)^{1/2}` made explicit. -/
example : gagliardoSymbol (1 / 2) 4 =
    ENNReal.ofReal 2 * ENNReal.ofReal ((2 * Real.pi) ^ (1 / 2 : ℝ)) := by
  rw [gagliardoSymbol_exact ⟨by norm_num, by norm_num⟩]
  rw [← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  rw [abs_of_pos (by positivity), show 2 * Real.pi * 4 = 4 * (2 * Real.pi) by ring,
    Real.mul_rpow (by norm_num) (by positivity)]
  have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h4]

end FracLapTest
