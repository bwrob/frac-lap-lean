/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.NashConsequences
import Mathlib.Tactic.NormNum

/-!
# FracLapTest.NashConsequencesTest

Explicit Nash constant, Friedrichs--Poincaré, and a negative check on the constant.
-/

namespace FracLapTest

open FracLap MeasureTheory

/-- The unit-frequency constant is exactly `(2π)^α`; for `α = 1` it is `2π`. -/
example : gagliardoSymbol 1 1 = ENNReal.ofReal (2 * Real.pi) := by
  rw [gagliardoSymbol_one_eq fractionalExponent_one, Real.rpow_one]

/-- Friedrichs--Poincaré at the Cauchy exponent for functions supported in `(0, 1)`:
`‖f‖₂² ≤ 2 (2/π) E_1(f)`. -/
example (f : L2C) (hf0 : ∀ᵐ x, x ∉ Set.Ioo (0 : ℝ) 1 → (f : ℝ → ℂ) x = 0) :
    ‖f‖ₑ ^ (2 : ℝ) ≤ 2 * ENNReal.ofReal ((2 * (volume (Set.Ioo (0 : ℝ) 1)).toReal / Real.pi) ^
      (1 : ℝ)) * gagliardoEnergyC 1 f :=
  poincare_friedrichs fractionalExponent_one f measurableSet_Ioo (by simp) hf0

/-- The measure of `(0, 1)` entering the constant is exactly `1`, so the constant is `4/π`. -/
example : (volume (Set.Ioo (0 : ℝ) 1)).toReal = 1 := by simp

end FracLapTest
