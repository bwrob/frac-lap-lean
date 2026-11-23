/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.ChainRule
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum

/-!
# FracLapTest.ChainRuleTest

Convex chain rule and Córdoba--Córdoba: instances and a negative counterexample.
-/

namespace FracLapTest

open FracLap MeasureTheory

/-- The chain rule for `φ = exp` at a point: `exp a - exp b ≤ exp a (a - b)`. -/
example (a b : ℝ) : Real.exp a - Real.exp b ≤ Real.exp a * (a - b) :=
  chain_rule_two_point (φ := Real.exp) (φ' := Real.exp) convexOn_exp Real.hasDerivAt_exp a b

/-- Córdoba--Córdoba is an equality up to the square `(a - b)²`: `2a(a-b) - (a² - b²) = (a-b)²`. -/
example (a b : ℝ) : 2 * a * (a - b) - (a ^ 2 - b ^ 2) = (a - b) ^ 2 := by ring

/-- Negative counterexample: the reversed Córdoba inequality `2a(a-b) ≤ a² - b²` is false
(`a = 0`, `b = 1`), so the direction of the inequality is not vacuous. -/
example : ¬ ∀ a b : ℝ, 2 * a * (a - b) ≤ a ^ 2 - b ^ 2 := by
  intro h
  have := h 0 1
  norm_num at this

/-- Concrete instance of the nonlocal form with the Dirac measure at `y₀`. -/
example (u : ℝ → ℝ) (x y₀ : ℝ) :
    ∫ y, (u x ^ 2 - u y ^ 2) ∂(Measure.dirac y₀) ≤
      2 * u x * ∫ y, (u x - u y) ∂(Measure.dirac y₀) := by
  rw [integral_dirac, integral_dirac]
  exact cordoba_two_point _ _

end FracLapTest
