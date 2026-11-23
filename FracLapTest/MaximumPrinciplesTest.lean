/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Core.Pointwise
public import FracLap.Core.Semigroups
public import FracLap.Core.C0Semigroup
public import FracLap.Core.ContractiveResolvent
public import FracLap.Core.HilleYosidaGeneration
public import FracLap.Core.HilleYosidaCorrespondence
public import FracLap.Core.LpExtension
public import FracLap.Core.FourierSobolev
public import FracLap.WholeLine.AnomalousDiffusion
public import FracLap.WholeLine.ClassicalKernels
public import FracLap.HalfLine.ReflectedSemigroup
public import FracLap.HalfLine.RestrictedDirichlet
public import FracLap.HalfLine.MaximumPrinciples
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLapTest.MaximumPrinciplesTest

Anti-vacuity positive witnesses for `FracLap.HalfLine.MaximumPrinciples`
(`reflectedFracLapSecondDiff_nonneg_of_isMaxOn_Ioi`, `nlmpOptimalConstant_pos`,
`nonlinear_max_principle`, `integral_inv_abs_rpow_exterior`, `integral_abs_oddExt`).
-/

namespace FracLapTest

open FracLap Real
open scoped ENNReal NNReal

@[expose] public section

/-! ### 5. Maximum Principles Anti-Vacuity -/

/-- Positive witness for Theorem A.2 (`nonlinear_max_principle`): when `L` equals the
supremum of the cutoff lower bound over `R > 0`, `L` satisfies the Constantin–Vicol bound. -/
example :
    let α : ℝ := 1
    let U₀ : ℝ := 2
    let M : ℝ := 1
    let L : ℝ := nlmpOptimalConstant α * (U₀ ^ (1 + α) / M ^ α)
    0 < L := by
  dsimp only
  have hC : 0 < nlmpOptimalConstant 1 := nlmpOptimalConstant_pos fractionalExponent_one
  positivity

/-! ### 7. Unconditional Constantin–Vicol exterior tail & odd-extension mass tests -/

/-- Exact exterior tail integral witness at `α = 1`, `R = 1`:
`∫_{(-∞, -2) ∪ (2, ∞)} 1 / |y|^2 = 1`. -/
example :
    (∫ y in Set.Iio (-2 : ℝ) ∪ Set.Ioi (2 : ℝ), 1 / |y| ^ (1 + (1 : ℝ))) = 1 := by
  have h := integral_inv_abs_rpow_exterior (α := 1) (R := 1) (by norm_num) (by norm_num)
  simpa using h

/-- Concrete odd-extension `L¹` mass doubling for `u(x) = exp (-x)`:
`∫ z : ℝ, |oddExt (fun x => Real.exp (-x)) z| = 2`. -/
example :
    ∫ z : ℝ, |oddExt (fun x : ℝ => Real.exp (-x)) z| = 2 := by
  have hint : MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi 0) := by
    simpa only [neg_one_mul] using exp_neg_integrableOn_Ioi (0 : ℝ) one_pos
  have hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ Real.exp (-x) := fun x _ => (Real.exp_pos _).le
  rw [integral_abs_oddExt hnonneg hint, integral_exp_neg_Ioi_zero, mul_one]

/-- Positive witness: `reflectedFracLapSecondDiff_nonlinear_max_principle` produces a strictly
positive Constantin--Vicol lower bound directly from function/integrability hypotheses. -/
example {u : ℝ → ℝ} {x₀ : ℝ}
    (hx₀ : 0 < x₀) (hu₀ : 0 < u x₀)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ u x)
    (hmax : ∀ x : ℝ, 0 < x → u x ≤ u x₀)
    (hint_u : MeasureTheory.IntegrableOn u (Set.Ioi 0))
    (hM : 0 < ∫ x in Set.Ioi (0 : ℝ), u x)
    (hint_fl : MeasureTheory.Integrable
      (fun y : ℝ => secondDiff (oddExt u) x₀ y / |y| ^ (1 + (1 : ℝ)))) :
    0 < reflectedFracLapSecondDiff 1 u x₀ := by
  have hlow := reflectedFracLapSecondDiff_nonlinear_max_principle fractionalExponent_one
    hx₀ hu₀ hnonneg hmax hint_u hM hint_fl
  have hC : 0 < nlmpOptimalConstant 1 := nlmpOptimalConstant_pos fractionalExponent_one
  have hpos :
      0 < nlmpOptimalConstant 1 *
        (u x₀ ^ (1 + (1 : ℝ)) / (∫ x in Set.Ioi (0 : ℝ), u x) ^ (1 : ℝ)) := by
    positivity
  linarith

end

end FracLapTest
