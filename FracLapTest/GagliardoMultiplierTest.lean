/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.GagliardoMultiplier
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# FracLapTest.GagliardoMultiplierTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.WholeLine.GagliardoMultiplier`.
-/

namespace FracLapTest

open Complex Filter FourierTransform FracLap MeasureTheory Real Set
open scoped ENNReal NNReal

/-! ### 13. Smooth cutoff and the multiplier estimate -/

/-- Closed-form values of the cutoff `θ_2`: it vanishes on `(-∞, 1]` and equals `1` on `[2, ∞)`. -/
example : cutoffStep 2 (-3) = 0 ∧ cutoffStep 2 1 = 0 ∧ cutoffStep 2 2 = 1 ∧ cutoffStep 2 5 = 1 :=
  ⟨cutoffStep_eq_zero (by norm_num) (by norm_num), cutoffStep_eq_zero (by norm_num) (by norm_num),
    cutoffStep_eq_one (by norm_num) (by norm_num), cutoffStep_eq_one (by norm_num) (by norm_num)⟩

/-- Negative counterexample: the cutoff is not constant (`θ_2(0) ≠ θ_2(2)`), and it is strictly
between `0` and `1` inside the transition region. -/
example : cutoffStep 2 0 ≠ cutoffStep 2 2 := by
  rw [cutoffStep_eq_zero (by norm_num) (by norm_num), cutoffStep_eq_one (by norm_num) (by norm_num)]
  norm_num

example : 0 < cutoffStep 2 (3 / 2) := by
  unfold cutoffStep
  exact Real.smoothTransition.pos_of_pos (by norm_num)

/-- The constant multiplier `θ ≡ 1` (`B = 1`, `L = 0`) satisfies the hypotheses of the
multiplier estimate, so the estimate applies non-vacuously. -/
example (f : L2C) :
    gagliardoEnergyC 1 f ≤ ENNReal.ofReal (2 * 1 ^ 2) * gagliardoEnergyC 1 f +
      ENNReal.ofReal (2 * max (0 ^ 2) (4 * 1 ^ 2)) * (∫⁻ h, gagliardoKernel 1 h) *
        ‖f‖ₑ ^ (2 : ℝ) :=
  gagliardoEnergyC_mul_le fractionalExponent_one (θ := fun _ => (1 : ℝ)) measurable_const
    (B := 1) (L := 0) (fun _ => by norm_num) (fun _ _ => by simp) f f
    (Filter.Eventually.of_forall fun x => by simp)

end FracLapTest
