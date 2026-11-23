/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.HardyLittlewood

/-!
# FracLapTest.HardyLittlewoodTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.Tools.HardyLittlewood`.
-/

namespace FracLapTest

open FracLap MeasureTheory Set
open scoped ENNReal

@[expose] public section

/-- The maximal function of the zero function vanishes. -/
example (x : ℝ) : hlMax (fun _ => (0 : ℝ≥0∞)) x = 0 := by
  unfold hlMax
  simp

/-- The maximal function dominates every single ball average (here `r = 1`). -/
example (g : ℝ → ℝ≥0∞) (x : ℝ) :
    (ENNReal.ofReal (2 * 1))⁻¹ * ∫⁻ y in Icc (x - 1) (x + 1), g y ≤ hlMax g x :=
  le_iSup_of_le (⟨1, one_pos⟩ : {r : ℝ // 0 < r}) le_rfl

/-- Weak type `(1, 1)` for the indicator of `[0, 1]`: `|{M g > 1/2}| ≤ 10`. -/
example : volume {x : ℝ | (2⁻¹ : ℝ≥0∞) < hlMax ((Icc (0 : ℝ) 1).indicator fun _ => (1 : ℝ≥0∞)) x} ≤
    5 * (2⁻¹ : ℝ≥0∞)⁻¹ * ∫⁻ y, (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) y :=
  hlMax_weak_type _ (by simp) (by simp)

/-- The weak-type bound is nontrivial: the right side is the finite number `10`. -/
example : 5 * (2⁻¹ : ℝ≥0∞)⁻¹ * ∫⁻ y, (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) y = 10 := by
  rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
  norm_num [ENNReal.ofReal_one]

end

end FracLapTest
