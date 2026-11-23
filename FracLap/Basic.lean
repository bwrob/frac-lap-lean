/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# FracLap.Basic

Starter definitions and theorems for the `FracLap` formalization project.
-/

namespace FracLap

@[expose] public section

/-- A fractional Laplacian order parameter `s ∈ (0, 1)`. -/
def FractionalOrder (s : ℝ) : Prop :=
  0 < s ∧ s < 1

/-- The standard half-Laplacian parameter `s = 1 / 2` satisfies `0 < s ∧ s < 1`. -/
theorem fractionalOrder_half : FractionalOrder (1 / 2 : ℝ) := by
  constructor <;> norm_num

end

end FracLap
