/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.StableKernelDecay
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# FracLapTest.StableKernelDecayTest

Anti-vacuity witnesses and concrete tail-decay checks for `FracLap.WholeLine.StableKernelDecay`
across the full fractional regime `0 < α < 2` (including `α > 1`).
-/

namespace FracLapTest

open FracLap Real

@[expose] public section

/-- Positivity of `stableTailB` and `stableDecayConst` at `α = 1` and `α = 3 / 2`. -/
example :
    0 < stableTailB 1 ∧ 0 < stableTailB (3 / 2 : ℝ) ∧
      0 < stableDecayConst 1 ∧ 0 < stableDecayConst (3 / 2 : ℝ) :=
  ⟨stableTailB_pos one_pos (by norm_num),
    stableTailB_pos (by norm_num) (by norm_num),
    stableDecayConst_pos one_pos (by norm_num),
    stableDecayConst_pos (by norm_num) (by norm_num)⟩

/-- Unit-time algebraic decay witness at `α = 3 / 2 > 1` (not covered by the `α ≤ 1` bound). -/
example (x : ℝ) :
    stableKernel (3 / 2 : ℝ) x 1 ≤ stableDecayConst (3 / 2 : ℝ) / (1 + |x|) ^ (5 / 2 : ℝ) := by
  have h := stableKernel_decay_unit_time (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num) x
  rwa [show 1 + (3 / 2 : ℝ) = 5 / 2 by norm_num] at h

/-- Off-origin tail bound witness for `x = 2` and `α = 3 / 2`. -/
example :
    |stableKernel (3 / 2 : ℝ) 2 1| ≤
      (stableTailB (3 / 2 : ℝ) / 4) * Real.pi ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (-5 / 2 : ℝ) := by
  have h := abs_stableKernel_one_le_rpow (x := (2 : ℝ)) (by norm_num : (0 : ℝ) < 3 / 2)
    (by norm_num) (by norm_num)
  rwa [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num,
    show -1 - (3 / 2 : ℝ) = -5 / 2 by norm_num] at h

end

end FracLapTest
