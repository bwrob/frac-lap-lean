/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.StableKernelTail
import Mathlib.Tactic.Positivity

/-!
# FracLapTest.StableKernelTailTest

Closed-form evaluations and instantiations for `FracLap.WholeLine.StableKernelTail`:
the mass of the density `k(ω) = α ω^(α-1) exp (-ω^α)` near the origin at `α = 1`, the density at
`α = 1` and `α = 1 / 2`, and the tail bound at `α = 1` (the Cauchy case).
-/

namespace FracLapTest

open FracLap MeasureTheory Real Set

/-- At `α = 1` the density is `exp (-ω)` and its mass on `(0, 1]` is `1 - exp (-1)`. -/
example : ∫ ν in Ioc (0 : ℝ) 1, stableDensity 1 ν = 1 - exp (-1) := by
  rw [integral_stableDensity_Ioc one_pos one_pos, rpow_one]

/-- Pointwise value of the density at `α = 1`. -/
example (ω : ℝ) : stableDensity 1 ω = exp (-ω) := by
  simp [stableDensity]

/-- The density at `α = 1 / 2` is decreasing: its value at `1 / 4` exceeds its value at `1`. -/
example : stableDensity (1 / 2) 1 ≤ stableDensity (1 / 2) (1 / 4) :=
  stableDensity_antitoneOn (by norm_num) (by norm_num) (show (1 / 4 : ℝ) ∈ Ioi 0 by norm_num)
    (show (1 : ℝ) ∈ Ioi 0 by norm_num) (by norm_num)

/-- The tail bound at `α = 1` and `x = π`: `|P₁(π, 1)| ≤ π⁻¹ (π⁻¹ 1^1)`. -/
example : |stableKernel 1 π 1| ≤ π⁻¹ * (π⁻¹ * (π / π) ^ (1 : ℝ)) :=
  abs_stableKernel_le_of_le_one one_pos le_rfl pi_pos

end FracLapTest
