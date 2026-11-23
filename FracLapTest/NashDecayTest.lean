/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.NashDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# FracLapTest.NashDecayTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.Tools.NashDecay`.
-/

namespace FracLapTest

open FracLap Set

@[expose] public section

/-- Sharpness: `u(t) = (1 + t)⁻¹` solves `u′ = -u²` (`α = 1`, `c = 1`), and `ode_decay` gives
`u(t) ≤ t⁻¹` (the profile `(c α (t + 1))⁻¹` saturates the bound up to the shift). -/
example : ∀ t : ℝ, 0 < t → (1 + t)⁻¹ ≤ (1 * 1 * t) ^ (-(1 / (1 : ℝ))) := by
  refine ode_decay (u := fun t : ℝ => (1 + t)⁻¹) (u' := fun t => -1 / (1 + t) ^ 2) one_pos one_pos
    ?_ (fun t ht => by positivity) ?_ ?_
  · exact ContinuousOn.inv₀ (continuousOn_const.add continuousOn_id) fun t ht => by
      have : 0 ≤ t := ht
      positivity
  · intro t ht
    have hne : (1 : ℝ) + t ≠ 0 := by positivity
    have h := ((hasDerivAt_id' t).const_add 1).inv hne
    convert h using 1
  · intro t ht
    have h2 : ((1 + t)⁻¹) ^ (1 + (1 : ℝ)) = ((1 + t) ^ 2)⁻¹ := by
      rw [show (1 + (1 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
    rw [h2]
    have : -1 / (1 + t) ^ 2 = -((1 + t) ^ 2)⁻¹ := by ring
    rw [this]
    linarith

/-- `nash_decay` for `α = 1`, `K = M = 1` and `u(t) = (1 + 2t)⁻¹`: here `u′ = -2 u²`, so
`E = u²` and the Nash inequality `u² ≤ K E M²` holds with equality; the conclusion is
`u(t) ≤ 1 / (2 t)`. -/
example : ∀ t : ℝ, 0 < t →
    (1 + 2 * t)⁻¹ ≤ (1 * (1 : ℝ) ^ (2 * (1 : ℝ)) / (2 * 1 * t)) ^ (1 / (1 : ℝ)) := by
  refine nash_decay (u := fun t : ℝ => (1 + 2 * t)⁻¹) (E := fun t => ((1 + 2 * t)⁻¹) ^ 2)
    one_pos one_pos one_pos ?_ (fun t ht => by positivity) ?_ ?_
  · exact ContinuousOn.inv₀ (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
      fun t ht => by
        have : 0 ≤ t := ht
        positivity
  · intro t ht
    have hne : (1 : ℝ) + 2 * t ≠ 0 := by positivity
    have h := (((hasDerivAt_id' t).const_mul 2).const_add 1).inv hne
    convert h using 1
    field_simp
  · intro t ht
    have h2 : ((1 + 2 * t)⁻¹) ^ (1 + (1 : ℝ)) = ((1 + 2 * t)⁻¹) ^ 2 := by
      rw [show (1 + (1 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h2, Real.one_rpow]
    simp

end

end FracLapTest
