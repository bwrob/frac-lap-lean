/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.Bootstrap
import Mathlib.Tactic.NormNum

/-!
# FracLapTest.BootstrapTest

Closed-form check of the threshold, a positive instantiation, and a negative counterexample showing
the initial-smallness hypothesis cannot be dropped.
-/

namespace FracLapTest

open FracLap Set

/-- For `p = 2`, `B = 1` the threshold is `x₀ = (2 · 1)^(-1) = 1 / 2`. -/
example : bootstrapThreshold 1 2 = 1 / 2 := by
  unfold bootstrapThreshold
  norm_num [Real.rpow_neg_one]

/-- Positive instantiation (`p = 2`, `B = 1`, `A = 1/8`): the constant function `1/8` obeys
`g ≤ A p / (p - 1) = 1/4`, as the lemma predicts for functions starting below the threshold. -/
example : ∀ t ∈ (univ : Set ℝ), (fun _ : ℝ => (1 / 8 : ℝ)) t ≤ 1 / 8 * 2 / (2 - 1) := by
  refine bootstrap_bound (A := 1 / 8) (B := 1) (p := 2) ordConnected_univ continuousOn_const
    (by norm_num) one_pos (by norm_num) ?_ ?_ (fun _ => by norm_num) (t₀ := 0) (mem_univ _) ?_
  · norm_num
  · intro t _
    norm_num
  · norm_num [bootstrapThreshold, Real.rpow_neg_one]

/-- Negative counterexample: `g ≡ 1` satisfies `g ≤ A + B g²` and all other hypotheses, yet
`g ≤ 1/4` fails. It starts above the threshold `1/2`, so the hypothesis `g t₀ ≤ x₀` is essential. -/
example : ¬ ∀ t ∈ (univ : Set ℝ), (fun _ : ℝ => (1 : ℝ)) t ≤ 1 / 8 * 2 / (2 - 1) := by
  intro h
  have := h 0 (mem_univ _)
  norm_num at this

end FracLapTest
