/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.AbstractLemmas
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NormNum

/-!
# FracLapTest.AbstractLemmasTest

The bilinear fixed-point lemma on ℝ and Bernstein scaling at concrete functions.
-/

namespace FracLapTest

open FracLap Set

/-- Fixed-point lemma on `ℝ` with `B u v = u v` (`η = 1`), `y = 1/10`, `ε = 1/5 < 1/4`:
there is a solution of `u = 1/10 + u²` with `|u| ≤ 2/5`. -/
example : ∃ u : ℝ, u = 1 / 10 + u * u ∧ ‖u‖ ≤ 2 * (1 / 5) := by
  obtain ⟨u, hu, hb, -⟩ := bilinear_fixed_point (ContinuousLinearMap.mul ℝ ℝ) (η := 1)
    (ε := 1 / 5) one_pos (fun u v => by simp [norm_mul]) (by norm_num) (by norm_num)
    (y := 1 / 10) (by norm_num [Real.norm_eq_abs, abs_of_pos])
  exact ⟨u, by simpa using hu, hb⟩

/-- Scaling for `φ(t) = t`: `φ(λ t) = λ φ(t) = max 1 λ · φ(t)` when `λ ≥ 1`. -/
example : (3 : ℝ) * 2 ≤ max 1 3 * 2 := by norm_num

/-- Bernstein scaling for `φ = id` on `[0, ∞)` (concave, nondecreasing, `φ 0 = 0`). -/
example {t l : ℝ} (ht : 0 < t) (hl : 0 < l) : id (l * t) ≤ max 1 l * id t :=
  scaling_le_max (φ := id) (by simpa using concaveOn_id (convex_Ici 0)) le_rfl
    (fun _ _ _ _ h => h) ht hl

/-- Lower scaling bound for `φ = id`. -/
example {t l : ℝ} (ht : 0 < t) (hl : 0 < l) : min 1 l * id t ≤ id (l * t) :=
  min_le_scaling (φ := id) (by simpa using concaveOn_id (convex_Ici 0)) le_rfl
    (fun _ _ _ _ h => h) ht hl

/-- `mul_deriv_le` for the concave nondecreasing function `φ(z) = min z 1` at `z = 1/2`
(`φ' = 1`): `0 ≤ 1` and `(1/2) · 1 ≤ min (1/2) 1 = 1/2`. -/
example : 0 ≤ (1 : ℝ) ∧ 1 / 2 * (1 : ℝ) ≤ min (1 / 2) 1 := by
  have hc : ConcaveOn ℝ (Ici 0) (fun z : ℝ => min z 1) := by
    refine ⟨convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    refine le_min ?_ ?_
    · nlinarith [min_le_left x 1, min_le_left y 1]
    · nlinarith [min_le_right x 1, min_le_right y 1]
  have hd : HasDerivAt (fun z : ℝ => min z 1) 1 (1 / 2) := by
    refine (hasDerivAt_id (1 / 2 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)] with x hx
    simp [min_eq_left (le_of_lt (mem_Iio.mp hx))]
  exact mul_deriv_le hc (by simp) (fun x _ y _ hxy => min_le_min_right 1 hxy)
    (by norm_num) hd

/-- Negative check: the companion estimate `-z φ''(z) ≤ 2 φ'(z)` fails for the Bernstein
function `φ(z) = 1 - e^{-z}` at `z = 3` (`φ' = e^{-z}`, `φ'' = -e^{-z}`), so it cannot follow from
concavity and monotonicity alone. -/
example : ¬ (3 * Real.exp (-3) ≤ 2 * Real.exp (-3)) := by
  have := Real.exp_pos (-3)
  intro h
  linarith

end FracLapTest
