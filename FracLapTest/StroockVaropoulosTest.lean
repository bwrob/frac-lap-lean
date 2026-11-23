/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.StroockVaropoulos
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum

/-!
# FracLapTest.StroockVaropoulosTest

Closed-form instances of the two-point Stroock--Varopoulos inequality: sharpness of the constant at
`q = 2` (where it is an equality), same-sign and opposite-sign numerical instances, and oddness of
the signed power.
-/

namespace FracLapTest

open FracLap

/-- At `q = 2` the signed powers are the identity and the constant `4 (q - 1) / q² = 1` is attained:
the inequality is an equality, so the constant cannot be improved. -/
example (a b : ℝ) :
    4 * (2 - 1) / (2 : ℝ) ^ 2 * (spow (2 / 2) a - spow (2 / 2) b) ^ 2 =
      (a - b) * (spow (2 - 1) a - spow (2 - 1) b) := by
  have h : ∀ s : ℝ, spow 1 s = s := by
    intro s
    rcases le_or_gt 0 s with hs | hs
    · rw [spow_of_nonneg _ hs, Real.rpow_one]
    · rw [spow_of_neg _ hs, Real.rpow_one, neg_neg]
  norm_num [h]
  ring

/-- Same-sign instance `q = 4`, `(a, b) = (1, 0)`: `3/4 · 1 ≤ 1`. -/
example : 4 * (4 - 1) / (4 : ℝ) ^ 2 * (spow (4 / 2) 1 - spow (4 / 2) 0) ^ 2 ≤
    (1 - 0) * (spow (4 - 1) 1 - spow (4 - 1) 0) :=
  sv_two_point (by norm_num) 1 0

/-- Opposite-sign instance `q = 3`, `(a, b) = (1, -1)`. -/
example : 4 * (3 - 1) / (3 : ℝ) ^ 2 * (spow (3 / 2) 1 - spow (3 / 2) (-1)) ^ 2 ≤
    (1 - -1) * (spow (3 - 1) 1 - spow (3 - 1) (-1)) :=
  sv_two_point (by norm_num) 1 (-1)

/-- The signed power is odd. -/
example (s : ℝ) : spow (3 / 2) (-s) = -spow (3 / 2) s := spow_neg (by norm_num) s

/-- The `|·|^(q/2)` form, which drops the sign. -/
example (a b : ℝ) : 4 * (3 - 1) / (3 : ℝ) ^ 2 * (|a| ^ ((3 : ℝ) / 2) - |b| ^ ((3 : ℝ) / 2)) ^ 2 ≤
    (a - b) * (spow (3 - 1) a - spow (3 - 1) b) :=
  sv_two_point_abs (by norm_num) a b

/-- Generalized Stroock--Varopoulos with `Ψ(s) = s³`, `Ψ'(s) = 3s²`, `ψ(s) = (9/5) s⁵`
(`ψ' = (Ψ')²`): `(a³ - b³)² ≤ (a - b)((9/5)a⁵ - (9/5)b⁵)`. -/
example (a b : ℝ) : (a ^ 3 - b ^ 3) ^ 2 ≤ (a - b) * (9 / 5 * a ^ 5 - 9 / 5 * b ^ 5) :=
  gen_sv_two_point (Ψ := fun s : ℝ => s ^ 3) (ψ := fun s : ℝ => 9 / 5 * s ^ 5)
    (Ψ' := fun s : ℝ => 3 * s ^ 2) (by fun_prop)
    (fun x => by simpa using hasDerivAt_pow 3 x)
    (fun x => ((hasDerivAt_pow 5 x).const_mul (9 / 5 : ℝ)).congr_deriv (by push_cast; ring)) a b

/-- Gen. SV recovers the identity case `Ψ = id`, `ψ = id`: equality. -/
example (a b : ℝ) : (a - b) ^ 2 ≤ (a - b) * (a - b) := by
  have := gen_sv_two_point (Ψ := id) (ψ := id) (Ψ' := fun _ => 1) continuous_const
    (fun x => hasDerivAt_id x) (fun x => by simpa using hasDerivAt_id x) a b
  simpa using this

end FracLapTest
