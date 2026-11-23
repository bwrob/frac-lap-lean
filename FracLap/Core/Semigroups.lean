/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLap.Core.Semigroups

Core reusable functional-analytic interfaces and normal-contraction lemmas for
fractional Laplacian semigroups and Dirichlet forms (Option A: bundled structures
representing foundational prerequisites from Sections 2–4):
- `ContractionSemigroup E`: a `C₀`-contraction semigroup family `T : ℝ → E → E` on a
  normed space `E` (`T 0 = id`, `T (s + t) = T s ∘ T t`, `‖T t u‖ ≤ ‖u‖`).
- `OddSubspaceConjugation E H`: isometric reflection/restriction conjugation
  (`E_op : H → E`, `R_op : E → H` with `R_op (E_op u) = u`, `E_op (R_op f) = f` on the odd
  invariant subspace, and `‖E_op u‖ = √2 ‖u‖`, `‖R_op f‖ = (1 / √2) ‖f‖`).
- `SymmetricAccretiveForm V`: a symmetric, accretive (`0 ≤ B u u`), and continuous
  (`|B u v| ≤ √(B u u) √(B v v)`) bilinear form `B : V → V → ℝ`.
- `IsMarkovForm V B absOp capOneOp`: the Beurling–Deny normal-contraction criteria
  `B (|u|) (|u|) ≤ B u u` and `B (u ∧ 1) (u ∧ 1) ≤ B u u`.
- Pointwise normal contraction inequalities:
  `||a| - |b|| ≤ |a - b|` (`abs_sub_abs_le_abs_sub`),
  `(|a| - |b|)^2 ≤ (a - b)^2` (`sq_abs_sub_abs_le_sq_sub`),
  `|min a 1 - min b 1| ≤ |a - b|` (`abs_min_one_sub_min_one_le`), and
  `(min a 1 - min b 1)^2 ≤ (a - b)^2` (`sq_min_one_sub_min_one_le`).
-/

namespace FracLap

open Real

@[expose] public section

/-- A bundled `C₀`-contraction semigroup family `T : ℝ → E → E` for `t ≥ 0`, equipped with
a norm function `normE : E → ℝ` and distance `distE : E → E → ℝ`. -/
structure ContractionSemigroup (E : Type*) where
  /-- Semigroup action `T t u` for `t ≥ 0`. -/
  T : ℝ → E → E
  /-- Norm functional `‖u‖_E`. -/
  normE : E → ℝ
  /-- Nonnegativity of the norm functional. -/
  normE_nonneg : ∀ u : E, 0 ≤ normE u
  /-- Identity at `t = 0`: `T 0 u = u`. -/
  map_zero_time : ∀ u : E, T 0 u = u
  /-- Semigroup composition law: `T s (T t u) = T (s + t) u` for `s, t ≥ 0`. -/
  map_add_time : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ u : E, T s (T t u) = T (s + t) u
  /-- Contractivity: `‖T t u‖_E ≤ ‖u‖_E` for `t ≥ 0`. -/
  contractive : ∀ t : ℝ, 0 ≤ t → ∀ u : E, normE (T t u) ≤ normE u

/-- An antisymmetric (odd) extension / restriction pair `(extOp, restOp)` between a half-line
function space `H` (modeling `L²(0, ∞)`) and a whole-line space `E` (modeling `L²(ℝ)`) with
invariant odd subspace predicate `IsOdd : E → Prop` and scaling factor `√2`. -/
structure OddSubspaceConjugation (E H : Type*) (normE : E → ℝ) (normH : H → ℝ) where
  /-- Predicate characterizing the closed odd subspace `L²_odd(ℝ) ⊂ L²(ℝ)`. -/
  IsOdd : E → Prop
  /-- Antisymmetric extension operator `E : L²(0, ∞) → L²_odd(ℝ)`. -/
  extOp : H → E
  /-- Restriction operator `R : L²(ℝ) → L²(0, ∞)`. -/
  restOp : E → H
  /-- Every extended function `extOp u` lies in the odd subspace. -/
  extOp_isOdd : ∀ u : H, IsOdd (extOp u)
  /-- Restricting an odd extension recovers the original half-line function: `R (E u) = u`. -/
  restOp_extOp : ∀ u : H, restOp (extOp u) = u
  /-- Extending the restriction of an odd function is the identity on `L²_odd(ℝ)`:
  `E (R f) = f`. -/
  extOp_restOp_of_isOdd : ∀ f : E, IsOdd f → extOp (restOp f) = f
  /-- Scaled isometry of odd extension: `‖E u‖_E = √2 ‖u‖_H`. -/
  norm_extOp : ∀ u : H, normE (extOp u) = sqrt 2 * normH u
  /-- Scaled isometry of restriction on odd functions: `√2 ‖R f‖_H = ‖f‖_E`. -/
  norm_restOp_of_isOdd : ∀ f : E, IsOdd f → sqrt 2 * normH (restOp f) = normE f

/-- A symmetric, accretive, and Cauchy–Schwarz continuous bilinear form `B : V → V → ℝ`
on a form domain `V` (modeling `H^(α / 2)(ℝ)` or `H^(α / 2)_0(ℝ)`). -/
structure SymmetricAccretiveForm (V : Type*) where
  /-- Bilinear form evaluation `B(u, v)`. -/
  form : V → V → ℝ
  /-- Symmetry: `B(u, v) = B(v, u)`. -/
  symm : ∀ u v : V, form u v = form v u
  /-- Accretiveness (nonnegativity): `0 ≤ B(u, u)`. -/
  accretive : ∀ u : V, 0 ≤ form u u
  /-- Cauchy–Schwarz continuity bound: `(B(u, v))² ≤ B(u, u) B(v, v)`. -/
  cauchy_schwarz_sq : ∀ u v : V, (form u v) ^ 2 ≤ form u u * form v v

/-- The Beurling–Deny normal-contraction criteria for a symmetric accretive form `B` on `V`
with respect to lattice modulus `absOp : V → V` (`u ↦ |u|`) and unit truncation
`capOneOp : V → V` (`u ↦ u ∧ 1`). -/
structure IsMarkovDirichletForm {V : Type*} (B : SymmetricAccretiveForm V)
    (absOp capOneOp : V → V) : Prop where
  /-- First Beurling–Deny condition: `B(|u|, |u|) ≤ B(u, u)`. -/
  form_abs_le : ∀ u : V, B.form (absOp u) (absOp u) ≤ B.form u u
  /-- Second Beurling–Deny condition: `B(u ∧ 1, u ∧ 1) ≤ B(u, u)`. -/
  form_capOne_le : ∀ u : V, B.form (capOneOp u) (capOneOp u) ≤ B.form u u

/-- Pointwise modulus normal-contraction inequality: `||a| - |b|| ≤ |a - b|`. -/
theorem abs_sub_abs_le_abs_sub (a b : ℝ) : |(|a| - |b|)| ≤ |a - b| :=
  abs_abs_sub_abs_le_abs_sub a b

/-- Squared modulus normal-contraction inequality for Gagliardo integrands:
`(|a| - |b|)^2 ≤ (a - b)^2`. -/
theorem sq_abs_sub_abs_le_sq_sub (a b : ℝ) : (|a| - |b|) ^ 2 ≤ (a - b) ^ 2 := by
  rw [← sq_abs (|a| - |b|), ← sq_abs (a - b)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_sub_abs_le_abs_sub a b) 2

/-- Pointwise unit-truncation (`u ↦ min u 1`) normal-contraction inequality:
`|min a 1 - min b 1| ≤ |a - b|`. -/
theorem abs_min_one_sub_min_one_le (a b : ℝ) : |min a 1 - min b 1| ≤ |a - b| := by
  rcases le_total a 1 with ha | ha <;> rcases le_total b 1 with hb | hb
  · rw [min_eq_left ha, min_eq_left hb]
  · rw [min_eq_left ha, min_eq_right hb]
    have h1 : a - 1 ≤ 0 := by linarith
    have h2 : a - b ≤ 0 := by linarith
    rw [abs_of_nonpos h1, abs_of_nonpos h2]
    linarith
  · rw [min_eq_right ha, min_eq_left hb]
    have h1 : 0 ≤ 1 - b := by linarith
    have h2 : 0 ≤ a - b := by linarith
    rw [abs_of_nonneg h1, abs_of_nonneg h2]
    linarith
  · rw [min_eq_right ha, min_eq_right hb, sub_self, abs_zero]
    exact abs_nonneg (a - b)

/-- Squared unit-truncation normal-contraction inequality for Gagliardo integrands:
`(min a 1 - min b 1)^2 ≤ (a - b)^2`. -/
theorem sq_min_one_sub_min_one_le (a b : ℝ) : (min a 1 - min b 1) ^ 2 ≤ (a - b) ^ 2 := by
  rw [← sq_abs (min a 1 - min b 1), ← sq_abs (a - b)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_min_one_sub_min_one_le a b) 2

end

end FracLap
