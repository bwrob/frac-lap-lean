/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Core.C0Semigroup
public import FracLap.Core.ContractiveResolvent
public import FracLap.Core.HilleYosidaGeneration
public import FracLap.Core.HilleYosidaCorrespondence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLapTest.HilleYosidaTest

High-signal tests for the $C_0$-contraction semigroup and Hille--Yosida correspondence API:
1. A non-trivial concrete $C_0$-contraction semigroup (`expDecaySemigroup a ha`, representing
   `S(t) x = exp (-a t) x` for `a ≥ 0`), its closed-form generator `L x = -a x`, and its
   closed-form Laplace resolvent `R_μ x = (μ + a)⁻¹ x`.
2. A concrete non-trivial contractive resolvent (`expDecayResolvent a ha`), its Yosida generator
   computation at explicit numeric parameters, and recovery of `expDecaySemigroup a ha` via
   Yosida generation.
3. Negative counterexamples showing why contractivity (`‖S t‖ ≤ 1`), the Hille--Yosida bound
   (`‖R_α‖ ≤ α⁻¹`), and dense range are non-vacuous hypotheses.
-/

@[expose] public section

namespace FracLapTest

open FracLap MeasureTheory Set
open scoped NNReal

section

/-! ### 1. Non-trivial exponential-decay contraction semigroup -/

/-- Concrete non-trivial `StronglyContinuousContractionSemigroup ℝ`: scalar damping
`S(t) x = exp (-a * t) * x` for `a ≥ 0`. -/
noncomputable def expDecaySemigroup (a : ℝ) (ha : 0 ≤ a) :
    StronglyContinuousContractionSemigroup ℝ where
  operator t := Real.exp (-a * (t : ℝ)) • ContinuousLinearMap.id ℝ ℝ
  operator_zero := by
    rw [NNReal.coe_zero, mul_zero, Real.exp_zero, one_smul]
  operator_add s t := by
    ext
    simp only [smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul, NNReal.coe_add]
    rw [mul_add, Real.exp_add]
    ring
  opNorm_le_one t := by
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hle : Real.exp (-a * (t : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) t.coe_nonneg)
    calc
      Real.exp (-a * (t : ℝ)) * ‖ContinuousLinearMap.id ℝ ℝ‖
          ≤ Real.exp (-a * (t : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (Real.exp_pos _).le
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_right hle zero_le_one
      _ = 1 := one_mul 1
  continuous_orbit x :=
    (Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)).smul continuous_const

/-- Evaluation of `expDecaySemigroup` at `t` and `x`. -/
theorem expDecaySemigroup_apply (a : ℝ) (ha : 0 ≤ a) (t : ℝ≥0) (x : ℝ) :
    expDecaySemigroup a ha t x = Real.exp (-a * (t : ℝ)) * x :=
  rfl

/-- Closed-form Laplace resolvent of `expDecaySemigroup a ha`:
`(expDecaySemigroup a ha).resolvent μ x = ((μ : ℝ) + a)⁻¹ * x`. -/
theorem expDecaySemigroup_resolvent (a : ℝ) (ha : 0 ≤ a) (μ : PositiveShift) (x : ℝ) :
    (expDecaySemigroup a ha).resolvent μ x = ((μ : ℝ) + a)⁻¹ * x := by
  rw [StronglyContinuousContractionSemigroup.resolvent_apply]
  have hcongr :
      ∫ t in Ioi (0 : ℝ), (expDecaySemigroup a ha).laplaceIntegrand μ x t =
        ∫ t in Ioi (0 : ℝ), Real.exp (-((μ : ℝ) + a) * t) * x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [StronglyContinuousContractionSemigroup.laplaceIntegrand_apply, expDecaySemigroup_apply,
      Real.coe_toNNReal t ht.le]
    simp only [smul_eq_mul]
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  have hμa : 0 < (μ : ℝ) + a := add_pos_of_pos_of_nonneg μ.2 ha
  rw [hcongr, integral_mul_const,
    StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero hμa]

/-- Closed-form generator action for `expDecaySemigroup a ha`: every `x : ℝ` lies in the
generator domain and satisfies `L x = -a * x`. -/
theorem expDecaySemigroup_generator (a : ℝ) (ha : 0 ≤ a) (x : ℝ) :
    ∃ hx : x ∈ (expDecaySemigroup a ha).generatorDomain,
      (expDecaySemigroup a ha).generator ⟨x, hx⟩ = -a * x := by
  let μ₁ : PositiveShift := ⟨1, by norm_num⟩
  have hres : (expDecaySemigroup a ha).resolvent μ₁ (((1 : ℝ) + a) * x) = x := by
    rw [expDecaySemigroup_resolvent]
    have hne : ((1 : ℝ) + a) ≠ 0 := by linarith
    change ((1 : ℝ) + a)⁻¹ * (((1 : ℝ) + a) * x) = x
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hx : x ∈ (expDecaySemigroup a ha).generatorDomain := by
    rw [← hres]
    exact (expDecaySemigroup a ha).resolvent_mem_generatorDomain μ₁ _
  refine ⟨hx, ?_⟩
  rw [(expDecaySemigroup a ha).generator_eq_of_resolvent_eq μ₁ hx hres]
  change (1 : ℝ) • x - ((1 : ℝ) + a) * x = -a * x
  ring

/-! ### 2. Concrete contractive resolvent and Hille--Yosida round-trip -/

/-- Concrete non-trivial `ContractiveResolvent ℝ`: `R_α x = ((α : ℝ) + a)⁻¹ * x` for `a ≥ 0`. -/
noncomputable def expDecayResolvent (a : ℝ) (ha : 0 ≤ a) : ContractiveResolvent ℝ where
  operator α := ((α : ℝ) + a)⁻¹ • ContinuousLinearMap.id ℝ ℝ
  resolvent_identity α β := by
    ext
    have hαpos : (0 : ℝ) < α := α.2
    have hβpos : (0 : ℝ) < β := β.2
    have hα : (α : ℝ) + a ≠ 0 := by linarith
    have hβ : (β : ℝ) + a ≠ 0 := by linarith
    simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul]
    field_simp
    ring
  opNorm_le_inv α := by
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    have hpos : 0 < (α : ℝ) + a := add_pos_of_pos_of_nonneg α.2 ha
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hpos.le)]
    have hinv : ((α : ℝ) + a)⁻¹ ≤ (α : ℝ)⁻¹ := inv_anti₀ α.2 (by linarith)
    calc
      ((α : ℝ) + a)⁻¹ * ‖ContinuousLinearMap.id ℝ ℝ‖
          ≤ ((α : ℝ) + a)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_nonneg.mpr hpos.le)
      _ = ((α : ℝ) + a)⁻¹ := mul_one _
      _ ≤ (α : ℝ)⁻¹ := hinv
  denseRange α := by
    refine Function.Surjective.denseRange fun y ↦ ⟨((α : ℝ) + a) * y, ?_⟩
    have hαpos : (0 : ℝ) < α := α.2
    have hα : (α : ℝ) + a ≠ 0 := by linarith
    change ((α : ℝ) + a)⁻¹ * (((α : ℝ) + a) * y) = y
    rw [← mul_assoc, inv_mul_cancel₀ hα, one_mul]

/-- The contractive resolvent attached to `expDecaySemigroup a ha` equals `expDecayResolvent a ha`.
-/
theorem expDecaySemigroup_toContractiveResolvent (a : ℝ) (ha : 0 ≤ a) :
    (expDecaySemigroup a ha).toContractiveResolvent = expDecayResolvent a ha := by
  simp only [StronglyContinuousContractionSemigroup.toContractiveResolvent,
    expDecayResolvent, ContractiveResolvent.mk.injEq]
  funext μ
  ext
  exact expDecaySemigroup_resolvent a ha μ 1

/-- Non-trivial Hille--Yosida generation check: the Yosida-generated semigroup of
`expDecayResolvent a ha` recovers `expDecaySemigroup a ha`. -/
theorem expDecayResolvent_generatedSemigroup (a : ℝ) (ha : 0 ≤ a) :
    (expDecayResolvent a ha).generatedSemigroup = expDecaySemigroup a ha := by
  rw [← expDecaySemigroup_toContractiveResolvent a ha]
  exact (expDecaySemigroup a ha).generatedSemigroup_toContractiveResolvent

/-- Numeric closed-form evaluation of `yosidaGenerator`: for `a = 2`, `α = 3`,
`G_3(1) = 3 * (3 / (3 + 2) - 1) = -6 / 5`. -/
example :
    (expDecayResolvent 2 (by norm_num)).yosidaGenerator ⟨3, by norm_num⟩ 1 = -(6 / 5 : ℝ) := by
  change (3 : ℝ) * (((3 : ℝ) * (((3 : ℝ) + 2)⁻¹ * 1)) - 1) = -(6 / 5 : ℝ)
  norm_num

/-! ### 3. Negative counterexamples (ruling out vacuity) -/

/-- Counterexample: the growing exponential operator `exp 1 • id` fails contractivity (`‖T‖ ≤ 1`).
-/
example : ¬ ‖Real.exp 1 • ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 := by
  intro hnorm
  have h1 : ‖(Real.exp 1 • ContinuousLinearMap.id ℝ ℝ) 1‖ ≤
      ‖Real.exp 1 • ContinuousLinearMap.id ℝ ℝ‖ * ‖(1 : ℝ)‖ :=
    (Real.exp 1 • ContinuousLinearMap.id ℝ ℝ).le_opNorm 1
  have h2 : (Real.exp 1 • ContinuousLinearMap.id ℝ ℝ) (1 : ℝ) = Real.exp 1 := by
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
  rw [h2, Real.norm_eq_abs, abs_of_pos (Real.exp_pos 1), norm_one, mul_one] at h1
  have hlt : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
  linarith

/-- Counterexample: the operator `2 • id` violates the Hille--Yosida bound `‖R_1‖ ≤ 1⁻¹`. -/
example : ¬ ‖(2 : ℝ) • ContinuousLinearMap.id ℝ ℝ‖ ≤ (1 : ℝ)⁻¹ := by
  intro hnorm
  have h1 : ‖((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) 1‖ ≤
      ‖(2 : ℝ) • ContinuousLinearMap.id ℝ ℝ‖ * ‖(1 : ℝ)‖ :=
    ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).le_opNorm 1
  have h2 : ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (1 : ℝ) = 2 := by
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
  rw [h2, Real.norm_eq_abs, norm_one, mul_one] at h1
  norm_num at h1 hnorm
  linarith

/-- Counterexample: the zero operator on `ℝ` fails the `denseRange` resolvent hypothesis. -/
example : ¬ DenseRange (0 : ℝ →L[ℝ] ℝ) := by
  intro hdense
  have hmem : (1 : ℝ) ∈ closure (Set.range (0 : ℝ →L[ℝ] ℝ)) := by
    rw [hdense.closure_eq]
    trivial
  have hsub : Set.range (0 : ℝ →L[ℝ] ℝ) ⊆ ({0} : Set ℝ) := by
    rintro _ ⟨x, rfl⟩
    simp
  have hcl : (1 : ℝ) ∈ ({0} : Set ℝ) := by
    simpa only [closure_singleton] using closure_mono hsub hmem
  norm_num at hcl

end

end FracLapTest
