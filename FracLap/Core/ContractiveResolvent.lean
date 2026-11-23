/-
Copyright (c) 2026 Scott Armstrong, Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Bartosz Wróblewski
-/
module

public import FracLap.Core.C0Semigroup
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Contractive resolvent families and strong operator limits

This module provides positive-shift limit helpers, dense-core convergence extensions for
contractions, strong operator limits of pointwise Cauchy contraction sequences, and the
`ContractiveResolvent` interface with its normalization estimate `α R_α → id` as `α → ∞`,
adapted and verified on Mathlib `v4.36.0` from Scott Armstrong's `scottnarmstrong/MarkovProcess`
(`MarkovProcess.Semigroup`).
-/

@[expose] public section

namespace FracLap

open Filter Set Topology

/-! ### Positive shifts and vanishing square bounds -/

/-- Positive real parameters, ordered by their underlying real values. -/
abbrev PositiveShift := Set.Ioi (0 : ℝ)

/-- Positive parameters tend to infinity in the ambient real line. -/
theorem tendsto_positiveShift_coe_atTop :
    Tendsto (fun α : PositiveShift ↦ (α : ℝ)) atTop atTop :=
  (tendsto_comp_val_Ioi_atTop (a := (0 : ℝ))).2 tendsto_id

/-- The inverse of a positive parameter tends to zero as the parameter tends to infinity. -/
theorem tendsto_positiveShift_inv_atTop_zero :
    Tendsto (fun α : PositiveShift ↦ (α : ℝ)⁻¹) atTop (nhds 0) :=
  (tendsto_comp_val_Ioi_atTop (a := (0 : ℝ))).2 tendsto_inv_atTop_zero

/-- A fixed real constant times the inverse parameter tends to zero. -/
theorem tendsto_const_mul_positiveShift_inv_atTop_zero (C : ℝ) :
    Tendsto (fun α : PositiveShift ↦ C * (α : ℝ)⁻¹) atTop (nhds 0) := by
  simpa only [mul_zero] using
    (tendsto_const_nhds (x := C)).mul tendsto_positiveShift_inv_atTop_zero

/-- A nonnegative quantity tends to zero if its square is bounded by a quantity
that tends to zero. This avoids introducing square roots in limit estimates. -/
theorem tendsto_zero_of_nonneg_sq_le {ι : Type*} {l : Filter ι}
    {e r : ι → ℝ} (he : ∀ i, 0 ≤ e i) (her : ∀ i, (e i) ^ 2 ≤ r i)
    (hr : Tendsto r l (nhds 0)) :
    Tendsto e l (nhds 0) := by
  rw [Metric.tendsto_nhds] at hr ⊢
  intro ε hε
  filter_upwards [hr (ε ^ 2) (sq_pos_of_pos hε)] with i hi
  have he_sq_lt : (e i) ^ 2 < ε ^ 2 := by
    calc
      (e i) ^ 2 ≤ r i := her i
      _ ≤ |r i| := le_abs_self (r i)
      _ = dist (r i) 0 := by rw [Real.dist_eq, sub_zero]
      _ < ε ^ 2 := hi
  have he_lt : e i < ε :=
    (sq_lt_sq₀ (he i) hε.le).1 he_sq_lt
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (he i)]
  exact he_lt

/-! ### Convergence from a dense core -/

/-- A family of continuous linear contractions that converges to the identity
on the range of a dense continuous linear map converges to the identity everywhere. -/
theorem tendsto_of_denseRange_of_opNorm_le_one
    {E F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter ι} (T : ι → E →L[ℝ] E) (D : F →L[ℝ] E)
    (hT : ∀ i, ‖T i‖ ≤ 1) (hD : DenseRange D)
    (hcore : ∀ v, Tendsto (fun i ↦ T i (D v)) l (nhds (D v))) :
    ∀ f, Tendsto (fun i ↦ T i f) l (nhds f) := by
  intro f
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨v, hv⟩ := hD.exists_dist_lt f (div_pos hε (by norm_num : (0 : ℝ) < 3))
  have hv' : dist (D v) f < ε / 3 := by
    rw [dist_comm]
    exact hv
  have hcore_eventually : ∀ᶠ i in l, dist (T i (D v)) (D v) < ε / 3 :=
    (Metric.tendsto_nhds.mp (hcore v)) (ε / 3) (div_pos hε (by norm_num))
  filter_upwards [hcore_eventually] with i hi
  have hcontract : dist (T i f) (T i (D v)) ≤ dist f (D v) := by
    calc
      dist (T i f) (T i (D v)) ≤ ‖T i‖ * dist f (D v) := (T i).dist_le_opNorm f (D v)
      _ ≤ 1 * dist f (D v) := mul_le_mul_of_nonneg_right (hT i) dist_nonneg
      _ = dist f (D v) := one_mul _
  calc
    dist (T i f) f ≤ dist (T i f) (T i (D v)) + dist (T i (D v)) f :=
      dist_triangle _ _ _
    _ ≤ dist (T i f) (T i (D v)) +
        (dist (T i (D v)) (D v) + dist (D v) f) :=
      add_le_add le_rfl (dist_triangle _ _ _)
    _ ≤ dist f (D v) + (dist (T i (D v)) (D v) + dist (D v) f) :=
      add_le_add hcontract le_rfl
    _ < ε / 3 + (ε / 3 + ε / 3) := add_lt_add hv (add_lt_add hi hv')
    _ = ε := by ring

/-- Pointwise Cauchy convergence on the range of a dense continuous linear map
extends to the whole space for a sequence of contractions. -/
theorem cauchySeq_of_denseRange_of_opNorm_le_one
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ℕ → E →L[ℝ] E) (D : F →L[ℝ] E)
    (hT : ∀ n, ‖T n‖ ≤ 1) (hD : DenseRange D)
    (hcore : ∀ v, CauchySeq (fun n ↦ T n (D v))) :
    ∀ x, CauchySeq (fun n ↦ T n x) := by
  intro x
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨v, hv⟩ := hD.exists_dist_lt x (div_pos hε (by norm_num : (0 : ℝ) < 3))
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hcore v) (ε / 3)
    (div_pos hε (by norm_num))
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  have hm_contract : dist (T m x) (T m (D v)) ≤ dist x (D v) := by
    calc
      dist (T m x) (T m (D v)) ≤ ‖T m‖ * dist x (D v) := (T m).dist_le_opNorm x (D v)
      _ ≤ 1 * dist x (D v) := mul_le_mul_of_nonneg_right (hT m) dist_nonneg
      _ = dist x (D v) := one_mul _
  have hn_contract : dist (T n (D v)) (T n x) ≤ dist (D v) x := by
    calc
      dist (T n (D v)) (T n x) ≤ ‖T n‖ * dist (D v) x := (T n).dist_le_opNorm (D v) x
      _ ≤ 1 * dist (D v) x := mul_le_mul_of_nonneg_right (hT n) dist_nonneg
      _ = dist (D v) x := one_mul _
  have hv' : dist (D v) x < ε / 3 := by
    rw [dist_comm]
    exact hv
  calc
    dist (T m x) (T n x) ≤
        dist (T m x) (T m (D v)) + dist (T m (D v)) (T n x) :=
      dist_triangle _ _ _
    _ ≤ dist (T m x) (T m (D v)) +
        (dist (T m (D v)) (T n (D v)) + dist (T n (D v)) (T n x)) :=
      add_le_add le_rfl (dist_triangle _ _ _)
    _ < ε / 3 + (ε / 3 + ε / 3) :=
      add_lt_add (lt_of_le_of_lt hm_contract hv)
        (add_lt_add (hN m hm n hn) (lt_of_le_of_lt hn_contract hv'))
    _ = ε := by ring

/-! ### Strong operator limits of contractions -/

section StrongOperatorLimit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Completeness

variable [CompleteSpace E]

/-- The continuous linear map obtained as the pointwise limit of a pointwise
Cauchy sequence of contractions. -/
noncomputable def strongOperatorLimit (T : ℕ → E →L[ℝ] E)
    (hT : ∀ n, ‖T n‖ ≤ 1) (hcauchy : ∀ x, CauchySeq (fun n ↦ T n x)) :
    E →L[ℝ] E :=
  ContinuousLinearMap.ofTendstoOfBoundedRange
    (fun x ↦ limUnder atTop (fun n ↦ T n x)) T
    (tendsto_pi_nhds.2 fun x ↦ (hcauchy x).tendsto_limUnder)
    (isBounded_iff_forall_norm_le.2 ⟨1, Set.forall_mem_range.2 fun n ↦ hT n⟩)

/-- The defining pointwise convergence of `strongOperatorLimit`. -/
theorem tendsto_strongOperatorLimit_apply (T : ℕ → E →L[ℝ] E)
    (hT : ∀ n, ‖T n‖ ≤ 1) (hcauchy : ∀ x, CauchySeq (fun n ↦ T n x)) (x : E) :
    Tendsto (fun n ↦ T n x) atTop (nhds (strongOperatorLimit T hT hcauchy x)) := by
  change Tendsto (fun n ↦ T n x) atTop (nhds (limUnder atTop (fun n ↦ T n x)))
  exact (hcauchy x).tendsto_limUnder

/-- The strong operator limit of contractions is again a contraction pointwise. -/
theorem norm_strongOperatorLimit_apply_le (T : ℕ → E →L[ℝ] E)
    (hT : ∀ n, ‖T n‖ ≤ 1) (hcauchy : ∀ x, CauchySeq (fun n ↦ T n x)) (x : E) :
    ‖strongOperatorLimit T hT hcauchy x‖ ≤ ‖x‖ := by
  refine le_of_tendsto (tendsto_strongOperatorLimit_apply T hT hcauchy x).norm ?_
  exact Eventually.of_forall fun n ↦
    calc
      ‖T n x‖ ≤ ‖T n‖ * ‖x‖ := (T n).le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (hT n) (norm_nonneg x)
      _ = ‖x‖ := one_mul _

/-- The strong operator limit of contractions has operator norm at most one. -/
theorem norm_strongOperatorLimit_le_one (T : ℕ → E →L[ℝ] E)
    (hT : ∀ n, ‖T n‖ ≤ 1) (hcauchy : ∀ x, CauchySeq (fun n ↦ T n x)) :
    ‖strongOperatorLimit T hT hcauchy‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x ↦ by
    simpa only [one_mul] using norm_strongOperatorLimit_apply_le T hT hcauchy x

end Completeness

/-- Two pointwise operator limits may be composed when the outer approximating
operators are contractions. -/
theorem tendsto_apply_comp_of_opNorm_le_one
    (T U : ℕ → E →L[ℝ] E) (Tlim Ulim : E →L[ℝ] E)
    (hT : ∀ n, ‖T n‖ ≤ 1)
    (hTlim : ∀ x, Tendsto (fun n ↦ T n x) atTop (nhds (Tlim x)))
    (hUlim : ∀ x, Tendsto (fun n ↦ U n x) atTop (nhds (Ulim x))) (x : E) :
    Tendsto (fun n ↦ T n (U n x)) atTop (nhds (Tlim (Ulim x))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hU_eventually : ∀ᶠ n in atTop, dist (U n x) (Ulim x) < ε / 2 :=
    Metric.tendsto_nhds.mp (hUlim x) (ε / 2) hε2
  have hT_eventually : ∀ᶠ n in atTop, dist (T n (Ulim x)) (Tlim (Ulim x)) < ε / 2 :=
    Metric.tendsto_nhds.mp (hTlim (Ulim x)) (ε / 2) hε2
  filter_upwards [hU_eventually, hT_eventually] with n hUn hTn
  have hcontract : dist (T n (U n x)) (T n (Ulim x)) ≤ dist (U n x) (Ulim x) := by
    calc
      dist (T n (U n x)) (T n (Ulim x)) ≤ ‖T n‖ * dist (U n x) (Ulim x) :=
        (T n).dist_le_opNorm (U n x) (Ulim x)
      _ ≤ 1 * dist (U n x) (Ulim x) := mul_le_mul_of_nonneg_right (hT n) dist_nonneg
      _ = dist (U n x) (Ulim x) := one_mul _
  calc
    dist (T n (U n x)) (Tlim (Ulim x)) ≤
        dist (T n (U n x)) (T n (Ulim x)) +
          dist (T n (Ulim x)) (Tlim (Ulim x)) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 :=
      lt_of_le_of_lt (add_le_add hcontract le_rfl) (add_lt_add hUn hTn)
    _ = ε := add_halves ε

end StrongOperatorLimit

/-! ### Contractive resolvent families -/

/-- A resolvent family on a real normed space with the contraction bound and
dense range needed for normalization at large positive shifts. -/
structure ContractiveResolvent (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The resolvent at a positive real shift. -/
  operator : PositiveShift → E →L[ℝ] E
  /-- The resolvent identity, with the sign convention for `(α + A)⁻¹`. -/
  resolvent_identity : ∀ α β,
    operator α - operator β =
      ((β : ℝ) - (α : ℝ)) • ((operator α).comp (operator β))
  /-- The Hille--Yosida contraction estimate. -/
  opNorm_le_inv : ∀ α, ‖operator α‖ ≤ (α : ℝ)⁻¹
  /-- Every resolvent has dense range. -/
  denseRange : ∀ α, DenseRange (operator α)

namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The normalized resolvent `α R_α`. -/
def scaledOperator (R : ContractiveResolvent E) (α : PositiveShift) : E →L[ℝ] E :=
  (α : ℝ) • R.operator α

/-- The normalized resolvent is a contraction in operator norm. -/
theorem opNorm_scaledOperator_le_one (R : ContractiveResolvent E) (α : PositiveShift) :
    ‖R.scaledOperator α‖ ≤ 1 := by
  have hα : 0 ≤ (α : ℝ) := α.property.le
  calc
    ‖R.scaledOperator α‖ ≤ ‖(α : ℝ)‖ * ‖R.operator α‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ = (α : ℝ) * ‖R.operator α‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hα]
    _ ≤ (α : ℝ) * (α : ℝ)⁻¹ := mul_le_mul_of_nonneg_left (R.opNorm_le_inv α) hα
    _ = 1 := mul_inv_cancel₀ α.property.ne'

/-- Pointwise contraction of the normalized resolvent. -/
theorem norm_scaledOperator_apply_le (R : ContractiveResolvent E)
    (α : PositiveShift) (x : E) :
    ‖R.scaledOperator α x‖ ≤ ‖x‖ := by
  calc
    ‖R.scaledOperator α x‖ ≤ ‖R.scaledOperator α‖ * ‖x‖ :=
      (R.scaledOperator α).le_opNorm x
    _ ≤ 1 * ‖x‖ :=
      mul_le_mul_of_nonneg_right (R.opNorm_scaledOperator_le_one α) (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-- Resolvents at two positive shifts commute. -/
theorem operator_comm (R : ContractiveResolvent E) (α β : PositiveShift) :
    (R.operator α).comp (R.operator β) = (R.operator β).comp (R.operator α) := by
  by_cases hαβ : (α : ℝ) = (β : ℝ)
  · have : α = β := Subtype.ext hαβ
    subst β
    rfl
  · have hβα : (β : ℝ) - (α : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hαβ)
    apply smul_right_injective (E →L[ℝ] E) hβα
    calc
      ((β : ℝ) - (α : ℝ)) • ((R.operator α).comp (R.operator β)) =
          R.operator α - R.operator β := (R.resolvent_identity α β).symm
      _ = ((β : ℝ) - (α : ℝ)) • ((R.operator β).comp (R.operator α)) := by
        calc
          R.operator α - R.operator β = -(R.operator β - R.operator α) := by abel
          _ = -((α : ℝ) - (β : ℝ)) • ((R.operator β).comp (R.operator α)) := by
            rw [R.resolvent_identity β α, neg_smul]
          _ = ((β : ℝ) - (α : ℝ)) • ((R.operator β).comp (R.operator α)) := by
            rw [neg_sub]

/-- The resolvent identity arranged as the core normalization formula. -/
theorem scaledOperator_apply_sub_on_range (R : ContractiveResolvent E)
    (α β : PositiveShift) (y : E) :
    R.scaledOperator α (R.operator β y) - R.operator β y =
      R.operator α ((β : ℝ) • R.operator β y - y) := by
  have h := DFunLike.congr_fun (R.resolvent_identity α β) y
  change
    R.operator α y - R.operator β y =
      ((β : ℝ) - (α : ℝ)) • R.operator α (R.operator β y) at h
  change
    (α : ℝ) • R.operator α (R.operator β y) - R.operator β y =
      R.operator α ((β : ℝ) • R.operator β y - y)
  rw [map_sub, map_smul]
  change
    (α : ℝ) • R.operator α (R.operator β y) - R.operator β y =
      (β : ℝ) • R.operator α (R.operator β y) - R.operator α y
  calc
    (α : ℝ) • R.operator α (R.operator β y) - R.operator β y =
        (α : ℝ) • R.operator α (R.operator β y) +
          (R.operator α y - R.operator β y) - R.operator α y := by abel
    _ = (α : ℝ) • R.operator α (R.operator β y) +
          ((β : ℝ) - (α : ℝ)) • R.operator α (R.operator β y) - R.operator α y := by
      rw [h]
    _ = (β : ℝ) • R.operator α (R.operator β y) - R.operator α y := by module

/-- Normalization converges on the range of any fixed resolvent. -/
theorem tendsto_scaledOperator_apply_on_range (R : ContractiveResolvent E)
    (μ : PositiveShift) (y : E) :
    Tendsto (fun α : PositiveShift ↦ R.scaledOperator α (R.operator μ y))
      atTop (nhds (R.operator μ y)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ α : PositiveShift,
      ‖R.scaledOperator α (R.operator μ y) - R.operator μ y‖ ≤
        ‖(μ : ℝ) • R.operator μ y - y‖ * (α : ℝ)⁻¹ := by
    intro α
    rw [R.scaledOperator_apply_sub_on_range α μ y]
    calc
      ‖R.operator α ((μ : ℝ) • R.operator μ y - y)‖ ≤
          ‖R.operator α‖ * ‖(μ : ℝ) • R.operator μ y - y‖ :=
        (R.operator α).le_opNorm _
      _ ≤ (α : ℝ)⁻¹ * ‖(μ : ℝ) • R.operator μ y - y‖ :=
        mul_le_mul_of_nonneg_right (R.opNorm_le_inv α) (norm_nonneg _)
      _ = ‖(μ : ℝ) • R.operator μ y - y‖ * (α : ℝ)⁻¹ := mul_comm _ _
  simpa only [dist_eq_norm] using
    squeeze_zero (fun α ↦ norm_nonneg _) hbound
      (tendsto_const_mul_positiveShift_inv_atTop_zero
        ‖(μ : ℝ) • R.operator μ y - y‖)

/-- The normalized resolvents converge strongly to the identity. -/
theorem tendsto_scaledOperator_apply (R : ContractiveResolvent E) (x : E) :
    Tendsto (fun α : PositiveShift ↦ R.scaledOperator α x) atTop (nhds x) :=
  tendsto_of_denseRange_of_opNorm_le_one
    R.scaledOperator (R.operator ⟨1, by norm_num⟩)
    R.opNorm_scaledOperator_le_one (R.denseRange ⟨1, by norm_num⟩)
    (R.tendsto_scaledOperator_apply_on_range ⟨1, by norm_num⟩) x

end ContractiveResolvent

end FracLap
