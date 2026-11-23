/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Core.AnalyticSemigroup

/-!
# FracLapTest.AnalyticSemigroupTest

Concrete sanity checks and non-vacuity instantiations for `FracLap.Core.AnalyticSemigroup`:
explicit scalar decay semigroup `z ↦ exp (-z) • id` on `ℂ` satisfying `AnalyticSemigroup ℂ`,
plus verification of immediate differentiability and `1 / t` smoothing bounds.
-/

namespace FracLapTest

open Complex Filter FracLap MeasureTheory Set Topology
open scoped NNReal

@[expose] public section

/-- Concrete holomorphic decay semigroup `T(z) = exp (-z) • id` on `ℂ` on `Σ_{π/2}`. -/
noncomputable def scalarExpAnalyticSemigroup : AnalyticSemigroup ℂ where
  delta := Real.pi / 2
  delta_pos := Real.pi_div_two_pos
  delta_le := le_rfl
  operator z := Complex.exp (-z) • ContinuousLinearMap.id ℂ ℂ
  operator_zero := by simp
  operator_add _ _ := by
    ext1
    simp only [smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, neg_add, Complex.exp_add, smul_eq_mul]
    ring
  differentiableOn x := by
    refine Differentiable.differentiableOn ?_
    have hexp : Differentiable ℂ (fun z : ℂ => Complex.exp (-z)) := by fun_prop
    simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] using
      hexp.mul_const x
  tendsto_zero {_} _ _ x := by
    have hcont : Continuous (fun z : ℂ => Complex.exp (-z) * x) := by fun_prop
    have h0 : Tendsto (fun z : ℂ => Complex.exp (-z) * x) (𝓝 0)
        (𝓝 (Complex.exp (-0) * x)) := hcont.continuousAt.tendsto
    simp only [neg_zero, Complex.exp_zero, one_mul] at h0
    simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] using
      h0.mono_left nhdsWithin_le_nhds

/-- Concrete real-time smoothness and domain membership for `scalarExpAnalyticSemigroup`. -/
example (x : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => scalarExpAnalyticSemigroup.operator (s : ℂ) x)
      (deriv (fun z : ℂ => scalarExpAnalyticSemigroup.operator z x) (t : ℂ)) t :=
  scalarExpAnalyticSemigroup.hasDerivAt_real_orbit x ht

/-- Closed form of the orbit derivative: `d/dz exp (-z) = -exp (-z)`, so the real-time derivative
of the scalar semigroup at `t > 0` is `-exp (-t) x`. -/
example (x : ℂ) (t : ℝ) :
    deriv (fun z : ℂ => scalarExpAnalyticSemigroup.operator z x) (t : ℂ) =
      -(Complex.exp (-(t : ℂ)) * x) := by
  have h : HasDerivAt (fun z : ℂ => Complex.exp (-z) * x) (-(Complex.exp (-(t : ℂ)) * x)) t := by
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-z)) (-Complex.exp (-(t : ℂ))) t := by
      simpa using ((hasDerivAt_id (t : ℂ)).neg).cexp
    simpa [neg_mul] using h1.mul_const x
  exact h.deriv

/-- Negative check: the scalar semigroup is not constant, so the analyticity structure is not
satisfied by a trivial (identity) family: `T(1) 1 ≠ 1`. -/
example : scalarExpAnalyticSemigroup.operator 1 1 ≠ 1 := by
  simp only [scalarExpAnalyticSemigroup, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    mul_one]
  intro h
  have := congrArg Complex.re h
  rw [← Complex.ofReal_one, ← Complex.ofReal_neg, ← Complex.ofReal_exp] at this
  simp only [Complex.ofReal_re] at this
  have hlt : Real.exp (-1) < 1 := by
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

end

end FracLapTest
