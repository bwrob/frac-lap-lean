/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.HalfLine.RestrictedSemigroup
import Mathlib.Tactic.NormNum

/-!
# FracLapTest.RestrictedSemigroupTest

Anti-vacuity witnesses, resolvent/semigroup sanity checks, sub-Markov preservation examples,
and non-triviality checks for `FracLap.HalfLine.RestrictedSemigroup`.
-/

namespace FracLapTest

open FracLap MeasureTheory Real Set

@[expose] public section

/-- Concrete contractive resolvent and `C₀`-contraction semigroup instantiation at `α = 1`,
`1 / 2`, and `3 / 2`. -/
example (μ : PositiveShift) (t : NNReal) (f : L2IoiR) :
    ‖(restrictedFracLapResolvent 1 fractionalExponent_one).operator μ f‖ ≤ (μ : ℝ)⁻¹ * ‖f‖ ∧
      ‖restrictedFracLapSemigroup (1 / 2) ⟨by norm_num, by norm_num⟩ t f‖ ≤ ‖f‖ ∧
      ‖restrictedFracLapSemigroup (3 / 2) ⟨by norm_num, by norm_num⟩ t f‖ ≤ ‖f‖ :=
  ⟨((restrictedFracLapResolvent 1 fractionalExponent_one).operator μ).le_opNorm f |>.trans
      (mul_le_mul_of_nonneg_right
        ((restrictedFracLapResolvent 1 fractionalExponent_one).opNorm_le_inv μ) (norm_nonneg f)),
    (restrictedFracLapSemigroup (1 / 2) ⟨by norm_num, by norm_num⟩).norm_apply_le t f,
    (restrictedFracLapSemigroup (3 / 2) ⟨by norm_num, by norm_num⟩).norm_apply_le t f⟩

/-- Semigroup law and resolvent identification for `restrictedFracLapSemigroup`. -/
example (α : ℝ) (hα : FractionalExponent α) (s t : NNReal) (μ : PositiveShift) (f : L2IoiR) :
    restrictedFracLapSemigroup α hα (s + t) f =
      restrictedFracLapSemigroup α hα s (restrictedFracLapSemigroup α hα t f) ∧
    (restrictedFracLapSemigroup α hα).resolvent μ f =
      (restrictedFracLapResolvent α hα).operator μ f :=
  ⟨by rw [← ContinuousLinearMap.comp_apply, (restrictedFracLapSemigroup α hα).operator_add],
    DFunLike.congr_fun (restrictedFracLapSemigroup_resolvent_eq α hα μ) f⟩

/-- Positivity and sub-Markov `L^∞` preservation on a bounded nonnegative datum (`0 ≤ f ≤ 1`). -/
example (α : ℝ) (hα : FractionalExponent α) (t : NNReal) {f : L2IoiR}
    (h0 : ∀ᵐ x : ℝ ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ)), 0 ≤ (f : ℝ → ℝ) x)
    (h1 : ∀ᵐ x : ℝ ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ)), (f : ℝ → ℝ) x ≤ 1) :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ)),
      0 ≤ (restrictedFracLapSemigroup α hα t f : ℝ → ℝ) x ∧
        (restrictedFracLapSemigroup α hα t f : ℝ → ℝ) x ≤ 1 :=
  (restrictedFracLapSemigroup_ae_nonneg hα t h0).and
    (restrictedFracLapSemigroup_ae_le hα t zero_le_one h1)

/-- Non-vacuity check: `restrictedFracLapResolvent 1` acts nontrivially at `μ = 1`. -/
example :
    ∃ f : L2IoiR,
      (∀ᵐ x : ℝ ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ)), 0 ≤ (f : ℝ → ℝ) x) ∧
      (restrictedFracLapResolvent 1 fractionalExponent_one).operator ⟨1, one_pos⟩ f ≠ 0 ∧
      0 < @inner ℝ L2IoiR _ f
        ((restrictedFracLapResolvent 1 fractionalExponent_one).operator ⟨1, one_pos⟩ f) :=
  exists_restrictedFracLapSemigroup_nontrivial fractionalExponent_one ⟨1, one_pos⟩

/-- Weak-form Friedrichs generator characterization (`prop:formoperator`, `thm:s0_generates`)
and dissipativity/symmetry checks: every `u ∈ D(A₀)` satisfies `⟨A₀ u, u⟩ = -B^α_0(u', u') ≤ 0`
and symmetry `⟨A₀ u, v⟩ = ⟨u, A₀ v⟩`, and `restrictedL2Map` preserves nonzero elements. -/
example {α : ℝ} (hα : FractionalExponent α) (u v : L2IoiR)
    (hu : u ∈ (restrictedFracLapSemigroup α hα).generatorDomain)
    (hv : v ∈ (restrictedFracLapSemigroup α hα).generatorDomain)
    {w : RestrictedGagliardoSpace α} (hw : w ≠ 0) :
    (∃ (u' : RestrictedGagliardoSpace α) (f : L2IoiR),
        restrictedL2Map α u' = u ∧
        (∀ z : RestrictedGagliardoSpace α,
          (restrictedGagliardoForm α).form u' z = @inner ℝ L2IoiR _ f (restrictedL2Map α z)) ∧
        @inner ℝ L2IoiR _ ((restrictedFracLapSemigroup α hα).generator ⟨u, hu⟩) u ≤ 0) ∧
      @inner ℝ L2IoiR _ ((restrictedFracLapSemigroup α hα).generator ⟨u, hu⟩) v =
        @inner ℝ L2IoiR _ u ((restrictedFracLapSemigroup α hα).generator ⟨v, hv⟩) ∧
      restrictedL2Map α w ≠ 0 := by
  refine ⟨?_, inner_generator_restrictedFracLapSemigroup_symm hα hu hv, ?_⟩
  · obtain ⟨u', hu', hform⟩ := restrictedFracLapSemigroup_mem_generatorDomain_forward hα hu
    refine ⟨u', -((restrictedFracLapSemigroup α hα).generator ⟨u, hu⟩), hu', hform, ?_⟩
    rw [inner_generator_restrictedFracLapSemigroup_eq_neg_form hα hu u' hu']
    exact neg_nonpos.mpr ((restrictedGagliardoForm α).accretive u')
  · intro h0
    exact hw (restrictedL2Map_injective α (h0.trans (map_zero (restrictedL2Map α)).symm))

end

end FracLapTest
