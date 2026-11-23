/-
Copyright (c) 2026 Scott Armstrong, Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import FracLap.Core.C0Semigroup
public import FracLap.Core.ContractiveResolvent
public import FracLap.Core.HilleYosidaGeneration
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The Hille--Yosida bijection between semigroups and contractive resolvents

This module establishes the full two-way correspondence between strongly continuous contraction
semigroups and contractive resolvent families on a real Banach space `E`, adapted and verified
on Mathlib `v4.36.0` from Scott Armstrong's `scottnarmstrong/MarkovProcess`
(`MarkovProcess.Semigroup`):
- Injectivity of `μ - L` for `μ > 0` via exponential defect and Grönwall's inequality
  (`operator_eq_exp_smul_of_generator_eq_smul`, `eq_zero_of_generator_eq_smul`,
  `eq_of_smul_sub_generator_eq`).
- The Laplace-transform resolvent `S.resolvent μ x = ∫₀^∞ e^{-μ t} S t x dt` and its package
  `S.toContractiveResolvent : ContractiveResolvent E`.
- Identification of the generator of `R.generatedSemigroup` (`generator_operator_apply`,
  `operator_smul_sub_generator`, `generatorDomain_eq_range`).
- Both round-trip identities of the Hille--Yosida bijection:
  `S.toContractiveResolvent.generatedSemigroup = S` (`generatedSemigroup_toContractiveResolvent`)
  and `R.generatedSemigroup.toContractiveResolvent = R`
  (`toContractiveResolvent_generatedSemigroup`).
-/

@[expose] public section

namespace FracLap

open Filter MeasureTheory NormedSpace Set Topology
open scoped NNReal

/-! ### Injectivity of `μ - L` via exponential defects -/

namespace StronglyContinuousContractionSemigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)

/-- The defect between the orbit of a vector and the scalar exponential `exp (μ t)` times it. -/
private def exponentialDefect (μ : ℝ) (f : E) (s : ℝ) : E :=
  S (Real.toNNReal s) f - Real.exp (μ * s) • f

private theorem continuous_exponentialDefect (μ : ℝ) (f : E) :
    Continuous (S.exponentialDefect μ f) :=
  (S.continuous_operator_toNNReal f).sub
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul continuous_const)

private theorem exponentialDefect_zero (μ : ℝ) (f : E) : S.exponentialDefect μ f 0 = 0 := by
  rw [exponentialDefect, Real.toNNReal_zero, S.zero_apply, mul_zero, Real.exp_zero, one_smul,
    sub_self]

private theorem hasDerivWithinAt_exponentialDefect {μ : ℝ} (f : S.generatorDomain)
    (hgen : S.generator f = μ • (f : E)) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (S.exponentialDefect μ f) (μ • S.exponentialDefect μ f s) (Ici s) s := by
  have horbit := S.hasDerivWithinAt_Ici f (Real.toNNReal s)
  rw [Real.coe_toNNReal s hs] at horbit
  have hlin : HasDerivAt (fun u : ℝ ↦ μ * u) μ s := by
    simpa using (hasDerivAt_id s).const_mul μ
  have hexp : HasDerivAt (fun u : ℝ ↦ Real.exp (μ * u) • (f : E))
      ((Real.exp (μ * s) * μ) • (f : E)) s := hlin.exp.smul_const (f : E)
  have hsub := horbit.sub hexp.hasDerivWithinAt
  rw [hgen, map_smul] at hsub
  have hval : μ • S (Real.toNNReal s) (f : E) - (Real.exp (μ * s) * μ) • (f : E)
      = μ • S.exponentialDefect μ (f : E) s := by
    rw [exponentialDefect, smul_sub, smul_smul, mul_comm μ (Real.exp (μ * s))]
  rw [hval] at hsub
  exact hsub

/-- **An eigenvector of the generator has an exponential orbit.** If `f` lies in the generator
domain and `L f = μ f`, then `S t f = exp (μ t) f` at every time `t`. -/
theorem operator_eq_exp_smul_of_generator_eq_smul {μ : ℝ} (f : S.generatorDomain)
    (hgen : S.generator f = μ • (f : E)) (t : ℝ≥0) :
    S t (f : E) = Real.exp (μ * t) • (f : E) := by
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := S.exponentialDefect μ f) (f' := fun s ↦ μ • S.exponentialDefect μ f s) (K := |μ|)
    (a := 0) (b := (t : ℝ)) (S.continuous_exponentialDefect μ f).continuousOn
    (fun s hs ↦ S.hasDerivWithinAt_exponentialDefect f hgen hs.1)
    (S.exponentialDefect_zero μ f)
    (fun s _ ↦ by rw [norm_smul, Real.norm_eq_abs])
    (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
  rw [exponentialDefect, Real.toNNReal_coe, sub_eq_zero] at hzero
  exact hzero

/-- **Positive eigenvalues are excluded.** For `μ > 0`, a vector of the generator domain with
`L f = μ f` vanishes: its orbit would grow like `exp (μ t)`, contradicting contractivity. -/
theorem eq_zero_of_generator_eq_smul {μ : ℝ} (hμ : 0 < μ) (f : S.generatorDomain)
    (hgen : S.generator f = μ • (f : E)) : (f : E) = 0 := by
  have hcontract : Real.exp μ * ‖(f : E)‖ ≤ ‖(f : E)‖ := by
    have hle := S.norm_apply_le 1 (f : E)
    rw [S.operator_eq_exp_smul_of_generator_eq_smul f hgen 1, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), NNReal.coe_one, mul_one] at hle
    exact hle
  have hone : 1 < Real.exp μ := by
    have hexp := Real.add_one_le_exp μ
    linarith only [hexp, hμ]
  rw [← norm_le_zero_iff]
  by_contra hpos
  push Not at hpos
  have hstrict : 1 * ‖(f : E)‖ < Real.exp μ * ‖(f : E)‖ :=
    mul_lt_mul_of_pos_right hone hpos
  rw [one_mul] at hstrict
  linarith only [hstrict, hcontract]

/-- **Injectivity of `μ - L`.** For `μ > 0`, two vectors of the generator domain with the same
image under `μ - L` are equal. -/
theorem eq_of_smul_sub_generator_eq {μ : ℝ} (hμ : 0 < μ) (f g : S.generatorDomain)
    (h : μ • (f : E) - S.generator f = μ • (g : E) - S.generator g) : (f : E) = (g : E) := by
  have hker : S.generator (f - g) = μ • ((f - g : S.generatorDomain) : E) := by
    rw [map_sub, Submodule.coe_sub, smul_sub]
    have h0 : μ • (f : E) - S.generator f - (μ • (g : E) - S.generator g) = 0 :=
      sub_eq_zero_of_eq h
    refine eq_of_sub_eq_zero ?_
    rw [← neg_zero, ← h0]
    abel
  have hzero := S.eq_zero_of_generator_eq_smul hμ (f - g) hker
  rw [Submodule.coe_sub, sub_eq_zero] at hzero
  exact hzero

end

end StronglyContinuousContractionSemigroup

/-! ### The Laplace-transform resolvent of a contraction semigroup -/

namespace StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (S : StronglyContinuousContractionSemigroup E)

noncomputable section

section Integrand

/-- The integrand of the Laplace transform of the orbit of `x` at the shift `μ`, read in the
real time variable. -/
def laplaceIntegrand (μ : ℝ) (x : E) (t : ℝ) : E :=
  Real.exp (-μ * t) • S (Real.toNNReal t) x

omit [CompleteSpace E] in
/-- The Laplace integrand, unfolded. -/
theorem laplaceIntegrand_apply (μ : ℝ) (x : E) (t : ℝ) :
    S.laplaceIntegrand μ x t = Real.exp (-μ * t) • S (Real.toNNReal t) x :=
  rfl

omit [CompleteSpace E] in
/-- The Laplace integrand is continuous in time. -/
theorem continuous_laplaceIntegrand (μ : ℝ) (x : E) : Continuous (S.laplaceIntegrand μ x) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    (S.continuous_operator_toNNReal x)

omit [CompleteSpace E] in
/-- The Laplace integrand is dominated by the exponential weight. -/
theorem norm_laplaceIntegrand_le (μ : ℝ) (x : E) (t : ℝ) :
    ‖S.laplaceIntegrand μ x t‖ ≤ Real.exp (-μ * t) * ‖x‖ := by
  rw [laplaceIntegrand_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (S.norm_apply_le _ x) (Real.exp_pos _).le

omit [CompleteSpace E] in
/-- The Laplace integrand is integrable on `(0, ∞)` for a positive shift. -/
theorem integrableOn_laplaceIntegrand {μ : ℝ} (hμ : 0 < μ) (x : E) :
    IntegrableOn (S.laplaceIntegrand μ x) (Ioi 0) :=
  Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hμ).mul_const ‖x‖)
    (S.continuous_laplaceIntegrand μ x).aestronglyMeasurable.restrict
    (Eventually.of_forall fun t ↦ S.norm_laplaceIntegrand_le μ x t)

omit [CompleteSpace E] in
/-- The Laplace integrand is additive in the vector. -/
theorem laplaceIntegrand_add (μ : ℝ) (x y : E) :
    S.laplaceIntegrand μ (x + y) = S.laplaceIntegrand μ x + S.laplaceIntegrand μ y := by
  funext t
  simp only [laplaceIntegrand_apply, map_add, smul_add, Pi.add_apply]

omit [CompleteSpace E] in
/-- The Laplace integrand is homogeneous in the vector. -/
theorem laplaceIntegrand_smul (μ : ℝ) (c : ℝ) (x : E) :
    S.laplaceIntegrand μ (c • x) = c • S.laplaceIntegrand μ x := by
  funext t
  simp only [laplaceIntegrand_apply, map_smul, Pi.smul_apply]
  exact smul_comm _ _ _

omit [CompleteSpace E] in
/-- The semigroup commutes with the Laplace integrand. -/
theorem laplaceIntegrand_operator (μ : ℝ) (h : ℝ≥0) (x : E) (t : ℝ) :
    S h (S.laplaceIntegrand μ x t) = S.laplaceIntegrand μ (S h x) t := by
  simp only [laplaceIntegrand_apply, map_smul, S.commute_apply]

omit [CompleteSpace E] in
/-- The Laplace integrand tends to zero at infinity for a positive shift. -/
theorem tendsto_laplaceIntegrand_atTop {μ : ℝ} (hμ : 0 < μ) (x : E) :
    Tendsto (S.laplaceIntegrand μ x) atTop (𝓝 0) := by
  have hexp : Tendsto (fun t : ℝ ↦ Real.exp (-μ * t)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hμ))
    refine this.congr fun t ↦ ?_
    simp only [Function.comp, id, neg_mul]
  refine squeeze_zero_norm (fun t ↦ S.norm_laplaceIntegrand_le μ x t) ?_
  simpa using hexp.mul_const ‖x‖

omit [CompleteSpace E] in
/-- The Laplace transform of the exponential weight. -/
theorem integral_exp_neg_mul_Ioi_zero {μ : ℝ} (hμ : 0 < μ) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-μ * t) = μ⁻¹ := by
  have h := integral_comp_mul_left_Ioi (fun t : ℝ ↦ Real.exp (-t)) 0 hμ
  simp only [mul_zero, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  rw [neg_mul]

omit [CompleteSpace E] in
/-- The Laplace transform of the orbit is bounded by `μ⁻¹ ‖x‖`. -/
theorem norm_integral_laplaceIntegrand_le {μ : ℝ} (hμ : 0 < μ) (x : E) :
    ‖∫ t in Ioi (0 : ℝ), S.laplaceIntegrand μ x t‖ ≤ μ⁻¹ * ‖x‖ := by
  rw [← integral_exp_neg_mul_Ioi_zero hμ, ← integral_mul_const]
  exact norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi 0 hμ).mul_const ‖x‖)
    (Eventually.of_forall fun t ↦ S.norm_laplaceIntegrand_le μ x t)

end Integrand

section Resolvent

/-- **The resolvent of the semigroup** at the positive shift `μ`: the Laplace transform of the
orbits, `R_μ x = ∫₀^∞ e^{-μ t} S t x dt`, as a bounded operator. -/
def resolvent (μ : PositiveShift) : E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ ∫ t in Ioi (0 : ℝ), S.laplaceIntegrand μ x t
      map_add' := fun x y ↦ by
        rw [laplaceIntegrand_add]
        change ∫ t in Ioi (0 : ℝ),
          (S.laplaceIntegrand μ x t + S.laplaceIntegrand μ y t) = _
        exact integral_add (S.integrableOn_laplaceIntegrand μ.2 x)
          (S.integrableOn_laplaceIntegrand μ.2 y)
      map_smul' := fun c x ↦ by
        rw [laplaceIntegrand_smul, RingHom.id_apply]
        change ∫ t in Ioi (0 : ℝ), c • S.laplaceIntegrand μ x t = _
        exact integral_smul c _ }
    (μ : ℝ)⁻¹ (fun x ↦ S.norm_integral_laplaceIntegrand_le μ.2 x)

omit [CompleteSpace E] in
/-- The resolvent, unfolded as the Laplace transform of the orbit. -/
theorem resolvent_apply (μ : PositiveShift) (x : E) :
    S.resolvent μ x = ∫ t in Ioi (0 : ℝ), S.laplaceIntegrand μ x t :=
  rfl

omit [CompleteSpace E] in
/-- The Hille--Yosida bound `‖R_μ‖ ≤ μ⁻¹`. -/
theorem opNorm_resolvent_le (μ : PositiveShift) : ‖S.resolvent μ‖ ≤ (μ : ℝ)⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (inv_nonneg.mpr μ.2.le) _

/-- The semigroup commutes with its resolvent. -/
theorem operator_resolvent (μ : PositiveShift) (h : ℝ≥0) (x : E) :
    S h (S.resolvent μ x) = S.resolvent μ (S h x) := by
  rw [resolvent_apply, resolvent_apply,
    ← ContinuousLinearMap.integral_comp_comm (S h) (S.integrableOn_laplaceIntegrand μ.2 x)]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ S.laplaceIntegrand_operator μ h x t

/-- **The resolvent inverts `μ − L` on the domain**: `R_μ (μ f − L f) = f`. -/
theorem resolvent_smul_sub_generator (μ : PositiveShift) (f : S.generatorDomain) :
    S.resolvent μ ((μ : ℝ) • (f : E) - S.generator f) = f := by
  have hμ : (0 : ℝ) < μ := μ.2
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (S.laplaceIntegrand μ f)
      (S.laplaceIntegrand μ (S.generator f) t - (μ : ℝ) • S.laplaceIntegrand μ f t) t := by
    intro t ht
    have hexp : HasDerivAt (fun s : ℝ ↦ Real.exp (-(μ : ℝ) * s))
        (Real.exp (-(μ : ℝ) * t) * (-(μ : ℝ) * 1)) t :=
      ((hasDerivAt_id t).const_mul (-(μ : ℝ))).exp
    refine (hexp.smul (S.hasDerivAt_operator_toNNReal f ht)).congr_deriv ?_
    simp only [laplaceIntegrand_apply, smul_smul]
    module
  have hcont : ContinuousWithinAt (S.laplaceIntegrand μ f) (Ici 0) 0 :=
    (S.continuous_laplaceIntegrand μ f).continuousWithinAt
  have hint1 : IntegrableOn (fun t ↦ S.laplaceIntegrand μ (S.generator f) t) (Ioi 0) :=
    S.integrableOn_laplaceIntegrand hμ _
  have hint2 : IntegrableOn (fun t ↦ (μ : ℝ) • S.laplaceIntegrand μ f t) (Ioi 0) :=
    (S.integrableOn_laplaceIntegrand hμ (f : E)).smul (μ : ℝ)
  have hkey := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv (hint1.sub hint2)
    (S.tendsto_laplaceIntegrand_atTop hμ (f : E))
  rw [integral_sub hint1 hint2, integral_smul, zero_sub, laplaceIntegrand_apply, mul_zero,
    Real.exp_zero, one_smul, Real.toNNReal_zero, S.zero_apply] at hkey
  rw [map_sub, map_smul, resolvent_apply, resolvent_apply, ← neg_sub, hkey, neg_neg]

/-- On the domain, the difference quotients of `R_μ f` converge to `R_μ (L f)`. -/
theorem tendsto_differenceQuotient_resolvent_of_mem (μ : PositiveShift) (f : S.generatorDomain) :
    Tendsto (fun t : ℝ≥0 ↦ (t : ℝ)⁻¹ • (S t (S.resolvent μ f) - S.resolvent μ f)) (𝓝[>] 0)
      (𝓝 (S.resolvent μ (S.generator f))) := by
  refine (((S.resolvent μ).continuous.tendsto _).comp (S.tendsto_generator f)).congr fun t ↦ ?_
  simp only [Function.comp, StronglyContinuousContractionSemigroup.differenceQuotient_apply,
    map_smul, map_sub, operator_resolvent]

/-- The resolvent maps the domain into the domain. -/
theorem resolvent_mem_generatorDomain_of_mem (μ : PositiveShift) (f : S.generatorDomain) :
    S.resolvent μ f ∈ S.generatorDomain :=
  S.mem_generatorDomain_of_tendsto (S.tendsto_differenceQuotient_resolvent_of_mem μ f)

/-- On the domain, `L (R_μ f) = μ R_μ f − f`. -/
theorem generator_resolvent_of_mem (μ : PositiveShift) (f : S.generatorDomain) :
    S.generator ⟨S.resolvent μ f, S.resolvent_mem_generatorDomain_of_mem μ f⟩ =
      (μ : ℝ) • S.resolvent μ f - f := by
  have h1 : S.generator ⟨S.resolvent μ f, S.resolvent_mem_generatorDomain_of_mem μ f⟩ =
      S.resolvent μ (S.generator f) :=
    S.generator_eq_of_tendsto ⟨S.resolvent μ f, S.resolvent_mem_generatorDomain_of_mem μ f⟩
      (S.tendsto_differenceQuotient_resolvent_of_mem μ f)
  rw [h1]
  have h := S.resolvent_smul_sub_generator μ f
  rw [map_sub, map_smul] at h
  calc S.resolvent μ (S.generator f)
      = (μ : ℝ) • S.resolvent μ f -
          ((μ : ℝ) • S.resolvent μ f - S.resolvent μ (S.generator f)) := by abel
    _ = (μ : ℝ) • S.resolvent μ f - f := by rw [h]

/-- Approximation of `R_μ x` by resolvents of domain vectors, with convergent generators. -/
theorem exists_seq_tendsto_resolvent (μ : PositiveShift) (x : E) :
    ∃ v : ℕ → S.generatorDomain,
      Tendsto (fun n ↦ (v n : E)) atTop (𝓝 (S.resolvent μ x)) ∧
        Tendsto (fun n ↦ S.generator (v n)) atTop (𝓝 ((μ : ℝ) • S.resolvent μ x - x)) := by
  obtain ⟨u, hu_mem, hu⟩ := mem_closure_iff_seq_limit.mp (S.dense_generatorDomain x)
  have hRu : Tendsto (fun n ↦ S.resolvent μ (u n)) atTop (𝓝 (S.resolvent μ x)) :=
    ((S.resolvent μ).continuous.tendsto x).comp hu
  refine ⟨fun n ↦ ⟨S.resolvent μ (u n),
    S.resolvent_mem_generatorDomain_of_mem μ ⟨u n, hu_mem n⟩⟩, hRu, ?_⟩
  have hgen : ∀ n, S.generator ⟨S.resolvent μ (u n),
      S.resolvent_mem_generatorDomain_of_mem μ ⟨u n, hu_mem n⟩⟩ =
        (μ : ℝ) • S.resolvent μ (u n) - u n :=
    fun n ↦ S.generator_resolvent_of_mem μ ⟨u n, hu_mem n⟩
  simp_rw [hgen]
  exact (hRu.const_smul (μ : ℝ)).sub hu

/-- **The resolvent maps into the domain.** -/
theorem resolvent_mem_generatorDomain (μ : PositiveShift) (x : E) :
    S.resolvent μ x ∈ S.generatorDomain := by
  obtain ⟨v, hv, hL⟩ := S.exists_seq_tendsto_resolvent μ x
  exact S.mem_generatorDomain_of_tendsto_generator hv hL

/-- **`μ − L` inverts the resolvent**: `L (R_μ x) = μ R_μ x − x` for every `x`. -/
theorem generator_resolvent (μ : PositiveShift) (x : E) :
    S.generator ⟨S.resolvent μ x, S.resolvent_mem_generatorDomain μ x⟩ =
      (μ : ℝ) • S.resolvent μ x - x := by
  obtain ⟨v, hv, hL⟩ := S.exists_seq_tendsto_resolvent μ x
  exact S.generator_eq_of_tendsto_generator hv hL

/-- The generator of a vector exhibited as a resolvent value. -/
theorem generator_eq_of_resolvent_eq (μ : PositiveShift) {f g : E} (hf : f ∈ S.generatorDomain)
    (h : S.resolvent μ g = f) : S.generator ⟨f, hf⟩ = (μ : ℝ) • f - g := by
  subst h
  exact S.generator_resolvent μ g

/-- **The domain is the range of the resolvent**, at every positive shift. -/
theorem generatorDomain_eq_range_resolvent (μ : PositiveShift) :
    (S.generatorDomain : Set E) = Set.range (S.resolvent μ) := by
  refine Set.Subset.antisymm (fun f hf ↦ ?_) ?_
  · exact ⟨(μ : ℝ) • f - S.generator ⟨f, hf⟩, S.resolvent_smul_sub_generator μ ⟨f, hf⟩⟩
  · rintro _ ⟨y, rfl⟩
    exact S.resolvent_mem_generatorDomain μ y

/-- **The resolvent identity** `R_α − R_β = (β − α) R_α R_β`. -/
theorem resolvent_sub_resolvent (α β : PositiveShift) :
    S.resolvent α - S.resolvent β =
      ((β : ℝ) - (α : ℝ)) • (S.resolvent α).comp (S.resolvent β) := by
  ext y
  have hz : S.resolvent α ((α : ℝ) • S.resolvent β y - ((β : ℝ) • S.resolvent β y - y)) =
      S.resolvent β y := by
    have h := S.resolvent_smul_sub_generator α
      ⟨S.resolvent β y, S.resolvent_mem_generatorDomain β y⟩
    rw [S.generator_resolvent β y] at h
    exact h
  rw [map_sub, map_smul, map_sub, map_smul] at hz
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply]
  calc S.resolvent α y - S.resolvent β y
      = S.resolvent α y - ((α : ℝ) • S.resolvent α (S.resolvent β y) -
          ((β : ℝ) • S.resolvent α (S.resolvent β y) - S.resolvent α y)) := by rw [hz]
    _ = ((β : ℝ) - (α : ℝ)) • S.resolvent α (S.resolvent β y) := by module

/-- The resolvent has dense range. -/
theorem denseRange_resolvent (μ : PositiveShift) : DenseRange (S.resolvent μ) := by
  change Dense (Set.range (S.resolvent μ))
  rw [← S.generatorDomain_eq_range_resolvent μ]
  exact S.dense_generatorDomain

/-- **The resolvent family of a strongly continuous contraction semigroup is a contractive
resolvent.** -/
def toContractiveResolvent : ContractiveResolvent E where
  operator := S.resolvent
  resolvent_identity := S.resolvent_sub_resolvent
  opNorm_le_inv := S.opNorm_resolvent_le
  denseRange := S.denseRange_resolvent

/-- The operators of the contractive resolvent of `S` are its resolvents. -/
theorem toContractiveResolvent_operator (μ : PositiveShift) :
    S.toContractiveResolvent.operator μ = S.resolvent μ :=
  rfl

end Resolvent

end

end StronglyContinuousContractionSemigroup

/-! ### Identification of the generated semigroup's generator -/

namespace ContractiveResolvent

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private instance cacheNormedAlgebraRatCLMC : NormedAlgebra ℚ (E →L[ℝ] E) :=
  NormedAlgebra.restrictScalars ℚ ℝ (E →L[ℝ] E)

/-- **The fundamental identity for a bounded Yosida approximation.** The exponential semigroup
of the bounded generator `G_α` satisfies `exp (t G_α) x - x = ∫₀ᵗ exp (s G_α) (G_α x) ds` for
every vector `x`, by the fundamental theorem of calculus for the Banach-algebra exponential. -/
theorem yosidaOperator_apply_sub_eq_integral (R : ContractiveResolvent E)
    (α : PositiveShift) (t : ℝ≥0) (x : E) :
    R.yosidaOperator α t x - x =
      ∫ s in (0 : ℝ)..(t : ℝ), R.yosidaOperator α (Real.toNNReal s) (R.yosidaGenerator α x) := by
  have hderiv : ∀ s : ℝ, HasDerivAt (fun u : ℝ ↦ exp (u • R.yosidaGenerator α) x)
      (exp (s • R.yosidaGenerator α) (R.yosidaGenerator α x)) s := by
    intro s
    have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (R.yosidaGenerator α) s).clm_apply
      (hasDerivAt_const s x)
    simpa only [mul_apply_eq_comp, map_zero, add_zero] using h
  have hcont : Continuous fun s : ℝ ↦
      exp (s • R.yosidaGenerator α) (R.yosidaGenerator α x) := by fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hderiv s)
    (hcont.intervalIntegrable 0 (t : ℝ))
  have hcongr :
      (∫ s in (0 : ℝ)..(t : ℝ),
          R.yosidaOperator α (Real.toNNReal s) (R.yosidaGenerator α x)) =
        ∫ s in (0 : ℝ)..(t : ℝ), exp (s • R.yosidaGenerator α) (R.yosidaGenerator α x) := by
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [Set.uIcc_of_le t.coe_nonneg] at hs
    unfold yosidaOperator
    rw [Real.coe_toNNReal s hs.1]
  rw [hcongr, hFTC]
  unfold yosidaOperator
  rw [zero_smul, exp_zero]
  rfl

/-- **The fundamental identity on the range of a resolvent.** For the generated semigroup `S`,
`S t (R_μ y) - R_μ y = ∫₀ᵗ S s (μ R_μ y - y) ds`. Both sides are limits along the canonical
shifts of the corresponding Yosida quantities, the integrals converging by dominated
convergence. -/
theorem generatedSemigroup_apply_sub_eq_orbitIntegral (R : ContractiveResolvent E)
    (μ : PositiveShift) (y : E) (t : ℝ≥0) :
    R.generatedSemigroup t (R.operator μ y) - R.operator μ y =
      R.generatedSemigroup.orbitIntegral ((μ : ℝ) • R.operator μ y - y) t := by
  obtain ⟨C, hC⟩ :=
    (R.cauchySeq_yosidaGenerator_naturalShift_apply_operator μ y).isBounded_range.exists_norm_le
  have hnorm : ∀ (n : ℕ) (s : ℝ), ‖R.yosidaOperator (naturalShift n) (Real.toNNReal s)
      (R.yosidaGenerator (naturalShift n) (R.operator μ y))‖ ≤ C := by
    intro n s
    refine le_trans ?_ (hC _ ⟨n, rfl⟩)
    simpa only [yosidaSemigroup_apply] using
      (R.yosidaSemigroup (naturalShift n)).norm_apply_le (Real.toNNReal s)
        (R.yosidaGenerator (naturalShift n) (R.operator μ y))
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun s : ℝ ↦ R.yosidaOperator (naturalShift n) (Real.toNNReal s)
        (R.yosidaGenerator (naturalShift n) (R.operator μ y)))
      (volume.restrict (Set.uIoc (0 : ℝ) (t : ℝ))) := fun n ↦
    ((R.continuous_yosidaOperator_apply (naturalShift n) _).comp
      continuous_real_toNNReal).aestronglyMeasurable
  have hpointwise : ∀ s : ℝ, Tendsto (fun n ↦ R.yosidaOperator (naturalShift n) (Real.toNNReal s)
      (R.yosidaGenerator (naturalShift n) (R.operator μ y))) atTop
      (nhds (R.generatedSemigroup (Real.toNNReal s) ((μ : ℝ) • R.operator μ y - y))) :=
    fun s ↦ tendsto_apply_of_opNorm_le_one
      (fun n ↦ R.yosidaOperator (naturalShift n) (Real.toNNReal s))
      (R.generatedSemigroup (Real.toNNReal s))
      (fun n ↦ R.yosidaGenerator (naturalShift n) (R.operator μ y))
      ((μ : ℝ) • R.operator μ y - y)
      (fun n ↦ R.norm_yosidaOperator_le_one (naturalShift n) (Real.toNNReal s))
      (R.tendsto_yosidaOperator_naturalShift_apply (Real.toNNReal s) _)
      (R.tendsto_yosidaGenerator_naturalShift_apply_operator μ y)
  have hlimR : Tendsto (fun n ↦ ∫ s in (0 : ℝ)..(t : ℝ),
      R.yosidaOperator (naturalShift n) (Real.toNNReal s)
        (R.yosidaGenerator (naturalShift n) (R.operator μ y))) atTop
      (nhds (R.generatedSemigroup.orbitIntegral ((μ : ℝ) • R.operator μ y - y) t)) := by
    rw [StronglyContinuousContractionSemigroup.orbitIntegral_apply]
    exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C)
      (Eventually.of_forall hmeas)
      (Eventually.of_forall fun n ↦ Eventually.of_forall fun s _ ↦ hnorm n s)
      intervalIntegrable_const
      (Eventually.of_forall fun s _ ↦ hpointwise s)
  refine tendsto_nhds_unique
    ((R.tendsto_yosidaOperator_naturalShift_apply t (R.operator μ y)).sub tendsto_const_nhds)
    (hlimR.congr fun n ↦ ?_)
  exact (R.yosidaOperator_apply_sub_eq_integral (naturalShift n) t (R.operator μ y)).symm

/-- The range of every resolvent lies in the generator domain of the generated semigroup. -/
theorem operator_mem_generatorDomain (R : ContractiveResolvent E) (μ : PositiveShift) (y : E) :
    R.operator μ y ∈ R.generatedSemigroup.generatorDomain := by
  refine R.generatedSemigroup.mem_generatorDomain_of_tendsto
    (g := (μ : ℝ) • R.operator μ y - y) ?_
  refine (R.generatedSemigroup.tendsto_inv_smul_orbitIntegral
    ((μ : ℝ) • R.operator μ y - y)).congr fun t ↦ ?_
  rw [R.generatedSemigroup_apply_sub_eq_orbitIntegral μ y t]

/-- **The generator inverts the resolvent.** On the range of `R_μ`, the generator of the
generated semigroup is `L (R_μ y) = μ R_μ y - y`. -/
theorem generator_operator_apply (R : ContractiveResolvent E) (μ : PositiveShift) (y : E) :
    R.generatedSemigroup.generator ⟨R.operator μ y, R.operator_mem_generatorDomain μ y⟩ =
      (μ : ℝ) • R.operator μ y - y := by
  refine R.generatedSemigroup.generator_eq_of_tendsto _ ?_
  refine (R.generatedSemigroup.tendsto_inv_smul_orbitIntegral
    ((μ : ℝ) • R.operator μ y - y)).congr fun t ↦ ?_
  rw [R.generatedSemigroup_apply_sub_eq_orbitIntegral μ y t]

/-- The generator on a vector presented as a resolvent image: if `R_μ g = f`, then
`L f = μ f - g`. -/
theorem generator_apply_of_operator_eq (R : ContractiveResolvent E) (μ : PositiveShift) {f g : E}
    (hf : f ∈ R.generatedSemigroup.generatorDomain) (hfg : R.operator μ g = f) :
    R.generatedSemigroup.generator ⟨f, hf⟩ = (μ : ℝ) • f - g := by
  subst hfg
  exact R.generator_operator_apply μ g

/-- **The resolvent inverts `μ - L`.** For every vector `f` of the generator domain of the
generated semigroup, `R_μ (μ f - L f) = f`. -/
theorem operator_smul_sub_generator (R : ContractiveResolvent E) (μ : PositiveShift)
    (f : R.generatedSemigroup.generatorDomain) :
    R.operator μ ((μ : ℝ) • (f : E) - R.generatedSemigroup.generator f) = (f : E) := by
  refine R.generatedSemigroup.eq_of_smul_sub_generator_eq μ.property
    ⟨R.operator μ ((μ : ℝ) • (f : E) - R.generatedSemigroup.generator f),
      R.operator_mem_generatorDomain μ _⟩ f ?_
  rw [R.generator_operator_apply μ ((μ : ℝ) • (f : E) - R.generatedSemigroup.generator f)]
  abel

/-- **The generator domain is the range of any resolvent.** `R_μ` is a bijection from `E` onto
the generator domain, inverse to `μ - L`. -/
theorem generatorDomain_eq_range (R : ContractiveResolvent E) (μ : PositiveShift) :
    (R.generatedSemigroup.generatorDomain : Set E) = Set.range (R.operator μ) := by
  refine Set.Subset.antisymm (fun f hf ↦ ?_) ?_
  · exact ⟨(μ : ℝ) • f - R.generatedSemigroup.generator ⟨f, hf⟩,
      R.operator_smul_sub_generator μ ⟨f, hf⟩⟩
  · rintro _ ⟨y, rfl⟩
    exact R.operator_mem_generatorDomain μ y

end

end ContractiveResolvent

/-! ### Round-trip Hille--Yosida bijection -/

namespace StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (S : StronglyContinuousContractionSemigroup E)

/-- The semigroup generated by the resolvent of `S` has the generator domain of `S`. -/
theorem generatorDomain_generatedSemigroup_toContractiveResolvent :
    S.toContractiveResolvent.generatedSemigroup.generatorDomain = S.generatorDomain := by
  have μ₁ : PositiveShift := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  apply SetLike.coe_injective
  exact (S.toContractiveResolvent.generatorDomain_eq_range μ₁).trans
    (S.generatorDomain_eq_range_resolvent μ₁).symm

/-- **The semigroup generated by the resolvent of `S` is `S`.** -/
theorem generatedSemigroup_toContractiveResolvent :
    S.toContractiveResolvent.generatedSemigroup = S := by
  have μ₁ : PositiveShift := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  refine S.toContractiveResolvent.generatedSemigroup.ext_of_generator S
    S.generatorDomain_generatedSemigroup_toContractiveResolvent ?_
  intro f hT hS
  obtain ⟨g, rfl⟩ : f ∈ Set.range (S.resolvent μ₁) := by
    rw [← S.generatorDomain_eq_range_resolvent μ₁]
    exact hS
  rw [S.toContractiveResolvent.generator_apply_of_operator_eq μ₁ (g := g) hT rfl,
    S.generator_eq_of_resolvent_eq μ₁ hS rfl]

end StronglyContinuousContractionSemigroup

namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The resolvent of the generated semigroup is the given resolvent.** -/
theorem resolvent_generatedSemigroup (R : ContractiveResolvent E) (μ : PositiveShift) :
    R.generatedSemigroup.resolvent μ = R.operator μ := by
  ext y
  apply R.generatedSemigroup.eq_of_smul_sub_generator_eq μ.2
    ⟨R.generatedSemigroup.resolvent μ y, R.generatedSemigroup.resolvent_mem_generatorDomain μ y⟩
    ⟨R.operator μ y, R.operator_mem_generatorDomain μ y⟩
  rw [R.generatedSemigroup.generator_resolvent μ y, R.generator_operator_apply μ y]
  simp only [sub_sub_cancel]

/-- The contractive resolvent of the generated semigroup is the given contractive resolvent. -/
theorem toContractiveResolvent_generatedSemigroup (R : ContractiveResolvent E) :
    R.generatedSemigroup.toContractiveResolvent = R := by
  cases R
  simp only [StronglyContinuousContractionSemigroup.toContractiveResolvent,
    ContractiveResolvent.mk.injEq]
  funext μ
  exact resolvent_generatedSemigroup _ μ

end ContractiveResolvent

end FracLap
