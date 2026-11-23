/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Core.HilleYosidaCorrespondence
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLap.Core.AnalyticSemigroup

Abstract theory of analytic (holomorphic) semigroups (`def:analytic_semigroup`), their
immediate real-time smoothness (`prop:analytic_diff`) and range in the generator domain
(`prop:analytic_domain`), and parabolic smoothing / gradient decay `‖L (S(t) u)‖ ≤ ‖u‖ / t`
for symmetric contractive resolvents on real Hilbert spaces:

- `openSector`: the open complex sector `Σ_δ = {z ∈ ℂ | z ≠ 0 ∧ |arg z| < δ}`.
- `AnalyticSemigroup`: holomorphic semigroup on `Σ_δ` with sectorial strong continuity at `0`
  (`def:analytic_semigroup`).
- `AnalyticSemigroup.hasDerivAt_real_orbit` & `AnalyticSemigroup.contDiffOn_real_orbit`:
  immediate `C^∞` differentiability on `(0, ∞)` (`prop:analytic_diff`).
- `AnalyticSemigroup.real_orbit_mem_generatorDomain` &
  `AnalyticSemigroup.generator_real_orbit_eq`: `T(t) x ∈ D(L)` and `L (T(t) x) = d/dt T(t) x`
  for all `t > 0` and all `x` (`prop:analytic_domain`).
- `generatedSemigroup_mem_generatorDomain_of_pos`,
  `norm_generator_generatedSemigroup_of_pos_le`,
  `generatedSemigroup_hasDerivAt_of_pos`: parabolic smoothing `S(t) H ⊆ D(L)` and sharp
  `1 / t` decay for any symmetric `ContractiveResolvent` on a complete real inner product space.
-/

namespace FracLap

open Complex Filter MeasureTheory NormedSpace Set Topology
open scoped NNReal InnerProductSpace

@[expose] public section

/-! ### 1. Open sectors in `ℂ` and analytic semigroups (`def:analytic_semigroup`) -/

/-- The open complex sector `Σ_δ = {z ∈ ℂ \ {0} | |arg z| < δ}`. -/
def openSector (δ : ℝ) : Set ℂ :=
  {z : ℂ | z ≠ 0 ∧ |Complex.arg z| < δ}

/-- Characterization of the open right half-plane as `Σ_{π/2}`. -/
theorem openSector_pi_div_two : openSector (Real.pi / 2) = {z : ℂ | 0 < z.re} := by
  ext z
  simp only [openSector, mem_ofPred_eq, Complex.abs_arg_lt_pi_div_two_iff]
  constructor
  · rintro ⟨hz0, hre | rfl⟩
    · exact hre
    · exact absurd rfl hz0
  · intro hre
    refine ⟨fun h0 => by subst h0; simp at hre, Or.inl hre⟩

/-- For any `δ ≤ π / 2`, the sector `Σ_δ` lies inside the open right half-plane `{z | 0 < z.re}`. -/
theorem openSector_subset_re_pos {δ : ℝ} (hδ : δ ≤ Real.pi / 2) :
    openSector δ ⊆ {z : ℂ | 0 < z.re} := by
  intro z ⟨hz0, harg⟩
  have hlt : |Complex.arg z| < Real.pi / 2 := lt_of_lt_of_le harg hδ
  rw [← openSector_pi_div_two]
  exact ⟨hz0, hlt⟩

/-- For any `δ ≤ π / 2`, the sector `Σ_δ` is an open subset of `ℂ`. -/
theorem isOpen_openSector {δ : ℝ} (hδ : δ ≤ Real.pi / 2) : IsOpen (openSector δ) := by
  have hsub : openSector δ ⊆ Complex.slitPlane := fun z hz => by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (openSector_subset_re_pos hδ hz)
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hz_slit : z ∈ Complex.slitPlane := hsub hz
  have hne : z ≠ 0 := hz.1
  have harg_lt : |Complex.arg z| < δ := hz.2
  have harg_cont : ContinuousAt (fun w : ℂ => |Complex.arg w|) z :=
    continuous_abs.continuousAt.comp (Complex.continuousAt_arg hz_slit)
  have h1 : ∀ᶠ w in 𝓝 z, w ≠ 0 := isOpen_ne.mem_nhds hne
  have h2 : ∀ᶠ w in 𝓝 z, |Complex.arg w| < δ := harg_cont.eventually (Iio_mem_nhds harg_lt)
  filter_upwards [h1, h2] with w hw1 hw2
  exact ⟨hw1, hw2⟩

/-- Every strictly positive real time `t > 0` lies in every sector `Σ_δ` with `δ > 0`. -/
theorem ofReal_mem_openSector {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) :
    (t : ℂ) ∈ openSector δ := by
  refine ⟨Complex.ofReal_ne_zero.mpr ht.ne', ?_⟩
  rw [Complex.arg_ofReal_of_nonneg ht.le, abs_zero]
  exact hδ

/-- **Analytic (Holomorphic) Semigroup (`def:analytic_semigroup`)** on a complex Banach space `E`:
a family `(T(z))_{z ∈ Σ_δ ∪ {0}}` of bounded complex linear operators satisfying the semigroup
law on `Σ_δ`, holomorphicity of every orbit `z ↦ T(z) x` on `Σ_δ`, and strong convergence
`T(z) x → x` as `z → 0` inside every smaller closed subsector `Σ_{δ'}` (`0 < δ' < δ`). -/
structure AnalyticSemigroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  /-- Half-opening angle `δ ∈ (0, π / 2]` of the analyticity sector `Σ_δ`. -/
  delta : ℝ
  /-- Strict positivity `0 < δ`. -/
  delta_pos : 0 < delta
  /-- Sector angle at most `π / 2`. -/
  delta_le : delta ≤ Real.pi / 2
  /-- The complex-linear operator family `z ↦ T(z) : E →L[ℂ] E`. -/
  operator : ℂ → E →L[ℂ] E
  /-- Identity at `z = 0`. -/
  operator_zero : operator 0 = ContinuousLinearMap.id ℂ E
  /-- Holomorphic composition law on `Σ_δ`: `T(z₁ + z₂) = T(z₁) ∘ T(z₂)`. -/
  operator_add :
    ∀ {z₁ z₂ : ℂ}, z₁ ∈ openSector delta → z₂ ∈ openSector delta →
      operator (z₁ + z₂) = (operator z₁).comp (operator z₂)
  /-- Complex differentiability (holomorphicity) of every orbit on `Σ_δ`. -/
  differentiableOn : ∀ x : E, DifferentiableOn ℂ (fun z : ℂ => operator z x) (openSector delta)
  /-- Strong sectorial continuity at `0`: `T(z) x → x` as `z → 0` in `Σ_{δ'}` (`0 < δ' < δ`). -/
  tendsto_zero :
    ∀ {δ' : ℝ}, 0 < δ' → δ' < delta → ∀ x : E,
      Tendsto (fun z : ℂ => operator z x) (𝓝[openSector δ'] 0) (𝓝 x)

/-! ### 2. Immediate differentiability and range in `D(L)` -/

namespace AnalyticSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- **Immediate Real-Time Differentiability (`prop:analytic_diff`)**:
for every analytic semigroup `S` and every vector `x : E`, the real-time orbit
`t ↦ S.operator (t : ℂ) x` is differentiable on `(0, ∞)` with derivative
`deriv (fun z : ℂ => S.operator z x) (t : ℂ)`. -/
theorem hasDerivAt_real_orbit (S : AnalyticSemigroup E) (x : E) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => S.operator (s : ℂ) x)
      (deriv (fun z : ℂ => S.operator z x) (t : ℂ)) t := by
  have hmem : (t : ℂ) ∈ openSector S.delta := ofReal_mem_openSector S.delta_pos ht
  have hdiff_at : DifferentiableAt ℂ (fun z : ℂ => S.operator z x) (t : ℂ) :=
    (S.differentiableOn x).differentiableAt ((isOpen_openSector S.delta_le).mem_nhds hmem)
  have hofReal : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hcomp := HasDerivAt.scomp t hdiff_at.hasDerivAt hofReal
  simpa [Function.comp_def] using hcomp

/-- **Immediate Real-Time `C^∞` Smoothness (`prop:analytic_diff`)**:
for every analytic semigroup `S` and every `x : E`, the real-time orbit `t ↦ S.operator (t : ℂ) x`
is smooth (`ContDiffOn ℝ ⊤`) on `(0, ∞)`. -/
theorem contDiffOn_real_orbit (S : AnalyticSemigroup E) (x : E) :
    ContDiffOn ℝ ⊤ (fun s : ℝ => S.operator (s : ℂ) x) (Ioi (0 : ℝ)) := by
  have hC : ContDiffOn ℂ ⊤ (fun z : ℂ => S.operator z x) (openSector S.delta) :=
    (S.differentiableOn x).contDiffOn (isOpen_openSector S.delta_le)
  have hR : ContDiffOn ℝ ⊤ (fun z : ℂ => S.operator z x) (openSector S.delta) :=
    hC.restrict_scalars ℝ
  have hmaps : MapsTo (fun s : ℝ => (s : ℂ)) (Ioi (0 : ℝ)) (openSector S.delta) :=
    fun s hs => ofReal_mem_openSector S.delta_pos hs
  have hofReal : ContDiffOn ℝ ⊤ (fun s : ℝ => (s : ℂ)) (Ioi (0 : ℝ)) :=
    (Complex.ofRealCLM.contDiff).contDiffOn
  exact hR.comp hofReal hmaps

/-- If `S : AnalyticSemigroup E` restricts to uniformly contractive operators at real times
`t : ℝ≥0`, its real-time restriction forms a `StronglyContinuousContractionSemigroup E`. -/
noncomputable def toRealSemigroup (S : AnalyticSemigroup E)
    (hcontract : ∀ t : ℝ≥0, ‖S.operator (t : ℂ)‖ ≤ 1)
    (hadd_real : ∀ s t : ℝ≥0,
      S.operator ((s + t : ℝ≥0) : ℂ) = (S.operator (s : ℂ)).comp (S.operator (t : ℂ))) :
    StronglyContinuousContractionSemigroup E :=
  StronglyContinuousContractionSemigroup.ofTendstoZero
    (fun t => (S.operator (t : ℂ)).restrictScalars ℝ)
    (by ext x; simp [S.operator_zero])
    (fun s t => by ext x; simpa using congrArg (fun L : E →L[ℂ] E => L x) (hadd_real s t))
    (fun t => hcontract t)
    (fun x => by
      have hδ' : 0 < S.delta / 2 := half_pos S.delta_pos
      have hδ'_lt : S.delta / 2 < S.delta := half_lt_self S.delta_pos
      have htend := S.tendsto_zero hδ' hδ'_lt x
      rw [Metric.tendsto_nhdsWithin_nhds] at htend
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨r, hrpos, hr⟩ := htend ε hε
      have hev : ∀ᶠ t : ℝ≥0 in 𝓝 0, (t : ℝ) < r :=
        NNReal.continuous_coe.continuousAt.tendsto.eventually (Iio_mem_nhds hrpos)
      refine hev.mono fun t (htr : (t : ℝ) < r) => ?_
      by_cases ht0 : t = 0
      · subst ht0
        simp only [ContinuousLinearMap.coe_restrictScalars', NNReal.coe_zero,
          Complex.ofReal_zero, S.operator_zero, ContinuousLinearMap.id_apply, dist_self, hε]
      · have htpos : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht0)
        have hmem : ((t : ℝ) : ℂ) ∈ openSector (S.delta / 2) :=
          ofReal_mem_openSector hδ' htpos
        have hdist : dist ((t : ℝ) : ℂ) 0 < r := by
          simpa [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos] using htr
        exact hr hmem hdist)

omit [CompleteSpace E] in
/-- **Immediate Range in the Generator Domain (`prop:analytic_domain`)**:
if `T : StronglyContinuousContractionSemigroup E` agrees on `ℝ≥0` with the real-time
restriction of an `AnalyticSemigroup E` `S`, then `T t x ∈ T.generatorDomain` for every
vector `x : E` and every strictly positive time `t > 0`. -/
theorem real_orbit_mem_generatorDomain (S : AnalyticSemigroup E)
    (T : StronglyContinuousContractionSemigroup E)
    (hT : ∀ s : ℝ≥0, ∀ y : E, T s y = S.operator (s : ℂ) y)
    (x : E) {t : ℝ≥0} (ht : 0 < (t : ℝ)) :
    T t x ∈ T.generatorDomain := by
  have hderiv := S.hasDerivAt_real_orbit x ht
  have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
  have hslope_right :
      Tendsto (fun h : ℝ => h⁻¹ • (S.operator (((t : ℝ) + h : ℝ) : ℂ) x - S.operator (t : ℂ) x))
        (𝓝[>] (0 : ℝ)) (𝓝 (deriv (fun z : ℂ => S.operator z x) (t : ℂ))) := by
    have hcomp :
        Tendsto (fun h : ℝ => ((t : ℝ) + h)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (t : ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun h : ℝ => (t : ℝ) + h) (𝓝 0) (𝓝 ((t : ℝ) + 0)) :=
          tendsto_const_nhds.add tendsto_id
        rw [add_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        exact ne_of_gt (by linarith [mem_Ioi.mp hh])
    have h1 := hslope.comp hcomp
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [Function.comp_apply, slope_def_module, add_sub_cancel_left]
  refine ⟨deriv (fun z : ℂ => S.operator z x) (t : ℂ), ?_⟩
  have hcomp_nn :
      Tendsto (fun s : ℝ≥0 => (s : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (NNReal.continuous_coe.continuousAt.mono_left nhdsWithin_le_nhds)
      (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact NNReal.coe_pos.mpr hs)
  have h2 := hslope_right.comp hcomp_nn
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s _
  change (s : ℝ)⁻¹ • (S.operator (((t : ℝ) + (s : ℝ) : ℝ) : ℂ) x - S.operator (t : ℂ) x) =
    (s : ℝ)⁻¹ • (T s (T t x) - T t x)
  rw [← ContinuousLinearMap.comp_apply, ← T.operator_add s t, add_comm s t,
    hT (t + s) x, hT t x]
  simp only [NNReal.coe_add]

omit [CompleteSpace E] in
/-- **Generator Action on Analytic Orbits (`prop:analytic_domain`)**:
for any `T` extending `S` on `ℝ≥0` and any `t > 0`, `T.generator (T t x)` equals the
complex-time orbit derivative at `(t : ℂ)`. -/
theorem generator_real_orbit_eq (S : AnalyticSemigroup E)
    (T : StronglyContinuousContractionSemigroup E)
    (hT : ∀ s : ℝ≥0, ∀ y : E, T s y = S.operator (s : ℂ) y)
    (x : E) {t : ℝ≥0} (ht : 0 < (t : ℝ)) :
    T.generator ⟨T t x, S.real_orbit_mem_generatorDomain T hT x ht⟩ =
      deriv (fun z : ℂ => S.operator z x) (t : ℂ) := by
  have hderiv := S.hasDerivAt_real_orbit x ht
  have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
  have hslope_right :
      Tendsto (fun h : ℝ => h⁻¹ • (S.operator (((t : ℝ) + h : ℝ) : ℂ) x - S.operator (t : ℂ) x))
        (𝓝[>] (0 : ℝ)) (𝓝 (deriv (fun z : ℂ => S.operator z x) (t : ℂ))) := by
    have hcomp :
        Tendsto (fun h : ℝ => ((t : ℝ) + h)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (t : ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun h : ℝ => (t : ℝ) + h) (𝓝 0) (𝓝 ((t : ℝ) + 0)) :=
          tendsto_const_nhds.add tendsto_id
        rw [add_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        exact ne_of_gt (by linarith [mem_Ioi.mp hh])
    have h1 := hslope.comp hcomp
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [Function.comp_apply, slope_def_module, add_sub_cancel_left]
  have hcomp_nn :
      Tendsto (fun s : ℝ≥0 => (s : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (NNReal.continuous_coe.continuousAt.mono_left nhdsWithin_le_nhds)
      (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact NNReal.coe_pos.mpr hs)
  have hlim :
      Tendsto (fun s : ℝ≥0 => (s : ℝ)⁻¹ • (T s (T t x) - T t x)) (𝓝[>] (0 : ℝ≥0))
        (𝓝 (deriv (fun z : ℂ => S.operator z x) (t : ℂ))) := by
    refine (hslope_right.comp hcomp_nn).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s _
    change (s : ℝ)⁻¹ • (S.operator (((t : ℝ) + (s : ℝ) : ℝ) : ℂ) x - S.operator (t : ℂ) x) =
      (s : ℝ)⁻¹ • (T s (T t x) - T t x)
    rw [← ContinuousLinearMap.comp_apply, ← T.operator_add s t, add_comm s t,
      hT (t + s) x, hT t x]
    simp only [NNReal.coe_add]
  exact T.generator_eq_of_tendsto ⟨T t x, S.real_orbit_mem_generatorDomain T hT x ht⟩ hlim

end AnalyticSemigroup

/-! ### 3. Parabolic smoothing and `1 / t` decay for symmetric contractive resolvents -/

namespace ContractiveResolvent

section SymmetricSmoothing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private noncomputable instance cacheRatAlgHilbertCLM : NormedAlgebra ℚ (H →L[ℝ] H) :=
  NormedAlgebra.restrictScalars ℚ ℝ (H →L[ℝ] H)

omit [CompleteSpace H] in
/-- Symmetry of the Yosida generator `G_μ = μ (μ R_μ - I)` inherited from resolvent symmetry. -/
theorem yosidaGenerator_symm (R : ContractiveResolvent H)
    (hSymm : ∀ μ : PositiveShift, ∀ x y : H, ⟪R.operator μ x, y⟫_ℝ = ⟪x, R.operator μ y⟫_ℝ)
    (μ : PositiveShift) (x y : H) :
    ⟪R.yosidaGenerator μ x, y⟫_ℝ = ⟪x, R.yosidaGenerator μ y⟫_ℝ := by
  change ⟪(μ : ℝ) • (R.scaledOperator μ x - x), y⟫_ℝ =
    ⟪x, (μ : ℝ) • (R.scaledOperator μ y - y)⟫_ℝ
  have hs : ∀ z : H, R.scaledOperator μ z = (μ : ℝ) • R.operator μ z := fun z => rfl
  simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right, hs]
  rw [hSymm μ x y]

omit [CompleteSpace H] in
/-- Nonpositivity `⟪G_μ x, x⟫ ≤ 0` of every Yosida generator of a `ContractiveResolvent`. -/
theorem inner_yosidaGenerator_nonpos (R : ContractiveResolvent H) (μ : PositiveShift) (x : H) :
    ⟪R.yosidaGenerator μ x, x⟫_ℝ ≤ 0 := by
  change ⟪(μ : ℝ) • (R.scaledOperator μ x - x), x⟫_ℝ ≤ 0
  rw [inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq]
  have hle : ⟪R.scaledOperator μ x, x⟫_ℝ ≤ ‖x‖ ^ 2 := by
    calc ⟪R.scaledOperator μ x, x⟫_ℝ
        ≤ ‖R.scaledOperator μ x‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ (‖R.scaledOperator μ‖ * ‖x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right ((R.scaledOperator μ).le_opNorm x) (norm_nonneg x)
      _ ≤ (1 * ‖x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (R.opNorm_scaledOperator_le_one μ) (norm_nonneg x))
          (norm_nonneg x)
      _ = ‖x‖ ^ 2 := by ring
  exact mul_nonpos_of_nonneg_of_nonpos μ.2.le (sub_nonpos.mpr hle)

omit [CompleteSpace H] in
/-- Time derivative of `s ↦ exp (s • G) x` commutes with `G`:
`exp (s • G) (G x) = G (exp (s • G) x)`. -/
theorem exp_smul_comp_eq_comp_exp_smul (G : H →L[ℝ] H) (s : ℝ) :
    (exp (s • G)).comp G = G.comp (exp (s • G)) := by
  have hc : Commute (s • G) G := (Commute.refl G).smul_left s
  exact (hc.exp_left).eq

/-- **Sharp `1 / t` Smoothing Bound for Yosida Semigroups** of a symmetric `ContractiveResolvent`:
for every `u : H`, shift `μ > 0`, and time `t > 0`,
`‖G_μ exp(t G_μ) u‖ ≤ ‖u‖ / t`. -/
theorem norm_yosidaGenerator_exp_le_div (R : ContractiveResolvent H)
    (hSymm : ∀ μ : PositiveShift, ∀ x y : H, ⟪R.operator μ x, y⟫_ℝ = ⟪x, R.operator μ y⟫_ℝ)
    (μ : PositiveShift) (u : H) {t : ℝ} (ht : 0 < t) :
    ‖R.yosidaGenerator μ (exp (t • R.yosidaGenerator μ) u)‖ ≤ ‖u‖ / t := by
  let G : H →L[ℝ] H := R.yosidaGenerator μ
  let E : ℝ → H := fun s => exp (s • G) u
  have hE_deriv : ∀ s : ℝ, HasDerivAt E (G (E s)) s := fun s => by
    have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) G s).clm_apply (hasDerivAt_const s u)
    have h2 : exp (s • G) (G u) = G (E s) := by
      have hc := congrArg (fun L : H →L[ℝ] H => L u) (exp_smul_comp_eq_comp_exp_smul G s)
      simpa only [ContinuousLinearMap.comp_apply, E] using hc
    simpa only [mul_apply_eq_comp, map_zero, add_zero, h2, E] using h1
  have hGE_deriv : ∀ s : ℝ, HasDerivAt (fun r => G (E r)) (G (G (E s))) s := fun s =>
    G.hasFDerivAt.comp_hasDerivAt s (hE_deriv s)
  -- Energy 0: `φ₀ s = ‖E s‖²`
  let φ₀ : ℝ → ℝ := fun s => ⟪E s, E s⟫_ℝ
  have hφ₀_deriv : ∀ s : ℝ, HasDerivAt φ₀ (2 * ⟪G (E s), E s⟫_ℝ) s := fun s => by
    have h := (hE_deriv s).inner ℝ (hE_deriv s)
    rw [real_inner_comm (G (E s)) (E s), ← two_mul] at h
    exact h
  -- Energy 1: `φ₁ s = -⟪G (E s), E s⟫` (nonnegative, nonincreasing)
  let φ₁ : ℝ → ℝ := fun s => -⟪G (E s), E s⟫_ℝ
  have hφ₁_nonneg : ∀ s : ℝ, 0 ≤ φ₁ s := fun s =>
    neg_nonneg.mpr (inner_yosidaGenerator_nonpos R μ (E s))
  have hφ₁_deriv : ∀ s : ℝ, HasDerivAt φ₁ (-2 * ‖G (E s)‖ ^ 2) s := fun s => by
    have h := ((hGE_deriv s).inner ℝ (hE_deriv s)).fun_neg
    have hsym : ⟪G (E s), G (E s)⟫_ℝ + ⟪G (G (E s)), E s⟫_ℝ = 2 * ‖G (E s)‖ ^ 2 := by
      rw [yosidaGenerator_symm R hSymm μ (G (E s)) (E s), real_inner_self_eq_norm_sq, two_mul]
    rw [hsym] at h
    simpa only [neg_mul] using h
  have hφ₁_anti : ∀ {a b : ℝ}, a ≤ b → φ₁ b ≤ φ₁ a := fun {a b} hab => by
    have hint : IntervalIntegrable (fun s => -2 * ‖G (E s)‖ ^ 2) volume a b :=
      (Continuous.mul continuous_const
        ((G.continuous.comp (by fun_prop : Continuous E)).norm.pow 2)).intervalIntegrable a b
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hφ₁_deriv s) hint
    have hpos : 0 ≤ ∫ s in a..b, 2 * ‖G (E s)‖ ^ 2 :=
      intervalIntegral.integral_nonneg hab fun s _ => by positivity
    have hneg_eq : ∫ s in a..b, -(2 * ‖G (E s)‖ ^ 2) = -(∫ s in a..b, 2 * ‖G (E s)‖ ^ 2) :=
      intervalIntegral.integral_neg
    have hsub : φ₁ b - φ₁ a = -(∫ s in a..b, 2 * ‖G (E s)‖ ^ 2) := by
      calc φ₁ b - φ₁ a = ∫ s in a..b, -2 * ‖G (E s)‖ ^ 2 := hftc.symm
        _ = ∫ s in a..b, -(2 * ‖G (E s)‖ ^ 2) := by simp [neg_mul]
        _ = -(∫ s in a..b, 2 * ‖G (E s)‖ ^ 2) := hneg_eq
    linarith
  -- Step 1: `φ₁ (t / 2) ≤ ‖u‖² / t`
  have hstep1 : φ₁ (t / 2) ≤ ‖u‖ ^ 2 / t := by
    have ht2 : 0 < t / 2 := half_pos ht
    have hint0 : IntervalIntegrable (fun s => 2 * ⟪G (E s), E s⟫_ℝ) volume 0 (t / 2) :=
      (Continuous.mul continuous_const
        (Continuous.inner (G.continuous.comp (by fun_prop : Continuous E))
          (by fun_prop : Continuous E))).intervalIntegrable 0 (t / 2)
    have hftc0 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hφ₀_deriv s) hint0
    have hE0 : E 0 = u := by simp [E]
    have hφ₀0 : φ₀ 0 = ‖u‖ ^ 2 := by simp [φ₀, hE0]
    have hφ₀_nn : 0 ≤ φ₀ (t / 2) := real_inner_self_nonneg
    have hlower : (t / 2) * (2 * φ₁ (t / 2)) ≤ ∫ s in (0 : ℝ)..(t / 2), 2 * φ₁ s := by
      have hi1 : IntervalIntegrable (fun _ : ℝ => 2 * φ₁ (t / 2)) volume 0 (t / 2) :=
        intervalIntegrable_const
      have hi2 : IntervalIntegrable (fun s : ℝ => 2 * φ₁ s) volume 0 (t / 2) := by
        refine (Continuous.mul continuous_const ?_).intervalIntegrable 0 (t / 2)
        exact (Continuous.inner (G.continuous.comp (by fun_prop : Continuous E))
          (by fun_prop : Continuous E)).neg
      have hmono := intervalIntegral.integral_mono_on ht2.le hi1 hi2 fun s hs =>
        mul_le_mul_of_nonneg_left (hφ₁_anti hs.2) (by norm_num)
      simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hmono
    have hneg_eq : ∫ s in (0 : ℝ)..(t / 2), 2 * φ₁ s = φ₀ 0 - φ₀ (t / 2) := by
      have : (fun s : ℝ => 2 * φ₁ s) = fun s => -(2 * ⟪G (E s), E s⟫_ℝ) := by
        ext s; simp [φ₁]
      rw [this, intervalIntegral.integral_neg, hftc0]
      ring
    have hbound : t * φ₁ (t / 2) ≤ ‖u‖ ^ 2 := by nlinarith
    exact (le_div_iff₀ ht).mpr (by linarith)
  -- Energy 2: `φ₂ s = ‖G (E s)‖²` (nonincreasing)
  let φ₂ : ℝ → ℝ := fun s => ‖G (E s)‖ ^ 2
  have hφ₂_deriv : ∀ s : ℝ, HasDerivAt φ₂ (2 * ⟪G (G (E s)), G (E s)⟫_ℝ) s := fun s => by
    have h := (hGE_deriv s).inner ℝ (hGE_deriv s)
    rw [real_inner_comm (G (G (E s))) (G (E s)), ← two_mul] at h
    have h2 : φ₂ = fun r => ⟪G (E r), G (E r)⟫_ℝ := by
      ext r; simp [φ₂]
    rw [h2]
    exact h
  have hφ₂_anti : ∀ {a b : ℝ}, a ≤ b → φ₂ b ≤ φ₂ a := fun {a b} hab => by
    have hint : IntervalIntegrable (fun s => 2 * ⟪G (G (E s)), G (E s)⟫_ℝ) volume a b :=
      (Continuous.mul continuous_const
        (Continuous.inner (G.continuous.comp (G.continuous.comp (by fun_prop : Continuous E)))
          (G.continuous.comp (by fun_prop : Continuous E)))).intervalIntegrable a b
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hφ₂_deriv s) hint
    have hpos : 0 ≤ ∫ s in a..b, -(2 * ⟪G (G (E s)), G (E s)⟫_ℝ) :=
      intervalIntegral.integral_nonneg hab fun s _ =>
        neg_nonneg.mpr
          (mul_nonpos_of_nonneg_of_nonpos (by norm_num)
            (inner_yosidaGenerator_nonpos R μ (G (E s))))
    have hneg_eq : ∫ s in a..b, -(2 * ⟪G (G (E s)), G (E s)⟫_ℝ) = φ₂ a - φ₂ b := by
      rw [intervalIntegral.integral_neg, hftc]
      ring
    linarith
  -- Step 2: `(t / 2) * 2 * φ₂ t ≤ ‖u‖² / t`
  have hstep2 : φ₂ t ≤ (‖u‖ / t) ^ 2 := by
    have ht2_le : t / 2 ≤ t := by linarith
    have hint1 : IntervalIntegrable (fun s => -2 * φ₂ s) volume (t / 2) t :=
      (Continuous.mul continuous_const
        ((G.continuous.comp (by fun_prop : Continuous E)).norm.pow 2)).intervalIntegrable (t / 2) t
    have hftc1 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hφ₁_deriv s) hint1
    have hlower : (t - t / 2) * (2 * φ₂ t) ≤ ∫ s in (t / 2)..t, 2 * φ₂ s := by
      have hi1 : IntervalIntegrable (fun _ : ℝ => 2 * φ₂ t) volume (t / 2) t :=
        intervalIntegrable_const
      have hi2 : IntervalIntegrable (fun s : ℝ => 2 * φ₂ s) volume (t / 2) t := by
        refine (Continuous.mul continuous_const ?_).intervalIntegrable (t / 2) t
        exact (G.continuous.comp (by fun_prop : Continuous E)).norm.pow 2
      have hmono := intervalIntegral.integral_mono_on ht2_le hi1 hi2 fun s hs =>
        mul_le_mul_of_nonneg_left (hφ₂_anti hs.2) (by norm_num)
      simpa only [intervalIntegral.integral_const, smul_eq_mul] using hmono
    have hneg_eq : ∫ s in (t / 2)..t, 2 * φ₂ s = φ₁ (t / 2) - φ₁ t := by
      have : (fun s : ℝ => 2 * φ₂ s) = fun s => -(-2 * φ₂ s) := by ext s; ring
      rw [this, intervalIntegral.integral_neg, hftc1]
      ring
    have hle1 : t * φ₂ t ≤ φ₁ (t / 2) := by
      have h0 := hφ₁_nonneg t
      linarith
    have hle2 : t * φ₂ t ≤ ‖u‖ ^ 2 / t := hle1.trans hstep1
    have hle3 : φ₂ t ≤ (‖u‖ ^ 2 / t) / t := (le_div_iff₀ ht).mpr (by linarith)
    calc φ₂ t ≤ (‖u‖ ^ 2 / t) / t := hle3
      _ = (‖u‖ / t) ^ 2 := by ring
  have hsq : ‖G (E t)‖ ^ 2 ≤ (‖u‖ / t) ^ 2 := hstep2
  have hrt := Real.sqrt_le_sqrt hsq
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (div_nonneg (norm_nonneg _) ht.le)]
    using hrt

/-- `1 / t` decay for vectors already in the generator domain of a symmetric
`ContractiveResolvent`: `‖L (S(t) v)‖ ≤ ‖v‖ / t`. -/
theorem norm_generator_generatedSemigroup_le_div (R : ContractiveResolvent H)
    (hSymm : ∀ μ : PositiveShift, ∀ x y : H, ⟪R.operator μ x, y⟫_ℝ = ⟪x, R.operator μ y⟫_ℝ)
    {v : H} (hv : v ∈ R.generatedSemigroup.generatorDomain) {t : ℝ≥0} (ht : 0 < (t : ℝ)) :
    ‖R.generatedSemigroup.generator
      ⟨R.generatedSemigroup t v,
        R.generatedSemigroup.operator_mem_generatorDomain ⟨v, hv⟩ t⟩‖ ≤ ‖v‖ / (t : ℝ) := by
  let one : PositiveShift := ⟨1, by norm_num⟩
  have hrange : v ∈ Set.range (R.operator one) := by
    rw [← R.generatorDomain_eq_range one]
    exact hv
  obtain ⟨y, hy⟩ := hrange
  have hgen_v : R.generatedSemigroup.generator ⟨v, hv⟩ = (one : ℝ) • v - y := by
    have hv_eq : v = R.operator one y := hy.symm
    have heq := R.generator_operator_apply one y
    have hsub : (⟨v, hv⟩ : R.generatedSemigroup.generatorDomain) =
        ⟨R.operator one y, R.operator_mem_generatorDomain one y⟩ := Subtype.ext hv_eq
    rw [hsub, heq, hv_eq]
  have htend_G :
      Tendsto (fun n : ℕ => R.yosidaGenerator (naturalShift n) v) atTop
        (𝓝 (R.generatedSemigroup.generator ⟨v, hv⟩)) := by
    rw [hgen_v, ← hy]
    exact R.tendsto_yosidaGenerator_naturalShift_apply_operator one y
  have htend_lhs :
      Tendsto (fun n : ℕ => R.yosidaGenerator (naturalShift n)
        (R.yosidaOperator (naturalShift n) t v)) atTop
        (𝓝 (R.generatedSemigroup.generator
          ⟨R.generatedSemigroup t v,
            R.generatedSemigroup.operator_mem_generatorDomain ⟨v, hv⟩ t⟩)) := by
    have hcomm : ∀ n : ℕ,
        R.yosidaGenerator (naturalShift n) (R.yosidaOperator (naturalShift n) t v) =
          R.yosidaOperator (naturalShift n) t (R.yosidaGenerator (naturalShift n) v) := fun n => by
      have hc := congrArg (fun L : H →L[ℝ] H => L v)
        (exp_smul_comp_eq_comp_exp_smul (R.yosidaGenerator (naturalShift n)) (t : ℝ)).symm
      exact hc
    simp_rw [hcomm]
    rw [R.generatedSemigroup.generator_operator ⟨v, hv⟩ t]
    exact tendsto_apply_of_opNorm_le_one
      (fun n => R.yosidaOperator (naturalShift n) t)
      (R.generatedSemigroup t)
      (fun n => R.yosidaGenerator (naturalShift n) v)
      (R.generatedSemigroup.generator ⟨v, hv⟩)
      (fun n => R.norm_yosidaOperator_le_one (naturalShift n) t)
      (R.tendsto_yosidaOperator_naturalShift_apply t _)
      htend_G
  exact le_of_tendsto htend_lhs.norm (Eventually.of_forall fun n =>
    R.norm_yosidaGenerator_exp_le_div hSymm (naturalShift n) v ht)

/-- **Immediate Parabolic Smoothing (`prop:analytic_domain`, Real Hilbert Case)**:
for any symmetric `ContractiveResolvent R` on a complete real inner product space `H`,
every rough initial datum `u : H` immediately enters `D(L)` at every strictly positive time
`t > 0`: `R.generatedSemigroup t u ∈ R.generatedSemigroup.generatorDomain`. -/
theorem generatedSemigroup_mem_generatorDomain_of_pos (R : ContractiveResolvent H)
    (hSymm : ∀ μ : PositiveShift, ∀ x y : H, ⟪R.operator μ x, y⟫_ℝ = ⟪x, R.operator μ y⟫_ℝ)
    (u : H) {t : ℝ≥0} (ht : 0 < (t : ℝ)) :
    R.generatedSemigroup t u ∈ R.generatedSemigroup.generatorDomain := by
  have hdense := R.generatedSemigroup.dense_generatorDomain
  have hex : ∀ k : ℕ, ∃ v : R.generatedSemigroup.generatorDomain,
      ‖(v : H) - u‖ < ((k : ℝ) + 1)⁻¹ := fun k => by
    have hkpos : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := inv_pos.mpr (by positivity)
    obtain ⟨v, hv_mem, hv_dist⟩ := Metric.mem_closure_iff.mp
      (hdense.closure_eq ▸ Set.mem_univ u) _ hkpos
    exact ⟨⟨v, hv_mem⟩, by
      change ‖v - u‖ < _
      rw [← dist_eq_norm, dist_comm]
      exact hv_dist⟩
  choose v hv_dist using hex
  have hv_tendsto : Tendsto (fun k : ℕ => (v k : H)) atTop (𝓝 u) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine Filter.eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
    have hlt : ((k : ℝ) + 1)⁻¹ ≤ ((N : ℝ) + 1)⁻¹ := by gcongr
    have hN' : ((N : ℝ) + 1)⁻¹ < ε := by simpa only [one_div] using hN
    rw [dist_eq_norm]
    exact lt_of_lt_of_le (hv_dist k) (hlt.trans hN'.le)
  let w : ℕ → H := fun k => R.generatedSemigroup t (v k : H)
  let gw : ℕ → H := fun k => R.generatedSemigroup.generator
    ⟨w k, R.generatedSemigroup.operator_mem_generatorDomain (v k) t⟩
  have hw_tendsto : Tendsto w atTop (𝓝 (R.generatedSemigroup t u)) :=
    (R.generatedSemigroup t).continuous.continuousAt.tendsto.comp hv_tendsto
  have hgw_cauchy : CauchySeq gw := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hv_tendsto.cauchySeq (ε * (t : ℝ)) (mul_pos hε ht)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hdiff_mem : (v m : H) - (v n : H) ∈ R.generatedSemigroup.generatorDomain :=
      R.generatedSemigroup.generatorDomain.sub_mem (v m).2 (v n).2
    have hgw_diff :
        gw m - gw n = R.generatedSemigroup.generator
          ⟨R.generatedSemigroup t ((v m : H) - (v n : H)),
            R.generatedSemigroup.operator_mem_generatorDomain ⟨_, hdiff_mem⟩ t⟩ := by
      have hdom_eq :
          (⟨w m, R.generatedSemigroup.operator_mem_generatorDomain (v m) t⟩ :
              R.generatedSemigroup.generatorDomain) -
            ⟨w n, R.generatedSemigroup.operator_mem_generatorDomain (v n) t⟩ =
            ⟨R.generatedSemigroup t ((v m : H) - (v n : H)),
              R.generatedSemigroup.operator_mem_generatorDomain ⟨_, hdiff_mem⟩ t⟩ := by
        ext1; exact (R.generatedSemigroup t).map_sub (v m : H) (v n : H) |>.symm
      rw [← (R.generatedSemigroup.generator).map_sub, hdom_eq]
    rw [dist_eq_norm, hgw_diff]
    calc ‖R.generatedSemigroup.generator
          ⟨R.generatedSemigroup t ((v m : H) - (v n : H)),
            R.generatedSemigroup.operator_mem_generatorDomain ⟨_, hdiff_mem⟩ t⟩‖
        ≤ ‖(v m : H) - (v n : H)‖ / (t : ℝ) :=
          R.norm_generator_generatedSemigroup_le_div hSymm hdiff_mem ht
      _ < (ε * (t : ℝ)) / (t : ℝ) :=
          div_lt_div_of_pos_right (by simpa only [dist_eq_norm] using hN m hm n hn) ht
      _ = ε := mul_div_cancel_right₀ ε ht.ne'
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hgw_cauchy
  exact R.generatedSemigroup.mem_generatorDomain_of_tendsto_generator
    (u := fun k => ⟨w k, R.generatedSemigroup.operator_mem_generatorDomain (v k) t⟩)
    hw_tendsto hy

/-- **`1 / t` Operator Decay on All Rough Data**:
for every `u : H` and `t > 0`, `‖L (S(t) u)‖ ≤ ‖u‖ / t`. -/
theorem norm_generator_generatedSemigroup_of_pos_le (R : ContractiveResolvent H)
    (hSymm : ∀ μ : PositiveShift, ∀ x y : H, ⟪R.operator μ x, y⟫_ℝ = ⟪x, R.operator μ y⟫_ℝ)
    (u : H) {t : ℝ≥0} (ht : 0 < (t : ℝ)) :
    ‖R.generatedSemigroup.generator
      ⟨R.generatedSemigroup t u,
        R.generatedSemigroup_mem_generatorDomain_of_pos hSymm u ht⟩‖ ≤ ‖u‖ / (t : ℝ) := by
  have hdense := R.generatedSemigroup.dense_generatorDomain
  have hex : ∀ k : ℕ, ∃ v : R.generatedSemigroup.generatorDomain,
      ‖(v : H) - u‖ < ((k : ℝ) + 1)⁻¹ := fun k => by
    have hkpos : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := inv_pos.mpr (by positivity)
    obtain ⟨v, hv_mem, hv_dist⟩ := Metric.mem_closure_iff.mp
      (hdense.closure_eq ▸ Set.mem_univ u) _ hkpos
    exact ⟨⟨v, hv_mem⟩, by
      change ‖v - u‖ < _
      rw [← dist_eq_norm, dist_comm]
      exact hv_dist⟩
  choose v hv_dist using hex
  have hv_tendsto : Tendsto (fun k : ℕ => (v k : H)) atTop (𝓝 u) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine Filter.eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
    have hlt : ((k : ℝ) + 1)⁻¹ ≤ ((N : ℝ) + 1)⁻¹ := by gcongr
    have hN' : ((N : ℝ) + 1)⁻¹ < ε := by simpa only [one_div] using hN
    rw [dist_eq_norm]
    exact lt_of_lt_of_le (hv_dist k) (hlt.trans hN'.le)
  have hdom : ∀ k : ℕ, ‖R.generatedSemigroup.generator
      ⟨R.generatedSemigroup t (v k : H),
        R.generatedSemigroup.operator_mem_generatorDomain (v k) t⟩‖ ≤ ‖(v k : H)‖ / (t : ℝ) :=
    fun k => R.norm_generator_generatedSemigroup_le_div hSymm (v k).2 ht
  have hw_tendsto : Tendsto (fun k => R.generatedSemigroup t (v k : H)) atTop
      (𝓝 (R.generatedSemigroup t u)) :=
    (R.generatedSemigroup t).continuous.continuousAt.tendsto.comp hv_tendsto
  have hgw_cauchy : CauchySeq (fun k => R.generatedSemigroup.generator
      ⟨R.generatedSemigroup t (v k : H),
        R.generatedSemigroup.operator_mem_generatorDomain (v k) t⟩) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hv_tendsto.cauchySeq (ε * (t : ℝ)) (mul_pos hε ht)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hdiff_mem : (v m : H) - (v n : H) ∈ R.generatedSemigroup.generatorDomain :=
      R.generatedSemigroup.generatorDomain.sub_mem (v m).2 (v n).2
    have hgw_diff :
        R.generatedSemigroup.generator
            ⟨R.generatedSemigroup t (v m : H),
              R.generatedSemigroup.operator_mem_generatorDomain (v m) t⟩ -
          R.generatedSemigroup.generator
            ⟨R.generatedSemigroup t (v n : H),
              R.generatedSemigroup.operator_mem_generatorDomain (v n) t⟩ =
          R.generatedSemigroup.generator
            ⟨R.generatedSemigroup t ((v m : H) - (v n : H)),
              R.generatedSemigroup.operator_mem_generatorDomain ⟨_, hdiff_mem⟩ t⟩ := by
      have hdom_eq :
          (⟨R.generatedSemigroup t (v m : H),
              R.generatedSemigroup.operator_mem_generatorDomain (v m) t⟩ :
                R.generatedSemigroup.generatorDomain) -
            ⟨R.generatedSemigroup t (v n : H),
              R.generatedSemigroup.operator_mem_generatorDomain (v n) t⟩ =
            ⟨R.generatedSemigroup t ((v m : H) - (v n : H)),
              R.generatedSemigroup.operator_mem_generatorDomain ⟨_, hdiff_mem⟩ t⟩ := by
        ext1; exact (R.generatedSemigroup t).map_sub (v m : H) (v n : H) |>.symm
      rw [← (R.generatedSemigroup.generator).map_sub, hdom_eq]
    rw [dist_eq_norm, hgw_diff]
    calc ‖R.generatedSemigroup.generator
          ⟨R.generatedSemigroup t ((v m : H) - (v n : H)),
            R.generatedSemigroup.operator_mem_generatorDomain ⟨_, hdiff_mem⟩ t⟩‖
        ≤ ‖(v m : H) - (v n : H)‖ / (t : ℝ) :=
          R.norm_generator_generatedSemigroup_le_div hSymm hdiff_mem ht
      _ < (ε * (t : ℝ)) / (t : ℝ) :=
          div_lt_div_of_pos_right (by simpa only [dist_eq_norm] using hN m hm n hn) ht
      _ = ε := mul_div_cancel_right₀ ε ht.ne'
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hgw_cauchy
  have hgen_eq := R.generatedSemigroup.generator_eq_of_tendsto_generator
    (u := fun k => ⟨R.generatedSemigroup t (v k : H),
      R.generatedSemigroup.operator_mem_generatorDomain (v k) t⟩)
    hw_tendsto hy
  have hnorm_lim : Tendsto (fun k : ℕ => ‖(v k : H)‖ / (t : ℝ)) atTop (𝓝 (‖u‖ / (t : ℝ))) :=
    (hv_tendsto.norm).div_const (t : ℝ)
  have hbound_y : ‖y‖ ≤ ‖u‖ / (t : ℝ) := le_of_tendsto_of_tendsto hy.norm hnorm_lim
    (Eventually.of_forall hdom)
  rw [hgen_eq]
  exact hbound_y

/-- **Immediate Time Differentiability on `(0, ∞)` for All Rough Data**:
for any symmetric `ContractiveResolvent R`, any `u : H`, and any `t > 0`,
`s ↦ R.generatedSemigroup (Real.toNNReal s) u` is differentiable at `t` with derivative
`L (R.generatedSemigroup (Real.toNNReal t) u)`. -/
theorem generatedSemigroup_hasDerivAt_of_pos (R : ContractiveResolvent H)
    (hSymm : ∀ μ : PositiveShift, ∀ x y : H, ⟪R.operator μ x, y⟫_ℝ = ⟪x, R.operator μ y⟫_ℝ)
    (u : H) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => R.generatedSemigroup (Real.toNNReal s) u)
      (R.generatedSemigroup.generator
        ⟨R.generatedSemigroup (Real.toNNReal t) u,
          R.generatedSemigroup_mem_generatorDomain_of_pos hSymm u
            (by simpa [Real.coe_toNNReal t ht.le] using ht)⟩) t := by
  let t2 : ℝ≥0 := Real.toNNReal (t / 2)
  have ht2_pos : 0 < (t2 : ℝ) := by
    rw [Real.coe_toNNReal (t / 2) (half_pos ht).le]
    exact half_pos ht
  have hv : R.generatedSemigroup t2 u ∈ R.generatedSemigroup.generatorDomain :=
    R.generatedSemigroup_mem_generatorDomain_of_pos hSymm u ht2_pos
  have hdiff := R.generatedSemigroup.hasDerivAt_operator_toNNReal ⟨_, hv⟩
    (t := t / 2) (half_pos ht)
  have hshift : HasDerivAt (fun s : ℝ => s - t / 2) 1 t := by
    simpa using (hasDerivAt_id t).sub_const (t / 2)
  have hshift_val : (t - t / 2 : ℝ) = (t2 : ℝ) := by
    rw [Real.coe_toNNReal (t / 2) (half_pos ht).le]
    ring
  have hdiff' :
      HasDerivAt (fun s : ℝ => R.generatedSemigroup (Real.toNNReal s) (R.generatedSemigroup t2 u))
        (R.generatedSemigroup t2 (R.generatedSemigroup.generator ⟨R.generatedSemigroup t2 u, hv⟩))
        (t - t / 2) := by
    rw [show t - t / 2 = t / 2 by ring]
    exact hdiff
  have hev : (fun s : ℝ => R.generatedSemigroup (Real.toNNReal s) u) =ᶠ[𝓝 t]
      ((fun s : ℝ => R.generatedSemigroup (Real.toNNReal s) (R.generatedSemigroup t2 u)) ∘
        fun s : ℝ => s - t / 2) := by
    filter_upwards [eventually_gt_nhds (half_lt_self ht)] with s (hs : t / 2 < s)
    dsimp only [Function.comp_apply]
    rw [← ContinuousLinearMap.comp_apply, ← R.generatedSemigroup.operator_add]
    congr 2
    ext1
    simp only [NNReal.coe_add, t2, Real.coe_toNNReal _ (sub_pos.mpr hs).le,
      Real.coe_toNNReal _ (half_pos ht).le, Real.coe_toNNReal _ ((half_pos ht).trans hs).le]
    ring
  have h_rhs :
      R.generatedSemigroup t2
          (R.generatedSemigroup.generator ⟨R.generatedSemigroup t2 u, hv⟩) =
        R.generatedSemigroup.generator
          ⟨R.generatedSemigroup (Real.toNNReal t) u,
            R.generatedSemigroup_mem_generatorDomain_of_pos hSymm u
              (by simpa [Real.coe_toNNReal t ht.le] using ht)⟩ := by
    have hgen_op := R.generatedSemigroup.generator_operator ⟨R.generatedSemigroup t2 u, hv⟩ t2
    have hval : R.generatedSemigroup t2 (R.generatedSemigroup t2 u) =
        R.generatedSemigroup (Real.toNNReal t) u := by
      rw [← ContinuousLinearMap.comp_apply, ← R.generatedSemigroup.operator_add]
      congr 2
      ext1
      simp only [NNReal.coe_add, t2, Real.coe_toNNReal _ (half_pos ht).le,
        Real.coe_toNNReal _ ht.le]
      ring
    rw [← hgen_op]
    exact congrArg R.generatedSemigroup.generator (Subtype.ext hval)
  have hfinal := (hdiff'.scomp t hshift).congr_of_eventuallyEq hev
  rw [one_smul, h_rhs] at hfinal
  exact hfinal

end SymmetricSmoothing

end ContractiveResolvent

end

end FracLap
