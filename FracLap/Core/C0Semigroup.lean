/-
Copyright (c) 2026 Scott Armstrong, Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Bartosz Wróblewski
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# FracLap.Core.C0Semigroup

Strongly continuous contraction semigroups (`StronglyContinuousContractionSemigroup E`)
on real normed spaces, adapted and verified on Mathlib `v4.36.0` from Scott Armstrong's
`scottnarmstrong/MarkovProcess` (`MarkovProcess.Semigroup`):
- `StronglyContinuousContractionSemigroup E`: a family of bounded linear contractions
  `S : ℝ≥0 → E →L[ℝ] E` with `S 0 = id`, `S (s + t) = (S s).comp (S t)`, `‖S t‖ ≤ 1`,
  and continuous orbits `t ↦ S t x`.
- `continuous_orbit_of_tendsto_zero` and `StronglyContinuousContractionSemigroup.ofTendstoZero`:
  upgrading strong continuity at `t = 0` to continuity of all orbits on `ℝ≥0` and joint
  continuity `continuous_operator_apply`.
- `generatorDomain` and `generator`: the infinitesimal generator `L : D(L) →ₗ[ℝ] E` defined as
  the right derivative `lim_{t → 0⁺} t⁻¹ • (S t f - f)`.
- `operator_mem_generatorDomain` and `generator_operator`: invariance of `D(L)` under `S t`
  and commutation `L (S t f) = S t (L f)`.
- `hasDerivWithinAt_Ioi`, `hasDerivWithinAt_Ici`, and `hasDerivAt_operator_toNNReal`:
  one-sided and two-sided time differentiability of orbits `(d/dt) S(t) f = S(t) L f`.
- `operator_sub_eq_integral`: the fundamental integral identity
  `S t f - f = ∫ s in (0 : ℝ)..t, S s (L f)`.
- `orbitIntegral`, `orbitIntegral_mem_generatorDomain`, `generator_orbitIntegral`, and
  `dense_generatorDomain`: density of the generator domain `D(L)` in any complete normed space `E`.
- `mem_generatorDomain_of_tendsto_generator` and `generator_eq_of_tendsto_generator`:
  closedness of the generator graph `(f, L f)`.
- `ext_of_generator`: **uniqueness of the semigroup from its generator** (two strongly continuous
  contraction semigroups with the same generator domain and generator are equal).
-/

namespace FracLap

open Filter Set Topology
open scoped NNReal

@[expose] public section

/-- A strongly continuous contraction semigroup (`C₀`-contraction semigroup) on a real normed
space `E`, parametrized by nonnegative time `t : ℝ≥0`. -/
structure StronglyContinuousContractionSemigroup (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The continuous linear time-evolution operator `S(t) : E →L[ℝ] E`. -/
  operator : ℝ≥0 → E →L[ℝ] E
  /-- Identity at time zero: `S(0) = I`. -/
  operator_zero : operator 0 = ContinuousLinearMap.id ℝ E
  /-- Semigroup composition law: `S(s + t) = S(s) ∘L S(t)`. -/
  operator_add : ∀ s t : ℝ≥0, operator (s + t) = (operator s).comp (operator t)
  /-- Operator-norm contractivity: `‖S(t)‖ ≤ 1`. -/
  opNorm_le_one : ∀ t : ℝ≥0, ‖operator t‖ ≤ 1
  /-- Strong continuity of every orbit `t ↦ S(t) x`. -/
  continuous_orbit : ∀ x : E, Continuous (fun t : ℝ≥0 => operator t x)

/-- Pointwise operator limit along a convergent family of vectors for uniformly contractive
continuous linear maps. -/
theorem tendsto_apply_of_opNorm_le_one {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {l : Filter ι}
    (T : ι → E →L[ℝ] E) (Tlim : E →L[ℝ] E) (v : ι → E) (w : E)
    (hT : ∀ i : ι, ‖T i‖ ≤ 1)
    (hTlim : Tendsto (fun i : ι => T i w) l (𝓝 (Tlim w)))
    (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun i : ι => T i (v i)) l (𝓝 (Tlim w)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  filter_upwards [Metric.tendsto_nhds.mp hv (ε / 2) hε2,
    Metric.tendsto_nhds.mp hTlim (ε / 2) hε2] with i hvi hTi
  have hcontract : dist (T i (v i)) (T i w) ≤ dist (v i) w := by
    calc
      dist (T i (v i)) (T i w) ≤ ‖T i‖ * dist (v i) w := (T i).dist_le_opNorm _ _
      _ ≤ 1 * dist (v i) w := mul_le_mul_of_nonneg_right (hT i) dist_nonneg
      _ = dist (v i) w := one_mul _
  calc
    dist (T i (v i)) (Tlim w) ≤ dist (T i (v i)) (T i w) + dist (T i w) (Tlim w) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hcontract.trans_lt hvi) hTi
    _ = ε := add_halves ε

/-- A contractive semigroup whose orbits converge strongly to the identity at `t = 0` has
continuous orbits on all of `ℝ≥0`. -/
theorem continuous_orbit_of_tendsto_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hadd : ∀ s t : ℝ≥0, T (s + t) = (T s).comp (T t))
    (hcontract : ∀ t : ℝ≥0, ‖T t‖ ≤ 1)
    (htend : ∀ x : E, Tendsto (fun t : ℝ≥0 => T t x) (𝓝 0) (𝓝 x))
    (x : E) :
    Continuous (fun t : ℝ≥0 => T t x) := by
  rw [Metric.continuous_iff]
  intro t ε hε
  obtain ⟨δ, hδ, hnear⟩ := (Metric.tendsto_nhds_nhds.mp (htend x)) ε hε
  refine ⟨δ, hδ, fun s hst => ?_⟩
  rcases le_total t s with hts | hst'
  · have hgap : dist (s - t) 0 < δ := by
      simpa only [NNReal.dist_eq, NNReal.coe_sub hts, NNReal.coe_zero, sub_zero,
        Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hts))] using hst
    have hsmall := hnear hgap
    have hs : T s x = T t (T (s - t) x) := by
      rw [← ContinuousLinearMap.comp_apply, ← hadd, add_comm, tsub_add_cancel_of_le hts]
    rw [hs]
    calc
      dist (T t (T (s - t) x)) (T t x) ≤ dist (T (s - t) x) x := by
        calc
          _ ≤ ‖T t‖ * dist (T (s - t) x) x := (T t).dist_le_opNorm _ _
          _ ≤ 1 * dist (T (s - t) x) x :=
            mul_le_mul_of_nonneg_right (hcontract t) dist_nonneg
          _ = _ := one_mul _
      _ < ε := hsmall
  · have hgap : dist (t - s) 0 < δ := by
      rw [dist_comm] at hst
      simpa only [NNReal.dist_eq, NNReal.coe_sub hst', NNReal.coe_zero, sub_zero,
        Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst'))] using hst
    have hsmall := hnear hgap
    have ht : T t x = T s (T (t - s) x) := by
      rw [← ContinuousLinearMap.comp_apply, ← hadd, add_comm, tsub_add_cancel_of_le hst']
    rw [ht, dist_comm]
    calc
      dist (T s (T (t - s) x)) (T s x) ≤ dist (T (t - s) x) x := by
        calc
          _ ≤ ‖T s‖ * dist (T (t - s) x) x := (T s).dist_le_opNorm _ _
          _ ≤ 1 * dist (T (t - s) x) x :=
            mul_le_mul_of_nonneg_right (hcontract s) dist_nonneg
          _ = _ := one_mul _
      _ < ε := hsmall

namespace StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

instance : CoeFun (StronglyContinuousContractionSemigroup E)
    (fun _ => ℝ≥0 → E →L[ℝ] E) where
  coe S := S.operator

@[ext]
theorem ext {S T : StronglyContinuousContractionSemigroup E}
    (h : ∀ t : ℝ≥0, S t = T t) : S = T := by
  cases S with
  | mk S _ _ _ _ =>
    cases T with
    | mk T _ _ _ _ =>
      have : S = T := funext h
      cases this
      rfl

variable (S : StronglyContinuousContractionSemigroup E)

/-- Construct a `StronglyContinuousContractionSemigroup` by checking strong continuity only at
`t = 0`. -/
def ofTendstoZero
    (T : ℝ≥0 → E →L[ℝ] E)
    (hzero : T 0 = ContinuousLinearMap.id ℝ E)
    (hadd : ∀ s t : ℝ≥0, T (s + t) = (T s).comp (T t))
    (hcontract : ∀ t : ℝ≥0, ‖T t‖ ≤ 1)
    (htend : ∀ x : E, Tendsto (fun t : ℝ≥0 => T t x) (𝓝 0) (𝓝 x)) :
    StronglyContinuousContractionSemigroup E where
  operator := T
  operator_zero := hzero
  operator_add := hadd
  opNorm_le_one := hcontract
  continuous_orbit := continuous_orbit_of_tendsto_zero T hadd hcontract htend

@[simp]
theorem zero : S 0 = ContinuousLinearMap.id ℝ E :=
  S.operator_zero

theorem zero_apply (x : E) : S 0 x = x := by
  rw [S.zero]
  rfl

@[simp]
theorem add (s t : ℝ≥0) : S (s + t) = (S s).comp (S t) :=
  S.operator_add s t

theorem add_apply (s t : ℝ≥0) (x : E) : S (s + t) x = S s (S t x) := by
  rw [S.add]
  rfl

theorem norm_operator_le_one (t : ℝ≥0) : ‖S t‖ ≤ 1 :=
  S.opNorm_le_one t

theorem norm_apply_le (t : ℝ≥0) (x : E) : ‖S t x‖ ≤ ‖x‖ := by
  calc
    ‖S t x‖ ≤ ‖S t‖ * ‖x‖ := (S t).le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (S.norm_operator_le_one t) (norm_nonneg x)
    _ = ‖x‖ := one_mul _

theorem dist_apply_le (t : ℝ≥0) (x y : E) : dist (S t x) (S t y) ≤ dist x y := by
  calc
    dist (S t x) (S t y) ≤ ‖S t‖ * dist x y := (S t).dist_le_opNorm x y
    _ ≤ 1 * dist x y :=
      mul_le_mul_of_nonneg_right (S.norm_operator_le_one t) dist_nonneg
    _ = dist x y := one_mul _

theorem continuous (x : E) : Continuous (fun t : ℝ≥0 => S t x) :=
  S.continuous_orbit x

theorem continuousAt (t : ℝ≥0) (x : E) : ContinuousAt (fun s : ℝ≥0 => S s x) t :=
  (S.continuous x).continuousAt

theorem tendsto (t : ℝ≥0) (x : E) :
    Tendsto (fun s : ℝ≥0 => S s x) (𝓝 t) (𝓝 (S t x)) :=
  S.continuousAt t x

theorem commute (s t : ℝ≥0) : (S s).comp (S t) = (S t).comp (S s) := by
  rw [← S.add, ← S.add, add_comm]

theorem commute_apply (s t : ℝ≥0) (x : E) : S s (S t x) = S t (S s x) := by
  change ((S s).comp (S t)) x = ((S t).comp (S s)) x
  rw [S.commute]

/-- Joint continuity of the evolution `(t, x) ↦ S(t) x`. -/
theorem continuous_operator_apply
    {X : Type*} [TopologicalSpace X] {u : X → ℝ≥0} {v : X → E}
    (hu : Continuous u) (hv : Continuous v) :
    Continuous fun x : X => S (u x) (v x) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact tendsto_apply_of_opNorm_le_one (fun z => S (u z)) (S (u x)) v (v x)
    (fun z => S.norm_operator_le_one (u z)) ((S.continuous (v x)).comp hu).continuousAt
    hv.continuousAt

/-! ### Difference Quotients and Infinitesimal Generator -/

/-- The difference quotient `t⁻¹ • (S t f - f)` of the orbit of `f` at `t = 0`. -/
noncomputable def differenceQuotient (f : E) (t : ℝ≥0) : E := (t : ℝ)⁻¹ • (S t f - f)

/-- The difference quotient, unfolded. -/
theorem differenceQuotient_apply (f : E) (t : ℝ≥0) :
    S.differenceQuotient f t = (t : ℝ)⁻¹ • (S t f - f) := rfl

/-- Difference quotients are additive in the vector. -/
theorem differenceQuotient_add (f g : E) (t : ℝ≥0) :
    S.differenceQuotient (f + g) t = S.differenceQuotient f t + S.differenceQuotient g t := by
  rw [differenceQuotient, differenceQuotient, differenceQuotient, map_add, add_sub_add_comm,
    smul_add]

/-- Difference quotients are homogeneous in the vector. -/
theorem differenceQuotient_smul (c : ℝ) (f : E) (t : ℝ≥0) :
    S.differenceQuotient (c • f) t = c • S.differenceQuotient f t := by
  rw [differenceQuotient, differenceQuotient, map_smul, ← smul_sub, smul_comm]

/-- The difference quotient of the zero vector vanishes. -/
theorem differenceQuotient_zero (t : ℝ≥0) : S.differenceQuotient 0 t = 0 := by
  rw [differenceQuotient, map_zero, sub_zero, smul_zero]

/-- `S(s)` commutes with difference quotients. -/
theorem differenceQuotient_operator (f : E) (s t : ℝ≥0) :
    S.differenceQuotient (S s f) t = S s (S.differenceQuotient f t) := by
  rw [differenceQuotient, differenceQuotient, map_smul, map_sub, S.commute_apply]

/-- The generator domain `D(L)` of `S`: the linear subspace of vectors `f : E` whose difference
quotients `t⁻¹ • (S t f - f)` converge as `t → 0⁺`. -/
def generatorDomain : Submodule ℝ E where
  carrier := {f | ∃ g : E, Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 g)}
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, (ha.add hb).congr fun t => ?_⟩
    exact (S.differenceQuotient_add f g t).symm
  zero_mem' := by
    refine ⟨0, ?_⟩
    have hzero : S.differenceQuotient 0 = fun _ => 0 := funext S.differenceQuotient_zero
    rw [hzero]
    exact tendsto_const_nhds
  smul_mem' := by
    rintro c f ⟨a, ha⟩
    refine ⟨c • a, (ha.const_smul c).congr fun t => ?_⟩
    exact (S.differenceQuotient_smul c f t).symm

/-- Membership in `D(L)` unfolded. -/
theorem mem_generatorDomain_iff {f : E} :
    f ∈ S.generatorDomain ↔ ∃ g : E, Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 g) :=
  Iff.rfl

/-- A vector whose difference quotients converge belongs to `D(L)`. -/
theorem mem_generatorDomain_of_tendsto {f g : E}
    (h : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (S t f - f)) (𝓝[>] 0) (𝓝 g)) :
    f ∈ S.generatorDomain :=
  ⟨g, h⟩

/-- The limit of the difference quotients for `f ∈ D(L)`. -/
noncomputable def generatorFun (f : S.generatorDomain) : E :=
  limUnder (𝓝[>] (0 : ℝ≥0)) (S.differenceQuotient f)

private theorem tendsto_generatorFun (f : S.generatorDomain) :
    Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 (S.generatorFun f)) :=
  tendsto_nhds_limUnder (S.mem_generatorDomain_iff.mp f.2)

private theorem generatorFun_eq_of_tendsto (f : S.generatorDomain) {g : E}
    (h : Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 g)) : S.generatorFun f = g :=
  tendsto_nhds_unique (S.tendsto_generatorFun f) h

/-- The infinitesimal generator `L : D(L) →ₗ[ℝ] E` of `S`. -/
noncomputable def generator : S.generatorDomain →ₗ[ℝ] E where
  toFun := S.generatorFun
  map_add' f g := by
    apply S.generatorFun_eq_of_tendsto
    refine ((S.tendsto_generatorFun f).add (S.tendsto_generatorFun g)).congr fun t => ?_
    rw [Submodule.coe_add, differenceQuotient_add]
  map_smul' c f := by
    apply S.generatorFun_eq_of_tendsto
    refine ((S.tendsto_generatorFun f).const_smul c).congr fun t => ?_
    rw [Submodule.coe_smul, differenceQuotient_smul]

/-- Defining limit of the generator: the difference quotients of `f ∈ D(L)` converge to `L f`. -/
theorem tendsto_generator (f : S.generatorDomain) :
    Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 (S.generator f)) :=
  S.tendsto_generatorFun f

/-- Uniqueness of the generator limit. -/
theorem generator_eq_of_tendsto (f : S.generatorDomain) {g : E}
    (h : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (S t f - f)) (𝓝[>] 0) (𝓝 g)) :
    S.generator f = g :=
  S.generatorFun_eq_of_tendsto f h

/-- The generator domain `D(L)` is invariant under `S(t)` for every `t ≥ 0`. -/
theorem operator_mem_generatorDomain (f : S.generatorDomain) (t : ℝ≥0) :
    S t f ∈ S.generatorDomain := by
  refine ⟨S t (S.generator f), ?_⟩
  refine (((S t).continuous.tendsto _).comp (S.tendsto_generator f)).congr fun h => ?_
  exact (S.differenceQuotient_operator f t h).symm

/-- `S(t)` commutes with its generator `L` on `D(L)`: `L (S(t) f) = S(t) (L f)`. -/
theorem generator_operator (f : S.generatorDomain) (t : ℝ≥0) :
    S.generator ⟨S t f, S.operator_mem_generatorDomain f t⟩ = S t (S.generator f) := by
  apply S.generator_eq_of_tendsto
  refine (((S t).continuous.tendsto _).comp (S.tendsto_generator f)).congr fun h => ?_
  exact (S.differenceQuotient_operator f t h).symm

/-- Right difference quotients at time `t` converge to `S(t) (L f)`. -/
theorem tendsto_differenceQuotient_add (f : S.generatorDomain) (t : ℝ≥0) :
    Tendsto (fun h : ℝ≥0 => (h : ℝ)⁻¹ • (S (t + h) f - S t f)) (𝓝[>] 0)
      (𝓝 (S t (S.generator f))) := by
  refine (((S t).continuous.tendsto _).comp (S.tendsto_generator f)).congr fun h => ?_
  change S t ((h : ℝ)⁻¹ • (S h f - f)) = (h : ℝ)⁻¹ • (S (t + h) f - S t f)
  rw [map_smul, map_sub, S.add_apply]

/-! ### Real-Time Differentiability, Fundamental Integral Identity, Density & Uniqueness -/

/-- Right neighborhood convergence `y ↦ Real.toNNReal (y - t)` as `y → t⁺`. -/
theorem tendsto_toNNReal_sub (t : ℝ≥0) :
    Tendsto (fun y : ℝ => Real.toNNReal (y - t)) (𝓝[>] (t : ℝ)) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Tendsto (fun y : ℝ => Real.toNNReal (y - t)) (𝓝 (t : ℝ))
        (𝓝 (Real.toNNReal ((t : ℝ) - t))) :=
      (continuous_real_toNNReal.tendsto _).comp ((continuous_id.sub continuous_const).tendsto _)
    rw [sub_self, Real.toNNReal_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact Set.mem_Ioi.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr hy))

/-- Left neighborhood convergence `y ↦ Real.toNNReal (t - y)` as `y → t⁻`. -/
theorem tendsto_toNNReal_const_sub (t : ℝ) :
    Tendsto (fun y : ℝ => Real.toNNReal (t - y)) (𝓝[<] t) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Tendsto (fun y : ℝ => Real.toNNReal (t - y)) (𝓝 t)
        (𝓝 (Real.toNNReal (t - t))) :=
      (continuous_real_toNNReal.tendsto _).comp ((continuous_const.sub continuous_id).tendsto _)
    rw [sub_self, Real.toNNReal_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact Set.mem_Ioi.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr hy))

/-- Continuity of the real-time orbit `s ↦ S (Real.toNNReal s) f`. -/
theorem continuous_operator_toNNReal (f : E) :
    Continuous fun s : ℝ => S (Real.toNNReal s) f :=
  (S.continuous f).comp continuous_real_toNNReal

/-- Right derivative of the orbit `s ↦ S(s) f` on `(t, ∞)` for `f ∈ D(L)`. -/
theorem hasDerivWithinAt_Ioi (f : S.generatorDomain) (t : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => S (Real.toNNReal s) f) (S t (S.generator f))
      (Set.Ioi (t : ℝ)) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hdiff : Set.Ioi (t : ℝ) \ {(t : ℝ)} = Set.Ioi (t : ℝ) := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_singleton_iff, and_iff_left_iff_imp]
    exact fun hy => ne_of_gt hy
  rw [hdiff]
  refine ((S.tendsto_differenceQuotient_add f t).comp (tendsto_toNNReal_sub t)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyt : (t : ℝ) < y := hy
  have hy0 : (0 : ℝ) ≤ y := le_trans t.coe_nonneg hyt.le
  have hcoe : ((Real.toNNReal (y - t) : ℝ≥0) : ℝ) = y - t :=
    Real.coe_toNNReal _ (sub_nonneg.mpr hyt.le)
  have htoNN : Real.toNNReal y = t + Real.toNNReal (y - t) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, hcoe, Real.coe_toNNReal y hy0]
    ring
  change ((Real.toNNReal (y - t) : ℝ≥0) : ℝ)⁻¹ •
      (S (t + Real.toNNReal (y - t)) f - S t f) =
    slope (fun s : ℝ => S (Real.toNNReal s) f) (t : ℝ) y
  rw [slope_def_module, hcoe, Real.toNNReal_coe, htoNN]

/-- Right derivative of the orbit `s ↦ S(s) f` on `[t, ∞)` for `f ∈ D(L)`. -/
theorem hasDerivWithinAt_Ici (f : S.generatorDomain) (t : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => S (Real.toNNReal s) f) (S t (S.generator f))
      (Set.Ici (t : ℝ)) t :=
  (S.hasDerivWithinAt_Ioi f t).Ici_of_Ioi

/-- Left derivative of the orbit `s ↦ S(s) f` on `(-∞, t]` for `f ∈ D(L)` and `t > 0`. -/
theorem hasDerivWithinAt_Iic (f : S.generatorDomain) {t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt (fun s : ℝ => S (Real.toNNReal s) f)
      (S (Real.toNNReal t) (S.generator f)) (Set.Iic t) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hdiff : Set.Iic t \ {t} = Set.Iio t := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_Iic, Set.mem_singleton_iff, Set.mem_Iio]
    exact ⟨fun hy => lt_of_le_of_ne hy.1 hy.2, fun hy => ⟨hy.le, hy.ne⟩⟩
  rw [hdiff]
  have horbit : Tendsto (fun y : ℝ => S (Real.toNNReal y) (S.generator f)) (𝓝[<] t)
      (𝓝 (S (Real.toNNReal t) (S.generator f))) :=
    ((S.continuous_operator_toNNReal (S.generator f)).tendsto t).mono_left nhdsWithin_le_nhds
  have hquot : Tendsto (fun y : ℝ => S.differenceQuotient f (Real.toNNReal (t - y))) (𝓝[<] t)
      (𝓝 (S.generator f)) :=
    (S.tendsto_generator f).comp (tendsto_toNNReal_const_sub t)
  have hmain := tendsto_apply_of_opNorm_le_one (fun y : ℝ => S (Real.toNNReal y))
    (S (Real.toNNReal t)) (fun y : ℝ => S.differenceQuotient f (Real.toNNReal (t - y)))
    (S.generator f) (fun _ => S.norm_operator_le_one _) horbit hquot
  refine hmain.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT ht] with y hy
  have hcoe : ((Real.toNNReal (t - y) : ℝ≥0) : ℝ) = t - y :=
    Real.coe_toNNReal _ (sub_nonneg.mpr hy.2.le)
  have hsum : Real.toNNReal y + Real.toNNReal (t - y) = Real.toNNReal t := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, hcoe, Real.coe_toNNReal y hy.1.le,
      Real.coe_toNNReal t (hy.1.trans hy.2).le]
    ring
  have hinv : (y - t)⁻¹ = -(t - y)⁻¹ := by rw [neg_inv, neg_sub]
  change S (Real.toNNReal y) (S.differenceQuotient f (Real.toNNReal (t - y)))
    = slope (fun s : ℝ => S (Real.toNNReal s) f) t y
  rw [S.differenceQuotient_apply, map_smul, map_sub, ← S.add_apply, hsum, hcoe,
    slope_def_module, hinv, neg_smul, ← smul_neg, neg_sub]

/-- **Two-sided time differentiability of semigroup orbits**:
For `f ∈ D(L)` and every `t > 0`, the orbit `s ↦ S(s) f` is differentiable at `t` with
derivative `(d/dt) S(t) f = S(t) (L f)`. -/
theorem hasDerivAt_operator_toNNReal (f : S.generatorDomain) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => S (Real.toNNReal s) f) (S (Real.toNNReal t) (S.generator f)) t := by
  have hright := S.hasDerivWithinAt_Ici f (Real.toNNReal t)
  rw [Real.coe_toNNReal t ht.le] at hright
  have hunion := (S.hasDerivWithinAt_Iic f ht).union hright
  rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at hunion

/-- The orbit integral `∫₀ᵘ S(s) f ds`. -/
noncomputable def orbitIntegral (f : E) (u : ℝ) : E :=
  ∫ s in (0 : ℝ)..u, S (Real.toNNReal s) f

/-- The orbit integral unfolded. -/
theorem orbitIntegral_apply (f : E) (u : ℝ) :
    S.orbitIntegral f u = ∫ s in (0 : ℝ)..u, S (Real.toNNReal s) f := rfl

/-- The orbit integral over `[0, 0]` vanishes. -/
theorem orbitIntegral_zero (f : E) : S.orbitIntegral f 0 = 0 :=
  intervalIntegral.integral_same

/-- The orbit integral is additive in the vector difference. -/
theorem orbitIntegral_sub (f g : E) (u : ℝ) :
    S.orbitIntegral f u - S.orbitIntegral g u = S.orbitIntegral (f - g) u := by
  simp only [orbitIntegral_apply, map_sub]
  exact (intervalIntegral.integral_sub ((S.continuous_operator_toNNReal f).intervalIntegrable _ _)
    ((S.continuous_operator_toNNReal g).intervalIntegrable _ _)).symm

/-- The orbit integral over `[0, t]` is bounded in norm by `‖f‖ * t`. -/
theorem norm_orbitIntegral_le (f : E) (t : ℝ≥0) : ‖S.orbitIntegral f t‖ ≤ ‖f‖ * t := by
  rw [orbitIntegral_apply]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
    (C := ‖f‖) (f := fun s : ℝ => S (Real.toNNReal s) f) (fun _ _ => S.norm_apply_le _ f)
  rwa [sub_zero, abs_of_nonneg t.coe_nonneg] at h

/-- Continuity of the orbit integral over `[0, t]` with respect to the vector. -/
theorem tendsto_orbitIntegral {ι : Type*} {l : Filter ι} {v : ι → E} {g : E}
    (hv : Tendsto v l (𝓝 g)) (t : ℝ≥0) :
    Tendsto (fun i : ι => S.orbitIntegral (v i) t) l (𝓝 (S.orbitIntegral g t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun i : ι => ‖v i - g‖ * (t : ℝ))
    (fun _ => norm_nonneg _) (fun i => ?_) ?_
  · rw [S.orbitIntegral_sub]
    exact S.norm_orbitIntegral_le _ t
  · simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hv).mul_const (t : ℝ)

private theorem tendsto_slope_add_of_hasDerivAt {F : ℝ → E} {F' : E} {u : ℝ}
    (hF : HasDerivAt F F' u) :
    Tendsto (fun h : ℝ≥0 => (h : ℝ)⁻¹ • (F (u + h) - F u)) (𝓝[>] 0) (𝓝 F') := by
  have hslope := hasDerivAt_iff_tendsto_slope.mp hF
  have hmap : Tendsto (fun h : ℝ≥0 => u + (h : ℝ)) (𝓝[>] 0) (𝓝[≠] u) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 : Tendsto (fun h : ℝ≥0 => u + (h : ℝ)) (𝓝 0) (𝓝 (u + ((0 : ℝ≥0) : ℝ))) :=
        (continuous_const.add NNReal.continuous_coe).tendsto _
      rw [NNReal.coe_zero, add_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      have hpos : (0 : ℝ) < h := NNReal.coe_pos.mpr hh
      exact ne_of_gt (lt_add_of_pos_right u hpos)
  refine (hslope.comp hmap).congr fun h => ?_
  change slope F u (u + h) = (h : ℝ)⁻¹ • (F (u + h) - F u)
  rw [slope_def_module, add_sub_cancel_left]

variable [CompleteSpace E]

/-- **Fundamental Integral Identity of the Generator**:
For `f ∈ D(L)` and every `t : ℝ≥0`, `S(t) f - f = ∫₀ᵗ S(s) (L f) ds`. -/
theorem operator_sub_eq_integral (f : S.generatorDomain) (t : ℝ≥0) :
    S t f - f = ∫ s in (0 : ℝ)..t, S (Real.toNNReal s) (S.generator f) := by
  have hcont : ContinuousOn (fun s : ℝ => S (Real.toNNReal s) f) (Set.Icc 0 t) :=
    (S.continuous_operator_toNNReal f).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) t,
      HasDerivWithinAt (fun s : ℝ => S (Real.toNNReal s) f)
        (S (Real.toNNReal x) (S.generator f)) (Set.Ioi x) x := by
    intro x hx
    have h := S.hasDerivWithinAt_Ioi f (Real.toNNReal x)
    rwa [Real.coe_toNNReal x hx.1.le] at h
  have hint : IntervalIntegrable (fun s : ℝ => S (Real.toNNReal s) (S.generator f))
      MeasureTheory.volume 0 t :=
    (S.continuous_operator_toNNReal _).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.coe_nonneg hcont
    hderiv hint
  rw [hftc, Real.toNNReal_coe, Real.toNNReal_zero, S.zero_apply]

/-- Differentiability of the orbit integral with respect to its upper limit. -/
theorem hasDerivAt_orbitIntegral (f : E) (u : ℝ) :
    HasDerivAt (S.orbitIntegral f) (S (Real.toNNReal u) f) u :=
  ((S.continuous_operator_toNNReal f).integral_hasStrictDerivAt 0 u).hasDerivAt

/-- Action of `S(h)` on an orbit integral shifts the integration interval. -/
theorem operator_orbitIntegral (f : E) (t h : ℝ≥0) :
    S h (S.orbitIntegral f t) = S.orbitIntegral f (t + h) - S.orbitIntegral f h := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ => S (Real.toNNReal s) f)
      MeasureTheory.volume a b :=
    fun a b => (S.continuous_operator_toNNReal f).intervalIntegrable a b
  have hshift : Set.EqOn (fun s : ℝ => S h (S (Real.toNNReal s) f))
      (fun s : ℝ => S (Real.toNNReal (s + h)) f) (Set.uIcc (0 : ℝ) t) := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := by
      rw [Set.uIcc_of_le t.coe_nonneg] at hs
      exact hs.1
    have hcoe : Real.toNNReal (s + h) = h + Real.toNNReal s := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, Real.coe_toNNReal s hs0,
        Real.coe_toNNReal _ (add_nonneg hs0 h.coe_nonneg), add_comm]
    change S h (S (Real.toNNReal s) f) = S (Real.toNNReal (s + h)) f
    rw [hcoe, S.add_apply]
  rw [orbitIntegral, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hint 0 t),
    intervalIntegral.integral_congr hshift,
    intervalIntegral.integral_comp_add_right (fun s : ℝ => S (Real.toNNReal s) f) (h : ℝ), zero_add,
    orbitIntegral, orbitIntegral,
    intervalIntegral.integral_interval_sub_left (hint 0 _) (hint 0 _)]

/-- Difference quotients of an orbit integral converge to `S(t) f - f`. -/
theorem tendsto_differenceQuotient_orbitIntegral (f : E) (t : ℝ≥0) :
    Tendsto (fun h : ℝ≥0 => (h : ℝ)⁻¹ • (S h (S.orbitIntegral f t) - S.orbitIntegral f t))
      (𝓝[>] 0) (𝓝 (S t f - f)) := by
  have ht := tendsto_slope_add_of_hasDerivAt (S.hasDerivAt_orbitIntegral f t)
  have h0 := tendsto_slope_add_of_hasDerivAt (S.hasDerivAt_orbitIntegral f 0)
  rw [Real.toNNReal_coe] at ht
  rw [Real.toNNReal_zero, S.zero_apply] at h0
  refine (ht.sub h0).congr fun h => ?_
  rw [S.operator_orbitIntegral, zero_add, S.orbitIntegral_zero, sub_zero, ← smul_sub,
    sub_right_comm]

/-- Every orbit integral `∫₀ᵗ S(s) f ds` belongs to the generator domain `D(L)`. -/
theorem orbitIntegral_mem_generatorDomain (f : E) (t : ℝ≥0) :
    S.orbitIntegral f t ∈ S.generatorDomain :=
  S.mem_generatorDomain_of_tendsto (S.tendsto_differenceQuotient_orbitIntegral f t)

/-- The generator applied to an orbit integral equals the orbit increment:
`L (∫₀ᵗ S(s) f ds) = S(t) f - f`. -/
theorem generator_orbitIntegral (f : E) (t : ℝ≥0) :
    S.generator ⟨S.orbitIntegral f t, S.orbitIntegral_mem_generatorDomain f t⟩ = S t f - f :=
  S.generator_eq_of_tendsto _ (S.tendsto_differenceQuotient_orbitIntegral f t)

/-- Time averages `t⁻¹ • ∫₀ᵗ S(s) f ds` converge to `f` as `t → 0⁺`. -/
theorem tendsto_inv_smul_orbitIntegral (f : E) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • S.orbitIntegral f t) (𝓝[>] 0) (𝓝 f) := by
  have h0 := tendsto_slope_add_of_hasDerivAt (S.hasDerivAt_orbitIntegral f 0)
  rw [Real.toNNReal_zero, S.zero_apply] at h0
  refine h0.congr fun t => ?_
  rw [zero_add, S.orbitIntegral_zero, sub_zero]

/-- **Density of the Generator Domain**:
For every strongly continuous contraction semigroup `S` on a complete normed space `E`,
the generator domain `D(L)` is dense in `E`. -/
theorem dense_generatorDomain : Dense (S.generatorDomain : Set E) := by
  intro f
  refine mem_closure_of_tendsto (S.tendsto_inv_smul_orbitIntegral f) ?_
  exact Eventually.of_forall fun t =>
    S.generatorDomain.smul_mem _ (S.orbitIntegral_mem_generatorDomain f t)

/-! ### Closedness of the Generator -/

/-- Passing to the limit in the fundamental integral identity of the generator. -/
theorem operator_sub_eq_orbitIntegral_of_tendsto_generator
    {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → S.generatorDomain} {f g : E}
    (hu : Tendsto (fun i : ι => (u i : E)) l (𝓝 f))
    (hL : Tendsto (fun i : ι => S.generator (u i)) l (𝓝 g)) (t : ℝ≥0) :
    S t f - f = S.orbitIntegral g t := by
  have h1 : Tendsto (fun i : ι => S t (u i : E) - (u i : E)) l (𝓝 (S t f - f)) :=
    (((S t).continuous.tendsto f).comp hu).sub hu
  have h2 : Tendsto (fun i : ι => S t (u i : E) - (u i : E)) l (𝓝 (S.orbitIntegral g t)) := by
    refine (S.tendsto_orbitIntegral hL t).congr fun i => ?_
    rw [orbitIntegral_apply]
    exact (S.operator_sub_eq_integral (u i) t).symm
  exact tendsto_nhds_unique h1 h2

/-- **The Infinitesimal Generator is a Closed Operator (Domain Membership)**:
If `u_i ∈ D(L)` converges to `f` and `L u_i` converges to `g`, then `f ∈ D(L)`. -/
theorem mem_generatorDomain_of_tendsto_generator
    {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → S.generatorDomain} {f g : E}
    (hu : Tendsto (fun i : ι => (u i : E)) l (𝓝 f))
    (hL : Tendsto (fun i : ι => S.generator (u i)) l (𝓝 g)) :
    f ∈ S.generatorDomain := by
  apply S.mem_generatorDomain_of_tendsto
  refine (S.tendsto_inv_smul_orbitIntegral g).congr fun t => ?_
  rw [S.operator_sub_eq_orbitIntegral_of_tendsto_generator hu hL t]

/-- **The Infinitesimal Generator is a Closed Operator (Value Identification)**:
If `u_i ∈ D(L)` converges to `f` and `L u_i` converges to `g`, then `L f = g`. -/
theorem generator_eq_of_tendsto_generator
    {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → S.generatorDomain} {f g : E}
    (hu : Tendsto (fun i : ι => (u i : E)) l (𝓝 f))
    (hL : Tendsto (fun i : ι => S.generator (u i)) l (𝓝 g)) :
    S.generator ⟨f, S.mem_generatorDomain_of_tendsto_generator hu hL⟩ = g := by
  apply S.generator_eq_of_tendsto
  refine (S.tendsto_inv_smul_orbitIntegral g).congr fun t => ?_
  rw [S.operator_sub_eq_orbitIntegral_of_tendsto_generator hu hL t]

/-! ### Uniqueness of the Semigroup from its Generator -/

variable (T : StronglyContinuousContractionSemigroup E)

private noncomputable def transferOrbit (f : E) (t s : ℝ) : E :=
  S (Real.toNNReal (t - s)) (T (Real.toNNReal s) f)

omit [CompleteSpace E] in
private theorem transferOrbit_apply (f : E) (t s : ℝ) :
    S.transferOrbit T f t s = S (Real.toNNReal (t - s)) (T (Real.toNNReal s) f) := rfl

omit [CompleteSpace E] in
private theorem continuous_transferOrbit (f : E) (t : ℝ) :
    Continuous (S.transferOrbit T f t) :=
  S.continuous_operator_apply
    (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))
    (T.continuous_operator_toNNReal f)

omit [CompleteSpace E] in
private theorem transferOrbit_zero (f : E) (t : ℝ) :
    S.transferOrbit T f t 0 = S (Real.toNNReal t) f := by
  rw [transferOrbit_apply, sub_zero, Real.toNNReal_zero, T.zero_apply]

omit [CompleteSpace E] in
private theorem transferOrbit_self (f : E) (t : ℝ) :
    S.transferOrbit T f t t = T (Real.toNNReal t) f := by
  rw [transferOrbit_apply, sub_self, Real.toNNReal_zero, S.zero_apply]

omit [CompleteSpace E] in
private theorem hasDerivWithinAt_transferOrbit
    (hdom : S.generatorDomain = T.generatorDomain)
    (hgen : ∀ (f : E) (hS : f ∈ S.generatorDomain) (hT : f ∈ T.generatorDomain),
      S.generator ⟨f, hS⟩ = T.generator ⟨f, hT⟩)
    {f : E} (hf : f ∈ S.generatorDomain) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    HasDerivWithinAt (S.transferOrbit T f t) 0 (Ici s) s := by
  have hfT : f ∈ T.generatorDomain := by rwa [← hdom]
  have hgT : T (Real.toNNReal s) f ∈ T.generatorDomain :=
    T.operator_mem_generatorDomain ⟨f, hfT⟩ (Real.toNNReal s)
  have hgS : T (Real.toNNReal s) f ∈ S.generatorDomain := by rwa [hdom]
  have hto : Tendsto (fun y : ℝ => Real.toNNReal (y - s)) (𝓝[>] s) (𝓝[>] 0) := by
    have h := tendsto_toNNReal_sub (Real.toNNReal s)
    rwa [Real.coe_toNNReal s hs] at h
  have hbound : Tendsto (fun y : ℝ =>
      ‖T.differenceQuotient (T (Real.toNNReal s) f) (Real.toNNReal (y - s)) -
        S.differenceQuotient (T (Real.toNNReal s) f) (Real.toNNReal (y - s))‖)
      (𝓝[>] s) (𝓝 0) := by
    have hT' := (T.tendsto_generator ⟨T (Real.toNNReal s) f, hgT⟩).comp hto
    have hS' := (S.tendsto_generator ⟨T (Real.toNNReal s) f, hgS⟩).comp hto
    have hdiff := hT'.sub hS'
    rw [← hgen _ hgS hgT, sub_self] at hdiff
    simpa using hdiff.norm
  have hslope : ∀ y ∈ Ioo s t, slope (S.transferOrbit T f t) s y =
      S (Real.toNNReal (t - y))
        (T.differenceQuotient (T (Real.toNNReal s) f) (Real.toNNReal (y - s)) -
          S.differenceQuotient (T (Real.toNNReal s) f) (Real.toNNReal (y - s))) := by
    intro y hy
    have hsy : (0 : ℝ) ≤ y - s := sub_nonneg.mpr hy.1.le
    have hcoe : ((Real.toNNReal (y - s) : ℝ≥0) : ℝ) = y - s := Real.coe_toNNReal _ hsy
    have hy0 : (0 : ℝ) ≤ y := hs.trans hy.1.le
    have hsplit : Real.toNNReal y = Real.toNNReal (y - s) + Real.toNNReal s := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, hcoe, Real.coe_toNNReal s hs, Real.coe_toNNReal y hy0]
      ring
    have hwindow : Real.toNNReal (t - s) = Real.toNNReal (t - y) + Real.toNNReal (y - s) := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, hcoe, Real.coe_toNNReal _ (sub_nonneg.mpr hy.2.le),
        Real.coe_toNNReal _ (sub_nonneg.mpr (hy.1.trans hy.2).le)]
      ring
    have key : S.transferOrbit T f t y - S.transferOrbit T f t s =
        S (Real.toNNReal (t - y))
          (T (Real.toNNReal (y - s)) (T (Real.toNNReal s) f) -
            S (Real.toNNReal (y - s)) (T (Real.toNNReal s) f)) := by
      rw [transferOrbit_apply, transferOrbit_apply, hsplit, T.add_apply, hwindow, S.add_apply,
        ← map_sub]
    rw [slope_def_module, key, T.differenceQuotient_apply, S.differenceQuotient_apply, hcoe,
      ← smul_sub, map_smul, sub_sub_sub_cancel_right]
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hdiff : Ici s \ {s} = Ioi s := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    exact ⟨fun hy => lt_of_le_of_ne hy.1 (Ne.symm hy.2), fun hy => ⟨hy.le, hy.ne'⟩⟩
  rw [hdiff]
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [Ioo_mem_nhdsGT hst] with y hy
  rw [hslope y hy]
  exact S.norm_apply_le _ _

/-- **Uniqueness of the Semigroup from its Generator**:
Two strongly continuous contraction semigroups on a complete real normed space `E` with the
same generator domain and the same generator on that domain are identical: `S = T`. -/
theorem ext_of_generator (hdom : S.generatorDomain = T.generatorDomain)
    (hgen : ∀ (f : E) (hS : f ∈ S.generatorDomain) (hT : f ∈ T.generatorDomain),
      S.generator ⟨f, hS⟩ = T.generator ⟨f, hT⟩) :
    S = T := by
  have hcore : ∀ (t : ℝ≥0) (f : E), f ∈ S.generatorDomain → S t f = T t f := by
    intro t f hf
    have hconst := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f := fun s => S.transferOrbit T f t s - S.transferOrbit T f t 0)
      (f' := fun _ => (0 : E)) (K := 0) (a := 0) (b := (t : ℝ))
      (((S.continuous_transferOrbit T f t).sub continuous_const).continuousOn)
      (fun s hs =>
        (S.hasDerivWithinAt_transferOrbit T hdom hgen hf hs.1 hs.2).sub_const _)
      (sub_self _)
      (fun _ _ => by rw [norm_zero, zero_mul])
      (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
    rw [sub_eq_zero, transferOrbit_self, transferOrbit_zero, Real.toNNReal_coe] at hconst
    exact hconst.symm
  refine StronglyContinuousContractionSemigroup.ext fun t => ?_
  refine DFunLike.coe_injective ?_
  refine Continuous.ext_on S.dense_generatorDomain (S t).continuous (T t).continuous ?_
  intro f hf
  exact hcore t f hf

end StronglyContinuousContractionSemigroup

end

end FracLap
