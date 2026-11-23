/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Core.FourierSobolev
public import FracLap.HalfLine.RestrictedDensity
public import FracLap.HalfLine.RestrictedSemigroup
public import FracLap.WholeLine.FourierSemigroup
public import FracLap.WholeLine.GagliardoSymbolExact
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLap.WholeLine.SobolevEquivalence

Completeness of the Fourier Sobolev spaces `H^s(ℝ)`, exact identification with Gagliardo spaces
and Mathlib's `TemperedDistribution.MemSobolev`, self-adjointness and Friedrichs form identity
for `fracLapSemigroup`, and closedness/density of the half-line Dirichlet spaces (`B5`):
- `FourierSobolevSpace s` (`thm:fracsobolevhilbert`): separable complex Hilbert space `H^s(ℝ)`
  isometrically isomorphic to `L²(ℝ; ℂ)` via `J_s u = (1 + ξ²)^(s/2) 𝓕 u`.
- `memSobolev_two_iff_memFourierSobolev`: for `s ≥ 0` and `f ∈ L²(ℝ; ℂ)`,
  `TemperedDistribution.MemSobolev s 2 (f : 𝓢'(ℝ, ℂ))` iff `f ∈ H^s(ℝ)`.
- `gagliardoEnergyC_lt_top_iff_memFourierSobolev`, `norm_sq_gagliardoSpace_equiv_fourierSobolev`
  (`thm:sobolev_equal`): for `0 < α < 2`, `H^(α/2)(ℝ)` equals `GagliardoSpace α` with explicit
  two-sided norm equivalence.
- `inner_neg_generator_fracLapSemigroup_eq`, `inner_neg_generator_fracLapSemigroup_symm`,
  `inner_neg_generator_fracLapSemigroup_re_nonneg`, `fracLapSemigroup_selfAdjoint`
  (`prop:selfadjoint`): symmetry, nonnegativity, and self-adjointness of `-A_α`.
- `denseRange_gagliardoL2Part`, `gagliardoForm_eq_inner_neg_generator` (`prop:fracform`):
  dense definition of `H^(α/2)(ℝ)` in `L²(ℝ; ℝ)` and Friedrichs weak-form equivalence.
- `l2ZeroSubmodule`, `isClosed_l2ZeroSubmodule`, `l2ZeroIsoIoi`,
  `denseRange_restrictedGagliardoL2Zero` (`prop:zerospaces`): closedness, Hilbert identification
  with `L²((0, ∞); ℝ)`, and density of `H^(α/2)_0(ℝ)` in `L²_0(ℝ)`.
-/

namespace FracLap

open Complex Filter FourierTransform MeasureTheory Real Set TemperedDistribution Topology
open scoped ENNReal NNReal InnerProductSpace ComplexInnerProductSpace SchwartzMap

@[expose] public section

/-! ### 1. Bessel weight and Fourier Sobolev Hilbert space `H^s(ℝ)` (`thm:fracsobolevhilbert`) -/

/-- The positive Bessel weight `(1 + ‖ξ‖²)^(s / 2)` as a measurable function of `ξ : ℝ`. -/
noncomputable def besselHalfWeight (s ξ : ℝ) : ℝ :=
  (1 + ‖ξ‖ ^ 2) ^ (s / 2)

theorem besselHalfWeight_eq (s ξ : ℝ) : besselHalfWeight s ξ = (1 + ξ ^ 2) ^ (s / 2) := by
  simp [besselHalfWeight]

theorem measurable_besselHalfWeight (s : ℝ) : Measurable (besselHalfWeight s) := by
  unfold besselHalfWeight
  fun_prop

theorem besselHalfWeight_pos (s ξ : ℝ) : 0 < besselHalfWeight s ξ := by
  unfold besselHalfWeight
  positivity

theorem besselHalfWeight_neg_le_one {s : ℝ} (hs : 0 ≤ s) (ξ : ℝ) :
    besselHalfWeight (-s) ξ ≤ 1 := by
  unfold besselHalfWeight
  rw [neg_div]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [sq_nonneg ‖ξ‖]) (by linarith)

theorem besselHalfWeight_mul_neg (s ξ : ℝ) :
    besselHalfWeight s ξ * besselHalfWeight (-s) ξ = 1 := by
  unfold besselHalfWeight
  rw [← Real.rpow_add (by positivity : 0 < 1 + ‖ξ‖ ^ 2)]
  simp [show s / 2 + (-s) / 2 = 0 by ring]

/-- Membership predicate for `L²(ℝ; ℂ)` functions lying in the Fourier Sobolev space `H^s(ℝ)`. -/
def MemFourierSobolev (s : ℝ) (f : L2C) : Prop :=
  MemLp (fun ξ : ℝ => ((besselHalfWeight s ξ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ) 2 volume

theorem memFourierSobolev_zero (s : ℝ) : MemFourierSobolev s (0 : L2C) := by
  unfold MemFourierSobolev
  have hz : (fun ξ : ℝ => ((besselHalfWeight s ξ : ℝ) : ℂ) *
      ((𝓕 (0 : L2C) : L2C) : ℝ → ℂ) ξ) =ᵐ[volume] 0 := by
    have hF0 : (𝓕 (0 : L2C) : L2C) = 0 := map_zero _
    rw [hF0]
    filter_upwards [Lp.coeFn_zero ℂ 2 volume] with ξ hξ
    change ((besselHalfWeight s ξ : ℝ) : ℂ) * ((0 : L2C) : ℝ → ℂ) ξ = 0
    rw [hξ]
    simp
  exact (MemLp.zero (p := 2) (μ := volume)).ae_eq hz.symm

theorem memFourierSobolev_add {s : ℝ} {f g : L2C} (hf : MemFourierSobolev s f)
    (hg : MemFourierSobolev s g) : MemFourierSobolev s (f + g) := by
  unfold MemFourierSobolev at hf hg ⊢
  have hFadd : (𝓕 (f + g) : L2C) = (𝓕 f : L2C) + (𝓕 g : L2C) :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).map_add f g
  have hsum : (fun ξ : ℝ => ((besselHalfWeight s ξ : ℝ) : ℂ) *
      ((𝓕 (f + g) : L2C) : ℝ → ℂ) ξ) =ᵐ[volume]
      (fun ξ => ((besselHalfWeight s ξ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ +
        ((besselHalfWeight s ξ : ℝ) : ℂ) * ((𝓕 g : L2C) : ℝ → ℂ) ξ) := by
    rw [hFadd]
    filter_upwards [Lp.coeFn_add (𝓕 f : L2C) (𝓕 g : L2C)] with ξ hξ
    rw [hξ, Pi.add_apply, mul_add]
  exact (hf.add hg).ae_eq hsum.symm

theorem memFourierSobolev_smul {s : ℝ} (c : ℂ) {f : L2C} (hf : MemFourierSobolev s f) :
    MemFourierSobolev s (c • f) := by
  unfold MemFourierSobolev at hf ⊢
  have hFsm : (𝓕 (c • f) : L2C) = c • (𝓕 f : L2C) :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).map_smul c f
  have hsm : (fun ξ : ℝ => ((besselHalfWeight s ξ : ℝ) : ℂ) *
      ((𝓕 (c • f) : L2C) : ℝ → ℂ) ξ) =ᵐ[volume]
      (fun ξ => c * (((besselHalfWeight s ξ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ)) := by
    rw [hFsm]
    filter_upwards [Lp.coeFn_smul c (𝓕 f : L2C)] with ξ hξ
    rw [hξ, Pi.smul_apply, smul_eq_mul]
    ring
  exact (hf.const_smul c).ae_eq hsm.symm

/-- Fourier Sobolev space `H^s(ℝ)` as a bundled subspace of `L²(ℝ; ℂ)`. -/
@[ext]
structure FourierSobolevSpace (s : ℝ) where
  /-- Underlying `L²(ℝ; ℂ)` element. -/
  toL2 : L2C
  /-- Membership of `(1 + ξ²)^(s / 2) 𝓕 u` in `L²(ℝ; ℂ)`. -/
  mem : MemFourierSobolev s toL2

noncomputable instance (s : ℝ) : Zero (FourierSobolevSpace s) :=
  ⟨⟨0, memFourierSobolev_zero s⟩⟩

noncomputable instance (s : ℝ) : Add (FourierSobolevSpace s) :=
  ⟨fun u v => ⟨u.toL2 + v.toL2, memFourierSobolev_add u.mem v.mem⟩⟩

noncomputable instance (s : ℝ) : Neg (FourierSobolevSpace s) :=
  ⟨fun u => ⟨(-1 : ℂ) • u.toL2, memFourierSobolev_smul (-1) u.mem⟩⟩

noncomputable instance (s : ℝ) : Sub (FourierSobolevSpace s) :=
  ⟨fun u v => u + (-v)⟩

noncomputable instance (s : ℝ) : SMul ℂ (FourierSobolevSpace s) :=
  ⟨fun c u => ⟨c • u.toL2, memFourierSobolev_smul c u.mem⟩⟩

@[simp] theorem fourierSobolev_toL2_zero (s : ℝ) : (0 : FourierSobolevSpace s).toL2 = 0 := rfl
@[simp] theorem fourierSobolev_toL2_add {s : ℝ} (u v : FourierSobolevSpace s) :
    (u + v).toL2 = u.toL2 + v.toL2 := rfl
@[simp] theorem fourierSobolev_toL2_neg {s : ℝ} (u : FourierSobolevSpace s) :
    (-u).toL2 = -u.toL2 := by
  change (-1 : ℂ) • u.toL2 = -u.toL2
  simp
@[simp] theorem fourierSobolev_toL2_sub {s : ℝ} (u v : FourierSobolevSpace s) :
    (u - v).toL2 = u.toL2 - v.toL2 := by
  change u.toL2 + (-1 : ℂ) • v.toL2 = u.toL2 - v.toL2
  simp [sub_eq_add_neg]
@[simp] theorem fourierSobolev_toL2_smul {s : ℝ} (c : ℂ) (u : FourierSobolevSpace s) :
    (c • u).toL2 = c • u.toL2 := rfl

noncomputable instance (s : ℝ) : AddCommGroup (FourierSobolevSpace s) where
  add_assoc a b c := by ext; simp [add_assoc]
  zero_add a := by ext; simp
  add_zero a := by ext; simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by ext; simp
  add_comm a b := by ext; simp [add_comm]

noncomputable instance (s : ℝ) : Module ℂ (FourierSobolevSpace s) where
  one_smul a := by ext; simp
  mul_smul a b x := by ext; simp [mul_smul]
  smul_zero a := by ext; simp
  smul_add a x y := by ext; simp [smul_add]
  add_smul a b x := by ext; simp [add_smul]
  zero_smul x := by ext; simp

/-- Isometric Bessel operator `J_s : H^s(ℝ) → L²(ℝ; ℂ)` defined by
`(J_s u)(ξ) = (1 + ξ²)^(s / 2) 𝓕 u(ξ)`. -/
noncomputable def fourierSobolevToL2 (s : ℝ) : FourierSobolevSpace s →ₗ[ℂ] L2C where
  toFun u := u.mem.toLp (fun ξ : ℝ => ((besselHalfWeight s ξ : ℝ) : ℂ) *
    ((𝓕 u.toL2 : L2C) : ℝ → ℂ) ξ)
  map_add' u v := by
    rw [Lp.ext_iff]
    have hFadd : (𝓕 (u + v).toL2 : L2C) = (𝓕 u.toL2 : L2C) + (𝓕 v.toL2 : L2C) :=
      (Lp.fourierTransformₗᵢ ℝ ℂ).map_add u.toL2 v.toL2
    filter_upwards [(u + v).mem.coeFn_toLp, u.mem.coeFn_toLp, v.mem.coeFn_toLp,
      Lp.coeFn_add (u.mem.toLp _) (v.mem.toLp _), Lp.coeFn_add (𝓕 u.toL2 : L2C) (𝓕 v.toL2 : L2C)]
      with ξ h1 h2 h3 h4 h5
    have hF : ((𝓕 (u + v).toL2 : L2C) : ℝ → ℂ) ξ =
        ((𝓕 u.toL2 : L2C) : ℝ → ℂ) ξ + ((𝓕 v.toL2 : L2C) : ℝ → ℂ) ξ := by
      rw [hFadd]
      exact h5
    rw [h1, h4, Pi.add_apply, h2, h3, hF, mul_add]
  map_smul' c u := by
    rw [Lp.ext_iff, RingHom.id_apply]
    have hFsm : (𝓕 (c • u).toL2 : L2C) = c • (𝓕 u.toL2 : L2C) :=
      (Lp.fourierTransformₗᵢ ℝ ℂ).map_smul c u.toL2
    filter_upwards [(c • u).mem.coeFn_toLp, u.mem.coeFn_toLp,
      Lp.coeFn_smul c (u.mem.toLp _), Lp.coeFn_smul c (𝓕 u.toL2 : L2C)] with ξ h1 h2 h3 h4
    have hF : ((𝓕 (c • u).toL2 : L2C) : ℝ → ℂ) ξ = c * ((𝓕 u.toL2 : L2C) : ℝ → ℂ) ξ := by
      rw [hFsm]
      simpa [smul_eq_mul] using h4
    rw [h1, h3, Pi.smul_apply, smul_eq_mul, h2, hF]
    ring

theorem fourierSobolevToL2_injective (s : ℝ) : Function.Injective (fourierSobolevToL2 s) := by
  intro u v huv
  have hae : (fourierSobolevToL2 s u : ℝ → ℂ) =ᵐ[volume] (fourierSobolevToL2 s v : ℝ → ℂ) :=
    Lp.ext_iff.mp huv
  have hFu : (𝓕 u.toL2 : L2C) = (𝓕 v.toL2 : L2C) := by
    rw [Lp.ext_iff]
    filter_upwards [hae, u.mem.coeFn_toLp, v.mem.coeFn_toLp] with ξ h1 h2 h3
    change (fourierSobolevToL2 s u : ℝ → ℂ) ξ =
        ((besselHalfWeight s ξ : ℝ) : ℂ) * ((𝓕 u.toL2 : L2C) : ℝ → ℂ) ξ at h2
    change (fourierSobolevToL2 s v : ℝ → ℂ) ξ =
        ((besselHalfWeight s ξ : ℝ) : ℂ) * ((𝓕 v.toL2 : L2C) : ℝ → ℂ) ξ at h3
    have hmul : ((besselHalfWeight s ξ : ℝ) : ℂ) * ((𝓕 u.toL2 : L2C) : ℝ → ℂ) ξ =
        ((besselHalfWeight s ξ : ℝ) : ℂ) * ((𝓕 v.toL2 : L2C) : ℝ → ℂ) ξ := by
      rw [← h2, ← h3, h1]
    have hne : ((besselHalfWeight s ξ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (besselHalfWeight_pos s ξ).ne'
    exact mul_left_cancel₀ hne hmul
  exact FourierSobolevSpace.ext ((Lp.fourierTransformₗᵢ ℝ ℂ).injective hFu)

/-- Inner product space core on `FourierSobolevSpace s`, induced via `J_s`. -/
@[instance_reducible]
noncomputable def fourierSobolevCore (s : ℝ) :
    InnerProductSpace.Core ℂ (FourierSobolevSpace s) where
  inner u v := @inner ℂ L2C _ (fourierSobolevToL2 s u) (fourierSobolevToL2 s v)
  conj_inner_symm u v := inner_conj_symm _ _
  re_inner_nonneg u := inner_self_nonneg
  add_left u v w := by simp only [map_add, inner_add_left]
  smul_left u v c := by simp only [map_smul, inner_smul_left]
  definite u hu := by
    have h0 : fourierSobolevToL2 s u = 0 := inner_self_eq_zero.mp hu
    exact fourierSobolevToL2_injective s (h0.trans (map_zero _).symm)

noncomputable instance instNormedAddCommGroupFourierSobolevSpace (s : ℝ) :
    NormedAddCommGroup (FourierSobolevSpace s) :=
  (fourierSobolevCore s).toNormedAddCommGroup

noncomputable instance instInnerProductSpaceFourierSobolevSpace (s : ℝ) :
    InnerProductSpace ℂ (FourierSobolevSpace s) :=
  InnerProductSpace.ofCore (fourierSobolevCore s).toCore

theorem fourierSobolev_inner_eq (s : ℝ) (u v : FourierSobolevSpace s) :
    @inner ℂ (FourierSobolevSpace s) _ u v =
      @inner ℂ L2C _ (fourierSobolevToL2 s u) (fourierSobolevToL2 s v) := rfl

theorem fourierSobolev_norm_eq (s : ℝ) (u : FourierSobolevSpace s) :
    ‖u‖ = ‖fourierSobolevToL2 s u‖ := by
  have h1 : ‖u‖ ^ 2 = ‖fourierSobolevToL2 s u‖ ^ 2 := by
    have hs1 : ((‖u‖ ^ 2 : ℝ) : ℂ) = @inner ℂ (FourierSobolevSpace s) _ u u := by
      rw [inner_self_eq_norm_sq_to_K]; simp
    have hs2 : ((‖fourierSobolevToL2 s u‖ ^ 2 : ℝ) : ℂ) =
        @inner ℂ L2C _ (fourierSobolevToL2 s u) (fourierSobolevToL2 s u) := by
      rw [inner_self_eq_norm_sq_to_K]; simp
    have hre := congrArg Complex.re (hs1.trans ((fourierSobolev_inner_eq s u u).trans hs2.symm))
    simpa only [Complex.ofReal_re] using hre
  have hsq := congrArg Real.sqrt h1
  simpa only [Real.sqrt_sq (norm_nonneg _)] using hsq

theorem fourierSobolev_norm_sq_eq (s : ℝ) (u : FourierSobolevSpace s) :
    ‖u‖ ^ 2 = ∫ ξ : ℝ, (1 + ξ ^ 2) ^ s * ‖((𝓕 u.toL2 : L2C) : ℝ → ℂ) ξ‖ ^ 2 := by
  have h1 : ‖u‖ ^ 2 = (@inner ℂ (FourierSobolevSpace s) _ u u).re := by
    have hs : @inner ℂ (FourierSobolevSpace s) _ u u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; simp
    rw [hs, Complex.ofReal_re]
  rw [h1, fourierSobolev_inner_eq, MeasureTheory.L2.inner_def]
  have hre_comm := (Complex.reCLM.integral_comp_comm
    (MeasureTheory.L2.integrable_inner ((fourierSobolevToL2 s) u) ((fourierSobolevToL2 s) u))).symm
  rw [show (∫ a : ℝ, @inner ℂ ℂ _ ((fourierSobolevToL2 s u : ℝ → ℂ) a)
      ((fourierSobolevToL2 s u : ℝ → ℂ) a)).re =
      Complex.reCLM (∫ a : ℝ, @inner ℂ ℂ _ ((fourierSobolevToL2 s u : ℝ → ℂ) a)
        ((fourierSobolevToL2 s u : ℝ → ℂ) a)) from rfl, hre_comm]
  refine integral_congr_ae ?_
  filter_upwards [u.mem.coeFn_toLp] with ξ hξ
  change (Complex.reCLM (@inner ℂ ℂ _ ((fourierSobolevToL2 s u : ℝ → ℂ) ξ)
      ((fourierSobolevToL2 s u : ℝ → ℂ) ξ))) = _
  change RCLike.re (@inner ℂ ℂ _ ((fourierSobolevToL2 s u : ℝ → ℂ) ξ)
      ((fourierSobolevToL2 s u : ℝ → ℂ) ξ)) = _
  rw [inner_self_eq_norm_sq (𝕜 := ℂ)]
  change ‖(u.mem.toLp _ : ℝ → ℂ) ξ‖ ^ 2 = _
  rw [hξ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (besselHalfWeight_pos s ξ), mul_pow]
  congr 1
  rw [besselHalfWeight_eq, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

theorem fourierSobolevFromL2_memLp {s : ℝ} (hs : 0 ≤ s) (w : L2C) :
    MemLp (fun ξ : ℝ => ((besselHalfWeight (-s) ξ : ℝ) : ℂ) * (w : ℝ → ℂ) ξ) 2 volume := by
  have hw := (Lp.memLp w).norm
  refine MemLp.mono' hw ?_ ?_
  · exact ((Complex.continuous_ofReal.measurable.comp
      (measurable_besselHalfWeight (-s))).mul
        (Lp.stronglyMeasurable w).measurable).aestronglyMeasurable
  · filter_upwards with ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (besselHalfWeight_pos (-s) ξ)]
    exact mul_le_of_le_one_left (norm_nonneg _) (besselHalfWeight_neg_le_one hs ξ)

/-- Auxiliary inverse `J_s⁻¹ : L²(ℝ; ℂ) → H^s(ℝ)` for `s ≥ 0`:
`w ↦ 𝓕⁻ ((1 + ξ²)^(-s/2) w)`. -/
noncomputable def fourierSobolevFromL2 {s : ℝ} (hs : 0 ≤ s) (w : L2C) : FourierSobolevSpace s :=
  let hw_mem := fourierSobolevFromL2_memLp hs w
  let f : L2C := 𝓕⁻ (hw_mem.toLp (fun ξ : ℝ =>
    ((besselHalfWeight (-s) ξ : ℝ) : ℂ) * (w : ℝ → ℂ) ξ))
  have hf_mem : MemFourierSobolev s f := by
    unfold MemFourierSobolev
    refine (Lp.memLp w).ae_eq ?_
    have hFf : (𝓕 f : L2C) =
        hw_mem.toLp (fun ξ : ℝ => ((besselHalfWeight (-s) ξ : ℝ) : ℂ) * (w : ℝ → ℂ) ξ) :=
      (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _
    rw [hFf]
    filter_upwards [hw_mem.coeFn_toLp] with ξ hξ
    rw [hξ, ← mul_assoc, ← Complex.ofReal_mul, besselHalfWeight_mul_neg s ξ,
      Complex.ofReal_one, one_mul]
  ⟨f, hf_mem⟩

theorem fourierSobolevToL2_fromL2 {s : ℝ} (hs : 0 ≤ s) (w : L2C) :
    fourierSobolevToL2 s (fourierSobolevFromL2 hs w) = w := by
  rw [Lp.ext_iff]
  dsimp only [fourierSobolevToL2, LinearMap.coe_mk, AddHom.coe_mk]
  have hFf : (𝓕 ((fourierSobolevFromL2 hs w).toL2) : L2C) =
      (fourierSobolevFromL2_memLp hs w).toLp
        (fun ξ : ℝ => ((besselHalfWeight (-s) ξ : ℝ) : ℂ) * (w : ℝ → ℂ) ξ) :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _
  filter_upwards [(fourierSobolevFromL2 hs w).mem.coeFn_toLp,
    (fourierSobolevFromL2_memLp hs w).coeFn_toLp] with ξ h1 h2
  change ((fourierSobolevFromL2 hs w).mem.toLp _ : ℝ → ℂ) ξ = _ at h1
  rw [h1, congrArg (fun g : L2C => (g : ℝ → ℂ) ξ) hFf, h2, ← mul_assoc, ← Complex.ofReal_mul,
    besselHalfWeight_mul_neg s ξ, Complex.ofReal_one, one_mul]

/-- **Isometric Isomorphism `J_s : H^s(ℝ) ≃ₗᵢ[ℂ] L²(ℝ; ℂ)` (`thm:fracsobolevhilbert`)**:
for `s ≥ 0`, `FourierSobolevSpace s` is linearly isometrically isomorphic to `L²(ℝ; ℂ)`,
hence is a complete separable complex Hilbert space. -/
noncomputable def fourierSobolevEquivL2 {s : ℝ} (hs : 0 ≤ s) :
    FourierSobolevSpace s ≃ₗᵢ[ℂ] L2C where
  toLinearMap := fourierSobolevToL2 s
  invFun := fourierSobolevFromL2 hs
  left_inv _ := fourierSobolevToL2_injective s (fourierSobolevToL2_fromL2 hs _)
  right_inv w := fourierSobolevToL2_fromL2 hs w
  norm_map' u := (fourierSobolev_norm_eq s u).symm

/-- Completeness of `FourierSobolevSpace s` for `s ≥ 0` (`thm:fracsobolevhilbert`). -/
noncomputable instance instCompleteSpaceFourierSobolevSpace (s : ℝ) [Fact (0 ≤ s)] :
    CompleteSpace (FourierSobolevSpace s) :=
  (fourierSobolevEquivL2 Fact.out).toIsometryEquiv.completeSpace_iff.2 inferInstance

/-- Second-countability (and hence separability) of `FourierSobolevSpace s` for `s ≥ 0`
(`thm:fracsobolevhilbert`). -/
theorem secondCountableTopologyFourierSobolevSpace {s : ℝ} (hs : 0 ≤ s) :
    SecondCountableTopology (FourierSobolevSpace s) :=
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  (fourierSobolevEquivL2 hs).toHomeomorph.isEmbedding.secondCountableTopology

/-- Separability of `FourierSobolevSpace s` for `s ≥ 0` (`thm:fracsobolevhilbert`). -/
theorem separableSpaceFourierSobolevSpace {s : ℝ} (hs : 0 ≤ s) :
    TopologicalSpace.SeparableSpace (FourierSobolevSpace s) :=
  have := secondCountableTopologyFourierSobolevSpace hs
  inferInstance

/-- Helper: multiplication of `w : L2C` by `(1 + ‖ξ‖²)^(-s/2)` (`s ≥ 0`) agrees with
`smulLeftCLM ℂ ((1 + ‖ξ‖²)^(-s/2))` in `𝓢'(ℝ, ℂ)`. -/
private theorem coe_fourierSobolevFromL2_mul_eq_smulLeftCLM {s : ℝ} (hs : 0 ≤ s) (w : L2C) :
    (((fourierSobolevFromL2_memLp hs w).toLp
      (fun ξ : ℝ => ((besselHalfWeight (-s) ξ : ℝ) : ℂ) * (w : ℝ → ℂ) ξ) : L2C) :
      𝓢'(ℝ, ℂ)) =
      smulLeftCLM ℂ (fun ξ : ℝ => ((besselHalfWeight (-s) ξ : ℝ) : ℂ)) (w : 𝓢'(ℝ, ℂ)) := by
  let g : ℝ → ℂ := fun ξ => ((besselHalfWeight (-s) ξ : ℝ) : ℂ)
  have hg_tg : g.HasTemperateGrowth := by
    have h1 := Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ ((-s) / 2)
    have h2 : g = fun ξ => Complex.ofRealCLM ((1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)) := by
      ext ξ
      simp [g, besselHalfWeight, neg_div]
    rw [h2]
    exact Complex.ofRealCLM.hasTemperateGrowth.comp h1
  ext φ
  rw [MeasureTheory.Lp.toTemperedDistribution_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, MeasureTheory.Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [(fourierSobolevFromL2_memLp hs w).coeFn_toLp] with ξ hξ
  change (φ ξ : ℂ) • ((fourierSobolevFromL2_memLp hs w).toLp _ : ℝ → ℂ) ξ =
    (SchwartzMap.smulLeftCLM ℂ g φ) ξ • (w : ℝ → ℂ) ξ
  rw [hξ, SchwartzMap.smulLeftCLM_apply_apply hg_tg, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  simp only [g]
  ring

/-- **Identification with Mathlib's `TemperedDistribution.MemSobolev`**:
for `s ≥ 0` and `f ∈ L²(ℝ; ℂ)`, `f` lies in `MemSobolev s 2` iff `MemFourierSobolev s f`. -/
theorem memSobolev_two_iff_memFourierSobolev {s : ℝ} (hs : 0 ≤ s) (f : L2C) :
    MemSobolev s 2 (f : 𝓢'(ℝ, ℂ)) ↔ MemFourierSobolev s f := by
  rw [memSobolev_iff_exists_smulLeftCLM_fourier, Lp.fourier_toTemperedDistribution_eq f]
  have hneg_tg : (fun ξ : ℝ => ((besselHalfWeight (-s) ξ : ℝ) : ℂ)).HasTemperateGrowth := by
    have h1 := Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ ((-s) / 2)
    have h2 : (fun ξ : ℝ => ((besselHalfWeight (-s) ξ : ℝ) : ℂ)) =
        fun ξ => Complex.ofRealCLM ((1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)) := by
      ext ξ; simp [besselHalfWeight, neg_div]
    rw [h2]
    exact Complex.ofRealCLM.hasTemperateGrowth.comp h1
  have hpos_tg : (fun ξ : ℝ => ((besselHalfWeight s ξ : ℝ) : ℂ)).HasTemperateGrowth := by
    have h1 := Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (s / 2)
    have h2 : (fun ξ : ℝ => ((besselHalfWeight s ξ : ℝ) : ℂ)) =
        fun ξ => Complex.ofRealCLM ((1 + ‖ξ‖ ^ 2) ^ (s / 2)) := rfl
    rw [h2]
    exact Complex.ofRealCLM.hasTemperateGrowth.comp h1
  have hprod_mul : (fun x : ℝ => ((besselHalfWeight s x : ℝ) : ℂ)) *
      (fun x : ℝ => ((besselHalfWeight (-s) x : ℝ) : ℂ)) = 1 := by
    ext x
    change ((besselHalfWeight s x : ℝ) : ℂ) * ((besselHalfWeight (-s) x : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, besselHalfWeight_mul_neg s x, Complex.ofReal_one]
  have hprod_mul' : (fun x : ℝ => ((besselHalfWeight (-s) x : ℝ) : ℂ)) *
      (fun x : ℝ => ((besselHalfWeight s x : ℝ) : ℂ)) = 1 := by
    rw [mul_comm, hprod_mul]
  have hnorm_eq : (fun x : ℝ => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) =
      (fun ξ : ℝ => ((besselHalfWeight s ξ : ℝ) : ℂ)) := rfl
  simp_rw [hnorm_eq]
  have hone : (1 : ℝ → ℂ) = fun _ : ℝ => (1 : ℂ) := rfl
  constructor
  · rintro ⟨f', hf'⟩
    have hsm := congrArg (smulLeftCLM ℂ (fun ξ : ℝ => ((besselHalfWeight (-s) ξ : ℝ) : ℂ))) hf'
    rw [smulLeftCLM_smulLeftCLM_apply hpos_tg hneg_tg, hprod_mul, hone, smulLeftCLM_const,
      one_smul, ← coe_fourierSobolevFromL2_mul_eq_smulLeftCLM hs f'] at hsm
    have hinj : (𝓕 f : L2C) = (fourierSobolevFromL2_memLp hs f').toLp
        (fun ξ : ℝ => ((besselHalfWeight (-s) ξ : ℝ) : ℂ) * (f' : ℝ → ℂ) ξ) := by
      have hker := LinearMap.ker_eq_bot.mp
        (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
          (E := ℝ) (F := ℂ) (μ := (volume : Measure ℝ)) (p := 2))
      exact hker (by simpa [MeasureTheory.Lp.toTemperedDistributionCLM_apply] using hsm)
    unfold MemFourierSobolev
    refine (Lp.memLp f').ae_eq ?_
    rw [hinj]
    filter_upwards [(fourierSobolevFromL2_memLp hs f').coeFn_toLp] with ξ hξ
    rw [hξ, ← mul_assoc, ← Complex.ofReal_mul, besselHalfWeight_mul_neg s ξ,
      Complex.ofReal_one, one_mul]
  · intro hf
    have hf_mem : MemLp (fun ξ : ℝ => ((besselHalfWeight s ξ : ℝ) : ℂ) *
        ((𝓕 f : L2C) : ℝ → ℂ) ξ) 2 volume := hf
    let f' : L2C := hf_mem.toLp (fun ξ : ℝ =>
      ((besselHalfWeight s ξ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ)
    refine ⟨f', ?_⟩
    have hneg_eq : (𝓕 f : L2C) = (fourierSobolevFromL2_memLp hs f').toLp
        (fun ξ : ℝ => ((besselHalfWeight (-s) ξ : ℝ) : ℂ) * (f' : ℝ → ℂ) ξ) := by
      rw [Lp.ext_iff]
      filter_upwards [(fourierSobolevFromL2_memLp hs f').coeFn_toLp, hf_mem.coeFn_toLp]
        with ξ h1 h2
      have h2' : (f' : ℝ → ℂ) ξ =
          ((besselHalfWeight s ξ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ := h2
      rw [h1, h2', ← mul_assoc, ← Complex.ofReal_mul, mul_comm (besselHalfWeight (-s) ξ),
        besselHalfWeight_mul_neg s ξ, Complex.ofReal_one, one_mul]
    have htd : ((𝓕 f : L2C) : 𝓢'(ℝ, ℂ)) =
        smulLeftCLM ℂ (fun ξ : ℝ => ((besselHalfWeight (-s) ξ : ℝ) : ℂ)) (f' : 𝓢'(ℝ, ℂ)) := by
      calc ((𝓕 f : L2C) : 𝓢'(ℝ, ℂ))
          = ((fourierSobolevFromL2_memLp hs f').toLp
              (fun ξ : ℝ => ((besselHalfWeight (-s) ξ : ℝ) : ℂ) * (f' : ℝ → ℂ) ξ) : 𝓢'(ℝ, ℂ)) := by
            rw [hneg_eq]
        _ = smulLeftCLM ℂ (fun ξ : ℝ => ((besselHalfWeight (-s) ξ : ℝ) : ℂ)) (f' : 𝓢'(ℝ, ℂ)) :=
            coe_fourierSobolevFromL2_mul_eq_smulLeftCLM hs f'
    rw [htd, smulLeftCLM_smulLeftCLM_apply hneg_tg hpos_tg, hprod_mul', hone, smulLeftCLM_const,
      one_smul]

/-! ### 2. Sobolev equality `H^(α / 2)(ℝ) = GagliardoSpace α` (`thm:sobolev_equal`) -/

/-- Lower symbol equivalence constant relating `‖u‖_{H^(α/2)}²` and `‖u‖_{GagliardoSpace α}²`. -/
noncomputable def gagliardoLowerConst (α : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(α / 2))

/-- Upper symbol equivalence constant relating `‖u‖_{GagliardoSpace α}²` and `‖u‖_{H^(α/2)}²`. -/
noncomputable def gagliardoUpperConst (α : ℝ) : ℝ :=
  2 * (2 * Real.pi) ^ α

theorem gagliardoLowerConst_pos (α : ℝ) : 0 < gagliardoLowerConst α := by
  unfold gagliardoLowerConst; positivity

theorem gagliardoUpperConst_pos (α : ℝ) : 0 < gagliardoUpperConst α := by
  unfold gagliardoUpperConst; positivity

/-- **Two-sided Symbol Equivalence**: for `0 < α < 2` and `ξ ∈ ℝ`,
`2^(-(α/2)) * (1 + ξ²)^(α/2) ≤ 1 + |2π ξ|^α ≤ 2 (2π)^α * (1 + ξ²)^(α/2)`. -/
theorem besselSymbol_equiv_gagliardoSymbol {α : ℝ} (hα : FractionalExponent α) (ξ : ℝ) :
    gagliardoLowerConst α * (1 + ξ ^ 2) ^ (α / 2) ≤ 1 + |2 * Real.pi * ξ| ^ α ∧
      1 + |2 * Real.pi * ξ| ^ α ≤ gagliardoUpperConst α * (1 + ξ ^ 2) ^ (α / 2) := by
  have hα_half_nn : 0 ≤ α / 2 := by linarith [hα.1]
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  have hpow2 : (1 : ℝ) ≤ (2 * Real.pi) ^ α := Real.one_le_rpow hpi hα.1.le
  have hmul : |2 * Real.pi * ξ| ^ α = (2 * Real.pi) ^ α * |ξ| ^ α := by
    rw [abs_mul (2 * Real.pi) ξ, abs_of_pos (by positivity : 0 < 2 * Real.pi),
      Real.mul_rpow (by positivity) (abs_nonneg _)]
  have hle_bessel := besselSymbol_le_two_rpow_mul hα_half_nn ξ
  have hge_bessel := half_mul_le_besselSymbol hα_half_nn ξ
  rw [show 2 * (α / 2) = α by ring] at hle_bessel hge_bessel
  constructor
  · have h1 : |ξ| ^ α ≤ |2 * Real.pi * ξ| ^ α := by
      rw [hmul]
      exact le_mul_of_one_le_left (Real.rpow_nonneg (abs_nonneg _) _) hpow2
    have h2 : (1 + ξ ^ 2) ^ (α / 2) ≤ (2 : ℝ) ^ (α / 2) * (1 + |2 * Real.pi * ξ| ^ α) :=
      hle_bessel.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    have hinv : (2 : ℝ) ^ (-(α / 2)) * (2 : ℝ) ^ (α / 2) = 1 := by
      rw [← Real.rpow_add two_pos]
      simp
    unfold gagliardoLowerConst
    calc (2 : ℝ) ^ (-(α / 2)) * (1 + ξ ^ 2) ^ (α / 2)
        ≤ (2 : ℝ) ^ (-(α / 2)) * ((2 : ℝ) ^ (α / 2) * (1 + |2 * Real.pi * ξ| ^ α)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ((2 : ℝ) ^ (-(α / 2)) * (2 : ℝ) ^ (α / 2)) * (1 + |2 * Real.pi * ξ| ^ α) := by ring
      _ = 1 + |2 * Real.pi * ξ| ^ α := by rw [hinv, one_mul]
  · unfold gagliardoUpperConst
    calc 1 + |2 * Real.pi * ξ| ^ α = 1 + (2 * Real.pi) ^ α * |ξ| ^ α := by rw [hmul]
      _ ≤ (2 * Real.pi) ^ α * (1 + |ξ| ^ α) := by nlinarith
      _ = (2 * (2 * Real.pi) ^ α) * ((1 / 2 : ℝ) * (1 + |ξ| ^ α)) := by ring
      _ ≤ 2 * (2 * Real.pi) ^ α * (1 + ξ ^ 2) ^ (α / 2) :=
          mul_le_mul_of_nonneg_left hge_bessel (by positivity)

private theorem measurable_one_add_fracLapSymbol {α : ℝ} (hα : FractionalExponent α) :
    Measurable fun ξ : ℝ => ENNReal.ofReal (1 + |2 * Real.pi * ξ| ^ α) :=
  ENNReal.measurable_ofReal.comp (measurable_const.add
    ((continuous_const.mul continuous_id).abs.rpow_const
      (fun _ => Or.inr hα.1.le)).measurable)

private theorem measurable_besselSymbol_half (α : ℝ) :
    Measurable fun ξ : ℝ => ENNReal.ofReal ((1 + ξ ^ 2) ^ (α / 2)) :=
  ENNReal.measurable_ofReal.comp (by fun_prop)

private theorem lintegral_norm_sq_add_energy_eq {α : ℝ} (hα : FractionalExponent α) (f : L2C) :
    ‖f‖ₑ ^ (2 : ℝ) + gagliardoEnergyC α f =
      ∫⁻ ξ : ℝ, ENNReal.ofReal (1 + |2 * Real.pi * ξ| ^ α) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) := by
  have h1 := norm_sq_add_energy_eq α f
  have hg1 : ∀ ξ : ℝ, 1 + gagliardoSymbol α ξ = ENNReal.ofReal (1 + |2 * Real.pi * ξ| ^ α) := by
    intro ξ
    rw [gagliardoSymbol_exact hα ξ, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one (by positivity)]
  have hg2 : gagliardoSpectralMeasure α =
      volume.withDensity (fun ξ : ℝ => ENNReal.ofReal (1 + |2 * Real.pi * ξ| ^ α)) := by
    unfold gagliardoSpectralMeasure
    exact congrArg volume.withDensity (funext hg1)
  rw [hg2] at h1
  have hwd := lintegral_withDensity_eq_lintegral_mul volume
    (measurable_one_add_fracLapSymbol hα)
    (g := fun ξ : ℝ => ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ))
    ((Lp.stronglyMeasurable (𝓕 f : L2C)).measurable.eNorm.pow_const _)
  change ∫⁻ ξ : ℝ, ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ)
      ∂(volume.withDensity fun ξ => ENNReal.ofReal (1 + |2 * Real.pi * ξ| ^ α)) =
      ∫⁻ ξ : ℝ, ((fun ξ => ENNReal.ofReal (1 + |2 * Real.pi * ξ| ^ α)) *
        fun ξ => ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ)) ξ at hwd
  rw [h1, hwd]
  refine lintegral_congr fun ξ => ?_
  rfl

/-- **Sobolev Space Equality `W^(α/2, 2)(ℝ) = H^(α/2)(ℝ)` (`thm:sobolev_equal`, Complex Form)**:
for `0 < α < 2` and `f ∈ L²(ℝ; ℂ)`, finite Gagliardo energy is equivalent to membership in
`FourierSobolevSpace (α / 2)` (and hence Mathlib's `TemperedDistribution.MemSobolev (α / 2) 2`). -/
theorem gagliardoEnergyC_lt_top_iff_memFourierSobolev {α : ℝ} (hα : FractionalExponent α)
    (f : L2C) :
    gagliardoEnergyC α f < ∞ ↔ MemFourierSobolev (α / 2) f := by
  have hsum_eq := lintegral_norm_sq_add_energy_eq hα f
  have hsob_eq : ∀ g : L2C,
      (∫⁻ ξ : ℝ, ENNReal.ofReal ((1 + ξ ^ 2) ^ (α / 2)) * ‖(𝓕 g : L2C) ξ‖ₑ ^ (2 : ℝ) < ∞) ↔
        MemFourierSobolev (α / 2) g := by
    intro g
    unfold MemFourierSobolev
    have haes : AEStronglyMeasurable
        (fun ξ : ℝ => ((besselHalfWeight (α / 2) ξ : ℝ) : ℂ) * ((𝓕 g : L2C) : ℝ → ℂ) ξ)
        volume :=
      ((Complex.continuous_ofReal.measurable.comp
        (measurable_besselHalfWeight (α / 2))).mul
        (Lp.stronglyMeasurable (𝓕 g : L2C)).measurable).aestronglyMeasurable
    have hcongr : (fun ξ : ℝ =>
        ‖((besselHalfWeight (α / 2) ξ : ℝ) : ℂ) * ((𝓕 g : L2C) : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ)) =
        fun ξ : ℝ => ENNReal.ofReal ((1 + ξ ^ 2) ^ (α / 2)) * ‖(𝓕 g : L2C) ξ‖ₑ ^ (2 : ℝ) := by
      funext ξ
      rw [eNorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      congr 1
      have hbw : ‖((besselHalfWeight (α / 2) ξ : ℝ) : ℂ)‖ₑ =
          ENNReal.ofReal (besselHalfWeight (α / 2) ξ) := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (besselHalfWeight_pos (α / 2) ξ)]
      rw [hbw, ENNReal.rpow_two, ← ENNReal.ofReal_pow (besselHalfWeight_pos (α / 2) ξ).le 2]
      congr 1
      rw [besselHalfWeight_eq, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
      congr 1
      ring
    have hiff := memLp_two_iff_integrable_sq_norm haes
    constructor
    · intro hfin
      refine hiff.2 ⟨(haes.norm.pow 2), ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
      have heq : (∫⁻ ξ : ℝ, ENNReal.ofReal (‖((besselHalfWeight (α / 2) ξ : ℝ) : ℂ) *
          ((𝓕 g : L2C) : ℝ → ℂ) ξ‖ ^ 2)) =
          ∫⁻ ξ : ℝ, ENNReal.ofReal ((1 + ξ ^ 2) ^ (α / 2)) * ‖(𝓕 g : L2C) ξ‖ₑ ^ (2 : ℝ) := by
        refine lintegral_congr fun ξ => ?_
        rw [← enorm_rpow_two_eq_ofReal, congrFun hcongr ξ]
      rw [heq]
      exact hfin
    · intro hint
      have hhas := (hiff.1 hint).hasFiniteIntegral
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => sq_nonneg _)] at hhas
      have heq : (∫⁻ ξ : ℝ, ENNReal.ofReal (‖((besselHalfWeight (α / 2) ξ : ℝ) : ℂ) *
          ((𝓕 g : L2C) : ℝ → ℂ) ξ‖ ^ 2)) =
          ∫⁻ ξ : ℝ, ENNReal.ofReal ((1 + ξ ^ 2) ^ (α / 2)) * ‖(𝓕 g : L2C) ξ‖ₑ ^ (2 : ℝ) := by
        refine lintegral_congr fun ξ => ?_
        rw [← enorm_rpow_two_eq_ofReal, congrFun hcongr ξ]
      rw [← heq]
      exact hhas
  have hm_f : Measurable fun ξ : ℝ =>
      ENNReal.ofReal ((1 + ξ ^ 2) ^ (α / 2)) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) :=
    (measurable_besselSymbol_half α).mul
      ((Lp.stronglyMeasurable (𝓕 f : L2C)).measurable.eNorm.pow_const _)
  have hlt_iff :
      (∫⁻ ξ : ℝ, ENNReal.ofReal (1 + |2 * Real.pi * ξ| ^ α) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) < ∞) ↔
        (∫⁻ ξ : ℝ, ENNReal.ofReal ((1 + ξ ^ 2) ^ (α / 2)) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) < ∞) := by
    constructor
    · intro hfin
      have hmono :
          ∫⁻ ξ : ℝ, ENNReal.ofReal (gagliardoLowerConst α) *
            (ENNReal.ofReal ((1 + ξ ^ 2) ^ (α / 2)) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ)) ≤
            ∫⁻ ξ : ℝ, ENNReal.ofReal (1 + |2 * Real.pi * ξ| ^ α) *
              ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) := by
        refine lintegral_mono fun ξ => ?_
        have hl := (besselSymbol_equiv_gagliardoSymbol hα ξ).1
        rw [← mul_assoc, ← ENNReal.ofReal_mul (gagliardoLowerConst_pos α).le]
        gcongr
      rw [lintegral_const_mul _ hm_f] at hmono
      have hmul_lt := lt_of_le_of_lt hmono hfin
      have hc0 : ENNReal.ofReal (gagliardoLowerConst α) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (gagliardoLowerConst_pos α)).ne'
      by_contra! htop
      rw [top_le_iff] at htop
      rw [htop, ENNReal.mul_top hc0] at hmul_lt
      exact lt_irrefl ∞ hmul_lt
    · intro hfin
      have hmono :
          ∫⁻ ξ : ℝ, ENNReal.ofReal (1 + |2 * Real.pi * ξ| ^ α) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) ≤
            ∫⁻ ξ : ℝ, ENNReal.ofReal (gagliardoUpperConst α) *
              (ENNReal.ofReal ((1 + ξ ^ 2) ^ (α / 2)) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ)) := by
        refine lintegral_mono fun ξ => ?_
        have hu := (besselSymbol_equiv_gagliardoSymbol hα ξ).2
        rw [← mul_assoc, ← ENNReal.ofReal_mul (gagliardoUpperConst_pos α).le]
        gcongr
      rw [lintegral_const_mul _ hm_f] at hmono
      exact lt_of_le_of_lt hmono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  have hf_fin : ‖f‖ₑ ^ (2 : ℝ) < ∞ := by
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
    rw [Lp.eNorm_def]
    exact Lp.eLpNorm_ne_top f
  have he_iff : gagliardoEnergyC α f < ∞ ↔ ‖f‖ₑ ^ (2 : ℝ) + gagliardoEnergyC α f < ∞ :=
    ⟨fun hg => ENNReal.add_lt_top.2 ⟨hf_fin, hg⟩, fun hadd => (ENNReal.add_lt_top.1 hadd).2⟩
  rw [he_iff, hsum_eq, hlt_iff, hsob_eq f]

/-- **Sobolev Space Equality with Mathlib's `MemSobolev` (`thm:sobolev_equal`)**:
for `0 < α < 2` and `f ∈ L²(ℝ; ℂ)`, finite Gagliardo energy is equivalent to
`TemperedDistribution.MemSobolev (α / 2) 2 (f : 𝓢'(ℝ, ℂ))`. -/
theorem gagliardoEnergyC_lt_top_iff_memSobolev {α : ℝ} (hα : FractionalExponent α) (f : L2C) :
    gagliardoEnergyC α f < ∞ ↔ MemSobolev (α / 2) 2 (f : 𝓢'(ℝ, ℂ)) :=
  (gagliardoEnergyC_lt_top_iff_memFourierSobolev hα f).trans
    (memSobolev_two_iff_memFourierSobolev (by linarith [hα.1]) f).symm

/-- Embed a real Gagliardo function `u : GagliardoSpace α` into `FourierSobolevSpace (α / 2)`
for `0 < α < 2`. -/
noncomputable def fourierSobolevOfGagliardo {α : ℝ} (hα : FractionalExponent α)
    (u : GagliardoSpace α) : FourierSobolevSpace (α / 2) :=
  ⟨ofRealL2 (gagliardoL2Part α u), by
    rw [← gagliardoEnergyC_lt_top_iff_memFourierSobolev hα, gagliardoEnergyC_ofRealL2]
    have hu := ofReal_norm_sq_gagliardoSpace α u
    exact lt_of_le_of_lt le_add_self (hu ▸ ENNReal.ofReal_lt_top)⟩

/-- **Norm Equivalence `GagliardoSpace α ↔ H^(α / 2)(ℝ)` (`thm:sobolev_equal`)**:
for `0 < α < 2` and `u : GagliardoSpace α`,
`gagliardoLowerConst α * ‖J u‖² ≤ ‖u‖² ≤ gagliardoUpperConst α * ‖J u‖²`. -/
theorem norm_sq_gagliardoSpace_equiv_fourierSobolev {α : ℝ} (hα : FractionalExponent α)
    (u : GagliardoSpace α) :
    gagliardoLowerConst α * ‖fourierSobolevOfGagliardo hα u‖ ^ 2 ≤ ‖u‖ ^ 2 ∧
      ‖u‖ ^ 2 ≤ gagliardoUpperConst α * ‖fourierSobolevOfGagliardo hα u‖ ^ 2 := by
  let f : L2C := ofRealL2 (gagliardoL2Part α u)
  have hf_mem := (fourierSobolevOfGagliardo hα u).mem
  have hnorm_ofReal : ‖f‖ = ‖gagliardoL2Part α u‖ := by
    have h1 : ‖f‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖gagliardoL2Part α u‖ ^ 2) := by
      have hf_eq := enorm_sq_ofRealL2 (gagliardoL2Part α u)
      change ‖f‖ₑ ^ (2 : ℝ) = ‖gagliardoL2Part α u‖ₑ ^ (2 : ℝ) at hf_eq
      rw [hf_eq, ← enorm_rpow_two_eq_ofReal]
    have h2 : ENNReal.ofReal (‖f‖ ^ 2) = ENNReal.ofReal (‖gagliardoL2Part α u‖ ^ 2) := by
      rw [← enorm_rpow_two_eq_ofReal f, h1]
    have hsq := (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg ‖f‖)
      (sq_nonneg (‖gagliardoL2Part α u‖))).1 h2
    have hrt := congrArg Real.sqrt hsq
    simpa only [Real.sqrt_sq (norm_nonneg _)] using hrt
  have hLHS_enn :
      ENNReal.ofReal (‖u‖ ^ 2) =
        ∫⁻ ξ : ℝ, ENNReal.ofReal (1 + |2 * Real.pi * ξ| ^ α) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) := by
    rw [ofReal_norm_sq_gagliardoSpace α u, ← gagliardoEnergyC_ofRealL2, ← hnorm_ofReal,
      ← enorm_rpow_two_eq_ofReal f]
    exact lintegral_norm_sq_add_energy_eq hα f
  have hRHS_enn :
      ENNReal.ofReal (‖fourierSobolevOfGagliardo hα u‖ ^ 2) =
        ∫⁻ ξ : ℝ, ENNReal.ofReal ((1 + ξ ^ 2) ^ (α / 2)) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) := by
    have hsq := fourierSobolev_norm_sq_eq (α / 2) (fourierSobolevOfGagliardo hα u)
    change ‖fourierSobolevOfGagliardo hα u‖ ^ 2 =
      ∫ ξ : ℝ, (1 + ξ ^ 2) ^ (α / 2) * ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2 at hsq
    have hm : MemLp (fun ξ : ℝ => ((besselHalfWeight (α / 2) ξ : ℝ) : ℂ) *
        ((𝓕 f : L2C) : ℝ → ℂ) ξ) 2 volume := hf_mem
    have haes : AEStronglyMeasurable (fun ξ : ℝ => ((besselHalfWeight (α / 2) ξ : ℝ) : ℂ) *
        ((𝓕 f : L2C) : ℝ → ℂ) ξ) volume := hm.aestronglyMeasurable
    have hint : Integrable (fun ξ : ℝ => (1 + ξ ^ 2) ^ (α / 2) * ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2)
        volume := by
      have hsq_mem := (memLp_two_iff_integrable_sq_norm haes).mp hm
      refine hsq_mem.congr (Filter.Eventually.of_forall fun ξ => ?_)
      dsimp only
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (besselHalfWeight_pos (α / 2) ξ), mul_pow]
      congr 1
      rw [besselHalfWeight_eq, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast; ring
    have hnn : ∀ ξ : ℝ, 0 ≤ (1 + ξ ^ 2) ^ (α / 2) * ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2 :=
      fun ξ => by positivity
    rw [hsq, ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
    refine lintegral_congr fun ξ => ?_
    rw [ENNReal.ofReal_mul (by positivity), ← enorm_rpow_two_eq_ofReal]
  have hm_f : Measurable fun ξ : ℝ =>
      ENNReal.ofReal ((1 + ξ ^ 2) ^ (α / 2)) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) :=
    (measurable_besselSymbol_half α).mul
      ((Lp.stronglyMeasurable (𝓕 f : L2C)).measurable.eNorm.pow_const _)
  constructor
  · have hmono :
        ENNReal.ofReal (gagliardoLowerConst α * ‖fourierSobolevOfGagliardo hα u‖ ^ 2) ≤
          ENNReal.ofReal (‖u‖ ^ 2) := by
      rw [ENNReal.ofReal_mul (gagliardoLowerConst_pos α).le, hRHS_enn, hLHS_enn,
        ← lintegral_const_mul _ hm_f]
      refine lintegral_mono fun ξ => ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul (gagliardoLowerConst_pos α).le]
      gcongr
      exact (besselSymbol_equiv_gagliardoSymbol hα ξ).1
    exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 hmono
  · have hmono :
        ENNReal.ofReal (‖u‖ ^ 2) ≤
          ENNReal.ofReal (gagliardoUpperConst α * ‖fourierSobolevOfGagliardo hα u‖ ^ 2) := by
      rw [ENNReal.ofReal_mul (gagliardoUpperConst_pos α).le, hLHS_enn, hRHS_enn,
        ← lintegral_const_mul _ hm_f]
      refine lintegral_mono fun ξ => ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul (gagliardoUpperConst_pos α).le]
      gcongr
      exact (besselSymbol_equiv_gagliardoSymbol hα ξ).2
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (gagliardoUpperConst_pos α).le (sq_nonneg _))).1
      hmono

/-! ### 3. Self-adjointness and nonnegativity of `fracLapSemigroup` (`prop:selfadjoint`) -/

/-- **Parseval Formula for the `fracLapSemigroup` Generator (`prop:selfadjoint`)**:
for `u ∈ D(A_α)` and `v ∈ L²(ℝ; ℂ)`,
`⟪-A_α u, v⟫ = ∫ ξ, |2π ξ|^α ⟪𝓕 u(ξ), 𝓕 v(ξ)⟫ dξ`. -/
theorem inner_neg_generator_fracLapSemigroup_eq (α : ℝ)
    (u : (fracLapSemigroup α).generatorDomain) (v : L2C) :
    @inner ℂ L2C _ (-((fracLapSemigroup α).generator u)) v =
      ∫ ξ : ℝ, ((fracLapSymbol α ξ : ℝ) : ℂ) *
        @inner ℂ ℂ _ (((𝓕 (u : L2C) : L2C) : ℝ → ℂ) ξ) (((𝓕 v : L2C) : ℝ → ℂ) ξ) := by
  have hmem := (fracLapSemigroup_mem_generatorDomain_iff α (u : L2C)).mp u.2
  rw [generator_fracLapSemigroup_of_memLp α u.2 hmem, neg_neg,
    ← parseval_inner_eq _ v]
  rw [show 𝓕 (𝓕⁻ (hmem.toLp (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) *
      ((𝓕 (u : L2C) : L2C) : ℝ → ℂ) ξ))) =
      hmem.toLp (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) *
      ((𝓕 (u : L2C) : L2C) : ℝ → ℂ) ξ) from (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _,
    MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hmem.coeFn_toLp] with ξ hξ
  change @inner ℂ ℂ _ ((hmem.toLp _ : ℝ → ℂ) ξ) ((𝓕 v : L2C) ξ) = _
  rw [hξ, RCLike.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_mul',
    Complex.star_def, Complex.conj_ofReal]
  ring

/-- **Symmetry of `-A_α` (`prop:selfadjoint`)**:
for all `u, v ∈ D(A_α)`, `⟪-A_α u, v⟫ = ⟪u, -A_α v⟫`. -/
theorem inner_neg_generator_fracLapSemigroup_symm (α : ℝ)
    (u v : (fracLapSemigroup α).generatorDomain) :
    @inner ℂ L2C _ (-((fracLapSemigroup α).generator u)) (v : L2C) =
      @inner ℂ L2C _ (u : L2C) (-((fracLapSemigroup α).generator v)) := by
  have h1 := inner_neg_generator_fracLapSemigroup_eq α u (v : L2C)
  have h2 := inner_neg_generator_fracLapSemigroup_eq α v (u : L2C)
  conv_rhs => rw [← inner_conj_symm]
  rw [h2, ← integral_conj, h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [map_mul, Complex.conj_ofReal, inner_conj_symm]

/-- **Nonnegativity of `-A_α` (`prop:selfadjoint`)**:
for every `u ∈ D(A_α)`, `⟪-A_α u, u⟫` has zero imaginary part and nonnegative real part. -/
theorem inner_neg_generator_fracLapSemigroup_re_nonneg (α : ℝ)
    (u : (fracLapSemigroup α).generatorDomain) :
    0 ≤ (@inner ℂ L2C _ (-((fracLapSemigroup α).generator u)) (u : L2C)).re ∧
      (@inner ℂ L2C _ (-((fracLapSemigroup α).generator u)) (u : L2C)).im = 0 := by
  rw [inner_neg_generator_fracLapSemigroup_eq]
  have hpt : ∀ ξ : ℝ,
      ((fracLapSymbol α ξ : ℝ) : ℂ) *
        @inner ℂ ℂ _ (((𝓕 (u : L2C) : L2C) : ℝ → ℂ) ξ) (((𝓕 (u : L2C) : L2C) : ℝ → ℂ) ξ) =
      ((fracLapSymbol α ξ * ‖((𝓕 (u : L2C) : L2C) : ℝ → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) := by
    intro ξ
    rw [inner_self_eq_norm_sq_to_K]
    apply Complex.ext <;> simp
  simp_rw [hpt]
  rw [integral_complex_ofReal, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨integral_nonneg fun ξ => ?_, rfl⟩
  unfold fracLapSymbol
  positivity

/-- **Self-adjointness of `-A_α` (`prop:selfadjoint`)**:
if `y, w ∈ L²(ℝ; ℂ)` satisfy `⟪y, -A_α u⟫ = ⟪w, u⟫` for all `u ∈ D(A_α)`,
then `y ∈ D(A_α)` and `-A_α y = w`. -/
theorem fracLapSemigroup_selfAdjoint (α : ℝ) {y w : L2C}
    (h : ∀ u : (fracLapSemigroup α).generatorDomain,
      @inner ℂ L2C _ y (-((fracLapSemigroup α).generator u)) = @inner ℂ L2C _ w (u : L2C)) :
    ∃ hy : y ∈ (fracLapSemigroup α).generatorDomain,
      -((fracLapSemigroup α).generator ⟨y, hy⟩) = w := by
  let invSym : ℝ → ℝ := fun ξ => (1 + fracLapSymbol α ξ)⁻¹
  have hinv_meas : Measurable invSym := by
    unfold invSym fracLapSymbol
    fun_prop
  have hinv_bd : ∀ ξ : ℝ, |invSym ξ| ≤ 1 := fun ξ => by
    have hnn : 0 ≤ fracLapSymbol α ξ := by unfold fracLapSymbol; positivity
    have hpos : 0 < 1 + fracLapSymbol α ξ := by linarith
    rw [abs_of_pos (inv_pos.mpr hpos)]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hFy : MemLp (fun ξ : ℝ => ((invSym ξ : ℝ) : ℂ) * ((𝓕 (y + w) : L2C) : ℝ → ℂ) ξ)
      2 volume := by
    have hbase := (Lp.memLp (𝓕 (y + w) : L2C)).norm
    refine MemLp.mono' hbase ?_ ?_
    · exact ((Complex.continuous_ofReal.measurable.comp hinv_meas).mul
        (Lp.stronglyMeasurable _).measurable).aestronglyMeasurable
    · filter_upwards with ξ
      rw [norm_mul, Complex.norm_real]
      exact mul_le_of_le_one_left (norm_nonneg _) (hinv_bd ξ)
  let z : L2C := 𝓕⁻ (hFy.toLp _)
  have hz_mem_sym : MemLp (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) *
      ((𝓕 z : L2C) : ℝ → ℂ) ξ) 2 volume := by
    have hFz : (𝓕 z : L2C) = hFy.toLp _ := (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _
    rw [hFz]
    have hbase := (Lp.memLp (𝓕 (y + w) : L2C)).norm
    have hmono : MemLp (fun ξ : ℝ =>
        ((fracLapSymbol α ξ * invSym ξ : ℝ) : ℂ) * ((𝓕 (y + w) : L2C) : ℝ → ℂ) ξ) 2 volume := by
      refine MemLp.mono' hbase ?_ ?_
      · refine ((Complex.continuous_ofReal.measurable.comp ?_).mul
          (Lp.stronglyMeasurable _).measurable).aestronglyMeasurable
        have hmeas_sym : Measurable (fracLapSymbol α) := by unfold fracLapSymbol; fun_prop
        exact hmeas_sym.mul hinv_meas
      · filter_upwards with ξ
        rw [norm_mul, Complex.norm_real]
        have hnn : 0 ≤ fracLapSymbol α ξ := by unfold fracLapSymbol; positivity
        have hpos : 0 < 1 + fracLapSymbol α ξ := by linarith
        have hle : |fracLapSymbol α ξ * invSym ξ| ≤ 1 := by
          unfold invSym
          rw [abs_of_nonneg (mul_nonneg hnn (inv_nonneg.mpr hpos.le)), mul_inv_le_iff₀ hpos]
          linarith
        exact mul_le_of_le_one_left (norm_nonneg _) hle
    refine hmono.ae_eq ?_
    filter_upwards [hFy.coeFn_toLp] with ξ hξ
    rw [hξ, Complex.ofReal_mul, mul_assoc]
  have hz_dom : z ∈ (fracLapSemigroup α).generatorDomain :=
    (fracLapSemigroup_mem_generatorDomain_iff α z).mpr hz_mem_sym
  have hz_eq : z - (fracLapSemigroup α).generator ⟨z, hz_dom⟩ = y + w := by
    rw [generator_fracLapSemigroup_of_memLp α hz_dom hz_mem_sym, sub_neg_eq_add]
    apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
    have hF_add := (Lp.fourierTransformₗᵢ ℝ ℂ).map_add z
      (𝓕⁻ (hz_mem_sym.toLp (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) *
        ((𝓕 z : L2C) : ℝ → ℂ) ξ)))
    change (Lp.fourierTransformₗᵢ ℝ ℂ)
        (z + 𝓕⁻ (hz_mem_sym.toLp (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) *
          ((𝓕 z : L2C) : ℝ → ℂ) ξ))) =
      (Lp.fourierTransformₗᵢ ℝ ℂ) (y + w)
    rw [hF_add, show (Lp.fourierTransformₗᵢ ℝ ℂ) z = (𝓕 z : L2C) from rfl,
      show (Lp.fourierTransformₗᵢ ℝ ℂ) (𝓕⁻ (hz_mem_sym.toLp (fun ξ : ℝ =>
        ((fracLapSymbol α ξ : ℝ) : ℂ) * ((𝓕 z : L2C) : ℝ → ℂ) ξ))) =
        hz_mem_sym.toLp (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) *
          ((𝓕 z : L2C) : ℝ → ℂ) ξ) from (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _,
      Lp.ext_iff]
    filter_upwards [Lp.coeFn_add (𝓕 z : L2C) (hz_mem_sym.toLp _),
      hFy.coeFn_toLp, hz_mem_sym.coeFn_toLp] with ξ hadd h1 h2
    have h1' : (hFy.toLp _ : ℝ → ℂ) ξ = ((invSym ξ : ℝ) : ℂ) * ((𝓕 (y + w) : L2C) : ℝ → ℂ) ξ :=
      h1
    have h2' : (hz_mem_sym.toLp _ : ℝ → ℂ) ξ =
        ((fracLapSymbol α ξ : ℝ) : ℂ) * ((𝓕 z : L2C) : ℝ → ℂ) ξ := h2
    have hFz_ξ : ((𝓕 z : L2C) : ℝ → ℂ) ξ = (hFy.toLp _ : ℝ → ℂ) ξ := by
      rw [show (𝓕 z : L2C) = hFy.toLp _ from (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _]
    have hadd' : ((𝓕 z + hz_mem_sym.toLp (fun ξ => ((fracLapSymbol α ξ : ℝ) : ℂ) *
        ((𝓕 z : L2C) : ℝ → ℂ) ξ) : L2C) : ℝ → ℂ) ξ =
        ((𝓕 z : L2C) : ℝ → ℂ) ξ + (hz_mem_sym.toLp _ : ℝ → ℂ) ξ := hadd
    rw [hadd', h2', hFz_ξ, h1']
    have hpos : (1 + fracLapSymbol α ξ : ℝ) ≠ 0 := by
      have hnn : 0 ≤ fracLapSymbol α ξ := by unfold fracLapSymbol; positivity
      linarith
    have hsum : ((invSym ξ : ℝ) : ℂ) + ((fracLapSymbol α ξ : ℝ) : ℂ) * ((invSym ξ : ℝ) : ℂ) =
        1 := by
      unfold invSym
      norm_cast
      field_simp
    calc ((invSym ξ : ℝ) : ℂ) * ((𝓕 (y + w) : L2C) : ℝ → ℂ) ξ +
          ((fracLapSymbol α ξ : ℝ) : ℂ) * (((invSym ξ : ℝ) : ℂ) * ((𝓕 (y + w) : L2C) : ℝ → ℂ) ξ)
        = (((invSym ξ : ℝ) : ℂ) + ((fracLapSymbol α ξ : ℝ) : ℂ) * ((invSym ξ : ℝ) : ℂ)) *
            ((𝓕 (y + w) : L2C) : ℝ → ℂ) ξ := by ring
      _ = ((𝓕 (y + w) : L2C) : ℝ → ℂ) ξ := by rw [hsum, one_mul]
  have hy_z : ∀ u : (fracLapSemigroup α).generatorDomain,
      @inner ℂ L2C _ (y - z) ((u : L2C) - (fracLapSemigroup α).generator u) = 0 := by
    intro u
    rw [inner_sub_left]
    have hzw : @inner ℂ L2C _ z ((u : L2C) - (fracLapSemigroup α).generator u) =
        @inner ℂ L2C _ (z - (fracLapSemigroup α).generator ⟨z, hz_dom⟩) (u : L2C) := by
      rw [inner_sub_right, inner_sub_left]
      have hsy := inner_neg_generator_fracLapSemigroup_symm α ⟨z, hz_dom⟩ u
      rw [inner_neg_right, inner_neg_left] at hsy
      rw [neg_inj.mp hsy]
    rw [sub_eq_add_neg (u : L2C) ((fracLapSemigroup α).generator u)] at hzw ⊢
    rw [inner_add_right, h u, hzw, hz_eq, inner_add_left]
    ring
  have hrange : ∀ d : L2C, ∃ u : (fracLapSemigroup α).generatorDomain,
      (u : L2C) - (fracLapSemigroup α).generator u = d := by
    intro d
    let μ : PositiveShift := ⟨1, one_pos⟩
    refine ⟨⟨(fracLapSemigroup α).resolvent μ d,
      (fracLapSemigroup α).resolvent_mem_generatorDomain μ d⟩, ?_⟩
    have hid := (fracLapSemigroup α).generator_resolvent μ d
    change (fracLapSemigroup α).generator ⟨(fracLapSemigroup α).resolvent μ d, _⟩ =
      ((1 : ℝ) • ((fracLapSemigroup α).resolvent μ d) - d) at hid
    rw [one_smul] at hid
    rw [hid]
    abel
  obtain ⟨u0, hu0⟩ := hrange (y - z)
  have hself := hy_z u0
  rw [hu0] at hself
  have hyz : y = z := sub_eq_zero.mp (inner_self_eq_zero.mp hself)
  refine ⟨hyz ▸ hz_dom, ?_⟩
  have h1 : (y : L2C) - (fracLapSemigroup α).generator ⟨y, hyz ▸ hz_dom⟩ = y + w := by
    simpa [hyz] using hz_eq
  have h2 : -((fracLapSemigroup α).generator ⟨y, hyz ▸ hz_dom⟩) = w := by
    have h3 := congrArg (fun x : L2C => x - y) h1
    simpa [sub_eq_add_neg, add_assoc] using h3
  exact h2

/-! ### 4. Density of `H^(α/2)(ℝ)` & whole-line Friedrichs equivalence (`prop:fracform`) -/

/-- **Dense Domain of `B^α` (`prop:fracform`)**:
for `0 < α < 2`, `gagliardoL2Part α : GagliardoSpace α → L²(ℝ; ℝ)` has dense range. -/
theorem denseRange_gagliardoL2Part {α : ℝ} (hα : FractionalExponent α) :
    DenseRange (gagliardoL2Part α) := by
  rw [Metric.denseRange_iff]
  intro g ε hε
  obtain ⟨φc, hφc⟩ := Metric.denseRange_iff.1
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top)
    (ofRealL2 g) ε hε
  let φ : 𝓢(ℝ, ℝ) := SchwartzMap.postcompCLM Complex.reCLM φc
  have hφ_L2 : (φ.toLp 2 volume : L2R) = reL2 (φc.toLp 2 volume : L2C) := by
    rw [Lp.ext_iff]
    filter_upwards [φ.coeFn_toLp 2 volume, coeFn_reL2 (φc.toLp 2 volume : L2C),
      φc.coeFn_toLp 2 volume] with x h1 h2 h3
    have h1' : (φ.toLp 2 volume : L2R) x = φ x := h1
    have h3' : ((φc.toLp 2 volume : L2C) : ℝ → ℂ) x = φc x := h3
    rw [h1', h2, h3']
    simp [φ]
  have hE : gagliardoEnergyR α (φ.toLp 2 volume : L2R) < ∞ := by
    rw [hφ_L2]
    exact lt_of_le_of_lt (gagliardoEnergyR_reL2_le α _) (gagliardoEnergyC_schwartz_lt_top hα φc)
  refine ⟨gagliardoMk (φ.toLp 2 volume : L2R) hE, ?_⟩
  rw [dist_comm, gagliardoL2Part_mk, dist_eq_norm, hφ_L2,
    show reL2 (φc.toLp 2 volume : L2C) - g =
      reL2 ((φc.toLp 2 volume : L2C) - ofRealL2 g) from by rw [map_sub, reL2_ofRealL2]]
  have hre_le : ‖reL2 ((φc.toLp 2 volume : L2C) - ofRealL2 g)‖ ≤
      ‖(φc.toLp 2 volume : L2C) - ofRealL2 g‖ := by
    have hsq := enorm_sq_reL2_le ((φc.toLp 2 volume : L2C) - ofRealL2 g)
    have hr := ENNReal.rpow_le_rpow hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simp only [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one] at hr
    simpa only [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)] using hr
  rw [dist_eq_norm, norm_sub_rev] at hφc
  exact lt_of_le_of_lt hre_le hφc

/-- Continuity of the Gagliardo Dirichlet form `gagliardoForm α` on `GagliardoSpace α`
(`prop:fracform`). -/
theorem gagliardoForm_continuous (α : ℝ) (u v : GagliardoSpace α) :
    |(gagliardoForm α).form u v| ≤ ‖u‖ * ‖v‖ := by
  have hle : ∀ w : GagliardoSpace α, (gagliardoForm α).form w w ≤ ‖w‖ ^ 2 := fun w => by
    rw [norm_sq_gagliardoSpace α w]
    change @inner ℝ (L2Gagliardo α) _ (gagliardoDiffPart α w) (gagliardoDiffPart α w) ≤
      ‖gagliardoL2Part α w‖ ^ 2 + ‖gagliardoDiffPart α w‖ ^ 2
    rw [real_inner_self_eq_norm_sq]
    linarith [sq_nonneg ‖gagliardoL2Part α w‖]
  have hcs_sq : |(gagliardoForm α).form u v| ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    calc |(gagliardoForm α).form u v| ^ 2
        = ((gagliardoForm α).form u v) ^ 2 := sq_abs _
      _ ≤ (gagliardoForm α).form u u * (gagliardoForm α).form v v :=
          (gagliardoForm α).cauchy_schwarz_sq u v
      _ ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 :=
          mul_le_mul (hle u) (hle v) ((gagliardoForm α).accretive v) (sq_nonneg _)
      _ = (‖u‖ * ‖v‖) ^ 2 := by ring
  exact le_of_sq_le_sq hcs_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- **Diagonal Weak-Form Identity on Whole Line**: for `0 < α < 2` and `u : GagliardoSpace α` with
`ofRealL2 (gagliardoL2Part α u) ∈ D(A_α)`,
`B^α(u, u) = Re ⟪-A_α (ofRealL2 u), ofRealL2 u⟫`. -/
private theorem gagliardoForm_self_eq_inner_neg_generator {α : ℝ} (hα : FractionalExponent α)
    (u : GagliardoSpace α)
    (hu : ofRealL2 (gagliardoL2Part α u) ∈ (fracLapSemigroup α).generatorDomain) :
    (gagliardoForm α).form u u =
      (@inner ℂ L2C _ (-((fracLapSemigroup α).generator ⟨ofRealL2 (gagliardoL2Part α u), hu⟩))
        (ofRealL2 (gagliardoL2Part α u))).re := by
  let f : L2C := ofRealL2 (gagliardoL2Part α u)
  have hleft : ENNReal.ofReal ((gagliardoForm α).form u u) =
      ∫⁻ ξ : ℝ, ENNReal.ofReal (fracLapSymbol α ξ) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) := by
    have hnorm := ofReal_norm_sq_gagliardoSpace α u
    rw [norm_sq_gagliardoSpace α u, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)] at hnorm
    have hadd_cancel :
        ENNReal.ofReal (‖gagliardoDiffPart α u‖ ^ 2) = gagliardoEnergyR α (gagliardoL2Part α u) :=
      (ENNReal.add_right_inj ENNReal.ofReal_ne_top).mp hnorm
    have hdiff_eq : (gagliardoForm α).form u u = ‖gagliardoDiffPart α u‖ ^ 2 := by
      change ⟪gagliardoDiffPart α u, gagliardoDiffPart α u⟫_ℝ = _
      exact real_inner_self_eq_norm_sq _
    rw [hdiff_eq, hadd_cancel, ← gagliardoEnergyC_ofRealL2]
    exact gagliardoEnergyC_eq_lintegral hα f
  have hright_eq :
      (@inner ℂ L2C _ (-((fracLapSemigroup α).generator ⟨f, hu⟩)) f).re =
        ∫ ξ : ℝ, fracLapSymbol α ξ * ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2 := by
    rw [inner_neg_generator_fracLapSemigroup_eq]
    have hpt : ∀ ξ : ℝ,
        ((fracLapSymbol α ξ : ℝ) : ℂ) *
          @inner ℂ ℂ _ (((𝓕 f : L2C) : ℝ → ℂ) ξ) (((𝓕 f : L2C) : ℝ → ℂ) ξ) =
        ((fracLapSymbol α ξ * ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) := by
      intro ξ
      rw [inner_self_eq_norm_sq_to_K]
      apply Complex.ext <;> simp [Complex.ofReal_pow]
    simp_rw [hpt]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  have hint : Integrable (fun ξ : ℝ => fracLapSymbol α ξ * ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2)
      volume := by
    have hmem := (fracLapSemigroup_mem_generatorDomain_iff α f).mp hu
    have hi := Complex.reCLM.integrable_comp (MeasureTheory.L2.integrable_inner (hmem.toLp _) (𝓕 f))
    refine hi.congr ?_
    filter_upwards [hmem.coeFn_toLp] with ξ hξ
    change (Complex.reCLM (@inner ℂ ℂ _ ((hmem.toLp _ : ℝ → ℂ) ξ) ((𝓕 f : L2C) ξ))) = _
    rw [Complex.reCLM_apply, hξ, RCLike.inner_apply, starRingEnd_apply, star_mul',
      Complex.star_def, Complex.conj_ofReal]
    have hm1 : ((𝓕 f : L2C) ξ) * (((fracLapSymbol α ξ : ℝ) : ℂ) *
        starRingEnd ℂ (((𝓕 f : L2C) : ℝ → ℂ) ξ)) =
        ((fracLapSymbol α ξ : ℝ) : ℂ) *
          @inner ℂ ℂ _ (((𝓕 f : L2C) : ℝ → ℂ) ξ) (((𝓕 f : L2C) : ℝ → ℂ) ξ) := by
      rw [RCLike.inner_apply, starRingEnd_apply]
      ring
    have hpt' : ((fracLapSymbol α ξ : ℝ) : ℂ) *
        @inner ℂ ℂ _ (((𝓕 f : L2C) : ℝ → ℂ) ξ) (((𝓕 f : L2C) : ℝ → ℂ) ξ) =
        ((fracLapSymbol α ξ * ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      apply Complex.ext <;> simp [Complex.ofReal_pow]
    rw [hm1, hpt', Complex.ofReal_re]
  have hright_enn :
      ENNReal.ofReal ((@inner ℂ L2C _ (-((fracLapSemigroup α).generator ⟨f, hu⟩)) f).re) =
        ∫⁻ ξ : ℝ, ENNReal.ofReal (fracLapSymbol α ξ) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) := by
    rw [hright_eq, ofReal_integral_eq_lintegral_ofReal hint]
    · refine lintegral_congr fun ξ => ?_
      rw [ENNReal.ofReal_mul (by unfold fracLapSymbol; positivity), ← enorm_rpow_two_eq_ofReal]
    · filter_upwards with ξ
      unfold fracLapSymbol
      positivity
  have heq := hleft.trans hright_enn.symm
  have hr := congrArg ENNReal.toReal heq
  rw [ENNReal.toReal_ofReal ((gagliardoForm α).accretive u),
    ENNReal.toReal_ofReal (inner_neg_generator_fracLapSemigroup_re_nonneg α ⟨f, hu⟩).1] at hr
  exact hr

/-- **Whole-Line Friedrichs Weak-Form Identity (`prop:fracform`)**:
for `0 < α < 2` and `u, v : GagliardoSpace α` with `ofRealL2 u_{L2} ∈ D(A_α)` and
`ofRealL2 v_{L2} ∈ D(A_α)`, `B^α(u, v) = Re ⟪-A_α (ofRealL2 u), ofRealL2 v⟫`. -/
theorem gagliardoForm_eq_inner_neg_generator {α : ℝ} (hα : FractionalExponent α)
    (u v : GagliardoSpace α)
    (hu : ofRealL2 (gagliardoL2Part α u) ∈ (fracLapSemigroup α).generatorDomain)
    (hv : ofRealL2 (gagliardoL2Part α v) ∈ (fracLapSemigroup α).generatorDomain) :
    (gagliardoForm α).form u v =
      (@inner ℂ L2C _ (-((fracLapSemigroup α).generator ⟨ofRealL2 (gagliardoL2Part α u), hu⟩))
        (ofRealL2 (gagliardoL2Part α v))).re := by
  have hadd : ofRealL2 (gagliardoL2Part α (u + v)) ∈ (fracLapSemigroup α).generatorDomain := by
    rw [map_add, map_add]
    exact (fracLapSemigroup α).generatorDomain.add_mem hu hv
  have hsub : ofRealL2 (gagliardoL2Part α (u - v)) ∈ (fracLapSemigroup α).generatorDomain := by
    rw [map_sub, map_sub]
    exact (fracLapSemigroup α).generatorDomain.sub_mem hu hv
  have hd_add := gagliardoForm_self_eq_inner_neg_generator hα (u + v) hadd
  have hd_sub := gagliardoForm_self_eq_inner_neg_generator hα (u - v) hsub
  have hF_pol : 4 * (gagliardoForm α).form u v =
      (gagliardoForm α).form (u + v) (u + v) - (gagliardoForm α).form (u - v) (u - v) := by
    change 4 * ⟪gagliardoDiffPart α u, gagliardoDiffPart α v⟫_ℝ =
      ⟪gagliardoDiffPart α (u + v), gagliardoDiffPart α (u + v)⟫_ℝ -
      ⟪gagliardoDiffPart α (u - v), gagliardoDiffPart α (u - v)⟫_ℝ
    simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
    rw [real_inner_comm (gagliardoDiffPart α v) (gagliardoDiffPart α u)]
    ring
  have hG_pol :
      4 * (@inner ℂ L2C _
          (-((fracLapSemigroup α).generator ⟨ofRealL2 (gagliardoL2Part α u), hu⟩))
          (ofRealL2 (gagliardoL2Part α v))).re =
        (@inner ℂ L2C _
          (-((fracLapSemigroup α).generator ⟨ofRealL2 (gagliardoL2Part α (u + v)), hadd⟩))
          (ofRealL2 (gagliardoL2Part α (u + v)))).re -
        (@inner ℂ L2C _
          (-((fracLapSemigroup α).generator ⟨ofRealL2 (gagliardoL2Part α (u - v)), hsub⟩))
          (ofRealL2 (gagliardoL2Part α (u - v)))).re := by
    let Au : L2C := -((fracLapSemigroup α).generator ⟨ofRealL2 (gagliardoL2Part α u), hu⟩)
    let Av : L2C := -((fracLapSemigroup α).generator ⟨ofRealL2 (gagliardoL2Part α v), hv⟩)
    let fu : L2C := ofRealL2 (gagliardoL2Part α u)
    let fv : L2C := ofRealL2 (gagliardoL2Part α v)
    let g₁ : (fracLapSemigroup α).generatorDomain :=
      ⟨ofRealL2 (gagliardoL2Part α (u + v)), hadd⟩
    let g₂ : (fracLapSemigroup α).generatorDomain :=
      ⟨ofRealL2 (gagliardoL2Part α (u - v)), hsub⟩
    have hA_add : -((fracLapSemigroup α).generator g₁) = Au + Av := by
      have hgen_add : (fracLapSemigroup α).generator g₁ =
          (fracLapSemigroup α).generator ⟨fu, hu⟩ + (fracLapSemigroup α).generator ⟨fv, hv⟩ := by
        have hdom_eq : g₁ = ⟨fu, hu⟩ + ⟨fv, hv⟩ := by ext1; simp [g₁, fu, fv, map_add]
        rw [hdom_eq, map_add]
      rw [hgen_add, neg_add]
    have hA_sub : -((fracLapSemigroup α).generator g₂) = Au - Av := by
      have hgen_sub : (fracLapSemigroup α).generator g₂ =
          (fracLapSemigroup α).generator ⟨fu, hu⟩ - (fracLapSemigroup α).generator ⟨fv, hv⟩ := by
        have hdom_eq : g₂ = ⟨fu, hu⟩ - ⟨fv, hv⟩ := by ext1; simp [g₂, fu, fv, map_sub]
        rw [hdom_eq, map_sub]
      rw [hgen_sub]
      simp only [Au, Av, fu, fv, sub_eq_add_neg, neg_add, neg_neg]
    have hsymm_re : (@inner ℂ L2C _ Av fu).re = (@inner ℂ L2C _ Au fv).re := by
      have hs := inner_neg_generator_fracLapSemigroup_symm α ⟨fu, hu⟩ ⟨fv, hv⟩
      have hs' : @inner ℂ L2C _ Au fv = @inner ℂ L2C _ fu Av := hs
      rw [hs', ← inner_conj_symm Av fu, Complex.conj_re]
    have hf_add : ofRealL2 (gagliardoL2Part α (u + v)) = fu + fv := by simp [fu, fv, map_add]
    have hf_sub : ofRealL2 (gagliardoL2Part α (u - v)) = fu - fv := by simp [fu, fv, map_sub]
    rw [hA_add, hA_sub, hf_add, hf_sub]
    change 4 * (@inner ℂ L2C _ Au fv).re =
      (@inner ℂ L2C _ (Au + Av) (fu + fv)).re - (@inner ℂ L2C _ (Au - Av) (fu - fv)).re
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      Complex.add_re, Complex.sub_re, hsymm_re]
    ring
  linarith

/-! ### 5. Closedness and density of `L²_0(ℝ)` and `H^(α/2)_0(ℝ)` (`prop:zerospaces`) -/

/-- Closed linear subspace `L²_0(ℝ) ⊆ L²(ℝ; ℝ)` of functions vanishing a.e. on `(-∞, 0]`. -/
noncomputable def l2ZeroSubmodule : Submodule ℝ L2R where
  carrier := {u | ∀ᵐ x : ℝ ∂volume, x ≤ 0 → (u : ℝ → ℝ) x = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℝ 2 volume] with x hx _
    exact hx
  add_mem' := by
    intro u v hu hv
    filter_upwards [hu, hv, Lp.coeFn_add u v] with x hux hvx hadd hx
    rw [hadd, Pi.add_apply, hux hx, hvx hx, add_zero]
  smul_mem' := by
    intro c u hu
    filter_upwards [hu, Lp.coeFn_smul c u] with x hux hsm hx
    rw [hsm, Pi.smul_apply, hux hx, smul_zero]

/-- Auxiliary restriction map from `L²(ℝ; ℝ)` to `L²((-∞, 0]; ℝ)`. -/
noncomputable def l2NegRestriction :
    L2R →L[ℝ] Lp (α := ℝ) ℝ 2 ((volume : Measure ℝ).restrict (Set.Iic (0 : ℝ))) :=
  Lp.LpToLpOfMeasureLeSMul (p := 2) (E := ℝ) (μ := (volume : Measure ℝ).restrict (Set.Iic (0 : ℝ)))
    (ν := (volume : Measure ℝ)) (c := 1) ENNReal.one_ne_top
    (by simpa only [one_smul] using Measure.restrict_le_self)

/-- Closedness of `L²_0(ℝ)` in `L²(ℝ; ℝ)` (`prop:zerospaces`). -/
theorem isClosed_l2ZeroSubmodule : IsClosed (l2ZeroSubmodule : Set L2R) := by
  have hker : (l2ZeroSubmodule : Set L2R) =
      ((l2NegRestriction : L2R →L[ℝ] _).toLinearMap.ker : Set L2R) := by
    ext u
    rw [SetLike.mem_coe, SetLike.mem_coe, LinearMap.mem_ker, Lp.ext_iff]
    change (∀ᵐ x : ℝ ∂volume, x ≤ 0 → (u : ℝ → ℝ) x = 0) ↔
      (l2NegRestriction u : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Set.Iic (0 : ℝ))]
        ((0 : Lp (α := ℝ) ℝ 2 ((volume : Measure ℝ).restrict (Set.Iic (0 : ℝ)))) : ℝ → ℝ)
    have hcoeff : (l2NegRestriction u : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Set.Iic (0 : ℝ))]
        (u : ℝ → ℝ) := Lp.coeFn_LpToLpOfMeasureLeSMul _ _ u
    have hzero : ((0 : Lp (α := ℝ) ℝ 2 ((volume : Measure ℝ).restrict (Set.Iic (0 : ℝ)))) :
        ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Set.Iic (0 : ℝ))] 0 := Lp.coeFn_zero ℝ 2 _
    change (∀ᵐ x : ℝ ∂volume, x ∈ Set.Iic (0 : ℝ) → (u : ℝ → ℝ) x = 0) ↔ _
    rw [← ae_restrict_iff' measurableSet_Iic]
    constructor
    · intro h; filter_upwards [h, hcoeff, hzero] with x hx hc hz; rw [hc, hz]; exact hx
    · intro h; filter_upwards [h, hcoeff, hzero] with x hx hc hz; rw [← hc, hx, hz]; rfl
  rw [hker]
  exact ContinuousLinearMap.isClosed_ker l2NegRestriction

/-- Completeness of `L²_0(ℝ)` (`prop:zerospaces`). -/
noncomputable instance instCompleteSpaceL2ZeroSubmodule : CompleteSpace ↥l2ZeroSubmodule :=
  isClosed_l2ZeroSubmodule.completeSpace_coe

/-- Canonical linear isometric isomorphism `L²_0(ℝ) ≃ₗᵢ[ℝ] L²((0, ∞); ℝ)` (`prop:zerospaces`). -/
noncomputable def l2ZeroIsoIoi : ↥l2ZeroSubmodule ≃ₗᵢ[ℝ] L2IoiR where
  toLinearMap :=
    { toFun := fun u => restIoiR u.1
      map_add' := fun u v => map_add restIoiR u.1 v.1
      map_smul' := fun c u => map_smul restIoiR c u.1 }
  invFun f := ⟨halfLineL2ExtendByZero f, by
    filter_upwards [coeFn_lpExtendByZero measurableSet_Ioi f] with x hx hx0
    have hx_not : x ∉ Set.Ioi (0 : ℝ) := fun hh => absurd hx0 (not_le.mpr hh)
    have hx' : (halfLineL2ExtendByZero f : ℝ → ℝ) x = (Set.Ioi (0 : ℝ)).indicator (f : ℝ → ℝ) x :=
      hx
    rw [hx', Set.indicator_of_notMem hx_not]⟩
  left_inv u := Subtype.ext (halfLineL2ExtendByZero_restIoiR_of_ae_zero u.2)
  right_inv f := restIoiR_halfLineL2ExtendByZero f
  norm_map' u := by
    change ‖restIoiR u.1‖ = ‖u.1‖
    have hback := halfLineL2ExtendByZero_restIoiR_of_ae_zero u.2
    calc ‖restIoiR u.1‖ = ‖halfLineL2ExtendByZero (restIoiR u.1)‖ :=
          (halfLineL2ExtendByZero.norm_map (restIoiR u.1)).symm
      _ = ‖u.1‖ := by rw [hback]

/-- **Density of `H^(α/2)_0(ℝ)` in `L²_0(ℝ)` (`prop:zerospaces`)**:
the natural embedding `(gagliardoL2Part α ·)` of `RestrictedGagliardoSpace α` has dense range
in `L²_0(ℝ)`. -/
theorem denseRange_restrictedGagliardoL2Zero {α : ℝ} (hα : FractionalExponent α) :
    DenseRange (fun u : RestrictedGagliardoSpace α =>
      (⟨gagliardoL2Part α u.1, u.2⟩ : ↥l2ZeroSubmodule)) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  obtain ⟨u, hu⟩ := Metric.denseRange_iff.1 (denseRange_restrictedL2Map hα) (restIoiR f.1) ε hε
  refine ⟨u, ?_⟩
  rw [dist_comm, Subtype.dist_eq, dist_eq_norm]
  have hiso : ‖gagliardoL2Part α u.1 - f.1‖ =
      ‖(⟨gagliardoL2Part α u.1, u.2⟩ : ↥l2ZeroSubmodule) - f‖ := rfl
  have hiso2 : ‖(⟨gagliardoL2Part α u.1, u.2⟩ : ↥l2ZeroSubmodule) - f‖ =
      ‖l2ZeroIsoIoi (⟨gagliardoL2Part α u.1, u.2⟩ : ↥l2ZeroSubmodule) - l2ZeroIsoIoi f‖ := by
    rw [← map_sub, l2ZeroIsoIoi.norm_map]
  rw [hiso, hiso2, ← dist_eq_norm, dist_comm]
  exact hu

end

end FracLap
