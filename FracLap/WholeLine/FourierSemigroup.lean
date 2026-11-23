/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Core.FourierSobolev
public import FracLap.Core.HilleYosidaCorrespondence
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLap.WholeLine.FourierSemigroup

Concrete `L²(ℝ; ℂ)` realization of whole-line Fourier multiplier semigroups, contractive
resolvents, Hille–Yosida generation, the 1D fractional Laplacian semigroup, and the Fourier
convolution equivalence (Engel–Nagel Paragraph I.4.12 / II.2.9):
- `L2C`: the concrete complex Hilbert space `Lp (α := ℝ) ℂ 2 volume`.
- `multOpCLM` & `fourierMultiplier`: bounded `L^∞` multiplication and Fourier multiplier
  operators on `L2C`, viewed over `ℝ` to interface with `StronglyContinuousContractionSemigroup`
  and `ContractiveResolvent`.
- `fourierMultiplierSemigroup`: the concrete `C₀`-contraction semigroup
  `S(t) = 𝓕⁻¹ ∘ M_{exp(-t ψ)} ∘ 𝓕` for any measurable nonnegative symbol `ψ : ℝ → ℝ`.
- `fourierMultiplierResolvent`: the concrete contractive resolvent
  `R_μ = 𝓕⁻¹ ∘ M_{(μ + ψ)⁻¹} ∘ 𝓕`.
- `fourierMultiplierSemigroup_resolvent_eq` & `fourierMultiplierResolvent_generatedSemigroup_eq`:
  exact Hille–Yosida identification `(fourierMultiplierResolvent ψ ...).generatedSemigroup =
  fourierMultiplierSemigroup ψ ...`.
- `fracLapSymbol`, `fracLapSemigroup`, `fracLapResolvent`, `fracLapResolvent_generatedSemigroup_eq`:
  specialization to the 1D fractional Laplacian symbol `|2 π ξ|^α`.
- `fourierMultiplier_eq_conv_toLp`: concrete identification on `L²(ℝ; ℂ)` of a Fourier multiplier
  with convolution by an integrable kernel `K` via `Real.fourier_mul_convolution_eq`.
-/

namespace FracLap

open Complex Filter FourierTransform MeasureTheory Real Set Topology
open scoped ENNReal NNReal SchwartzMap ComplexInnerProductSpace Convolution

@[expose] public section

/-- Concrete Hilbert space `L²(ℝ; ℂ)` with Lebesgue measure `volume`. -/
noncomputable abbrev L2C := Lp (α := ℝ) ℂ 2 volume

/-! ### 1. Bounded `L^∞` multiplication operators and Fourier multipliers on `L²(ℝ; ℂ)` -/

/-- Construct an `L^∞(ℝ; ℂ)` element from a strongly measurable uniformly bounded function. -/
noncomputable def toLpTop {m : ℝ → ℂ} (hm : AEStronglyMeasurable m volume)
    {C : ℝ} (hC : 0 ≤ C) (hbdd : ∀ ξ, ‖m ξ‖ ≤ C) : Lp (α := ℝ) ℂ ∞ volume :=
  have _ := hC
  (memLp_top_of_bound hm C (Eventually.of_forall hbdd)).toLp m

/-- Coercion to functions agrees a.e. for `toLpTop`. -/
theorem coeFn_toLpTop {m : ℝ → ℂ} (hm : AEStronglyMeasurable m volume)
    {C : ℝ} (hC : 0 ≤ C) (hbdd : ∀ ξ, ‖m ξ‖ ≤ C) :
    (toLpTop hm hC hbdd : ℝ → ℂ) =ᵐ[volume] m :=
  MemLp.coeFn_toLp (memLp_top_of_bound hm C (Eventually.of_forall hbdd))

/-- Operator norm bound on `toLpTop`: `‖toLpTop hm hC hbdd‖ ≤ C`. -/
theorem norm_toLpTop_le {m : ℝ → ℂ} (hm : AEStronglyMeasurable m volume)
    {C : ℝ} (hC : 0 ≤ C) (hbdd : ∀ ξ, ‖m ξ‖ ≤ C) :
    ‖toLpTop hm hC hbdd‖ ≤ C := by
  rw [Lp.norm_def]
  have he : eLpNorm (toLpTop hm hC hbdd : ℝ → ℂ) ∞ volume ≤ ENNReal.ofReal C := by
    rw [eLpNorm_congr_ae (coeFn_toLpTop hm hC hbdd), eLpNorm_exponent_top]
    · exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall hbdd)
    · exact hm
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq (ENNReal.toReal_ofReal hC)

/-- Multiplication by `m ∈ L^∞(ℝ; ℂ)` as an `ℝ`-continuous linear operator on `L²(ℝ; ℂ)`. -/
noncomputable def multOpCLM (m : Lp (α := ℝ) ℂ ∞ volume) : L2C →L[ℝ] L2C :=
  LinearMap.mkContinuous
    { toFun := fun f => (m • f : L2C)
      map_add' := fun f g => by
        rw [Lp.ext_iff]
        filter_upwards [Lp.coeFn_lpSMul (r := 2) m (f + g),
          Lp.coeFn_lpSMul (r := 2) m f, Lp.coeFn_lpSMul (r := 2) m g,
          Lp.coeFn_add (m • f : L2C) (m • g : L2C), Lp.coeFn_add f g]
          with ξ hfg hf hg haddm hadd
        simp only [smul_eq_mul, Pi.mul_apply, Pi.add_apply] at hfg hf hg haddm hadd ⊢
        rw [hfg, hadd, haddm, hf, hg, mul_add]
      map_smul' := fun r f => by
        rw [Lp.ext_iff]
        filter_upwards [Lp.coeFn_lpSMul (r := 2) m (r • f),
          Lp.coeFn_lpSMul (r := 2) m f,
          Lp.coeFn_smul r f, Lp.coeFn_smul r (m • f : L2C)] with ξ hmf hr hs1 hs2
        have hs1' : ((r • f : L2C) : ℝ → ℂ) ξ = (r : ℂ) * (f : ℝ → ℂ) ξ := by
          simpa only [Pi.smul_apply, Complex.real_smul] using hs1
        have hs2' :
            ((r • (m • f : L2C) : L2C) : ℝ → ℂ) ξ =
              (r : ℂ) * ((m • f : L2C) : ℝ → ℂ) ξ := by
          simpa only [Pi.smul_apply, Complex.real_smul] using hs2
        simp only [smul_eq_mul, Pi.mul_apply] at hmf hr
        change ((m • (r • f : L2C) : L2C) : ℝ → ℂ) ξ = ((r • (m • f : L2C) : L2C) : ℝ → ℂ) ξ
        rw [hmf, hs1', hs2', hr]
        ring }
    ‖m‖ (fun f => Lp.norm_smul_le m f)

/-- Unfolding `multOpCLM`. -/
theorem multOpCLM_apply (m : Lp (α := ℝ) ℂ ∞ volume) (f : L2C) :
    multOpCLM m f = (m • f : L2C) := by
  simp only [multOpCLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]

/-- Operator norm bound for `multOpCLM`. -/
theorem opNorm_multOpCLM_le (m : Lp (α := ℝ) ℂ ∞ volume) : ‖multOpCLM m‖ ≤ ‖m‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg m) _

/-- `multOpCLM` at the constant symbol `1` is the identity operator. -/
theorem multOpCLM_one :
    multOpCLM
        (toLpTop (m := fun _ : ℝ => (1 : ℂ)) aestronglyMeasurable_const zero_le_one
          (fun _ : ℝ => by norm_num)) =
      ContinuousLinearMap.id ℝ L2C := by
  ext1 f
  rw [ContinuousLinearMap.id_apply, multOpCLM_apply, Lp.ext_iff]
  filter_upwards [Lp.coeFn_lpSMul (r := 2)
      (toLpTop (m := fun _ : ℝ => (1 : ℂ)) aestronglyMeasurable_const zero_le_one
        (fun _ : ℝ => by norm_num)) f,
    coeFn_toLpTop (m := fun _ : ℝ => (1 : ℂ)) aestronglyMeasurable_const zero_le_one
      (fun _ : ℝ => by norm_num)] with ξ hsmul hm
  simp only [smul_eq_mul, Pi.mul_apply, hm, one_mul] at hsmul ⊢
  exact hsmul

/-- Composition of two `multOpCLM`s corresponds to pointwise multiplication of symbols. -/
theorem multOpCLM_comp {m₁ m₂ m₁₂ : ℝ → ℂ}
    (hm₁ : AEStronglyMeasurable m₁ volume) {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (hb₁ : ∀ ξ, ‖m₁ ξ‖ ≤ C₁)
    (hm₂ : AEStronglyMeasurable m₂ volume) {C₂ : ℝ} (hC₂ : 0 ≤ C₂) (hb₂ : ∀ ξ, ‖m₂ ξ‖ ≤ C₂)
    (hm₁₂ : AEStronglyMeasurable m₁₂ volume) {C₁₂ : ℝ} (hC₁₂ : 0 ≤ C₁₂)
    (hb₁₂ : ∀ ξ, ‖m₁₂ ξ‖ ≤ C₁₂) (heq : ∀ ξ, m₁ ξ * m₂ ξ = m₁₂ ξ) :
    (multOpCLM (toLpTop hm₁ hC₁ hb₁)).comp (multOpCLM (toLpTop hm₂ hC₂ hb₂)) =
      multOpCLM (toLpTop hm₁₂ hC₁₂ hb₁₂) := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply, multOpCLM_apply, multOpCLM_apply, multOpCLM_apply,
    Lp.ext_iff]
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (toLpTop hm₁ hC₁ hb₁) ((toLpTop hm₂ hC₂ hb₂ • f : L2C)),
    Lp.coeFn_lpSMul (r := 2) (toLpTop hm₂ hC₂ hb₂) f,
    Lp.coeFn_lpSMul (r := 2) (toLpTop hm₁₂ hC₁₂ hb₁₂) f,
    coeFn_toLpTop hm₁ hC₁ hb₁, coeFn_toLpTop hm₂ hC₂ hb₂,
    coeFn_toLpTop hm₁₂ hC₁₂ hb₁₂] with ξ hsmul₁ hsmul₂ hsmul₁₂ h1 h2 h12
  simp only [smul_eq_mul, Pi.mul_apply, h1, h2, h12] at hsmul₁ hsmul₂ hsmul₁₂ ⊢
  rw [hsmul₁, hsmul₂, hsmul₁₂, ← mul_assoc, heq ξ]

/-- Difference of two `multOpCLM`s corresponds to pointwise difference of symbols. -/
theorem multOpCLM_sub {m₁ m₂ d : ℝ → ℂ}
    (hm₁ : AEStronglyMeasurable m₁ volume) {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (hb₁ : ∀ ξ, ‖m₁ ξ‖ ≤ C₁)
    (hm₂ : AEStronglyMeasurable m₂ volume) {C₂ : ℝ} (hC₂ : 0 ≤ C₂) (hb₂ : ∀ ξ, ‖m₂ ξ‖ ≤ C₂)
    (hd : AEStronglyMeasurable d volume) {Cd : ℝ} (hCd : 0 ≤ Cd) (hbd : ∀ ξ, ‖d ξ‖ ≤ Cd)
    (heq : ∀ ξ, m₁ ξ - m₂ ξ = d ξ) :
    multOpCLM (toLpTop hm₁ hC₁ hb₁) - multOpCLM (toLpTop hm₂ hC₂ hb₂) =
      multOpCLM (toLpTop hd hCd hbd) := by
  ext1 f
  rw [sub_apply, multOpCLM_apply, multOpCLM_apply, multOpCLM_apply, Lp.ext_iff]
  filter_upwards [Lp.coeFn_sub (toLpTop hm₁ hC₁ hb₁ • f : L2C) (toLpTop hm₂ hC₂ hb₂ • f : L2C),
    Lp.coeFn_lpSMul (r := 2) (toLpTop hm₁ hC₁ hb₁) f,
    Lp.coeFn_lpSMul (r := 2) (toLpTop hm₂ hC₂ hb₂) f,
    Lp.coeFn_lpSMul (r := 2) (toLpTop hd hCd hbd) f,
    coeFn_toLpTop hm₁ hC₁ hb₁, coeFn_toLpTop hm₂ hC₂ hb₂,
    coeFn_toLpTop hd hCd hbd] with ξ hsub hsmul₁ hsmul₂ hsmuld h1 h2 h3
  simp only [Pi.sub_apply, smul_eq_mul, Pi.mul_apply, h1, h2, h3]
    at hsub hsmul₁ hsmul₂ hsmuld ⊢
  rw [hsub, hsmul₁, hsmul₂, hsmuld, ← sub_mul, heq ξ]

/-- Scalar multiplication on `multOpCLM`. -/
theorem multOpCLM_smul (c : ℝ) {m cm : ℝ → ℂ}
    (hm : AEStronglyMeasurable m volume) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ ξ, ‖m ξ‖ ≤ C)
    (hcm : AEStronglyMeasurable cm volume) {Cc : ℝ} (hCc : 0 ≤ Cc) (hbc : ∀ ξ, ‖cm ξ‖ ≤ Cc)
    (heq : ∀ ξ, (c : ℂ) * m ξ = cm ξ) :
    c • multOpCLM (toLpTop hm hC hb) = multOpCLM (toLpTop hcm hCc hbc) := by
  ext1 f
  rw [smul_apply, multOpCLM_apply, multOpCLM_apply, Lp.ext_iff]
  filter_upwards [Lp.coeFn_smul c (toLpTop hm hC hb • f : L2C),
    Lp.coeFn_lpSMul (r := 2) (toLpTop hm hC hb) f,
    Lp.coeFn_lpSMul (r := 2) (toLpTop hcm hCc hbc) f,
    coeFn_toLpTop hm hC hb, coeFn_toLpTop hcm hCc hbc] with ξ hsmulc hsmulm hsmulcm h1 h2
  have hsmulc' :
      ((c • (toLpTop hm hC hb • f : L2C) : L2C) : ℝ → ℂ) ξ =
        (c : ℂ) * ((toLpTop hm hC hb • f : L2C) : ℝ → ℂ) ξ := by
    simpa only [Pi.smul_apply, Complex.real_smul] using hsmulc
  simp only [smul_eq_mul, Pi.mul_apply, h1, h2] at hsmulm hsmulcm
  rw [hsmulc', hsmulm, hsmulcm, ← mul_assoc, heq ξ]

/-- The `L²(ℝ; ℂ)` Fourier transform as an `ℝ`-continuous linear operator. -/
noncomputable def fourierCLEReal : L2C →L[ℝ] L2C :=
  ((Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ

/-- The `L²(ℝ; ℂ)` inverse Fourier transform as an `ℝ`-continuous linear operator. -/
noncomputable def fourierInvCLEReal : L2C →L[ℝ] L2C :=
  ((Lp.fourierTransformₗᵢ ℝ ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ

/-- Fourier multiplier operator `M_m^𝓕 = 𝓕⁻¹ ∘ M_m ∘ 𝓕` on `L²(ℝ; ℂ)`. -/
noncomputable def fourierMultiplier (m : Lp (α := ℝ) ℂ ∞ volume) : L2C →L[ℝ] L2C :=
  fourierInvCLEReal.comp ((multOpCLM m).comp fourierCLEReal)

/-- Unfolding `fourierMultiplier`. -/
theorem fourierMultiplier_apply (m : Lp (α := ℝ) ℂ ∞ volume) (f : L2C) :
    fourierMultiplier m f = 𝓕⁻ (m • 𝓕 f) := by
  simp only [fourierMultiplier, fourierCLEReal, fourierInvCLEReal, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', multOpCLM_apply]
  rfl

/-- Plancherel norm preservation for `fourierMultiplier`: `‖fourierMultiplier m‖ ≤ ‖m‖`. -/
theorem opNorm_fourierMultiplier_le (m : Lp (α := ℝ) ℂ ∞ volume) : ‖fourierMultiplier m‖ ≤ ‖m‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg m) fun f => ?_
  rw [fourierMultiplier_apply]
  calc
    ‖(𝓕⁻ (m • 𝓕 f) : L2C)‖ = ‖(m • 𝓕 f : L2C)‖ := (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map _
    _ ≤ ‖m‖ * ‖𝓕 f‖ := Lp.norm_smul_le m (𝓕 f)
    _ = ‖m‖ * ‖f‖ := by rw [Lp.norm_fourier_eq f]

/-- `fourierMultiplier` at constant symbol `1` is the identity on `L²(ℝ; ℂ)`. -/
theorem fourierMultiplier_one :
    fourierMultiplier
        (toLpTop (m := fun _ : ℝ => (1 : ℂ)) aestronglyMeasurable_const zero_le_one
          (fun _ : ℝ => by norm_num)) =
      ContinuousLinearMap.id ℝ L2C := by
  ext1 f
  rw [ContinuousLinearMap.id_apply, fourierMultiplier_apply,
    ← multOpCLM_apply, multOpCLM_one, ContinuousLinearMap.id_apply]
  exact fourierInv_fourier_eq f

/-- Composition of Fourier multipliers multiplies their symbols. -/
theorem fourierMultiplier_comp {m₁ m₂ m₁₂ : ℝ → ℂ}
    (hm₁ : AEStronglyMeasurable m₁ volume) {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (hb₁ : ∀ ξ, ‖m₁ ξ‖ ≤ C₁)
    (hm₂ : AEStronglyMeasurable m₂ volume) {C₂ : ℝ} (hC₂ : 0 ≤ C₂) (hb₂ : ∀ ξ, ‖m₂ ξ‖ ≤ C₂)
    (hm₁₂ : AEStronglyMeasurable m₁₂ volume) {C₁₂ : ℝ} (hC₁₂ : 0 ≤ C₁₂)
    (hb₁₂ : ∀ ξ, ‖m₁₂ ξ‖ ≤ C₁₂) (heq : ∀ ξ, m₁ ξ * m₂ ξ = m₁₂ ξ) :
    (fourierMultiplier (toLpTop hm₁ hC₁ hb₁)).comp
        (fourierMultiplier (toLpTop hm₂ hC₂ hb₂)) =
      fourierMultiplier (toLpTop hm₁₂ hC₁₂ hb₁₂) := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply, fourierMultiplier_apply, fourierMultiplier_apply,
    fourierMultiplier_apply]
  have hinv : 𝓕 (𝓕⁻ ((toLpTop hm₂ hC₂ hb₂ • 𝓕 f : L2C))) = (toLpTop hm₂ hC₂ hb₂ • 𝓕 f : L2C) :=
    fourier_fourierInv_eq _
  rw [hinv]
  have hcomp := congrArg (fun T : L2C →L[ℝ] L2C => T (𝓕 f))
    (multOpCLM_comp hm₁ hC₁ hb₁ hm₂ hC₂ hb₂ hm₁₂ hC₁₂ hb₁₂ heq)
  simp only [ContinuousLinearMap.comp_apply, multOpCLM_apply] at hcomp
  rw [hcomp]

/-- Difference of Fourier multipliers subtracts their symbols. -/
theorem fourierMultiplier_sub {m₁ m₂ d : ℝ → ℂ}
    (hm₁ : AEStronglyMeasurable m₁ volume) {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (hb₁ : ∀ ξ, ‖m₁ ξ‖ ≤ C₁)
    (hm₂ : AEStronglyMeasurable m₂ volume) {C₂ : ℝ} (hC₂ : 0 ≤ C₂) (hb₂ : ∀ ξ, ‖m₂ ξ‖ ≤ C₂)
    (hd : AEStronglyMeasurable d volume) {Cd : ℝ} (hCd : 0 ≤ Cd) (hbd : ∀ ξ, ‖d ξ‖ ≤ Cd)
    (heq : ∀ ξ, m₁ ξ - m₂ ξ = d ξ) :
    fourierMultiplier (toLpTop hm₁ hC₁ hb₁) - fourierMultiplier (toLpTop hm₂ hC₂ hb₂) =
      fourierMultiplier (toLpTop hd hCd hbd) := by
  ext1 f
  rw [sub_apply, fourierMultiplier_apply, fourierMultiplier_apply, fourierMultiplier_apply,
    ← fourierInv_sub]
  have hsub := congrArg (fun T : L2C →L[ℝ] L2C => T (𝓕 f))
    (multOpCLM_sub hm₁ hC₁ hb₁ hm₂ hC₂ hb₂ hd hCd hbd heq)
  simp only [sub_apply, multOpCLM_apply] at hsub
  rw [hsub]

/-- Real scalar multiple of a Fourier multiplier scales its symbol. -/
theorem fourierMultiplier_smul (c : ℝ) {m cm : ℝ → ℂ}
    (hm : AEStronglyMeasurable m volume) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ ξ, ‖m ξ‖ ≤ C)
    (hcm : AEStronglyMeasurable cm volume) {Cc : ℝ} (hCc : 0 ≤ Cc) (hbc : ∀ ξ, ‖cm ξ‖ ≤ Cc)
    (heq : ∀ ξ, (c : ℂ) * m ξ = cm ξ) :
    c • fourierMultiplier (toLpTop hm hC hb) = fourierMultiplier (toLpTop hcm hCc hbc) := by
  ext1 f
  rw [smul_apply, fourierMultiplier_apply, fourierMultiplier_apply]
  have hinv_smul :
      (c • (𝓕⁻ (toLpTop hm hC hb • 𝓕 f : L2C) : L2C) : L2C) =
        𝓕⁻ (c • (toLpTop hm hC hb • 𝓕 f : L2C)) := by
    change c • fourierInvCLEReal (toLpTop hm hC hb • 𝓕 f : L2C) =
      fourierInvCLEReal (c • (toLpTop hm hC hb • 𝓕 f : L2C))
    exact (map_smul fourierInvCLEReal c _).symm
  rw [hinv_smul]
  have hsmul := congrArg (fun T : L2C →L[ℝ] L2C => T (𝓕 f))
    (multOpCLM_smul c hm hC hb hcm hCc hbc heq)
  simp only [smul_apply, multOpCLM_apply] at hsmul
  rw [hsmul]

/-! ### 2. Concrete Fourier multiplier `C₀`-contraction semigroup -/

/-- Strong measurability of `ξ ↦ exp (-t * ψ ξ)`. -/
theorem expSymbol_aestronglyMeasurable (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ) (t : ℝ) :
    AEStronglyMeasurable (fun ξ : ℝ => ((Real.exp (-t * ψ ξ) : ℝ) : ℂ)) volume :=
  (Complex.continuous_ofReal.measurable.comp
    (Real.continuous_exp.measurable.comp (measurable_const.mul hψ_meas))).aestronglyMeasurable

/-- Uniform `L^∞` bound `≤ 1` on `ξ ↦ exp (-t * ψ ξ)` when `0 ≤ t` and `ψ ≥ 0`. -/
theorem norm_expSymbol_le_one (ψ : ℝ → ℝ) (hψ_nonneg : ∀ ξ, 0 ≤ ψ ξ)
    {t : ℝ} (ht : 0 ≤ t) (ξ : ℝ) :
    ‖((Real.exp (-t * ψ ξ) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (hψ_nonneg ξ)

/-- Exponential Fourier multiplier symbol `ξ ↦ exp(-t ψ(ξ))` in `L^∞(ℝ; ℂ)`. -/
noncomputable def expMultiplierSymbol (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ)
    (hψ_nonneg : ∀ ξ, 0 ≤ ψ ξ) (t : ℝ≥0) : Lp (α := ℝ) ℂ ∞ volume :=
  toLpTop (expSymbol_aestronglyMeasurable ψ hψ_meas t) zero_le_one
    (norm_expSymbol_le_one ψ hψ_nonneg t.coe_nonneg)

/-- Strong orbit continuity of the Fourier multiplier semigroup `t ↦ M_{exp(-t ψ)}^𝓕 f`. -/
theorem continuous_orbit_expMultiplier (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ)
    (hψ_nonneg : ∀ ξ, 0 ≤ ψ ξ) (f : L2C) :
    Continuous fun t : ℝ≥0 =>
      fourierMultiplier (expMultiplierSymbol ψ hψ_meas hψ_nonneg t) f := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hsq_tendsto :
      Tendsto (fun t : ℝ≥0 =>
          ∫ ξ : ℝ,
            ‖(expMultiplierSymbol ψ hψ_meas hψ_nonneg t : ℝ → ℂ) ξ -
              (expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀ : ℝ → ℂ) ξ‖ ^ 2 *
                ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2)
        (𝓝 t₀) (𝓝 0) := by
    have hf2 : Integrable (fun ξ : ℝ => 4 * ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2) volume := by
      have hinner :
          Integrable (fun ξ : ℝ => ⟪((𝓕 f : L2C) : ℝ → ℂ) ξ, ((𝓕 f : L2C) : ℝ → ℂ) ξ⟫) volume :=
        L2.integrable_inner (𝓕 f) (𝓕 f)
      have hre :
          Integrable (fun ξ : ℝ =>
            RCLike.re ⟪((𝓕 f : L2C) : ℝ → ℂ) ξ, ((𝓕 f : L2C) : ℝ → ℂ) ξ⟫) volume :=
        hinner.re
      have hnormsq : Integrable (fun ξ : ℝ => ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2) volume := by
        refine hre.congr (Eventually.of_forall fun ξ => ?_)
        dsimp only
        rw [inner_self_eq_norm_sq_to_K]
        simp only [Complex.coe_algebraMap, RCLike.re_to_complex, ← Complex.ofReal_pow,
          Complex.ofReal_re]
      exact hnormsq.const_mul 4
    have hlim_int :
        Tendsto (fun t : ℝ≥0 =>
            ∫ ξ : ℝ, ((Real.exp (-(t : ℝ) * ψ ξ) -
              Real.exp (-(t₀ : ℝ) * ψ ξ)) ^ 2) * ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2)
          (𝓝 t₀) (𝓝 0) := by
      have hdom :=
        tendsto_integral_filter_of_dominated_convergence
          (F := fun (t : ℝ≥0) (ξ : ℝ) =>
            ((Real.exp (-(t : ℝ) * ψ ξ) - Real.exp (-(t₀ : ℝ) * ψ ξ)) ^ 2) *
              ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2)
          (f := fun _ : ℝ => (0 : ℝ))
          (bound := fun ξ : ℝ => 4 * ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2)
          (l := 𝓝 t₀)
          (Eventually.of_forall fun t => by
            have hm1 : Measurable (fun ξ : ℝ =>
                (Real.exp (-(t : ℝ) * ψ ξ) - Real.exp (-(t₀ : ℝ) * ψ ξ)) ^ 2) :=
              ((Real.continuous_exp.measurable.comp (measurable_const.mul hψ_meas)).sub
                (Real.continuous_exp.measurable.comp
                  (measurable_const.mul hψ_meas))).pow_const 2
            exact (hm1.aestronglyMeasurable.mul
              ((Lp.aestronglyMeasurable (𝓕 f)).norm.pow 2)))
          (Eventually.of_forall fun t => Eventually.of_forall fun ξ => by
            have h1 : ‖Real.exp (-(t : ℝ) * ψ ξ)‖ ≤ 1 := by
              rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
              exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg) (hψ_nonneg ξ)
            have h2 : ‖Real.exp (-(t₀ : ℝ) * ψ ξ)‖ ≤ 1 := by
              rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
              exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t₀.coe_nonneg) (hψ_nonneg ξ)
            have hdiff :
                |Real.exp (-(t : ℝ) * ψ ξ) - Real.exp (-(t₀ : ℝ) * ψ ξ)| ≤ 2 := by
              calc
                |Real.exp (-(t : ℝ) * ψ ξ) - Real.exp (-(t₀ : ℝ) * ψ ξ)|
                    ≤ |Real.exp (-(t : ℝ) * ψ ξ)| + |Real.exp (-(t₀ : ℝ) * ψ ξ)| :=
                  abs_sub _ _
                _ ≤ 1 + 1 := by
                  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
                  exact add_le_add h1 h2
                _ = 2 := by norm_num
            have hsq :
                (Real.exp (-(t : ℝ) * ψ ξ) - Real.exp (-(t₀ : ℝ) * ψ ξ)) ^ 2 ≤ 4 := by
              have hsq' :
                  |Real.exp (-(t : ℝ) * ψ ξ) - Real.exp (-(t₀ : ℝ) * ψ ξ)| ^ 2 ≤ 2 ^ 2 :=
                pow_le_pow_left₀ (abs_nonneg _) hdiff 2
              rw [sq_abs] at hsq'
              linarith
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _))
          hf2
          (Eventually.of_forall fun ξ => by
            have hcont : Continuous fun t : ℝ≥0 =>
                (Real.exp (-(t : ℝ) * ψ ξ) - Real.exp (-(t₀ : ℝ) * ψ ξ)) ^ 2 *
                  ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2 :=
              (((Real.continuous_exp.comp
                (NNReal.continuous_coe.neg.mul continuous_const)).sub
                  continuous_const).pow 2).mul continuous_const
            have ht0 := hcont.tendsto t₀
            simpa only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
              zero_mul] using ht0)
      simpa only [integral_zero] using hdom
    refine hlim_int.congr fun t => integral_congr_ae ?_
    filter_upwards [coeFn_toLpTop (expSymbol_aestronglyMeasurable ψ hψ_meas t) zero_le_one
      (norm_expSymbol_le_one ψ hψ_nonneg t.coe_nonneg),
      coeFn_toLpTop (expSymbol_aestronglyMeasurable ψ hψ_meas t₀) zero_le_one
      (norm_expSymbol_le_one ψ hψ_nonneg t₀.coe_nonneg)] with ξ ht ht₀
    simp only [expMultiplierSymbol, ht, ht₀]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hnorm_tendsto :
      Tendsto (fun t : ℝ≥0 =>
          dist (fourierMultiplier (expMultiplierSymbol ψ hψ_meas hψ_nonneg t) f)
            (fourierMultiplier (expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀) f))
        (𝓝 t₀) (𝓝 0) := by
    refine tendsto_zero_of_nonneg_sq_le (fun _ => dist_nonneg) (fun t => ?_) hsq_tendsto
    rw [dist_eq_norm, fourierMultiplier_apply, fourierMultiplier_apply, ← fourierInv_sub]
    have hnorm_inv :
        ‖(𝓕⁻ ((expMultiplierSymbol ψ hψ_meas hψ_nonneg t • 𝓕 f : L2C) -
          (expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀ • 𝓕 f : L2C)) : L2C)‖ =
          ‖(expMultiplierSymbol ψ hψ_meas hψ_nonneg t • 𝓕 f : L2C) -
            (expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀ • 𝓕 f : L2C)‖ :=
      (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map _
    have hsub_smul :
        (expMultiplierSymbol ψ hψ_meas hψ_nonneg t • 𝓕 f : L2C) -
          (expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀ • 𝓕 f : L2C) =
          ((expMultiplierSymbol ψ hψ_meas hψ_nonneg t -
            expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀) • 𝓕 f : L2C) := by
      rw [Lp.ext_iff]
      filter_upwards [Lp.coeFn_sub
        (expMultiplierSymbol ψ hψ_meas hψ_nonneg t • 𝓕 f : L2C)
        (expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀ • 𝓕 f : L2C),
        Lp.coeFn_lpSMul (r := 2) (expMultiplierSymbol ψ hψ_meas hψ_nonneg t) (𝓕 f),
        Lp.coeFn_lpSMul (r := 2) (expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀) (𝓕 f),
        Lp.coeFn_lpSMul (r := 2)
          (expMultiplierSymbol ψ hψ_meas hψ_nonneg t -
            expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀) (𝓕 f),
        Lp.coeFn_sub (expMultiplierSymbol ψ hψ_meas hψ_nonneg t)
          (expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀)]
        with ξ hsub h1 h2 hdiff hsym
      simp only [Pi.sub_apply] at hsub hsym
      have h1' :
          ((expMultiplierSymbol ψ hψ_meas hψ_nonneg t • 𝓕 f : L2C) : ℝ → ℂ) ξ =
            (expMultiplierSymbol ψ hψ_meas hψ_nonneg t : ℝ → ℂ) ξ * ((𝓕 f : L2C) : ℝ → ℂ) ξ := h1
      have h2' :
          ((expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀ • 𝓕 f : L2C) : ℝ → ℂ) ξ =
            (expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀ : ℝ → ℂ) ξ * ((𝓕 f : L2C) : ℝ → ℂ) ξ := h2
      have hdiff' :
          (((expMultiplierSymbol ψ hψ_meas hψ_nonneg t -
            expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀) • 𝓕 f : L2C) : ℝ → ℂ) ξ =
            ((expMultiplierSymbol ψ hψ_meas hψ_nonneg t -
              expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀ : Lp (α := ℝ) ℂ ∞ volume) :
                ℝ → ℂ) ξ * ((𝓕 f : L2C) : ℝ → ℂ) ξ := hdiff
      rw [hsub, h1', h2', hdiff', hsym, sub_mul]
    rw [hnorm_inv, hsub_smul]
    have hnormsq :
        ‖(expMultiplierSymbol ψ hψ_meas hψ_nonneg t -
          expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀) • 𝓕 f‖ ^ 2 =
          ∫ ξ : ℝ,
            ‖(expMultiplierSymbol ψ hψ_meas hψ_nonneg t : ℝ → ℂ) ξ -
              (expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀ : ℝ → ℂ) ξ‖ ^ 2 *
                ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2 := by
      have hx :
          ‖((expMultiplierSymbol ψ hψ_meas hψ_nonneg t -
            expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀) • 𝓕 f : L2C)‖ ^ 2 =
            (⟪((expMultiplierSymbol ψ hψ_meas hψ_nonneg t -
              expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀) • 𝓕 f : L2C),
              ((expMultiplierSymbol ψ hψ_meas hψ_nonneg t -
                expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀) • 𝓕 f : L2C)⟫ : ℂ).re := by
        simpa only [RCLike.re_to_complex] using
          norm_sq_eq_re_inner (𝕜 := ℂ)
            ((expMultiplierSymbol ψ hψ_meas hψ_nonneg t -
              expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀) • 𝓕 f : L2C)
      have hint_re :
          (∫ ξ : ℝ,
            ⟪(((expMultiplierSymbol ψ hψ_meas hψ_nonneg t -
              expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀) • 𝓕 f : L2C) : ℝ → ℂ) ξ,
              (((expMultiplierSymbol ψ hψ_meas hψ_nonneg t -
                expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀) • 𝓕 f : L2C) : ℝ → ℂ) ξ⟫).re =
            ∫ ξ : ℝ,
              (⟪(((expMultiplierSymbol ψ hψ_meas hψ_nonneg t -
                expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀) • 𝓕 f : L2C) : ℝ → ℂ) ξ,
                (((expMultiplierSymbol ψ hψ_meas hψ_nonneg t -
                  expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀) • 𝓕 f : L2C) : ℝ → ℂ) ξ⟫ : ℂ).re :=
        (Complex.reCLM.integral_comp_comm (L2.integrable_inner _ _)).symm
      rw [hx, L2.inner_def, hint_re]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_lpSMul (r := 2)
        (expMultiplierSymbol ψ hψ_meas hψ_nonneg t -
          expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀) (𝓕 f),
        Lp.coeFn_sub (expMultiplierSymbol ψ hψ_meas hψ_nonneg t)
          (expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀)] with ξ hsmul hsub
      have hsmul' :
          (((expMultiplierSymbol ψ hψ_meas hψ_nonneg t -
            expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀) • 𝓕 f : L2C) : ℝ → ℂ) ξ =
            ((expMultiplierSymbol ψ hψ_meas hψ_nonneg t : ℝ → ℂ) ξ -
              (expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀ : ℝ → ℂ) ξ) *
                ((𝓕 f : L2C) : ℝ → ℂ) ξ := by
        have hpi :
            (((expMultiplierSymbol ψ hψ_meas hψ_nonneg t -
              expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀) • 𝓕 f : L2C) : ℝ → ℂ) ξ =
              ((expMultiplierSymbol ψ hψ_meas hψ_nonneg t -
                expMultiplierSymbol ψ hψ_meas hψ_nonneg t₀ :
                  Lp (α := ℝ) ℂ ∞ volume) : ℝ → ℂ) ξ * ((𝓕 f : L2C) : ℝ → ℂ) ξ := hsmul
        rw [hpi, hsub]
        rfl
      rw [hsmul', inner_self_eq_norm_sq_to_K]
      simp only [Complex.coe_algebraMap, ← Complex.ofReal_pow, Complex.ofReal_re,
        norm_mul, mul_pow]
    exact hnormsq.le
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using
    Metric.tendsto_nhds.mp hnorm_tendsto ε hε

/-- **Concrete Fourier Multiplier `C₀`-Contraction Semigroup on `L²(ℝ; ℂ)`**:
`S(t) f = 𝓕⁻¹ (exp(-t ψ(·)) • 𝓕 f)`. -/
noncomputable def fourierMultiplierSemigroup (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ)
    (hψ_nonneg : ∀ ξ, 0 ≤ ψ ξ) :
    StronglyContinuousContractionSemigroup L2C where
  operator t := fourierMultiplier (expMultiplierSymbol ψ hψ_meas hψ_nonneg t)
  operator_zero := by
    have heq : expMultiplierSymbol ψ hψ_meas hψ_nonneg 0 =
        toLpTop (m := fun _ : ℝ => (1 : ℂ)) aestronglyMeasurable_const zero_le_one
          (fun _ : ℝ => by norm_num) := by
      rw [Lp.ext_iff]
      filter_upwards [coeFn_toLpTop (expSymbol_aestronglyMeasurable ψ hψ_meas 0) zero_le_one
        (norm_expSymbol_le_one ψ hψ_nonneg (0 : ℝ≥0).coe_nonneg),
        coeFn_toLpTop (m := fun _ : ℝ => (1 : ℂ)) aestronglyMeasurable_const zero_le_one
          (fun _ : ℝ => by norm_num)] with ξ h1 h2
      have h1' :
          (expMultiplierSymbol ψ hψ_meas hψ_nonneg 0 : ℝ → ℂ) ξ =
            ((Real.exp (-((0 : ℝ≥0) : ℝ) * ψ ξ) : ℝ) : ℂ) := h1
      rw [h1', h2]
      simp only [NNReal.coe_zero, neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one]
    rw [heq, fourierMultiplier_one]
  operator_add s t := by
    symm
    refine fourierMultiplier_comp
      (expSymbol_aestronglyMeasurable ψ hψ_meas s) zero_le_one
      (norm_expSymbol_le_one ψ hψ_nonneg s.coe_nonneg)
      (expSymbol_aestronglyMeasurable ψ hψ_meas t) zero_le_one
      (norm_expSymbol_le_one ψ hψ_nonneg t.coe_nonneg)
      (expSymbol_aestronglyMeasurable ψ hψ_meas (s + t)) zero_le_one
      (norm_expSymbol_le_one ψ hψ_nonneg (s + t).coe_nonneg)
      fun ξ => ?_
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  opNorm_le_one t := by
    calc
      ‖fourierMultiplier (expMultiplierSymbol ψ hψ_meas hψ_nonneg t)‖
          ≤ ‖expMultiplierSymbol ψ hψ_meas hψ_nonneg t‖ :=
        opNorm_fourierMultiplier_le _
      _ ≤ 1 :=
        norm_toLpTop_le (expSymbol_aestronglyMeasurable ψ hψ_meas t) zero_le_one
          (norm_expSymbol_le_one ψ hψ_nonneg t.coe_nonneg)
  continuous_orbit := continuous_orbit_expMultiplier ψ hψ_meas hψ_nonneg

/-- Unfolding `(fourierMultiplierSemigroup ψ hψ_meas hψ_nonneg t f)`. -/
theorem fourierMultiplierSemigroup_apply (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ)
    (hψ_nonneg : ∀ ξ, 0 ≤ ψ ξ) (t : ℝ≥0) (f : L2C) :
    fourierMultiplierSemigroup ψ hψ_meas hψ_nonneg t f =
      𝓕⁻ (expMultiplierSymbol ψ hψ_meas hψ_nonneg t • 𝓕 f) := by
  dsimp only [fourierMultiplierSemigroup]
  exact fourierMultiplier_apply _ f

/-! ### 3. Concrete Fourier multiplier contractive resolvent -/

/-- Strong measurability of `ξ ↦ (μ + ψ ξ)⁻¹`. -/
theorem resSymbol_aestronglyMeasurable (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ)
    (μ : PositiveShift) :
    AEStronglyMeasurable (fun ξ : ℝ => ((((μ : ℝ) + ψ ξ)⁻¹ : ℝ) : ℂ)) volume :=
  (Complex.continuous_ofReal.measurable.comp
    ((measurable_const.add hψ_meas).inv)).aestronglyMeasurable

/-- Uniform `L^∞` bound `≤ μ⁻¹` on `ξ ↦ (μ + ψ ξ)⁻¹`. -/
theorem norm_resSymbol_le_inv (ψ : ℝ → ℝ) (hψ_nonneg : ∀ ξ, 0 ≤ ψ ξ)
    (μ : PositiveShift) (ξ : ℝ) :
    ‖((((μ : ℝ) + ψ ξ)⁻¹ : ℝ) : ℂ)‖ ≤ (μ : ℝ)⁻¹ := by
  have hμ : 0 < (μ : ℝ) := μ.2
  have hle : (μ : ℝ) ≤ (μ : ℝ) + ψ ξ := le_add_of_nonneg_right (hψ_nonneg ξ)
  have hpos : 0 < ((μ : ℝ) + ψ ξ)⁻¹ := inv_pos.mpr (lt_of_lt_of_le hμ hle)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  exact inv_anti₀ hμ hle

/-- Resolvent Fourier multiplier symbol `ξ ↦ (μ + ψ(ξ))⁻¹` in `L^∞(ℝ; ℂ)`. -/
noncomputable def resMultiplierSymbol (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ)
    (hψ_nonneg : ∀ ξ, 0 ≤ ψ ξ) (μ : PositiveShift) : Lp (α := ℝ) ℂ ∞ volume :=
  toLpTop (resSymbol_aestronglyMeasurable ψ hψ_meas μ) (inv_nonneg.mpr μ.2.le)
    (norm_resSymbol_le_inv ψ hψ_nonneg μ)

/-- Dense range of `R_μ = 𝓕⁻¹ ∘ M_{(μ + ψ)⁻¹} ∘ 𝓕` via frequency truncation `{ψ ≤ N}`. -/
theorem denseRange_resMultiplier (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ)
    (hψ_nonneg : ∀ ξ, 0 ≤ ψ ξ) (μ : PositiveShift) :
    DenseRange (fourierMultiplier (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ)) := by
  rw [Metric.denseRange_iff]
  intro g ε hε
  have hlim_int :
      Tendsto (fun n : ℕ =>
          ∫ ξ : ℝ,
            (if ψ ξ ≤ (n : ℝ) then (0 : ℝ) else 1) ^ 2 * ‖((𝓕 g : L2C) : ℝ → ℂ) ξ‖ ^ 2)
        atTop (𝓝 0) := by
    have hf2 : Integrable (fun ξ : ℝ => ‖((𝓕 g : L2C) : ℝ → ℂ) ξ‖ ^ 2) volume := by
      have hinner :
          Integrable (fun ξ : ℝ => ⟪((𝓕 g : L2C) : ℝ → ℂ) ξ, ((𝓕 g : L2C) : ℝ → ℂ) ξ⟫) volume :=
        L2.integrable_inner (𝓕 g) (𝓕 g)
      refine hinner.re.congr (Eventually.of_forall fun ξ => ?_)
      dsimp only
      rw [inner_self_eq_norm_sq_to_K]
      simp only [Complex.coe_algebraMap, RCLike.re_to_complex, ← Complex.ofReal_pow,
        Complex.ofReal_re]
    simpa only [integral_zero] using
      tendsto_integral_of_dominated_convergence (fun ξ : ℝ => ‖((𝓕 g : L2C) : ℝ → ℂ) ξ‖ ^ 2)
        (f := fun _ : ℝ => (0 : ℝ))
        (fun n => by
          have hm : Measurable (fun ξ : ℝ => if ψ ξ ≤ (n : ℝ) then (0 : ℝ) else 1) :=
            Measurable.ite (measurableSet_le hψ_meas measurable_const) measurable_const
              measurable_const
          exact ((hm.pow_const 2).aestronglyMeasurable.mul
            ((Lp.aestronglyMeasurable (𝓕 g)).norm.pow 2)))
        hf2
        (fun n => Eventually.of_forall fun ξ => by
          have hle : (if ψ ξ ≤ (n : ℝ) then (0 : ℝ) else (1 : ℝ)) ^ 2 ≤ 1 := by
            by_cases h : ψ ξ ≤ (n : ℝ) <;> simp [h]
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
          calc
            (if ψ ξ ≤ (n : ℝ) then (0 : ℝ) else (1 : ℝ)) ^ 2 * ‖((𝓕 g : L2C) : ℝ → ℂ) ξ‖ ^ 2
                ≤ 1 * ‖((𝓕 g : L2C) : ℝ → ℂ) ξ‖ ^ 2 :=
              mul_le_mul_of_nonneg_right hle (sq_nonneg _)
            _ = ‖((𝓕 g : L2C) : ℝ → ℂ) ξ‖ ^ 2 := one_mul _)
        (Eventually.of_forall fun ξ => by
          obtain ⟨N, hN⟩ := exists_nat_gt (ψ ξ)
          refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
          have hle : ψ ξ ≤ (n : ℝ) := hN.le.trans (Nat.cast_le.mpr hn)
          simp [hle])
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((Metric.tendsto_nhds.mp hlim_int) (ε ^ 2)
    (sq_pos_of_pos hε))
  let bN : ℝ → ℂ := fun ξ =>
    if ψ ξ ≤ (N : ℝ) then ((((μ : ℝ) + ψ ξ : ℝ) : ℂ)) else 0
  have hbN_meas : AEStronglyMeasurable bN volume :=
    (Measurable.ite (measurableSet_le hψ_meas measurable_const)
      (Complex.continuous_ofReal.measurable.comp (measurable_const.add hψ_meas))
      measurable_const).aestronglyMeasurable
  have hbN_bdd : ∀ ξ, ‖bN ξ‖ ≤ (μ : ℝ) + (N : ℝ) := by
    intro ξ
    by_cases hξ : ψ ξ ≤ (N : ℝ)
    · simp only [bN, hξ, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg μ.2.le (hψ_nonneg ξ))]
      linarith
    · simp only [bN, hξ, ↓reduceIte, norm_zero]
      exact add_nonneg μ.2.le (Nat.cast_nonneg N)
  let hN_lp : L2C := (toLpTop hbN_meas (add_nonneg μ.2.le (Nat.cast_nonneg N)) hbN_bdd) • 𝓕 g
  let x : L2C := 𝓕⁻ hN_lp
  refine ⟨x, ?_⟩
  have hdist_sq :
      dist (fourierMultiplier (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ) x) g ^ 2 < ε ^ 2 := by
    rw [dist_eq_norm, fourierMultiplier_apply]
    have hx_fourier : 𝓕 x = hN_lp := fourier_fourierInv_eq hN_lp
    rw [hx_fourier]
    have hrew :
        (𝓕⁻ (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • hN_lp : L2C) : L2C) - g =
          𝓕⁻ ((resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • hN_lp : L2C) - 𝓕 g) := by
      rw [fourierInv_sub, fourierInv_fourier_eq]
    rw [hrew]
    have hnorm_inv :
        ‖(𝓕⁻ ((resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • hN_lp : L2C) - 𝓕 g) : L2C)‖ =
          ‖(resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • hN_lp : L2C) - 𝓕 g‖ :=
      (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map _
    rw [hnorm_inv]
    have hnormsq :
        ‖(resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • hN_lp : L2C) - 𝓕 g‖ ^ 2 =
          ∫ ξ : ℝ, (if ψ ξ ≤ (N : ℝ) then (0 : ℝ) else 1) ^ 2 *
            ‖((𝓕 g : L2C) : ℝ → ℂ) ξ‖ ^ 2 := by
      have hx_norm :
          ‖(resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • hN_lp : L2C) - 𝓕 g‖ ^ 2 =
            (⟪(resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • hN_lp : L2C) - 𝓕 g,
              (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • hN_lp : L2C) - 𝓕 g⟫ : ℂ).re := by
        simpa only [RCLike.re_to_complex] using
          norm_sq_eq_re_inner (𝕜 := ℂ)
            ((resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • hN_lp : L2C) - 𝓕 g)
      have hint_re :
          (∫ ξ : ℝ,
            ⟪(((resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • hN_lp : L2C) - 𝓕 g : L2C) :
                ℝ → ℂ) ξ,
              (((resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • hN_lp : L2C) - 𝓕 g : L2C) :
                ℝ → ℂ) ξ⟫).re =
            ∫ ξ : ℝ,
              (⟪(((resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • hN_lp : L2C) - 𝓕 g : L2C) :
                  ℝ → ℂ) ξ,
                (((resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • hN_lp : L2C) - 𝓕 g : L2C) :
                  ℝ → ℂ) ξ⟫ : ℂ).re :=
        (Complex.reCLM.integral_comp_comm (L2.integrable_inner _ _)).symm
      rw [hx_norm, L2.inner_def, hint_re]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • hN_lp : L2C) (𝓕 g),
        Lp.coeFn_lpSMul (r := 2) (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ) hN_lp,
        Lp.coeFn_lpSMul (r := 2)
          (toLpTop hbN_meas (add_nonneg μ.2.le (Nat.cast_nonneg N)) hbN_bdd) (𝓕 g),
        coeFn_toLpTop (resSymbol_aestronglyMeasurable ψ hψ_meas μ) (inv_nonneg.mpr μ.2.le)
          (norm_resSymbol_le_inv ψ hψ_nonneg μ),
        coeFn_toLpTop hbN_meas (add_nonneg μ.2.le (Nat.cast_nonneg N)) hbN_bdd]
        with ξ hsub hsm1 hsm2 hres hb
      have hsub' :
          (((resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • hN_lp : L2C) - 𝓕 g : L2C) : ℝ → ℂ) ξ =
            (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ : ℝ → ℂ) ξ * (hN_lp : ℝ → ℂ) ξ -
              ((𝓕 g : L2C) : ℝ → ℂ) ξ := by
        simpa only [Pi.sub_apply, smul_eq_mul, Pi.mul_apply, hsm1] using hsub
      have hsm2' : (hN_lp : ℝ → ℂ) ξ = bN ξ * ((𝓕 g : L2C) : ℝ → ℂ) ξ := by
        simpa only [hN_lp, smul_eq_mul, Pi.mul_apply, hb] using hsm2
      have hcoeff :
          (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ : ℝ → ℂ) ξ * bN ξ - 1 =
            ((-(if ψ ξ ≤ (N : ℝ) then (0 : ℝ) else 1) : ℝ) : ℂ) := by
        unfold resMultiplierSymbol
        rw [hres]
        by_cases hξ : ψ ξ ≤ (N : ℝ)
        · have hpos : ((μ : ℝ) + ψ ξ) ≠ 0 := (lt_of_lt_of_le μ.2 (le_add_of_nonneg_right
            (hψ_nonneg ξ))).ne'
          simp only [bN, hξ, ↓reduceIte, neg_zero, Complex.ofReal_zero]
          rw [← Complex.ofReal_mul, inv_mul_cancel₀ hpos, Complex.ofReal_one, sub_self]
        · simp [bN, hξ]
      have hval :
          (((resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • hN_lp : L2C) - 𝓕 g : L2C) : ℝ → ℂ) ξ =
            ((-(if ψ ξ ≤ (N : ℝ) then (0 : ℝ) else 1) : ℝ) : ℂ) * ((𝓕 g : L2C) : ℝ → ℂ) ξ := by
        rw [hsub', hsm2', ← mul_assoc, ← sub_one_mul, hcoeff]
      rw [hval, inner_self_eq_norm_sq_to_K]
      simp only [Complex.coe_algebraMap, ← Complex.ofReal_pow, Complex.ofReal_re,
        norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, neg_sq]
    rw [hnormsq]
    have hN_spec := hN N le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun ξ => by positivity)] at hN_spec
    exact hN_spec
  rw [dist_comm]
  have hdist_nonneg :
      0 ≤ dist (fourierMultiplier (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ) x) g := dist_nonneg
  exact (sq_lt_sq₀ hdist_nonneg hε.le).mp hdist_sq

/-- **Concrete Fourier Multiplier Contractive Resolvent on `L²(ℝ; ℂ)`**:
`R_μ f = 𝓕⁻¹ ((μ + ψ(·))⁻¹ • 𝓕 f)`. -/
noncomputable def fourierMultiplierResolvent (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ)
    (hψ_nonneg : ∀ ξ, 0 ≤ ψ ξ) : ContractiveResolvent L2C where
  operator μ := fourierMultiplier (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ)
  resolvent_identity α β := by
    let pSymbol : ℝ → ℂ := fun ξ =>
      ((((α : ℝ) + ψ ξ)⁻¹ * ((β : ℝ) + ψ ξ)⁻¹ : ℝ) : ℂ)
    have hp_meas : AEStronglyMeasurable pSymbol volume :=
      (Complex.continuous_ofReal.measurable.comp
        (((measurable_const.add hψ_meas).inv).mul
          ((measurable_const.add hψ_meas).inv))).aestronglyMeasurable
    have hp_bdd : ∀ ξ, ‖pSymbol ξ‖ ≤ (α : ℝ)⁻¹ * (β : ℝ)⁻¹ := fun ξ => by
      have ha : 0 < (α : ℝ) + ψ ξ := lt_of_lt_of_le α.2 (le_add_of_nonneg_right (hψ_nonneg ξ))
      have hb : 0 < (β : ℝ) + ψ ξ := lt_of_lt_of_le β.2 (le_add_of_nonneg_right (hψ_nonneg ξ))
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (inv_pos.mpr ha)
        (inv_pos.mpr hb))]
      exact mul_le_mul (inv_anti₀ α.2 (le_add_of_nonneg_right (hψ_nonneg ξ)))
        (inv_anti₀ β.2 (le_add_of_nonneg_right (hψ_nonneg ξ))) (inv_pos.mpr hb).le
        (inv_nonneg.mpr α.2.le)
    let diffSymbol : ℝ → ℂ := fun ξ => ((((β : ℝ) - (α : ℝ)) *
      (((α : ℝ) + ψ ξ)⁻¹ * ((β : ℝ) + ψ ξ)⁻¹) : ℝ) : ℂ)
    have hd_meas : AEStronglyMeasurable diffSymbol volume :=
      (Complex.continuous_ofReal.measurable.comp (measurable_const.mul
        (((measurable_const.add hψ_meas).inv).mul
          ((measurable_const.add hψ_meas).inv)))).aestronglyMeasurable
    have hd_bdd : ∀ ξ, ‖diffSymbol ξ‖ ≤ |(β : ℝ) - (α : ℝ)| * ((α : ℝ)⁻¹ * (β : ℝ)⁻¹) := by
      intro ξ
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      simpa only [pSymbol, Complex.norm_real, Real.norm_eq_abs] using hp_bdd ξ
    have hsub := fourierMultiplier_sub
      (resSymbol_aestronglyMeasurable ψ hψ_meas α) (inv_nonneg.mpr α.2.le)
      (norm_resSymbol_le_inv ψ hψ_nonneg α)
      (resSymbol_aestronglyMeasurable ψ hψ_meas β) (inv_nonneg.mpr β.2.le)
      (norm_resSymbol_le_inv ψ hψ_nonneg β)
      hd_meas (mul_nonneg (abs_nonneg _) (mul_nonneg (inv_nonneg.mpr α.2.le)
        (inv_nonneg.mpr β.2.le)))
      hd_bdd fun ξ => by
        have ha : (α : ℝ) + ψ ξ ≠ 0 :=
          (lt_of_lt_of_le α.2 (le_add_of_nonneg_right (hψ_nonneg ξ))).ne'
        have hb : (β : ℝ) + ψ ξ ≠ 0 :=
          (lt_of_lt_of_le β.2 (le_add_of_nonneg_right (hψ_nonneg ξ))).ne'
        rw [← Complex.ofReal_sub]
        congr 1
        field_simp
        ring
    have hcomp := fourierMultiplier_comp
      (resSymbol_aestronglyMeasurable ψ hψ_meas α) (inv_nonneg.mpr α.2.le)
      (norm_resSymbol_le_inv ψ hψ_nonneg α)
      (resSymbol_aestronglyMeasurable ψ hψ_meas β) (inv_nonneg.mpr β.2.le)
      (norm_resSymbol_le_inv ψ hψ_nonneg β)
      hp_meas (mul_nonneg (inv_nonneg.mpr α.2.le) (inv_nonneg.mpr β.2.le)) hp_bdd
      fun ξ => by
        rw [← Complex.ofReal_mul]
    have hsmul := fourierMultiplier_smul ((β : ℝ) - (α : ℝ))
      hp_meas (mul_nonneg (inv_nonneg.mpr α.2.le) (inv_nonneg.mpr β.2.le)) hp_bdd
      hd_meas (mul_nonneg (abs_nonneg _) (mul_nonneg (inv_nonneg.mpr α.2.le)
        (inv_nonneg.mpr β.2.le)))
      hd_bdd fun ξ => by
        rw [← Complex.ofReal_mul]
    unfold resMultiplierSymbol
    rw [hsub, hcomp, hsmul]
  opNorm_le_inv μ := by
    calc
      ‖fourierMultiplier (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ)‖
          ≤ ‖resMultiplierSymbol ψ hψ_meas hψ_nonneg μ‖ :=
        opNorm_fourierMultiplier_le _
      _ ≤ (μ : ℝ)⁻¹ :=
        norm_toLpTop_le (resSymbol_aestronglyMeasurable ψ hψ_meas μ) (inv_nonneg.mpr μ.2.le)
          (norm_resSymbol_le_inv ψ hψ_nonneg μ)
  denseRange := denseRange_resMultiplier ψ hψ_meas hψ_nonneg

/-! ### 4. Exact Hille–Yosida identification -/

/-- **Laplace-transform resolvent of `fourierMultiplierSemigroup` equals
`fourierMultiplierResolvent`**: checked weakly against every `g ∈ L²(ℝ; ℂ)` via Parseval's
identity and Fubini–Tonelli (`integral_integral_swap`). -/
theorem fourierMultiplierSemigroup_resolvent_eq (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ)
    (hψ_nonneg : ∀ ξ, 0 ≤ ψ ξ) (μ : PositiveShift) :
    (fourierMultiplierSemigroup ψ hψ_meas hψ_nonneg).resolvent μ =
      (fourierMultiplierResolvent ψ hψ_meas hψ_nonneg).operator μ := by
  ext1 f
  refine ext_inner_left ℂ fun g => ?_
  let S := fourierMultiplierSemigroup ψ hψ_meas hψ_nonneg
  let R := fourierMultiplierResolvent ψ hψ_meas hψ_nonneg
  have hLHS1 :
      ⟪g, S.resolvent μ f⟫ =
        ∫ t in Ioi (0 : ℝ), ⟪g, S.laplaceIntegrand μ f t⟫ := by
    rw [StronglyContinuousContractionSemigroup.resolvent_apply]
    exact ((innerSL ℂ g).restrictScalars ℝ).integral_comp_comm
      (S.integrableOn_laplaceIntegrand μ.2 f) |>.symm
  have hLHS2 :
      (∫ t in Ioi (0 : ℝ), ⟪g, S.laplaceIntegrand μ f t⟫) =
        ∫ t in Ioi (0 : ℝ),
          ∫ ξ : ℝ,
            ((Real.exp (-((μ : ℝ) + ψ ξ) * t) : ℝ) : ℂ) *
              ⟪((𝓕 g : L2C) : ℝ → ℂ) ξ, ((𝓕 f : L2C) : ℝ → ℂ) ξ⟫ := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht_nonneg : 0 ≤ t := ht.le
    rw [StronglyContinuousContractionSemigroup.laplaceIntegrand_apply,
      show Real.exp (-(μ : ℝ) * t) • S (Real.toNNReal t) f =
        ((Real.exp (-(μ : ℝ) * t) : ℝ) : ℂ) • S (Real.toNNReal t) f from rfl,
      inner_smul_right,
      show S (Real.toNNReal t) f =
        𝓕⁻ ((expMultiplierSymbol ψ hψ_meas hψ_nonneg (Real.toNNReal t) • 𝓕 f : L2C)) from rfl]
    have hparseval :
        ⟪g, 𝓕⁻ ((expMultiplierSymbol ψ hψ_meas hψ_nonneg (Real.toNNReal t) • 𝓕 f : L2C))⟫ =
          ⟪𝓕 g, (expMultiplierSymbol ψ hψ_meas hψ_nonneg (Real.toNNReal t) • 𝓕 f : L2C)⟫ := by
      have h1 := parseval_inner_eq g
        (𝓕⁻ ((expMultiplierSymbol ψ hψ_meas hψ_nonneg (Real.toNNReal t) • 𝓕 f : L2C)))
      rw [fourier_fourierInv_eq] at h1
      exact h1.symm
    rw [hparseval, L2.inner_def, ← smul_eq_mul, ← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_lpSMul (r := 2)
      (expMultiplierSymbol ψ hψ_meas hψ_nonneg (Real.toNNReal t)) (𝓕 f),
      coeFn_toLpTop (expSymbol_aestronglyMeasurable ψ hψ_meas (Real.toNNReal t)) zero_le_one
        (norm_expSymbol_le_one ψ hψ_nonneg (Real.toNNReal t).coe_nonneg)] with ξ hsmul hexp
    have hsmul' :
        ((expMultiplierSymbol ψ hψ_meas hψ_nonneg (Real.toNNReal t) • 𝓕 f : L2C) : ℝ → ℂ) ξ =
          (Real.exp (-t * ψ ξ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ := by
      have hpi :
          ((expMultiplierSymbol ψ hψ_meas hψ_nonneg (Real.toNNReal t) • 𝓕 f : L2C) : ℝ → ℂ) ξ =
            (expMultiplierSymbol ψ hψ_meas hψ_nonneg (Real.toNNReal t) : ℝ → ℂ) ξ *
              ((𝓕 f : L2C) : ℝ → ℂ) ξ := hsmul
      have hexp' :
          (expMultiplierSymbol ψ hψ_meas hψ_nonneg (Real.toNNReal t) : ℝ → ℂ) ξ =
            (Real.exp (-(Real.toNNReal t : ℝ) * ψ ξ) : ℂ) := hexp
      rw [hpi, hexp', Real.coe_toNNReal t ht_nonneg]
    have hprod_exp :
        (Real.exp (-(μ : ℝ) * t) : ℂ) * (Real.exp (-t * ψ ξ) : ℂ) =
          ((Real.exp (-((μ : ℝ) + ψ ξ) * t) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    have hinner_mul : ∀ (c a b : ℂ), ⟪a, c * b⟫ = c * ⟪a, b⟫ := fun c a b => by
      simpa only [smul_eq_mul] using inner_smul_right (𝕜 := ℂ) a b c
    rw [smul_eq_mul, hsmul', hinner_mul, ← mul_assoc, hprod_exp]
  have hfubini :
      Integrable
        (fun p : ℝ × ℝ =>
          ((Real.exp (-((μ : ℝ) + ψ p.2) * p.1) : ℝ) : ℂ) *
            ⟪((𝓕 g : L2C) : ℝ → ℂ) p.2, ((𝓕 f : L2C) : ℝ → ℂ) p.2⟫)
        ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    have hexp_int : Integrable (fun t : ℝ => Real.exp (-(μ : ℝ) * t))
        (volume.restrict (Ioi (0 : ℝ))) := exp_neg_integrableOn_Ioi 0 μ.2
    have hnorm_in :
        Integrable (fun ξ : ℝ => ‖⟪((𝓕 g : L2C) : ℝ → ℂ) ξ, ((𝓕 f : L2C) : ℝ → ℂ) ξ⟫‖) volume :=
      (L2.integrable_inner (𝓕 g) (𝓕 f)).norm
    have hprod_dom :
        Integrable
          (fun p : ℝ × ℝ =>
            Real.exp (-(μ : ℝ) * p.1) *
              ‖⟪((𝓕 g : L2C) : ℝ → ℂ) p.2, ((𝓕 f : L2C) : ℝ → ℂ) p.2⟫‖)
          ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
      hexp_int.mul_prod hnorm_in
    refine hprod_dom.mono' ?_ ?_
    · have hm_exp : Measurable fun p : ℝ × ℝ =>
          ((Real.exp (-((μ : ℝ) + ψ p.2) * p.1) : ℝ) : ℂ) :=
        Complex.continuous_ofReal.measurable.comp
          (Real.continuous_exp.measurable.comp
            (((measurable_const.add (hψ_meas.comp measurable_snd)).neg).mul measurable_fst))
      have hm_in : AEStronglyMeasurable
          (fun p : ℝ × ℝ => ⟪((𝓕 g : L2C) : ℝ → ℂ) p.2, ((𝓕 f : L2C) : ℝ → ℂ) p.2⟫)
          ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
        ((Lp.aestronglyMeasurable (𝓕 g)).inner (Lp.aestronglyMeasurable (𝓕 f))).comp_snd
      exact hm_exp.aestronglyMeasurable.mul hm_in
    · have hae_fst : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi (0 : ℝ))).prod volume), p.1 ∈ Ioi 0 :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
      filter_upwards [hae_fst] with ⟨t, ξ⟩ ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact Real.exp_le_exp.mpr (by nlinarith [ht.le, hψ_nonneg ξ])
  have hswap :=
    integral_integral_swap
      (f := fun (t : ℝ) (ξ : ℝ) =>
        ((Real.exp (-((μ : ℝ) + ψ ξ) * t) : ℝ) : ℂ) *
          ⟪((𝓕 g : L2C) : ℝ → ℂ) ξ, ((𝓕 f : L2C) : ℝ → ℂ) ξ⟫)
      hfubini
  have hRHS_eval :
      (∫ ξ : ℝ, ∫ t in Ioi (0 : ℝ),
          ((Real.exp (-((μ : ℝ) + ψ ξ) * t) : ℝ) : ℂ) *
            ⟪((𝓕 g : L2C) : ℝ → ℂ) ξ, ((𝓕 f : L2C) : ℝ → ℂ) ξ⟫) =
        ∫ ξ : ℝ,
          ((((μ : ℝ) + ψ ξ)⁻¹ : ℝ) : ℂ) *
            ⟪((𝓕 g : L2C) : ℝ → ℂ) ξ, ((𝓕 f : L2C) : ℝ → ℂ) ξ⟫ := by
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [integral_mul_const]
    have hreal :
        (∫ t in Ioi (0 : ℝ), ((Real.exp (-((μ : ℝ) + ψ ξ) * t) : ℝ) : ℂ)) =
          ((((μ : ℝ) + ψ ξ)⁻¹ : ℝ) : ℂ) := by
      have hpos : 0 < (μ : ℝ) + ψ ξ := lt_of_lt_of_le μ.2 (le_add_of_nonneg_right (hψ_nonneg ξ))
      have hcomm :
          (∫ t in Ioi (0 : ℝ), ((Real.exp (-((μ : ℝ) + ψ ξ) * t) : ℝ) : ℂ)) =
            ((∫ t in Ioi (0 : ℝ), Real.exp (-((μ : ℝ) + ψ ξ) * t) : ℝ) : ℂ) :=
        Complex.ofRealCLM.integral_comp_comm (exp_neg_integrableOn_Ioi 0 hpos)
      rw [hcomm, StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero hpos]
    rw [hreal]
  have hRHS2 :
      (∫ ξ : ℝ,
          ((((μ : ℝ) + ψ ξ)⁻¹ : ℝ) : ℂ) *
            ⟪((𝓕 g : L2C) : ℝ → ℂ) ξ, ((𝓕 f : L2C) : ℝ → ℂ) ξ⟫) =
        ⟪g, R.operator μ f⟫ := by
    have hparseval :
        ⟪g, R.operator μ f⟫ =
          ⟪𝓕 g, (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • 𝓕 f : L2C)⟫ := by
      have h1 := parseval_inner_eq g (R.operator μ f)
      have h2 :
          𝓕 (R.operator μ f) =
            (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • 𝓕 f : L2C) :=
        fourier_fourierInv_eq _
      rw [h2] at h1
      exact h1.symm
    rw [hparseval, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_lpSMul (r := 2) (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ) (𝓕 f),
      coeFn_toLpTop (resSymbol_aestronglyMeasurable ψ hψ_meas μ) (inv_nonneg.mpr μ.2.le)
        (norm_resSymbol_le_inv ψ hψ_nonneg μ)] with ξ hsmul hres
    have hsmul' :
        ((resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • 𝓕 f : L2C) : ℝ → ℂ) ξ =
          ((((μ : ℝ) + ψ ξ)⁻¹ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ := by
      have hpi :
          ((resMultiplierSymbol ψ hψ_meas hψ_nonneg μ • 𝓕 f : L2C) : ℝ → ℂ) ξ =
            (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ : ℝ → ℂ) ξ *
              ((𝓕 f : L2C) : ℝ → ℂ) ξ := hsmul
      have hres' :
          (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ : ℝ → ℂ) ξ =
            ((((μ : ℝ) + ψ ξ)⁻¹ : ℝ) : ℂ) := hres
      rw [hpi, hres']
    have hinner_mul : ∀ (c a b : ℂ), ⟪a, c * b⟫ = c * ⟪a, b⟫ := fun c a b => by
      simpa only [smul_eq_mul] using inner_smul_right (𝕜 := ℂ) a b c
    rw [hsmul', hinner_mul]
  rw [hLHS1, hLHS2, hswap, hRHS_eval, hRHS2]

/-- **Main Whole-Line Hille–Yosida Identification Theorem**:
The `C₀`-contraction semigroup generated via Yosida approximation from the concrete Fourier
multiplier resolvent `fourierMultiplierResolvent ψ ...` equals
`fourierMultiplierSemigroup ψ ...`. -/
theorem fourierMultiplierResolvent_generatedSemigroup_eq (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ)
    (hψ_nonneg : ∀ ξ, 0 ≤ ψ ξ) :
    (fourierMultiplierResolvent ψ hψ_meas hψ_nonneg).generatedSemigroup =
      fourierMultiplierSemigroup ψ hψ_meas hψ_nonneg := by
  have hres :
      (fourierMultiplierSemigroup ψ hψ_meas hψ_nonneg).toContractiveResolvent =
        fourierMultiplierResolvent ψ hψ_meas hψ_nonneg := by
    rw [StronglyContinuousContractionSemigroup.toContractiveResolvent]
    cases hR : fourierMultiplierResolvent ψ hψ_meas hψ_nonneg
    simp only [ContractiveResolvent.mk.injEq]
    funext μ
    calc
      (fourierMultiplierSemigroup ψ hψ_meas hψ_nonneg).resolvent μ
          = (fourierMultiplierResolvent ψ hψ_meas hψ_nonneg).operator μ :=
        fourierMultiplierSemigroup_resolvent_eq ψ hψ_meas hψ_nonneg μ
      _ = _ := by rw [hR]
  rw [← hres]
  exact (fourierMultiplierSemigroup ψ hψ_meas hψ_nonneg).generatedSemigroup_toContractiveResolvent

/-! ### 5. Specialization to the 1D fractional Laplacian -/

/-- Frequency symbol of the 1D fractional Laplacian `(-Δ)^(α/2)` in Mathlib's `exp(-2π i x ξ)`
Fourier convention: `ψ_α(ξ) = |2 π ξ|^α`. -/
noncomputable def fracLapSymbol (α : ℝ) (ξ : ℝ) : ℝ := |2 * Real.pi * ξ| ^ α

/-- Measurability of `fracLapSymbol α`. -/
theorem measurable_fracLapSymbol (α : ℝ) : Measurable (fracLapSymbol α) :=
  ((continuous_abs.comp (continuous_const.mul continuous_id)).measurable.pow_const α)

/-- Nonnegativity of `fracLapSymbol α`. -/
theorem fracLapSymbol_nonneg (α : ℝ) (ξ : ℝ) : 0 ≤ fracLapSymbol α ξ :=
  rpow_nonneg (abs_nonneg _) α

/-- **Concrete Whole-Line Fractional Heat `C₀`-Contraction Semigroup on `L²(ℝ; ℂ)`**:
`S_α(t) f = 𝓕⁻¹ (exp(-t |2π ξ|^α) • 𝓕 f)`. -/
noncomputable def fracLapSemigroup (α : ℝ) :
    StronglyContinuousContractionSemigroup L2C :=
  fourierMultiplierSemigroup (fracLapSymbol α) (measurable_fracLapSymbol α)
    (fracLapSymbol_nonneg α)

/-- **Concrete Whole-Line Fractional Laplacian Contractive Resolvent on `L²(ℝ; ℂ)`**:
`R_{μ, α} f = 𝓕⁻¹ ((μ + |2π ξ|^α)⁻¹ • 𝓕 f)`. -/
noncomputable def fracLapResolvent (α : ℝ) : ContractiveResolvent L2C :=
  fourierMultiplierResolvent (fracLapSymbol α) (measurable_fracLapSymbol α)
    (fracLapSymbol_nonneg α)

/-- **Exact Hille–Yosida Generation of the Whole-Line Fractional Heat Semigroup**:
The semigroup generated by `fracLapResolvent α` via Yosida approximations equals
`fracLapSemigroup α`. -/
theorem fracLapResolvent_generatedSemigroup_eq (α : ℝ) :
    (fracLapResolvent α).generatedSemigroup = fracLapSemigroup α :=
  fourierMultiplierResolvent_generatedSemigroup_eq (fracLapSymbol α)
    (measurable_fracLapSymbol α) (fracLapSymbol_nonneg α)

private theorem fourierMultiplierResolvent_one_add_eq (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ)
    (hψ_nonneg : ∀ ξ, 0 ≤ ψ ξ) {f : L2C}
    (hM : MemLp (fun ξ : ℝ => ((ψ ξ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ) 2 volume) :
    (fourierMultiplierResolvent ψ hψ_meas hψ_nonneg).operator ⟨1, Set.mem_Ioi.mpr one_pos⟩
      (f + 𝓕⁻ (hM.toLp (fun ξ : ℝ => ((ψ ξ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ))) = f := by
  let R := fourierMultiplierResolvent ψ hψ_meas hψ_nonneg
  let μ₁ : PositiveShift := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  let mLp : L2C := hM.toLp (fun ξ : ℝ => ((ψ ξ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ)
  let g : L2C := f + 𝓕⁻ mLp
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change 𝓕 (R.operator μ₁ g) = 𝓕 f
  have hF1 : 𝓕 (R.operator μ₁ g) =
      (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ₁ • 𝓕 g : L2C) :=
    fourier_fourierInv_eq _
  rw [hF1, Lp.ext_iff]
  have hFg : 𝓕 g = 𝓕 f + mLp := by
    change (Lp.fourierTransformₗᵢ ℝ ℂ) (f + 𝓕⁻ mLp) = (Lp.fourierTransformₗᵢ ℝ ℂ) f + mLp
    rw [LinearIsometryEquiv.map_add]
    change 𝓕 f + 𝓕 (𝓕⁻ mLp) = 𝓕 f + mLp
    rw [fourier_fourierInv_eq]
  rw [hFg]
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ₁)
      (𝓕 f + mLp),
    coeFn_toLpTop (resSymbol_aestronglyMeasurable ψ hψ_meas μ₁) (inv_nonneg.mpr μ₁.2.le)
      (norm_resSymbol_le_inv ψ hψ_nonneg μ₁),
    Lp.coeFn_add (𝓕 f) mLp, hM.coeFn_toLp] with ξ hsm hres hadd hm
  have hsm' :
      ((resMultiplierSymbol ψ hψ_meas hψ_nonneg μ₁ • (𝓕 f + mLp) : L2C) : ℝ → ℂ) ξ =
        (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ₁ : ℝ → ℂ) ξ *
          ((𝓕 f + mLp : L2C) : ℝ → ℂ) ξ := hsm
  have hres' :
      (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ₁ : ℝ → ℂ) ξ =
        ((((1 : ℝ) + ψ ξ)⁻¹ : ℝ) : ℂ) := hres
  have hadd' : ((𝓕 f + mLp : L2C) : ℝ → ℂ) ξ =
      ((𝓕 f : L2C) : ℝ → ℂ) ξ + (mLp : ℝ → ℂ) ξ := hadd
  have hm' : (mLp : ℝ → ℂ) ξ = ((ψ ξ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ := hm
  rw [hsm', hres', hadd', hm']
  have hpos : (1 : ℝ) + ψ ξ ≠ 0 := by linarith [hψ_nonneg ξ]
  have hc : (1 : ℂ) + (ψ ξ : ℂ) ≠ 0 := by exact_mod_cast hpos
  push_cast
  field_simp

/-- **Generator Domain and Formula for Fourier Multiplier Semigroups**:
`f ∈ D(L)` iff `ξ ↦ ψ ξ * (𝓕 f) ξ` is in `L²(ℝ; ℂ)`. When this holds, the generator acts by
`L f = -𝓕⁻¹ (ψ • 𝓕 f)`. -/
theorem fourierMultiplierSemigroup_mem_generatorDomain_iff (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ)
    (hψ_nonneg : ∀ ξ, 0 ≤ ψ ξ) (f : L2C) :
    f ∈ (fourierMultiplierSemigroup ψ hψ_meas hψ_nonneg).generatorDomain ↔
      MemLp (fun ξ : ℝ => ((ψ ξ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ) 2 volume := by
  let R := fourierMultiplierResolvent ψ hψ_meas hψ_nonneg
  have hgen : R.generatedSemigroup = fourierMultiplierSemigroup ψ hψ_meas hψ_nonneg :=
    fourierMultiplierResolvent_generatedSemigroup_eq ψ hψ_meas hψ_nonneg
  let μ₁ : PositiveShift := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  constructor
  · intro hf
    have hmemR : f ∈ R.generatedSemigroup.generatorDomain := hgen ▸ hf
    have hrange : f ∈ Set.range (R.operator μ₁) := by
      rw [← R.generatorDomain_eq_range μ₁]
      exact hmemR
    rcases hrange with ⟨g, rfl⟩
    have hFf :
        ((𝓕 (R.operator μ₁ g) : L2C) : ℝ → ℂ) =ᵐ[volume]
          fun ξ : ℝ => ((((1 : ℝ) + ψ ξ)⁻¹ : ℝ) : ℂ) * ((𝓕 g : L2C) : ℝ → ℂ) ξ := by
      have h1 : 𝓕 (R.operator μ₁ g) = (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ₁ • 𝓕 g : L2C) :=
        fourier_fourierInv_eq _
      rw [h1]
      filter_upwards [Lp.coeFn_lpSMul (r := 2) (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ₁) (𝓕 g),
        coeFn_toLpTop (resSymbol_aestronglyMeasurable ψ hψ_meas μ₁) (inv_nonneg.mpr μ₁.2.le)
          (norm_resSymbol_le_inv ψ hψ_nonneg μ₁)] with ξ hsm hres
      have hsm' :
          ((resMultiplierSymbol ψ hψ_meas hψ_nonneg μ₁ • 𝓕 g : L2C) : ℝ → ℂ) ξ =
            (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ₁ : ℝ → ℂ) ξ *
              ((𝓕 g : L2C) : ℝ → ℂ) ξ := hsm
      have hres' :
          (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ₁ : ℝ → ℂ) ξ =
            ((((1 : ℝ) + ψ ξ)⁻¹ : ℝ) : ℂ) := hres
      rw [hsm', hres']
    have hae :
        (fun ξ : ℝ => ((ψ ξ : ℝ) : ℂ) * ((𝓕 (R.operator μ₁ g) : L2C) : ℝ → ℂ) ξ) =ᵐ[volume]
          ((𝓕 g - 𝓕 (R.operator μ₁ g) : L2C) : ℝ → ℂ) := by
      filter_upwards [hFf, Lp.coeFn_sub (𝓕 g) (𝓕 (R.operator μ₁ g))] with ξ hFξ hsub
      have hpos : (1 : ℝ) + ψ ξ ≠ 0 := by linarith [hψ_nonneg ξ]
      have hsub' :
          ((𝓕 g - 𝓕 (R.operator μ₁ g) : L2C) : ℝ → ℂ) ξ =
            ((𝓕 g : L2C) : ℝ → ℂ) ξ - ((𝓕 (R.operator μ₁ g) : L2C) : ℝ → ℂ) ξ := hsub
      rw [hsub', hFξ]
      push_cast
      have hc : (1 : ℂ) + (ψ ξ : ℂ) ≠ 0 := by exact_mod_cast hpos
      field_simp
      ring
    exact (Lp.memLp (𝓕 g - 𝓕 (R.operator μ₁ g))).ae_eq hae.symm
  · intro hM
    let g : L2C := f + 𝓕⁻ (hM.toLp (fun ξ : ℝ => ((ψ ξ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ))
    have hRg : R.operator μ₁ g = f :=
      fourierMultiplierResolvent_one_add_eq ψ hψ_meas hψ_nonneg hM
    have hmemR : f ∈ R.generatedSemigroup.generatorDomain := by
      rw [← hRg]
      exact R.operator_mem_generatorDomain μ₁ g
    exact hgen ▸ hmemR

/-- **Action of the Infinitesimal Generator of `fourierMultiplierSemigroup`**:
for `f` in `D(L)` with `ψ • 𝓕 f ∈ L²`, `L f = -𝓕⁻¹ (ψ • 𝓕 f)`. -/
theorem generator_fourierMultiplierSemigroup_of_memLp (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ)
    (hψ_nonneg : ∀ ξ, 0 ≤ ψ ξ) {f : L2C}
    (hf : f ∈ (fourierMultiplierSemigroup ψ hψ_meas hψ_nonneg).generatorDomain)
    (hM : MemLp (fun ξ : ℝ => ((ψ ξ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ) 2 volume) :
    (fourierMultiplierSemigroup ψ hψ_meas hψ_nonneg).generator ⟨f, hf⟩ =
      -(𝓕⁻ (hM.toLp (fun ξ : ℝ => ((ψ ξ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ))) := by
  let R := fourierMultiplierResolvent ψ hψ_meas hψ_nonneg
  have hgen : R.generatedSemigroup = fourierMultiplierSemigroup ψ hψ_meas hψ_nonneg :=
    fourierMultiplierResolvent_generatedSemigroup_eq ψ hψ_meas hψ_nonneg
  let μ₁ : PositiveShift := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  let mLp : L2C := hM.toLp (fun ξ : ℝ => ((ψ ξ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ)
  let g : L2C := f + 𝓕⁻ mLp
  have hRg : R.operator μ₁ g = f :=
    fourierMultiplierResolvent_one_add_eq ψ hψ_meas hψ_nonneg hM
  have hmemR : f ∈ R.generatedSemigroup.generatorDomain := hgen ▸ hf
  have hactR : R.generatedSemigroup.generator ⟨f, hmemR⟩ = (1 : ℝ) • f - g :=
    R.generator_apply_of_operator_eq μ₁ hmemR hRg
  have hmatch : ∀ {T : StronglyContinuousContractionSemigroup L2C} (hT : R.generatedSemigroup = T)
      (hfT : f ∈ T.generatorDomain),
      T.generator ⟨f, hfT⟩ = R.generatedSemigroup.generator ⟨f, hmemR⟩ := by
    rintro T rfl hfT
    rfl
  rw [hmatch hgen hf, hactR, one_smul]
  dsimp only [g, mLp]
  rw [sub_add_cancel_left]

/-- **Generator Domain of `fracLapSemigroup α`**: `f ∈ D(-(−Δ)^(α/2))` iff
`ξ ↦ |2π ξ|^α * 𝓕 f ξ ∈ L²(ℝ; ℂ)`. -/
theorem fracLapSemigroup_mem_generatorDomain_iff (α : ℝ) (f : L2C) :
    f ∈ (fracLapSemigroup α).generatorDomain ↔
      MemLp (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ) 2 volume :=
  fourierMultiplierSemigroup_mem_generatorDomain_iff (fracLapSymbol α)
    (measurable_fracLapSymbol α) (fracLapSymbol_nonneg α) f

/-- **Generator Formula for `fracLapSemigroup α`**: on `D(-(−Δ)^(α/2))`, the generator acts by
`L f = -𝓕⁻¹ (|2π ξ|^α • 𝓕 f)`. -/
theorem generator_fracLapSemigroup_of_memLp (α : ℝ) {f : L2C}
    (hf : f ∈ (fracLapSemigroup α).generatorDomain)
    (hM : MemLp (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ)
      2 volume) :
    (fracLapSemigroup α).generator ⟨f, hf⟩ =
      -(𝓕⁻ (hM.toLp (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ))) :=
  generator_fourierMultiplierSemigroup_of_memLp (fracLapSymbol α)
    (measurable_fracLapSymbol α) (fracLapSymbol_nonneg α) hf hM

/-! ### 6. Concrete `L²(ℝ; ℂ)` Fourier convolution equivalence -/

/-- **L¹ ∩ L² Fourier Transform Consistency**:
If `f : ℝ → ℂ` is both integrable (`L¹`) and square-integrable (`L²`), then the `L²` Fourier
transform `𝓕 (hf2.toLp f)` agrees almost everywhere with the pointwise `L¹` Fourier integral
`𝓕 f`. -/
theorem coeFn_fourier_toLp_ae_eq_of_integrable {f : ℝ → ℂ} (hf1 : Integrable f volume)
    (hf2 : MemLp f 2 volume) :
    ((𝓕 (hf2.toLp f) : L2C) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  have hsub_ae : (fun ξ : ℝ => ((𝓕 (hf2.toLp f) : L2C) : ℝ → ℂ) ξ - 𝓕 f ξ) =ᵐ[volume] 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero ?_ ?_
    · exact ((Lp.memLp (𝓕 (hf2.toLp f))).locallyIntegrable (by norm_num)).sub
        (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
          (innerSL ℝ).continuous₂ hf1).locallyIntegrable
    · intro g hg_smooth hg_cpt
      let gc : ℝ → ℂ := Complex.ofRealCLM ∘ g
      have hgc_cpt : HasCompactSupport gc := hg_cpt.comp_left rfl
      have hgc_smooth : ContDiff ℝ (⊤ : ℕ∞) gc := Complex.ofRealCLM.contDiff.comp hg_smooth
      let φ : 𝓢(ℝ, ℂ) := hgc_cpt.toSchwartzMap hgc_smooth
      have hL2_pair :
          ∫ ξ : ℝ, gc ξ * ((𝓕 (hf2.toLp f) : L2C) : ℝ → ℂ) ξ = ∫ x : ℝ, (𝓕 φ) x * f x := by
        have hLHS :
            ∫ ξ : ℝ, gc ξ * ((𝓕 (hf2.toLp f) : L2C) : ℝ → ℂ) ξ =
              ((𝓕 (hf2.toLp f) : L2C) : 𝓢'(ℝ, ℂ)) φ := by
          rw [Lp.toTemperedDistribution_apply]
          refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
          change (g ξ : ℂ) * ((𝓕 (hf2.toLp f) : L2C) : ℝ → ℂ) ξ =
            φ ξ * ((𝓕 (hf2.toLp f) : L2C) : ℝ → ℂ) ξ
          rfl
        have hRHS : ((hf2.toLp f : 𝓢'(ℝ, ℂ))) (𝓕 φ) = ∫ x : ℝ, (𝓕 φ) x * f x := by
          rw [Lp.toTemperedDistribution_apply]
          refine integral_congr_ae ?_
          filter_upwards [hf2.coeFn_toLp] with x hx
          rw [hx]
          rfl
        have hdist := congrArg (fun T : 𝓢'(ℝ, ℂ) => T φ)
          (Lp.fourier_toTemperedDistribution_eq (hf2.toLp f))
        rw [TemperedDistribution.fourier_apply] at hdist
        rw [hLHS, ← hdist, hRHS]
      have hL1_pair :
          ∫ ξ : ℝ, gc ξ * 𝓕 f ξ = ∫ x : ℝ, (𝓕 φ) x * f x := by
        have hflip := VectorFourier.integral_fourierIntegral_smul_eq_flip
          (L := innerₗ ℝ)
          Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf1 (φ.integrable (μ := volume))
        have hflip_L : (innerₗ ℝ).flip = innerₗ ℝ :=
          LinearMap.ext fun u => LinearMap.ext fun v => by
            change inner ℝ v u = inner ℝ u v
            exact real_inner_comm u v
        rw [hflip_L] at hflip
        have h1 : (∫ ξ : ℝ, 𝓕 f ξ * φ ξ) = ∫ x : ℝ, f x * (𝓕 φ) x := by
          simp_rw [SchwartzMap.fourier_coe]
          exact hflip
        have h0 : (∫ ξ : ℝ, gc ξ * 𝓕 f ξ) = ∫ ξ : ℝ, 𝓕 f ξ * φ ξ := by
          refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
          change (g ξ : ℂ) * 𝓕 f ξ = 𝓕 f ξ * φ ξ
          rw [mul_comm]
          rfl
        have h2 : (∫ x : ℝ, f x * (𝓕 φ) x) = ∫ x : ℝ, (𝓕 φ) x * f x := by
          refine integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
        exact h0.trans (h1.trans h2)
      have hbound :
          Integrable (fun ξ : ℝ => gc ξ * ((𝓕 (hf2.toLp f) : L2C) : ℝ → ℂ) ξ) volume := by
        have hφ2 : MemLp (φ : ℝ → ℂ) 2 volume := φ.memLp 2
        refine (hφ2.integrable_mul (Lp.memLp (𝓕 (hf2.toLp f)))).congr
          (Eventually.of_forall fun ξ => rfl)
      have hbound1 : Integrable (fun ξ : ℝ => gc ξ * 𝓕 f ξ) volume := by
        have hcont_bdd : ∃ C, ∀ ξ : ℝ, ‖𝓕 f ξ‖ ≤ C :=
          ⟨∫ x : ℝ, ‖f x‖, fun ξ => Real.norm_fourier_le_integral_norm f ξ⟩
        rcases hcont_bdd with ⟨C, hC⟩
        have hF_meas : AEStronglyMeasurable (𝓕 f) volume :=
          (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
            (innerSL ℝ).continuous₂ hf1).aestronglyMeasurable
        exact ((memLp_top_of_bound hF_meas C (Eventually.of_forall hC)).integrable_mul
          (memLp_one_iff_integrable.mpr φ.integrable)).congr
            (Eventually.of_forall fun ξ => mul_comm _ _)
      have hzero :
          ∫ ξ : ℝ, g ξ • (((𝓕 (hf2.toLp f) : L2C) : ℝ → ℂ) ξ - 𝓕 f ξ) = 0 := by
        have hcongr :
            (fun ξ : ℝ => g ξ • (((𝓕 (hf2.toLp f) : L2C) : ℝ → ℂ) ξ - 𝓕 f ξ)) =
              fun ξ : ℝ => gc ξ * ((𝓕 (hf2.toLp f) : L2C) : ℝ → ℂ) ξ - gc ξ * 𝓕 f ξ := by
          funext ξ
          simp only [gc, Function.comp_apply, Complex.ofRealCLM_apply, Complex.real_smul]
          ring
        rw [hcongr, integral_sub hbound hbound1, hL2_pair, hL1_pair, sub_self]
      exact hzero
  filter_upwards [hsub_ae] with ξ hξ
  exact sub_eq_zero.mp hξ

/-- On `L²(ℝ; ℂ)`, `𝓕⁻ g` agrees a.e. with the spatial reflection `x ↦ (𝓕 g) (-x)`. -/
theorem coeFn_fourierInv_ae_eq_fourier_neg (g : L2C) :
    ((𝓕⁻ g : L2C) : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => ((𝓕 g : L2C) : ℝ → ℂ) (-x) := by
  let negL2 : L2C →L[ℝ] L2C :=
    (Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := ℂ) (p := 2)
      (μ := (volume : Measure ℝ)) (μb := (volume : Measure ℝ))
      Neg.neg (Measure.measurePreserving_neg (volume : Measure ℝ))).toContinuousLinearMap
  have heq : (fun h : L2C => (𝓕⁻ h : L2C)) = fun h : L2C => negL2 (𝓕 h) := by
    refine (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2)
      ENNReal.ofNat_ne_top).equalizer
      (Lp.fourierTransformₗᵢ ℝ ℂ).symm.continuous
      (negL2.continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous) ?_
    ext1 φ
    change 𝓕⁻ (φ.toLp 2) = negL2 (𝓕 (φ.toLp 2))
    rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourierInv_eq, Lp.ext_iff]
    have hcoe := Lp.coeFn_compMeasurePreserving ((𝓕 φ).toLp 2)
      (Measure.measurePreserving_neg (volume : Measure ℝ))
    have href := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      ((𝓕 φ).coeFn_toLp 2 volume)
    filter_upwards [(𝓕⁻ φ).coeFn_toLp 2 volume, hcoe, href] with x h1 h2 h3
    have h1' : (((𝓕⁻ φ).toLp 2 volume : L2C) : ℝ → ℂ) x =
        ((𝓕⁻ φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x := h1
    have h2' : (negL2 ((𝓕 φ).toLp 2 volume) : ℝ → ℂ) x =
        (((𝓕 φ).toLp 2 volume : L2C) : ℝ → ℂ) (-x) := h2
    rw [h1', h2', h3, SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe]
    exact Real.fourierInv_eq_fourier_neg (φ : ℝ → ℂ) x
  have hgx := congrFun heq g
  have hg2 := Lp.coeFn_compMeasurePreserving (𝓕 g)
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  change (𝓕⁻ g : L2C) = negL2 (𝓕 g) at hgx
  rw [hgx]
  exact hg2

/-- **L¹ ∩ L² Inverse Fourier Transform Consistency**:
If `f : ℝ → ℂ` is both integrable (`L¹`) and square-integrable (`L²`), then the `L²` inverse
Fourier transform `𝓕⁻ (hf2.toLp f)` agrees a.e. with the pointwise `L¹` inverse Fourier integral
`𝓕⁻ f`. -/
theorem coeFn_fourierInv_toLp_ae_eq_of_integrable {f : ℝ → ℂ} (hf1 : Integrable f volume)
    (hf2 : MemLp f 2 volume) :
    ((𝓕⁻ (hf2.toLp f) : L2C) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ f := by
  have h1 := coeFn_fourierInv_ae_eq_fourier_neg (hf2.toLp f)
  have h2 := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
    (coeFn_fourier_toLp_ae_eq_of_integrable hf1 hf2)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1]
  change ((𝓕 (hf2.toLp f) : L2C) : ℝ → ℂ) (-x) = (𝓕 f) (-x) at hx2
  rw [hx2]
  exact (Real.fourierInv_eq_fourier_neg f x).symm

/-- **Concrete `L²(ℝ; ℂ)` Fourier Convolution Equivalence**:
If `K ∈ L¹(ℝ; ℂ)` has `L^∞` Fourier transform `m` (`m =ᵐ 𝓕 K`) and `u ∈ 𝓢(ℝ, ℂ)` is a Schwartz
initial datum such that `K ⋆ u ∈ L²(ℝ; ℂ)`, then the concrete `L²` Fourier multiplier
`fourierMultiplier m (u.toLp 2)` equals `K ⋆ u` in `L²(ℝ; ℂ)`. -/
theorem fourierMultiplier_eq_conv_toLp {K : ℝ → ℂ} (hK : Integrable K volume)
    {m : Lp (α := ℝ) ℂ ∞ volume} (hm : (m : ℝ → ℂ) =ᵐ[volume] 𝓕 K)
    (u : 𝓢(ℝ, ℂ)) (hKu : MemLp (K ⋆[ContinuousLinearMap.mul ℂ ℂ] (u : ℝ → ℂ)) 2 volume) :
    fourierMultiplier m (u.toLp 2) =
      hKu.toLp (K ⋆[ContinuousLinearMap.mul ℂ ℂ] (u : ℝ → ℂ)) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change 𝓕 (fourierMultiplier m (u.toLp 2)) =
    𝓕 (hKu.toLp (K ⋆[ContinuousLinearMap.mul ℂ ℂ] (u : ℝ → ℂ)))
  rw [fourierMultiplier_apply, fourier_fourierInv_eq, Lp.ext_iff]
  have hKu1 : Integrable (K ⋆[ContinuousLinearMap.mul ℂ ℂ] (u : ℝ → ℂ)) volume :=
    hK.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) u.integrable
  have hRHS_ae := coeFn_fourier_toLp_ae_eq_of_integrable hKu1 hKu
  filter_upwards [Lp.coeFn_lpSMul (r := 2) m (𝓕 (u.toLp 2)), hm, hRHS_ae,
    (𝓕 u).coeFn_toLp 2 volume] with ξ hsmul hm_ae hKu_ae hu_ae
  have hLHS :
      ((m • 𝓕 (u.toLp 2) : L2C) : ℝ → ℂ) ξ = 𝓕 K ξ * 𝓕 (u : ℝ → ℂ) ξ := by
    have hpi :
        ((m • 𝓕 (u.toLp 2) : L2C) : ℝ → ℂ) ξ =
          (m : ℝ → ℂ) ξ * ((𝓕 (u.toLp 2) : L2C) : ℝ → ℂ) ξ := hsmul
    rw [hpi, hm_ae, SchwartzMap.toLp_fourier_eq, hu_ae, SchwartzMap.fourier_coe]
  rw [hLHS, hKu_ae, Real.fourier_mul_convolution_eq hK u.integrable ξ]

end

end FracLap
