/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.GagliardoFourier
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# FracLap.WholeLine.GagliardoDensity

Density of real Schwartz functions in the concrete Gagliardo space `H^(α / 2)(ℝ)` for
`α ∈ (0, 2)`, obtained from the complex density theorem of `GagliardoFourier` by taking real parts:
- `gagliardoEnergyR`, `gagliardoMk`: build an element of `GagliardoSpace α` from an `L²`
  function of finite Gagliardo energy.
- `ofReal_norm_sq_gagliardoSpace`: `‖v‖² = ‖v_{L²}‖² + E_α(v_{L²})` in `GagliardoSpace α`.
- `reL2`, `ofRealL2` and the energy comparisons `gagliardoEnergyR_reL2_le`,
  `gagliardoEnergyC_ofRealL2`: real parts do not increase `‖·‖² + E_α`.
- `gagliardoEnergyC_schwartz_lt_top`: Schwartz functions have finite Gagliardo energy.
- `exists_schwartz_close_real`: for every `u : GagliardoSpace α` and `ε > 0` there is a real
  Schwartz function `φ` with `‖gagliardoMk φ - u‖ < ε`.
-/

namespace FracLap

open Complex Filter FourierTransform MeasureTheory Real Set Topology
open scoped ENNReal NNReal ComplexInnerProductSpace SchwartzMap

@[expose] public section

/-- The Gagliardo energy of a real `L²` function. -/
noncomputable def gagliardoEnergyR (α : ℝ) (g : L2R) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ, gagliardoWeight α p *
    ENNReal.ofReal (((g : ℝ → ℝ) p.1 - (g : ℝ → ℝ) p.2) ^ 2) ∂((volume : Measure ℝ).prod volume)

/-- A real `L²` function of finite Gagliardo energy has an `L²(gagliardoMeasure α)` difference
quotient. -/
theorem integrable_sq_diff_of_energy {α : ℝ} (g : L2R) (hg : gagliardoEnergyR α g < ∞) :
    MemLp (fun p : ℝ × ℝ => (g : ℝ → ℝ) p.1 - (g : ℝ → ℝ) p.2) 2 (gagliardoMeasure α) := by
  have hm : Measurable (g : ℝ → ℝ) := (Lp.stronglyMeasurable g).measurable
  have hF : Measurable fun p : ℝ × ℝ => (g : ℝ → ℝ) p.1 - (g : ℝ → ℝ) p.2 :=
    (hm.comp measurable_fst).sub (hm.comp measurable_snd)
  refine (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).2
    ⟨(hF.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => sq_nonneg _)]
  unfold gagliardoMeasure
  have hg' : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (((g : ℝ → ℝ) p.1 - (g : ℝ → ℝ) p.2) ^ 2) :=
    ENNReal.measurable_ofReal.comp (hF.pow_const 2)
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_gagliardoWeight α) hg']
  exact hg

/-- The difference quotient of `g` as an element of `L²(gagliardoMeasure α)`. -/
noncomputable def gagliardoDiffL2 {α : ℝ} (g : L2R) (hg : gagliardoEnergyR α g < ∞) :
    L2Gagliardo α :=
  (integrable_sq_diff_of_energy g hg).toLp _

/-- `(g, diff g)` lies in the Gagliardo graph subspace. -/
theorem gagliardoMk_mem {α : ℝ} (g : L2R) (hg : gagliardoEnergyR α g < ∞) :
    (WithLp.toLp 2 (g, gagliardoDiffL2 g hg) : GagliardoAmbient α) ∈ gagliardoSubmodule α := by
  change ∀ᵐ p : ℝ × ℝ ∂gagliardoMeasure α, (gagliardoDiffL2 g hg : ℝ × ℝ → ℝ) p =
    (g : ℝ → ℝ) p.1 - (g : ℝ → ℝ) p.2
  exact (integrable_sq_diff_of_energy g hg).coeFn_toLp

/-- Build an element of `H^(α / 2)(ℝ)` from an `L²` function of finite Gagliardo energy. -/
noncomputable def gagliardoMk {α : ℝ} (g : L2R) (hg : gagliardoEnergyR α g < ∞) :
    GagliardoSpace α :=
  ⟨_, gagliardoMk_mem g hg⟩

/-- The `L²` component of `gagliardoMk g` is `g`. -/
theorem gagliardoL2Part_mk {α : ℝ} (g : L2R) (hg : gagliardoEnergyR α g < ∞) :
    gagliardoL2Part α (gagliardoMk g hg) = g := rfl

/-- General-measure squared `L²` norm as a lintegral. -/
theorem lintegral_enorm_sq_eq_general {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} (g : Lp (α := X) E 2 μ) :
    ∫⁻ x, ‖(g : X → E) x‖ₑ ^ (2 : ℝ) ∂μ = ‖g‖ₑ ^ (2 : ℝ) := by
  rw [lintegral_rpow_eNorm_eq_rpow_eLpNorm' (μ := μ) two_pos, Lp.eNorm_def,
    eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top]
  · norm_num
  · exact Lp.aestronglyMeasurable g

/-- **Norm in `H^(α / 2)(ℝ)`**: `‖v‖² = ‖v_{L²}‖² + E_α(v_{L²})`. -/
theorem ofReal_norm_sq_gagliardoSpace (α : ℝ) (v : GagliardoSpace α) :
    ENNReal.ofReal (‖v‖ ^ 2) =
      ENNReal.ofReal (‖gagliardoL2Part α v‖ ^ 2) + gagliardoEnergyR α (gagliardoL2Part α v) := by
  rw [norm_sq_gagliardoSpace, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  congr 1
  have hm : Measurable (gagliardoL2Part α v : ℝ → ℝ) := (Lp.stronglyMeasurable _).measurable
  have hF : Measurable fun p : ℝ × ℝ =>
      (gagliardoL2Part α v : ℝ → ℝ) p.1 - (gagliardoL2Part α v : ℝ → ℝ) p.2 :=
    (hm.comp measurable_fst).sub (hm.comp measurable_snd)
  have hae : (gagliardoDiffPart α v : ℝ × ℝ → ℝ) =ᵐ[gagliardoMeasure α]
      fun p => (gagliardoL2Part α v : ℝ → ℝ) p.1 - (gagliardoL2Part α v : ℝ → ℝ) p.2 := v.2
  have hsq : ENNReal.ofReal (‖gagliardoDiffPart α v‖ ^ 2) =
      ∫⁻ p, ‖(gagliardoDiffPart α v : ℝ × ℝ → ℝ) p‖ₑ ^ (2 : ℝ) ∂gagliardoMeasure α := by
    rw [lintegral_enorm_sq_eq_general, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg
      (norm_nonneg _) (by norm_num), Real.rpow_two]
  rw [hsq, lintegral_congr_ae (hae.mono fun p hp => by rw [hp])]
  unfold gagliardoEnergyR
  have hg' : Measurable fun p : ℝ × ℝ =>
      ‖(gagliardoL2Part α v : ℝ → ℝ) p.1 - (gagliardoL2Part α v : ℝ → ℝ) p.2‖ₑ ^ (2 : ℝ) :=
    hF.eNorm.pow_const _
  have key : ∀ G : ℝ × ℝ → ℝ≥0∞, Measurable G →
      ∫⁻ p, G p ∂gagliardoMeasure α =
        ∫⁻ p, (gagliardoWeight α * G) p ∂((volume : Measure ℝ).prod volume) :=
    fun G hG => lintegral_withDensity_eq_lintegral_mul _ (measurable_gagliardoWeight α) hG
  rw [key _ hg']
  refine lintegral_congr fun p => ?_
  simp only [Pi.mul_apply]
  rw [enorm_rpow_two_eq_ofReal, Real.norm_eq_abs, sq_abs]

/-- Real part as a continuous linear map `L²(ℝ; ℂ) → L²(ℝ; ℝ)`. -/
noncomputable def reL2 : L2C →L[ℝ] L2R := Complex.reCLM.compLpL 2 volume

/-- Inclusion of real functions as a continuous linear map `L²(ℝ; ℝ) → L²(ℝ; ℂ)`. -/
noncomputable def ofRealL2 : L2R →L[ℝ] L2C := Complex.ofRealCLM.compLpL 2 volume

/-- A.e. values of `reL2`. -/
theorem coeFn_reL2 (h : L2C) : (reL2 h : ℝ → ℝ) =ᵐ[volume] fun x => ((h : ℝ → ℂ) x).re :=
  ContinuousLinearMap.coeFn_compLpL Complex.reCLM h

/-- A.e. values of `ofRealL2`. -/
theorem coeFn_ofRealL2 (g : L2R) :
    (ofRealL2 g : ℝ → ℂ) =ᵐ[volume] fun x => (((g : ℝ → ℝ) x : ℝ) : ℂ) :=
  ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM g

/-- The real part of the complexification of `g` is `g`. -/
theorem reL2_ofRealL2 (g : L2R) : reL2 (ofRealL2 g) = g := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_reL2 (ofRealL2 g), coeFn_ofRealL2 g] with x h1 h2
  rw [h1, h2]
  simp

/-- Transfer an a.e. statement on `ℝ` to the first coordinate of Lebesgue product measure. -/
theorem ae_prod_fst {P : ℝ → Prop} (h : ∀ᵐ x : ℝ ∂volume, P x) :
    ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod volume), P p.1 :=
  Measure.quasiMeasurePreserving_fst.ae h

/-- Transfer an a.e. statement on `ℝ` to the second coordinate of Lebesgue product measure. -/
theorem ae_prod_snd {P : ℝ → Prop} (h : ∀ᵐ x : ℝ ∂volume, P x) :
    ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod volume), P p.2 :=
  Measure.quasiMeasurePreserving_snd.ae h

/-- Taking real parts does not increase the Gagliardo energy. -/
theorem gagliardoEnergyR_reL2_le (α : ℝ) (h : L2C) :
    gagliardoEnergyR α (reL2 h) ≤ gagliardoEnergyC α h := by
  unfold gagliardoEnergyR gagliardoEnergyC
  refine lintegral_mono_ae ?_
  filter_upwards [ae_prod_fst (coeFn_reL2 h), ae_prod_snd (coeFn_reL2 h)] with p h1 h2
  rw [h1, h2, enorm_rpow_two_eq_ofReal]
  refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
  rw [← Complex.sub_re]
  calc ((((h : ℝ → ℂ) p.1 - (h : ℝ → ℂ) p.2)).re) ^ 2
      ≤ ‖(h : ℝ → ℂ) p.1 - (h : ℝ → ℂ) p.2‖ ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2

/-- The complexification of `g` has the same Gagliardo energy as `g`. -/
theorem gagliardoEnergyC_ofRealL2 (α : ℝ) (g : L2R) :
    gagliardoEnergyC α (ofRealL2 g) = gagliardoEnergyR α g := by
  unfold gagliardoEnergyR gagliardoEnergyC
  refine lintegral_congr_ae ?_
  filter_upwards [ae_prod_fst (coeFn_ofRealL2 g), ae_prod_snd (coeFn_ofRealL2 g)] with p h1 h2
  rw [h1, h2, ← Complex.ofReal_sub, enorm_rpow_two_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]

/-- Taking real parts does not increase the squared `L²` norm. -/
theorem enorm_sq_reL2_le (h : L2C) : ‖reL2 h‖ₑ ^ (2 : ℝ) ≤ ‖h‖ₑ ^ (2 : ℝ) := by
  rw [← lintegral_enorm_sq_eq_general, ← lintegral_enorm_sq_eq_general]
  refine lintegral_mono_ae ?_
  filter_upwards [coeFn_reL2 h] with x hx
  rw [hx]
  gcongr
  rw [← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm ((h : ℝ → ℂ) x)

/-- The complexification preserves the squared `L²` norm. -/
theorem enorm_sq_ofRealL2 (g : L2R) : ‖ofRealL2 g‖ₑ ^ (2 : ℝ) = ‖g‖ₑ ^ (2 : ℝ) := by
  rw [← lintegral_enorm_sq_eq_general, ← lintegral_enorm_sq_eq_general]
  refine lintegral_congr_ae ?_
  filter_upwards [coeFn_ofRealL2 g] with x hx
  rw [hx, enorm_rpow_two_eq_ofReal, enorm_rpow_two_eq_ofReal, Complex.norm_real]

/-- Schwartz functions have finite Gagliardo energy. -/
theorem gagliardoEnergyC_schwartz_lt_top {α : ℝ} (hα : FractionalExponent α) (φ : 𝓢(ℝ, ℂ)) :
    gagliardoEnergyC α (φ.toLp 2 volume : L2C) < ∞ := by
  have := gagliardoSpectralMeasure_hasTemperateGrowth hα
  have := gagliardoSpectralMeasure_isFiniteMeasureOnCompacts hα
  set ν := gagliardoSpectralMeasure α with hν
  have hνac : ν ≪ (volume : Measure ℝ) := withDensity_absolutelyContinuous _ _
  have hF : 𝓕 (φ.toLp 2 volume : L2C) = ((𝓕 φ).toLp 2 volume : L2C) :=
    SchwartzMap.toLp_fourier_eq φ
  have hmain := norm_sq_add_energy_eq α (φ.toLp 2 volume : L2C)
  have hfin : ∫⁻ ξ, ‖(𝓕 (φ.toLp 2 volume : L2C) : L2C) ξ‖ₑ ^ (2 : ℝ) ∂ν < ∞ := by
    have hae : ((𝓕 (φ.toLp 2 volume : L2C) : L2C) : ℝ → ℂ) =ᵐ[ν] fun ξ => (𝓕 φ) ξ := by
      refine hνac.ae_le ?_
      rw [hF]
      exact (𝓕 φ).coeFn_toLp 2 volume
    obtain ⟨G, hG⟩ : ∃ G : Lp (α := ℝ) ℂ 2 ν, G = (𝓕 φ).toLp 2 ν := ⟨_, rfl⟩
    have hae2 : (G : ℝ → ℂ) =ᵐ[ν] fun ξ => (𝓕 φ) ξ := by
      rw [hG]; exact (𝓕 φ).coeFn_toLp 2 ν
    have hGfin : ‖G‖ₑ ^ (2 : ℝ) < ∞ := by
      refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
      rw [Lp.eNorm_def]
      exact Lp.eLpNorm_ne_top G
    calc ∫⁻ ξ, ‖(𝓕 (φ.toLp 2 volume : L2C) : L2C) ξ‖ₑ ^ (2 : ℝ) ∂ν
        = ∫⁻ ξ, ‖(G : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) ∂ν := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae, hae2] with ξ h1 h2
          rw [h1, h2]
      _ = ‖G‖ₑ ^ (2 : ℝ) := lintegral_enorm_sq_eq_general G
      _ < ∞ := hGfin
  rw [← hmain] at hfin
  exact lt_of_le_of_lt le_add_self hfin

/-- **Density of real Schwartz functions in `H^(α / 2)(ℝ)`**: for `α ∈ (0, 2)`, every element
`u` of the Gagliardo space is approximated, in the Gagliardo norm, by a real Schwartz function
`φ` (viewed in the Gagliardo space through `gagliardoMk`). -/
theorem exists_schwartz_close_real {α : ℝ} (hα : FractionalExponent α) (u : GagliardoSpace α)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (φ : 𝓢(ℝ, ℝ)) (hφ : gagliardoEnergyR α (φ.toLp 2 volume : L2R) < ∞),
      ‖gagliardoMk (φ.toLp 2 volume : L2R) hφ - u‖ < ε := by
  set g0 : L2R := gagliardoL2Part α u with hg0
  have hu := ofReal_norm_sq_gagliardoSpace α u
  have hEg0 : gagliardoEnergyR α g0 < ∞ :=
    lt_of_le_of_lt le_add_self (hu ▸ ENNReal.ofReal_lt_top)
  set f : L2C := ofRealL2 g0 with hf
  have hEf : gagliardoEnergyC α f < ∞ := by
    rw [hf, gagliardoEnergyC_ofRealL2]; exact hEg0
  obtain ⟨φc, hφc⟩ := exists_schwartz_close_complex hα f hEf (sq_pos_of_pos hε)
  set φ : 𝓢(ℝ, ℝ) := SchwartzMap.postcompCLM Complex.reCLM φc with hφ
  have hφL : (φ.toLp 2 volume : L2R) = reL2 (φc.toLp 2 volume : L2C) := by
    rw [Lp.ext_iff]
    filter_upwards [φ.coeFn_toLp 2 volume, coeFn_reL2 (φc.toLp 2 volume : L2C),
      φc.coeFn_toLp 2 volume] with x h1 h2 h3
    have h1' : (φ.toLp 2 volume : L2R) x = φ x := h1
    have h3' : ((φc.toLp 2 volume : L2C) : ℝ → ℂ) x = φc x := h3
    rw [h1', h2, h3']
    simp [hφ]
  have hEφ : gagliardoEnergyR α (φ.toLp 2 volume : L2R) < ∞ := by
    rw [hφL]
    exact lt_of_le_of_lt (gagliardoEnergyR_reL2_le α _) (gagliardoEnergyC_schwartz_lt_top hα φc)
  refine ⟨φ, hEφ, ?_⟩
  set v : GagliardoSpace α := gagliardoMk (φ.toLp 2 volume : L2R) hEφ with hv
  set D : L2C := (φc.toLp 2 volume : L2C) - f with hD
  have hL2 : gagliardoL2Part α (v - u) = reL2 D := by
    rw [map_sub, hD, map_sub, reL2_ofRealL2, ← hφL]
    rfl
  have hnorm := ofReal_norm_sq_gagliardoSpace α (v - u)
  rw [hL2] at hnorm
  have hlt : ENNReal.ofReal (‖v - u‖ ^ 2) < ENNReal.ofReal (ε ^ 2) := by
    rw [hnorm]
    calc ENNReal.ofReal (‖reL2 D‖ ^ 2) + gagliardoEnergyR α (reL2 D)
        ≤ ‖D‖ₑ ^ (2 : ℝ) + gagliardoEnergyC α D := by
          gcongr
          · rw [← enorm_rpow_two_eq_ofReal]
            exact enorm_sq_reL2_le D
          · exact gagliardoEnergyR_reL2_le α D
      _ < ENNReal.ofReal (ε ^ 2) := hφc
  have := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hlt
  exact lt_of_pow_lt_pow_left₀ 2 hε.le this

end

end FracLap
