/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.AnomalousDiffusion
public import FracLap.WholeLine.ClassicalKernels
public import FracLap.WholeLine.StableKernelPositivity
public import FracLap.WholeLine.StableKernelDecay
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLap.WholeLine.StableHeatKernel

Full Fourier-inversion construction of the symmetric `α`-stable fractional heat kernel
`FractionalHeatKernel α` for every fractional exponent `0 < α < 2`:
- `continuous_stableKernel`: continuity of `x ↦ stableKernel α x t` for `t > 0`.
- `integrable_stableKernel`: spatial integrability `stableKernel α · t ∈ L¹(ℝ)` from the
  algebraic unit-time tail decay and self-similar scaling.
- `fourier_stableSymbol_eq_stableKernel` and `fourierInv_stableSymbol_eq_stableKernel`:
  explicit identification of the Mathlib `2π`-normalized Fourier transform of
  `ξ ↦ exp (-t |2π ξ|^α)` with `stableKernel α · t`.
- `fourier_stableKernel_eq`: **Fourier faithfulness witness**
  `𝓕 (stableKernel α · t) ξ = exp (-t |2π ξ|^α)`, proved via `Continuous.fourier_fourierInv_eq`.
- `integral_stableKernel_eq_one`: unit total mass `∫ x, stableKernel α x t = 1` from `ξ = 0`.
- `stableHeatKernel`: concrete `FractionalHeatKernel α` instance for all `0 < α < 2`.
- `stableHeatKernel_one_eq_cauchy`: exact agreement with `cauchyHeatKernel` at `α = 1`.
-/

namespace FracLap

open Complex FourierTransform MeasureTheory Real Set Filter Topology

@[expose] public section

/-! ### Continuity and spatial integrability of `stableKernel` -/

/-- For `α, t > 0`, the kernel `x ↦ stableKernel α x t` is continuous on `ℝ`. -/
theorem continuous_stableKernel {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    Continuous fun x : ℝ => stableKernel α x t := by
  have hcongr :
      (fun x : ℝ => stableKernel α x t) =
        fun x : ℝ => (2 * π)⁻¹ * ∫ ω : ℝ, Real.cos (x * ω) * Real.exp (-t * |ω| ^ α) := by
    ext x
    exact stableKernel_eq_integral x t
  rw [hcongr]
  refine continuous_const.mul ?_
  refine continuous_of_dominated
    (F := fun x ω : ℝ => Real.cos (x * ω) * Real.exp (-t * |ω| ^ α))
    (bound := fun ω : ℝ => Real.exp (-t * |ω| ^ α)) ?_ ?_ ?_ ?_
  · intro x
    exact ((Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable).mul
      (integrable_stableSymbol hα ht).aestronglyMeasurable
  · intro x
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_cos_le_one _)
  · exact integrable_stableSymbol hα ht
  · refine Filter.Eventually.of_forall fun ω => ?_
    exact (Real.continuous_cos.comp (continuous_id.mul continuous_const)).mul continuous_const

/-- For `α > 0`, the weight `x ↦ (1 + |x|)^(-1 - α)` is integrable on `ℝ`. -/
theorem integrable_one_add_abs_neg_rpow {α : ℝ} (hα : 0 < α) :
    Integrable fun x : ℝ => (1 + |x|) ^ (-1 - α) := by
  have hmeas : Continuous fun x : ℝ => (1 + |x|) ^ (-1 - α) := by
    refine Continuous.rpow (continuous_const.add continuous_abs) continuous_const fun x => Or.inl ?_
    linarith [abs_nonneg x]
  have hlt : -1 - α < -1 := by linarith
  have hIoi : IntegrableOn (fun x : ℝ => (1 + |x|) ^ (-1 - α)) (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt hlt one_pos).mono'
      hmeas.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 < x := hx
    have hx0 : 0 < x := lt_trans one_pos hx1
    rw [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_nonpos hx0 (by rw [abs_of_pos hx0]; linarith) (by linarith)
  have hIio : IntegrableOn (fun x : ℝ => (1 + |x|) ^ (-1 - α)) (Iio (-1)) := by
    have hcomp :
        IntegrableOn (fun x : ℝ => (1 + |-x|) ^ (-1 - α)) (Neg.neg ⁻¹' Ioi (1 : ℝ)) :=
      (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg _)
        (Homeomorph.neg ℝ).measurableEmbedding).mpr hIoi
    have hpre : Neg.neg ⁻¹' Ioi (1 : ℝ) = Iio (-1) := by
      ext x
      simp only [mem_preimage, mem_Ioi, mem_Iio]
      exact ⟨fun h => by linarith, fun h => by linarith⟩
    rw [hpre] at hcomp
    refine hcomp.congr_fun (fun x _ => ?_) measurableSet_Iio
    simp only [abs_neg]
  have hIcc : IntegrableOn (fun x : ℝ => (1 + |x|) ^ (-1 - α)) (Icc (-1) 1) :=
    hmeas.continuousOn.integrableOn_Icc
  have huniv : Iio (-1 : ℝ) ∪ Icc (-1) 1 ∪ Ioi 1 = univ := by
    ext x
    simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
    rcases lt_trichotomy x (-1) with h1 | h1 | h1
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr ⟨le_of_eq h1.symm, by linarith⟩)
    · rcases le_or_gt x 1 with h2 | h2
      · exact Or.inl (Or.inr ⟨h1.le, h2⟩)
      · exact Or.inr h2
  rw [← integrableOn_univ, ← huniv]
  exact (hIio.union hIcc).union hIoi

/-- For `0 < α < 2` and `t > 0`, `x ↦ stableKernel α x t` is integrable on `ℝ`. -/
theorem integrable_stableKernel {α t : ℝ} (hα : 0 < α) (hα2 : α < 2) (ht : 0 < t) :
    Integrable fun x : ℝ => stableKernel α x t := by
  have hunit : Integrable fun x : ℝ => stableKernel α x 1 := by
    have hdom : Integrable fun x : ℝ => stableDecayConst α * (1 + |x|) ^ (-1 - α) :=
      (integrable_one_add_abs_neg_rpow hα).const_mul (stableDecayConst α)
    refine hdom.mono' (continuous_stableKernel hα one_pos).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    have hnn := stableKernel_nonneg hα hα2 one_pos x
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hdec := stableKernel_decay_unit_time hα hα2 x
    have hpos : 0 ≤ 1 + |x| := by positivity
    rw [div_eq_mul_inv, ← rpow_neg hpos] at hdec
    have hexp : -(1 + α) = -1 - α := by ring
    rwa [hexp] at hdec
  have hEq :
      (fun x : ℝ => stableKernel α x t) =
        fun x : ℝ => t ^ (-1 / α) * stableKernel α (x * t ^ (-1 / α)) 1 := by
    ext x
    exact stableKernel_self_similar hα x ht
  rw [hEq]
  have hsc_ne : t ^ (-1 / α) ≠ 0 := (rpow_pos_of_pos ht _).ne'
  exact (hunit.comp_mul_right' hsc_ne).const_mul (t ^ (-1 / α))

/-! ### Fourier transform and inversion of the stable symbol -/

/-- The `2π`-scaled stable symbol `ξ ↦ exp (-t |2π ξ|^α)` is complex-integrable on `ℝ`. -/
theorem integrable_stableSymbol_twoPi {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    Integrable fun ξ : ℝ => ((Real.exp (-t * |2 * π * ξ| ^ α) : ℝ) : ℂ) := by
  have h2pi : (2 * π) ≠ 0 := by positivity
  have hr : Integrable fun ξ : ℝ => Real.exp (-t * |2 * π * ξ| ^ α) :=
    (integrable_stableSymbol hα ht).comp_mul_left' h2pi
  exact Complex.ofRealCLM.integrable_comp hr

/-- Exact Fourier transform of the `2π`-scaled stable symbol `ξ ↦ exp (-t |2π ξ|^α)` in
Mathlib's Fourier convention: it equals `stableKernel α x t`. -/
theorem fourier_stableSymbol_eq_stableKernel {α t : ℝ} (hα : 0 < α) (ht : 0 < t) (x : ℝ) :
    𝓕 (fun ξ : ℝ => ((Real.exp (-t * |2 * π * ξ| ^ α) : ℝ) : ℂ)) x =
      ((stableKernel α x t : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun ξ => ((Real.exp (-t * |2 * π * ξ| ^ α) : ℝ) : ℂ)
  have hint :
      Integrable fun ξ : ℝ => Complex.exp (↑(-2 * π * ξ * x) * Complex.I) • f ξ := by
    have hcont :
        Continuous fun ξ : ℝ => Complex.exp (↑(-2 * π * ξ * x) * Complex.I) • f ξ := by
      refine (Complex.continuous_exp.comp ?_).smul ?_
      · exact (Complex.continuous_ofReal.comp
          ((continuous_const.mul continuous_id).mul continuous_const)).mul continuous_const
      · have hpow : Continuous fun ξ : ℝ => |2 * π * ξ| ^ α :=
          (continuous_abs.comp (continuous_const.mul continuous_id)).rpow_const fun _ =>
            Or.inr hα.le
        exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hpow))
    have h2pi : (2 * π) ≠ 0 := by positivity
    refine ((integrable_stableSymbol hα ht).comp_mul_left' h2pi).mono'
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
    rw [norm_smul, Complex.norm_exp]
    have hre0 : ((↑(-2 * π * ξ * x) : ℂ) * Complex.I).re = 0 := by simp [Complex.mul_re]
    rw [hre0, Real.exp_zero, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hdecomp :
      ∀ ξ : ℝ, Complex.exp (↑(-2 * π * ξ * x) * Complex.I) • f ξ =
        ((Real.cos (x * (2 * π * ξ)) * Real.exp (-t * |2 * π * ξ| ^ α) : ℝ) : ℂ) +
          ((-(Real.sin (x * (2 * π * ξ)) * Real.exp (-t * |2 * π * ξ| ^ α)) : ℝ) : ℂ) *
            Complex.I := by
    intro ξ
    rw [smul_eq_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hcos : Real.cos (-2 * π * ξ * x) = Real.cos (x * (2 * π * ξ)) := by
      have harg : -2 * π * ξ * x = -(x * (2 * π * ξ)) := by ring
      rw [harg, Real.cos_neg]
    have hsin : Real.sin (-2 * π * ξ * x) = -Real.sin (x * (2 * π * ξ)) := by
      have harg : -2 * π * ξ * x = -(x * (2 * π * ξ)) := by ring
      rw [harg, Real.sin_neg]
    simp only [hcos, hsin, f]
    push_cast
    ring
  have hre : (𝓕 f x).re = stableKernel α x t := by
    rw [Real.fourier_real_eq_integral_exp_smul, ← Complex.reCLM_apply,
      ← Complex.reCLM.integral_comp_comm hint]
    simp only [Complex.reCLM_apply]
    have hre_congr :
        (fun ξ : ℝ => (Complex.exp (↑(-2 * π * ξ * x) * Complex.I) • f ξ).re) =
          fun ξ : ℝ => Real.cos (x * (2 * π * ξ)) * Real.exp (-t * |2 * π * ξ| ^ α) := by
      funext ξ
      rw [hdecomp ξ]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    have h2pi : 0 < 2 * π := by positivity
    rw [hre_congr,
      Measure.integral_comp_mul_left (fun ω : ℝ => Real.cos (x * ω) * Real.exp (-t * |ω| ^ α))
        (2 * π), smul_eq_mul, abs_inv, abs_of_pos h2pi, stableKernel_eq_integral]
  have him : (𝓕 f x).im = 0 := by
    rw [Real.fourier_real_eq_integral_exp_smul, ← Complex.imCLM_apply,
      ← Complex.imCLM.integral_comp_comm hint]
    simp only [Complex.imCLM_apply]
    let g : ℝ → ℝ :=
      fun ξ => -(Real.sin (x * (2 * π * ξ)) * Real.exp (-t * |2 * π * ξ| ^ α))
    have him_congr :
        (fun ξ : ℝ => (Complex.exp (↑(-2 * π * ξ * x) * Complex.I) • f ξ).im) = g := by
      funext ξ
      rw [hdecomp ξ]
      simp only [g, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    have hneg : ∫ ξ : ℝ, g (-ξ) = ∫ ξ : ℝ, g ξ := integral_neg_eq_self g volume
    have hodd : ∫ ξ : ℝ, g (-ξ) = -∫ ξ : ℝ, g ξ := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      simp only [g, mul_neg, Real.sin_neg, abs_neg]
      ring
    rw [him_congr]
    linarith
  exact Complex.ext hre (by simpa only [Complex.ofReal_im] using him)

/-- Exact inverse Fourier transform of the `2π`-scaled stable symbol `ξ ↦ exp (-t |2π ξ|^α)`. -/
theorem fourierInv_stableSymbol_eq_stableKernel {α t : ℝ} (hα : 0 < α) (ht : 0 < t) (x : ℝ) :
    𝓕⁻ (fun ξ : ℝ => ((Real.exp (-t * |2 * π * ξ| ^ α) : ℝ) : ℂ)) x =
      ((stableKernel α x t : ℝ) : ℂ) := by
  rw [Real.fourierInv_eq_fourier_neg, fourier_stableSymbol_eq_stableKernel hα ht (-x),
    stableKernel_neg]

/-- **Fourier Faithfulness of the Symmetric `α`-Stable Heat Kernel**:
for every `0 < α < 2`, `t > 0`, and `ξ ∈ ℝ`,
`𝓕 (stableKernel α · t) ξ = exp (-t |2π ξ|^α)`. -/
theorem fourier_stableKernel_eq {α t : ℝ} (hα : 0 < α) (hα2 : α < 2) (ht : 0 < t) (ξ : ℝ) :
    𝓕 (fun x : ℝ => ((stableKernel α x t : ℝ) : ℂ)) ξ =
      ((Real.exp (-t * |2 * π * ξ| ^ α) : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun ζ => ((Real.exp (-t * |2 * π * ζ| ^ α) : ℝ) : ℂ)
  have hf_cont : Continuous f := by
    have hpow : Continuous fun ζ : ℝ => |2 * π * ζ| ^ α :=
      (continuous_abs.comp (continuous_const.mul continuous_id)).rpow_const fun _ => Or.inr hα.le
    exact Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul hpow))
  have hf_int : Integrable f := integrable_stableSymbol_twoPi hα ht
  have hFf_int : Integrable (𝓕 f) := by
    have hEq : 𝓕 f = fun x : ℝ => ((stableKernel α x t : ℝ) : ℂ) := by
      ext x
      exact fourier_stableSymbol_eq_stableKernel hα ht x
    rw [hEq]
    exact Complex.ofRealCLM.integrable_comp (integrable_stableKernel hα hα2 ht)
  have hinv := congrFun (Continuous.fourier_fourierInv_eq hf_cont hf_int hFf_int) ξ
  have hinv_eq : 𝓕⁻ f = fun x : ℝ => ((stableKernel α x t : ℝ) : ℂ) := by
    ext x
    exact fourierInv_stableSymbol_eq_stableKernel hα ht x
  rw [hinv_eq] at hinv
  exact hinv

/-- **Unit Total Mass of `stableKernel`**: `∫ x, stableKernel α x t = 1` for all
`0 < α < 2` and `t > 0`. -/
theorem integral_stableKernel_eq_one {α t : ℝ} (hα : 0 < α) (hα2 : α < 2) (ht : 0 < t) :
    ∫ x : ℝ, stableKernel α x t = 1 := by
  have hF0 := fourier_stableKernel_eq hα hα2 ht 0
  have hLHS :
      𝓕 (fun x : ℝ => ((stableKernel α x t : ℝ) : ℂ)) 0 =
        ((∫ x : ℝ, stableKernel α x t : ℝ) : ℂ) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    simpa only [Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.integral_comp_comm (integrable_stableKernel hα hα2 ht)
  have hRHS : ((Real.exp (-t * |2 * π * (0 : ℝ)| ^ α) : ℝ) : ℂ) = 1 := by
    simp [Real.zero_rpow hα.ne']
  rw [hLHS, hRHS] at hF0
  exact_mod_cast congrArg Complex.re hF0

/-! ### General `FractionalHeatKernel α` instance and classical Cauchy match -/

/-- **Concrete General `α`-Stable Fractional Heat Kernel** for every fractional exponent
`0 < α < 2` (`FractionalExponent α`). -/
noncomputable def stableHeatKernel (α : ℝ) (hα : FractionalExponent α) :
    FractionalHeatKernel α where
  P := stableKernel α
  decayConst := stableDecayConst α
  decayConst_pos := stableDecayConst_pos hα.1 hα.2
  even_space x _ _ := stableKernel_neg α x _
  self_similar x _ ht := stableKernel_self_similar hα.1 x ht
  nonneg x _ ht := stableKernel_nonneg hα.1 hα.2 ht x
  radial_antitone _ _ _ ht hab := stableKernel_antitone hα.1 hα.2 ht hab
  decay_unit_time x := stableKernel_decay_unit_time hα.1 hα.2 x
  integrable_space _ ht := integrable_stableKernel hα.1 hα.2 ht
  integral_eq_one _ ht := integral_stableKernel_eq_one hα.1 hα.2 ht

/-- For `α = 1`, `stableHeatKernel 1` coincides pointwise with the explicit Cauchy/Poisson kernel
`cauchyHeatKernel`. -/
theorem stableHeatKernel_one_eq_cauchy (x : ℝ) {t : ℝ} (ht : 0 < t) :
    (stableHeatKernel 1 fractionalExponent_one).P x t = cauchyHeatKernel.P x t := by
  have h0 :
      (stableHeatKernel 1 fractionalExponent_one).P x t =
        (fourierInvFracSemigroupSymbol 1 t x).re := by
    change stableKernel 1 x t =
      ((2 * (π : ℂ))⁻¹ *
        ∫ ξ : ℝ, Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)) *
          Complex.exp (-(t : ℂ) * ((|ξ| ^ (1 : ℝ) : ℝ) : ℂ))).re
    rw [stableKernel_eq_integral x t]
    have hre_pref :
        ∀ z : ℂ, ((2 * (π : ℂ))⁻¹ * z).re = (2 * π)⁻¹ * z.re := by
      intro z
      have hcast : ((2 * (π : ℂ))⁻¹) = (((2 * π)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      rw [hcast, Complex.re_ofReal_mul]
    rw [hre_pref]
    congr 1
    have hint :
        Integrable fun ξ : ℝ =>
          Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)) *
            Complex.exp (-(t : ℂ) * ((|ξ| ^ (1 : ℝ) : ℝ) : ℂ)) := by
      refine (integrable_stableSymbol one_pos ht).mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
      · exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
          (Complex.continuous_exp.comp
            (continuous_const.mul (Complex.continuous_ofReal.comp
              (continuous_abs.rpow_const fun _ => Or.inr zero_le_one))))).aestronglyMeasurable
      · rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
        have hre1 : (Complex.I * (x : ℂ) * (ξ : ℂ)).re = 0 := by
          simp [Complex.mul_re]
        have hre2 : (-(t : ℂ) * ((|ξ| ^ (1 : ℝ) : ℝ) : ℂ)).re = -t * |ξ| ^ (1 : ℝ) := by
          simp
        rw [hre1, hre2, Real.exp_zero, one_mul]
    rw [← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hint]
    simp only [Complex.reCLM_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    have hre1 :
        (Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))).re = Real.cos (x * ξ) := by
      rw [show Complex.I * (x : ℂ) * (ξ : ℂ) = ((x * ξ : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero]
      ring
    have hcexp :
        Complex.exp (-(t : ℂ) * ((|ξ| ^ (1 : ℝ) : ℝ) : ℂ)) =
          ((Real.exp (-t * |ξ| ^ (1 : ℝ)) : ℝ) : ℂ) := by
      have harg : (-(t : ℂ) * ((|ξ| ^ (1 : ℝ) : ℝ) : ℂ)) = ((-t * |ξ| ^ (1 : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg, ← Complex.ofReal_exp]
    dsimp only
    rw [hcexp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hre1]
  rw [h0, fourierInvFracSemigroupSymbol_one ht x, Complex.ofReal_re]

/-! ### `C₀(ℝ)` decay at infinity (`thm:kernelprop` (1)) -/

/-- For `0 < α < 2` and `t > 0`, the stable heat kernel vanishes at spatial infinity:
`stableKernel α x t → 0` as `|x| → ∞` (`cocompact ℝ`). -/
theorem tendsto_stableKernel_cocompact {α t : ℝ} (hα : 0 < α) (hα2 : α < 2) (ht : 0 < t) :
    Tendsto (fun x : ℝ => stableKernel α x t) (cocompact ℝ) (𝓝 0) := by
  have habs : Tendsto (fun x : ℝ => |x|) (cocompact ℝ) atTop :=
    (tendsto_norm_cocompact_atTop (E := ℝ)).congr (fun x => Real.norm_eq_abs x)
  have hsc_pos : 0 < |t ^ (-1 / α)| := abs_pos.mpr (rpow_pos_of_pos ht _).ne'
  have habs_sc : Tendsto (fun x : ℝ => |x * t ^ (-1 / α)|) (cocompact ℝ) atTop := by
    refine (habs.atTop_mul_const hsc_pos).congr fun x => ?_
    rw [abs_mul]
  have h1 : Tendsto (fun x : ℝ => 1 + |x * t ^ (-1 / α)|) (cocompact ℝ) atTop :=
    tendsto_atTop_add_const_left _ 1 habs_sc
  have hneg : Tendsto (fun x : ℝ => (1 + |x * t ^ (-1 / α)|) ^ (-(1 + α))) (cocompact ℝ) (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by positivity : 0 < 1 + α)).comp h1
  have hpow : Tendsto (fun x : ℝ => t ^ (-1 / α) * (stableDecayConst α /
      (1 + |x * t ^ (-1 / α)|) ^ (1 + α))) (cocompact ℝ) (𝓝 0) := by
    have hmul := (hneg.const_mul (stableDecayConst α)).const_mul (t ^ (-1 / α))
    rw [mul_zero, mul_zero] at hmul
    refine hmul.congr fun x => ?_
    rw [rpow_neg (by positivity), ← div_eq_mul_inv]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow
    (fun x => stableKernel_nonneg hα hα2 ht x) (fun x => ?_)
  rw [stableKernel_self_similar hα x ht]
  exact mul_le_mul_of_nonneg_left (stableKernel_decay_unit_time hα hα2 _) (by positivity)

/-- Package `x ↦ stableKernel α x t` as a continuous function vanishing at infinity in
`C₀(ℝ, ℝ)` (`ZeroAtInftyContinuousMap ℝ ℝ`). -/
noncomputable def stableKernelC0Map (α t : ℝ) (hα : FractionalExponent α) (ht : 0 < t) :
    ZeroAtInftyContinuousMap ℝ ℝ where
  toFun := fun x => stableKernel α x t
  continuous_toFun := continuous_stableKernel hα.1 ht
  zero_at_infty' := tendsto_stableKernel_cocompact hα.1 hα.2 ht

end

end FracLap
