/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.AnomalousDiffusion
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLap.WholeLine.ClassicalKernels

Canonical concrete instances of `FractionalHeatKernel α` for `α = 1` (Cauchy/Poisson kernel)
and `α = 2` (Gaussian heat kernel), together with direct Fourier inversion proofs from the
semigroup symbol `ξ ↦ exp (-t |ξ|^α)`:
- `cauchyHeatKernel`: concrete `FractionalHeatKernel 1` with
  `P₁(x, t) = t / (π (t² + x²))`.
- `gaussianHeatKernel`: concrete `FractionalHeatKernel 2` with
  `P₂(x, t) = (4 π t)^(-1/2) exp (-x² / (4 t))`.
- `fourierInvFracSemigroupSymbol`: inverse Fourier transform
  `(2 π)⁻¹ ∫ ξ, exp (I x ξ) exp (-t |ξ|^α) dξ`.
- `fourierInvFracSemigroupSymbol_one` and `fourierInvFracSemigroupSymbol_two`:
  exact identification with `cauchyHeatKernel.P x t` and `gaussianHeatKernel.P x t`.
-/

namespace FracLap

open Complex Filter MeasureTheory Real Set Topology

@[expose] public section

/-! ### 1. Concrete `α = 1` Cauchy (Poisson) fractional heat kernel -/

/-- The canonical 1D Cauchy (Poisson) heat kernel at order `α = 1`:
`P₁(x, t) = t / (π (t² + x²))`. -/
noncomputable def cauchyHeatKernel : FractionalHeatKernel 1 where
  P x t := t / (Real.pi * (t ^ 2 + x ^ 2))
  decayConst := 2 / Real.pi
  decayConst_pos := div_pos (by norm_num) Real.pi_pos
  even_space x t _ := by ring_nf
  self_similar x t ht := by
    have hpow : t ^ (-1 / (1 : ℝ)) = t⁻¹ := by
      have hexp : (-1 / (1 : ℝ)) = -1 := by norm_num
      rw [hexp, Real.rpow_neg_one]
    have hden1 : Real.pi * (t ^ 2 + x ^ 2) ≠ 0 := by positivity
    have hden2 : Real.pi * (1 ^ 2 + (x * t⁻¹) ^ 2) ≠ 0 := by positivity
    have ht_ne : t ≠ 0 := ht.ne'
    rw [hpow]
    field_simp
  nonneg x t ht := by positivity
  radial_antitone a b t ht hab := by
    have hsq : a ^ 2 ≤ b ^ 2 := by
      rw [← sq_abs a, ← sq_abs b]
      exact pow_le_pow_left₀ (abs_nonneg a) hab 2
    have hden_pos : 0 < Real.pi * (t ^ 2 + a ^ 2) := by positivity
    have hden_le : Real.pi * (t ^ 2 + a ^ 2) ≤ Real.pi * (t ^ 2 + b ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
    exact div_le_div_of_nonneg_left ht.le hden_pos hden_le
  decay_unit_time x := by
    have hexp : (1 + (1 : ℝ)) = (2 : ℕ) := by norm_num
    rw [hexp, rpow_natCast, one_pow]
    have hquad : (1 + |x|) ^ 2 ≤ 2 * (1 + x ^ 2) := by
      nlinarith [sq_abs x, sq_nonneg (1 - |x|)]
    have hden1 : 0 < Real.pi * (1 + x ^ 2) := by positivity
    have hden2 : 0 < (1 + |x|) ^ 2 := by positivity
    rw [div_div, div_le_div_iff₀ hden1 (mul_pos Real.pi_pos hden2)]
    calc
      1 * (Real.pi * (1 + |x|) ^ 2) = Real.pi * (1 + |x|) ^ 2 := one_mul _
      _ ≤ Real.pi * (2 * (1 + x ^ 2)) := mul_le_mul_of_nonneg_left hquad Real.pi_pos.le
      _ = 2 * (Real.pi * (1 + x ^ 2)) := by ring
  integrable_space t ht := by
    have ht_ne : t ≠ 0 := ht.ne'
    have hcongr : (fun x : ℝ ↦ t / (Real.pi * (t ^ 2 + x ^ 2))) =
        fun x : ℝ ↦ (1 / (Real.pi * t)) * (1 + (t⁻¹ * x) ^ 2)⁻¹ := by
      funext x
      have hden1 : Real.pi * (t ^ 2 + x ^ 2) ≠ 0 := by positivity
      have hden2 : 1 + (t⁻¹ * x) ^ 2 ≠ 0 := by positivity
      field_simp
    rw [hcongr]
    exact (integrable_inv_one_add_mul_sq (inv_ne_zero ht_ne)).const_mul (1 / (Real.pi * t))
  integral_eq_one t ht := by
    have ht_ne : t ≠ 0 := ht.ne'
    have hcongr : (fun x : ℝ ↦ t / (Real.pi * (t ^ 2 + x ^ 2))) =
        fun x : ℝ ↦ (1 / (Real.pi * t)) * (1 + (t⁻¹ * x) ^ 2)⁻¹ := by
      funext x
      have hden1 : Real.pi * (t ^ 2 + x ^ 2) ≠ 0 := by positivity
      have hden2 : 1 + (t⁻¹ * x) ^ 2 ≠ 0 := by positivity
      field_simp
    rw [hcongr, integral_const_mul, integral_univ_inv_one_add_mul_sq t⁻¹,
      abs_of_pos (inv_pos.mpr ht)]
    have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp

/-! ### 2. Concrete `α = 2` Gaussian heat kernel -/

/-- The canonical 1D Gaussian heat kernel at order `α = 2`:
`P₂(x, t) = (4 π t)^(-1/2) exp (-x² / (4 t))`. -/
noncomputable def gaussianHeatKernel : FractionalHeatKernel 2 where
  P x t := (1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (-x ^ 2 / (4 * t))
  decayConst := 32 / Real.sqrt (4 * Real.pi)
  decayConst_pos := by positivity
  even_space x t _ := by ring_nf
  self_similar x t ht := by
    have hpow : t ^ (-1 / (2 : ℝ)) = (Real.sqrt t)⁻¹ := by
      have hexp : (-1 / (2 : ℝ)) = -(1 / 2) := by norm_num
      rw [hexp, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
    have hsqrt_mul : Real.sqrt (4 * Real.pi * t) = Real.sqrt (4 * Real.pi) * Real.sqrt t :=
      Real.sqrt_mul (by positivity) t
    have hsq_sqrt : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
    have harg : -(x * (Real.sqrt t)⁻¹) ^ 2 / (4 * 1) = -x ^ 2 / (4 * t) := by
      have hsqrt_ne : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
      calc
        -(x * (Real.sqrt t)⁻¹) ^ 2 / (4 * 1)
            = -x ^ 2 / (4 * (Real.sqrt t) ^ 2) := by field_simp
        _ = -x ^ 2 / (4 * t) := by rw [hsq_sqrt]
    rw [hpow, harg, mul_one (4 * Real.pi), hsqrt_mul]
    ring
  nonneg x t ht := by positivity
  radial_antitone a b t ht hab := by
    have hsq : a ^ 2 ≤ b ^ 2 := by
      rw [← sq_abs a, ← sq_abs b]
      exact pow_le_pow_left₀ (abs_nonneg a) hab 2
    have hexp_le : Real.exp (-b ^ 2 / (4 * t)) ≤ Real.exp (-a ^ 2 / (4 * t)) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) (by positivity))
    exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
  decay_unit_time x := by
    have hexp : (1 + (2 : ℝ)) = (3 : ℕ) := by norm_num
    rw [hexp, rpow_natCast, mul_one (4 * Real.pi)]
    have hsum : (∑ i ∈ Finset.range 3, (x ^ 2 / 4) ^ i / (i.factorial : ℝ)) ≤
        Real.exp (x ^ 2 / 4) :=
      Real.sum_le_exp_of_nonneg (by positivity) 3
    have hsum_eval :
        (∑ i ∈ Finset.range 3, (x ^ 2 / 4) ^ i / (i.factorial : ℝ)) =
          1 + x ^ 2 / 4 + x ^ 4 / 32 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      norm_num
      ring
    rw [hsum_eval] at hsum
    have hpoly : (1 + |x|) ^ 3 ≤ 32 * (1 + x ^ 2 / 4 + x ^ 4 / 32) := by
      have hdiff : 32 * (1 + x ^ 2 / 4 + x ^ 4 / 32) - (1 + |x|) ^ 3 =
          (|x| ^ 2 - |x| / 2) ^ 2 + (2 * |x| - 1) ^ 2 + (3 / 4) * |x| ^ 2 + |x| + 30 := by
        have hxa : |x| ^ 2 = x ^ 2 := sq_abs x
        have hxa4 : |x| ^ 4 = x ^ 4 := by
          calc
            |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
            _ = (x ^ 2) ^ 2 := by rw [hxa]
            _ = x ^ 4 := by ring
        rw [← hxa, ← hxa4]
        ring
      have hpos : 0 ≤ (|x| ^ 2 - |x| / 2) ^ 2 + (2 * |x| - 1) ^ 2 +
          (3 / 4) * |x| ^ 2 + |x| + 30 := by positivity
      linarith
    have hbound : (1 + |x|) ^ 3 ≤ 32 * Real.exp (x ^ 2 / 4) := by linarith
    have hexp_neg : Real.exp (-x ^ 2 / 4) = (Real.exp (x ^ 2 / 4))⁻¹ := by
      rw [← Real.exp_neg]
      ring_nf
    rw [mul_one (4 : ℝ)]
    calc
      (1 / Real.sqrt (4 * Real.pi)) * Real.exp (-x ^ 2 / 4)
          = (1 / Real.sqrt (4 * Real.pi)) * (Real.exp (x ^ 2 / 4))⁻¹ := by rw [hexp_neg]
      _ ≤ (1 / Real.sqrt (4 * Real.pi)) * (32 / (1 + |x|) ^ 3) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
        simpa only [one_mul, mul_comm] using hbound
      _ = (32 / Real.sqrt (4 * Real.pi)) / (1 + |x|) ^ 3 := by ring
  integrable_space t ht := by
    have hcongr :
        (fun x : ℝ ↦ (1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (-x ^ 2 / (4 * t))) =
          fun x : ℝ ↦
            (1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (-(1 / (4 * t)) * x ^ 2) := by
      funext x
      ring_nf
    rw [hcongr]
    exact (integrable_exp_neg_mul_sq (by positivity : 0 < 1 / (4 * t))).const_mul _
  integral_eq_one t ht := by
    have hcongr :
        (fun x : ℝ ↦ (1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (-x ^ 2 / (4 * t))) =
          fun x : ℝ ↦
            (1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (-(1 / (4 * t)) * x ^ 2) := by
      funext x
      ring_nf
    rw [hcongr, integral_const_mul, integral_gaussian]
    have hdiv : Real.pi / (1 / (4 * t)) = 4 * Real.pi * t := by
      field_simp
    have hsqrt_pos : 0 < Real.sqrt (4 * Real.pi * t) := Real.sqrt_pos.mpr (by positivity)
    rw [hdiv, one_div, inv_mul_cancel₀ hsqrt_pos.ne']

/-! ### 3. Direct Fourier inversion for `α = 1` and `α = 2` -/

/-- Inverse Fourier transform of the fractional heat semigroup multiplier symbol
`ξ ↦ exp (-t |ξ|^α)`:
`(2 π)⁻¹ ∫ ξ, exp (I x ξ) exp (-t |ξ|^α) dξ`. -/
noncomputable def fourierInvFracSemigroupSymbol (α t x : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ *
    ∫ ξ : ℝ, Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)) *
      Complex.exp (-(t : ℂ) * ((|ξ| ^ α : ℝ) : ℂ))

/-- Exact exponential integral on `(0, ∞)` for complex decay parameters `z` with `0 < z.re`:
`∫_{0}^{∞} exp (-z ξ) dξ = z⁻¹`. -/
theorem integral_Ioi_cexp_neg_mul {z : ℂ} (hz : 0 < z.re) :
    ∫ ξ in Set.Ioi (0 : ℝ), Complex.exp (-z * (ξ : ℂ)) = z⁻¹ := by
  have hz_ne : z ≠ 0 := by
    intro h0
    rw [h0, zero_re] at hz
    exact lt_irrefl 0 hz
  have hint : IntegrableOn (fun ξ : ℝ ↦ Complex.exp (-z * (ξ : ℂ))) (Set.Ioi 0) := by
    have hdom : IntegrableOn (fun ξ : ℝ ↦ Real.exp (-z.re * ξ)) (Set.Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 hz
    refine hdom.mono' ?_ ?_
    · have hcont : Continuous (fun ξ : ℝ ↦ Complex.exp (-z * (ξ : ℂ))) :=
        Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
      exact hcont.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ _
      have hre : (-z * (ξ : ℂ)).re = -z.re * ξ := by
        simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      rw [Complex.norm_exp, hre]
  have hderiv : ∀ ξ ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun u : ℝ ↦ (-z)⁻¹ * Complex.exp (-z * (u : ℂ)))
        (Complex.exp (-z * (ξ : ℂ))) ξ := by
    intro ξ _
    have hlin : HasDerivAt (fun u : ℝ ↦ -z * (u : ℂ)) (-z * 1) ξ :=
      (Complex.ofRealCLM.hasDerivAt (x := ξ)).const_mul (-z)
    have hexp : HasDerivAt (fun u : ℝ ↦ Complex.exp (-z * (u : ℂ)))
        (Complex.exp (-z * (ξ : ℂ)) * (-z * 1)) ξ := hlin.cexp
    have hmul := hexp.const_mul (-z)⁻¹
    refine hmul.congr_deriv ?_
    field_simp
  have hcont : ContinuousWithinAt (fun u : ℝ ↦ (-z)⁻¹ * Complex.exp (-z * (u : ℂ)))
      (Set.Ici 0) 0 :=
    (continuous_const.mul
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal))).continuousWithinAt
  have hlim : Tendsto (fun u : ℝ ↦ (-z)⁻¹ * Complex.exp (-z * (u : ℂ))) atTop (𝓝 0) := by
    have hexp_real : Tendsto (fun u : ℝ ↦ Real.exp (-z.re * u)) atTop (𝓝 0) := by
      have h := Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hz))
      refine h.congr fun u ↦ ?_
      simp only [Function.comp_apply, id_eq, neg_mul]
    have hcexp_zero : Tendsto (fun u : ℝ ↦ Complex.exp (-z * (u : ℂ))) atTop (𝓝 0) := by
      refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
      refine hexp_real.congr fun u ↦ ?_
      have hre : (-z * (u : ℂ)).re = -z.re * u := by
        simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      rw [Complex.norm_exp, hre]
    simpa only [mul_zero] using (tendsto_const_nhds (x := (-z)⁻¹)).mul hcexp_zero
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, mul_one, zero_sub, neg_inv, neg_neg] at hFTC
  exact hFTC

/-- **Fourier Inversion for `α = 1`**:
The inverse Fourier transform of `ξ ↦ exp (-t |ξ|)` equals the Cauchy/Poisson heat kernel
`cauchyHeatKernel.P x t = t / (π (t² + x²))` for every `t > 0` and `x ∈ ℝ`. -/
theorem fourierInvFracSemigroupSymbol_one {t : ℝ} (ht : 0 < t) (x : ℝ) :
    fourierInvFracSemigroupSymbol 1 t x = (cauchyHeatKernel.P x t : ℂ) := by
  set z₁ : ℂ := (t : ℂ) - Complex.I * (x : ℂ)
  set z₂ : ℂ := (t : ℂ) + Complex.I * (x : ℂ)
  have hz₁ : 0 < z₁.re := by
    simp only [z₁, sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
      sub_self, sub_zero]
    exact ht
  have hz₂ : 0 < z₂.re := by
    simp only [z₂, add_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
      sub_self, add_zero]
    exact ht
  have hint_pos : IntegrableOn (fun ξ : ℝ ↦ Complex.exp (-z₁ * (ξ : ℂ))) (Set.Ioi 0) := by
    have hdom : IntegrableOn (fun ξ : ℝ ↦ Real.exp (-z₁.re * ξ)) (Set.Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 hz₁
    refine hdom.mono' ?_ ?_
    · exact (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ _
      have hre : (-z₁ * (ξ : ℂ)).re = -z₁.re * ξ := by
        simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      rw [Complex.norm_exp, hre]
  have hint_neg : IntegrableOn (fun ξ : ℝ ↦ Complex.exp (-z₂ * (-(ξ : ℂ)))) (Set.Iio 0) := by
    have hdom : IntegrableOn (fun ξ : ℝ ↦ Real.exp (-z₂.re * ξ)) (Set.Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 hz₂
    have hcomp_pos : IntegrableOn (fun ξ : ℝ ↦ Complex.exp (-z₂ * (ξ : ℂ))) (Set.Ioi 0) := by
      refine hdom.mono' ?_ ?_
      · exact (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable.restrict
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ _
        have hre : (-z₂ * (ξ : ℂ)).re = -z₂.re * ξ := by
          simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
        rw [Complex.norm_exp, hre]
    have hcomp := (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg _)
      (Homeomorph.neg ℝ).measurableEmbedding).mpr hcomp_pos
    have hpre : (Neg.neg ⁻¹' Set.Ioi (0 : ℝ)) = Set.Iio (0 : ℝ) := by
      ext ξ
      simp only [Set.mem_preimage, Set.mem_Ioi, Left.neg_pos_iff, Set.mem_Iio]
    rw [hpre] at hcomp
    refine hcomp.congr_fun (fun ξ _ ↦ ?_) measurableSet_Iio
    simp only [Function.comp_apply, ofReal_neg]
  let f : ℝ → ℂ := fun ξ ↦
    Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)) * Complex.exp (-(t : ℂ) * ((|ξ| ^ (1 : ℝ) : ℝ) : ℂ))
  have hf_pos : ∀ ξ ∈ Set.Ioi (0 : ℝ), f ξ = Complex.exp (-z₁ * (ξ : ℂ)) := by
    intro ξ hξ
    dsimp only [f]
    rw [rpow_one, abs_of_pos hξ, ← Complex.exp_add]
    congr 1
    simp only [z₁]
    ring
  have hf_neg : ∀ ξ ∈ Set.Iio (0 : ℝ), f ξ = Complex.exp (-z₂ * (-(ξ : ℂ))) := by
    intro ξ hξ
    dsimp only [f]
    rw [rpow_one, abs_of_neg hξ, ← Complex.exp_add]
    congr 1
    simp only [z₂, ofReal_neg]
    ring
  have hint_f_pos : IntegrableOn f (Set.Ioi 0) :=
    hint_pos.congr_fun (fun ξ hξ ↦ (hf_pos ξ hξ).symm) measurableSet_Ioi
  have hint_f_Ici : IntegrableOn f (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hint_f_pos
  have hint_f_neg : IntegrableOn f (Set.Iio 0) :=
    hint_neg.congr_fun (fun ξ hξ ↦ (hf_neg ξ hξ).symm) measurableSet_Iio
  have hint_f : Integrable f := by
    rw [← integrableOn_univ, ← Set.Iio_union_Ici (a := (0 : ℝ))]
    exact hint_f_neg.union hint_f_Ici
  have hsplit : (∫ ξ : ℝ, f ξ) = (∫ ξ in Set.Iio (0 : ℝ), f ξ) + ∫ ξ in Set.Ici (0 : ℝ), f ξ :=
    (integral_add_compl (μ := volume) (measurableSet_Iio (a := (0 : ℝ))) hint_f).symm.trans (by
      rw [Set.compl_Iio])
  have hright : (∫ ξ in Set.Ici (0 : ℝ), f ξ) = z₁⁻¹ := by
    rw [integral_Ici_eq_integral_Ioi]
    have hcongr : (∫ ξ in Set.Ioi (0 : ℝ), f ξ) =
        ∫ ξ in Set.Ioi (0 : ℝ), Complex.exp (-z₁ * (ξ : ℂ)) :=
      setIntegral_congr_fun measurableSet_Ioi hf_pos
    rw [hcongr, integral_Ioi_cexp_neg_mul hz₁]
  have hleft : (∫ ξ in Set.Iio (0 : ℝ), f ξ) = z₂⁻¹ := by
    have hcongr : (∫ ξ in Set.Iio (0 : ℝ), f ξ) =
        ∫ ξ in Set.Iio (0 : ℝ), Complex.exp (-z₂ * (-(ξ : ℂ))) :=
      setIntegral_congr_fun measurableSet_Iio hf_neg
    rw [hcongr, ← integral_Iic_eq_integral_Iio]
    have hrefl : (∫ ξ in Set.Iic (0 : ℝ), Complex.exp (-z₂ * (-(ξ : ℂ))) =
        ∫ ξ in Set.Ioi (0 : ℝ), Complex.exp (-z₂ * (ξ : ℂ))) := by
      have hrefl' :=
        integral_comp_neg_Iic (0 : ℝ) (fun ξ : ℝ ↦ Complex.exp (-z₂ * (ξ : ℂ)))
      simpa only [neg_zero, ofReal_neg] using hrefl'
    rw [hrefl, integral_Ioi_cexp_neg_mul hz₂]
  unfold fourierInvFracSemigroupSymbol
  change (2 * (Real.pi : ℂ))⁻¹ * (∫ ξ : ℝ, f ξ) =
    ((t / (Real.pi * (t ^ 2 + x ^ 2)) : ℝ) : ℂ)
  rw [hsplit, hleft, hright]
  have hz₁_ne : z₁ ≠ 0 := fun h0 ↦ by rw [h0, zero_re] at hz₁; exact lt_irrefl 0 hz₁
  have hz₂_ne : z₂ ≠ 0 := fun h0 ↦ by rw [h0, zero_re] at hz₂; exact lt_irrefl 0 hz₂
  have hsum : z₂⁻¹ + z₁⁻¹ = 2 * (t : ℂ) / ((t : ℂ) ^ 2 + (x : ℂ) ^ 2) := by
    have hprod : z₂ * z₁ = (t : ℂ) ^ 2 + (x : ℂ) ^ 2 := by
      simp only [z₁, z₂]
      ring_nf
      rw [Complex.I_sq]
      ring
    have hden_ne : (t : ℂ) ^ 2 + (x : ℂ) ^ 2 ≠ 0 := by
      rw [← hprod]
      exact mul_ne_zero hz₂_ne hz₁_ne
    have hadd : z₁ + z₂ = 2 * (t : ℂ) := by
      simp only [z₁, z₂]
      ring
    calc
      z₂⁻¹ + z₁⁻¹ = (z₁ + z₂) / (z₂ * z₁) := by field_simp
      _ = 2 * (t : ℂ) / ((t : ℂ) ^ 2 + (x : ℂ) ^ 2) := by rw [hadd, hprod]
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hden_pos : 0 < t ^ 2 + x ^ 2 := by positivity
  have hdenC_ne : (t : ℂ) ^ 2 + (x : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast hden_pos.ne'
  rw [hsum]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow]
  field_simp

/-- **Fourier Inversion for `α = 2`**:
The inverse Fourier transform of `ξ ↦ exp (-t ξ²)` equals the Gaussian heat kernel
`gaussianHeatKernel.P x t = (4 π t)^(-1/2) exp (-x² / (4 t))` for every `t > 0` and `x ∈ ℝ`. -/
theorem fourierInvFracSemigroupSymbol_two {t : ℝ} (ht : 0 < t) (x : ℝ) :
    fourierInvFracSemigroupSymbol 2 t x = (gaussianHeatKernel.P x t : ℂ) := by
  unfold fourierInvFracSemigroupSymbol
  change (2 * (Real.pi : ℂ))⁻¹ *
      ∫ ξ : ℝ, Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)) *
        Complex.exp (-(t : ℂ) * ((|ξ| ^ (2 : ℝ) : ℝ) : ℂ)) =
    (((1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (-x ^ 2 / (4 * t)) : ℝ) : ℂ)
  have hcongr :
      (fun ξ : ℝ ↦
        Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)) *
          Complex.exp (-(t : ℂ) * ((|ξ| ^ (2 : ℝ) : ℝ) : ℂ))) =
        fun ξ : ℝ ↦
          Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)) *
            Complex.exp (-(t : ℂ) * (ξ : ℂ) ^ 2) := by
    funext ξ
    have hpow : |ξ| ^ (2 : ℝ) = ξ ^ 2 := by
      rw [rpow_two, sq_abs]
    rw [hpow]
    push_cast
    rfl
  rw [hcongr, fourierIntegral_gaussian (b := (t : ℂ)) (by simpa using ht) (x : ℂ)]
  have hpref :
      (2 * (Real.pi : ℂ))⁻¹ * (((Real.pi : ℂ) / (t : ℂ)) ^ (1 / 2 : ℂ)) =
        (((1 / Real.sqrt (4 * Real.pi * t) : ℝ) : ℂ)) := by
    have hpi_t : ((Real.pi / t : ℝ) : ℂ) = (Real.pi : ℂ) / (t : ℂ) := by push_cast; rfl
    have hcpow : ((Real.pi / t : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) =
        ((((Real.pi / t) ^ (1 / 2 : ℝ) : ℝ)) : ℂ) :=
      (Complex.ofReal_cpow (div_nonneg Real.pi_pos.le ht.le) (1 / 2)).symm
    have hreal : (Real.pi / t) ^ (1 / 2 : ℝ) = Real.sqrt (Real.pi / t) :=
      (Real.sqrt_eq_rpow _).symm
    have h12 : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; rfl
    rw [← hpi_t, ← h12, hcpow, hreal]
    have hreal_eq : (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / t) =
        1 / Real.sqrt (4 * Real.pi * t) := by
      have h4 : Real.sqrt (4 * Real.pi * t) = 2 * Real.sqrt (Real.pi * t) := by
        have h : (4 * Real.pi * t) = 2 ^ 2 * (Real.pi * t) := by ring
        rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
      have hmul : Real.sqrt (Real.pi / t) * Real.sqrt (Real.pi * t) = Real.pi := by
        rw [← Real.sqrt_mul (div_nonneg Real.pi_pos.le ht.le)]
        have h : (Real.pi / t) * (Real.pi * t) = Real.pi ^ 2 := by
          have ht_ne : t ≠ 0 := ht.ne'
          field_simp
        rw [h, Real.sqrt_sq Real.pi_pos.le]
      have hsqrt_pos : 0 < Real.sqrt (Real.pi * t) := Real.sqrt_pos.mpr (by positivity)
      have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
      rw [h4]
      calc
        (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / t)
            = (2 * Real.pi)⁻¹ * (Real.sqrt (Real.pi / t) * Real.sqrt (Real.pi * t) /
                Real.sqrt (Real.pi * t)) := by field_simp
        _ = (2 * Real.pi)⁻¹ * (Real.pi / Real.sqrt (Real.pi * t)) := by rw [hmul]
        _ = 1 / (2 * Real.sqrt (Real.pi * t)) := by field_simp
    have hcast : ((2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / t) : ℝ) =
        (1 / Real.sqrt (4 * Real.pi * t) : ℝ) := hreal_eq
    exact_mod_cast hcast
  have hexp_arg : (-(x : ℂ) ^ 2 / (4 * (t : ℂ))) = (((-x ^ 2 / (4 * t) : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [← mul_assoc, hpref, hexp_arg, ← Complex.ofReal_exp]
  push_cast
  rfl

end

end FracLap
