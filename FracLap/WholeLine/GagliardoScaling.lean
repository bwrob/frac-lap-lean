/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.GagliardoFourier

/-!
# FracLap.WholeLine.GagliardoScaling

Exact homogeneity of the Fourier-side Gagliardo weight: `Λ_α(ξ) = |ξ|^α Λ_α(1)` for `ξ ≠ 0`.
Together with `0 < Λ_α(1) < ∞` this identifies the Gagliardo energy with the `H^(α/2)` seminorm
`Λ_α(1) ∫ |ξ|^α |𝓕 f|²` without the closed form of the constant.

- `gagliardoWeight_scale`: `w(s / ξ, 0) = ξ^(1+α) w(s, 0)` for `ξ > 0`.
- `gagliardoSymbol_scale`: `Λ_α(ξ) = ξ^α Λ_α(1)` for `ξ > 0`.
- `gagliardoSymbol_neg`: `Λ_α(-ξ) = Λ_α(ξ)`.
- `gagliardoSymbol_eq`: `Λ_α(ξ) = |ξ|^α Λ_α(1)` for `ξ ≠ 0`.
- `gagliardoSymbol_one_pos`, `gagliardoSymbol_one_lt_top`: `0 < Λ_α(1) < ∞`.
-/

namespace FracLap

open Complex FourierTransform MeasureTheory Real Set
open scoped ENNReal

@[expose] public section

/-- Homogeneity of the Gagliardo weight: `w(s / ξ, 0) = ξ^(1+α) w(s, 0)` for `ξ > 0`, `α > 0`. -/
theorem gagliardoWeight_scale {α ξ : ℝ} (hα : 0 < α) (hξ : 0 < ξ) (s : ℝ) :
    gagliardoWeight α (s / ξ, 0) = ENNReal.ofReal (ξ ^ (1 + α)) * gagliardoWeight α (s, 0) := by
  have h1 : 0 < 1 + α := by linarith
  unfold gagliardoWeight
  simp only [sub_zero]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hξ.le _)]
  congr 1
  rcases eq_or_ne s 0 with rfl | hs
  · simp [Real.zero_rpow h1.ne']
  · have hs' : 0 < |s| := abs_pos.mpr hs
    have hξp : 0 < ξ ^ (1 + α) := Real.rpow_pos_of_pos hξ _
    have hsp : 0 < |s| ^ (1 + α) := Real.rpow_pos_of_pos hs' _
    rw [abs_div, abs_of_pos hξ, Real.div_rpow hs'.le hξ.le]
    field_simp

/-- **Homogeneity of the Fourier-side weight** for positive frequencies. -/
theorem gagliardoSymbol_scale {α ξ : ℝ} (hα : 0 < α) (hξ : 0 < ξ) :
    gagliardoSymbol α ξ = ENNReal.ofReal (ξ ^ α) * gagliardoSymbol α 1 := by
  unfold gagliardoSymbol
  set F : ℝ → ℝ≥0∞ := fun s => gagliardoWeight α (s / ξ, 0) *
    ‖((𝐞 (s * 1) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ) with hF
  have hphase : Measurable fun s : ℝ => ((𝐞 (s * 1) : Circle) : ℂ) :=
    (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_id.mul continuous_const))).measurable
  have hFm : Measurable F := by
    refine ((measurable_gagliardoWeight α).comp
      ((measurable_id.div_const ξ).prodMk measurable_const)).mul ?_
    exact ((hphase.sub measurable_const).eNorm).pow_const _
  have hint : ∀ h : ℝ, gagliardoWeight α (h, 0) *
      ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ) = F (ξ * h) := by
    intro h
    simp only [hF]
    rw [show ξ * h / ξ = h by field_simp, show ξ * h * 1 = h * ξ by ring]
  simp_rw [hint]
  have hmap : ∫⁻ h : ℝ, F (ξ * h) = ENNReal.ofReal |ξ⁻¹| * ∫⁻ s, F s := by
    have := lintegral_map hFm (measurable_const_mul ξ) (μ := (volume : Measure ℝ))
    rw [Real.map_volume_mul_left hξ.ne', lintegral_smul_measure, smul_eq_mul] at this
    exact this.symm
  rw [hmap]
  have hscale : ∫⁻ s, F s = ENNReal.ofReal (ξ ^ (1 + α)) * ∫⁻ s,
      gagliardoWeight α (s, 0) * ‖((𝐞 (s * 1) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun s => ?_
    simp only [hF]
    rw [gagliardoWeight_scale hα hξ, mul_assoc]
  rw [hscale, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 2
  rw [abs_of_pos (inv_pos.mpr hξ), Real.rpow_add hξ, Real.rpow_one]
  field_simp

/-- The Fourier-side weight is even. -/
theorem gagliardoSymbol_neg (α ξ : ℝ) : gagliardoSymbol α (-ξ) = gagliardoSymbol α ξ := by
  unfold gagliardoSymbol
  set G : ℝ → ℝ≥0∞ := fun h => gagliardoWeight α (h, 0) *
    ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ) with hG
  have hGneg : ∀ h : ℝ, gagliardoWeight α (h, 0) *
      ‖((𝐞 (h * -ξ) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ) = G (-h) := by
    intro h
    simp only [hG, gagliardoWeight, sub_zero, abs_neg, neg_mul, mul_neg]
  simp_rw [hGneg]
  exact (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp_emb
    (Homeomorph.neg ℝ).measurableEmbedding G

/-- **Homogeneity of the Fourier-side weight**: `Λ_α(ξ) = |ξ|^α Λ_α(1)` for `ξ ≠ 0`, `α > 0`. -/
theorem gagliardoSymbol_eq {α ξ : ℝ} (hα : 0 < α) (hξ : ξ ≠ 0) :
    gagliardoSymbol α ξ = ENNReal.ofReal (|ξ| ^ α) * gagliardoSymbol α 1 := by
  rcases lt_or_gt_of_ne hξ with h | h
  · rw [← gagliardoSymbol_neg, gagliardoSymbol_scale hα (neg_pos.mpr h), abs_of_neg h]
  · rw [gagliardoSymbol_scale hα h, abs_of_pos h]

/-- `Λ_α(1) < ∞`. -/
theorem gagliardoSymbol_one_lt_top {α : ℝ} (hα : FractionalExponent α) :
    gagliardoSymbol α 1 < ∞ := by
  refine (gagliardoSymbol_le hα 1).trans_lt ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_gagliardoKernel_lt_top hα)

/-- `𝐞 h ≠ 1` for `0 < h < 1`. -/
theorem fourierChar_ne_one {h : ℝ} (h0 : 0 < h) (h1 : h < 1) : ((𝐞 h : Circle) : ℂ) ≠ 1 := by
  intro heq
  rw [Real.fourierChar_apply, Complex.exp_eq_one_iff] at heq
  obtain ⟨n, hn⟩ := heq
  have hre := congrArg Complex.im hn
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_add, Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat,
    Complex.im_ofNat] at hre
  have hpos : 0 < Real.pi := Real.pi_pos
  have hn' : (n : ℝ) = h := by
    have : 2 * Real.pi * h = 2 * Real.pi * n := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hre
    have h2 : (2 * Real.pi) ≠ 0 := by positivity
    exact (mul_left_cancel₀ h2 this).symm
  have h1' : (0 : ℝ) < n := by rw [hn']; exact h0
  have h2' : (n : ℝ) < 1 := by rw [hn']; exact h1
  have h3 : (0 : ℤ) < n := by exact_mod_cast h1'
  have h4 : n < (1 : ℤ) := by exact_mod_cast h2'
  omega

/-- `Λ_α(1) > 0`. -/
theorem gagliardoSymbol_one_pos {α : ℝ} (hα : FractionalExponent α) :
    0 < gagliardoSymbol α 1 := by
  unfold gagliardoSymbol
  have hWm : Measurable fun h : ℝ => gagliardoWeight α (h, 0) :=
    (measurable_gagliardoWeight α).comp (measurable_id.prodMk measurable_const)
  have hphase : Measurable fun h : ℝ => ((𝐞 (h * 1) : Circle) : ℂ) :=
    (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_id.mul continuous_const))).measurable
  have hm : Measurable fun h : ℝ => gagliardoWeight α (h, 0) *
      ‖((𝐞 (h * 1) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ) :=
    hWm.mul (((hphase.sub measurable_const).eNorm).pow_const _)
  rw [lintegral_pos_iff_support hm]
  refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo (0 : ℝ) 1) (fun h hh => ?_))
  · simp
  · have hh0 : 0 < h := hh.1
    have hne : ((𝐞 (h * 1) : Circle) : ℂ) - 1 ≠ 0 := by
      rw [mul_one]
      exact sub_ne_zero.mpr (fourierChar_ne_one hh.1 hh.2)
    have hW : gagliardoWeight α (h, 0) ≠ 0 :=
      (gagliardoWeight_pos hα (x := h) (y := 0) hh0.ne').ne'
    have hn : ‖((𝐞 (h * 1) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ) ≠ 0 := by
      refine (ENNReal.rpow_pos (by simpa using hne) (by simp)).ne'
    exact mul_ne_zero hW hn

end

end FracLap
