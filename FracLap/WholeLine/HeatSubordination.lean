/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.ClassicalKernels
public import FracLap.WholeLine.GagliardoSymbolExact
public import FracLap.WholeLine.PointwiseEquivalence
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLap.WholeLine.HeatSubordination

Bochner heat subordination representation of the fractional Laplacian (`thm:heat_subordination`):
- `inv_gamma_neg_half_eq_neg_levyConst`: `Γ(-α/2)⁻¹ = -c_{α/2} = -(α/2) / Γ(1 - α/2)` for
  `0 < α < 2`.
- `gaussianHeatKernel_P_eq_gaussDensity`: `gaussianHeatKernel.P y t = gaussDensity t y` for `t > 0`.
- `fracLapSymbol_eq_heat_subordination`: spectral subordination identity
  `|2π ξ|^α = Γ(-α/2)⁻¹ ∫_{t > 0} t^(-α/2 - 1) (exp(-t (2π ξ)²) - 1) dt`.
- `fracHeatConv_gaussian_sub_eq_secondDiff`: symmetrized heat representation
  `(e^{tΔ} φ)(x) - φ(x) = (1/2) ∫ g_t(y) δ_2 φ(x, y) dy`.
- `fracLapSecondDiff_eq_heat_subordination` (`thm:heat_subordination`): for `0 < α < 2`,
  `φ ∈ 𝓢(ℝ, ℝ)`, and `x ∈ ℝ`,
  `(-Δ)^(α/2) φ(x) = Γ(-α/2)⁻¹ ∫_{t > 0} t^(-α/2 - 1) (e^{tΔ} φ(x) - φ(x)) dt`.
-/

namespace FracLap

open MeasureTheory Real Set
open scoped ENNReal SchwartzMap

@[expose] public section

/-- Gamma recurrence relating `Γ(-α / 2)` and the Lévy subordination constant
`levyConst (α / 2) = (α / 2) / Γ(1 - α / 2)`:
`(Γ(-α / 2))⁻¹ = -levyConst (α / 2)` for `0 < α < 2`. -/
theorem inv_gamma_neg_half_eq_neg_levyConst {α : ℝ} (hα : FractionalExponent α) :
    (Real.Gamma (-α / 2))⁻¹ = -levyConst (α / 2) := by
  have hne : (-α / 2 : ℝ) ≠ 0 := by linarith [hα.1]
  have hsum : (-α / 2 : ℝ) + 1 = 1 - α / 2 := by ring
  have hrec : Real.Gamma (1 - α / 2) = -(α / 2) * Real.Gamma (-(α / 2)) := by
    rw [show -(α / 2) = -α / 2 by ring, ← hsum, Real.Gamma_add_one hne]
  have hG1 : Real.Gamma (1 - α / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (one_sub_half_pos hα)).ne'
  unfold levyConst
  rw [hrec]
  have hα0 : α ≠ 0 := hα.1.ne'
  field_simp

/-- The Gamma value `Γ(-α / 2)` is strictly negative for `0 < α < 2`. -/
theorem gamma_neg_half_neg {α : ℝ} (hα : FractionalExponent α) :
    Real.Gamma (-α / 2) < 0 := by
  have hc : 0 < levyConst (α / 2) := levyConst_pos (by linarith [hα.1]) (by linarith [hα.2])
  have hinv : (Real.Gamma (-α / 2))⁻¹ < 0 := by
    rw [inv_gamma_neg_half_eq_neg_levyConst hα]
    linarith
  exact inv_lt_zero.mp hinv

/-- Identification of `gaussianHeatKernel.P y t` with `gaussDensity t y` for `t > 0`. -/
theorem gaussianHeatKernel_P_eq_gaussDensity (y : ℝ) {t : ℝ} (ht : 0 < t) :
    gaussianHeatKernel.P y t = gaussDensity t y := by
  change (1 / √(4 * π * t)) * exp (-y ^ 2 / (4 * t)) =
    (4 * π * t) ^ (-1 / 2 : ℝ) * exp (-(y ^ 2 / 4 / t))
  have hsq : 1 / √(4 * π * t) = (4 * π * t) ^ (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, one_div, show (-1 / 2 : ℝ) = -(1 / 2) by ring,
      Real.rpow_neg (by positivity)]
  rw [hsq]
  congr 2
  ring

/-- **Spectral Heat Subordination Identity**: for every `0 < α < 2` and `ξ ∈ ℝ`,
`|2π ξ|^α = Γ(-α/2)⁻¹ ∫_{t > 0} t^(-α/2 - 1) (exp (-t (2π ξ)²) - 1) dt`. -/
theorem fracLapSymbol_eq_heat_subordination {α : ℝ} (hα : FractionalExponent α) (ξ : ℝ) :
    fracLapSymbol α ξ =
      (Real.Gamma (-α / 2))⁻¹ *
        ∫ t in Ioi (0 : ℝ), t ^ (-α / 2 - 1) * (exp (-t * (2 * π * ξ) ^ 2) - 1) := by
  have hβ0 : 0 < α / 2 := by linarith [hα.1]
  have hβ1 : α / 2 < 1 := by linarith [hα.2]
  rw [inv_gamma_neg_half_eq_neg_levyConst hα]
  have hpt : ∀ t : ℝ, t ^ (-α / 2 - 1) * (exp (-t * (2 * π * ξ) ^ 2) - 1) =
      -((1 - exp (-((2 * π * ξ) ^ 2 * t))) * t ^ (-1 - α / 2)) := by
    intro t
    have : -t * (2 * π * ξ) ^ 2 = -((2 * π * ξ) ^ 2 * t) := by ring
    rw [this]
    ring_nf
  simp_rw [hpt, integral_neg]
  rw [neg_mul_neg]
  by_cases hξ : ξ = 0
  · subst hξ
    simp [fracLapSymbol, hα.1.ne']
  · have hlam : 0 < (2 * π * ξ) ^ 2 := by positivity
    have hsub := integral_one_sub_exp_scaled hβ0 hβ1 hlam
    have hlam_pow : ((2 * π * ξ) ^ 2) ^ (α / 2) = fracLapSymbol α ξ := by
      unfold fracLapSymbol
      rw [← sq_abs (2 * π * ξ), ← Real.rpow_natCast |2 * π * ξ| 2, ← Real.rpow_mul (abs_nonneg _)]
      congr 1
      push_cast
      ring
    have hΓ : Real.Gamma (1 - α / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
    have hlevy : levyConst (α / 2) * (Real.Gamma (1 - α / 2) / (α / 2)) = 1 := by
      unfold levyConst
      have hα2 : α / 2 ≠ 0 := by positivity
      rw [div_mul_div_cancel₀ hΓ, div_self hα2]
    symm
    calc levyConst (α / 2) * ∫ t in Ioi (0 : ℝ),
          (1 - exp (-((2 * π * ξ) ^ 2 * t))) * t ^ (-1 - α / 2)
        = levyConst (α / 2) *
            (((2 * π * ξ) ^ 2) ^ (α / 2) * (Real.Gamma (1 - α / 2) / (α / 2))) := by
          rw [hsub]
      _ = ((2 * π * ξ) ^ 2) ^ (α / 2) *
            (levyConst (α / 2) * (Real.Gamma (1 - α / 2) / (α / 2))) := by
          ring
      _ = fracLapSymbol α ξ := by rw [hlam_pow, hlevy, mul_one]

/-- **Symmetrized Heat Difference Identity**: for `t > 0` and bounded measurable `u`,
`fracHeatConv gaussianHeatKernel t u x - u x` equals `(1 / 2) * ∫ g_t(y) δ₂u(x, y)`. -/
theorem fracHeatConv_gaussian_sub_eq_secondDiff {t : ℝ} (ht : 0 < t)
    {u : ℝ → ℝ} (hu_meas : Measurable u) {M : ℝ} (hu_bd : ∀ z : ℝ, |u z| ≤ M) (x : ℝ) :
    fracHeatConv gaussianHeatKernel t u x - u x =
      (1 / 2) * ∫ y : ℝ, gaussDensity t y * secondDiff u x y := by
  have hg : Integrable (fun y : ℝ => gaussDensity t y) volume := by
    have hcongr : (fun y : ℝ => gaussDensity t y) = fun y => gaussianHeatKernel.P y t := by
      funext y; exact (gaussianHeatKernel_P_eq_gaussDensity y ht).symm
    rw [hcongr]
    exact gaussianHeatKernel.integrable_space t ht
  have hg_int : ∀ s : ℝ, Integrable (fun y : ℝ => gaussDensity t y * u (x + s * y)) volume := by
    intro s
    refine (hg.const_mul M).mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · have hm1 : Measurable fun y : ℝ => gaussDensity t y := by
        unfold gaussDensity; fun_prop
      exact (hm1.mul (hu_meas.comp (measurable_const.add
        (measurable_const.mul measurable_id)))).aestronglyMeasurable
    · have hp : 0 ≤ gaussDensity t y := by unfold gaussDensity; positivity
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp]
      exact (mul_le_mul_of_nonneg_left (hu_bd _) hp).trans_eq (mul_comm _ _)
  have hp_int : Integrable (fun y : ℝ => gaussDensity t y * u (x + y)) volume := by
    simpa [one_mul] using hg_int 1
  have hm_int : Integrable (fun y : ℝ => gaussDensity t y * u (x - y)) volume := by
    simpa [sub_eq_add_neg, neg_one_mul] using hg_int (-1)
  have hc_int : Integrable (fun y : ℝ => gaussDensity t y * u x) volume := hg.mul_const (u x)
  have hconv : fracHeatConv gaussianHeatKernel t u x =
      ∫ y : ℝ, gaussDensity t y * u (x - y) := by
    unfold fracHeatConv
    rw [← integral_sub_left_eq_self (fun y => gaussianHeatKernel.P (x - y) t * u y) volume x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [show x - (x - y) = y by ring, gaussianHeatKernel_P_eq_gaussDensity y ht]
  have hsym : ∫ y : ℝ, gaussDensity t y * u (x - y) =
      ∫ y : ℝ, gaussDensity t y * u (x + y) := by
    rw [← integral_neg_eq_self (fun y => gaussDensity t y * u (x - y))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    have heven : gaussDensity t (-y) = gaussDensity t y := by
      unfold gaussDensity; simp
    rw [heven, sub_neg_eq_add]
  have hunit : ∫ y : ℝ, gaussDensity t y * u x = u x := by
    rw [integral_mul_const]
    have h1 : (∫ y : ℝ, gaussDensity t y) = 1 := by
      calc ∫ y : ℝ, gaussDensity t y
          = ∫ y : ℝ, gaussianHeatKernel.P y t := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            exact (gaussianHeatKernel_P_eq_gaussDensity y ht).symm
        _ = 1 := gaussianHeatKernel.integral_eq_one t ht
    rw [h1, one_mul]
  have havg : 2 * (fracHeatConv gaussianHeatKernel t u x - u x) =
      ∫ y : ℝ, gaussDensity t y * secondDiff u x y := by
    have hp_s := integral_sub hp_int hc_int
    have hm_s := integral_sub hm_int hc_int
    have hadd := integral_add (hp_int.sub hc_int) (hm_int.sub hc_int)
    change ∫ y : ℝ, (gaussDensity t y * u (x + y) - gaussDensity t y * u x) +
        (gaussDensity t y * u (x - y) - gaussDensity t y * u x) =
      (∫ y : ℝ, gaussDensity t y * u (x + y) - gaussDensity t y * u x) +
        ∫ y : ℝ, gaussDensity t y * u (x - y) - gaussDensity t y * u x at hadd
    rw [hp_s, hm_s, ← hsym, hunit, ← hconv] at hadd
    have hsplit : (fun y : ℝ => gaussDensity t y * secondDiff u x y) =
        fun y : ℝ => (gaussDensity t y * u (x + y) - gaussDensity t y * u x) +
          (gaussDensity t y * u (x - y) - gaussDensity t y * u x) := by
      funext y
      unfold secondDiff
      ring
    rw [hsplit, hadd]
    ring
  linarith

/-- Quadratic Taylor bound for `secondDiff φ x y` of a real Schwartz function `φ : 𝓢(ℝ, ℝ)`:
`|secondDiff φ x y| ≤ 2 * C₂ * y²` where `C₂ = ‖φ''‖_∞`. -/
private theorem abs_secondDiff_le_sq_of_schwartz (φ : 𝓢(ℝ, ℝ)) (x y : ℝ) :
    |secondDiff φ x y| ≤
      2 * SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℝ (SchwartzMap.derivCLM ℝ ℝ φ)) *
        y ^ 2 := by
  let φ' : 𝓢(ℝ, ℝ) := SchwartzMap.derivCLM ℝ ℝ φ
  let φ'' : 𝓢(ℝ, ℝ) := SchwartzMap.derivCLM ℝ ℝ φ'
  let C₂ : ℝ := SchwartzMap.seminorm ℝ 0 0 φ''
  have hC2_bd : ∀ z : ℝ, |φ'' z| ≤ C₂ := fun z => by
    simpa [C₂] using φ''.le_seminorm ℝ 0 0 z
  have hderiv1 : ∀ z : ℝ, deriv (φ : ℝ → ℝ) z = φ' z := fun z =>
    (SchwartzMap.derivCLM_apply ℝ φ z).symm
  have hderiv2 : ∀ z : ℝ, deriv (φ' : ℝ → ℝ) z = φ'' z := fun z =>
    (SchwartzMap.derivCLM_apply ℝ φ' z).symm
  have h_sub_diff : ∀ s : ℝ, |φ' (x + s) - φ' (x - s)| ≤ 2 * C₂ * |s| := by
    intro s
    have hmv := convex_univ.norm_image_sub_le_of_norm_deriv_le
      (fun z _ => φ'.differentiableAt)
      (fun z _ => by rw [hderiv2 z]; exact hC2_bd z)
      (Set.mem_univ (x - s)) (Set.mem_univ (x + s))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, show (x + s) - (x - s) = 2 * s by ring] at hmv
    conv_rhs at hmv => rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [mul_comm C₂ (2 * |s|)]
  let g : ℝ → ℝ := fun s => φ (x + s) + φ (x - s)
  have hg_deriv : ∀ s : ℝ, HasDerivAt g (φ' (x + s) - φ' (x - s)) s := by
    intro s
    have hplus : HasDerivAt (fun t : ℝ => φ (x + t)) (φ' (x + s)) s := by
      have h1 : HasDerivAt (φ : ℝ → ℝ) (φ' (x + s)) (x + s) := by
        simpa [hderiv1] using φ.differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun t : ℝ => x + t) 1 s := (hasDerivAt_id s).const_add x
      have hc : HasDerivAt ((φ : ℝ → ℝ) ∘ fun t : ℝ => x + t) (φ' (x + s) * 1) s := h1.comp s h2
      simpa only [Function.comp_def, mul_one] using hc
    have hminus : HasDerivAt (fun t : ℝ => φ (x - t)) (-φ' (x - s)) s := by
      have h1 : HasDerivAt (φ : ℝ → ℝ) (φ' (x - s)) (x - s) := by
        simpa [hderiv1] using φ.differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun t : ℝ => x - t) (-1) s := (hasDerivAt_id s).const_sub x
      have hc : HasDerivAt ((φ : ℝ → ℝ) ∘ fun t : ℝ => x - t) (φ' (x - s) * (-1)) s := h1.comp s h2
      simpa only [Function.comp_def, mul_neg, mul_one] using hc
    have hsum : HasDerivAt (fun s : ℝ => φ (x + s) + φ (x - s)) (φ' (x + s) + -φ' (x - s)) s :=
      hplus.add hminus
    exact hsum.congr_deriv (sub_eq_add_neg _ _).symm
  have hmv_g := (convex_Icc (0 : ℝ) |y|).norm_image_sub_le_of_norm_deriv_le
    (fun s _ => (hg_deriv s).differentiableAt)
    (fun s hs => by
      rw [(hg_deriv s).deriv, Real.norm_eq_abs]
      have hs_abs : |s| ≤ |y| := by
        rw [abs_of_nonneg hs.1]
        exact hs.2
      have hC2_nn : 0 ≤ C₂ := le_trans (abs_nonneg _) (hC2_bd 0)
      calc |φ' (x + s) - φ' (x - s)| ≤ 2 * C₂ * |s| := h_sub_diff s
        _ ≤ 2 * C₂ * |y| := mul_le_mul_of_nonneg_left hs_abs (by positivity))
    (Set.left_mem_Icc.mpr (abs_nonneg y)) (Set.right_mem_Icc.mpr (abs_nonneg y))
  have hg_abs : g |y| = φ (x + y) + φ (x - y) := by
    rcases le_total 0 y with hy | hy
    · simp [g, abs_of_nonneg hy]
    · simp only [g, abs_of_nonpos hy, sub_neg_eq_add]
      rw [show x + -y = x - y by ring, add_comm]
  have hg_zero : g 0 = 2 * φ x := by
    simp [g]
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_abs, hg_abs, hg_zero] at hmv_g
  refine hmv_g.trans_eq ?_
  rw [mul_assoc (2 * C₂), ← sq, sq_abs]

/-- Helper: if `g : ℝ → ℝ` is even (`∀ y, g (-y) = g y`) and `IntegrableOn g (Ioo 0 1)`, then
`IntegrableOn g (Ioo (-1) 1)`. -/
private theorem integrableOn_Ioo_neg_one_one_of_even {g : ℝ → ℝ}
    (hg_even : ∀ y : ℝ, g (-y) = g y) (hg : IntegrableOn g (Set.Ioo 0 1)) :
    IntegrableOn g (Set.Ioo (-1) 1) := by
  have hneg : IntegrableOn g (Set.Ioo (-1) 0) := by
    have hcomp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (MeasurableEquiv.neg ℝ).measurableEmbedding (f := g) (s := Set.Ioo 0 1)
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Set.Ioo 0 1 = Set.Ioo (-1) 0 := by
      ext y; simp only [Set.mem_preimage, Set.mem_Ioo]; constructor <;> intro ⟨h1, h2⟩ <;>
        constructor <;> linarith
    rw [hpre] at hcomp
    have hmap := hcomp.mpr hg
    refine hmap.congr_fun (fun y _ => hg_even y) measurableSet_Ioo
  have hunion : IntegrableOn g (Set.Ioo (-1) 0 ∪ Set.Ioo 0 1) := hneg.union hg
  have hae : (Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo 0 1 : Set ℝ) =ᵐ[volume]
      (Set.Ioo (-1 : ℝ) 1 : Set ℝ) := by
    have hdiff : ((Set.Ioo (-1 : ℝ) 1) \ (Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo 0 1)) ⊆ {0} := by
      intro y ⟨⟨h1, h2⟩, hnot⟩
      by_contra h0
      rw [Set.mem_singleton_iff] at h0
      rcases lt_or_gt_of_ne h0 with hlt | hgt
      · exact hnot (Or.inl ⟨h1, hlt⟩)
      · exact hnot (Or.inr ⟨hgt, h2⟩)
    have hsub : (Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo 0 1 : Set ℝ) ⊆ Set.Ioo (-1 : ℝ) 1 := by
      intro y hy
      rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [MeasureTheory.ae_eq_set]
    constructor
    · rw [Set.sdiff_eq_empty.mpr hsub]; simp
    · exact measure_mono_null hdiff (by simp)
  exact hunion.congr_set_ae hae.symm

/-- Helper: if `g : ℝ → ℝ` is even and `IntegrableOn g (Ioi 1)`, then
`IntegrableOn g ((Ioo (-1) 1)ᶜ)`. -/
private theorem integrableOn_compl_Ioo_of_even {g : ℝ → ℝ}
    (hg_even : ∀ y : ℝ, g (-y) = g y) (hg : IntegrableOn g (Set.Ioi 1)) :
    IntegrableOn g ((Set.Ioo (-1 : ℝ) 1)ᶜ) := by
  have hneg : IntegrableOn g (Set.Iio (-1)) := by
    have hcomp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (MeasurableEquiv.neg ℝ).measurableEmbedding (f := g) (s := Set.Ioi 1)
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Set.Ioi 1 = Set.Iio (-1) := by
      ext y; simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio]; constructor <;> intro h <;>
        linarith
    rw [hpre] at hcomp
    have hmap := hcomp.mpr hg
    refine hmap.congr_fun (fun y _ => hg_even y) measurableSet_Iio
  have hunion : IntegrableOn g (Set.Iio (-1) ∪ Set.Ioi 1) := hneg.union hg
  have hae : (Set.Iio (-1 : ℝ) ∪ Set.Ioi 1 : Set ℝ) =ᵐ[volume]
      ((Set.Ioo (-1 : ℝ) 1)ᶜ : Set ℝ) := by
    have h1 : ((Set.Ioo (-1 : ℝ) 1)ᶜ \ (Set.Iio (-1 : ℝ) ∪ Set.Ioi 1)) ⊆ {-1, 1} := by
      intro y hy
      simp only [Set.mem_sdiff, Set.mem_compl_iff, Set.mem_Ioo, Set.mem_union, Set.mem_Iio,
        Set.mem_Ioi, not_or, not_lt, Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      rcases hy with ⟨hnot, hy1, hy2⟩
      by_cases hm : y = -1
      · exact Or.inl hm
      · right
        have hlt : -1 < y := lt_of_le_of_ne hy1 (Ne.symm hm)
        by_contra hne
        exact hnot ⟨hlt, lt_of_le_of_ne hy2 hne⟩
    have h2 : (Set.Iio (-1 : ℝ) ∪ Set.Ioi 1 : Set ℝ) ⊆ (Set.Ioo (-1 : ℝ) 1)ᶜ := by
      intro y hy hmem
      simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi] at hy
      simp only [Set.mem_Ioo] at hmem
      rcases hy with hy | hy
      · linarith
      · linarith
    rw [MeasureTheory.ae_eq_set]
    constructor
    · rw [Set.sdiff_eq_empty.mpr h2]; exact measure_empty
    · have hpair : volume ({(-1 : ℝ), 1} : Set ℝ) = 0 :=
        (Set.toFinite ({(-1 : ℝ), 1} : Set ℝ)).measure_zero volume
      exact measure_mono_null h1 hpair
  exact hunion.congr_set_ae hae.symm

/-- Integrability of `y ↦ secondDiff φ x y / |y|^(1 + α)` for real Schwartz `φ`. -/
theorem integrable_secondDiff_div_abs_rpow {α : ℝ} (hα : FractionalExponent α)
    (φ : 𝓢(ℝ, ℝ)) (x : ℝ) :
    Integrable (fun y : ℝ => secondDiff φ x y / |y| ^ (1 + α)) volume := by
  let C0 : ℝ := SchwartzMap.seminorm ℝ 0 0 φ
  let C2 : ℝ := SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℝ (SchwartzMap.derivCLM ℝ ℝ φ))
  have hC0_bd : ∀ z : ℝ, |φ z| ≤ C0 := fun z => by simpa [C0] using φ.le_seminorm ℝ 0 0 z
  have hmeas : Measurable fun y : ℝ => secondDiff φ x y / |y| ^ (1 + α) := by
    have hm1 : Measurable fun y : ℝ => secondDiff φ x y := by
      unfold secondDiff
      exact ((φ.continuous.measurable.comp (measurable_const.add measurable_id)).add
        (φ.continuous.measurable.comp (measurable_const.sub measurable_id))).sub measurable_const
    exact hm1.div ((continuous_abs.rpow_const (fun _ => Or.inr (by linarith [hα.1]))).measurable)
  have hsmall_Ioo : IntegrableOn (fun y : ℝ => |y| ^ (1 - α)) (Set.Ioo 0 1) := by
    have hpos : IntegrableOn (fun z : ℝ => z ^ (1 - α)) (Set.Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith [hα.2] : -1 < 1 - α))
    exact (hpos.mono_set Set.Ioo_subset_Ioc_self).congr_fun
      (fun y hy => by rw [abs_of_pos hy.1]) measurableSet_Ioo
  have hsmall : Integrable (fun y : ℝ => Set.indicator (Set.Ioo (-1) 1)
      (fun y => (2 * C2) * |y| ^ (1 - α)) y) volume := by
    rw [integrable_indicator_iff measurableSet_Ioo]
    exact (integrableOn_Ioo_neg_one_one_of_even (fun y => by simp) hsmall_Ioo).const_mul _
  have hbig_Ioi : IntegrableOn (fun y : ℝ => |y| ^ (-1 - α)) (Set.Ioi 1) := by
    have hpos : IntegrableOn (fun z : ℝ => z ^ (-1 - α)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith [hα.1] : -1 - α < -1) one_pos
    exact hpos.congr_fun (fun y hy => by rw [abs_of_pos (lt_trans one_pos hy)]) measurableSet_Ioi
  have hbig : Integrable (fun y : ℝ => Set.indicator ((Set.Ioo (-1) 1)ᶜ)
      (fun y => (4 * C0) * |y| ^ (-1 - α)) y) volume := by
    rw [integrable_indicator_iff measurableSet_Ioo.compl]
    exact (integrableOn_compl_Ioo_of_even (fun y => by simp) hbig_Ioi).const_mul _
  refine (hsmall.add hbig).mono' hmeas.aestronglyMeasurable ?_
  have hne0 : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hne0] with y hy0
  have habs_pos : 0 < |y| := abs_pos.mpr hy0
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.rpow_pos_of_pos habs_pos _)]
  dsimp only [Pi.add_apply]
  by_cases hy : y ∈ Set.Ioo (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hy, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hy), add_zero]
    have hsd := abs_secondDiff_le_sq_of_schwartz φ x y
    have hdiv := div_le_div_of_nonneg_right hsd (Real.rpow_pos_of_pos habs_pos (1 + α)).le
    refine hdiv.trans_eq ?_
    have hsq_eq : y ^ 2 / |y| ^ (1 + α) = |y| ^ (1 - α) := by
      rw [← sq_abs y, ← Real.rpow_natCast |y| 2, ← Real.rpow_sub habs_pos]
      congr 1; norm_num; ring
    rw [mul_div_assoc, hsq_eq]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_mem hy, zero_add]
    have hsd : |secondDiff φ x y| ≤ 4 * C0 := by
      unfold secondDiff
      have h1 := hC0_bd (x + y)
      have h2 := hC0_bd (x - y)
      have h3 := hC0_bd x
      rw [abs_le] at h1 h2 h3 ⊢
      constructor <;> linarith
    have hdiv := div_le_div_of_nonneg_right hsd (Real.rpow_pos_of_pos habs_pos (1 + α)).le
    refine hdiv.trans_eq ?_
    rw [div_eq_mul_inv, ← Real.rpow_neg habs_pos.le, show -(1 + α) = -1 - α by ring]

/-- **Bochner Heat Subordination Formula (`thm:heat_subordination`)**:
for every `0 < α < 2`, real Schwartz function `φ ∈ 𝓢(ℝ, ℝ)`, and `x ∈ ℝ`,
`(-Δ)^(α/2) φ(x) = Γ(-α/2)⁻¹ ∫_{t > 0} t^(-α/2 - 1) ((e^{tΔ} φ)(x) - φ(x)) dt`. -/
theorem fracLapSecondDiff_eq_heat_subordination {α : ℝ} (hα : FractionalExponent α)
    (φ : 𝓢(ℝ, ℝ)) (x : ℝ) :
    fracLapSecondDiff α φ x =
      (Real.Gamma (-α / 2))⁻¹ *
        ∫ t in Set.Ioi (0 : ℝ), t ^ (-α / 2 - 1) *
          (fracHeatConv gaussianHeatKernel t φ x - φ x) := by
  have hα0 : 0 < α := hα.1
  have hβ0 : 0 < α / 2 := by linarith
  have hβ1 : α / 2 < 1 := by linarith [hα.2]
  have hc_pos : 0 < levyConst (α / 2) := levyConst_pos hβ0 hβ1
  let H : ℝ → ℝ → ℝ := fun t y => t ^ (-α / 2 - 1) * gaussDensity t y * secondDiff φ x y
  have hH_meas : Measurable (Function.uncurry H) := by
    unfold H gaussDensity secondDiff
    have hφm : Measurable (φ : ℝ → ℝ) := φ.continuous.measurable
    have h1 : Measurable fun p : ℝ × ℝ => p.1 ^ (-α / 2 - 1) :=
      measurable_fst.pow_const _
    have h2 : Measurable fun p : ℝ × ℝ =>
        (4 * π * p.1) ^ (-1 / 2 : ℝ) * exp (-(p.2 ^ 2 / 4 / p.1)) := by
      fun_prop
    have h3 : Measurable fun p : ℝ × ℝ =>
        φ (x + p.2) + φ (x - p.2) - 2 * φ x :=
      ((hφm.comp (measurable_const.add measurable_snd)).add
        (hφm.comp (measurable_const.sub measurable_snd))).sub measurable_const
    exact (h1.mul h2).mul h3
  -- Compute the inner `t`-integral of `t^(-α/2-1) gaussDensity t y`
  have ht_ker : ∀ {y : ℝ}, y ≠ 0 →
      ∫ t in Set.Ioi (0 : ℝ), t ^ (-α / 2 - 1) * gaussDensity t y =
        (fracLapConstant α / levyConst (α / 2)) * |y| ^ (-1 - α) := by
    intro y hy
    have hlk := levy_kernel_eq hα hy
    have hcongr : (fun s : ℝ => levyConst (α / 2) * s ^ (-1 - α / 2) * gaussDensity s y) =
        fun s : ℝ => levyConst (α / 2) * (s ^ (-α / 2 - 1) * gaussDensity s y) := by
      funext s; ring_nf
    rw [hcongr, integral_const_mul] at hlk
    rw [div_mul_eq_mul_div, eq_div_iff hc_pos.ne', mul_comm]
    exact hlk
  -- Establish joint integrability of `H` on `(volume.restrict (Ioi 0)).prod volume`
  have ht_ker_integrable : ∀ {y : ℝ}, y ≠ 0 →
      IntegrableOn (fun t : ℝ => t ^ (-α / 2 - 1) * gaussDensity t y) (Set.Ioi 0) := by
    intro y hy
    have hlk := integrableOn_rpow_exp_inv (by positivity : 0 < y ^ 2 / 4) hβ0
    refine IntegrableOn.congr_fun (hlk.const_mul ((4 * π) ^ (-1 / 2 : ℝ)))
      (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := ht
    unfold gaussDensity
    rw [Real.mul_rpow (by positivity) ht0.le]
    have e : t ^ (-α / 2 - 1) * t ^ (-1 / 2 : ℝ) = t ^ (-3 / 2 - α / 2) := by
      rw [← Real.rpow_add ht0]
      congr 1; ring
    calc (4 * π) ^ (-1 / 2 : ℝ) * (t ^ (-3 / 2 - α / 2) * exp (-(y ^ 2 / 4 / t)))
        = (4 * π) ^ (-1 / 2 : ℝ) * ((t ^ (-α / 2 - 1) * t ^ (-1 / 2 : ℝ)) *
            exp (-(y ^ 2 / 4 / t))) := by rw [e]
      _ = t ^ (-α / 2 - 1) * ((4 * π) ^ (-1 / 2 : ℝ) * t ^ (-1 / 2 : ℝ) *
            exp (-(y ^ 2 / 4 / t))) := by ring
  have hH_lintegral :
      ∫⁻ p : ℝ × ℝ, ‖Function.uncurry H p‖ₑ ∂((volume.restrict (Set.Ioi 0)).prod volume) < ∞ := by
    rw [lintegral_prod_symm _ hH_meas.eNorm.aemeasurable]
    simp_rw [Function.uncurry]
    have hy_step : ∀ᵐ y : ℝ ∂volume,
        (∫⁻ t in Set.Ioi (0 : ℝ), ‖H t y‖ₑ) =
          ENNReal.ofReal (fracLapConstant α / levyConst (α / 2)) *
            ENNReal.ofReal |secondDiff φ x y / |y| ^ (1 + α)| := by
      have hne0 : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by rw [ae_iff]; simp
      filter_upwards [hne0] with y hy
      have hnonneg : ∀ t ∈ Set.Ioi (0 : ℝ),
          0 ≤ t ^ (-α / 2 - 1) * gaussDensity t y := fun t ht => by
        have ht0 : 0 < t := ht
        unfold gaussDensity
        exact mul_nonneg (Real.rpow_nonneg ht0.le _) (by positivity)
      have heq_t : ∀ t ∈ Set.Ioi (0 : ℝ), ‖H t y‖ₑ =
          ENNReal.ofReal |secondDiff φ x y| *
            ENNReal.ofReal (t ^ (-α / 2 - 1) * gaussDensity t y) := by
        intro t ht
        have hp := hnonneg t ht
        rw [Real.eNorm_eq_ofReal_abs,
          show |H t y| = |secondDiff φ x y| * (t ^ (-α / 2 - 1) * gaussDensity t y) from by
            dsimp [H]; rw [abs_mul, abs_of_nonneg hp, mul_comm]]
        exact ENNReal.ofReal_mul (abs_nonneg _)
      have hm_gauss : Measurable fun t : ℝ =>
          ENNReal.ofReal (t ^ (-α / 2 - 1) * gaussDensity t y) := by
        refine ENNReal.measurable_ofReal.comp ?_
        unfold gaussDensity
        fun_prop
      rw [setLIntegral_congr_fun measurableSet_Ioi heq_t, lintegral_const_mul _ hm_gauss]
      have hint_t :
          (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-α / 2 - 1) * gaussDensity t y)) =
          ENNReal.ofReal ((fracLapConstant α / levyConst (α / 2)) * |y| ^ (-1 - α)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (ht_ker_integrable hy)
          (ae_restrict_of_forall_mem measurableSet_Ioi hnonneg), ht_ker hy]
      rw [hint_t, ← ENNReal.ofReal_mul (abs_nonneg _)]
      have hpow_pos : 0 < |y| ^ (1 + α) := Real.rpow_pos_of_pos (abs_pos.mpr hy) _
      have hconst_nn : 0 ≤ fracLapConstant α / levyConst (α / 2) :=
        div_nonneg (fracLapConstant_pos hα).le hc_pos.le
      rw [← ENNReal.ofReal_mul hconst_nn]
      congr 1
      rw [abs_div, abs_of_pos hpow_pos,
        show (-1 - α : ℝ) = -(1 + α) by ring, Real.rpow_neg (abs_nonneg y), div_eq_mul_inv]
      ring
    have hm_div : Measurable fun y : ℝ => ENNReal.ofReal |secondDiff φ x y / |y| ^ (1 + α)| := by
      refine ENNReal.measurable_ofReal.comp ?_
      have hφm : Measurable (φ : ℝ → ℝ) := φ.continuous.measurable
      have hm1 : Measurable fun y : ℝ => secondDiff φ x y := by
        unfold secondDiff
        exact ((hφm.comp (measurable_const.add measurable_id)).add
          (hφm.comp (measurable_const.sub measurable_id))).sub measurable_const
      exact continuous_abs.measurable.comp (hm1.div ((continuous_abs.rpow_const (p := 1 + α)
        (fun _ => Or.inr (by linarith [hα.1]))).measurable))
    rw [lintegral_congr_ae hy_step, lintegral_const_mul _ hm_div]
    have hfin : (∫⁻ y : ℝ, ENNReal.ofReal |secondDiff φ x y / |y| ^ (1 + α)|) < ∞ := by
      have hhas := (integrable_secondDiff_div_abs_rpow hα φ x).hasFiniteIntegral
      simpa only [HasFiniteIntegral, Real.eNorm_eq_ofReal_abs] using hhas
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  have hH_int : Integrable (Function.uncurry H) ((volume.restrict (Set.Ioi 0)).prod volume) :=
    ⟨hH_meas.aestronglyMeasurable, hH_lintegral⟩
  have hswap := integral_integral_swap hH_int
  let C0 : ℝ := SchwartzMap.seminorm ℝ 0 0 φ
  have hC0_bd : ∀ z : ℝ, |φ z| ≤ C0 := fun z => by simpa [C0] using φ.le_seminorm ℝ 0 0 z
  have hLHS : ∫ t in Set.Ioi (0 : ℝ), ∫ y : ℝ, H t y =
      2 * ∫ t in Set.Ioi (0 : ℝ), t ^ (-α / 2 - 1) *
        (fracHeatConv gaussianHeatKernel t φ x - φ x) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hmul : ∫ y : ℝ, H t y =
        t ^ (-α / 2 - 1) * ∫ y : ℝ, gaussDensity t y * secondDiff φ x y := by
      have heq : (fun y : ℝ => H t y) =
          fun y => t ^ (-α / 2 - 1) * (gaussDensity t y * secondDiff φ x y) := by
        funext y; dsimp [H]; ring
      rw [heq, integral_const_mul]
    rw [hmul, fracHeatConv_gaussian_sub_eq_secondDiff ht φ.continuous.measurable hC0_bd x]
    ring
  have hRHS : ∫ y : ℝ, ∫ t in Set.Ioi (0 : ℝ), H t y =
      (fracLapConstant α / levyConst (α / 2)) * ∫ y : ℝ, secondDiff φ x y / |y| ^ (1 + α) := by
    rw [← integral_const_mul]
    have hne0 : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by rw [ae_iff]; simp
    refine integral_congr_ae ?_
    filter_upwards [hne0] with y hy
    have hmul : ∫ t in Set.Ioi (0 : ℝ), H t y =
        secondDiff φ x y * ∫ t in Set.Ioi (0 : ℝ), t ^ (-α / 2 - 1) * gaussDensity t y := by
      have heq : (fun t : ℝ => H t y) =
          fun t => secondDiff φ x y * (t ^ (-α / 2 - 1) * gaussDensity t y) := by
        funext t; dsimp [H]; ring
      rw [heq, integral_const_mul]
    rw [hmul, ht_ker hy, show (-1 - α : ℝ) = -(1 + α) by ring, Real.rpow_neg (abs_nonneg y),
      div_eq_mul_inv]
    ring
  rw [hLHS, hRHS] at hswap
  rw [inv_gamma_neg_half_eq_neg_levyConst hα]
  unfold fracLapSecondDiff
  have hdiv2 : ∫ t in Set.Ioi (0 : ℝ), t ^ (-α / 2 - 1) *
      (fracHeatConv gaussianHeatKernel t φ x - φ x) =
      (fracLapConstant α / (2 * levyConst (α / 2))) *
        ∫ y : ℝ, secondDiff φ x y / |y| ^ (1 + α) := by
    field_simp at hswap ⊢
    linarith
  rw [hdiv2]
  field_simp

end

end FracLap
