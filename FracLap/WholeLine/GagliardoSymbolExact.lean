/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.GagliardoScaling
public import FracLap.WholeLine.StableLevy

/-!
# FracLap.WholeLine.GagliardoSymbolExact

The exact Fourier symbol of the Gagliardo energy: `Λ_α(ξ) = |2π ξ|^α`. Equivalently the classical
identity `C(α) ∫ (1 - cos (ξ h)) |h|^(-1-α) dh = |ξ|^α` with
`C(α) = 2^(α-1) α Γ((1+α)/2) / (√π Γ(1 - α/2))`.

The proof is by Bochner subordination of the Gaussian:
`|ξ|^α = c_β ∫ (1 - e^{-s ξ²}) s^(-1-β) ds` (Lévy--Khintchine, `StableLevy`, `β = α/2`) and
`1 - e^{-s ξ²} = ∫ (1 - cos (ξ h)) g_s(h) dh` for the Gaussian density `g_s`;
Tonelli turns the two integrals into `∫ (1 - cos (ξ h)) K(h) dh` with
`K(h) = c_β ∫ g_s(h) s^(-1-β) ds = C(α) |h|^(-1-α)`.

- `integral_rpow_exp_inv`: `∫_{s > 0} s^(-3/2-β) exp (-A/s) ds = A^(-(β+1/2)) Γ(β + 1/2)`.
- `levy_kernel_eq`: `c_β ∫_{s > 0} g_s(h) s^(-1-β) ds = C(α) |h|^(-1-α)` for `h ≠ 0`.
- `gagliardoSymbol_exact`: `Λ_α(ξ) = |2π ξ|^α`.
-/

namespace FracLap

open MeasureTheory Real Set
open scoped ENNReal FourierTransform

@[expose] public section

/-- `∫_{s > 0} s^(-3/2-β) exp (-A/s) ds = (1/A)^(β+1/2) Γ(β + 1/2)`, by the inversion `s ↦ 1/s`. -/
theorem integral_rpow_exp_inv {A β : ℝ} (hA : 0 < A) (hβ : 0 < β) :
    ∫ s in Ioi (0 : ℝ), s ^ (-3 / 2 - β) * exp (-(A / s)) =
      (1 / A) ^ (β + 1 / 2) * Gamma (β + 1 / 2) := by
  have h := integral_comp_rpow_Ioi (fun y : ℝ => y ^ (β + 1 / 2 - 1) * exp (-(A * y)))
    (p := -1) (by norm_num)
  rw [integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hA] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := hx
  have e1 : (x ^ (-1 : ℝ)) ^ (β + 1 / 2 - 1) = x ^ (-(β + 1 / 2 - 1)) := by
    rw [← Real.rpow_mul hx0.le]
    ring_nf
  have e2 : x ^ (-1 - 1 : ℝ) * x ^ (-(β + 1 / 2 - 1)) = x ^ (-3 / 2 - β) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have e3 : exp (-(A * x ^ (-1 : ℝ))) = exp (-(A / x)) := by
    rw [Real.rpow_neg_one, div_eq_mul_inv]
  simp only [smul_eq_mul, abs_neg, abs_one, one_mul]
  rw [e1, e3, ← e2]
  ring

/-- The Gaussian heat density `g_s(h) = (4π s)^(-1/2) exp (-h² / (4 s))`. -/
noncomputable def gaussDensity (s h : ℝ) : ℝ := (4 * π * s) ^ (-1 / 2 : ℝ) * exp (-(h ^ 2 / 4 / s))

/-- **The subordinated kernel**: for `h ≠ 0` and `0 < α < 2` (with `β = α / 2`),
`c_β ∫_{s > 0} s^(-1-β) g_s(h) ds = C(α) |h|^(-1-α)`. -/
theorem levy_kernel_eq {α h : ℝ} (hα : FractionalExponent α) (hh : h ≠ 0) :
    ∫ s in Ioi (0 : ℝ), levyConst (α / 2) * s ^ (-1 - α / 2) * gaussDensity s h =
      fracLapConstant α * |h| ^ (-1 - α) := by
  have hα0 := hα.1
  have hβ : 0 < α / 2 := by linarith
  have hA : 0 < h ^ 2 / 4 := by positivity
  have hpt : ∀ s ∈ Ioi (0 : ℝ), levyConst (α / 2) * s ^ (-1 - α / 2) * gaussDensity s h =
      (levyConst (α / 2) * (4 * π) ^ (-1 / 2 : ℝ)) *
        (s ^ (-3 / 2 - α / 2) * exp (-(h ^ 2 / 4 / s))) := by
    intro s hs
    have hs0 : 0 < s := hs
    have e : s ^ (-1 - α / 2) * s ^ (-1 / 2 : ℝ) = s ^ (-3 / 2 - α / 2) := by
      rw [← Real.rpow_add hs0]
      congr 1
      ring
    unfold gaussDensity
    rw [Real.mul_rpow (by positivity) hs0.le]
    calc levyConst (α / 2) * s ^ (-1 - α / 2) *
        ((4 * π) ^ (-1 / 2 : ℝ) * s ^ (-1 / 2 : ℝ) * exp (-(h ^ 2 / 4 / s)))
        = (levyConst (α / 2) * (4 * π) ^ (-1 / 2 : ℝ)) *
          ((s ^ (-1 - α / 2) * s ^ (-1 / 2 : ℝ)) * exp (-(h ^ 2 / 4 / s))) := by ring
      _ = _ := by rw [e]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_rpow_exp_inv hA (by linarith : 0 < α / 2)]
  have hsq : (4 * π) ^ (-1 / 2 : ℝ) = 1 / (2 * √π) := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg (by positivity),
      ← Real.sqrt_eq_rpow, show (4 : ℝ) * π = 2 ^ 2 * π by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    simp
  have habs : 0 < |h| := abs_pos.mpr hh
  have hA2 : (1 / (h ^ 2 / 4)) ^ (α / 2 + 1 / 2) = 2 ^ (1 + α) * |h| ^ (-1 - α) := by
    have e1 : 1 / (h ^ 2 / 4) = (2 / |h|) ^ (2 : ℕ) := by
      rw [div_pow, sq_abs]
      field_simp
      norm_num
    have e2 : ((2 : ℕ) : ℝ) * (α / 2 + 1 / 2) = 1 + α := by push_cast; ring
    rw [e1, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      Real.div_rpow (by norm_num) habs.le, e2, show (-1 - α : ℝ) = -(1 + α) by ring,
      Real.rpow_neg habs.le, div_eq_mul_inv]
  have hΓ : 0 < Gamma (1 - α / 2) := Real.Gamma_pos_of_pos (by linarith [hα.2])
  have h2 : (2 : ℝ) ^ (1 + α) = 2 ^ (α - 1) * 4 := by
    rw [show (1 + α) = (α - 1) + 2 by ring, Real.rpow_add (by norm_num)]
    norm_num
  have hsqrt : 0 < √π := Real.sqrt_pos.mpr pi_pos
  rw [hsq, hA2, h2]
  unfold levyConst fracLapConstant
  rw [show α / 2 + 1 / 2 = (1 + α) / 2 by ring]
  field_simp
  ring

/-- Integrability of the subordinated kernel integrand. -/
theorem integrableOn_rpow_exp_inv {A β : ℝ} (hA : 0 < A) (hβ : 0 < β) :
    IntegrableOn (fun s : ℝ => s ^ (-3 / 2 - β) * exp (-(A / s))) (Ioi 0) := by
  have hg : IntegrableOn (fun y : ℝ => y ^ (β + 1 / 2 - 1) * exp (-(A * y))) (Ioi 0) := by
    simpa only [neg_mul] using integrableOn_rpow_mul_exp_neg_mul_rpow (s := β + 1 / 2 - 1)
      (p := 1) (b := A) (by linarith) one_pos hA |>.congr_fun (fun y _ => by simp) measurableSet_Ioi
  have h := (integrableOn_Ioi_comp_rpow_iff _ (p := -1) (by norm_num)).mpr hg
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : 0 < x := hx
  have e1 : (x ^ (-1 : ℝ)) ^ (β + 1 / 2 - 1) = x ^ (-(β + 1 / 2 - 1)) := by
    rw [← Real.rpow_mul hx0.le]
    ring_nf
  have e2 : x ^ (-1 - 1 : ℝ) * x ^ (-(β + 1 / 2 - 1)) = x ^ (-3 / 2 - β) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have e3 : exp (-(A * x ^ (-1 : ℝ))) = exp (-(A / x)) := by
    rw [Real.rpow_neg_one, div_eq_mul_inv]
  simp only [smul_eq_mul, abs_neg, abs_one, one_mul]
  rw [e1, e3, ← e2]
  ring

/-- The Gaussian density integrates to `1` against `1` and to `exp (-s x²)` against `cos (x ·)`:
`∫ g_s(h) (1 - cos (x h)) dh = 1 - exp (-s x²)`. -/
theorem integral_gaussDensity_one_sub_cos {s : ℝ} (hs : 0 < s) (x : ℝ) :
    ∫ h, gaussDensity s h * (1 - cos (x * h)) = 1 - exp (-(s * x ^ 2)) := by
  have hb : 0 < 1 / (4 * s) := by positivity
  have hint : ∀ a : ℝ, Integrable (fun h : ℝ => exp (-(1 / (4 * s)) * h ^ 2) * cos (a * h)) := by
    intro a
    have h0 : Integrable (fun h : ℝ => exp (-(1 / (4 * s)) * h ^ 2)) := by
      simpa [neg_mul] using integrable_exp_neg_mul_sq hb
    refine h0.mono' (by fun_prop : Continuous fun h : ℝ => exp (-(1 / (4 * s)) * h ^ 2) *
      cos (a * h)).aestronglyMeasurable (Filter.Eventually.of_forall fun h => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact mul_le_of_le_one_right (exp_pos _).le (abs_cos_le_one _)
  have hg : ∀ h : ℝ, gaussDensity s h = (4 * π * s) ^ (-1 / 2 : ℝ) *
      exp (-(1 / (4 * s)) * h ^ 2) := by
    intro h
    unfold gaussDensity
    congr 2
    field_simp
  have hnorm : (4 * π * s) ^ (-1 / 2 : ℝ) * √(π / (1 / (4 * s))) = 1 := by
    have h4 : π / (1 / (4 * s)) = 4 * π * s := by field_simp
    rw [h4, show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg (by positivity),
      ← Real.sqrt_eq_rpow]
    exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (by positivity)).ne'
  have hcos : ∫ h : ℝ, exp (-(1 / (4 * s)) * h ^ 2) * cos (x * h) =
      √(π / (1 / (4 * s))) * exp (-s * x ^ 2) := by
    rw [integral_exp_neg_mul_sq_mul_cos hb x]
    congr 2
    field_simp
  have hone := integral_exp_neg_mul_sq_mul_cos hb 0
  simp only [zero_mul, Real.cos_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, neg_zero, zero_div, exp_zero] at hone
  simp_rw [hg]
  have hsplit : ∀ h : ℝ, (4 * π * s) ^ (-1 / 2 : ℝ) * exp (-(1 / (4 * s)) * h ^ 2) *
      (1 - cos (x * h)) =
      (4 * π * s) ^ (-1 / 2 : ℝ) * (exp (-(1 / (4 * s)) * h ^ 2) -
        exp (-(1 / (4 * s)) * h ^ 2) * cos (x * h)) := fun h => by ring
  simp_rw [hsplit]
  have hI1 : Integrable (fun h : ℝ => exp (-(1 / (4 * s)) * h ^ 2)) := by
    simpa [neg_mul] using integrable_exp_neg_mul_sq hb
  rw [integral_const_mul, integral_sub hI1 (hint x), hone, hcos]
  have : (4 * π * s) ^ (-1 / 2 : ℝ) * (√(π / (1 / (4 * s))) -
      √(π / (1 / (4 * s))) * exp (-s * x ^ 2)) = 1 - exp (-(s * x ^ 2)) := by
    rw [mul_sub, hnorm, ← mul_assoc, hnorm, neg_mul, one_mul]
  rw [this]

/-- `h ↦ g_s(h) (1 - cos (x h))` is integrable. -/
theorem integrable_gaussDensity_one_sub_cos {s : ℝ} (hs : 0 < s) (x : ℝ) :
    Integrable fun h : ℝ => gaussDensity s h * (1 - cos (x * h)) := by
  have hb : 0 < 1 / (4 * s) := by positivity
  have h0 : Integrable (fun h : ℝ => (4 * π * s) ^ (-1 / 2 : ℝ) *
      exp (-(1 / (4 * s)) * h ^ 2)) := by
    have : Integrable (fun h : ℝ => exp (-(1 / (4 * s)) * h ^ 2)) := by
      simpa [neg_mul] using integrable_exp_neg_mul_sq hb
    exact this.const_mul _
  have hg : ∀ h : ℝ, gaussDensity s h = (4 * π * s) ^ (-1 / 2 : ℝ) *
      exp (-(1 / (4 * s)) * h ^ 2) := by
    intro h
    unfold gaussDensity
    congr 2
    field_simp
  simp_rw [hg]
  refine (h0.const_mul 2).mono' (by fun_prop : Continuous fun h : ℝ =>
    (4 * π * s) ^ (-1 / 2 : ℝ) * exp (-(1 / (4 * s)) * h ^ 2) *
      (1 - cos (x * h))).aestronglyMeasurable (Filter.Eventually.of_forall fun h => ?_)
  have hp : 0 ≤ (4 * π * s) ^ (-1 / 2 : ℝ) * exp (-(1 / (4 * s)) * h ^ 2) := by positivity
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp]
  have h1 : |1 - cos (x * h)| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [neg_one_le_cos (x * h), cos_le_one (x * h)]
  nlinarith

/-- The integrand of the subordination identity (nonnegative for `s > 0`). -/
noncomputable def subIntegrand (α x s h : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (levyConst (α / 2) * s ^ (-1 - α / 2) * gaussDensity s h * (1 - cos (x * h)))

theorem measurable_subIntegrand (α x : ℝ) :
    Measurable (Function.uncurry fun h s : ℝ => subIntegrand α x s h) := by
  unfold subIntegrand gaussDensity
  refine ENNReal.measurable_ofReal.comp ?_
  fun_prop

/-- **Subordination identity, lintegral form**: for every real `x` and `0 < α < 2`,
`∫ C(α) |h|^(-1-α) (1 - cos (x h)) dh = |x|^α`. -/
theorem lintegral_kernel_one_sub_cos {α : ℝ} (hα : FractionalExponent α) (x : ℝ) :
    ∫⁻ h, ENNReal.ofReal (fracLapConstant α * |h| ^ (-1 - α) * (1 - cos (x * h))) =
      ENNReal.ofReal (|x| ^ α) := by
  have hα0 := hα.1
  have hβ : 0 < α / 2 := by linarith
  have hβ1 : α / 2 < 1 := by linarith [hα.2]
  have hc : 0 < levyConst (α / 2) := levyConst_pos hβ hβ1
  -- Step 1: the `h`-integrand as an `s`-integral
  have step1 : ∀ h : ℝ, ENNReal.ofReal (fracLapConstant α * |h| ^ (-1 - α) * (1 - cos (x * h))) =
      ∫⁻ s in Ioi (0 : ℝ), subIntegrand α x s h := by
    intro h
    by_cases hh : h = 0
    · subst hh
      simp [subIntegrand]
    · have hA : 0 < h ^ 2 / 4 := by positivity
      have hpt : ∀ s ∈ Ioi (0 : ℝ), levyConst (α / 2) * s ^ (-1 - α / 2) * gaussDensity s h *
          (1 - cos (x * h)) = ((levyConst (α / 2) * (4 * π) ^ (-1 / 2 : ℝ)) * (1 - cos (x * h))) *
            (s ^ (-3 / 2 - α / 2) * exp (-(h ^ 2 / 4 / s))) := by
        intro s hs
        have hs0 : 0 < s := hs
        have e : s ^ (-1 - α / 2) * s ^ (-1 / 2 : ℝ) = s ^ (-3 / 2 - α / 2) := by
          rw [← Real.rpow_add hs0]
          congr 1
          ring
        unfold gaussDensity
        rw [Real.mul_rpow (by positivity) hs0.le]
        calc levyConst (α / 2) * s ^ (-1 - α / 2) *
            ((4 * π) ^ (-1 / 2 : ℝ) * s ^ (-1 / 2 : ℝ) * exp (-(h ^ 2 / 4 / s))) *
              (1 - cos (x * h))
            = ((levyConst (α / 2) * (4 * π) ^ (-1 / 2 : ℝ)) * (1 - cos (x * h))) *
              ((s ^ (-1 - α / 2) * s ^ (-1 / 2 : ℝ)) * exp (-(h ^ 2 / 4 / s))) := by ring
          _ = _ := by rw [e]
      have hint : IntegrableOn (fun s : ℝ => levyConst (α / 2) * s ^ (-1 - α / 2) *
          gaussDensity s h * (1 - cos (x * h))) (Ioi 0) := by
        have h0 : IntegrableOn (fun s : ℝ => ((levyConst (α / 2) * (4 * π) ^ (-1 / 2 : ℝ)) *
            (1 - cos (x * h))) * (s ^ (-3 / 2 - α / 2) * exp (-(h ^ 2 / 4 / s)))) (Ioi 0) :=
          (integrableOn_rpow_exp_inv hA hβ).const_mul _
        exact h0.congr_fun (fun s hs => (hpt s hs).symm) measurableSet_Ioi
      have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun s : ℝ =>
          levyConst (α / 2) * s ^ (-1 - α / 2) * gaussDensity s h * (1 - cos (x * h)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 < s := hs
        have : 0 ≤ 1 - cos (x * h) := sub_nonneg.mpr (cos_le_one _)
        unfold gaussDensity
        positivity
      unfold subIntegrand
      rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
      congr 1
      have := levy_kernel_eq hα hh
      calc fracLapConstant α * |h| ^ (-1 - α) * (1 - cos (x * h))
          = (∫ s in Ioi (0 : ℝ), levyConst (α / 2) * s ^ (-1 - α / 2) * gaussDensity s h) *
              (1 - cos (x * h)) := by rw [this]
        _ = _ := by rw [← integral_mul_const]
  -- Step 2: Tonelli
  rw [lintegral_congr step1]
  rw [lintegral_lintegral_swap (μ := (volume : Measure ℝ)) (ν := volume.restrict (Ioi (0 : ℝ)))
    (measurable_subIntegrand α x).aemeasurable]
  -- Step 3: inner `h`-integral for `s > 0`
  have step3 : ∀ s ∈ Ioi (0 : ℝ), ∫⁻ h, subIntegrand α x s h =
      ENNReal.ofReal (levyConst (α / 2) * s ^ (-1 - α / 2) * (1 - exp (-(x ^ 2 * s)))) := by
    intro s hs
    have hs0 : 0 < s := hs
    have hKnn : 0 ≤ levyConst (α / 2) * s ^ (-1 - α / 2) :=
      mul_nonneg hc.le (Real.rpow_nonneg hs0.le _)
    have hint := (integrable_gaussDensity_one_sub_cos hs0 x).const_mul
      (levyConst (α / 2) * s ^ (-1 - α / 2))
    have hnn : 0 ≤ᵐ[volume] fun h : ℝ => levyConst (α / 2) * s ^ (-1 - α / 2) *
        (gaussDensity s h * (1 - cos (x * h))) :=
      Filter.Eventually.of_forall fun h => mul_nonneg hKnn (mul_nonneg (by
        unfold gaussDensity; positivity) (sub_nonneg.mpr (cos_le_one _)))
    have hre : (fun h : ℝ => subIntegrand α x s h) = fun h : ℝ => ENNReal.ofReal
        (levyConst (α / 2) * s ^ (-1 - α / 2) * (gaussDensity s h * (1 - cos (x * h)))) :=
      funext fun h => by
        unfold subIntegrand
        congr 1
        ring
    rw [hre, ← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
      integral_gaussDensity_one_sub_cos hs0 x]
    congr 1
    ring_nf
  rw [setLIntegral_congr_fun measurableSet_Ioi (fun s hs => step3 s hs)]
  -- Step 4: Lévy--Khintchine
  by_cases hx : x = 0
  · subst hx
    simp [Real.zero_rpow hα0.ne']
  · have hlam : 0 < x ^ 2 := by positivity
    have hint : IntegrableOn (fun s : ℝ => levyConst (α / 2) *
        ((1 - exp (-(x ^ 2 * s))) * s ^ (-1 - α / 2))) (Ioi 0) :=
      (integrableOn_one_sub_exp_scaled hβ hβ1 hlam).const_mul _
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun s : ℝ => levyConst (α / 2) *
        ((1 - exp (-(x ^ 2 * s))) * s ^ (-1 - α / 2)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 < s := hs
      have : exp (-(x ^ 2 * s)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      exact mul_nonneg hc.le (mul_nonneg (by linarith) (Real.rpow_nonneg hs0.le _))
    have hfun : ∀ s : ℝ, ENNReal.ofReal (levyConst (α / 2) * s ^ (-1 - α / 2) *
        (1 - exp (-(x ^ 2 * s)))) = ENNReal.ofReal (levyConst (α / 2) *
        ((1 - exp (-(x ^ 2 * s))) * s ^ (-1 - α / 2))) := fun s => by ring_nf
    simp_rw [hfun]
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
      integral_one_sub_exp_scaled hβ hβ1 hlam]
    congr 1
    have hΓ : Gamma (1 - α / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
    have : levyConst (α / 2) * ((x ^ 2) ^ (α / 2) * (Gamma (1 - α / 2) / (α / 2))) =
        (x ^ 2) ^ (α / 2) := by
      unfold levyConst
      field_simp
      exact div_self (by rw [show (2 - α) / 2 = 1 - α / 2 by ring]; exact hΓ)
    rw [this, sq_rpow_half]

/-- `‖e^{2π i x} - 1‖² = 2 - 2 cos (2π x)`. -/
theorem norm_fourierChar_sub_one_sq_eq (x : ℝ) :
    ‖((𝐞 x : Circle) : ℂ) - 1‖ ^ 2 = 2 - 2 * cos (2 * π * x) := by
  rw [Real.fourierChar_apply, ← Complex.normSq_eq_norm_sq, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.mul_im, Complex.ofReal_im, Complex.I_im, Complex.one_re,
    Complex.sub_im, Complex.add_im, Complex.one_im]
  nlinarith [sin_sq_add_cos_sq (2 * π * x)]

/-- **The exact Fourier symbol of the Gagliardo energy**: for `0 < α < 2`,
`Λ_α(ξ) = |2π ξ|^α`. Combined with `lintegral_gagliardo_energy_fourier` this gives
`E_α(f) = ∫ |2π ξ|^α ‖𝓕 f(ξ)‖² dξ`, the exact identification of the singular-integral energy
with the Fourier multiplier `(−Δ)^(α/2)` used in `FracLap.WholeLine.FourierSemigroup`. -/
theorem gagliardoSymbol_exact {α : ℝ} (hα : FractionalExponent α) (ξ : ℝ) :
    gagliardoSymbol α ξ = ENNReal.ofReal (|2 * π * ξ| ^ α) := by
  rw [← lintegral_kernel_one_sub_cos hα (2 * π * ξ)]
  unfold gagliardoSymbol
  refine lintegral_congr fun h => ?_
  rw [enorm_rpow_two_eq_ofReal, gagliardoWeight_mul_ofReal hα,
    norm_fourierChar_sub_one_sq_eq]
  congr 1
  have hexp : (-1 - α) = -(1 + α) := by ring
  rw [hexp, Real.rpow_neg (abs_nonneg h)]
  have : 2 * π * (h * ξ) = 2 * π * ξ * h := by ring
  rw [this]
  field_simp

/-- **Exact energy identity**: for `0 < α < 2` and `f ∈ L²(ℝ; ℂ)`,
`E_α(f) = ∫ |2π ξ|^α ‖𝓕 f(ξ)‖² dξ` in `[0, ∞]`. -/
theorem gagliardoEnergyC_eq_lintegral {α : ℝ} (hα : FractionalExponent α) (f : L2C) :
    gagliardoEnergyC α f =
      ∫⁻ ξ, ENNReal.ofReal (|2 * π * ξ| ^ α) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) := by
  unfold gagliardoEnergyC
  rw [lintegral_gagliardo_energy_fourier]
  exact lintegral_congr fun ξ => by rw [gagliardoSymbol_exact hα]

end

end FracLap
