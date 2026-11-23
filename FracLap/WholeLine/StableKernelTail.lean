/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.StableKernel
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# FracLap.WholeLine.StableKernelTail

Half-period shift estimates for oscillatory integrals on `(0, ∞)`, used to bound the tail of the
stable kernel. If `x δ = π` then `sin (x (ν - δ)) = - sin (x ν)`, so translating the integration
variable by `δ` flips the sign of the sine transform:
- `integrableOn_Ioi_shift` and `integral_Ioi_shift`: translation of a half-line integral.
- `integral_sin_shift`: `∫_{ν > 0} f ν sin (x ν) = - ∫_{ν > δ} f (ν - δ) sin (x ν)`.
- `abs_integral_sin_le_of_antitone`: for nonnegative antitone integrable `f`,
  `|∫_{ν > 0} f ν sin (x ν)| ≤ ∫_{0 < ν ≤ δ} f ν`.
-/

namespace FracLap

open MeasureTheory Real Set Filter Topology

@[expose] public section

/-- A half-line integrable function stays integrable after translating the variable. -/
theorem integrableOn_Ioi_shift {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) (δ : ℝ) :
    IntegrableOn (fun ν : ℝ => f (ν - δ)) (Ioi δ) := by
  have h1 : Integrable ((Ioi (0 : ℝ)).indicator f) :=
    (integrable_indicator_iff measurableSet_Ioi).2 hf
  have h2 := h1.comp_sub_right δ
  have h3 : (fun ν : ℝ => (Ioi (0 : ℝ)).indicator f (ν - δ)) =
      (Ioi δ).indicator (fun ν : ℝ => f (ν - δ)) := by
    ext ν
    simp only [indicator, mem_Ioi, sub_pos]
  rw [h3] at h2
  exact (integrable_indicator_iff measurableSet_Ioi).1 h2

/-- Translating the variable of a half-line integral. -/
theorem integral_Ioi_shift (f : ℝ → ℝ) (δ : ℝ) :
    ∫ ν in Ioi δ, f (ν - δ) = ∫ ν in Ioi (0 : ℝ), f ν := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_sub_right_eq_self ((Ioi (0 : ℝ)).indicator f) δ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ν => ?_)
  simp only [indicator, mem_Ioi, sub_pos]

/-- **Half-period shift**: if `x δ = π`, translating by `δ` flips the sign of the sine transform
on `(0, ∞)`. -/
theorem integral_sin_shift (f : ℝ → ℝ) {x δ : ℝ} (hxδ : x * δ = π) :
    ∫ ν in Ioi (0 : ℝ), f ν * sin (x * ν) = -∫ ν in Ioi δ, f (ν - δ) * sin (x * ν) := by
  rw [← integral_indicator measurableSet_Ioi,
    ← integral_sub_right_eq_self ((Ioi (0 : ℝ)).indicator fun ν => f ν * sin (x * ν)) δ,
    ← integral_neg, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ν => ?_)
  by_cases hν : δ < ν
  · have h0 : (0 : ℝ) < ν - δ := sub_pos.mpr hν
    have hsin : sin (x * (ν - δ)) = -sin (x * ν) := by
      rw [mul_sub, hxδ, sin_sub_pi]
    simp only [indicator, mem_Ioi, h0, hν, ite_true, hsin]
    ring
  · have h0 : ¬ (0 : ℝ) < ν - δ := fun h => hν (sub_pos.mp h)
    simp [indicator, mem_Ioi, h0, hν]

/-- A bounded-sine multiple of a half-line integrable function is integrable. -/
theorem integrableOn_mul_sin {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) (x : ℝ) :
    IntegrableOn (fun ν : ℝ => f ν * sin (x * ν)) (Ioi 0) := by
  refine hf.norm.mono' (hf.aestronglyMeasurable.mul
    (by fun_prop : Continuous fun ν : ℝ => sin (x * ν)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ν => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (by simpa using abs_sin_le_one (x * ν))

/-- **Sine transform of a monotone function**: for a nonnegative antitone integrable `f` on
`(0, ∞)` and `x δ = π`, `|∫_{ν > 0} f ν sin (x ν)| ≤ ∫_{0 < ν ≤ δ} f ν`. -/
theorem abs_integral_sin_le_of_antitone {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    (hnn : ∀ ν ∈ Ioi (0 : ℝ), 0 ≤ f ν) (hanti : AntitoneOn f (Ioi 0)) {x δ : ℝ} (hδ : 0 < δ)
    (hxδ : x * δ = π) :
    |∫ ν in Ioi (0 : ℝ), f ν * sin (x * ν)| ≤ ∫ ν in Ioc (0 : ℝ) δ, f ν := by
  set I := ∫ ν in Ioi (0 : ℝ), f ν * sin (x * ν) with hI
  have hsub : Ioc (0 : ℝ) δ ⊆ Ioi 0 := fun ν hν => hν.1
  have hsubδ : Ioi δ ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hδ.le
  have hsin := integrableOn_mul_sin hf x
  have hsplit : ∀ g : ℝ → ℝ, IntegrableOn g (Ioi 0) →
      ∫ ν in Ioi (0 : ℝ), g ν = (∫ ν in Ioc (0 : ℝ) δ, g ν) + ∫ ν in Ioi δ, g ν := by
    intro g hg
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (hg.mono_set hsub)
      (hg.mono_set hsubδ), Ioc_union_Ioi_eq_Ioi hδ.le]
  have hshift := integral_sin_shift f hxδ
  have hfshift := integrableOn_Ioi_shift hf δ
  have hJ : IntegrableOn (fun ν : ℝ => f (ν - δ) * sin (x * ν)) (Ioi δ) := by
    refine hfshift.norm.mono' (hfshift.aestronglyMeasurable.mul
      (by fun_prop : Continuous fun ν : ℝ => sin (x * ν)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ν => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (by simpa using abs_sin_le_one (x * ν))
  have hB := hsin.mono_set hsubδ
  have hdiff : (∫ ν in Ioi δ, f ν * sin (x * ν)) - ∫ ν in Ioi δ, f (ν - δ) * sin (x * ν) =
      ∫ ν in Ioi δ, (f ν - f (ν - δ)) * sin (x * ν) := by
    rw [← integral_sub hB hJ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ν => by simp only [sub_mul])
  have hA : |∫ ν in Ioc (0 : ℝ) δ, f ν * sin (x * ν)| ≤ ∫ ν in Ioc (0 : ℝ) δ, f ν := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hf.mono_set hsub) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with ν hν
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hnn ν (hsub hν))]
    exact mul_le_of_le_one_right (hnn ν (hsub hν)) (abs_sin_le_one _)
  have hmass : (∫ ν in Ioi δ, (f (ν - δ) - f ν)) = ∫ ν in Ioc (0 : ℝ) δ, f ν := by
    rw [integral_sub hfshift (hf.mono_set hsubδ), integral_Ioi_shift f δ,
      hsplit f hf]
    ring
  have hD : |∫ ν in Ioi δ, (f ν - f (ν - δ)) * sin (x * ν)| ≤ ∫ ν in Ioc (0 : ℝ) δ, f ν := by
    rw [← hmass, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hfshift.sub (hf.mono_set hsubδ)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ν hν
    have hν0 : (0 : ℝ) < ν - δ := sub_pos.mpr hν
    have hle : f ν ≤ f (ν - δ) :=
      hanti (show ν - δ ∈ Ioi (0 : ℝ) from hν0) (show ν ∈ Ioi (0 : ℝ) from hsubδ hν)
        (by linarith)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonpos (by linarith : f ν - f (ν - δ) ≤ 0)]
    have h0 : 0 ≤ -(f ν - f (ν - δ)) := by linarith
    have := mul_le_of_le_one_right h0 (abs_sin_le_one (x * ν))
    linarith
  have h2 : 2 * I = (∫ ν in Ioc (0 : ℝ) δ, f ν * sin (x * ν)) +
      ∫ ν in Ioi δ, (f ν - f (ν - δ)) * sin (x * ν) := by
    rw [← hdiff]
    have h1 := hsplit _ hsin
    linarith [hshift]
  have : 2 * |I| ≤ 2 * ∫ ν in Ioc (0 : ℝ) δ, f ν := by
    have : |2 * I| ≤ _ := h2 ▸ abs_add_le _ _
    rw [abs_mul, abs_two] at this
    linarith
  linarith

/-! ### Integration by parts: cosine transform to sine transform -/

/-- The density `k ω = α ω^(α-1) exp (-ω^α)`, minus the derivative of `exp (-ω^α)`. -/
noncomputable def stableDensity (α ω : ℝ) : ℝ := α * ω ^ (α - 1) * exp (-ω ^ α)

/-- `ω ↦ α ω^(α-1) exp (-ω^α)` is integrable on `(0, ∞)` for `α > 0`. -/
theorem integrableOn_stableDensity {α : ℝ} (hα : 0 < α) :
    IntegrableOn (stableDensity α) (Ioi 0) := by
  have h : IntegrableOn (fun ω : ℝ => α * (ω ^ (α - 1) * exp (-1 * ω ^ α))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := α - 1) (p := α) (b := 1)
      (by linarith) hα one_pos).const_mul α
  refine h.congr_fun (fun ω _ => ?_) measurableSet_Ioi
  simp only [stableDensity, neg_mul, one_mul]
  ring

/-- Derivative of `ω ↦ exp (-ω^α)` on `(0, ∞)`. -/
theorem hasDerivAt_exp_neg_rpow {α ω : ℝ} (hω : 0 < ω) :
    HasDerivAt (fun ω : ℝ => exp (-ω ^ α)) (-stableDensity α ω) ω := by
  have h1 : HasDerivAt (fun ω : ℝ => ω ^ α) (α * ω ^ (α - 1)) ω :=
    hasDerivAt_rpow_const (Or.inl hω.ne')
  have h2 : HasDerivAt (fun ω : ℝ => exp (-ω ^ α)) (exp (-ω ^ α) * -(α * ω ^ (α - 1))) ω :=
    h1.neg.exp
  convert h2 using 1
  simp only [stableDensity]
  ring

/-- **Cosine transform as a sine transform**: for `α, x > 0`,
`∫_{ω > 0} exp (-ω^α) cos (x ω) dω = x⁻¹ ∫_{ω > 0} k(ω) sin (x ω) dω` with `k = stableDensity α`. -/
theorem integral_exp_neg_rpow_mul_cos {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    ∫ ω in Ioi (0 : ℝ), exp (-ω ^ α) * cos (x * ω) =
      x⁻¹ * ∫ ω in Ioi (0 : ℝ), stableDensity α ω * sin (x * ω) := by
  have hv : ∀ ω ∈ Ioi (0 : ℝ), HasDerivAt (fun ω : ℝ => sin (x * ω) / x) (cos (x * ω)) ω := by
    intro ω _
    have h := (((hasDerivAt_id ω).const_mul x).sin).div_const x
    simp only [id] at h
    convert h using 1
    field_simp
  have hu : ∀ ω ∈ Ioi (0 : ℝ), HasDerivAt (fun ω : ℝ => exp (-ω ^ α)) (-stableDensity α ω) ω :=
    fun ω hω => hasDerivAt_exp_neg_rpow hω
  have hsym : IntegrableOn (fun ω : ℝ => exp (-ω ^ α)) (Ioi 0) := by
    simpa only [neg_mul, one_mul] using integrableOn_stableSymbol hα one_pos
  have hcos : IntegrableOn (fun ω : ℝ => exp (-ω ^ α) * cos (x * ω)) (Ioi 0) := by
    refine hsym.mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact (by fun_prop : Continuous fun ω : ℝ => exp (-ω ^ α) * cos (x * ω)).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact mul_le_of_le_one_right (exp_pos _).le (abs_cos_le_one _)
  have hk : IntegrableOn (fun ω : ℝ => -stableDensity α ω * (sin (x * ω) / x)) (Ioi 0) := by
    have h : IntegrableOn (fun ω : ℝ => -x⁻¹ * (stableDensity α ω * sin (x * ω))) (Ioi 0) :=
      (integrableOn_mul_sin (integrableOn_stableDensity hα) x).const_mul (-x⁻¹)
    refine h.congr_fun (fun ω _ => ?_) measurableSet_Ioi
    simp only
    field_simp
  have h0 : Tendsto (fun ω : ℝ => exp (-ω ^ α) * (sin (x * ω) / x)) (nhdsWithin 0 (Ioi 0))
      (nhds 0) := by
    have hc : Continuous fun ω : ℝ => exp (-ω ^ α) * (sin (x * ω) / x) := by
      have := Real.continuous_rpow_const hα.le
      fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [zero_rpow hα.ne'] using this
  have hinf : Tendsto (fun ω : ℝ => exp (-ω ^ α) * (sin (x * ω) / x)) atTop (nhds 0) := by
    have hlim : Tendsto (fun ω : ℝ => exp (-ω ^ α) / x) atTop (nhds 0) := by
      have := (tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_rpow_atTop hα)).div_const x
      simpa using this
    refine squeeze_zero_norm (fun ω => ?_) hlim
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _), abs_div,
      abs_of_pos hx, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (exp_pos _).le (abs_sin_le_one _))
      hx.le
  have key := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) hu hv hcos hk (by exact h0)
    (by exact hinf)
  have key' : ∫ ω in Ioi (0 : ℝ), exp (-ω ^ α) * cos (x * ω) =
      0 - 0 - ∫ ω in Ioi (0 : ℝ), -stableDensity α ω * (sin (x * ω) / x) := key
  rw [key', sub_zero, zero_sub, ← integral_neg, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  field_simp

/-- The density `stableDensity α` is nonnegative on `(0, ∞)`. -/
theorem stableDensity_nonneg {α : ℝ} (hα : 0 < α) {ω : ℝ} (hω : 0 < ω) :
    0 ≤ stableDensity α ω := by
  unfold stableDensity
  have := rpow_pos_of_pos hω (α - 1)
  positivity

/-- For `0 < α ≤ 1` the density `stableDensity α` is antitone on `(0, ∞)`. -/
theorem stableDensity_antitoneOn {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    AntitoneOn (stableDensity α) (Ioi 0) := by
  intro a ha b hb hab
  have ha0 : (0 : ℝ) < a := ha
  have h1 : b ^ (α - 1) ≤ a ^ (α - 1) :=
    Real.rpow_le_rpow_of_nonpos ha0 hab (by linarith)
  have h2 : exp (-b ^ α) ≤ exp (-a ^ α) :=
    exp_le_exp.mpr (neg_le_neg (Real.rpow_le_rpow ha0.le hab hα.le))
  unfold stableDensity
  have hb0 : (0 : ℝ) < b := hb
  have := rpow_pos_of_pos hb0 (α - 1)
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hα.le) h2 (exp_pos _).le
    (mul_nonneg hα.le (rpow_pos_of_pos ha0 _).le)

/-- Mass of the density near the origin: `∫_{0 < ν ≤ δ} k = 1 - exp (-δ^α)`. -/
theorem integral_stableDensity_Ioc {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) :
    ∫ ν in Ioc (0 : ℝ) δ, stableDensity α ν = 1 - exp (-δ ^ α) := by
  have hcont : Continuous fun ω : ℝ => -exp (-ω ^ α) := by
    have := Real.continuous_rpow_const hα.le
    fun_prop
  have hint : IntervalIntegrable (stableDensity α) volume 0 δ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le).mpr
      ((integrableOn_stableDensity hα).mono_set Ioc_subset_Ioi_self)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hδ.le
    (f := fun ω : ℝ => -exp (-ω ^ α)) (f' := stableDensity α) hcont.continuousOn
    (fun ω hω => by
      have h := (hasDerivAt_exp_neg_rpow (α := α) hω.1).neg
      rw [neg_neg] at h
      exact h) hint
  rw [← intervalIntegral.integral_of_le hδ.le, hftc]
  simp [zero_rpow hα.ne']
  ring

/-- **Tail bound for `0 < α ≤ 1`**: for `x > 0`,
`|P_α(x, 1)| ≤ π⁻¹ x⁻¹ (π / x)^α`, i.e. `|P_α(x, 1)| ≤ π^(α-1) x^(-1-α)`. -/
theorem abs_stableKernel_le_of_le_one {α x : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hx : 0 < x) :
    |stableKernel α x 1| ≤ π⁻¹ * (x⁻¹ * (π / x) ^ α) := by
  have hδ : 0 < π / x := div_pos pi_pos hx
  have hxδ : x * (π / x) = π := by field_simp
  have hsin := abs_integral_sin_le_of_antitone (integrableOn_stableDensity hα)
    (fun ν hν => stableDensity_nonneg hα hν) (stableDensity_antitoneOn hα hα1) hδ hxδ
  rw [integral_stableDensity_Ioc hα hδ] at hsin
  have hle : 1 - exp (-(π / x) ^ α) ≤ (π / x) ^ α := by
    linarith [add_one_le_exp (-(π / x) ^ α)]
  unfold stableKernel
  simp only [neg_mul, one_mul]
  rw [integral_exp_neg_rpow_mul_cos hα hx, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr pi_pos),
    abs_of_pos (inv_pos.mpr hx)]
  gcongr
  exact hsin.trans hle

end

end FracLap
