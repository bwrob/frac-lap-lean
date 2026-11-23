/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.StableSubordination
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Gamma

/-!
# FracLap.WholeLine.StableLevy

The Lévy-Khintchine representation of the one-sided stable Bernstein function `λ ↦ λ^β` for
`0 < β < 1`:
`λ^β = (β / Γ(1 - β)) ∫_{s > 0} (1 - exp (-λ s)) s^(-1-β) ds`.

- `integrableOn_one_sub_exp_mul_rpow`: integrability of `(1 - exp (-u)) u^(-1-β)` on `(0, ∞)`.
- `integral_one_sub_exp_mul_rpow`: `∫_{u > 0} (1 - exp (-u)) u^(-1-β) du = Γ(1 - β) / β`.
- `integral_one_sub_exp_scaled`: the scaled version `∫ (1 - exp (-λ s)) s^(-1-β) ds = λ^β Γ(1-β)/β`.
-/

namespace FracLap

open MeasureTheory Set Filter Topology
open scoped NNReal

@[expose] public section

/-- `(1 - exp (-u)) u^(-1-β)` is integrable on `(0, ∞)` for `0 < β < 1`. -/
theorem integrableOn_one_sub_exp_mul_rpow {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IntegrableOn (fun u : ℝ => (1 - Real.exp (-u)) * u ^ (-1 - β)) (Ioi 0) := by
  have hmeas : Measurable fun u : ℝ => (1 - Real.exp (-u)) * u ^ (-1 - β) :=
    (measurable_const.sub measurable_neg.exp).mul (measurable_id.pow_const _)
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · have h1 : IntegrableOn (fun u : ℝ => u ^ (-β)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    refine h1.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : 0 < u := hu.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by
      linarith [Real.exp_le_one_iff.mpr (by linarith : -u ≤ 0)]) (Real.rpow_nonneg hu0.le _))]
    have h2 : 1 - Real.exp (-u) ≤ u := by linarith [Real.add_one_le_exp (-u)]
    calc (1 - Real.exp (-u)) * u ^ (-1 - β) ≤ u * u ^ (-1 - β) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hu0.le _)
      _ = u ^ (-β) := by
          rw [← Real.rpow_one_add' hu0.le (by linarith)]
          ring_nf
  · have h1 : IntegrableOn (fun u : ℝ => u ^ (-1 - β)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine h1.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans one_pos hu
    have hexp : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [mem_Ioi.mp hu])
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [Real.exp_pos (-u)])
      (Real.rpow_nonneg hu0.le _))]
    calc (1 - Real.exp (-u)) * u ^ (-1 - β) ≤ 1 * u ^ (-1 - β) :=
          mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos (-u)]) (Real.rpow_nonneg hu0.le _)
      _ = u ^ (-1 - β) := one_mul _

/-- **The basic Lévy integral**: `∫_{u > 0} (1 - exp (-u)) u^(-1-β) du = Γ(1 - β) / β` for
`0 < β < 1`, by integration by parts. -/
theorem integral_one_sub_exp_mul_rpow {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∫ u in Ioi (0 : ℝ), (1 - Real.exp (-u)) * u ^ (-1 - β) = Real.Gamma (1 - β) / β := by
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) (Real.exp (-x)) x := by
    intro x _
    have h := (hasDerivAt_neg x).exp.const_sub 1
    convert h using 1
    ring
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => -(x ^ (-β) / β)) (x ^ (-1 - β)) x := by
    intro x hx
    have hx0 : 0 < x := hx
    have h := ((Real.hasDerivAt_rpow_const (p := -β) (Or.inl hx0.ne')).div_const β).neg
    convert h using 1
    field_simp
    ring_nf
  have hΓ : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((1 - β) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by linarith)
  have hk : IntegrableOn (fun x : ℝ => Real.exp (-x) * -(x ^ (-β) / β)) (Ioi 0) := by
    have h : IntegrableOn (fun x : ℝ => -β⁻¹ * (Real.exp (-x) * x ^ ((1 - β) - 1))) (Ioi 0) :=
      hΓ.const_mul (-β⁻¹)
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [sub_sub_cancel_left]
    field_simp
  have h0 : Tendsto (fun x : ℝ => (1 - Real.exp (-x)) * -(x ^ (-β) / β)) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => x ^ (1 - β) / β) (𝓝[>] 0) (𝓝 0) := by
      have hc := (Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 - β)).tendsto 0
      rw [Real.zero_rpow (by linarith)] at hc
      simpa using (hc.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).div_const β
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : 0 < x := hx
    have h1 : 0 ≤ 1 - Real.exp (-x) := by
      linarith [Real.exp_le_one_iff.mpr (by linarith : -x ≤ 0)]
    have h2 : 1 - Real.exp (-x) ≤ x := by linarith [Real.add_one_le_exp (-x)]
    rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1,
      abs_of_nonneg (by positivity)]
    calc (1 - Real.exp (-x)) * (x ^ (-β) / β) ≤ x * (x ^ (-β) / β) := by gcongr
      _ = x ^ (1 - β) / β := by
          rw [Real.rpow_sub hx0, Real.rpow_neg hx0.le, Real.rpow_one]
          field_simp
  have hinf : Tendsto (fun x : ℝ => (1 - Real.exp (-x)) * -(x ^ (-β) / β)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => x ^ (-β) / β) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop hβ0).div_const β
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with x hx0
    have h1 : 0 ≤ 1 - Real.exp (-x) := by
      linarith [Real.exp_le_one_iff.mpr (by linarith : -x ≤ 0)]
    have h3 : 1 - Real.exp (-x) ≤ 1 := by linarith [Real.exp_pos (-x)]
    rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1,
      abs_of_nonneg (by positivity)]
    calc (1 - Real.exp (-x)) * (x ^ (-β) / β) ≤ 1 * (x ^ (-β) / β) := by gcongr
      _ = x ^ (-β) / β := one_mul _
  have key := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) hu hv
    (integrableOn_one_sub_exp_mul_rpow hβ0 hβ1) hk (by exact h0) (by exact hinf)
  have key' : ∫ u in Ioi (0 : ℝ), (1 - Real.exp (-u)) * u ^ (-1 - β) =
      0 - 0 - ∫ x in Ioi (0 : ℝ), Real.exp (-x) * -(x ^ (-β) / β) := key
  rw [key', sub_zero, zero_sub, ← integral_neg]
  have hG := Real.Gamma_eq_integral (s := 1 - β) (by linarith)
  rw [hG, ← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [sub_sub_cancel_left]
  ring

/-- Scaled integrability: `(1 - exp (-λ s)) s^(-1-β)` is integrable on `(0, ∞)` for `λ > 0`. -/
theorem integrableOn_one_sub_exp_scaled {β lam : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam) :
    IntegrableOn (fun s : ℝ => (1 - Real.exp (-(lam * s))) * s ^ (-1 - β)) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun u : ℝ => (1 - Real.exp (-u)) * u ^ (-1 - β)) 0 hlam).2
    (by simpa using integrableOn_one_sub_exp_mul_rpow hβ0 hβ1)
  have h2 : IntegrableOn (fun s : ℝ => lam ^ (1 + β) *
      ((1 - Real.exp (-(lam * s))) * (lam * s) ^ (-1 - β))) (Ioi 0) := h.const_mul (lam ^ (1 + β))
  refine h2.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hs0 : 0 < s := hs
  beta_reduce
  rw [Real.mul_rpow hlam.le hs0.le]
  have : lam ^ (1 + β) * lam ^ (-1 - β) = 1 := by
    rw [← Real.rpow_add hlam]
    simp
  calc lam ^ (1 + β) * ((1 - Real.exp (-(lam * s))) * (lam ^ (-1 - β) * s ^ (-1 - β)))
      = (lam ^ (1 + β) * lam ^ (-1 - β)) * ((1 - Real.exp (-(lam * s))) * s ^ (-1 - β)) := by ring
    _ = (1 - Real.exp (-(lam * s))) * s ^ (-1 - β) := by rw [this, one_mul]

/-- **Scaled Lévy integral**: `∫_{s > 0} (1 - exp (-λ s)) s^(-1-β) ds = λ^β Γ(1 - β) / β`. -/
theorem integral_one_sub_exp_scaled {β lam : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam) :
    ∫ s in Ioi (0 : ℝ), (1 - Real.exp (-(lam * s))) * s ^ (-1 - β) =
      lam ^ β * (Real.Gamma (1 - β) / β) := by
  have h := integral_comp_mul_left_Ioi (fun u : ℝ => (1 - Real.exp (-u)) * u ^ (-1 - β)) 0 hlam
  rw [mul_zero, smul_eq_mul, integral_one_sub_exp_mul_rpow hβ0 hβ1] at h
  have hconv : ∫ s in Ioi (0 : ℝ), (1 - Real.exp (-(lam * s))) * s ^ (-1 - β) =
      lam ^ (1 + β) * ∫ s in Ioi (0 : ℝ), (1 - Real.exp (-(lam * s))) * (lam * s) ^ (-1 - β) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : 0 < s := hs
    rw [Real.mul_rpow hlam.le hs0.le]
    have : lam ^ (1 + β) * lam ^ (-1 - β) = 1 := by
      rw [← Real.rpow_add hlam]
      simp
    calc (1 - Real.exp (-(lam * s))) * s ^ (-1 - β)
        = (lam ^ (1 + β) * lam ^ (-1 - β)) * ((1 - Real.exp (-(lam * s))) * s ^ (-1 - β)) := by
          rw [this, one_mul]
      _ = _ := by ring
  rw [hconv, h]
  have : lam ^ (1 + β) * lam⁻¹ = lam ^ β := by
    rw [Real.rpow_add hlam, Real.rpow_one]
    field_simp
  calc lam ^ (1 + β) * (lam⁻¹ * (Real.Gamma (1 - β) / β))
      = (lam ^ (1 + β) * lam⁻¹) * (Real.Gamma (1 - β) / β) := by ring
    _ = _ := by rw [this]

/-! ### The truncated Lévy measure -/

/-- The normalizing constant `β / Γ(1 - β)` of the Lévy density of the `β`-stable subordinator. -/
noncomputable def levyConst (β : ℝ) : ℝ := β / Real.Gamma (1 - β)

/-- The Lévy measure `levyConst β · s^(-1-β) ds` of the `β`-stable subordinator, truncated to
`s > ε` and viewed as a measure on `[0, ∞)`. -/
noncomputable def levyMeasure (β ε : ℝ) : Measure ℝ≥0 :=
  ((volume.restrict (Ioi ε)).withDensity
    fun s => ENNReal.ofReal (levyConst β * s ^ (-1 - β))).map Real.toNNReal

/-- The truncated Lévy density is integrable on `(ε, ∞)`. -/
theorem integrableOn_levyDensity {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε) :
    IntegrableOn (fun s : ℝ => levyConst β * s ^ (-1 - β)) (Ioi ε) :=
  (integrableOn_Ioi_rpow_of_lt (by linarith) hε).const_mul (levyConst β)

/-- The truncated Lévy measure is finite. -/
theorem levyMeasure_isFiniteMeasure {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε) :
    IsFiniteMeasure (levyMeasure β ε) := by
  have : IsFiniteMeasure ((volume.restrict (Ioi ε)).withDensity
      fun s => ENNReal.ofReal (levyConst β * s ^ (-1 - β))) :=
    isFiniteMeasure_withDensity_ofReal (integrableOn_levyDensity hβ hε).2
  unfold levyMeasure
  infer_instance

/-- The Lévy constant is positive for `0 < β < 1`. -/
theorem levyConst_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 < levyConst β :=
  div_pos hβ0 (Real.Gamma_pos_of_pos (by linarith))

/-- The mixture of the truncated Lévy measure is the Laplace integral of the Lévy density. -/
theorem gaussMixture_levyMeasure {β ε : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hε : 0 < ε) (ξ : ℝ) :
    gaussMixture (levyMeasure β ε) ξ =
      ∫ s in Ioi ε, levyConst β * s ^ (-1 - β) * Real.exp (-(ξ ^ 2) * s) := by
  have hmeas : Measurable fun s : ℝ => ENNReal.ofReal (levyConst β * s ^ (-1 - β)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const _))
  unfold gaussMixture levyMeasure
  rw [integral_map measurable_real_toNNReal.aemeasurable
    (by fun_prop : Continuous fun s : ℝ≥0 => Real.exp (-(ξ ^ 2) * (s : ℝ))).aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := lt_trans hε hs
  have hnn : 0 ≤ levyConst β * s ^ (-1 - β) :=
    mul_nonneg (levyConst_pos hβ0 hβ1).le (Real.rpow_nonneg hs0.le _)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal hnn, Real.coe_toNNReal _ hs0.le]

/-- The truncated Lévy density times `exp (-ξ² s)` is integrable on `(ε, ∞)`. -/
theorem integrableOn_levyDensity_mul_exp {β ε : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hε : 0 < ε)
    (ξ : ℝ) :
    IntegrableOn (fun s : ℝ => levyConst β * s ^ (-1 - β) * Real.exp (-(ξ ^ 2) * s))
      (Ioi ε) := by
  refine (integrableOn_levyDensity hβ hε).mono' ?_ ?_
  · exact ((measurable_const.mul (measurable_id.pow_const _)).mul
      (measurable_const.mul measurable_id).exp).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans hε hs
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-(ξ ^ 2) * s) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg ξ]
    calc |levyConst β * s ^ (-1 - β)| * Real.exp (-(ξ ^ 2) * s)
        ≤ |levyConst β * s ^ (-1 - β)| * 1 := by gcongr
      _ = |levyConst β * s ^ (-1 - β)| := mul_one _
      _ = levyConst β * s ^ (-1 - β) := by
          exact abs_of_nonneg (mul_nonneg (levyConst_pos hβ hβ1).le (Real.rpow_nonneg hs0.le _))

/-- **Truncated Bernstein function**: `H(0) - H(ξ)` for the mixture `H` of the truncated Lévy
measure is `levyConst β ∫_{s > ε} (1 - exp (-ξ² s)) s^(-1-β) ds`. -/
theorem gaussMixture_levy_sub {β ε : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hε : 0 < ε) (ξ : ℝ) :
    gaussMixture (levyMeasure β ε) 0 - gaussMixture (levyMeasure β ε) ξ =
      levyConst β * ∫ s in Ioi ε, (1 - Real.exp (-(ξ ^ 2) * s)) * s ^ (-1 - β) := by
  rw [gaussMixture_levyMeasure hβ0 hβ1 hε, gaussMixture_levyMeasure hβ0 hβ1 hε,
    ← integral_sub (integrableOn_levyDensity_mul_exp hβ0 hβ1 hε 0)
      (integrableOn_levyDensity_mul_exp hβ0 hβ1 hε ξ), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_mul,
    Real.exp_zero]
  ring

/-- **Convergence to the stable Bernstein function**: along `ε = 1 / (n + 1)`,
`H_ε(0) - H_ε(ξ) → (ξ²)^β`. -/
theorem tendsto_levy_sub {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ξ : ℝ) :
    Tendsto (fun n : ℕ => gaussMixture (levyMeasure β (1 / ((n : ℝ) + 1))) 0 -
      gaussMixture (levyMeasure β (1 / ((n : ℝ) + 1))) ξ) atTop (𝓝 ((ξ ^ 2) ^ β)) := by
  have hε : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  simp_rw [gaussMixture_levy_sub hβ0 hβ1 (hε _)]
  by_cases hξ : ξ = 0
  · subst hξ
    simp [Real.zero_rpow hβ0.ne']
  · have hlam : 0 < ξ ^ 2 := by positivity
    have hint : IntegrableOn (fun s : ℝ => (1 - Real.exp (-(ξ ^ 2) * s)) * s ^ (-1 - β))
        (Ioi 0) := by
      simpa only [neg_mul] using integrableOn_one_sub_exp_scaled hβ0 hβ1 hlam
    have hset : (⋃ n : ℕ, Ioi (1 / ((n : ℝ) + 1))) = Ioi (0 : ℝ) := by
      ext x
      simp only [mem_iUnion, mem_Ioi]
      refine ⟨fun ⟨n, hn⟩ => lt_trans (by positivity) hn, fun hx => ?_⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
      exact ⟨n, hn⟩
    have hmono : Monotone fun n : ℕ => Ioi (1 / ((n : ℝ) + 1)) := by
      intro n m hnm
      refine Ioi_subset_Ioi ?_
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hnm)
    have hlim := tendsto_setIntegral_of_monotone (μ := volume)
      (f := fun s : ℝ => (1 - Real.exp (-(ξ ^ 2) * s)) * s ^ (-1 - β))
      (fun n => measurableSet_Ioi) hmono (by rw [hset]; exact hint)
    rw [hset] at hlim
    have hval : ∫ s in Ioi (0 : ℝ), (1 - Real.exp (-(ξ ^ 2) * s)) * s ^ (-1 - β) =
        (ξ ^ 2) ^ β * (Real.Gamma (1 - β) / β) := by
      simpa only [neg_mul] using integral_one_sub_exp_scaled hβ0 hβ1 hlam
    rw [hval] at hlim
    have hc : levyConst β * ((ξ ^ 2) ^ β * (Real.Gamma (1 - β) / β)) = (ξ ^ 2) ^ β := by
      have hΓ : Real.Gamma (1 - β) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
      unfold levyConst
      field_simp
    rw [← hc]
    exact hlim.const_mul _

/-- `(ξ²)^(α/2) = |ξ|^α`. -/
theorem sq_rpow_half (α ξ : ℝ) : (ξ ^ 2) ^ (α / 2) = |ξ| ^ α := by
  rw [← sq_abs ξ, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg ξ)]
  congr 1
  push_cast
  ring

/-- **The stable symbol is Gaussian monotone.** For `0 < α < 2` and `t > 0`, the function
`ξ ↦ exp (-t |ξ|^α)` is the bounded pointwise limit of the compound-Poisson exponentials built
from the truncated Lévy measures of the `α/2`-stable subordinator. -/
theorem isGaussMonotone_stableSymbol {α t : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (ht : 0 < t) :
    IsGaussMonotone fun ξ : ℝ => Real.exp (-t * |ξ| ^ α) := by
  have hβ0 : 0 < α / 2 := by linarith
  have hβ1 : α / 2 < 1 := by linarith
  set mn : ℕ → Measure ℝ≥0 := fun n => levyMeasure (α / 2) (1 / ((n : ℝ) + 1)) with hmn
  have hfin : ∀ n, IsFiniteMeasure (mn n) := fun n =>
    levyMeasure_isFiniteMeasure hβ0 (by positivity)
  refine IsGaussMonotone.of_tendsto (C := 1) (Fn := fun n ξ =>
    Real.exp (-t * (gaussMixture (mn n) 0 - gaussMixture (mn n) ξ))) (fun n => ?_) (fun n ξ => ?_)
    (fun ξ => ?_) (fun n => ?_)
  · have := hfin n
    exact (Real.continuous_exp.comp (continuous_const.mul
      (continuous_const.sub (continuous_gaussMixture (mn n))))).measurable
  · have := hfin n
    have hle := gaussMixture_le_zero (mn n) ξ
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    nlinarith
  · have h := tendsto_levy_sub hβ0 hβ1 ξ
    have h2 := (Real.continuous_exp.tendsto _).comp (h.const_mul (-t))
    rw [sq_rpow_half] at h2
    exact h2
  · have := hfin n
    exact isGaussMonotone_exp_sub (mn n) ht.le

end

end FracLap
