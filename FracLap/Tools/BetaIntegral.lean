/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# FracLap.Tools.BetaIntegral

The real Beta integral and its subtracted form.

- `beta_integral_real`: for `a, b > 0`,
  `∫₀¹ x^(a-1) (1-x)^(b-1) dx = Γ(a) Γ(b) / Γ(a+b)`.
- `beta_integral_subtracted`: `∫₀¹ x^(a-1) ((1-x)^(b-1) - 1) dx = Γ(a) Γ(b) / Γ(a+b) - 1/a`
  (Jakubowski--Kwaśnicki), the regularized form used for the half-line ground-state computation.
- `beta_integral_subtracted_neg`: the same identity for `-1 < a < 0`, `b > 0` (the first
  parameter continued past `0`), proved by a first-order recurrence in `a` and the fundamental
  theorem of calculus, with no analytic continuation.
-/

namespace FracLap

open MeasureTheory Set Real

@[expose] public section

/-- The real Beta integrand is interval integrable on `[0, 1]` for `a, b > 0`. -/
theorem intervalIntegrable_beta_real {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1)) volume 0 1 := by
  have hc := Complex.betaIntegral_convergent (u := (a : ℂ)) (v := (b : ℂ)) (by simpa using ha)
    (by simpa using hb)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hc ⊢
  have hre := Complex.reCLM.integrable_comp hc
  refine hre.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx => ?_)
  have h1 : (((x : ℝ) : ℂ)) ^ ((a : ℂ) - 1) = (((x ^ (a - 1) : ℝ)) : ℂ) := by
    rw [Complex.ofReal_cpow hx.1.le]; push_cast; rfl
  have h2 : (1 - ((x : ℝ) : ℂ)) ^ ((b : ℂ) - 1) = (((1 - x) ^ (b - 1) : ℝ) : ℂ) := by
    have : (1 - ((x : ℝ) : ℂ)) = (((1 - x : ℝ)) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_cpow (by linarith [hx.2])]; push_cast; rfl
  simp only [Complex.reCLM_apply]
  rw [h1, h2, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Real Beta integral**: `∫₀¹ x^(a-1) (1-x)^(b-1) dx = Γ(a) Γ(b) / Γ(a+b)` for `a, b > 0`. -/
theorem beta_integral_real {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) = Gamma a * Gamma b / Gamma (a + b) := by
  have hgam := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := (b : ℂ))
    (by simpa using ha) (by simpa using hb)
  have hβ : Complex.betaIntegral (a : ℂ) (b : ℂ) =
      ((∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ) := by
    unfold Complex.betaIntegral
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    have h1 : (((x : ℝ) : ℂ)) ^ ((a : ℂ) - 1) = (((x ^ (a - 1) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_cpow hx.1]; push_cast; rfl
    have h2 : (1 - ((x : ℝ) : ℂ)) ^ ((b : ℂ) - 1) = (((1 - x) ^ (b - 1) : ℝ) : ℂ) := by
      have : (1 - ((x : ℝ) : ℂ)) = (((1 - x : ℝ)) : ℂ) := by push_cast; rfl
      rw [this, Complex.ofReal_cpow (by linarith [hx.2])]; push_cast; rfl
    simp only [h1, h2]
    push_cast; rfl
  rw [hβ, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul] at hgam
  have hpos : 0 < Gamma (a + b) := Gamma_pos_of_pos (by linarith)
  have hg := Complex.ofReal_injective hgam
  field_simp
  linarith

/-- **Subtracted Beta integral**: for `a, b > 0`,
`∫₀¹ x^(a-1) ((1-x)^(b-1) - 1) dx = Γ(a) Γ(b) / Γ(a+b) - 1/a`. -/
theorem beta_integral_subtracted {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in (0 : ℝ)..1, x ^ (a - 1) * ((1 - x) ^ (b - 1) - 1) =
      Gamma a * Gamma b / Gamma (a + b) - 1 / a := by
  have hI : IntervalIntegrable (fun x : ℝ => x ^ (a - 1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hJ := intervalIntegrable_beta_real ha hb
  have e : ∀ x : ℝ, x ^ (a - 1) * ((1 - x) ^ (b - 1) - 1) =
      x ^ (a - 1) * (1 - x) ^ (b - 1) - x ^ (a - 1) := fun x => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_sub hJ hI, beta_integral_real ha hb,
    integral_rpow (Or.inl (by linarith))]
  have h0 : (0 : ℝ) ^ (a - 1 + 1) = 0 := by
    rw [sub_add_cancel]; exact Real.zero_rpow ha.ne'
  rw [h0, sub_add_cancel, Real.one_rpow]
  ring

/-- Linear bound for `(1 - y)^c - 1` on `[0, 1/2]`. -/
theorem exists_abs_one_sub_rpow_le (c : ℝ) :
    ∃ M : ℝ, ∀ y ∈ Icc (0 : ℝ) (1 / 2), |(1 - y) ^ c - 1| ≤ M * y := by
  have hcont : ContinuousOn (fun y : ℝ => -c * (1 - y) ^ (c - 1)) (Icc 0 (1 / 2)) := by
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.rpow_const (by fun_prop) fun y hy => Or.inl ?_
    linarith [hy.2]
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 2)).exists_bound_of_continuousOn hcont
  refine ⟨M, fun y hy => ?_⟩
  have hder : ∀ x ∈ Icc (0 : ℝ) (1 / 2),
      HasDerivWithinAt (fun y : ℝ => (1 - y) ^ c) (-c * (1 - x) ^ (c - 1)) (Icc 0 (1 / 2)) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by simpa using (hasDerivAt_id x).const_sub 1
    have := (h1.rpow_const (p := c) (Or.inl (by linarith [hx.2]))).hasDerivWithinAt
      (s := Icc 0 (1 / 2))
    convert this using 1
    ring
  have := (convex_Icc (0 : ℝ) (1 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le hder hM
    (left_mem_Icc.2 (by norm_num)) hy
  simpa [Real.norm_eq_abs, abs_of_nonneg hy.1] using this


/-- The subtracted Beta integrand is interval integrable for `-1 < a` and `0 < b`. -/
theorem intervalIntegrable_beta_subtracted {a b : ℝ} (ha : -1 < a) (hb : 0 < b) :
    IntervalIntegrable (fun y : ℝ => y ^ (a - 1) * ((1 - y) ^ (b - 1) - 1)) volume 0 1 := by
  obtain ⟨M, hM⟩ := exists_abs_one_sub_rpow_le (b - 1)
  have h1 : IntervalIntegrable (fun y : ℝ => y ^ (a - 1) * ((1 - y) ^ (b - 1) - 1)) volume 0
      (1 / 2) := by
    have hd : IntervalIntegrable (fun y : ℝ => |M| * y ^ a) volume 0 (1 / 2) :=
      (intervalIntegral.intervalIntegrable_rpow' ha).const_mul _
    refine hd.mono_fun' ?_ ?_
    · refine (Measurable.aestronglyMeasurable ?_)
      fun_prop
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      refine ae_of_all _ fun y hy => ?_
      rw [uIoc_of_le (by norm_num)] at hy
      have hy0 : 0 < y := hy.1
      have hb' := hM y ⟨hy0.le, hy.2⟩
      have : y ^ (a - 1) * y = y ^ a := by
        rw [← Real.rpow_add_one hy0.ne']; ring_nf
      have hp1 : 0 < y ^ (a - 1) := Real.rpow_pos_of_pos hy0 _
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hp1]
      calc _ ≤ y ^ (a - 1) * (M * y) := by
            gcongr
        _ ≤ y ^ (a - 1) * (|M| * y) := by
            gcongr
            exact le_abs_self M
        _ = |M| * y ^ a := by rw [← this]; ring
  have h2 : IntervalIntegrable (fun y : ℝ => y ^ (a - 1) * ((1 - y) ^ (b - 1) - 1)) volume
      (1 / 2) 1 := by
    have hB : IntervalIntegrable (fun y : ℝ => (1 - y) ^ (b - 1)) volume (1 / 2) 1 := by
      have := (intervalIntegral.intervalIntegrable_rpow' (r := b - 1) (a := 0) (b := 1 / 2)
        (by linarith)).comp_sub_left 1
      convert this.symm using 2 <;> norm_num
    have hB' : IntervalIntegrable (fun y : ℝ => (1 - y) ^ (b - 1) - 1) volume (1 / 2) 1 :=
      hB.sub intervalIntegrable_const
    refine hB'.continuousOn_mul ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.rpow_const continuousOn_id fun y hy => Or.inl ?_
    linarith [hy.1]
  exact h1.trans h2


/-- Continuation of the subtracted Beta integral to `-1 < a < 0` (second parameter `b > 0`). -/
theorem beta_integral_subtracted_neg {a b : ℝ} (ha1 : -1 < a) (ha0 : a < 0) (hb : 0 < b) :
    ∫ x in (0 : ℝ)..1, x ^ (a - 1) * ((1 - x) ^ (b - 1) - 1) =
      Gamma a * Gamma b / Gamma (a + b) - 1 / a := by
  set h : ℝ → ℝ := fun y => (1 - y) ^ (b - 1) - 1 with hh
  set F : ℝ → ℝ := fun y => y ^ a * ((1 - y) ^ b - 1) + (a + b) / (a + 1) * y ^ (a + 1) with hF
  have hA : IntervalIntegrable (fun y : ℝ => y ^ (a - 1) * h y) volume 0 1 :=
    intervalIntegrable_beta_subtracted ha1 hb
  have hB : IntervalIntegrable (fun y : ℝ => y ^ (a + 1 - 1) * h y) volume 0 1 :=
    intervalIntegrable_beta_subtracted (by linarith) hb
  have hrec : a * (∫ y in (0 : ℝ)..1, y ^ (a - 1) * h y) -
      (a + b) * (∫ y in (0 : ℝ)..1, y ^ (a + 1 - 1) * h y) = (b - 1) / (a + 1) := by
    have hint : IntervalIntegrable (fun y : ℝ => a * (y ^ (a - 1) * h y) -
        (a + b) * (y ^ (a + 1 - 1) * h y)) volume 0 1 :=
      (hA.const_mul a).sub (hB.const_mul (a + b))
    have hderiv : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt F
        (a * (y ^ (a - 1) * h y) - (a + b) * (y ^ (a + 1 - 1) * h y)) (Ioi y) y := by
      intro y hy
      have hy0 : 0 < y := hy.1
      have hy1 : 0 < 1 - y := by linarith [hy.2]
      have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
        simpa using (hasDerivAt_id y).const_sub 1
      have h2 : HasDerivAt (fun y : ℝ => (1 - y) ^ b) (-1 * b * (1 - y) ^ (b - 1)) y :=
        h1.rpow_const (Or.inl hy1.ne')
      have h3 : HasDerivAt (fun y : ℝ => y ^ a) (a * y ^ (a - 1)) y :=
        Real.hasDerivAt_rpow_const (Or.inl hy0.ne')
      have h4 : HasDerivAt (fun y : ℝ => y ^ (a + 1)) ((a + 1) * y ^ (a + 1 - 1)) y :=
        Real.hasDerivAt_rpow_const (Or.inl hy0.ne')
      have h5 := (h3.mul (h2.sub_const 1)).add (h4.const_mul ((a + b) / (a + 1)))
      refine HasDerivAt.hasDerivWithinAt ?_
      convert h5 using 1
      have e1 : (1 - y) ^ b = (1 - y) ^ (b - 1) * (1 - y) := by
        rw [← Real.rpow_add_one hy1.ne']; ring_nf
      have e2 : y ^ a = y ^ (a - 1) * y := by
        rw [← Real.rpow_add_one hy0.ne']; ring_nf
      have e3 : y ^ (a + 1 - 1) = y ^ a := by ring_nf
      simp only [hh, e3]
      rw [e1]
      rw [e2]
      have ha' : a + 1 ≠ 0 := by linarith
      field_simp
      ring
    have hcont : ContinuousOn F (Icc 0 1) := by
      intro y hy
      rcases hy.1.eq_or_lt with h0 | hpos
      · subst h0
        obtain ⟨M, hM⟩ := exists_abs_one_sub_rpow_le b
        have ha' : a + 1 ≠ 0 := by linarith
        have hF0 : F 0 = 0 := by
          simp [hF, Real.zero_rpow ha0.ne, Real.zero_rpow ha']
        have hG2 : ContinuousAt (fun y : ℝ => y ^ (a + 1)) 0 :=
          ContinuousAt.rpow_const (by fun_prop) (Or.inr (by linarith))
        have hbound : Filter.Tendsto (fun y : ℝ => |M| * y ^ (a + 1))
            (nhdsWithin 0 (Icc 0 1)) (nhds 0) := by
          have := (hG2.tendsto.const_mul |M|).mono_left
            (nhdsWithin_le_nhds (s := Icc (0 : ℝ) 1))
          simpa [Real.zero_rpow ha'] using this
        have hG1 : Filter.Tendsto (fun y : ℝ => y ^ a * ((1 - y) ^ b - 1))
            (nhdsWithin 0 (Icc 0 1)) (nhds 0) := by
          refine squeeze_zero_norm' ?_ hbound
          have hmem : Icc (0 : ℝ) 1 ∩ Iio (1 / 2 : ℝ) ∈ nhdsWithin (0 : ℝ) (Icc 0 1) :=
            inter_mem_nhdsWithin _ (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
          filter_upwards [hmem] with y hy
          rcases hy.1.1.eq_or_lt with h0 | hpos
          · subst h0
            simp [Real.zero_rpow ha0.ne, Real.zero_rpow ha']
          · have hb' := hM y ⟨hy.1.1, hy.2.le⟩
            have hp : 0 < y ^ a := Real.rpow_pos_of_pos hpos _
            have e : y ^ (a + 1) = y ^ a * y := Real.rpow_add_one hpos.ne' a
            rw [e, Real.norm_eq_abs, abs_mul, abs_of_pos hp]
            calc y ^ a * |(1 - y) ^ b - 1| ≤ y ^ a * (M * y) := by gcongr
              _ ≤ y ^ a * (|M| * y) := by gcongr; exact le_abs_self M
              _ = |M| * (y ^ a * y) := by ring
        have hG3 := (hG2.tendsto.const_mul ((a + b) / (a + 1))).mono_left
          (nhdsWithin_le_nhds (s := Icc (0 : ℝ) 1))
        have hsum := hG1.add hG3
        rw [ContinuousWithinAt, hF0]
        simpa [Real.zero_rpow ha'] using hsum
      · refine ContinuousAt.continuousWithinAt ?_
        have hc2 : ContinuousAt (fun y : ℝ => (1 - y) ^ b) y :=
          ContinuousAt.rpow_const (by fun_prop) (Or.inr hb.le)
        have hc1 : ContinuousAt (fun y : ℝ => y ^ a) y :=
          ContinuousAt.rpow_const (by fun_prop) (Or.inl hpos.ne')
        have hc3 : ContinuousAt (fun y : ℝ => y ^ (a + 1)) y :=
          ContinuousAt.rpow_const (by fun_prop) (Or.inl hpos.ne')
        exact (hc1.mul (hc2.sub continuousAt_const)).add (hc3.const_smul ((a + b) / (a + 1)))
    have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one hcont hderiv
      hint
    rw [intervalIntegral.integral_sub (hA.const_mul a) (hB.const_mul (a + b)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hftc
    rw [hftc]
    have ha' : a + 1 ≠ 0 := by linarith
    simp only [hF, Real.one_rpow, sub_self, Real.zero_rpow hb.ne', Real.zero_rpow ha0.ne,
      Real.zero_rpow ha', mul_zero, add_zero, mul_one]
    field_simp
    ring
  have hS1 := beta_integral_subtracted (a := a + 1) (b := b) (by linarith) hb
  have hΓa : Gamma (a + 1) = a * Gamma a := Real.Gamma_add_one ha0.ne
  have ha' : a + 1 ≠ 0 := by linarith
  change (∫ y in (0 : ℝ)..1, y ^ (a - 1) * h y) = _
  by_cases hab : a + b = 0
  · have hΓ0 : Gamma (a + b) = 0 := by rw [hab]; exact Real.Gamma_zero
    have hb1 : b = -a := by linarith
    rw [hΓ0, div_zero, zero_sub]
    have hr := hrec
    rw [hab, zero_mul, sub_zero, hb1] at hr
    have : (-a - 1) / (a + 1) = -1 := by field_simp; ring
    rw [this] at hr
    have hag : a ≠ 0 := ha0.ne
    rw [← neg_div, eq_div_iff hag]
    linarith [mul_comm a (∫ y in (0 : ℝ)..1, y ^ (a - 1) * h y)]
  · have hΓab : Gamma (a + b + 1) = (a + b) * Gamma (a + b) := Real.Gamma_add_one hab
    have hne : Gamma (a + b) ≠ 0 := by
      refine Real.Gamma_ne_zero fun m hm => ?_
      rcases Nat.eq_zero_or_pos m with h0 | hm0
      · subst h0; exact hab (by simpa using hm)
      · have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
        linarith
    have e : a + 1 + b = a + b + 1 := by ring
    rw [e, hΓab, hΓa] at hS1
    have hS1' : ∫ y in (0 : ℝ)..1, y ^ (a + 1 - 1) * h y =
        a * Gamma a * Gamma b / ((a + b) * Gamma (a + b)) - 1 / (a + 1) := hS1
    rw [hS1'] at hrec
    have : (∫ y in (0 : ℝ)..1, y ^ (a - 1) * h y) = Gamma a * Gamma b / Gamma (a + b) - 1 / a := by
      have hag : a ≠ 0 := ha0.ne
      field_simp at hrec ⊢
      nlinarith [hrec]
    exact this

end

end FracLap
