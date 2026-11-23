/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.HalfLine.ReflectedSemigroup
public import FracLap.WholeLine.GagliardoFourier
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# FracLap.HalfLine.FormOrdering

Ordering of the restricted and spectral half-line energies (Musina--Nazarov).

The Hankel kernel `(x + y + ε)^(-(1+α))` on `(0, ∞)²` is positive definite: it is a mixture
`Γ(1+α)⁻¹ ∫ s^α e^{-s(x+y+ε)} ds` of rank-one kernels. This is the analytic input to
`restricted_le_spectral`.
-/

namespace FracLap

open MeasureTheory Set Real
open scoped ENNReal

@[expose] public section

/-- The shifted Hankel kernel `(x + y + ε)^(-(1+α))`. -/
noncomputable def hankelKernel (α ε x y : ℝ) : ℝ := (x + y + ε) ^ (-(1 + α))

/-- **Laplace representation** of the Hankel kernel: for `x, y ≥ 0` and `ε, α > 0`,
`(x + y + ε)^(-(1+α)) = Γ(1+α)⁻¹ ∫₀^∞ s^α e^{-s (x + y + ε)} ds`. -/
theorem hankelKernel_eq_integral {α ε x y : ℝ} (hα : 0 < α) (hε : 0 < ε) (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    hankelKernel α ε x y =
      (Real.Gamma (1 + α))⁻¹ * ∫ s in Ioi (0 : ℝ), s ^ α * Real.exp (-(s * (x + y + ε))) := by
  have hr : 0 < x + y + ε := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 + α) (r := x + y + ε)
    (by linarith) hr
  simp only [add_sub_cancel_left] at h
  have e : (fun s : ℝ => s ^ α * Real.exp (-(s * (x + y + ε)))) =
      fun s : ℝ => s ^ α * Real.exp (-((x + y + ε) * s)) := by
    funext s; rw [mul_comm s]
  rw [e, h, one_div, Real.inv_rpow hr.le, hankelKernel, Real.rpow_neg hr.le]
  have : 0 < Real.Gamma (1 + α) := Real.Gamma_pos_of_pos (by linarith)
  field_simp

/-- Primitive of the Hankel kernel in `y`: `-(x + y + ε)^(-α) / α`. -/
theorem hasDerivAt_hankel_primitive {α ε x y : ℝ} (hα : 0 < α) (hε : 0 < ε) (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    HasDerivAt (fun y : ℝ => -(1 / α) * (x + y + ε) ^ (-α)) (hankelKernel α ε x y) y := by
  have hr : 0 < x + y + ε := by positivity
  have h1 : HasDerivAt (fun y : ℝ => x + y + ε) 1 y :=
    ((hasDerivAt_id' y).const_add x).add_const ε
  have h2 := (h1.rpow_const (p := -α) (Or.inl hr.ne')).const_mul (-(1 / α))
  convert h2 using 1
  unfold hankelKernel
  have : -(1 + α) = -α - 1 := by ring
  rw [this]
  field_simp

/-- The kernel is integrable on `(0, ∞)` and its integral is `(x + ε)^(-α) / α`. -/
theorem integrableOn_hankel {α ε x : ℝ} (hα : 0 < α) (hε : 0 < ε) (hx : 0 ≤ x) :
    IntegrableOn (hankelKernel α ε x) (Ioi 0) := by
  refine integrableOn_Ioi_deriv_of_nonneg (g := fun y : ℝ => -(1 / α) * (x + y + ε) ^ (-α))
    (l := 0) ?_ (fun y hy => hasDerivAt_hankel_primitive hα hε hx (le_of_lt hy))
    (fun y hy => ?_) ?_
  · exact (hasDerivAt_hankel_primitive hα hε hx le_rfl).continuousAt.continuousWithinAt
  · unfold hankelKernel; exact Real.rpow_nonneg (by have : 0 < y := hy; positivity) _
  · have h1 : Filter.Tendsto (fun y : ℝ => x + y + ε) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ _ (Filter.tendsto_atTop_add_const_left _ _
        Filter.tendsto_id)
    have h2 := (tendsto_rpow_neg_atTop hα).comp h1
    simpa using h2.const_mul (-(1 / α))

theorem integral_hankel {α ε x : ℝ} (hα : 0 < α) (hε : 0 < ε) (hx : 0 ≤ x) :
    ∫ y in Ioi (0 : ℝ), hankelKernel α ε x y = (x + ε) ^ (-α) / α := by
  have hint := integrableOn_hankel hα hε hx
  have := integral_Ioi_of_hasDerivAt_of_nonneg (g := fun y : ℝ => -(1 / α) * (x + y + ε) ^ (-α))
    (g' := hankelKernel α ε x) (l := 0)
    ((hasDerivAt_hankel_primitive hα hε hx le_rfl).continuousAt.continuousWithinAt)
    (fun y hy => hasDerivAt_hankel_primitive hα hε hx (le_of_lt hy))
    (fun y hy => by
      unfold hankelKernel; exact Real.rpow_nonneg (by have : 0 < y := hy; positivity) _)
    (by
      have h1 : Filter.Tendsto (fun y : ℝ => x + y + ε) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_right _ _ (Filter.tendsto_atTop_add_const_left _ _
          Filter.tendsto_id)
      have h2 := (tendsto_rpow_neg_atTop hα).comp h1
      simpa using h2.const_mul (-(1 / α)))
  rw [this]
  simp only [add_zero]
  rw [add_comm x ε]
  field_simp
  ring

/-- The Hankel kernel restricted to the open quadrant `(0, ∞)²`. -/
noncomputable def hankelQuadrant (α ε : ℝ) : ℝ × ℝ → ℝ :=
  (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator fun p => hankelKernel α ε p.1 p.2

theorem measurable_hankelQuadrant (α ε : ℝ) : Measurable (hankelQuadrant α ε) := by
  unfold hankelQuadrant hankelKernel
  refine Measurable.indicator ?_ (measurableSet_Ioi.prod measurableSet_Ioi)
  exact ((measurable_fst.add measurable_snd).add measurable_const).pow_const _

theorem hankelQuadrant_nonneg (α : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (p : ℝ × ℝ) :
    0 ≤ hankelQuadrant α ε p := by
  unfold hankelQuadrant
  by_cases h : p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem h]
    unfold hankelKernel
    have h1 : 0 < p.1 := h.1
    have h2 : 0 < p.2 := h.2
    exact Real.rpow_nonneg (by positivity) _
  · rw [Set.indicator_of_notMem h]

/-- The quadrant kernel times `‖z y‖²` is integrable on `ℝ × ℝ`. -/
theorem integrable_hankelQuadrant_mul_sq {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) {z : ℝ → ℂ}
    (hzm : Measurable z) (hz : MemLp z 2 volume) :
    Integrable (fun p : ℝ × ℝ => hankelQuadrant α ε p * ‖z p.2‖ ^ 2) (volume.prod volume) := by
  have hz2 : Integrable (fun y => ‖z y‖ ^ 2) := hz.integrable_norm_pow (by norm_num)
  have hmeas : Measurable (fun p : ℝ × ℝ => hankelQuadrant α ε p * ‖z p.2‖ ^ 2) :=
    (measurable_hankelQuadrant α ε).mul ((hzm.comp measurable_snd).norm.pow_const 2)
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  have hinner : ∀ y : ℝ, ∫ x, ‖hankelQuadrant α ε (x, y) * ‖z y‖ ^ 2‖ =
      if 0 < y then (y + ε) ^ (-α) / α * ‖z y‖ ^ 2 else 0 := by
    intro y
    by_cases hy : 0 < y
    · simp only [hy, ↓reduceIte]
      have : ∀ x : ℝ, ‖hankelQuadrant α ε (x, y) * ‖z y‖ ^ 2‖ =
          (Ioi (0 : ℝ)).indicator (fun x => hankelKernel α ε y x) x * ‖z y‖ ^ 2 := fun x => by
        rw [Real.norm_of_nonneg (mul_nonneg (hankelQuadrant_nonneg α hε.le _) (sq_nonneg _))]
        unfold hankelQuadrant
        by_cases hx : 0 < x
        · rw [Set.indicator_of_mem (show (x, y) ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) from ⟨hx, hy⟩),
            Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
          unfold hankelKernel; ring_nf
        · rw [Set.indicator_of_notMem (show (x, y) ∉ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) from
            fun h => hx h.1), Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]
      simp_rw [this]
      rw [integral_mul_const, integral_indicator measurableSet_Ioi, integral_hankel hα hε hy.le]
    · simp only [hy, ↓reduceIte]
      simp [hankelQuadrant, Set.indicator_of_notMem (show (_, y) ∉ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) from
        fun h => hy h.2)]
  refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
  · by_cases hy : 0 < y
    · have hI := integrableOn_hankel hα hε hy.le
      have : (fun x : ℝ => hankelQuadrant α ε (x, y) * ‖z y‖ ^ 2) =
          fun x => (Ioi (0 : ℝ)).indicator (fun x => hankelKernel α ε y x) x * ‖z y‖ ^ 2 := by
        funext x
        unfold hankelQuadrant
        by_cases hx : 0 < x
        · rw [Set.indicator_of_mem (show (x, y) ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) from ⟨hx, hy⟩),
            Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
          unfold hankelKernel; ring_nf
        · rw [Set.indicator_of_notMem (show (x, y) ∉ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) from
            fun h => hx h.1), Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]
      rw [this]
      exact (hI.integrable_indicator measurableSet_Ioi).mul_const _
    · have : (fun x : ℝ => hankelQuadrant α ε (x, y) * ‖z y‖ ^ 2) = fun _ => 0 := by
        funext x
        simp [hankelQuadrant, Set.indicator_of_notMem (show (x, y) ∉ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
          from fun h => hy h.2)]
      rw [this]; exact integrable_zero _ _ _
  · simp_rw [hinner]
    refine (hz2.const_mul (ε ^ (-α) / α)).mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (Measurable.ite measurableSet_Ioi
        ((((measurable_id.add_const ε).pow_const (-α)).div_const α).mul
          ((hzm.norm).pow_const 2)) measurable_const).aestronglyMeasurable
    · by_cases hy : 0 < y
      · simp only [hy, ↓reduceIte]
        have h1 : (y + ε) ^ (-α) ≤ ε ^ (-α) :=
          Real.rpow_le_rpow_of_nonpos hε (by linarith) (by linarith)
        rw [Real.norm_of_nonneg (by positivity)]
        have := sq_nonneg ‖z y‖
        have h2 : (y + ε) ^ (-α) / α ≤ ε ^ (-α) / α := div_le_div_of_nonneg_right h1 hα.le
        nlinarith
      · simp only [hy, ↓reduceIte, norm_zero]
        positivity

theorem hankelQuadrant_swap (α ε : ℝ) (p : ℝ × ℝ) :
    hankelQuadrant α ε p.swap = hankelQuadrant α ε p := by
  unfold hankelQuadrant hankelKernel
  by_cases h : p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show p.swap ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
      from ⟨h.2, h.1⟩)]
    simp [add_comm]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show p.swap ∉ Ioi (0 : ℝ) ×ˢ
      Ioi (0 : ℝ) from fun h' => h ⟨h'.2, h'.1⟩)]

/-- The quadrant kernel times `‖z x‖²` is integrable (by symmetry). -/
theorem integrable_hankelQuadrant_mul_sq_fst {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) {z : ℝ → ℂ}
    (hzm : Measurable z) (hz : MemLp z 2 volume) :
    Integrable (fun p : ℝ × ℝ => hankelQuadrant α ε p * ‖z p.1‖ ^ 2) (volume.prod volume) := by
  have h := integrable_hankelQuadrant_mul_sq hα hε hzm hz
  have h2 := (integrable_swap_iff (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (f := fun p : ℝ × ℝ => hankelQuadrant α ε p * ‖z p.2‖ ^ 2)).2 h
  refine h2.congr (Filter.Eventually.of_forall fun p => ?_)
  simp [Function.comp, hankelQuadrant_swap]

/-- The Hankel quadratic-form integrand is integrable for `z ∈ L²`. -/
theorem integrable_hankel_form {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) {z : ℝ → ℂ}
    (hzm : Measurable z) (hz : MemLp z 2 volume) :
    Integrable (fun p : ℝ × ℝ => (hankelQuadrant α ε p : ℂ) *
      (z p.1 * (starRingEnd ℂ) (z p.2))) (volume.prod volume) := by
  have h1 := integrable_hankelQuadrant_mul_sq_fst hα hε hzm hz
  have h2 := integrable_hankelQuadrant_mul_sq hα hε hzm hz
  have hmeas : Measurable (fun p : ℝ × ℝ => (hankelQuadrant α ε p : ℂ) *
      (z p.1 * (starRingEnd ℂ) (z p.2))) :=
    (Complex.measurable_ofReal.comp (measurable_hankelQuadrant α ε)).mul
      ((hzm.comp measurable_fst).mul (Complex.continuous_conj.measurable.comp
        (hzm.comp measurable_snd)))
  refine ((h1.add h2).const_mul (1 / 2)).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  have hk := hankelQuadrant_nonneg α hε.le p
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hk, norm_mul, Complex.norm_conj]
  have := two_mul_le_add_sq ‖z p.1‖ ‖z p.2‖
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left this hk]

/-- `s ↦ s^α e^{-r s}` is integrable on `(0, ∞)` for `r > 0`, `α > -1`. -/
theorem integrableOn_rpow_exp {α r : ℝ} (hα : -1 < α) (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => s ^ α * Real.exp (-(r * s))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := α) (b := r) hα one_pos hr
  refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  rw [neg_mul]

/-- The Laplace transform of `z` against `e^{-s x}`, for `s > 0`. -/
noncomputable def laplaceU (z : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ x : ℝ, ((Real.exp (-(s * x)) : ℝ) : ℂ) * z x

/-- **Positive definiteness of the Hankel kernel.** For `z ∈ L²` vanishing on `(-∞, 0]`,
`∬ (x + y + ε)^(-(1+α)) z(x) \overline{z(y)} = Γ(1+α)⁻¹ ∫₀^∞ s^α e^{-s ε} |U(s)|² ds`, where
`U(s) = ∫ e^{-s x} z(x) dx`. In particular the left side is a nonnegative real number. -/
theorem hankel_form_eq {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) {z : ℝ → ℂ} (hzm : Measurable z)
    (hz : MemLp z 2 volume) (hS : ∀ x ≤ 0, z x = 0) :
    ∫ p : ℝ × ℝ, (hankelQuadrant α ε p : ℂ) * (z p.1 * (starRingEnd ℂ) (z p.2))
        ∂(volume.prod volume) =
      ((Real.Gamma (1 + α))⁻¹ : ℝ) *
        ∫ s in Ioi (0 : ℝ), ((s ^ α * Real.exp (-(s * ε)) * ‖laplaceU z s‖ ^ 2 : ℝ) : ℂ) := by
  have hΓ : 0 < Real.Gamma (1 + α) := Real.Gamma_pos_of_pos (by linarith)
  set Φ : ℝ × ℝ → ℝ → ℂ := fun p s =>
    ((s ^ α * Real.exp (-(s * ε)) : ℝ) : ℂ) * (((Real.exp (-(s * p.1)) : ℝ) : ℂ) * z p.1) *
      (starRingEnd ℂ) (((Real.exp (-(s * p.2)) : ℝ) : ℂ) * z p.2) with hΦ
  have hzero : ∀ p : ℝ × ℝ, p ∉ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) → z p.1 = 0 ∨ z p.2 = 0 := by
    intro p hp
    by_contra h
    push Not at h
    exact hp ⟨lt_of_not_ge (fun h1 => h.1 (hS _ h1)), lt_of_not_ge (fun h2 => h.2 (hS _ h2))⟩
  have hΦe : ∀ p : ℝ × ℝ, p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) → ∀ s : ℝ,
      Φ p s = ((s ^ α * Real.exp (-(s * (p.1 + p.2 + ε))) : ℝ) : ℂ) *
        (z p.1 * (starRingEnd ℂ) (z p.2)) := by
    intro p hp s
    have he : Real.exp (-(s * (p.1 + p.2 + ε))) =
        Real.exp (-(s * ε)) * Real.exp (-(s * p.1)) * Real.exp (-(s * p.2)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    simp only [hΦ, map_mul, Complex.conj_ofReal]
    rw [he]; push_cast; ring
  have hΦ0 : ∀ p : ℝ × ℝ, p ∉ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) → ∀ s : ℝ, Φ p s = 0 := by
    intro p hp s
    rcases hzero p hp with h | h <;> simp [hΦ, h]
  have hpt : ∀ p : ℝ × ℝ, (hankelQuadrant α ε p : ℂ) * (z p.1 * (starRingEnd ℂ) (z p.2)) =
      (((Real.Gamma (1 + α))⁻¹ : ℝ) : ℂ) * ∫ s in Ioi (0 : ℝ), Φ p s := by
    intro p
    by_cases hp : p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
    · have hx : 0 < p.1 := hp.1
      have hy : 0 < p.2 := hp.2
      have hk : hankelQuadrant α ε p = hankelKernel α ε p.1 p.2 := by
        unfold hankelQuadrant; rw [Set.indicator_of_mem hp]
      rw [hk, hankelKernel_eq_integral hα hε hx.le hy.le]
      simp_rw [hΦe p hp]
      rw [integral_mul_const, integral_complex_ofReal]
      push_cast; ring
    · have hq : hankelQuadrant α ε p = 0 := by
        unfold hankelQuadrant; rw [Set.indicator_of_notMem hp]
      simp [hq, hΦ0 p hp]
  have hΦmeas : Measurable (Function.uncurry Φ) := by
    simp only [hΦ]
    have h1 : Measurable fun q : (ℝ × ℝ) × ℝ => q.2 ^ α := measurable_snd.pow_const _
    fun_prop
  have hint : Integrable (Function.uncurry Φ)
      ((volume.prod volume).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff hΦmeas.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun p => ?_, ?_⟩
    · change Integrable (fun s => Φ p s) _
      by_cases hp : p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
      · have hr : 0 < p.1 + p.2 + ε := by
          have hx : 0 < p.1 := hp.1
          have hy : 0 < p.2 := hp.2
          positivity
        have h := integrableOn_rpow_exp (α := α) (r := p.1 + p.2 + ε) (by linarith) hr
        have h' : Integrable (fun s : ℝ => s ^ α * Real.exp (-(s * (p.1 + p.2 + ε))))
            (volume.restrict (Ioi (0 : ℝ))) := by
          exact h.congr_fun (fun s hs => by rw [mul_comm s]) measurableSet_Ioi
        have hfun : (fun s => Φ p s) = fun s => ((s ^ α * Real.exp (-(s * (p.1 + p.2 + ε))) : ℝ) :
            ℂ) * (z p.1 * (starRingEnd ℂ) (z p.2)) := funext (hΦe p hp)
        rw [hfun]
        exact (h'.ofReal (𝕜 := ℂ)).mul_const _
      · simp only [hΦ0 p hp]; exact integrable_zero _ _ _
    · have hnorm : ∀ p : ℝ × ℝ, ∫ s in Ioi (0 : ℝ), ‖Function.uncurry Φ (p, s)‖ =
          Real.Gamma (1 + α) * (hankelQuadrant α ε p * (‖z p.1‖ * ‖z p.2‖)) := by
        intro p
        by_cases hp : p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
        · have hx : 0 < p.1 := hp.1
          have hy : 0 < p.2 := hp.2
          have hk : hankelQuadrant α ε p = hankelKernel α ε p.1 p.2 := by
            unfold hankelQuadrant; rw [Set.indicator_of_mem hp]
          have hr : 0 < p.1 + p.2 + ε := by positivity
          have hI : ∫ s in Ioi (0 : ℝ), s ^ α * Real.exp (-(s * (p.1 + p.2 + ε))) =
              Real.Gamma (1 + α) * hankelKernel α ε p.1 p.2 := by
            rw [hankelKernel_eq_integral hα hε hx.le hy.le, ← mul_assoc, mul_inv_cancel₀ hΓ.ne',
              one_mul]
          have hcongr : ∀ s ∈ Ioi (0 : ℝ), ‖Function.uncurry Φ (p, s)‖ =
              (s ^ α * Real.exp (-(s * (p.1 + p.2 + ε)))) * (‖z p.1‖ * ‖z p.2‖) := by
            intro s hs
            have hs0 : 0 < s := hs
            change ‖Φ p s‖ = _
            rw [hΦe p hp s]
            simp only [norm_mul, Complex.norm_real, Complex.norm_conj]
            rw [Real.norm_of_nonneg (Real.rpow_nonneg hs0.le _),
              Real.norm_of_nonneg (Real.exp_pos _).le]
          rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_mul_const, hI, hk]
          ring
        · have hq : hankelQuadrant α ε p = 0 := by
            unfold hankelQuadrant; rw [Set.indicator_of_notMem hp]
          simp [hq, show ∀ s, Function.uncurry Φ (p, s) = 0 from fun s => hΦ0 p hp s]
      have hfun : (fun p : ℝ × ℝ => ∫ s in Ioi (0 : ℝ), ‖Function.uncurry Φ (p, s)‖) =
          fun p => Real.Gamma (1 + α) * (hankelQuadrant α ε p * (‖z p.1‖ * ‖z p.2‖)) :=
        funext hnorm
      rw [hfun]
      have h1 := integrable_hankelQuadrant_mul_sq_fst hα hε hzm hz
      have h2 := integrable_hankelQuadrant_mul_sq hα hε hzm hz
      refine ((h1.add h2).const_mul (Real.Gamma (1 + α) / 2)).mono'
        ((measurable_const.mul ((measurable_hankelQuadrant α ε).mul
          ((hzm.comp measurable_fst).norm.mul
            (hzm.comp measurable_snd).norm))).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun p => ?_)
      have hk := hankelQuadrant_nonneg α hε.le p
      rw [Real.norm_of_nonneg (by positivity)]
      have := two_mul_le_add_sq ‖z p.1‖ ‖z p.2‖
      simp only [Pi.add_apply]
      nlinarith [mul_le_mul_of_nonneg_left this hk, mul_pos hΓ hΓ]
  have hswap := integral_integral_swap (μ := volume.prod volume)
    (ν := volume.restrict (Ioi (0 : ℝ))) (f := Φ) hint
  have hinner : ∀ s : ℝ, ∫ p : ℝ × ℝ, Φ p s ∂(volume.prod volume) =
      ((s ^ α * Real.exp (-(s * ε)) : ℝ) : ℂ) *
        ((laplaceU z s) * (starRingEnd ℂ) (laplaceU z s)) := by
    intro s
    have : ∀ p : ℝ × ℝ, Φ p s = ((s ^ α * Real.exp (-(s * ε)) : ℝ) : ℂ) *
        ((((Real.exp (-(s * p.1)) : ℝ) : ℂ) * z p.1) *
          (starRingEnd ℂ) (((Real.exp (-(s * p.2)) : ℝ) : ℂ) * z p.2)) := fun p => by
      simp only [hΦ]; ring
    simp_rw [this]
    rw [integral_const_mul]
    congr 1
    rw [integral_prod_mul (fun x : ℝ => ((Real.exp (-(s * x)) : ℝ) : ℂ) * z x)
      (fun x : ℝ => (starRingEnd ℂ) (((Real.exp (-(s * x)) : ℝ) : ℂ) * z x))]
    unfold laplaceU
    rw [integral_conj]
  calc ∫ p : ℝ × ℝ, (hankelQuadrant α ε p : ℂ) * (z p.1 * (starRingEnd ℂ) (z p.2))
          ∂(volume.prod volume)
      = ∫ p : ℝ × ℝ, ((((Real.Gamma (1 + α))⁻¹ : ℝ) : ℂ) * ∫ s in Ioi (0 : ℝ), Φ p s)
          ∂(volume.prod volume) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => hpt p)
    _ = (((Real.Gamma (1 + α))⁻¹ : ℝ) : ℂ) * ∫ p : ℝ × ℝ, (∫ s in Ioi (0 : ℝ), Φ p s)
          ∂(volume.prod volume) := by
        rw [integral_const_mul]
    _ = (((Real.Gamma (1 + α))⁻¹ : ℝ) : ℂ) * ∫ s in Ioi (0 : ℝ),
          (∫ p : ℝ × ℝ, Φ p s ∂(volume.prod volume)) := by
        rw [hswap]
    _ = _ := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
        change ∫ p : ℝ × ℝ, Φ p s ∂(volume.prod volume) = _
        rw [hinner s, Complex.mul_conj']
        push_cast; ring

/-- **Hankel quadratic form is nonnegative**: for `z ∈ L²` vanishing on `(-∞, 0]`,
`∬ (x + y + ε)^(-(1+α)) Re (z(x) \overline{z(y)}) ≥ 0`. -/
theorem hankel_form_nonneg {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) {z : ℝ → ℂ}
    (hzm : Measurable z) (hz : MemLp z 2 volume) (hS : ∀ x ≤ 0, z x = 0) :
    0 ≤ ∫ p : ℝ × ℝ, hankelQuadrant α ε p * (z p.1 * (starRingEnd ℂ) (z p.2)).re
      ∂(volume.prod volume) := by
  have h := hankel_form_eq hα hε hzm hz hS
  have hint := integrable_hankel_form hα hε hzm hz
  have hre := congrArg Complex.re h
  have hI := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at hI
  rw [← hI] at hre
  have e : ∀ p : ℝ × ℝ, ((hankelQuadrant α ε p : ℂ) * (z p.1 * (starRingEnd ℂ) (z p.2))).re =
      hankelQuadrant α ε p * (z p.1 * (starRingEnd ℂ) (z p.2)).re := fun p => by
    rw [Complex.re_ofReal_mul]
  simp_rw [e] at hre
  rw [hre]
  rw [show ((((Real.Gamma (1 + α))⁻¹ : ℝ) : ℂ) * ∫ s in Ioi (0 : ℝ),
      ((s ^ α * Real.exp (-(s * ε)) * ‖laplaceU z s‖ ^ 2 : ℝ) : ℂ)) =
      (((Real.Gamma (1 + α))⁻¹ * ∫ s in Ioi (0 : ℝ),
        (s ^ α * Real.exp (-(s * ε)) * ‖laplaceU z s‖ ^ 2) : ℝ) : ℂ) by
    rw [integral_complex_ofReal]; push_cast; ring, Complex.ofReal_re]
  have hΓ : 0 < Real.Gamma (1 + α) := Real.Gamma_pos_of_pos (by linarith)
  refine mul_nonneg (inv_nonneg.2 hΓ.le) (setIntegral_nonneg measurableSet_Ioi fun s hs => ?_)
  have : 0 < s := hs
  positivity

/-! ### Quadrant decomposition of the pair energies -/

/-- The double-integral energy of `g`: `∬ w(x, y) ‖g x - g y‖² dx dy`. -/
noncomputable def pairEnergy (α : ℝ) (g : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ, gagliardoWeight α p * ‖g p.1 - g p.2‖ₑ ^ (2 : ℝ) ∂(volume.prod volume)

theorem gagliardoWeight_neg (α : ℝ) (p : ℝ × ℝ) :
    gagliardoWeight α (-p.1, -p.2) = gagliardoWeight α p := by
  unfold gagliardoWeight
  rw [show (-p.1 - -p.2) = -(p.1 - p.2) by ring, abs_neg]

theorem gagliardoWeight_neg_snd_neg (α : ℝ) (p : ℝ × ℝ) :
    gagliardoWeight α (p.1, -(-p.2)) = gagliardoWeight α p := by
  rw [neg_neg]

theorem gagliardoWeight_swap (α : ℝ) (p : ℝ × ℝ) :
    gagliardoWeight α p.swap = gagliardoWeight α p := by
  unfold gagliardoWeight
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [abs_sub_comm]

theorem mp_neg_snd : MeasurePreserving (fun p : ℝ × ℝ => (p.1, -p.2)) (volume.prod volume)
    (volume.prod volume) :=
  (MeasurePreserving.id volume).prod (Measure.measurePreserving_neg volume)

theorem mp_neg_fst : MeasurePreserving (fun p : ℝ × ℝ => (-p.1, p.2)) (volume.prod volume)
    (volume.prod volume) :=
  (Measure.measurePreserving_neg volume).prod (MeasurePreserving.id volume)

theorem mp_neg_both : MeasurePreserving (fun p : ℝ × ℝ => (-p.1, -p.2)) (volume.prod volume)
    (volume.prod volume) :=
  (Measure.measurePreserving_neg volume).prod (Measure.measurePreserving_neg volume)

/-- The coordinate axes form a null set of the plane. -/
theorem axes_null : (volume.prod volume) {p : ℝ × ℝ | p.1 = 0 ∨ p.2 = 0} = 0 := by
  have h : {p : ℝ × ℝ | p.1 = 0 ∨ p.2 = 0} = ({0} : Set ℝ) ×ˢ univ ∪ univ ×ˢ ({0} : Set ℝ) := by
    ext p; simp
  rw [h]
  refine measure_union_null ?_ ?_
  · rw [Measure.prod_prod]; simp
  · rw [Measure.prod_prod]; simp

/-- Transfer of a set-lintegral along a measure-preserving map of the plane. -/
theorem lintegral_region_transfer {f : ℝ × ℝ → ℝ × ℝ}
    (hf : MeasurePreserving f (volume.prod volume) (volume.prod volume)) {R T : Set (ℝ × ℝ)}
    (hT : MeasurableSet T) (hR : MeasurableSet R) (hpre : f ⁻¹' T = R) {F G : ℝ × ℝ → ℝ≥0∞}
    (hG : Measurable G) (hFG : ∀ p ∈ R, F p = G (f p)) :
    ∫⁻ p in R, F p ∂(volume.prod volume) = ∫⁻ q in T, G q ∂(volume.prod volume) := by
  calc ∫⁻ p in R, F p ∂(volume.prod volume)
      = ∫⁻ p in R, G (f p) ∂(volume.prod volume) := setLIntegral_congr_fun hR hFG
    _ = ∫⁻ p in f ⁻¹' T, G (f p) ∂(volume.prod volume) := by rw [hpre]
    _ = ∫⁻ q in T, G q ∂(volume.prod volume) := hf.setLIntegral_comp_preimage hT hG

/-- Squared modulus in `[0, ∞]`. -/
noncomputable def esq (a : ℂ) : ℝ≥0∞ := ‖a‖ₑ ^ (2 : ℝ)

theorem esq_neg (a : ℂ) : esq (-a) = esq a := by unfold esq; rw [eNorm_neg]

theorem measurable_esq : Measurable esq := by
  unfold esq; exact (measurable_eNorm).pow_const _

/-- `∬_{(0,∞)²} w(x, y) |z x - z y|²`. -/
noncomputable def qSS (α : ℝ) (z : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), gagliardoWeight α p * esq (z p.1 - z p.2)
    ∂(volume.prod volume)

/-- `∬_{(0,∞)²} w(x, -y) |z x|²`. -/
noncomputable def qT1 (α : ℝ) (z : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), gagliardoWeight α (p.1, -p.2) * esq (z p.1)
    ∂(volume.prod volume)

/-- `∬_{(0,∞)²} w(x, -y) |z y|²`. -/
noncomputable def qT2 (α : ℝ) (z : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), gagliardoWeight α (p.1, -p.2) * esq (z p.2)
    ∂(volume.prod volume)

/-- `∬_{(0,∞)²} w(x, -y) |z x + z y|²`. -/
noncomputable def qI2 (α : ℝ) (z : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), gagliardoWeight α (p.1, -p.2) * esq (z p.1 + z p.2)
    ∂(volume.prod volume)

/-- **Restricted energy of a half-line function**: `E(z) ≤ qSS + qT1 + qT2`
(in fact equality). -/
theorem pairEnergy_le {α : ℝ} {z : ℝ → ℂ} (hzm : Measurable z) (hS : ∀ x ≤ 0, z x = 0) :
    pairEnergy α z ≤ qSS α z + qT1 α z + qT2 α z := by
  set S : Set ℝ := Ioi 0 with hSdef
  set Nn : Set ℝ := Iio 0 with hNdef
  set Zs : Set (ℝ × ℝ) := {p | p.1 = 0 ∨ p.2 = 0} with hZ
  set F : ℝ × ℝ → ℝ≥0∞ := fun p => gagliardoWeight α p * esq (z p.1 - z p.2) with hF
  have hFm : Measurable F := (measurable_gagliardoWeight α).mul
    (measurable_esq.comp ((hzm.comp measurable_fst).sub (hzm.comp measurable_snd)))
  have hcover : (univ : Set (ℝ × ℝ)) ⊆ (S ×ˢ S ∪ S ×ˢ Nn ∪ Nn ×ˢ S ∪ Nn ×ˢ Nn) ∪ Zs := by
    intro p _
    by_cases h1 : p.1 = 0
    · exact Or.inr (Or.inl h1)
    by_cases h2 : p.2 = 0
    · exact Or.inr (Or.inr h2)
    refine Or.inl ?_
    rcases lt_or_gt_of_ne h1 with a | a <;> rcases lt_or_gt_of_ne h2 with b | b
    · exact Or.inr ⟨a, b⟩
    · exact Or.inl (Or.inr ⟨a, b⟩)
    · exact Or.inl (Or.inl (Or.inr ⟨a, b⟩))
    · exact Or.inl (Or.inl (Or.inl ⟨a, b⟩))
  have hmS : MeasurableSet S := measurableSet_Ioi
  have hmN : MeasurableSet Nn := measurableSet_Iio
  have hNN : ∫⁻ p in Nn ×ˢ Nn, F p ∂(volume.prod volume) = 0 := by
    rw [setLIntegral_congr_fun (hmN.prod hmN) (g := fun _ => (0 : ℝ≥0∞)) (fun p hp => by
      have h1 : z p.1 = 0 := hS _ (le_of_lt hp.1)
      have h2 : z p.2 = 0 := hS _ (le_of_lt hp.2)
      simp [hF, h1, h2, esq])]
    simp
  have hZ0 : ∫⁻ p in Zs, F p ∂(volume.prod volume) = 0 := setLIntegral_measure_zero _ _ axes_null
  have hSN : ∫⁻ p in S ×ˢ Nn, F p ∂(volume.prod volume) = qT1 α z := by
    unfold qT1
    refine lintegral_region_transfer mp_neg_snd (hmS.prod hmS) (hmS.prod hmN) ?_ ?_ ?_
    · ext p; simp [hSdef, hNdef]
    · exact (measurable_gagliardoWeight α |>.comp (measurable_fst.prodMk measurable_snd.neg)).mul
        (measurable_esq.comp (hzm.comp measurable_fst))
    · intro p hp
      have h2 : z p.2 = 0 := hS _ (le_of_lt hp.2)
      simp only [hF, h2, sub_zero, neg_neg]
  have hNS : ∫⁻ p in Nn ×ˢ S, F p ∂(volume.prod volume) = qT2 α z := by
    unfold qT2
    refine lintegral_region_transfer mp_neg_fst (hmS.prod hmS) (hmN.prod hmS) ?_ ?_ ?_
    · ext p; simp [hSdef, hNdef]
    · exact (measurable_gagliardoWeight α |>.comp (measurable_fst.prodMk measurable_snd.neg)).mul
        (measurable_esq.comp (hzm.comp measurable_snd))
    · intro p hp
      have h1 : z p.1 = 0 := hS _ (le_of_lt hp.1)
      simp only [hF, h1, zero_sub, esq_neg]
      rw [gagliardoWeight_neg α p]
  have a1 := lintegral_union_le F (S ×ˢ S ∪ S ×ˢ Nn ∪ Nn ×ˢ S) (Nn ×ˢ Nn) (μ := volume.prod volume)
  have a2 := lintegral_union_le F (S ×ˢ S ∪ S ×ˢ Nn) (Nn ×ˢ S) (μ := volume.prod volume)
  have a3 := lintegral_union_le F (S ×ˢ S) (S ×ˢ Nn) (μ := volume.prod volume)
  have a4 := lintegral_union_le F (S ×ˢ S ∪ S ×ˢ Nn ∪ Nn ×ˢ S ∪ Nn ×ˢ Nn) Zs
    (μ := volume.prod volume)
  have hU : ∫⁻ p in S ×ˢ S ∪ S ×ˢ Nn ∪ Nn ×ˢ S ∪ Nn ×ˢ Nn, F p ∂(volume.prod volume) ≤
      qSS α z + qT1 α z + qT2 α z := by
    calc ∫⁻ p in S ×ˢ S ∪ S ×ˢ Nn ∪ Nn ×ˢ S ∪ Nn ×ˢ Nn, F p ∂(volume.prod volume)
        ≤ (∫⁻ p in S ×ˢ S ∪ S ×ˢ Nn ∪ Nn ×ˢ S, F p ∂(volume.prod volume)) +
            ∫⁻ p in Nn ×ˢ Nn, F p ∂(volume.prod volume) := a1
      _ = ∫⁻ p in S ×ˢ S ∪ S ×ˢ Nn ∪ Nn ×ˢ S, F p ∂(volume.prod volume) := by
          rw [hNN, add_zero]
      _ ≤ (∫⁻ p in S ×ˢ S ∪ S ×ˢ Nn, F p ∂(volume.prod volume)) +
            ∫⁻ p in Nn ×ˢ S, F p ∂(volume.prod volume) := a2
      _ ≤ ((∫⁻ p in S ×ˢ S, F p ∂(volume.prod volume)) +
            ∫⁻ p in S ×ˢ Nn, F p ∂(volume.prod volume)) +
            ∫⁻ p in Nn ×ˢ S, F p ∂(volume.prod volume) := by gcongr
      _ = qSS α z + qT1 α z + qT2 α z := by rw [hSN, hNS]; rfl
  calc pairEnergy α z = ∫⁻ p in univ, F p ∂(volume.prod volume) := by
        rw [Measure.restrict_univ]; rfl
    _ ≤ ∫⁻ p in (S ×ˢ S ∪ S ×ˢ Nn ∪ Nn ×ˢ S ∪ Nn ×ˢ Nn) ∪ Zs, F p ∂(volume.prod volume) :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ p in S ×ˢ S ∪ S ×ˢ Nn ∪ Nn ×ˢ S ∪ Nn ×ˢ Nn, F p ∂(volume.prod volume)) +
          ∫⁻ p in Zs, F p ∂(volume.prod volume) := a4
    _ ≤ qSS α z + qT1 α z + qT2 α z := by rw [hZ0, add_zero]; exact hU

/-- **Spectral energy of the odd extension**: `E(z - z(-·)) ≥ 2 qSS + 2 qI2`
(in fact equality). -/
theorem two_qSS_add_le_pairEnergy_odd {α : ℝ} {z : ℝ → ℂ} (hzm : Measurable z)
    (hS : ∀ x ≤ 0, z x = 0) :
    2 * qSS α z + 2 * qI2 α z ≤ pairEnergy α (fun x => z x - z (-x)) := by
  set S : Set ℝ := Ioi 0 with hSdef
  set Nn : Set ℝ := Iio 0 with hNdef
  set o : ℝ → ℂ := fun x => z x - z (-x) with ho
  set F : ℝ × ℝ → ℝ≥0∞ := fun p => gagliardoWeight α p * esq (o p.1 - o p.2) with hF
  have hmS : MeasurableSet S := measurableSet_Ioi
  have hmN : MeasurableSet Nn := measurableSet_Iio
  have hGm : Measurable (fun q : ℝ × ℝ => gagliardoWeight α (q.1, -q.2) *
      esq (z q.1 + z q.2)) :=
    (measurable_gagliardoWeight α |>.comp (measurable_fst.prodMk measurable_snd.neg)).mul
      (measurable_esq.comp ((hzm.comp measurable_fst).add (hzm.comp measurable_snd)))
  have hSS : ∫⁻ p in S ×ˢ S, F p ∂(volume.prod volume) = qSS α z := by
    unfold qSS
    refine setLIntegral_congr_fun (hmS.prod hmS) fun p hp => ?_
    have h1 : z (-p.1) = 0 := hS _ (by have : 0 < p.1 := hp.1; linarith)
    have h2 : z (-p.2) = 0 := hS _ (by have : 0 < p.2 := hp.2; linarith)
    simp [hF, ho, h1, h2]
  have hNN : ∫⁻ p in Nn ×ˢ Nn, F p ∂(volume.prod volume) = qSS α z := by
    unfold qSS
    refine lintegral_region_transfer mp_neg_both (hmS.prod hmS) (hmN.prod hmN) ?_
      ((measurable_gagliardoWeight α).mul (measurable_esq.comp
        ((hzm.comp measurable_fst).sub (hzm.comp measurable_snd)))) ?_
    · ext p; simp [hSdef, hNdef]
    · intro p hp
      have h1 : z p.1 = 0 := hS _ (le_of_lt hp.1)
      have h2 : z p.2 = 0 := hS _ (le_of_lt hp.2)
      simp only [hF, ho, h1, h2, zero_sub, gagliardoWeight_neg α p]
      congr 1
      rw [← esq_neg]; congr 1; ring
  have hSN : ∫⁻ p in S ×ˢ Nn, F p ∂(volume.prod volume) = qI2 α z := by
    unfold qI2
    refine lintegral_region_transfer mp_neg_snd (hmS.prod hmS) (hmS.prod hmN) ?_ hGm ?_
    · ext p; simp [hSdef, hNdef]
    · intro p hp
      have h1 : z (-p.1) = 0 := hS _ (by have : 0 < p.1 := hp.1; linarith)
      have h2 : z p.2 = 0 := hS _ (le_of_lt hp.2)
      simp only [hF, ho, h1, h2, zero_sub, sub_zero, neg_neg]
      congr 2; ring
  have hNS : ∫⁻ p in Nn ×ˢ S, F p ∂(volume.prod volume) = qI2 α z := by
    unfold qI2
    refine lintegral_region_transfer mp_neg_fst (hmS.prod hmS) (hmN.prod hmS) ?_ hGm ?_
    · ext p; simp [hSdef, hNdef]
    · intro p hp
      have h1 : z p.1 = 0 := hS _ (le_of_lt hp.1)
      have h2 : z (-p.2) = 0 := hS _ (by have : 0 < p.2 := hp.2; linarith)
      simp only [hF, ho, h1, h2, zero_sub, sub_zero, gagliardoWeight_neg α p]
      congr 1
      rw [← esq_neg]; congr 1; ring
  have hd1 : Disjoint (S ×ˢ S) (S ×ˢ Nn) := by
    rw [Set.disjoint_left]; intro p hp hq
    have h1 : 0 < p.2 := hp.2
    have h2 : p.2 < 0 := hq.2
    linarith
  have hd2 : Disjoint (S ×ˢ S ∪ S ×ˢ Nn) (Nn ×ˢ S) := by
    rw [Set.disjoint_left]; intro p hp hq
    have h1 : p.1 < 0 := hq.1
    rcases hp with hp | hp
    · have : 0 < p.1 := hp.1
      linarith
    · have : 0 < p.1 := hp.1
      linarith
  have hd3 : Disjoint (S ×ˢ S ∪ S ×ˢ Nn ∪ Nn ×ˢ S) (Nn ×ˢ Nn) := by
    rw [Set.disjoint_left]; intro p hp hq
    have h1 : p.1 < 0 := hq.1
    have h2 : p.2 < 0 := hq.2
    rcases hp with (hp | hp) | hp
    · have : 0 < p.1 := hp.1
      linarith
    · have : 0 < p.1 := hp.1
      linarith
    · have : 0 < p.2 := hp.2
      linarith
  have hU : ∫⁻ p in S ×ˢ S ∪ S ×ˢ Nn ∪ Nn ×ˢ S ∪ Nn ×ˢ Nn, F p ∂(volume.prod volume) =
      qSS α z + qI2 α z + qI2 α z + qSS α z := by
    rw [lintegral_union (hmN.prod hmN) hd3, lintegral_union (hmN.prod hmS) hd2,
      lintegral_union (hmS.prod hmN) hd1, hSS, hSN, hNS, hNN]
  calc 2 * qSS α z + 2 * qI2 α z = qSS α z + qI2 α z + qI2 α z + qSS α z := by ring
    _ = ∫⁻ p in S ×ˢ S ∪ S ×ˢ Nn ∪ Nn ×ˢ S ∪ Nn ×ˢ Nn, F p ∂(volume.prod volume) := hU.symm
    _ ≤ ∫⁻ p in univ, F p ∂(volume.prod volume) := lintegral_mono_set (subset_univ _)
    _ = pairEnergy α o := by rw [Measure.restrict_univ]; rfl

theorem esq_eq_ofReal (a : ℂ) : esq a = ENNReal.ofReal (‖a‖ ^ 2) := by
  unfold esq; rw [enorm_rpow_two_eq_ofReal]

/-- **Positive definiteness at the level of lower integrals**: for `ε > 0` and `c ≥ 0`,
`∬ c k_ε (|z x|² + |z y|²) ≤ ∬ c k_ε |z x + z y|²`. -/
theorem hankel_lintegral_le {α ε c : ℝ} (hα : 0 < α) (hε : 0 < ε) (hc : 0 ≤ c) {z : ℝ → ℂ}
    (hzm : Measurable z) (hz : MemLp z 2 volume) (hS : ∀ x ≤ 0, z x = 0) :
    ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (c * hankelQuadrant α ε p) * (esq (z p.1) + esq (z p.2))
        ∂(volume.prod volume) ≤
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (c * hankelQuadrant α ε p) * esq (z p.1 + z p.2)
        ∂(volume.prod volume) := by
  have ia := integrable_hankelQuadrant_mul_sq_fst hα hε hzm hz
  have ib := integrable_hankelQuadrant_mul_sq hα hε hzm hz
  have ir : Integrable (fun p : ℝ × ℝ => hankelQuadrant α ε p *
      (z p.1 * (starRingEnd ℂ) (z p.2)).re) (volume.prod volume) := by
    have h := (integrable_hankel_form hα hε hzm hz).re
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp
  have hQ := hankel_form_nonneg hα hε hzm hz hS
  have hk : ∀ p : ℝ × ℝ, 0 ≤ hankelQuadrant α ε p := hankelQuadrant_nonneg α hε.le
  -- pointwise real forms
  have e3 : ∀ p : ℝ × ℝ, c * hankelQuadrant α ε p * (‖z p.1‖ ^ 2 + ‖z p.2‖ ^ 2) =
      c * (hankelQuadrant α ε p * ‖z p.1‖ ^ 2 + hankelQuadrant α ε p * ‖z p.2‖ ^ 2) :=
    fun p => by ring
  have e2 : ∀ p : ℝ × ℝ, c * hankelQuadrant α ε p * ‖z p.1 + z p.2‖ ^ 2 =
      c * (hankelQuadrant α ε p * ‖z p.1‖ ^ 2 + hankelQuadrant α ε p * ‖z p.2‖ ^ 2 +
        2 * (hankelQuadrant α ε p * (z p.1 * (starRingEnd ℂ) (z p.2)).re)) := fun p => by
    have : ‖z p.1 + z p.2‖ ^ 2 = ‖z p.1‖ ^ 2 + ‖z p.2‖ ^ 2 +
        2 * (z p.1 * (starRingEnd ℂ) (z p.2)).re := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_add]
    rw [this]; ring
  have iL : Integrable (fun p : ℝ × ℝ => c * (hankelQuadrant α ε p * ‖z p.1‖ ^ 2 +
      hankelQuadrant α ε p * ‖z p.2‖ ^ 2)) (volume.prod volume) :=
    (ia.add ib).const_mul c
  have iR : Integrable (fun p : ℝ × ℝ => c * (hankelQuadrant α ε p * ‖z p.1‖ ^ 2 +
      hankelQuadrant α ε p * ‖z p.2‖ ^ 2 + 2 * (hankelQuadrant α ε p *
        (z p.1 * (starRingEnd ℂ) (z p.2)).re))) (volume.prod volume) :=
    ((ia.add ib).add (ir.const_mul 2)).const_mul c
  have nnR : 0 ≤ᵐ[volume.prod volume] fun p : ℝ × ℝ => c * (hankelQuadrant α ε p * ‖z p.1‖ ^ 2 +
      hankelQuadrant α ε p * ‖z p.2‖ ^ 2 + 2 * (hankelQuadrant α ε p *
        (z p.1 * (starRingEnd ℂ) (z p.2)).re)) := by
    refine Filter.Eventually.of_forall fun p => ?_
    simp only [Pi.zero_apply]
    rw [← e2 p]; have := hk p; positivity
  have nnL : 0 ≤ᵐ[volume.prod volume] fun p : ℝ × ℝ => c * (hankelQuadrant α ε p *
      ‖z p.1‖ ^ 2 + hankelQuadrant α ε p * ‖z p.2‖ ^ 2) := by
    refine Filter.Eventually.of_forall fun p => ?_
    simp only [Pi.zero_apply]
    have := hk p; positivity
  have hL : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (c * hankelQuadrant α ε p) *
      (esq (z p.1) + esq (z p.2)) ∂(volume.prod volume) =
      ENNReal.ofReal (∫ p : ℝ × ℝ, c * (hankelQuadrant α ε p * ‖z p.1‖ ^ 2 +
        hankelQuadrant α ε p * ‖z p.2‖ ^ 2) ∂(volume.prod volume)) := by
    rw [ofReal_integral_eq_lintegral_ofReal iL nnL]
    refine lintegral_congr fun p => ?_
    rw [esq_eq_ofReal, esq_eq_ofReal, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by have := hk p; positivity), ← e3 p]
  have hR : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (c * hankelQuadrant α ε p) *
      esq (z p.1 + z p.2) ∂(volume.prod volume) =
      ENNReal.ofReal (∫ p : ℝ × ℝ, c * (hankelQuadrant α ε p * ‖z p.1‖ ^ 2 +
        hankelQuadrant α ε p * ‖z p.2‖ ^ 2 + 2 * (hankelQuadrant α ε p *
          (z p.1 * (starRingEnd ℂ) (z p.2)).re)) ∂(volume.prod volume)) := by
    rw [ofReal_integral_eq_lintegral_ofReal iR nnR]
    refine lintegral_congr fun p => ?_
    rw [esq_eq_ofReal, ← ENNReal.ofReal_mul (by have := hk p; positivity), ← e2 p]
  rw [hL, hR]
  refine ENNReal.ofReal_le_ofReal ?_
  have iab : Integrable (fun p : ℝ × ℝ => hankelQuadrant α ε p * ‖z p.1‖ ^ 2 +
      hankelQuadrant α ε p * ‖z p.2‖ ^ 2) (volume.prod volume) := ia.add ib
  have ir2 : Integrable (fun p : ℝ × ℝ => 2 * (hankelQuadrant α ε p *
      (z p.1 * (starRingEnd ℂ) (z p.2)).re)) (volume.prod volume) := ir.const_mul 2
  rw [integral_const_mul, integral_const_mul,
    integral_add (f := fun p : ℝ × ℝ => hankelQuadrant α ε p * ‖z p.1‖ ^ 2 +
      hankelQuadrant α ε p * ‖z p.2‖ ^ 2) (g := fun p : ℝ × ℝ => 2 * (hankelQuadrant α ε p *
        (z p.1 * (starRingEnd ℂ) (z p.2)).re)) iab ir2, integral_const_mul]
  nlinarith [mul_nonneg hc hQ]

theorem gagliardoWeight_hankel {α : ℝ} {p : ℝ × ℝ} (hp : p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :
    gagliardoWeight α (p.1, -p.2) =
      ENNReal.ofReal (fracLapConstant α / 2 * hankelQuadrant α 0 p) := by
  have hx : 0 < p.1 := hp.1
  have hy : 0 < p.2 := hp.2
  unfold gagliardoWeight hankelQuadrant hankelKernel
  rw [Set.indicator_of_mem hp]
  congr 1
  simp only [sub_neg_eq_add]
  rw [abs_of_pos (by positivity), add_zero, Real.rpow_neg (by positivity)]
  field_simp

theorem hankelQuadrant_le_zero {α ε : ℝ} (hε : 0 ≤ ε) {p : ℝ × ℝ}
    (hp : p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (hα : 0 < α) :
    hankelQuadrant α ε p ≤ hankelQuadrant α 0 p := by
  have hx : 0 < p.1 := hp.1
  have hy : 0 < p.2 := hp.2
  unfold hankelQuadrant hankelKernel
  rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
  exact Real.rpow_le_rpow_of_nonpos (x := p.1 + p.2 + 0) (y := p.1 + p.2 + ε)
    (z := -(1 + α)) (by positivity) (by linarith) (by linarith)

/-- **Hankel domination**: `qT1 + qT2 ≤ qI2` for `z ∈ L²(0, ∞)` and `0 < α < 2`
(`qI2 - qT1 - qT2 = 2 ∬ w(x, -y) Re (z x \overline{z y}) ≥ 0`). -/
theorem qT_le_qI2 {α : ℝ} (hα : FractionalExponent α) {z : ℝ → ℂ} (hzm : Measurable z)
    (hz : MemLp z 2 volume) (hS : ∀ x ≤ 0, z x = 0) :
    qT1 α z + qT2 α z ≤ qI2 α z := by
  have hα0 : 0 < α := hα.1
  have hC := fracLapConstant_pos hα
  set c : ℝ := fracLapConstant α / 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set Q : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) with hQ
  have hmQ : MeasurableSet Q := measurableSet_Ioi.prod measurableSet_Ioi
  set εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεn
  have hεpos : ∀ n, 0 < εn n := fun n => by simp only [hεn]; positivity
  have hkeq : ∀ (ε : ℝ) (p : ℝ × ℝ), p ∈ Q → hankelQuadrant α ε p =
      (p.1 + p.2 + ε) ^ (-(1 + α)) := fun ε p hp => by
    unfold hankelQuadrant hankelKernel; rw [Set.indicator_of_mem hp]
  have hgmono : ∀ p : ℝ × ℝ, Monotone fun n : ℕ =>
      ENNReal.ofReal (c * hankelQuadrant α (εn n) p) := by
    intro p m n hmn
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hc0)
    by_cases hp : p ∈ Q
    · rw [hkeq _ p hp, hkeq _ p hp]
      have hx : 0 < p.1 := hp.1
      have hy : 0 < p.2 := hp.2
      have hen : εn n ≤ εn m := by
        simp only [hεn]
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast by linarith)
      have := hεpos n
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    · unfold hankelQuadrant; rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]
  set f : ℕ → ℝ × ℝ → ℝ≥0∞ := fun n p => ENNReal.ofReal (c * hankelQuadrant α (εn n) p) *
    (esq (z p.1) + esq (z p.2)) with hf
  have hfm : ∀ n, Measurable (f n) := fun n =>
    (ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_hankelQuadrant α _))).mul
      ((measurable_esq.comp (hzm.comp measurable_fst)).add
        (measurable_esq.comp (hzm.comp measurable_snd)))
  have hmono : Monotone f := by
    intro m n hmn p
    exact mul_le_mul_of_nonneg_right (hgmono p hmn) bot_le
  -- pointwise supremum
  have hsup : ∀ p : ℝ × ℝ, ⨆ n, f n p =
      Q.indicator (fun p => gagliardoWeight α (p.1, -p.2) * (esq (z p.1) + esq (z p.2))) p := by
    intro p
    by_cases hp : p ∈ Q
    · rw [Set.indicator_of_mem hp, gagliardoWeight_hankel hp]
      simp only [hf]
      rw [← ENNReal.iSup_mul]
      congr 1
      have hx : 0 < p.1 := hp.1
      have hy : 0 < p.2 := hp.2
      have ht : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (c * hankelQuadrant α (εn n) p))
          Filter.atTop (nhds (ENNReal.ofReal (c * hankelQuadrant α 0 p))) := by
        refine (ENNReal.tendsto_ofReal ?_)
        refine Filter.Tendsto.const_mul c ?_
        simp_rw [hkeq _ p hp]
        have h0 : Filter.Tendsto εn Filter.atTop (nhds 0) := by
          simp only [hεn]
          exact tendsto_one_div_add_atTop_nhds_zero_nat
        have h1 : Filter.Tendsto (fun n : ℕ => p.1 + p.2 + εn n) Filter.atTop
            (nhds (p.1 + p.2 + 0)) := tendsto_const_nhds.add h0
        exact (Real.continuousAt_rpow_const (p.1 + p.2 + 0) (-(1 + α))
          (Or.inl (by positivity))).tendsto.comp h1
      exact iSup_eq_of_tendsto (hgmono p) ht
    · rw [Set.indicator_of_notMem hp]
      have : ∀ n, f n p = 0 := fun n => by
        simp only [hf]
        have : hankelQuadrant α (εn n) p = 0 := by
          unfold hankelQuadrant; rw [Set.indicator_of_notMem hp]
        simp [this]
      simp [this]
  -- the quantity `J₂(ε) ≤ qI2`
  have hJ2 : ∀ n, ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (c * hankelQuadrant α (εn n) p) *
      esq (z p.1 + z p.2) ∂(volume.prod volume) ≤ qI2 α z := by
    intro n
    have hsupp : Function.support (fun p : ℝ × ℝ => ENNReal.ofReal (c * hankelQuadrant α (εn n) p) *
        esq (z p.1 + z p.2)) ⊆ Q := by
      intro p hp
      by_contra hpQ
      apply hp
      have : hankelQuadrant α (εn n) p = 0 := by
        unfold hankelQuadrant; rw [Set.indicator_of_notMem hpQ]
      simp [this]
    rw [← setLIntegral_eq_of_support_subset hsupp]
    unfold qI2
    refine setLIntegral_mono' hmQ fun p hp => ?_
    rw [gagliardoWeight_hankel hp]
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (hankelQuadrant_le_zero (hεpos n).le hp hα0) hc0)) bot_le
  have hE : ∫⁻ p, ⨆ n, f n p ∂(volume.prod volume) = ⨆ n, ∫⁻ p, f n p ∂(volume.prod volume) :=
    lintegral_iSup hfm hmono
  have hqT : qT1 α z + qT2 α z =
      ∫⁻ p, Q.indicator (fun p => gagliardoWeight α (p.1, -p.2) *
        (esq (z p.1) + esq (z p.2))) p ∂(volume.prod volume) := by
    rw [lintegral_indicator hmQ]
    unfold qT1 qT2
    have hm1 : Measurable (fun p : ℝ × ℝ => gagliardoWeight α (p.1, -p.2) * esq (z p.1)) :=
      ((measurable_gagliardoWeight α).comp (measurable_fst.prodMk measurable_snd.neg)).mul
        (measurable_esq.comp (hzm.comp measurable_fst))
    rw [← lintegral_add_left hm1]
    refine lintegral_congr fun p => ?_
    rw [mul_add]
  rw [hqT]
  simp_rw [← hsup]
  rw [hE]
  refine iSup_le fun n => ?_
  exact (hankel_lintegral_le hα0 (hεpos n) hc0 hzm hz hS).trans (hJ2 n)

/-- **Restricted energy ≤ spectral energy** (function level): for `z ∈ L²` vanishing on
`(-∞, 0]` and `0 < α < 2`, `E(z) ≤ ½ E(z - z(-·))`; here `½ E(z - z(-·))` is the energy of the odd
(Dirichlet) extension and `E(z)` that of the zero extension. -/
theorem pairEnergy_le_half_odd {α : ℝ} (hα : FractionalExponent α) {z : ℝ → ℂ}
    (hzm : Measurable z) (hz : MemLp z 2 volume) (hS : ∀ x ≤ 0, z x = 0) :
    pairEnergy α z ≤ 2⁻¹ * pairEnergy α (fun x => z x - z (-x)) := by
  have h1 := pairEnergy_le hzm hS (α := α)
  have h2 := qT_le_qI2 hα hzm hz hS
  have h3 := two_qSS_add_le_pairEnergy_odd hzm hS (α := α)
  have h4 : 2 * pairEnergy α z ≤ pairEnergy α (fun x => z x - z (-x)) := by
    calc 2 * pairEnergy α z ≤ 2 * (qSS α z + qT1 α z + qT2 α z) := by gcongr
      _ = 2 * qSS α z + 2 * (qT1 α z + qT2 α z) := by ring
      _ ≤ 2 * qSS α z + 2 * qI2 α z := by gcongr
      _ ≤ _ := h3
  calc pairEnergy α z = 2⁻¹ * (2 * pairEnergy α z) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ 2⁻¹ * pairEnergy α (fun x => z x - z (-x)) := by gcongr

/-- The pair energy only depends on the a.e. class. -/
theorem pairEnergy_congr_ae (α : ℝ) {g h : ℝ → ℂ} (hgh : g =ᵐ[volume] h) :
    pairEnergy α g = pairEnergy α h := by
  unfold pairEnergy
  refine lintegral_congr_ae ?_
  have h1 : (fun p : ℝ × ℝ => g p.1) =ᵐ[volume.prod volume] fun p => h p.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).ae_eq_comp hgh
  have h2 : (fun p : ℝ × ℝ => g p.2) =ᵐ[volume.prod volume] fun p => h p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).ae_eq_comp hgh
  filter_upwards [h1, h2] with p a b
  simp only [a, b]

/-- **Restricted ≤ spectral ordering on the half-line** (Musina--Nazarov): for `u ∈ L²(0, ∞)`
and `0 < α < 2`, the Gagliardo energy of the zero extension (restricted fractional Laplacian)
is at most half the energy of the odd extension (spectral Dirichlet fractional Laplacian). -/
theorem restricted_le_spectral {α : ℝ} (hα : FractionalExponent α) (u : L2IoiC) :
    gagliardoEnergyC α (extendByZeroIoiC u) ≤ 2⁻¹ * gagliardoEnergyC α (oddExtL2 u) := by
  set z : ℝ → ℂ := (Ioi (0 : ℝ)).indicator (u : ℝ → ℂ) with hz
  have hzm : Measurable z :=
    (Lp.stronglyMeasurable u).measurable.indicator measurableSet_Ioi
  have hzL2 : MemLp z 2 volume := memLp_indicator_IoiC u
  have hS : ∀ x ≤ 0, z x = 0 := fun x hx => by
    simp [hz, Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from not_lt.2 hx)]
  have e1 : gagliardoEnergyC α (extendByZeroIoiC u) = pairEnergy α z :=
    pairEnergy_congr_ae α (coeFn_extendByZeroIoiC u)
  have e2 : gagliardoEnergyC α (oddExtL2 u) = pairEnergy α (fun x => z x - z (-x)) := by
    refine pairEnergy_congr_ae α ?_
    rw [oddExtL2_apply]
    have a1 := Lp.coeFn_sub (extendByZeroIoiC u : L2C) (reflectL2 (extendByZeroIoiC u))
    have a2 := coeFn_reflectL2 (extendByZeroIoiC u)
    have a3 : (fun x : ℝ => (extendByZeroIoiC u : ℝ → ℂ) (-x)) =ᵐ[volume] fun x => z (-x) :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
        (coeFn_extendByZeroIoiC u)
    filter_upwards [a1, a2, a3, coeFn_extendByZeroIoiC u] with x b1 b2 b3 b4
    rw [b1, Pi.sub_apply, b2, b3, b4]
  rw [e1, e2]
  exact pairEnergy_le_half_odd hα hzm hzL2 hS

end

end FracLap
