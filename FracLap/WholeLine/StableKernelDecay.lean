/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.StableKernelTail

/-!
# FracLap.WholeLine.StableKernelDecay

The algebraic tail `|P_α(x, 1)| ≲ |x|^(-1-α)` of the stable kernel for every `0 < α < 2`, by a
second-difference version of the half-period shift trick:
if `x δ = π` and `Δ²g(ν) = g ν - 2 g (ν - δ) + g (ν - 2δ)`, then
`∫ g sin (x ·) = (1/4) ∫ Δ²g sin (x ·)`.

- `integral_sin_second_diff`: the identity above for integrable `g` on `ℝ`.
-/

namespace FracLap

open MeasureTheory Real Set Filter Topology

@[expose] public section

/-- An integrable function times a sine is integrable. -/
theorem integrable_mul_sin_real {g : ℝ → ℝ} (hg : Integrable g) (x : ℝ) :
    Integrable fun ν : ℝ => g ν * sin (x * ν) := by
  refine hg.norm.mono' (hg.aestronglyMeasurable.mul
    (by fun_prop : Continuous fun ν : ℝ => sin (x * ν)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ν => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (by simpa using abs_sin_le_one (x * ν))

/-- **Half-period shift on the line**: if `x δ = π` then
`∫ g sin (x ·) = - ∫ g (· - δ) sin (x ·)`. -/
theorem integral_sin_shift_real (g : ℝ → ℝ) {x δ : ℝ} (hxδ : x * δ = π) :
    ∫ ν : ℝ, g ν * sin (x * ν) = -∫ ν : ℝ, g (ν - δ) * sin (x * ν) := by
  rw [← integral_sub_right_eq_self (fun ν : ℝ => g ν * sin (x * ν)) δ, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ν => ?_)
  have hsin : sin (x * (ν - δ)) = -sin (x * ν) := by
    rw [mul_sub, hxδ, sin_sub_pi]
  simp only [hsin]
  ring

/-- **Second-difference identity**: for integrable `g` and `x δ = π`,
`∫ g sin (x ·) = (1/4) ∫ (g ν - 2 g (ν - δ) + g (ν - 2δ)) sin (x ν) dν`. -/
theorem integral_sin_second_diff {g : ℝ → ℝ} (hg : Integrable g) {x δ : ℝ} (hxδ : x * δ = π) :
    ∫ ν : ℝ, g ν * sin (x * ν) =
      (1 / 4) * ∫ ν : ℝ, (g ν - 2 * g (ν - δ) + g (ν - 2 * δ)) * sin (x * ν) := by
  have h1 : Integrable fun ν : ℝ => g (ν - δ) := hg.comp_sub_right δ
  have h2 : Integrable fun ν : ℝ => g (ν - δ - δ) := h1.comp_sub_right δ
  have e1 := integral_sin_shift_real g hxδ
  have e2 := integral_sin_shift_real (fun ν => g (ν - δ)) hxδ
  have hg' := integrable_mul_sin_real hg x
  have h1' := integrable_mul_sin_real h1 x
  have h2' := integrable_mul_sin_real h2 x
  have hsplit : ∫ ν : ℝ, (g ν - 2 * g (ν - δ) + g (ν - 2 * δ)) * sin (x * ν) =
      (∫ ν : ℝ, g ν * sin (x * ν)) - 2 * (∫ ν : ℝ, g (ν - δ) * sin (x * ν)) +
        ∫ ν : ℝ, g (ν - δ - δ) * sin (x * ν) := by
    calc ∫ ν : ℝ, (g ν - 2 * g (ν - δ) + g (ν - 2 * δ)) * sin (x * ν)
        = ∫ ν : ℝ, (g ν * sin (x * ν) - 2 * (g (ν - δ) * sin (x * ν)) +
            g (ν - δ - δ) * sin (x * ν)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ν => ?_)
          beta_reduce
          have : ν - 2 * δ = ν - δ - δ := by ring
          rw [this]
          ring
      _ = (∫ ν : ℝ, (g ν * sin (x * ν) - 2 * (g (ν - δ) * sin (x * ν)))) +
            ∫ ν : ℝ, g (ν - δ - δ) * sin (x * ν) :=
          integral_add (hg'.sub (h1'.const_mul 2)) h2'
      _ = _ := by
          rw [integral_sub hg' (h1'.const_mul 2), integral_const_mul]
  rw [hsplit]
  linarith

/-! ### Second differences of a `C²` function -/

/-- Mean value inequality on a closed interval with `HasDerivAt` data. -/
theorem abs_sub_le_of_hasDerivAt {f f' : ℝ → ℝ} {a b C : ℝ}
    (hf : ∀ w ∈ Icc a b, HasDerivAt f (f' w) w) (hC : ∀ w ∈ Icc a b, |f' w| ≤ C)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : |f y - f x| ≤ C * |y - x| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (s := Icc a b) (C := C) (fun w hw => (hf w hw).hasDerivWithinAt)
    (fun w hw => by simpa using hC w hw) (convex_Icc a b) hx hy
  simpa [Real.norm_eq_abs] using this

/-- **Second-difference bound**: if `f` is `C²` on `[a, b]` with `|f''| ≤ C`, and `a ≤ b - 2δ`,
then `|f b - 2 f (b - δ) + f (b - 2δ)| ≤ C δ²`. -/
theorem abs_second_diff_le {f f1 f2 : ℝ → ℝ} {a b δ C : ℝ} (hδ : 0 < δ) (hab : a ≤ b - 2 * δ)
    (hf : ∀ w ∈ Icc a b, HasDerivAt f (f1 w) w) (hf1 : ∀ w ∈ Icc a b, HasDerivAt f1 (f2 w) w)
    (hC : ∀ w ∈ Icc a b, |f2 w| ≤ C) :
    |f b - 2 * f (b - δ) + f (b - 2 * δ)| ≤ C * δ ^ 2 := by
  have hCnn : 0 ≤ C := (abs_nonneg _).trans (hC b ⟨by linarith, le_rfl⟩)
  -- derivative of `g u = f u - f (u - δ)` is `f1 u - f1 (u - δ)` on `[b - δ, b]`
  have hmem : ∀ u ∈ Icc (b - δ) b, u ∈ Icc a b ∧ u - δ ∈ Icc a b := by
    intro u hu
    refine ⟨⟨by linarith [hu.1], hu.2⟩, ⟨by linarith [hu.1], by linarith [hu.2]⟩⟩
  have hg : ∀ u ∈ Icc (b - δ) b,
      HasDerivAt (fun u => f u - f (u - δ)) (f1 u - f1 (u - δ)) u := by
    intro u hu
    obtain ⟨h1, h2⟩ := hmem u hu
    have hd := (hf (u - δ) h2).comp_sub_const u δ
    exact (hf u h1).sub hd
  have hbound : ∀ u ∈ Icc (b - δ) b, |f1 u - f1 (u - δ)| ≤ C * δ := by
    intro u hu
    obtain ⟨h1, h2⟩ := hmem u hu
    have hsub : Icc (u - δ) u ⊆ Icc a b := fun w hw => ⟨by linarith [h2.1, hw.1], by
      linarith [h1.2, hw.2]⟩
    have := abs_sub_le_of_hasDerivAt (f := f1) (f' := f2) (a := u - δ) (b := u) (C := C)
      (fun w hw => hf1 w (hsub hw)) (fun w hw => hC w (hsub hw))
      (x := u - δ) (y := u) ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩
    rw [show u - (u - δ) = δ by ring, abs_of_pos hδ] at this
    exact this
  have := abs_sub_le_of_hasDerivAt (f := fun u => f u - f (u - δ))
    (f' := fun u => f1 u - f1 (u - δ)) (a := b - δ) (b := b) (C := C * δ) hg hbound
    (x := b - δ) (y := b) ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩
  rw [show b - (b - δ) = δ by ring, abs_of_pos hδ] at this
  have e : f b - 2 * f (b - δ) + f (b - 2 * δ) =
      (f b - f (b - δ)) - (f (b - δ) - f (b - δ - δ)) := by
    rw [show b - δ - δ = b - 2 * δ by ring]
    ring
  rw [e]
  calc _ ≤ C * δ * δ := this
    _ = C * δ ^ 2 := by ring

/-! ### Derivatives of the density -/

/-- Derivative of `ω ↦ ω^p exp (-ω^α)` on `(0, ∞)`. -/
theorem hasDerivAt_rpow_mul_exp {α p ω : ℝ} (hω : 0 < ω) :
    HasDerivAt (fun ω : ℝ => ω ^ p * exp (-ω ^ α))
      (p * ω ^ (p - 1) * exp (-ω ^ α) - α * ω ^ (p + α - 1) * exp (-ω ^ α)) ω := by
  have h1 : HasDerivAt (fun ω : ℝ => ω ^ p) (p * ω ^ (p - 1)) ω :=
    Real.hasDerivAt_rpow_const (Or.inl hω.ne')
  have h2 := hasDerivAt_exp_neg_rpow (α := α) hω
  have h3 := h1.mul h2
  convert h3 using 1
  simp only [stableDensity]
  have : ω ^ (p + α - 1) = ω ^ p * ω ^ (α - 1) := by
    rw [← Real.rpow_add hω]
    ring_nf
  rw [this]
  ring

/-- First derivative of the density `k = stableDensity α`. -/
noncomputable def stableDensity1 (α ω : ℝ) : ℝ :=
  α * ((α - 1) * ω ^ (α - 1 - 1) * exp (-ω ^ α) - α * ω ^ (α - 1 + α - 1) * exp (-ω ^ α))

/-- Second derivative of the density `k = stableDensity α`. -/
noncomputable def stableDensity2 (α ω : ℝ) : ℝ :=
  α * ((α - 1) * ((α - 1 - 1) * ω ^ (α - 1 - 1 - 1) * exp (-ω ^ α) -
        α * ω ^ (α - 1 - 1 + α - 1) * exp (-ω ^ α)) -
    α * ((α - 1 + α - 1) * ω ^ (α - 1 + α - 1 - 1) * exp (-ω ^ α) -
        α * ω ^ (α - 1 + α - 1 + α - 1) * exp (-ω ^ α)))

/-- `k' = stableDensity1`. -/
theorem hasDerivAt_stableDensity {α ω : ℝ} (hω : 0 < ω) :
    HasDerivAt (stableDensity α) (stableDensity1 α ω) ω := by
  have h : HasDerivAt (fun y : ℝ => α * (y ^ (α - 1) * exp (-y ^ α)))
      (α * ((α - 1) * ω ^ (α - 1 - 1) * exp (-ω ^ α) -
        α * ω ^ (α - 1 + α - 1) * exp (-ω ^ α))) ω :=
    (hasDerivAt_rpow_mul_exp (α := α) (p := α - 1) hω).const_mul α
  have hfun : stableDensity α = fun y : ℝ => α * (y ^ (α - 1) * exp (-y ^ α)) := by
    ext y
    simp only [stableDensity]
    ring
  rw [hfun]
  exact h

/-- `k'' = stableDensity2`. -/
theorem hasDerivAt_stableDensity1 {α ω : ℝ} (hω : 0 < ω) :
    HasDerivAt (stableDensity1 α) (stableDensity2 α ω) ω := by
  have hA := (hasDerivAt_rpow_mul_exp (α := α) (p := α - 1 - 1) hω).const_mul (α - 1)
  have hB := (hasDerivAt_rpow_mul_exp (α := α) (p := α - 1 + α - 1) hω).const_mul α
  have h : HasDerivAt (fun y : ℝ => α * ((α - 1) * (y ^ (α - 1 - 1) * exp (-y ^ α)) -
      α * (y ^ (α - 1 + α - 1) * exp (-y ^ α)))) (stableDensity2 α ω) ω := by
    have := (hA.sub hB).const_mul α
    unfold stableDensity2
    exact this
  have hfun : stableDensity1 α = fun y : ℝ => α * ((α - 1) * (y ^ (α - 1 - 1) * exp (-y ^ α)) -
      α * (y ^ (α - 1 + α - 1) * exp (-y ^ α))) := by
    ext y
    simp only [stableDensity1]
    ring
  rw [hfun]
  exact h

/-- Closed form of the second derivative of the density. -/
theorem stableDensity2_eq {α ω : ℝ} (hω : 0 < ω) :
    stableDensity2 α ω = α * ω ^ (α - 3) * ((α - 1) * (α - 2) * exp (-ω ^ α) -
      ((α - 1) * α + α * (2 * α - 2)) * (ω ^ α * exp (-ω ^ α)) +
      α ^ 2 * (ω ^ α * ω ^ α * exp (-ω ^ α))) := by
  have e0 : ω ^ (α - 1 - 1 - 1) = ω ^ (α - 3) := by ring_nf
  have e1 : ω ^ (α - 1 - 1 + α - 1) = ω ^ (α - 3) * ω ^ α := by
    rw [← Real.rpow_add hω]
    ring_nf
  have e2 : ω ^ (α - 1 + α - 1 - 1) = ω ^ (α - 3) * ω ^ α := by
    rw [← Real.rpow_add hω]
    ring_nf
  have e3 : ω ^ (α - 1 + α - 1 + α - 1) = ω ^ (α - 3) * (ω ^ α * ω ^ α) := by
    rw [← Real.rpow_add hω, ← Real.rpow_add hω]
    ring_nf
  unfold stableDensity2
  rw [e0, e1, e2, e3]
  ring

/-- The constant in the second-derivative bound `|k''| ≤ K ω^(α-3)`. -/
noncomputable def stableK (α : ℝ) : ℝ :=
  α * (|(α - 1) * (α - 2)| + |(α - 1) * α + α * (2 * α - 2)| + 2 * α ^ 2)

/-- `|k''(ω)| ≤ K ω^(α-3)` for all `ω > 0`. -/
theorem abs_stableDensity2_le {α : ℝ} (hα : 0 < α) {ω : ℝ} (hω : 0 < ω) :
    |stableDensity2 α ω| ≤ stableK α * ω ^ (α - 3) := by
  rw [stableDensity2_eq hω]
  set y := ω ^ α with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg hω.le _
  set E := exp (-y) with hE
  have hE0 : 0 < E := exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hyE : y * E ≤ 1 := by
    have h1 : y + 1 ≤ exp y := add_one_le_exp y
    have h2 : exp (-y) * exp y = 1 := by rw [← exp_add]; simp
    calc y * E ≤ exp y * E := by gcongr; linarith
      _ = 1 := by rw [mul_comm, h2]
  have hyyE : y * y * E ≤ 2 := by
    have h1 : 1 + y + y ^ 2 / 2 ≤ exp y := quadratic_le_exp_of_nonneg hy0
    have h2 : exp (-y) * exp y = 1 := by rw [← exp_add]; simp
    have h3 : y * y ≤ 2 * exp y := by nlinarith [h1, hy0]
    calc y * y * E ≤ (2 * exp y) * E := mul_le_mul_of_nonneg_right h3 hE0.le
      _ = 2 * (exp (-y) * exp y) := by rw [hE]; ring
      _ = 2 := by rw [h2]; ring
  have hw : 0 < ω ^ (α - 3) := Real.rpow_pos_of_pos hω _
  set c0 := (α - 1) * (α - 2) with hc0
  set c1 := (α - 1) * α + α * (2 * α - 2) with hc1
  have hinner : |c0 * E - c1 * (y * E) + α ^ 2 * (y * y * E)| ≤
      |c0| + |c1| + 2 * α ^ 2 := by
    calc |c0 * E - c1 * (y * E) + α ^ 2 * (y * y * E)|
        ≤ |c0 * E - c1 * (y * E)| + |α ^ 2 * (y * y * E)| := abs_add_le _ _
      _ ≤ (|c0 * E| + |c1 * (y * E)|) + |α ^ 2 * (y * y * E)| := by
          gcongr; exact abs_sub _ _
      _ ≤ |c0| + |c1| + 2 * α ^ 2 := by
          have a1 : |c0 * E| ≤ |c0| := by
            rw [abs_mul, abs_of_pos hE0]
            exact mul_le_of_le_one_right (abs_nonneg _) hE1
          have a2 : |c1 * (y * E)| ≤ |c1| := by
            rw [abs_mul, abs_of_nonneg (mul_nonneg hy0 hE0.le)]
            exact mul_le_of_le_one_right (abs_nonneg _) hyE
          have a3 : |α ^ 2 * (y * y * E)| ≤ 2 * α ^ 2 := by
            rw [abs_mul, abs_of_nonneg (sq_nonneg α),
              abs_of_nonneg (mul_nonneg (mul_nonneg hy0 hy0) hE0.le)]
            nlinarith [sq_nonneg α]
          linarith
  rw [abs_mul, abs_mul, abs_of_pos hα, abs_of_pos hw]
  unfold stableK
  calc α * ω ^ (α - 3) * |c0 * E - c1 * (y * E) + α ^ 2 * (y * y * E)|
      ≤ α * ω ^ (α - 3) * (|c0| + |c1| + 2 * α ^ 2) := by gcongr
    _ = α * (|c0| + |c1| + 2 * α ^ 2) * ω ^ (α - 3) := by ring

/-! ### The density extended by zero, and its mass near the origin -/

/-- The density `k = stableDensity α` extended by `0` to the negative half-line. -/
noncomputable def stableDensity0 (α : ℝ) : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (stableDensity α)

/-- The extended density is integrable on `ℝ`. -/
theorem integrable_stableDensity0 {α : ℝ} (hα : 0 < α) : Integrable (stableDensity0 α) :=
  (integrable_indicator_iff measurableSet_Ioi).2 (integrableOn_stableDensity hα)

/-- The extended density is nonnegative. -/
theorem stableDensity0_nonneg {α : ℝ} (hα : 0 < α) (ν : ℝ) : 0 ≤ stableDensity0 α ν := by
  unfold stableDensity0
  by_cases h : ν ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem h]
    exact stableDensity_nonneg hα h
  · rw [indicator_of_notMem h]

/-- Translating an indicator-weighted integral over a left half-line. -/
theorem integral_Iic_shift (g : ℝ → ℝ) (c d : ℝ) :
    ∫ ν in Iic c, g (ν - d) = ∫ ν in Iic (c - d), g ν := by
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic,
    ← integral_sub_right_eq_self ((Iic (c - d)).indicator g) d]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ν => ?_)
  simp only [indicator, mem_Iic, sub_le_sub_iff_right]

/-- The mass of the extended density to the left of `c > 0`. -/
theorem integral_stableDensity0_Iic {α c : ℝ} (hα : 0 < α) (hc : 0 < c) :
    ∫ ν in Iic c, stableDensity0 α ν = 1 - exp (-c ^ α) := by
  unfold stableDensity0
  rw [setIntegral_indicator measurableSet_Ioi, Iic_inter_Ioi]
  exact integral_stableDensity_Ioc hα hc

/-- The mass to the left of `c ≤ c'` is monotone in `c`. -/
theorem integral_stableDensity0_Iic_mono {α c c' : ℝ} (hα : 0 < α) (hcc : c ≤ c') :
    ∫ ν in Iic c, stableDensity0 α ν ≤ ∫ ν in Iic c', stableDensity0 α ν := by
  refine setIntegral_mono_set (integrable_stableDensity0 hα).integrableOn
    (Filter.Eventually.of_forall fun ν => stableDensity0_nonneg hα ν)
    (Filter.Eventually.of_forall (Iic_subset_Iic.mpr hcc))

/-- `1 - exp (-c^α) ≤ c^α`. -/
theorem one_sub_exp_neg_le (y : ℝ) : 1 - exp (-y) ≤ y := by
  linarith [add_one_le_exp (-y)]

/-- The second difference of the extended density with step `δ`. -/
noncomputable def stableDensity0Δ2 (α δ ν : ℝ) : ℝ :=
  stableDensity0 α ν - 2 * stableDensity0 α (ν - δ) + stableDensity0 α (ν - 2 * δ)

/-- The second difference is integrable. -/
theorem integrable_stableDensity0Δ2 {α : ℝ} (hα : 0 < α) (δ : ℝ) :
    Integrable (stableDensity0Δ2 α δ) := by
  have h0 := integrable_stableDensity0 hα
  have h1 : Integrable fun ν : ℝ => stableDensity0 α (ν - δ) := h0.comp_sub_right δ
  have h2 : Integrable fun ν : ℝ => stableDensity0 α (ν - 2 * δ) := h0.comp_sub_right (2 * δ)
  exact (h0.sub (h1.const_mul 2)).add h2

/-- **Crude bound near the origin**: `∫_{ν ≤ 4δ} |Δ²k₀| ≤ 4 (4δ)^α`. -/
theorem integral_abs_Δ2_Iic_le {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) :
    ∫ ν in Iic (4 * δ), |stableDensity0Δ2 α δ ν| ≤ 4 * (4 * δ) ^ α := by
  have h0 := integrable_stableDensity0 hα
  have h1 : Integrable fun ν : ℝ => stableDensity0 α (ν - δ) := h0.comp_sub_right δ
  have h2 : Integrable fun ν : ℝ => stableDensity0 α (ν - 2 * δ) := h0.comp_sub_right (2 * δ)
  have hbound : ∀ ν : ℝ, |stableDensity0Δ2 α δ ν| ≤
      stableDensity0 α ν + 2 * stableDensity0 α (ν - δ) + stableDensity0 α (ν - 2 * δ) := by
    intro ν
    unfold stableDensity0Δ2
    have a := stableDensity0_nonneg hα ν
    have b := stableDensity0_nonneg hα (ν - δ)
    have c := stableDensity0_nonneg hα (ν - 2 * δ)
    rw [abs_le]
    constructor <;> linarith
  have hint : Integrable fun ν : ℝ =>
      stableDensity0 α ν + 2 * stableDensity0 α (ν - δ) + stableDensity0 α (ν - 2 * δ) :=
    (h0.add (h1.const_mul 2)).add h2
  have hle := setIntegral_mono_on (s := Iic (4 * δ))
    (integrable_stableDensity0Δ2 hα δ).abs.integrableOn hint.integrableOn measurableSet_Iic
    (fun ν _ => hbound ν)
  refine hle.trans ?_
  have i0 : IntegrableOn (stableDensity0 α) (Iic (4 * δ)) := h0.integrableOn
  have i1 : IntegrableOn (fun ν : ℝ => 2 * stableDensity0 α (ν - δ)) (Iic (4 * δ)) :=
    (h1.const_mul 2).integrableOn
  have i2 : IntegrableOn (fun ν : ℝ => stableDensity0 α (ν - 2 * δ)) (Iic (4 * δ)) :=
    h2.integrableOn
  have i01 : IntegrableOn (fun ν : ℝ => stableDensity0 α ν + 2 * stableDensity0 α (ν - δ))
      (Iic (4 * δ)) := i0.add i1
  rw [integral_add i01 i2, integral_add i0 i1, integral_const_mul,
    integral_Iic_shift (stableDensity0 α) (4 * δ) δ,
    integral_Iic_shift (stableDensity0 α) (4 * δ) (2 * δ)]
  have hm : 1 - exp (-(4 * δ) ^ α) ≤ (4 * δ) ^ α := one_sub_exp_neg_le _
  have e0 := integral_stableDensity0_Iic (α := α) hα (by positivity : 0 < 4 * δ)
  have e1 : ∫ ν in Iic (4 * δ - δ), stableDensity0 α ν ≤ ∫ ν in Iic (4 * δ), stableDensity0 α ν :=
    integral_stableDensity0_Iic_mono hα (by linarith)
  have e2 : ∫ ν in Iic (4 * δ - 2 * δ), stableDensity0 α ν ≤
      ∫ ν in Iic (4 * δ), stableDensity0 α ν :=
    integral_stableDensity0_Iic_mono hα (by linarith)
  rw [e0] at e1 e2
  linarith

/-- The constant `K` of the second-derivative bound is nonnegative. -/
theorem stableK_nonneg {α : ℝ} (hα : 0 < α) : 0 ≤ stableK α := by
  unfold stableK
  positivity

/-- **Pointwise second-difference bound away from the origin**: for `ν > 4δ`,
`|Δ²k₀(ν)| ≤ K δ² (ν / 2)^(α-3)`. -/
theorem abs_Δ2_le_of_gt {α δ ν : ℝ} (hα : 0 < α) (hα2 : α < 2) (hδ : 0 < δ) (hν : 4 * δ < ν) :
    |stableDensity0Δ2 α δ ν| ≤ stableK α * δ ^ 2 * (ν / 2) ^ (α - 3) := by
  have ha : 0 < ν - 2 * δ := by linarith
  have hpos : ∀ w : ℝ, ν - 2 * δ ≤ w → 0 < w := fun w hw => lt_of_lt_of_le ha hw
  have h0 : stableDensity0 α ν = stableDensity α ν := indicator_of_mem (mem_Ioi.2 (hpos ν (by
    linarith))) _
  have h1 : stableDensity0 α (ν - δ) = stableDensity α (ν - δ) :=
    indicator_of_mem (mem_Ioi.2 (hpos _ (by linarith))) _
  have h2 : stableDensity0 α (ν - 2 * δ) = stableDensity α (ν - 2 * δ) :=
    indicator_of_mem (mem_Ioi.2 ha) _
  unfold stableDensity0Δ2
  rw [h0, h1, h2]
  have hK := stableK_nonneg hα
  have hbound :
      ∀ w ∈ Icc (ν - 2 * δ) ν, |stableDensity2 α w| ≤ stableK α * (ν - 2 * δ) ^ (α - 3) := by
    intro w hw
    have hw0 : 0 < w := hpos w hw.1
    exact (abs_stableDensity2_le hα hw0).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hw.1 (by linarith)) hK)
  have hmain := abs_second_diff_le (f := stableDensity α) (f1 := stableDensity1 α)
    (f2 := stableDensity2 α) (a := ν - 2 * δ) (b := ν) (δ := δ)
    (C := stableK α * (ν - 2 * δ) ^ (α - 3)) hδ (by linarith)
    (fun w hw => hasDerivAt_stableDensity (hpos w hw.1))
    (fun w hw => hasDerivAt_stableDensity1 (hpos w hw.1)) hbound
  refine hmain.trans ?_
  have hle : (ν - 2 * δ) ^ (α - 3) ≤ (ν / 2) ^ (α - 3) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  calc stableK α * (ν - 2 * δ) ^ (α - 3) * δ ^ 2 ≤ stableK α * (ν / 2) ^ (α - 3) * δ ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hK) (sq_nonneg δ)
    _ = stableK α * δ ^ 2 * (ν / 2) ^ (α - 3) := by ring

/-! ### Full tail bound on `|Δ²k₀|` and algebraic kernel decay for `0 < α < 2` -/

/-- Integrable upper bound on `(4δ, ∞)`:
`∫_{ν > 4δ} |Δ²k₀(ν)| dν ≤ K δ² 2^(3-α) (4δ)^(α-2) / (2 - α)`. -/
theorem integral_abs_Δ2_Ioi_le {α δ : ℝ} (hα : 0 < α) (hα2 : α < 2) (hδ : 0 < δ) :
    ∫ ν in Ioi (4 * δ), |stableDensity0Δ2 α δ ν| ≤
      stableK α * δ ^ 2 * (2 ^ (3 - α) * (4 * δ) ^ (α - 2) / (2 - α)) := by
  have h4δ : 0 < 4 * δ := by positivity
  have hlt : α - 3 < -1 := by linarith
  have hdom_eq : ∀ ν : ℝ, 0 < ν → (ν / 2) ^ (α - 3) = 2 ^ (3 - α) * ν ^ (α - 3) := by
    intro ν hν
    rw [div_rpow hν.le zero_le_two, div_eq_mul_inv, ← Real.rpow_neg zero_le_two]
    have hexp : -(α - 3) = 3 - α := by ring
    rw [hexp, mul_comm]
  have hrpow : IntegrableOn (fun ν : ℝ => ν ^ (α - 3)) (Ioi (4 * δ)) :=
    integrableOn_Ioi_rpow_of_lt hlt h4δ
  have hmul_int :
      IntegrableOn (fun ν : ℝ => (stableK α * δ ^ 2 * 2 ^ (3 - α)) * ν ^ (α - 3))
        (Ioi (4 * δ)) :=
    hrpow.const_mul _
  have hle :
      ∫ ν in Ioi (4 * δ), |stableDensity0Δ2 α δ ν| ≤
        ∫ ν in Ioi (4 * δ), (stableK α * δ ^ 2 * 2 ^ (3 - α)) * ν ^ (α - 3) := by
    refine setIntegral_mono_on (integrable_stableDensity0Δ2 hα δ).abs.integrableOn hmul_int
      measurableSet_Ioi fun ν hν => ?_
    have hν0 : 0 < ν := h4δ.trans hν
    have h1 := abs_Δ2_le_of_gt hα hα2 hδ hν
    rw [hdom_eq ν hν0] at h1
    linarith
  have hint_val :
      (∫ ν in Ioi (4 * δ), (stableK α * δ ^ 2 * 2 ^ (3 - α)) * ν ^ (α - 3)) =
        stableK α * δ ^ 2 * (2 ^ (3 - α) * (4 * δ) ^ (α - 2) / (2 - α)) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt h4δ]
    have hexp : α - 3 + 1 = α - 2 := by ring
    rw [hexp]
    have hneg : -(4 * δ) ^ (α - 2) / (α - 2) = (4 * δ) ^ (α - 2) / (2 - α) := by
      have h2m : 2 - α = -(α - 2) := by ring
      rw [h2m, div_neg, neg_div]
    rw [hneg]
    ring
  exact hle.trans_eq hint_val

/-- Tail prefactor `B(α) = 4^(1 + α) + K(α) 2^(3 - α) 4^(α - 2) / (2 - α)`. -/
noncomputable def stableTailB (α : ℝ) : ℝ :=
  4 * (4 : ℝ) ^ α + stableK α * (2 : ℝ) ^ (3 - α) * (4 : ℝ) ^ (α - 2) / (2 - α)

/-- `stableTailB α > 0` for `0 < α < 2`. -/
theorem stableTailB_pos {α : ℝ} (hα : 0 < α) (hα2 : α < 2) : 0 < stableTailB α := by
  unfold stableTailB
  have h1 : 0 < 4 * (4 : ℝ) ^ α := by positivity
  have hK : 0 ≤ stableK α := stableK_nonneg hα
  have h2 : 0 ≤ stableK α * (2 : ℝ) ^ (3 - α) * (4 : ℝ) ^ (α - 2) / (2 - α) := by
    have hden : 0 < 2 - α := by linarith
    positivity
  linarith

/-- Total second-difference `L¹` bound: `∫_ℝ |Δ²k₀(ν)| dν ≤ stableTailB α * δ^α`. -/
theorem integral_abs_Δ2_le {α δ : ℝ} (hα : 0 < α) (hα2 : α < 2) (hδ : 0 < δ) :
    ∫ ν : ℝ, |stableDensity0Δ2 α δ ν| ≤ stableTailB α * δ ^ α := by
  have hint : Integrable (fun ν : ℝ => |stableDensity0Δ2 α δ ν|) :=
    (integrable_stableDensity0Δ2 hα δ).abs
  have hsplit :
      ∫ ν : ℝ, |stableDensity0Δ2 α δ ν| =
        (∫ ν in Iic (4 * δ), |stableDensity0Δ2 α δ ν|) +
          ∫ ν in Ioi (4 * δ), |stableDensity0Δ2 α δ ν| := by
    have h := (integral_add_compl (measurableSet_Iic (a := 4 * δ)) hint).symm
    rw [compl_Iic] at h
    exact h
  have h1 := integral_abs_Δ2_Iic_le hα hδ
  have h2 := integral_abs_Δ2_Ioi_le hα hα2 hδ
  have hpow1 : (4 * δ) ^ α = (4 : ℝ) ^ α * δ ^ α := mul_rpow (by norm_num) hδ.le
  have hpow2 : δ ^ 2 * (4 * δ) ^ (α - 2) = (4 : ℝ) ^ (α - 2) * δ ^ α := by
    have hδsq : δ ^ 2 * δ ^ (α - 2) = δ ^ α := by
      rw [← Real.rpow_natCast δ 2, ← Real.rpow_add hδ]
      congr 1
      norm_num
    calc
      δ ^ 2 * (4 * δ) ^ (α - 2) = δ ^ 2 * ((4 : ℝ) ^ (α - 2) * δ ^ (α - 2)) := by
        rw [mul_rpow (by norm_num) hδ.le]
      _ = (4 : ℝ) ^ (α - 2) * (δ ^ 2 * δ ^ (α - 2)) := by ring
      _ = (4 : ℝ) ^ (α - 2) * δ ^ α := by rw [hδsq]
  rw [hsplit]
  calc
    (∫ ν in Iic (4 * δ), |stableDensity0Δ2 α δ ν|) +
        ∫ ν in Ioi (4 * δ), |stableDensity0Δ2 α δ ν|
        ≤ 4 * (4 * δ) ^ α +
          stableK α * δ ^ 2 * (2 ^ (3 - α) * (4 * δ) ^ (α - 2) / (2 - α)) := add_le_add h1 h2
    _ = 4 * (4 * δ) ^ α +
          (stableK α * (2 : ℝ) ^ (3 - α) / (2 - α)) * (δ ^ 2 * (4 * δ) ^ (α - 2)) := by ring
    _ = 4 * ((4 : ℝ) ^ α * δ ^ α) +
          (stableK α * (2 : ℝ) ^ (3 - α) / (2 - α)) * ((4 : ℝ) ^ (α - 2) * δ ^ α) := by
        rw [hpow1, hpow2]
    _ = stableTailB α * δ ^ α := by
          unfold stableTailB
          ring

/-- **Algebraic tail bound for `P_α(x, 1)` for all `0 < α < 2` and `x > 0`**:
`|P_α(x, 1)| ≤ (stableTailB α / 4) * π^(α - 1) * x^(-1 - α)`. -/
theorem abs_stableKernel_one_le_rpow {α x : ℝ} (hα : 0 < α) (hα2 : α < 2) (hx : 0 < x) :
    |stableKernel α x 1| ≤ (stableTailB α / 4) * π ^ (α - 1) * x ^ (-1 - α) := by
  set δ := π / x
  have hδ : 0 < δ := div_pos pi_pos hx
  have hxδ : x * δ = π := by
    dsimp only [δ]
    field_simp
  have hsin_eq :
      (∫ ω in Ioi (0 : ℝ), stableDensity α ω * sin (x * ω)) =
        ∫ ν : ℝ, stableDensity0 α ν * sin (x * ν) := by
    rw [← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ν => ?_)
    by_cases h : ν ∈ Ioi (0 : ℝ)
    · simp only [stableDensity0, indicator_of_mem h]
    · simp only [stableDensity0, indicator_of_notMem h, zero_mul]
  have hdiff_eq :
      (∫ ν : ℝ, stableDensity0 α ν * sin (x * ν)) =
        (1 / 4) * ∫ ν : ℝ, stableDensity0Δ2 α δ ν * sin (x * ν) := by
    simpa only [stableDensity0Δ2] using integral_sin_second_diff (integrable_stableDensity0 hα) hxδ
  have hint_sin :
      |∫ ν : ℝ, stableDensity0Δ2 α δ ν * sin (x * ν)| ≤
        ∫ ν : ℝ, |stableDensity0Δ2 α δ ν| := by
    have hnorm :
        ‖∫ ν : ℝ, stableDensity0Δ2 α δ ν * sin (x * ν)‖ ≤
          ∫ ν : ℝ, ‖stableDensity0Δ2 α δ ν * sin (x * ν)‖ :=
      norm_integral_le_integral_norm _
    have hle :
        (∫ ν : ℝ, ‖stableDensity0Δ2 α δ ν * sin (x * ν)‖) ≤
          ∫ ν : ℝ, |stableDensity0Δ2 α δ ν| := by
      refine integral_mono (integrable_mul_sin_real (integrable_stableDensity0Δ2 hα δ) x).norm
        (integrable_stableDensity0Δ2 hα δ).abs fun ν => ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)
    simpa only [Real.norm_eq_abs] using hnorm.trans hle
  have hP :
      |stableKernel α x 1| ≤ π⁻¹ * x⁻¹ * ((1 / 4) * (stableTailB α * δ ^ α)) := by
    unfold stableKernel
    simp only [neg_mul, one_mul]
    rw [integral_exp_neg_rpow_mul_cos hα hx, hsin_eq, hdiff_eq]
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr pi_pos),
      abs_of_pos (inv_pos.mpr hx), abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    have hcomb := hint_sin.trans (integral_abs_Δ2_le hα hα2 hδ)
    have hpre : 0 ≤ π⁻¹ * x⁻¹ * (1 / 4) := by positivity
    calc
      π⁻¹ * (x⁻¹ * (1 / 4 * |∫ ν : ℝ, stableDensity0Δ2 α δ ν * sin (x * ν)|))
          = (π⁻¹ * x⁻¹ * (1 / 4)) * |∫ ν : ℝ, stableDensity0Δ2 α δ ν * sin (x * ν)| := by ring
      _ ≤ (π⁻¹ * x⁻¹ * (1 / 4)) * (stableTailB α * δ ^ α) :=
          mul_le_mul_of_nonneg_left hcomb hpre
      _ = π⁻¹ * x⁻¹ * ((1 / 4) * (stableTailB α * δ ^ α)) := by ring
  have hpow : π⁻¹ * x⁻¹ * (π / x) ^ α = π ^ (α - 1) * x ^ (-1 - α) := by
    rw [div_rpow pi_pos.le hx.le, div_eq_mul_inv]
    have hπ : π⁻¹ * π ^ α = π ^ (α - 1) := by
      rw [← rpow_neg_one, ← rpow_add pi_pos]
      ring_nf
    have hxpow : x⁻¹ * (x ^ α)⁻¹ = x ^ (-1 - α) := by
      rw [← rpow_neg_one, ← rpow_neg hx.le, ← rpow_add hx]
      ring_nf
    calc
      π⁻¹ * x⁻¹ * (π ^ α * (x ^ α)⁻¹) = (π⁻¹ * π ^ α) * (x⁻¹ * (x ^ α)⁻¹) := by ring
      _ = π ^ (α - 1) * x ^ (-1 - α) := by rw [hπ, hxpow]
  refine hP.trans_eq ?_
  calc
    π⁻¹ * x⁻¹ * ((1 / 4) * (stableTailB α * δ ^ α))
        = (stableTailB α / 4) * (π⁻¹ * x⁻¹ * (π / x) ^ α) := by ring
    _ = (stableTailB α / 4) * π ^ (α - 1) * x ^ (-1 - α) := by
        rw [hpow]
        ring

/-- Explicit unit-time decay constant `C(α) > 0` for `stableKernel α · 1` on `ℝ` (`0 < α < 2`). -/
noncomputable def stableDecayConst (α : ℝ) : ℝ :=
  2 ^ (1 + α) *
    (π⁻¹ * (∫ ω in Ioi (0 : ℝ), exp (-ω ^ α)) + (stableTailB α / 4) * π ^ (α - 1))

/-- Strict positivity of `stableDecayConst α` for `0 < α < 2`. -/
theorem stableDecayConst_pos {α : ℝ} (hα : 0 < α) (hα2 : α < 2) :
    0 < stableDecayConst α := by
  unfold stableDecayConst
  have hint : 0 ≤ π⁻¹ * ∫ ω in Ioi (0 : ℝ), exp (-ω ^ α) :=
    mul_nonneg (inv_pos.mpr pi_pos).le (integral_nonneg fun _ => (exp_pos _).le)
  have hB : 0 < (stableTailB α / 4) * π ^ (α - 1) :=
    mul_pos (div_pos (stableTailB_pos hα hα2) (by norm_num)) (rpow_pos_of_pos pi_pos _)
  have h2 : 0 < (2 : ℝ) ^ (1 + α) := by positivity
  exact mul_pos h2 (by linarith)

/-- **Unit-time algebraic decay bound for all `0 < α < 2`**:
`stableKernel α x 1 ≤ stableDecayConst α / (1 + |x|) ^ (1 + α)` for every `x : ℝ`. -/
theorem stableKernel_decay_unit_time {α : ℝ} (hα : 0 < α) (hα2 : α < 2) (x : ℝ) :
    stableKernel α x 1 ≤ stableDecayConst α / (1 + |x|) ^ (1 + α) := by
  set M₀ := π⁻¹ * ∫ ω in Ioi (0 : ℝ), exp (-ω ^ α)
  set M₁ := (stableTailB α / 4) * π ^ (α - 1)
  have hM₀_nn : 0 ≤ M₀ :=
    mul_nonneg (inv_pos.mpr pi_pos).le (integral_nonneg fun _ => (exp_pos _).le)
  have hM₁_nn : 0 ≤ M₁ :=
    mul_nonneg (div_nonneg (stableTailB_pos hα hα2).le (by norm_num))
      (rpow_pos_of_pos pi_pos _).le
  have h1a : 0 ≤ 1 + α := by linarith
  by_cases hx : |x| ≤ 1
  · have hP : stableKernel α x 1 ≤ M₀ := by
      refine (le_abs_self _).trans ?_
      simpa only [M₀, neg_mul, one_mul] using abs_stableKernel_le hα x one_pos
    have hpow : (1 + |x|) ^ (1 + α) ≤ (2 : ℝ) ^ (1 + α) :=
      rpow_le_rpow (by positivity) (by linarith) h1a
    have hC_ge : M₀ * (1 + |x|) ^ (1 + α) ≤ stableDecayConst α := by
      unfold stableDecayConst
      calc
        M₀ * (1 + |x|) ^ (1 + α) ≤ M₀ * (2 : ℝ) ^ (1 + α) :=
          mul_le_mul_of_nonneg_left hpow hM₀_nn
        _ ≤ (M₀ + M₁) * (2 : ℝ) ^ (1 + α) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = 2 ^ (1 + α) * (M₀ + M₁) := by ring
    have hden : 0 < (1 + |x|) ^ (1 + α) := by positivity
    rw [le_div_iff₀ hden]
    exact (mul_le_mul_of_nonneg_right hP hden.le).trans hC_ge
  · have hxgt : 1 < |x| := lt_of_not_ge hx
    have hxpos : 0 < |x| := by linarith
    have hP : stableKernel α x 1 ≤ M₁ * |x| ^ (-1 - α) := by
      have heq : stableKernel α x 1 = stableKernel α |x| 1 := by
        rcases abs_choice x with h | h
        · rw [h]
        · rw [h, stableKernel_neg]
      rw [heq]
      exact (le_abs_self _).trans (abs_stableKernel_one_le_rpow hα hα2 hxpos)
    have hsum : 1 + |x| ≤ 2 * |x| := by linarith
    have hpow : (1 + |x|) ^ (1 + α) ≤ (2 : ℝ) ^ (1 + α) * |x| ^ (1 + α) := by
      calc
        (1 + |x|) ^ (1 + α) ≤ (2 * |x|) ^ (1 + α) :=
          rpow_le_rpow (by positivity) hsum h1a
        _ = (2 : ℝ) ^ (1 + α) * |x| ^ (1 + α) := mul_rpow (by norm_num) hxpos.le
    have hcancel : |x| ^ (-1 - α) * |x| ^ (1 + α) = 1 := by
      rw [← rpow_add hxpos]
      have h0 : (-1 - α) + (1 + α) = 0 := by ring
      rw [h0, rpow_zero]
    have hden : 0 < (1 + |x|) ^ (1 + α) := by positivity
    rw [le_div_iff₀ hden]
    calc
      stableKernel α x 1 * (1 + |x|) ^ (1 + α)
          ≤ (M₁ * |x| ^ (-1 - α)) * ((2 : ℝ) ^ (1 + α) * |x| ^ (1 + α)) :=
        mul_le_mul hP hpow hden.le (mul_nonneg hM₁_nn (rpow_nonneg hxpos.le _))
      _ = 2 ^ (1 + α) * M₁ * (|x| ^ (-1 - α) * |x| ^ (1 + α)) := by ring
      _ = 2 ^ (1 + α) * M₁ := by rw [hcancel, mul_one]
      _ ≤ 2 ^ (1 + α) * (M₀ + M₁) := by
          have h2nn : 0 ≤ (2 : ℝ) ^ (1 + α) := by positivity
          exact mul_le_mul_of_nonneg_left (by linarith) h2nn

end

end FracLap
