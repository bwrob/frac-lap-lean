/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.HalfLine.MaximumPrinciples

/-!
# FracLap.HalfLine.WholeLineMaximumPrinciple

The Constantin--Vicol nonlinear maximum principle on the whole line.

For `α ∈ (0, 2)` and a nonnegative integrable `u : ℝ → ℝ` with a positive global maximum at `x₀`
and integrable weighted second difference,
`(-Δ)^(α/2) u(x₀) ≥ c(α) u(x₀)^(1+α) / ‖u‖_{L¹}^α`, with the explicit constant
`wholeLineNlmpConstant α = (2C/α)^(1+α) / (2^(1+α) C^α)`, `C = fracLapConstant α`.

Unlike the reflected half-line version, no antiderivative or smooth cutoff is needed: a sharp
cutoff at radius `ρ` gives `(-Δ)^(α/2) u(x₀) ≥ (2C/α) u(x₀) ρ^(-α) - C ‖u‖₁ ρ^(-1-α)`, which is
optimized in `ρ` by `nlmp_scale_optimization`.
-/

namespace FracLap

open MeasureTheory Set Real

@[expose] public section

/-- Whole-line Constantin--Vicol constant `(2C/α)^(1+α) / (2^(1+α) C^α)`. -/
noncomputable def wholeLineNlmpConstant (α : ℝ) : ℝ :=
  (2 * fracLapConstant α / α) ^ (1 + α) / ((2 : ℝ) ^ (1 + α) * fracLapConstant α ^ α)

/-- The whole-line constant is positive for `α ∈ (0, 2)`. -/
theorem wholeLineNlmpConstant_pos {α : ℝ} (hα : FractionalExponent α) :
    0 < wholeLineNlmpConstant α := by
  have hC : 0 < fracLapConstant α := fracLapConstant_pos hα
  have h0 : 0 < α := hα.1
  unfold wholeLineNlmpConstant
  positivity

/-- **Sharp-cutoff lower bound.** For every cutoff radius `ρ > 0`,
`(2C/α) u(x₀) / ρ^α - C ‖u‖₁ / ρ^(1+α) ≤ (-Δ)^(α/2) u(x₀)`. -/
theorem fracLapSecondDiff_cutoff_bound {α : ℝ} (hα : FractionalExponent α) {u : ℝ → ℝ} {x₀ : ℝ}
    (hnonneg : ∀ x, 0 ≤ u x) (hmax : ∀ z, u z ≤ u x₀) (hint_u : Integrable u)
    (hint_fl : Integrable (fun y : ℝ => secondDiff u x₀ y / |y| ^ (1 + α))) {ρ : ℝ}
    (hρ : 0 < ρ) :
    (2 * fracLapConstant α / α) * u x₀ / ρ ^ α - fracLapConstant α * (∫ x, u x) / ρ ^ (1 + α) ≤
      fracLapSecondDiff α u x₀ := by
  have hC : 0 < fracLapConstant α := fracLapConstant_pos hα
  have h0 : 0 < α := hα.1
  set E : Set ℝ := Iio (-ρ) ∪ Ioi ρ with hE
  have hρ2 : 0 < ρ / 2 := by positivity
  have hEint : IntegrableOn (fun y : ℝ => 1 / |y| ^ (1 + α)) E := by
    have := integrableOn_inv_abs_rpow_exterior h0 hρ2
    rwa [show -2 * (ρ / 2) = -ρ by ring, show 2 * (ρ / 2) = ρ by ring] at this
  have hEval : (∫ y in E, 1 / |y| ^ (1 + α)) = 2 / (α * ρ ^ α) := by
    have := integral_inv_abs_rpow_exterior h0 hρ2
    rwa [show -2 * (ρ / 2) = -ρ by ring, show 2 * (ρ / 2) = ρ by ring] at this
  have hEmeas : MeasurableSet E := measurableSet_Iio.union measurableSet_Ioi
  -- the minorant `g`
  set k : ℝ := ρ ^ (-(1 + α)) with hk
  have hk0 : 0 ≤ k := Real.rpow_nonneg hρ.le _
  have hu1 : Integrable (fun y : ℝ => u (x₀ + y)) := hint_u.comp_add_left x₀
  have hu2 : Integrable (fun y : ℝ => u (x₀ - y)) := by
    simpa using (hint_u.comp_sub_left x₀)
  set g : ℝ → ℝ := fun y =>
    2 * u x₀ * E.indicator (fun y : ℝ => 1 / |y| ^ (1 + α)) y - k * (u (x₀ + y) + u (x₀ - y))
    with hg
  have hgint : Integrable g :=
    ((hEint.integrable_indicator hEmeas).const_mul (2 * u x₀)).sub ((hu1.add hu2).const_mul k)
  have hI : Integrable (fun y : ℝ => -(secondDiff u x₀ y / |y| ^ (1 + α))) := hint_fl.neg
  have hmono : ∀ y, g y ≤ -(secondDiff u x₀ y / |y| ^ (1 + α)) := by
    intro y
    have hmx1 := hmax (x₀ + y)
    have hmx2 := hmax (x₀ - y)
    have hn1 := hnonneg (x₀ + y)
    have hn2 := hnonneg (x₀ - y)
    have hden : 0 ≤ |y| ^ (1 + α) := by positivity
    by_cases hy : y ∈ E
    · have hyρ : ρ ≤ |y| := by
        rcases hy with hy | hy
        · rw [mem_Iio] at hy
          rw [abs_of_neg (by linarith)]
          linarith
        · rw [mem_Ioi] at hy
          rw [abs_of_pos (by linarith)]
          linarith
      have hypos : 0 < |y| ^ (1 + α) := by
        have : 0 < |y| := lt_of_lt_of_le hρ hyρ
        positivity
      have hkle : (1 : ℝ) / |y| ^ (1 + α) ≤ k := by
        rw [hk, Real.rpow_neg hρ.le, one_div]
        exact inv_anti₀ (by positivity) (Real.rpow_le_rpow hρ.le hyρ (by linarith))
      have hsum : 0 ≤ u (x₀ + y) + u (x₀ - y) := by linarith
      simp only [hg, Set.indicator_of_mem hy, secondDiff]
      have e : -((u (x₀ + y) + u (x₀ - y) - 2 * u x₀) / |y| ^ (1 + α)) =
          2 * u x₀ * (1 / |y| ^ (1 + α)) - (u (x₀ + y) + u (x₀ - y)) * (1 / |y| ^ (1 + α)) := by
        field_simp
        ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left hkle hsum]
    · simp only [hg, Set.indicator_of_notMem hy, mul_zero, zero_sub]
      have hnum : u (x₀ + y) + u (x₀ - y) - 2 * u x₀ ≤ 0 := by linarith
      have : 0 ≤ -((u (x₀ + y) + u (x₀ - y) - 2 * u x₀) / |y| ^ (1 + α)) :=
        neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hnum hden)
      have hsum : 0 ≤ k * (u (x₀ + y) + u (x₀ - y)) := mul_nonneg hk0 (by linarith)
      simp only [secondDiff]
      linarith
  have hgI : ∫ y, g y ≤ ∫ y, -(secondDiff u x₀ y / |y| ^ (1 + α)) :=
    integral_mono hgint hI hmono
  have hgval : ∫ y, g y =
      2 * u x₀ * (2 / (α * ρ ^ α)) - k * (2 * ∫ x, u x) := by
    have hind : ∫ y, E.indicator (fun y : ℝ => 1 / |y| ^ (1 + α)) y = 2 / (α * ρ ^ α) := by
      rw [integral_indicator hEmeas, hEval]
    have h1 : ∫ y : ℝ, u (x₀ + y) = ∫ x, u x := integral_add_left_eq_self (fun x => u x) x₀
    have h2 : ∫ y : ℝ, u (x₀ - y) = ∫ x, u x := by
      have := integral_sub_left_eq_self (fun x => u x) volume x₀
      simpa using this
    have hA : Integrable (fun y : ℝ =>
        2 * u x₀ * E.indicator (fun y : ℝ => 1 / |y| ^ (1 + α)) y) :=
      (hEint.integrable_indicator hEmeas).const_mul (2 * u x₀)
    have hB : Integrable (fun y : ℝ => k * (u (x₀ + y) + u (x₀ - y))) :=
      (hu1.add hu2).const_mul k
    have hS : ∫ y : ℝ, (u (x₀ + y) + u (x₀ - y)) = 2 * ∫ x, u x := by
      rw [integral_add hu1 hu2, h1, h2]; ring
    simp only [hg]
    rw [integral_sub hA hB, integral_const_mul, integral_const_mul, hind, hS]
  have hL : fracLapSecondDiff α u x₀ = fracLapConstant α / 2 *
      ∫ y, -(secondDiff u x₀ y / |y| ^ (1 + α)) := by
    unfold fracLapSecondDiff
    rw [integral_neg]; ring
  have hρα : ρ ^ (1 + α) = ρ * ρ ^ α := by
    rw [add_comm (1 : ℝ) α, Real.rpow_add_one hρ.ne']; ring
  have hkρ : k = 1 / (ρ * ρ ^ α) := by
    rw [hk, Real.rpow_neg hρ.le, ← hρα, one_div]
  have hρpos : 0 < ρ ^ α := Real.rpow_pos_of_pos hρ α
  rw [hL]
  have hmul := mul_le_mul_of_nonneg_left (hgval ▸ hgI) (by positivity : 0 ≤ fracLapConstant α / 2)
  refine le_trans (le_of_eq ?_) hmul
  rw [hkρ, hρα]
  field_simp

/-- **Whole-line Constantin--Vicol nonlinear maximum principle.** -/
theorem fracLapSecondDiff_nonlinear_max_principle {α : ℝ} (hα : FractionalExponent α)
    {u : ℝ → ℝ} {x₀ : ℝ} (hu₀ : 0 < u x₀) (hnonneg : ∀ x, 0 ≤ u x) (hmax : ∀ z, u z ≤ u x₀)
    (hint_u : Integrable u) (hM : 0 < ∫ x, u x)
    (hint_fl : Integrable (fun y : ℝ => secondDiff u x₀ y / |y| ^ (1 + α))) :
    wholeLineNlmpConstant α * (u x₀ ^ (1 + α) / (∫ x, u x) ^ α) ≤ fracLapSecondDiff α u x₀ := by
  have hC : 0 < fracLapConstant α := fracLapConstant_pos hα
  have h0 : 0 < α := hα.1
  have hC₁ : 0 < 2 * fracLapConstant α / α := by positivity
  have hρ := nlmpOptimalRadius_pos hC₁ hC hu₀ hM
  have hb := fracLapSecondDiff_cutoff_bound hα hnonneg hmax hint_u hint_fl hρ
  have ho := nlmp_scale_optimization (α := α) hC₁ hC hu₀ hM
  simp only at ho
  unfold wholeLineNlmpConstant
  linarith

/-- **Linear maximum principle at a global minimum** (Stinga--Torrea; the pointwise formula of
Silvestre): if `u` attains its global minimum at `x₀`, then `(-Δ)^(α/2) u(x₀) ≤ 0`. The second
difference at a minimum is nonnegative, so the integral is nonnegative; if the integral is not
integrable the Bochner integral is `0` and the statement still holds. -/
theorem fracLapSecondDiff_nonpos_of_isMin {α : ℝ} (hα : FractionalExponent α) (u : ℝ → ℝ)
    (x₀ : ℝ) (hmin : ∀ z : ℝ, u x₀ ≤ u z) : fracLapSecondDiff α u x₀ ≤ 0 := by
  unfold fracLapSecondDiff
  have hC := fracLapConstant_pos hα
  have hint : 0 ≤ ∫ y : ℝ, secondDiff u x₀ y / |y| ^ (1 + α) := by
    refine integral_nonneg fun y => ?_
    refine div_nonneg ?_ (by positivity)
    unfold secondDiff
    linarith [hmin (x₀ + y), hmin (x₀ - y)]
  have h2 : 0 ≤ fracLapConstant α / 2 := by positivity
  nlinarith

/-- **Zero-minimum form**: a nonnegative `f` vanishing at `x₀` has `(-Δ)^(α/2) f(x₀) ≤ 0`. -/
theorem fracLapSecondDiff_nonpos_of_zero_min {α : ℝ} (hα : FractionalExponent α) {f : ℝ → ℝ}
    (hf : ∀ z, 0 ≤ f z) {x₀ : ℝ} (h0 : f x₀ = 0) : fracLapSecondDiff α f x₀ ≤ 0 :=
  fracLapSecondDiff_nonpos_of_isMin hα f x₀ fun z => by rw [h0]; exact hf z

end

end FracLap
