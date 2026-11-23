/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.HalfLine.WholeLineMaximumPrinciple
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# FracLapTest.WholeLineMaximumPrincipleTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.HalfLine.WholeLineMaximumPrinciple`.
-/

namespace FracLapTest

open FracLap MeasureTheory Set

@[expose] public section

/-- `|y|^s` is integrable on `[-1, 1]` for `s > -1`. -/
theorem integrableOn_abs_rpow_Icc {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun y : ℝ => |y| ^ s) (Icc (-1) 1) := by
  have hpos : IntegrableOn (fun y : ℝ => |y| ^ s) (Ioc 0 1) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := s) hs).1
    refine this.congr_fun (fun y hy => ?_) measurableSet_Ioc
    simp only [abs_of_pos hy.1]
  have hneg : IntegrableOn (fun y : ℝ => |y| ^ s) (Ico (-1) 0) := by
    have h1 : IntegrableOn (fun y : ℝ => |-y| ^ s) (Neg.neg ⁻¹' Ioc 0 1) :=
      (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg _)
        (Homeomorph.neg ℝ).measurableEmbedding).mpr hpos
    have hpre : Neg.neg ⁻¹' Ioc (0 : ℝ) 1 = Ico (-1) 0 := by
      ext y
      simp only [mem_preimage, mem_Ioc, mem_Ico]
      exact ⟨fun h => ⟨by linarith [h.2], by linarith [h.1]⟩,
        fun h => ⟨by linarith [h.2], by linarith [h.1]⟩⟩
    rw [hpre] at h1
    simpa [abs_neg] using h1
  have hsub : Icc (-1 : ℝ) 1 ⊆ Ico (-1) 0 ∪ Ioc 0 1 ∪ {0} := by
    intro y hy
    rcases lt_trichotomy y 0 with h | h | h
    · exact Or.inl (Or.inl ⟨hy.1, h⟩)
    · exact Or.inr h
    · exact Or.inl (Or.inr ⟨h, hy.2⟩)
  exact ((hneg.union hpos).union (integrableOn_singleton (hx := by simp))).mono_set hsub

/-- The second difference of the Gaussian at the origin against `|y|^(-1-α)` is integrable. -/
theorem gaussian_secondDiff_integrable {α : ℝ} (hα : FractionalExponent α) :
    Integrable (fun y : ℝ =>
      secondDiff (fun x : ℝ => Real.exp (-(x ^ 2))) 0 y / |y| ^ (1 + α)) := by
  have h0 : 0 < α := hα.1
  have h2 : α < 2 := hα.2
  set A : Set ℝ := Icc (-1) 1 with hA
  have hAm : MeasurableSet A := measurableSet_Icc
  have hA1 : IntegrableOn (fun y : ℝ => 2 * |y| ^ (1 - α)) A :=
    (integrableOn_abs_rpow_Icc (by linarith)).const_mul 2
  have hmaj1 : Integrable (A.indicator (fun y : ℝ => 2 * |y| ^ (1 - α))) :=
    hA1.integrable_indicator hAm
  have hmaj2 : Integrable (Aᶜ.indicator (fun y : ℝ => 2 * (1 / |y| ^ (1 + α)))) := by
    have := integrableOn_inv_abs_rpow_exterior h0 (R := 1 / 2) (by norm_num)
    have hset : Iio (-2 * (1 / 2 : ℝ)) ∪ Ioi (2 * (1 / 2 : ℝ)) = Aᶜ := by
      ext y
      simp only [mem_union, mem_Iio, mem_Ioi, mem_compl_iff, hA, mem_Icc, not_and_or, not_le]
      constructor
      · rintro (h | h) <;> [left; right] <;> linarith
      · rintro (h | h) <;> [left; right] <;> linarith
    rw [hset] at this
    have h2' : IntegrableOn (fun y : ℝ => 2 * (1 / |y| ^ (1 + α))) Aᶜ := this.const_mul 2
    exact h2'.integrable_indicator hAm.compl
  refine (hmaj1.add hmaj2).mono' ?_ (ae_of_all _ fun y => ?_)
  · have : Measurable (fun y : ℝ =>
        secondDiff (fun x : ℝ => Real.exp (-(x ^ 2))) 0 y / |y| ^ (1 + α)) := by
      unfold secondDiff
      fun_prop
    exact this.aestronglyMeasurable
  · have hnum : secondDiff (fun x : ℝ => Real.exp (-(x ^ 2))) 0 y =
        2 * Real.exp (-(y ^ 2)) - 2 := by
      simp [secondDiff]; ring
    have hexp0 : 0 < Real.exp (-(y ^ 2)) := Real.exp_pos _
    have hexp1 : Real.exp (-(y ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg y]
    have hexp2 : 1 - y ^ 2 ≤ Real.exp (-(y ^ 2)) := by
      have := Real.add_one_le_exp (-(y ^ 2)); linarith
    have hden : 0 ≤ |y| ^ (1 + α) := by positivity
    rw [Real.norm_eq_abs, hnum]
    by_cases hy : y ∈ A
    · have hyc : y ∉ Aᶜ := by simpa using hy
      simp only [Pi.add_apply, Set.indicator_of_mem hy, Set.indicator_of_notMem hyc, add_zero]
      rcases eq_or_ne y 0 with h0y | hy0
      · have h00 : |(2 * Real.exp (-(y ^ 2)) - 2) / |y| ^ (1 + α)| = 0 := by
          subst h0y; simp
        rw [h00]; positivity
      · have hpos : 0 < |y| ^ (1 + α) := by positivity
        have e : |y| ^ (1 - α) = y ^ 2 / |y| ^ (1 + α) := by
          have : (1 - α) = 2 - (1 + α) := by ring
          rw [this, Real.rpow_sub (abs_pos.2 hy0), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast, sq_abs]
        rw [abs_div, abs_of_nonneg hden, e, ← mul_div_assoc,
          div_le_div_iff_of_pos_right hpos, abs_of_nonpos (by linarith)]
        linarith
    · simp only [Pi.add_apply, Set.indicator_of_notMem hy,
        Set.indicator_of_mem (show y ∈ Aᶜ from hy), zero_add]
      have hyA : 1 < |y| := by
        rw [hA, mem_Icc, not_and_or, not_le, not_le] at hy
        rcases hy with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have hpos : 0 < |y| ^ (1 + α) := by positivity
      rw [abs_div, abs_of_nonneg hden, mul_one_div, div_le_div_iff_of_pos_right hpos,
        abs_of_nonpos (by linarith)]
      linarith

/-- The whole-line principle applies to the Gaussian `u = exp (-x²)` at `x₀ = 0`: all
hypotheses are met, and the conclusion is a strictly positive lower bound for `(-Δ)^(α/2) u(0)`. -/
theorem gaussian_nonlinear_max_principle {α : ℝ} (hα : FractionalExponent α) :
    0 < wholeLineNlmpConstant α *
      (Real.exp (-((0 : ℝ) ^ 2)) ^ (1 + α) / (∫ x : ℝ, Real.exp (-(x ^ 2))) ^ α) ∧
    wholeLineNlmpConstant α *
      (Real.exp (-((0 : ℝ) ^ 2)) ^ (1 + α) / (∫ x : ℝ, Real.exp (-(x ^ 2))) ^ α) ≤
        fracLapSecondDiff α (fun x : ℝ => Real.exp (-(x ^ 2))) 0 := by
  have hM : 0 < ∫ x : ℝ, Real.exp (-(x ^ 2)) := by
    have h := integral_gaussian (1 : ℝ)
    simp only [neg_mul, one_mul] at h
    rw [h]; positivity
  have hint : Integrable (fun x : ℝ => Real.exp (-(x ^ 2))) := by
    refine (integrable_exp_neg_mul_sq (b := 1) one_pos).congr (ae_of_all _ fun x => ?_)
    ring_nf
  refine ⟨?_, ?_⟩
  · have := wholeLineNlmpConstant_pos hα
    have h1 : Real.exp (-((0 : ℝ) ^ 2)) = 1 := by norm_num
    rw [h1, Real.one_rpow]
    positivity
  · refine fracLapSecondDiff_nonlinear_max_principle hα (by simp) (fun x => (Real.exp_pos _).le)
      (fun z => ?_) hint hM (gaussian_secondDiff_integrable hα)
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg z])

/-- Zero-minimum principle at the origin for the nonnegative function `x ↦ x²`: the pointwise
operator there is `≤ 0` (it is in fact `0` by non-integrability of `|y|^(1-α)`, which the Bochner
integral reports as `0`). -/
example {α : ℝ} (hα : FractionalExponent α) : fracLapSecondDiff α (fun x => x ^ 2) 0 ≤ 0 :=
  fracLapSecondDiff_nonpos_of_zero_min hα (fun z => sq_nonneg z) (by simp)

/-- Maximum principle at the maximum of a Gaussian. -/
example {α : ℝ} (hα : FractionalExponent α) :
    0 ≤ fracLapSecondDiff α (fun x => Real.exp (-x ^ 2)) 0 :=
  fracLapSecondDiff_nonneg_of_isMax hα _ 0 fun z =>
    Real.exp_le_exp.2 (by simp; nlinarith [sq_nonneg z])

/-- Negative check: the minimum principle needs a *global* minimum. The function `x ↦ x` has no
minimum and `secondDiff` of an affine function vanishes, so the statement is not contradicted, but
the hypothesis `∀ z, u x₀ ≤ u z` fails for it at every point. -/
example (x₀ : ℝ) : ¬ ∀ z : ℝ, (fun x : ℝ => x) x₀ ≤ (fun x : ℝ => x) z := by
  intro h
  have := h (x₀ - 1)
  simp at this
  linarith

end

end FracLapTest
