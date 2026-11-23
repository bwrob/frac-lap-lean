/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.PointwiseEquivalence
public import FracLap.HalfLine.MaximumPrinciples
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# FracLapTest.PointwiseEquivalenceTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.WholeLine.PointwiseEquivalence`.
-/

namespace FracLapTest

open FracLap FourierTransform MeasureTheory
open scoped SchwartzMap

@[expose] public section

/-- A real smooth bump as a Schwartz function. -/
noncomputable def bumpSchwartz : 𝓢(ℝ, ℂ) :=
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  (b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp b.contDiff)

theorem bumpSchwartz_apply (x : ℝ) :
    (bumpSchwartz : ℝ → ℂ) x = (((⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)) x : ℝ) : ℂ)
    := rfl

/-- Consistency of the two definitions with the maximum principle: the Fourier integral
`∫ |2π ξ|^α 𝓕φ(ξ) dξ` of the bump `φ` (whose maximum is attained at `0`) is a nonnegative real,
because it equals the singular integral `(-Δ)^(α/2) φ (0) ≥ 0`. -/
example {α : ℝ} (hα : FractionalExponent α) :
    ∃ r : ℝ, 0 ≤ r ∧ (r : ℂ) = ∫ ξ : ℝ, ((|2 * Real.pi * ξ| ^ α : ℝ) : ℂ) *
      ((𝐞 (ξ * 0) : ℂ) * (𝓕 bumpSchwartz : 𝓢(ℝ, ℂ)) ξ) := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fracLapSecondDiff α (fun x => b x) 0, ?_, ?_⟩
  · refine fracLapSecondDiff_nonneg_of_isMax hα _ 0 fun z => ?_
    have h0 : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    rw [h0]
    exact b.le_one
  · exact fracLapSecondDiff_eq_fourier hα bumpSchwartz (u := fun x => b x)
      (fun x => bumpSchwartz_apply x) 0

/-- Full `L²` bridge on `bumpSchwartz`: `bumpSchwartz` belongs to the generator domain of
`fracLapSemigroup α`, its pointwise fractional Laplacian matches `𝓕⁻ (|2π ξ|^α 𝓕 φ)`, and agrees
a.e. with the negative generator `-(fracLapSemigroup α).generator bumpSchwartz`. -/
example {α : ℝ} (hα : FractionalExponent α) :
    (bumpSchwartz.toLp 2 volume : L2C) ∈ (fracLapSemigroup α).generatorDomain ∧
      (fun x : ℝ => (fracLapSecondDiff α (fun y =>
        (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)) y) x : ℂ)) =ᵐ[volume]
        ((-((fracLapSemigroup α).generator
          ⟨bumpSchwartz.toLp 2 volume,
            fracLapSemigroup_schwartz_mem_generatorDomain hα bumpSchwartz⟩) : L2C) :
            ℝ → ℂ) :=
  ⟨fracLapSemigroup_schwartz_mem_generatorDomain hα bumpSchwartz,
    fracLapSecondDiff_ae_eq_neg_generator hα bumpSchwartz (fun x => bumpSchwartz_apply x)⟩

/-- Exact closed-form evaluation of `prop:constantexplicit` at `α = 1`:
`∫ (1 - cos ω) / |ω|² dω = π` and `(∫ (1 - cos ω) / |ω|² dω)⁻¹ = C(1)`. -/
example : (∫ ω : ℝ, (1 - Real.cos ω) / |ω| ^ (1 + (1 : ℝ))) = Real.pi ∧
    fracLapConstant (1 : ℝ) = (∫ ω : ℝ, (1 - Real.cos ω) / |ω| ^ (1 + (1 : ℝ)))⁻¹ := by
  have hC1 : fracLapConstant (1 : ℝ) = Real.pi⁻¹ := by
    unfold fracLapConstant
    have h0 : (1 + (1 : ℝ)) / 2 = 1 := by norm_num
    have h1 : 1 - (1 : ℝ) / 2 = 1 / 2 := by norm_num
    have h2 : (1 : ℝ) - 1 = 0 := by norm_num
    rw [h0, h1, h2, Real.rpow_zero, Real.Gamma_one, Real.Gamma_one_half_eq]
    have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
    calc 1 * 1 * 1 / (Real.sqrt Real.pi * Real.sqrt Real.pi)
        = 1 / Real.pi := by rw [hsq]; ring
      _ = Real.pi⁻¹ := one_div _
  refine ⟨?_, fracLapConstant_eq_inv_integral_cos fractionalExponent_one⟩
  rw [integral_one_sub_cos_div_abs_rpow fractionalExponent_one, hC1, inv_inv]

open Classical in
/-- Strong `L²` endpoint limits (`cor:limit`) specialized to the real smooth bump `bumpSchwartz`. -/
example :
    Filter.Tendsto (fun α : ℝ =>
      if _hα : FractionalExponent α then
        MeasureTheory.eLpNorm (fun x : ℝ =>
          (fracLapSecondDiff α (fun y =>
            (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)) y) x : ℂ) -
            ((⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)) x : ℂ)) 2 volume
      else 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun α : ℝ =>
      if _hα : FractionalExponent α then
        MeasureTheory.eLpNorm (fun x : ℝ =>
          (fracLapSecondDiff α (fun y =>
            (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)) y) x : ℂ) +
            deriv (deriv (bumpSchwartz : ℝ → ℂ)) x) 2 volume
      else 0) (nhdsWithin 2 (Set.Iio 2)) (nhds 0) :=
  ⟨tendsto_fracLapSecondDiff_zero_L2 bumpSchwartz (fun x => bumpSchwartz_apply x),
    tendsto_fracLapSecondDiff_two_L2 bumpSchwartz (fun x => bumpSchwartz_apply x)⟩

/-- **Non-Schwartz instance of the general pointwise theorem.** The Fourier datum
`g = 1_{[-1,1]}` has `u(z) = ∫_{-1}^{1} 𝐞(ξ z) dξ` (a sinc function with only `1/|z|` decay), yet
`g` and `|2π ξ|^α g` are integrable, so the singular integral equals the Fourier multiplier. -/
example {α : ℝ} (hα : FractionalExponent α) (x : ℝ) :
    ((fracLapConstant α / 2 : ℝ) : ℂ) *
        ∫ y : ℝ, (2 * (∫ ξ : ℝ, (𝐞 (ξ * x) : ℂ) * (Set.Icc (-1 : ℝ) 1).indicator
              (fun _ => (1 : ℂ)) ξ) -
            (∫ ξ : ℝ, (𝐞 (ξ * (x + y)) : ℂ) * (Set.Icc (-1 : ℝ) 1).indicator
              (fun _ => (1 : ℂ)) ξ) -
            (∫ ξ : ℝ, (𝐞 (ξ * (x - y)) : ℂ) * (Set.Icc (-1 : ℝ) 1).indicator
              (fun _ => (1 : ℂ)) ξ)) / ((|y| ^ (1 + α) : ℝ) : ℂ) =
      ∫ ξ : ℝ, ((|2 * Real.pi * ξ| ^ α : ℝ) : ℂ) *
        ((𝐞 (ξ * x) : ℂ) * (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℂ)) ξ) := by
  refine fracLap_pointwise_eq_fourier_of_integrable hα
    (g := (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℂ)))
    (measurable_const.indicator measurableSet_Icc) ?_ ?_ (fun z => rfl) x
  · exact (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  · have hb : MeasureTheory.IntegrableOn (fun ξ : ℝ => |2 * Real.pi * ξ| ^ α)
        (Set.Icc (-1) 1) := by
      refine Continuous.integrableOn_Icc ?_
      exact (continuous_abs.comp (continuous_const.mul continuous_id)).rpow_const
        (fun _ => Or.inr hα.1.le)
    refine (hb.integrable_indicator measurableSet_Icc).congr
      (Filter.Eventually.of_forall fun ξ => ?_)
    by_cases h : ξ ∈ Set.Icc (-1 : ℝ) 1 <;> simp [Set.indicator, h]

end

end FracLapTest
