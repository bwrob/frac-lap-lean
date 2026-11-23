/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.Bernstein

/-!
# FracLapTest.BernsteinTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.Tools.Bernstein`.
-/

namespace FracLapTest

open FracLap FourierTransform MeasureTheory Set Real
open scoped ENNReal

@[expose] public section

/-- The band `1 ≤ ξ ≤ 2` as an `L²` datum on the Fourier side. -/
noncomputable def bandDatum : L2C :=
  indicatorConstLp 2 (measurableSet_Icc : MeasurableSet (Icc (1 : ℝ) 2))
    (by simp) (1 : ℂ)

/-- A function whose Fourier transform is supported in `1 ≤ |ξ| ≤ 2`. -/
noncomputable def bandFunction : L2C := 𝓕⁻ bandDatum

theorem fourier_bandFunction_ae : ∀ᵐ ξ : ℝ,
    ((𝓕 bandFunction : L2C) : ℝ → ℂ) ξ = (Icc (1 : ℝ) 2).indicator (fun _ => (1 : ℂ)) ξ := by
  have h : 𝓕 bandFunction = bandDatum := by
    unfold bandFunction; exact fourier_fourierInv_eq bandDatum
  rw [h]
  exact indicatorConstLp_coeFn

/-- Two-sided Bernstein sandwich for the band `[1, 2]`:
`(2π)^α ‖f‖² ≤ E_α(f) ≤ (4π)^α ‖f‖²`. -/
example {α : ℝ} (hα : FractionalExponent α) :
    ENNReal.ofReal ((2 * π * 1) ^ α) * ‖bandFunction‖ₑ ^ (2 : ℝ) ≤ gagliardoEnergyC α bandFunction ∧
      gagliardoEnergyC α bandFunction ≤ ENNReal.ofReal ((2 * π * 2) ^ α) *
        ‖bandFunction‖ₑ ^ (2 : ℝ) := by
  refine ⟨bernstein_lower hα bandFunction zero_le_one ?_, bernstein_upper hα bandFunction ?_⟩
  · filter_upwards [fourier_bandFunction_ae] with ξ hξ hlt
    rw [hξ]
    have : ξ ∉ Icc (1 : ℝ) 2 := fun hm => by
      have := hm.1
      rw [abs_lt] at hlt; linarith [hlt.2]
    simp [this]
  · filter_upwards [fourier_bandFunction_ae] with ξ hξ hlt
    rw [hξ]
    have : ξ ∉ Icc (1 : ℝ) 2 := fun hm => by
      rw [abs_of_nonneg (by linarith [hm.1])] at hlt
      linarith [hm.2]
    simp [this]

end

end FracLapTest
