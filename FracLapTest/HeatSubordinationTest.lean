/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.HeatSubordination
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# FracLapTest.HeatSubordinationTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and sign consistency checks for
`FracLap.WholeLine.HeatSubordination`.
-/

namespace FracLapTest

open FracLap MeasureTheory Real
open scoped SchwartzMap

@[expose] public section

/-- Explicit evaluation of `inv_gamma_neg_half_eq_neg_levyConst` at `α = 1`:
`Γ(-1/2) = -2 √π` so `Γ(-1/2)⁻¹ = -1 / (2 √π)`. -/
example : (Real.Gamma (-(1 : ℝ) / 2))⁻¹ = -(1 / (2 * Real.sqrt Real.pi)) := by
  have h := inv_gamma_neg_half_eq_neg_levyConst fractionalExponent_one
  rw [h]
  unfold levyConst
  norm_num [Real.Gamma_one_half_eq]
  ring

/-- Negative witness: `Γ(-α / 2)` is strictly negative (never positive or zero) for `0 < α < 2`,
explaining why the subordination sign flips at a global maximum. -/
example {α : ℝ} (hα : FractionalExponent α) : ¬ 0 ≤ Real.Gamma (-α / 2) :=
  not_le.mpr (gamma_neg_half_neg hα)

/-- Real smooth bump function as a Schwartz element `𝓢(ℝ, ℝ)`. -/
noncomputable def bumpSchwartzReal : 𝓢(ℝ, ℝ) :=
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  b.hasCompactSupport.toSchwartzMap b.contDiff

/-- Spectral and physical heat subordination check on the real bump `bumpSchwartzReal` at `x = 0`
and frequency `ξ = (2π)⁻¹`. -/
example {α : ℝ} (hα : FractionalExponent α) :
    (1 : ℝ) = (Real.Gamma (-α / 2))⁻¹ *
      ∫ t in Set.Ioi (0 : ℝ), t ^ (-α / 2 - 1) * (Real.exp (-t * 1 ^ 2) - 1) ∧
    fracLapSecondDiff α bumpSchwartzReal 0 =
      (Real.Gamma (-α / 2))⁻¹ *
        ∫ t in Set.Ioi (0 : ℝ), t ^ (-α / 2 - 1) *
          (fracHeatConv gaussianHeatKernel t bumpSchwartzReal 0 - bumpSchwartzReal 0) := by
  refine ⟨?_, fracLapSecondDiff_eq_heat_subordination hα bumpSchwartzReal 0⟩
  have hsym := fracLapSymbol_eq_heat_subordination hα ((2 * Real.pi)⁻¹)
  have hpi : 2 * Real.pi * (2 * Real.pi)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  unfold fracLapSymbol at hsym
  rw [hpi, abs_one, Real.one_rpow] at hsym
  exact hsym

end

end FracLapTest
