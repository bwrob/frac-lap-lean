/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.FourierSemigroup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLapTest.FourierSemigroupTest

High-signal tests for the concrete `L²(ℝ; ℂ)` Fourier multiplier semigroup and resolvent
construction in `FracLap.WholeLine.FourierSemigroup`:
1. Concrete non-zero `L²(ℝ; ℂ)` vector (`unitBoxL2 := 1_{[0, 1]}`) with unit norm.
2. Exact multiplier identity check and semigroup evaluation properties (`t = 0`,
   semigroup composition, and contraction bounds) for `fracLapSemigroup 1` and
   `fracLapSemigroup 2`.
3. Exact Hille–Yosida round-trip identities `(fracLapResolvent α).generatedSemigroup =
   fracLapSemigroup α` and `(fracLapSemigroup α).resolvent μ = (fracLapResolvent α).operator μ`.
4. Non-triviality / non-vacuity check: `fracLapSemigroup 1 1 (𝓕⁻ unitBoxL2) ≠ 𝓕⁻ unitBoxL2`
   (ruling out degenerate identity semigroups).
-/

@[expose] public section

namespace FracLapTest

open Complex Filter FourierTransform FracLap MeasureTheory Real Set
open scoped ENNReal NNReal

section

/-- Concrete unit-norm `L²(ℝ; ℂ)` test function: indicator of `[0, 1]`. -/
noncomputable def unitBoxL2 : L2C :=
  indicatorConstLp (2 : ℝ≥0∞) (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) 1))
    (by simp) (1 : ℂ)

/-- The concrete `unitBoxL2` vector has norm `1`. -/
theorem norm_unitBoxL2 : ‖unitBoxL2‖ = 1 := by
  rw [unitBoxL2, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp

/-- Constant symbol `1` acts as the identity Fourier multiplier on `unitBoxL2`. -/
theorem fourierMultiplier_one_unitBoxL2 :
    fourierMultiplier
        (toLpTop (m := fun _ : ℝ => (1 : ℂ)) aestronglyMeasurable_const zero_le_one
          (fun _ : ℝ => by norm_num))
        unitBoxL2 =
      unitBoxL2 := by
  rw [fourierMultiplier_one, ContinuousLinearMap.id_apply]

/-- Time-zero evaluation of `fracLapSemigroup` fixes `unitBoxL2`. -/
theorem fracLapSemigroup_zero_unitBoxL2 (α : ℝ) :
    fracLapSemigroup α 0 unitBoxL2 = unitBoxL2 :=
  (fracLapSemigroup α).zero_apply unitBoxL2

/-- Semigroup composition check for `fracLapSemigroup` at `α = 1` on `unitBoxL2`. -/
theorem fracLapSemigroup_add_unitBoxL2 (s t : ℝ≥0) :
    fracLapSemigroup 1 s (fracLapSemigroup 1 t unitBoxL2) =
      fracLapSemigroup 1 (s + t) unitBoxL2 := by
  rw [← ContinuousLinearMap.comp_apply, ← (fracLapSemigroup 1).operator_add]

/-- Contraction estimate `‖fracLapSemigroup α t unitBoxL2‖ ≤ 1` for any `α : ℝ` and `t : ℝ≥0`. -/
theorem norm_fracLapSemigroup_unitBoxL2_le_one (α : ℝ) (t : ℝ≥0) :
    ‖fracLapSemigroup α t unitBoxL2‖ ≤ 1 := by
  calc
    ‖fracLapSemigroup α t unitBoxL2‖ ≤ ‖unitBoxL2‖ := (fracLapSemigroup α).norm_apply_le t unitBoxL2
    _ = 1 := norm_unitBoxL2

/-- Exact Hille–Yosida correspondence check at `α = 1` and `α = 2`. -/
theorem fracLapResolvent_generated_checks (μ : PositiveShift) :
    (fracLapResolvent 1).generatedSemigroup = fracLapSemigroup 1 ∧
      (fracLapResolvent 2).generatedSemigroup = fracLapSemigroup 2 ∧
      (fracLapSemigroup 1).resolvent μ = (fracLapResolvent 1).operator μ :=
  ⟨fracLapResolvent_generatedSemigroup_eq 1,
    fracLapResolvent_generatedSemigroup_eq 2,
    fourierMultiplierSemigroup_resolvent_eq (fracLapSymbol 1) (measurable_fracLapSymbol 1)
      (fracLapSymbol_nonneg 1) μ⟩

/-- **Non-vacuity check**: `fracLapSemigroup 1 1` acts strictly non-trivially on
`f := 𝓕⁻ unitBoxL2`. -/
theorem fracLapSemigroup_one_nontrivial :
    fracLapSemigroup 1 1 (𝓕⁻ unitBoxL2) ≠ 𝓕⁻ unitBoxL2 := by
  intro heq
  have hF :
      𝓕 (fracLapSemigroup 1 1 (𝓕⁻ unitBoxL2)) = 𝓕 (𝓕⁻ unitBoxL2 : L2C) :=
    congrArg (fun x : L2C => 𝓕 x) heq
  change 𝓕 (𝓕⁻ (expMultiplierSymbol (fracLapSymbol 1) (measurable_fracLapSymbol 1)
    (fracLapSymbol_nonneg 1) 1 • 𝓕 (𝓕⁻ unitBoxL2))) = 𝓕 (𝓕⁻ unitBoxL2 : L2C) at hF
  rw [fourier_fourierInv_eq, fourier_fourierInv_eq] at hF
  have hae :
      ((expMultiplierSymbol (fracLapSymbol 1) (measurable_fracLapSymbol 1)
          (fracLapSymbol_nonneg 1) 1 • unitBoxL2 : L2C) : ℝ → ℂ) =ᵐ[volume]
        (unitBoxL2 : ℝ → ℂ) :=
    Lp.ext_iff.mp hF
  have hae_box :
      ∀ᵐ ξ : ℝ,
        ξ ∈ Icc (0 : ℝ) 1 →
          (Real.exp (-((1 : ℝ≥0) : ℝ) * fracLapSymbol 1 ξ) : ℂ) * 1 = 1 := by
    filter_upwards [hae, Lp.coeFn_lpSMul (r := 2)
      (expMultiplierSymbol (fracLapSymbol 1) (measurable_fracLapSymbol 1)
        (fracLapSymbol_nonneg 1) 1) unitBoxL2,
      coeFn_toLpTop
        (expSymbol_aestronglyMeasurable (fracLapSymbol 1) (measurable_fracLapSymbol 1) (1 : ℝ≥0))
        zero_le_one
        (norm_expSymbol_le_one (fracLapSymbol 1) (fracLapSymbol_nonneg 1) (1 : ℝ≥0).coe_nonneg),
      indicatorConstLp_coeFn (p := 2) (s := Icc (0 : ℝ) 1)
        (hs := measurableSet_Icc) (hμs := by simp) (c := (1 : ℂ))]
      with ξ h1 hsmul hexp hind hξ
    have hsmul' :
        ((expMultiplierSymbol (fracLapSymbol 1) (measurable_fracLapSymbol 1)
            (fracLapSymbol_nonneg 1) 1 • unitBoxL2 : L2C) : ℝ → ℂ) ξ =
          (expMultiplierSymbol (fracLapSymbol 1) (measurable_fracLapSymbol 1)
            (fracLapSymbol_nonneg 1) 1 : ℝ → ℂ) ξ * (unitBoxL2 : ℝ → ℂ) ξ := hsmul
    have hexp' :
        (expMultiplierSymbol (fracLapSymbol 1) (measurable_fracLapSymbol 1)
            (fracLapSymbol_nonneg 1) 1 : ℝ → ℂ) ξ =
          (Real.exp (-((1 : ℝ≥0) : ℝ) * fracLapSymbol 1 ξ) : ℂ) := hexp
    have hind' : (unitBoxL2 : ℝ → ℂ) ξ = 1 := by
      simpa only [unitBoxL2, Set.indicator_of_mem hξ] using hind
    calc
      (Real.exp (-((1 : ℝ≥0) : ℝ) * fracLapSymbol 1 ξ) : ℂ) * 1
          = (expMultiplierSymbol (fracLapSymbol 1) (measurable_fracLapSymbol 1)
              (fracLapSymbol_nonneg 1) 1 : ℝ → ℂ) ξ * (unitBoxL2 : ℝ → ℂ) ξ := by
            rw [hexp', hind']
      _ = ((expMultiplierSymbol (fracLapSymbol 1) (measurable_fracLapSymbol 1)
              (fracLapSymbol_nonneg 1) 1 • unitBoxL2 : L2C) : ℝ → ℂ) ξ := hsmul'.symm
      _ = (unitBoxL2 : ℝ → ℂ) ξ := h1
      _ = 1 := hind'
  have hsub :
      Icc (1 / 2 : ℝ) 1 ⊆
        {ξ : ℝ | ¬ (ξ ∈ Icc (0 : ℝ) 1 →
          (Real.exp (-((1 : ℝ≥0) : ℝ) * fracLapSymbol 1 ξ) : ℂ) * 1 = 1)} := by
    intro ξ hξ_mem hξ_eq
    have hξ_icc : ξ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hξ_mem.1], hξ_mem.2⟩
    have hreal : Real.exp (-|2 * Real.pi * ξ|) = 1 := by
      have hC := congrArg Complex.re (hξ_eq hξ_icc)
      simpa only [NNReal.coe_one, neg_mul, one_mul, mul_one, Complex.ofReal_re, Complex.one_re,
        fracLapSymbol, rpow_one] using hC
    have hpi : 0 < |2 * Real.pi * ξ| := by
      have hξpos : 0 < ξ := by linarith [hξ_mem.1]
      positivity
    have hlt : Real.exp (-|2 * Real.pi * ξ|) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hzero : volume (Icc (1 / 2 : ℝ) 1) = 0 :=
    measure_mono_null hsub (ae_iff.mp hae_box)
  rw [Real.volume_Icc] at hzero
  norm_num at hzero

end

end FracLapTest
