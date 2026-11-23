/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.BernsteinLp
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# FracLapTest.BernsteinLpTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.Tools.BernsteinLp`.
-/

namespace FracLapTest

open FracLap FourierTransform MeasureTheory Set Real
open scoped ENNReal SchwartzMap

@[expose] public section

/-- A narrow smooth bump supported in `[-1/2, 1/2]` as a Schwartz symbol. -/
noncomputable def narrowBump : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

noncomputable def narrowSymbol : 𝓢(ℝ, ℂ) :=
  (narrowBump.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ))
    Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp narrowBump.contDiff)

theorem narrowSymbol_apply (ξ : ℝ) :
    (narrowSymbol : ℝ → ℂ) ξ = ((narrowBump ξ : ℝ) : ℂ) := rfl

/-- A band-limited Schwartz function: the inverse Fourier transform of `narrowSymbol`. -/
noncomputable def bandLimited : 𝓢(ℝ, ℂ) := 𝓕⁻ narrowSymbol

theorem fourier_bandLimited (ξ : ℝ) :
    𝓕 (bandLimited : ℝ → ℂ) ξ = ((narrowBump ξ : ℝ) : ℂ) := by
  have h : 𝓕 bandLimited = narrowSymbol := FourierInvPair.fourier_fourierInv_eq narrowSymbol
  have := congrArg (fun F : 𝓢(ℝ, ℂ) => (F : ℝ → ℂ) ξ) h
  simpa [SchwartzMap.fourier_coe, narrowSymbol_apply] using this

theorem bandLimited_band (ξ : ℝ) (hξ : 1 < |ξ|) : 𝓕 (bandLimited : ℝ → ℂ) ξ = 0 := by
  rw [fourier_bandLimited]
  have : narrowBump ξ = 0 := by
    refine narrowBump.zero_of_le_dist ?_
    simp only [narrowBump, Real.dist_eq, sub_zero]
    linarith
  simp [this]

/-- Bernstein's inequality in `L^p` applies to a concrete band-limited function, `R = 1`. -/
example {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, ‖deriv (bandLimited : ℝ → ℂ) x‖ₑ ^ p ≤
      ENNReal.ofReal (1 * bernConst) ^ p * ∫⁻ x, ‖(bandLimited : ℝ → ℂ) x‖ₑ ^ p :=
  bernstein_Lp hp one_pos bandLimited bandLimited_band

/-- The test function is nonzero: `φ(0) = ∫ bump > 0`. -/
theorem bandLimited_zero_ne : (bandLimited : ℝ → ℂ) 0 ≠ 0 := by
  have : (bandLimited : ℝ → ℂ) 0 = ∫ ξ : ℝ, ((narrowBump ξ : ℝ) : ℂ) := by
    simp [bandLimited, SchwartzMap.fourierInv_coe, Real.fourierInv_eq, narrowSymbol_apply]
  rw [this, integral_complex_ofReal]
  exact_mod_cast (narrowBump.integral_pos (μ := volume)).ne'

end

end FracLapTest
