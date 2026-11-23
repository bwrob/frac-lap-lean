/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.TranslationFourier
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# FracLapTest.TranslationFourierTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.WholeLine.TranslationFourier`.
-/

namespace FracLapTest

open Complex Filter FourierTransform FracLap MeasureTheory Real Set
open scoped ENNReal NNReal

/-! ### Translation on `L²` and its Fourier-side phase -/

/-- Boundary check: translation by `0` is the identity on `L²(ℝ; ℂ)`. -/
example (f : L2C) : translateL2 0 f = f := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_translateL2 0 f] with x hx
  simpa using hx

/-- Closed-form evaluations of the phase `𝐞(h ξ) = exp(2π i h ξ)`: it is `1` at `ξ = 0` and at
the full period `ξ = 1 / h`, and `-1` at the half period `ξ = 1 / (2 h)`. -/
example : ((𝐞 (2 * 0) : Circle) : ℂ) = 1 ∧ ((𝐞 (2 * (1 / 2)) : Circle) : ℂ) = 1 ∧
    ((𝐞 (2 * (1 / 4)) : Circle) : ℂ) = -1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · rw [Real.fourierChar_apply]
    rw [show 2 * (1 / 2 : ℝ) = 1 by norm_num]
    have : (↑(2 * π * 1) * I : ℂ) = 1 * (2 * π * I) := by push_cast; ring
    rw [this, one_mul, Complex.exp_two_pi_mul_I]
  · rw [Real.fourierChar_apply]
    rw [show 2 * (1 / 4 : ℝ) = 1 / 2 by norm_num]
    have : (↑(2 * π * (1 / 2)) * I : ℂ) = π * I := by push_cast; ring
    rw [this, Complex.exp_pi_mul_I]

/-- Negative counterexample: the phase symbol is not constant, so the multiplier
`translatePhase h - 1` is genuinely nonzero: at the half period it has modulus `2`. -/
example : ‖((𝐞 (2 * (1 / 4)) : Circle) : ℂ) - 1‖ = 2 := by
  have h : ((𝐞 (2 * (1 / 4)) : Circle) : ℂ) = -1 := by
    rw [Real.fourierChar_apply, show 2 * (1 / 4 : ℝ) = 1 / 2 by norm_num]
    have : (↑(2 * π * (1 / 2)) * I : ℂ) = π * I := by push_cast; ring
    rw [this, Complex.exp_pi_mul_I]
  rw [h]
  norm_num

/-- Consistency of the Fourier-side translation modulus at `h = 0`: both sides vanish. -/
example (f : L2C) :
    ∫⁻ ξ, ‖((𝐞 (0 * ξ) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) = 0 := by
  rw [← lintegral_enorm_sq_translate_sub 0 f]
  simp

/-- Instance of the Plancherel-side identity: it transports the `L²` translation modulus of any
`f ∈ L²(ℝ; ℂ)` to a weighted integral of `‖𝓕 f‖²`. -/
example (h : ℝ) (f : L2C) :
    ∫⁻ y, ‖(f : ℝ → ℂ) (y + h) - (f : ℝ → ℂ) y‖ₑ ^ (2 : ℝ) =
      ∫⁻ ξ, ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) :=
  lintegral_enorm_sq_translate_sub h f

end FracLapTest
