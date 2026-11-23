/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.GagliardoFourier
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# FracLapTest.GagliardoFourierTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.WholeLine.GagliardoFourier`.
-/

namespace FracLapTest

open Complex Filter FourierTransform FracLap MeasureTheory Real Set
open scoped ENNReal NNReal

/-! ### Fourier side of the Gagliardo energy -/

/-- Closed-form evaluation: the Fourier-side weight vanishes at the zero frequency, because
`𝐞(h · 0) = 1` kills the integrand. -/
example (α : ℝ) : gagliardoSymbol α 0 = 0 := by
  unfold gagliardoSymbol
  simp

/-- The weight is bounded by a quadratic polynomial, giving a concrete finite value at `ξ = 1`
for the exponent `α = 1`. -/
example : gagliardoSymbol 1 1 ≤
    ENNReal.ofReal (4 * π ^ 2 * (1 + 1 ^ 2)) * ∫⁻ h, gagliardoKernel 1 h :=
  gagliardoSymbol_le fractionalExponent_one 1

/-- The spectral measure at `α = 1` has temperate growth and is finite on compacts, which is
what lets Schwartz functions be dense in `L²(ν₁)`. -/
example : (gagliardoSpectralMeasure 1).HasTemperateGrowth ∧
    IsFiniteMeasureOnCompacts (gagliardoSpectralMeasure 1) :=
  ⟨gagliardoSpectralMeasure_hasTemperateGrowth fractionalExponent_one,
    gagliardoSpectralMeasure_isFiniteMeasureOnCompacts fractionalExponent_one⟩

/-- Boundary case: the zero function has zero Gagliardo energy. -/
example : gagliardoEnergyC 1 0 = 0 := by
  unfold gagliardoEnergyC
  simp

/-- Positive witness for the density theorem at `α = 1`: every `f ∈ L²(ℝ; ℂ)` of finite
energy is approximated by a Schwartz function in the `H^(1/2)` norm. -/
example (f : L2C) (hf : gagliardoEnergyC 1 f < ∞) :
    ∃ φ : SchwartzMap ℝ ℂ, ‖(φ.toLp 2 volume : L2C) - f‖ₑ ^ (2 : ℝ) +
      gagliardoEnergyC 1 ((φ.toLp 2 volume : L2C) - f) < ENNReal.ofReal (1 / 100) :=
  exists_schwartz_close_complex fractionalExponent_one f hf (by norm_num)

end FracLapTest
