/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.Young
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# FracLapTest.YoungTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.Tools.Young`.
-/

namespace FracLapTest

open FracLap MeasureTheory
open scoped ENNReal Convolution SchwartzMap

@[expose] public section

/-- Young's inequality applies to a pair of Schwartz functions at every exponent `p ≥ 1`. -/
example (u v : 𝓢(ℝ, ℂ)) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, ‖((u : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (v : ℝ → ℂ)) x‖ₑ ^ p ≤
      (∫⁻ y, ‖(u : ℝ → ℂ) y‖ₑ) ^ p * ∫⁻ x, ‖(v : ℝ → ℂ) x‖ₑ ^ p :=
  lintegral_rpow_convolution_le' hp u.continuous.aestronglyMeasurable
    v.continuous.aestronglyMeasurable u.integrable.hasFiniteIntegral.ne

/-- Sanity check at the `p = 1` endpoint: the constant is the product of the `L¹` norms. -/
example (u v : 𝓢(ℝ, ℂ)) :
    ∫⁻ x, ‖((u : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (v : ℝ → ℂ)) x‖ₑ ≤
      (∫⁻ y, ‖(u : ℝ → ℂ) y‖ₑ) * ∫⁻ x, ‖(v : ℝ → ℂ) x‖ₑ :=
  lintegral_enorm_convolution_le u.continuous.aestronglyMeasurable
    v.continuous.aestronglyMeasurable

end

end FracLapTest
