/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.Symmetrization
import Mathlib.Tactic.NormNum

/-!
# FracLapTest.SymmetrizationTest

The symmetrization identity applies to product measures, and swap-invariance is a necessary
hypothesis: for the non-symmetric measure `δ_(1, 0)` the two sides differ.
-/

namespace FracLapTest

open FracLap MeasureTheory

/-- The identity holds for every product measure `μ ⊗ μ`. -/
example (μ : Measure ℝ) [SFinite μ] (u g : ℝ → ℝ)
    (h1 : Integrable (fun z : ℝ × ℝ => (u z.1 - u z.2) * g z.1) (μ.prod μ))
    (h2 : Integrable (fun z : ℝ × ℝ => (u z.1 - u z.2) * g z.2) (μ.prod μ)) :
    ∫ z, (u z.1 - u z.2) * g z.1 ∂(μ.prod μ) =
      (1 / 2) * ∫ z, (u z.1 - u z.2) * (g z.1 - g z.2) ∂(μ.prod μ) :=
  integral_sub_mul_eq_half Measure.measurePreserving_swap u g h1 h2

/-- Negative counterexample: for the non-symmetric measure `δ_(1, 0)` and `u = g = id`, the left
side is `1` but the right side is `1/2`, so swap-invariance cannot be dropped. -/
example :
    ∫ z : ℝ × ℝ, (z.1 - z.2) * z.1 ∂(Measure.dirac ((1 : ℝ), (0 : ℝ))) ≠
      (1 / 2) * ∫ z : ℝ × ℝ, (z.1 - z.2) * (z.1 - z.2) ∂(Measure.dirac ((1 : ℝ), (0 : ℝ))) := by
  rw [integral_dirac, integral_dirac]
  norm_num

end FracLapTest
