/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.SemigroupDissipation

/-!
# FracLapTest.SemigroupDissipationTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.WholeLine.SemigroupDissipation`.
-/

namespace FracLapTest

open FracLap MeasureTheory
open scoped ENNReal NNReal

@[expose] public section

/-- The Hardy--Stein identity implies `L²` contractivity of the semigroup (the energy integral
is nonnegative). -/
example (α : ℝ) (f : L2C) (t : ℝ≥0) : ‖fracLapSemigroup α t f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have h := hardy_stein_l2 α f t
  have hnn : 0 ≤ ∫ s in (0 : ℝ)..t, spectralEnergy α f s := by
    refine intervalIntegral.integral_nonneg t.coe_nonneg fun s hs => ?_
    unfold spectralEnergy
    exact integral_nonneg fun ξ => by have := fracLapSymbol_nonneg α ξ; positivity
  linarith

/-- At `t = 0` the identity reads `‖f‖² - ‖f‖² = 0`. -/
example (α : ℝ) (f : L2C) : ‖f‖ ^ 2 - ‖fracLapSemigroup α 0 f‖ ^ 2 =
    2 * ∫ s in (0 : ℝ)..((0 : ℝ≥0) : ℝ), spectralEnergy α f s := hardy_stein_l2 α f 0

/-- The spectral mass at `t = 0` is the squared norm. -/
example (α : ℝ) (f : L2C) : spectralMass α f 0 = ‖f‖ ^ 2 := spectralMass_zero α f

end

end FracLapTest
