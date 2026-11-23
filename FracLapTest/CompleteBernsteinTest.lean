/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.CompleteBernstein

/-!
# FracLapTest.CompleteBernsteinTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.Tools.CompleteBernstein`.
-/

namespace FracLapTest

open FracLap MeasureTheory

@[expose] public section

/-- The Stieltjes measure `δ₁` is admissible. -/
theorem dirac_one_admissible :
    (∀ᵐ s ∂(Measure.dirac (1 : ℝ)), 0 ≤ s) ∧
      Integrable (fun s : ℝ => 1 / (1 + s)) (Measure.dirac (1 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · rw [ae_dirac_iff (measurableSet_Ici (a := (0 : ℝ)))]; norm_num
  · exact integrable_dirac eNorm_lt_top

/-- Closed form for `σ = δ₁`: `f(z) = z / (z + 1)`. -/
example (z : ℝ) : cbf 0 0 (Measure.dirac (1 : ℝ)) z = z / (z + 1) := by
  simp [cbf, integral_dirac]

/-- Closed forms for the derivatives: `f′ = 1/(z+1)²`, `f″ = -2/(z+1)³`. -/
example (z : ℝ) : cbfDeriv 0 (Measure.dirac (1 : ℝ)) z = 1 / (z + 1) ^ 2 := by
  simp [cbfDeriv, integral_dirac]

example (z : ℝ) : cbfDeriv2 (Measure.dirac (1 : ℝ)) z = -2 / (z + 1) ^ 3 := by
  simp [cbfDeriv2, integral_dirac]
  ring

/-- The derivative formulas apply: `f = z/(z+1)` has derivative `cbfDeriv` at `z = 3`, and
`cbfDeriv` has derivative `cbfDeriv2`. -/
example : HasDerivAt (cbf 0 0 (Measure.dirac (1 : ℝ))) (cbfDeriv 0 (Measure.dirac (1 : ℝ)) 3) 3 :=
  hasDerivAt_cbf dirac_one_admissible.1 dirac_one_admissible.2 (by norm_num)

example : HasDerivAt (cbfDeriv 0 (Measure.dirac (1 : ℝ))) (cbfDeriv2 (Measure.dirac (1 : ℝ)) 3) 3 :=
  hasDerivAt_cbfDeriv dirac_one_admissible.1 dirac_one_admissible.2 (by norm_num)

/-- Both estimates hold for `z / (z + 1)` at `z = 3`: `-z f″ = 3/32 ≤ 2 f′ = 1/8`. -/
example : 0 ≤ -(3 * cbfDeriv2 (Measure.dirac (1 : ℝ)) 3) ∧
    -(3 * cbfDeriv2 (Measure.dirac (1 : ℝ)) 3) ≤ 2 * cbfDeriv 0 (Measure.dirac (1 : ℝ)) 3 :=
  cbf_neg_mul_deriv2_le le_rfl dirac_one_admissible.1 dirac_one_admissible.2 (by norm_num)

example : 3 * cbfDeriv 0 (Measure.dirac (1 : ℝ)) 3 ≤ cbf 0 0 (Measure.dirac (1 : ℝ)) 3 :=
  cbf_mul_deriv_le le_rfl dirac_one_admissible.1 dirac_one_admissible.2 (by norm_num)

/-- Negative check: the second estimate is false for the Bernstein function `1 - e^{-z}`
(`f′ = e^{-z}`, `f″ = -e^{-z}`) at `z = 3`; it needs the Stieltjes structure. -/
example : ¬ (-(3 * (-Real.exp (-3))) ≤ 2 * Real.exp (-3)) := by
  have := Real.exp_pos (-3)
  intro h; linarith

end

end FracLapTest
