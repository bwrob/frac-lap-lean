/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.HalfLine.RestrictedDensity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# FracLapTest.RestrictedDensityTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.HalfLine.RestrictedDensity`.
-/

namespace FracLapTest

open Complex Filter FourierTransform FracLap MeasureTheory Real Set
open scoped ENNReal NNReal

/-! ### 14. Density in the exterior-Dirichlet space -/

/-- Concrete application of the restricted density theorem: the tent element of
`H^(1/2)_0(0, ∞)` is within `1/100` of a real Schwartz function that vanishes on a half-line
`(-∞, δ]`, `δ > 0`. -/
example :
    ∃ (ψ : SchwartzMap ℝ ℝ) (δ : ℝ), 0 < δ ∧ (∀ x, x ≤ δ → ψ x = 0) ∧
      ∃ hψ : gagliardoEnergyR 1 (ψ.toLp 2 MeasureTheory.volume : L2R) < ∞,
        ‖gagliardoMk (ψ.toLp 2 MeasureTheory.volume : L2R) hψ -
          (gagliardoTentRestricted fractionalExponent_one : GagliardoSpace 1)‖ < 1 / 100 :=
  exists_schwartz_close_restricted fractionalExponent_one _ (by norm_num)

/-- Consequence: the approximants satisfy the exterior Dirichlet condition `ψ(0) = 0`, as they
must for functions close to an element of `H^(α/2)_0(0, ∞)`. -/
example (u : RestrictedGagliardoSpace 1) :
    ∃ ψ : SchwartzMap ℝ ℝ, ψ 0 = 0 := by
  obtain ⟨ψ, δ, hδ, hv, -⟩ := exists_schwartz_close_restricted fractionalExponent_one u
    (ε := 1) one_pos
  exact ⟨ψ, hv 0 hδ.le⟩

/-- Boundary check: the zero function has zero `H^(α/2)` norm squared. -/
example (α : ℝ) : gagliardoN2 α 0 = 0 := by
  unfold gagliardoN2 gagliardoEnergyC
  simp

/-- Boundary check for translation continuity: the translation by `0` leaves the `H^(α/2)` norm
squared of the difference at `0`. -/
example (α : ℝ) (f : L2C) : gagliardoN2 α (translateL2 0 f - f) = 0 := by
  have h0 : translateL2 0 f = f := by
    rw [MeasureTheory.Lp.ext_iff]
    filter_upwards [coeFn_translateL2 0 f] with x hx
    simpa using hx
  rw [h0, sub_self]
  unfold gagliardoN2 gagliardoEnergyC
  simp

/-- The quasi-triangle inequality applied to `a + a`: `N²(2 a) ≤ 4 N²(a)`. -/
example (α : ℝ) (a : L2C) : gagliardoN2 α (a + a) ≤ 2 * gagliardoN2 α a + 2 * gagliardoN2 α a :=
  gagliardoN2_add_le α a a

end FracLapTest
