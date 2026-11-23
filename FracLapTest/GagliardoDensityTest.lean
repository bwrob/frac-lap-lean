/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.GagliardoDensity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# FracLapTest.GagliardoDensityTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.WholeLine.GagliardoDensity`.
-/

namespace FracLapTest

open Complex Filter FourierTransform FracLap MeasureTheory Real Set
open scoped ENNReal NNReal

/-! ### 12. Density of Schwartz functions in the Gagliardo space -/

/-- Concrete application of the density theorem: the tent element of `H^(1/2)(ℝ)` is within
`1/100` of a real Schwartz function, measured in the Gagliardo norm. -/
example :
    ∃ (φ : SchwartzMap ℝ ℝ) (hφ : gagliardoEnergyR 1 (φ.toLp 2 MeasureTheory.volume : L2R) < ∞),
      ‖gagliardoMk (φ.toLp 2 MeasureTheory.volume : L2R) hφ -
        gagliardoTentSpace fractionalExponent_one‖ < 1 / 100 :=
  exists_schwartz_close_real fractionalExponent_one _ (by norm_num)

/-- Round trip: the real part of a complexified function is the function itself. -/
example (g : L2R) : reL2 (ofRealL2 g) = g := reL2_ofRealL2 g

/-- Consequence of the round trip: complexification is injective, so no information is lost
when passing to the Fourier side. -/
example (g h : L2R) (e : ofRealL2 g = ofRealL2 h) : g = h := by
  rw [← reL2_ofRealL2 g, ← reL2_ofRealL2 h, e]

/-- Boundary check: the zero function has zero real Gagliardo energy. -/
example (α : ℝ) : gagliardoEnergyR α 0 = 0 := by
  unfold gagliardoEnergyR
  simp

/-- The `L²` part of `gagliardoMk g` is `g`: the construction is a section of the projection. -/
example (g : L2R) (hg : gagliardoEnergyR 1 g < ∞) : gagliardoL2Part 1 (gagliardoMk g hg) = g :=
  gagliardoL2Part_mk g hg

/-- Negative counterexample for degeneracy: the energy part of the tent element is strictly
positive, so the norm formula `‖v‖² = ‖v_{L²}‖² + E(v_{L²})` has a genuinely nonzero second
term there. -/
example : 0 < (gagliardoForm 1).form (gagliardoTentSpace fractionalExponent_one)
    (gagliardoTentSpace fractionalExponent_one) := by
  change 0 < inner ℝ (gagliardoDiffPart 1 (gagliardoTentSpace fractionalExponent_one))
    (gagliardoDiffPart 1 (gagliardoTentSpace fractionalExponent_one))
  rw [real_inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.mpr (gagliardoTentDiffL2_ne_zero fractionalExponent_one)) 2

end FracLapTest
