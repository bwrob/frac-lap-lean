/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.NashUltracontractivity
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# FracLapTest.NashUltracontractivityTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.WholeLine.NashUltracontractivity`.
-/

namespace FracLapTest

open FracLap MeasureTheory
open scoped ENNReal NNReal SchwartzMap

@[expose] public section

/-- Anti-vacuity: there is a Schwartz function with positive `L¹` norm (a smooth bump). -/
theorem exists_schwartz_pos_l1 : ∃ u : 𝓢(ℝ, ℂ), 0 < ∫ x, ‖(u : ℝ → ℂ) x‖ := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let φ : ℝ → ℂ := fun x => (b x : ℂ)
  have hcs : HasCompactSupport φ := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ))
    Complex.ofReal_zero
  have hsm : ContDiff ℝ (⊤ : ℕ∞) φ := Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨hcs.toSchwartzMap hsm, ?_⟩
  have : ∀ x, ‖(hcs.toSchwartzMap hsm : ℝ → ℂ) x‖ = b x := fun x => by
    change ‖((b x : ℝ) : ℂ)‖ = b x
    rw [Complex.norm_real, Real.norm_of_nonneg b.nonneg]
  simp_rw [this]
  exact b.integral_pos

/-- The `L¹ → L²` decay theorem applies to a genuine datum, at every order `α ∈ (0, 2)`. -/
example {α : ℝ} (hα : FractionalExponent α) {t : ℝ≥0} (ht : 0 < (t : ℝ)) :
    ∃ u : 𝓢(ℝ, ℂ), ‖fracLapSemigroup α t (u.toLp 2)‖ ^ 2 ≤
      (3 ^ (1 + α) * ((2 * Real.pi) ^ α)⁻¹ * (∫ x, ‖(u : ℝ → ℂ) x‖) ^ (2 * α) /
        (2 * α * t)) ^ (1 / α) := by
  obtain ⟨u, hu⟩ := exists_schwartz_pos_l1
  exact ⟨u, nash_l1_l2_decay hα u hu ht⟩

end

end FracLapTest
