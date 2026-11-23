/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.HalfLine.FormOrdering

/-!
# FracLapTest.FormOrderingTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.HalfLine.FormOrdering`.
-/

namespace FracLapTest

open FracLap MeasureTheory Set
open scoped ENNReal

@[expose] public section

/-- A concrete datum on the half-line: the indicator of `(0, 1)`. -/
noncomputable def unitIndicator : L2IoiC :=
  indicatorConstLp 2 (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 1))
    (by
      rw [Measure.restrict_apply measurableSet_Ioo]
      exact (lt_of_le_of_lt (measure_mono inter_subset_left) (by simp)).ne) (1 : ℂ)

/-- The ordering applies to a genuine datum, for every `α ∈ (0, 2)`. -/
example {α : ℝ} (hα : FractionalExponent α) :
    gagliardoEnergyC α (extendByZeroIoiC unitIndicator) ≤
      2⁻¹ * gagliardoEnergyC α (oddExtL2 unitIndicator) :=
  restricted_le_spectral hα unitIndicator

/-- The Hankel kernel is a mixture of exponentials: at `x = y = 1`, `ε = 1` and `α = 1`,
`(1 + 1 + 1)^(-2) = 1/9`, and the Laplace representation `Γ(2)⁻¹ ∫₀^∞ s e^{-3 s} ds = 1/9`. -/
example : hankelKernel 1 1 1 1 = 1 / 9 := by
  unfold hankelKernel
  rw [show (1 + 1 + 1 : ℝ) = 3 by norm_num, show (-(1 + (1 : ℝ))) = -2 by norm_num,
    Real.rpow_neg (by norm_num), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- The marginal of the Hankel kernel: `∫₀^∞ (x + y + ε)^(-2) dy = 1 / (x + ε)` for `α = 1`. -/
example : ∫ y in Ioi (0 : ℝ), hankelKernel 1 1 1 y = (1 + 1) ^ (-(1 : ℝ)) / 1 :=
  integral_hankel one_pos one_pos zero_le_one

/-- The datum `1_{(0,1)}` as a function on the line. -/
noncomputable def unitFun : ℝ → ℂ := (Ioo (0 : ℝ) 1).indicator fun _ => (1 : ℂ)

theorem measurable_unitFun : Measurable unitFun :=
  measurable_const.indicator measurableSet_Ioo

theorem memLp_unitFun : MemLp unitFun 2 (volume : Measure ℝ) := by
  rw [memLp_two_iff_integrable_sq_norm measurable_unitFun.aestronglyMeasurable]
  have : (fun x : ℝ => ‖unitFun x‖ ^ 2) = (Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) := by
    funext x
    unfold unitFun
    by_cases hx : x ∈ Ioo (0 : ℝ) 1 <;> simp [hx]
  rw [this]
  exact (integrableOn_const (by simp [Real.volume_Ioo])).integrable_indicator measurableSet_Ioo

theorem unitFun_nonpos (x : ℝ) (hx : x ≤ 0) : unitFun x = 0 := by
  unfold unitFun
  rw [Set.indicator_of_notMem]
  intro h
  linarith [h.1]

/-- Concretely the Hankel form is nonnegative for the datum `1_{(0,1)}`. -/
theorem hankel_unit_nonneg {α : ℝ} (hα : 0 < α) :
    0 ≤ ∫ p : ℝ × ℝ, hankelQuadrant α 1 p *
        (unitFun p.1 * (starRingEnd ℂ) (unitFun p.2)).re ∂(volume.prod volume) :=
  hankel_form_nonneg hα one_pos measurable_unitFun memLp_unitFun unitFun_nonpos

end

end FracLapTest
