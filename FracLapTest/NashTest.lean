/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.Nash
import Mathlib.Tactic.NormNum

/-!
# FracLapTest.NashTest

The optimization step at `α = 1` on concrete data, and the Nash inequality for `f = 0`, which shows
that its hypotheses are satisfiable.
-/

namespace FracLapTest

open FracLap MeasureTheory

/-- At `α = 1`, `S = T = e = 1` satisfy `S ≤ 2 R T + R^(-1) e` for all `R > 0`, hence
`S² ≤ 9 e T`. -/
example : (1 : ℝ) ^ (1 + (1 : ℝ)) ≤ 3 ^ (1 + (1 : ℝ)) * 1 * 1 ^ (1 : ℝ) := by
  refine nash_optimize (α := 1) one_pos zero_le_one zero_le_one zero_le_one fun R hR => ?_
  rw [Real.rpow_neg_one]
  rcases le_or_gt (1 / 2) R with h | h
  · have : 0 < R⁻¹ := inv_pos.mpr hR
    nlinarith
  · have : 2 < R⁻¹ := by
      rw [lt_inv_comm₀ (by norm_num) hR]
      linarith
    nlinarith

/-- The conclusion of `nash_optimize` forces `S = 0` when `T = 0` (functions with zero `L¹` norm
have zero `L²` norm), a degenerate but consistent case. -/
example {S e : ℝ} (hS : 0 ≤ S) (he : 0 ≤ e)
    (h : ∀ R : ℝ, 0 < R → S ≤ 2 * R * 0 + R ^ (-(1 : ℝ)) * e) : S ^ (1 + (1 : ℝ)) ≤ 0 := by
  have := nash_optimize (α := 1) one_pos hS le_rfl he h
  simpa [Real.zero_rpow] using this

/-- The real-valued Nash inequality is available for every exponent `0 < α < 2` under the stated
hypotheses (integrability and finite energy), with the explicit constant `3^(1+α) / Λ_α(1)`. -/
example {α : ℝ} (hα : FractionalExponent α) (g : L2R) (hg1 : Integrable (g : ℝ → ℝ))
    (hE : gagliardoEnergyR α g ≠ ⊤) :
    (‖g‖ ^ 2) ^ (1 + α) ≤ 3 ^ (1 + α) *
      ((gagliardoSymbol α 1).toReal⁻¹ * (gagliardoEnergyR α g).toReal) *
        ((∫ x, ‖(g : ℝ → ℝ) x‖) ^ 2) ^ α :=
  fractional_nash_real hα g hg1 hE

end FracLapTest
