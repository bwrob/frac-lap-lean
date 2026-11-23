/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.Gronwall

/-!
# FracLapTest.GronwallTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.Tools.Gronwall`.
-/

namespace FracLapTest

open FracLap

/-- Closed form of the singular kernel integral: `∫₀⁴ (4 - τ)^(-1/2) dτ = 4`. -/
example : ∫ τ in (0 : ℝ)..4, (4 - τ) ^ (-(1 / 2 : ℝ)) = 4 := by
  rw [integral_sub_rpow_neg (by norm_num) 4]
  have h : (4 : ℝ) ^ (1 - 1 / 2 : ℝ) = 2 := by
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h]; norm_num

/-- The Gronwall lemma applies to `h(t) = 1 + t` with `C₁ = 1`, `C₂ = 1`, `a = 1/2`, `b = 1`:
the hypothesis `h(t) ≤ C₁ (1 + t) + C₂ ∫ …` holds because the integral term is nonnegative, so
the hypotheses are satisfiable with a nonzero kernel term, and the lemma yields a linear bound. -/
example : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → 1 + t ≤ C * (1 + t) := by
  refine gronwall_singular (h := fun t => 1 + t) (C₁ := 1) (C₂ := 1) (a := 1 / 2) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) zero_le_one
    (fun t ht => by linarith) (fun T => ⟨1 + T, fun t _ ht => by linarith⟩) ?_
  intro t ht
  have hI : 0 ≤ ∫ τ in (0 : ℝ)..t, (t - τ) ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-(1 : ℝ)) * (1 + τ) := by
    refine intervalIntegral.integral_nonneg ht fun τ hτ => ?_
    have h0 : 0 ≤ t - τ := by linarith [hτ.2]
    have h1 : 0 ≤ 1 + τ := by linarith [hτ.1]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg h0 _) (Real.rpow_nonneg h1 _)) h1
  change 1 + t ≤ 1 * (1 + t) + 1 * _
  linarith

/-- Negative check: for the borderline exponent `a = 1` the kernel `(1 - τ)^(-1)` is not
integrable, so the interval integral collapses to the junk value `0`; this is why the lemma
requires `a < 1`. -/
example : ∫ τ in (0 : ℝ)..1, (1 - τ) ^ (-(1 : ℝ)) = 0 := by
  have : ¬ IntervalIntegrable (fun τ : ℝ => (1 - τ) ^ (-(1 : ℝ))) MeasureTheory.volume 0 1 := by
    intro h
    have h2 := h.comp_sub_left 1
    simp only [sub_self, sub_zero, sub_sub_cancel] at h2
    have h3 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 : ℝ))) MeasureTheory.volume 0 1 :=
      h2.symm
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one,
      intervalIntegral.integrableOn_Ioo_rpow_iff one_pos] at h3
    exact lt_irrefl _ h3
  exact intervalIntegral.integral_undef this

end FracLapTest
