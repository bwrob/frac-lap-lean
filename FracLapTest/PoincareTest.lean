/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.Poincare
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# FracLapTest.PoincareTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.Tools.Poincare`.
-/

namespace FracLapTest

open FracLap MeasureTheory Set
open scoped ENNReal

@[expose] public section

/-- Closed form of the variance on `[0, 1]` for `u(x) = x`: `∫₀¹ (x - 1/2)² = 1/12`. -/
example : ∫ x in Icc (0 : ℝ) 1, (x - (∫ y in Icc (0 : ℝ) 1, y) / (1 - 0)) ^ 2 = 1 / 12 := by
  have h1 : ∫ y in Icc (0 : ℝ) 1, y = 1 / 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    simp [integral_id]
  rw [h1, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have : ∀ x : ℝ, (x - 1 / 2 / (1 - 0)) ^ 2 = x ^ 2 - x + 1 / 4 := fun x => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub]
  · simp [integral_pow, integral_id]; norm_num
  all_goals first
    | exact (continuous_pow 2).intervalIntegrable _ _
    | exact continuous_id.intervalIntegrable _ _
    | exact (((continuous_pow 2).sub continuous_id)).intervalIntegrable _ _
    | exact intervalIntegrable_const

/-- `u(x) = x` is square integrable on `[0, 1]`. -/
theorem memLp_id_Icc : MemLp (fun x : ℝ => x) 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
  refine MemLp.of_bound measurable_id.aestronglyMeasurable 1 ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
  exact hx.2

/-- The fractional Poincaré inequality applies to `u(x) = x` on `[0, 1]` with `α = 1`, `C = 1`
(constant `(b - a)^α / C = 1`). -/
example : ENNReal.ofReal (∫ x in Icc (0 : ℝ) 1, (x - (∫ y in Icc (0 : ℝ) 1, y) / (1 - 0)) ^ 2) ≤
    ENNReal.ofReal ((1 - 0 : ℝ) ^ (1 : ℝ) / 1) *
      ∫⁻ p, ENNReal.ofReal (1 / 2 * |p.1 - p.2| ^ (-(1 + (1 : ℝ)))) *
        ENNReal.ofReal ((p.1 - p.2) ^ 2) ∂(volume.prod volume) :=
  poincare_gagliardo_interval (a := 0) (b := 1) (α := 1) (C := 1) zero_lt_one one_pos one_pos
    measurable_id memLp_id_Icc

/-- The Poincaré inequality for the Lebesgue kernel on `[0, 1]` is applicable to `u(x) = x`
(`m = 1`, `J = 1` on `[0,1]²`): the hypotheses of `poincare_of_kernel_lower_bound` are met. -/
example : ENNReal.ofReal (∫ x in Icc (0 : ℝ) 1, (x - (∫ y in Icc (0 : ℝ) 1, y) /
      (volume (Icc (0 : ℝ) 1)).toReal) ^ 2) ≤
    ENNReal.ofReal (1 / (2 * 1 * (volume (Icc (0 : ℝ) 1)).toReal)) *
      ∫⁻ p, (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) p *
        ENNReal.ofReal ((p.1 - p.2) ^ 2) ∂(volume.prod volume) := by
  refine poincare_of_kernel_lower_bound (by simp) (by simp) memLp_id_Icc one_pos
    measurable_id (measurable_const.indicator (measurableSet_Icc.prod measurableSet_Icc)) ?_
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
  rw [Set.indicator_of_mem hp]
  simp


/-- **Negative check (atoms alone do not suffice).** For the one-step jump measure
`ν = (x ↦ (x, x+1))_* Leb|[0,1]`, which has no absolutely continuous part, `u = cos (2π ·)` has
zero `ν`-energy on `I = [0, 2]` although its variance on `I` is positive. Hence no inequality
`ofReal m • Leb|_{I×I} ≤ ν` can hold, and the lower bound hypothesis of
`poincare_of_lower_bound` cannot be dropped. -/
example : ¬ ∃ m : ℝ, 0 < m ∧ ENNReal.ofReal m • (volume.prod volume).restrict
    (Icc (0 : ℝ) 2 ×ˢ Icc (0 : ℝ) 2) ≤
      Measure.map (fun x : ℝ => (x, x + 1)) (volume.restrict (Icc (0 : ℝ) 1)) := by
  rintro ⟨m, hm, h⟩
  -- the set `{(x, y) ∈ I × I | y ≠ x + 1}` is null for `ν` but not for Lebesgue measure
  set S : Set (ℝ × ℝ) := {p | p.2 ≠ p.1 + 1} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_eq_fun measurable_snd (measurable_fst.add measurable_const)).compl
  have hν0 : Measure.map (fun x : ℝ => (x, x + 1)) (volume.restrict (Icc (0 : ℝ) 1)) S = 0 := by
    rw [Measure.map_apply (by fun_prop) hSm]
    have : (fun x : ℝ => (x, x + 1)) ⁻¹' S = ∅ := by ext x; simp [hS]
    rw [this]; simp
  have h1 := h S
  rw [hν0, le_zero_iff, smul_apply, Measure.restrict_apply hSm, smul_eq_mul] at h1
  have hmpos : ENNReal.ofReal m ≠ 0 := by simpa using hm
  have hz := (mul_eq_zero.1 h1).resolve_left hmpos
  -- but `S ∩ (I × I)` contains the open square `(0, 1) × (0, 1/2)`, of positive measure
  have hsub : Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) (1 / 2) ⊆ S ∩ Icc (0 : ℝ) 2 ×ˢ Icc (0 : ℝ) 2 := by
    rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, hy0, hy1⟩
    refine ⟨?_, ⟨hx0.le, by linarith⟩, hy0.le, by linarith⟩
    simp only [hS, mem_ofPred_eq]
    intro hxy; linarith
  have hpos : 0 < (volume.prod volume) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) (1 / 2)) := by
    rw [Measure.prod_prod]
    simp
  exact (hpos.trans_le (measure_mono hsub)).ne' hz

end

end FracLapTest
