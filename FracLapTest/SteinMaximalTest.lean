/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.SteinMaximal
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# FracLapTest.SteinMaximalTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.WholeLine.SteinMaximal`.
-/

namespace FracLapTest

open FracLap MeasureTheory
open scoped ENNReal SchwartzMap Convolution

@[expose] public section

/-- Stein's maximal inequality at `p = 2` for every Schwartz datum and every `α ∈ (0, 2)`. -/
example {α : ℝ} (hα : FractionalExponent α) (u : 𝓢(ℝ, ℂ)) :
    ∫⁻ x, (⨆ t : {t : ℝ // 0 < t},
        ‖((fun y : ℝ => (((stableHeatKernel α hα).P y t.1 : ℝ) : ℂ)) ⋆[
          ContinuousLinearMap.mul ℂ ℂ] (u : ℝ → ℂ)) x‖ₑ) ^ (2 : ℝ) ≤
      ENNReal.ofReal (10 * 2 * 2 ^ ((2 : ℝ) - 1) / ((2 : ℝ) - 1)) *
        ∫⁻ y, ‖(u : ℝ → ℂ) y‖ₑ ^ (2 : ℝ) :=
  stein_maximal hα (by norm_num) u

/-- The supremum over `t` dominates the value at `t = 1`, so the single-time bound
`‖P_1 ⋆ u‖₂² ≤ 40 ‖u‖₂²` follows (consistent with the `L²` contractivity `≤ 1`). -/
example {α : ℝ} (hα : FractionalExponent α) (u : 𝓢(ℝ, ℂ)) :
    ∫⁻ x, ‖((fun y : ℝ => (((stableHeatKernel α hα).P y 1 : ℝ) : ℂ)) ⋆[
          ContinuousLinearMap.mul ℂ ℂ] (u : ℝ → ℂ)) x‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (10 * 2 * 2 ^ ((2 : ℝ) - 1) / ((2 : ℝ) - 1)) *
        ∫⁻ y, ‖(u : ℝ → ℂ) y‖ₑ ^ (2 : ℝ) := by
  refine le_trans (lintegral_mono fun x => ENNReal.rpow_le_rpow
    (le_iSup (fun t : {t : ℝ // 0 < t} =>
      ‖((fun y : ℝ => (((stableHeatKernel α hα).P y t.1 : ℝ) : ℂ)) ⋆[
        ContinuousLinearMap.mul ℂ ℂ] (u : ℝ → ℂ)) x‖ₑ) ⟨1, one_pos⟩) (by norm_num)) ?_
  exact stein_maximal hα (by norm_num) u

end

end FracLapTest
