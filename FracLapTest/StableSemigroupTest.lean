/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.StableSemigroup
import Mathlib.Tactic.NormNum

/-!
# FracLapTest.StableSemigroupTest

Consequences of the bridge between the `L²` Fourier-multiplier semigroup and convolution with the
stable kernel: `L²` contractivity of stable convolution, and the semigroup law on Schwartz data.
-/

namespace FracLapTest

open FracLap MeasureTheory
open scoped ENNReal NNReal SchwartzMap Convolution

/-- Convolution with `P_{3/2}(·, t)` is an `L²` contraction on Schwartz data. This is a genuine
consequence of the bridge `fracLapSemigroup_apply_schwartz` and contractivity of the semigroup:
no Young inequality is used. -/
example {t : ℝ≥0} (ht : 0 < (t : ℝ)) (u : 𝓢(ℝ, ℂ)) :
    ‖(memLp_two_convolution_schwartz
        (K := fun x : ℝ => (((stableHeatKernel (3 / 2) ⟨by norm_num, by norm_num⟩).P x t : ℝ) : ℂ))
        (Complex.ofRealCLM.integrable_comp
          ((stableHeatKernel (3 / 2) ⟨by norm_num, by norm_num⟩).integrable_space t ht)) u).toLp
        ((fun x : ℝ =>
          (((stableHeatKernel (3 / 2) ⟨by norm_num, by norm_num⟩).P x t : ℝ) : ℂ)) ⋆[
            ContinuousLinearMap.mul ℂ ℂ] (u : ℝ → ℂ))‖ ≤ ‖u.toLp 2‖ := by
  rw [← fracLapSemigroup_apply_schwartz (α := 3 / 2) ⟨by norm_num, by norm_num⟩ ht u]
  exact (fracLapSemigroup (3 / 2)).norm_apply_le t _

/-- The convolution of the stable kernel with a Schwartz datum is square integrable, at `α = 1`. -/
example (u : 𝓢(ℝ, ℂ)) :
    MemLp ((fun x : ℝ => (((stableHeatKernel 1 fractionalExponent_one).P x 2 : ℝ) : ℂ)) ⋆[
      ContinuousLinearMap.mul ℂ ℂ] (u : ℝ → ℂ)) 2 volume :=
  memLp_two_convolution_schwartz (Complex.ofRealCLM.integrable_comp
    ((stableHeatKernel 1 fractionalExponent_one).integrable_space 2 (by norm_num))) u

/-- Full `L²(ℝ; ℂ)` semigroup–kernel realization (`prop:s_equals_t`) and Markov preservation
(`thm:s_markov`) at `α = 1`: `fracLapSemigroup 1 t` equals `stableConvOp 1` and preserves real
nonnegativity and upper bounds a.e. -/
example {t : ℝ≥0} (ht : 0 < (t : ℝ)) {f : L2C}
    (hf_real : ∀ᵐ x : ℝ ∂volume, ((f : ℝ → ℂ) x).im = 0)
    (hf_nn : ∀ᵐ x : ℝ ∂volume, 0 ≤ ((f : ℝ → ℂ) x).re)
    (hf_le : ∀ᵐ x : ℝ ∂volume, ((f : ℝ → ℂ) x).re ≤ 1) :
    fracLapSemigroup 1 t f = stableConvOp 1 fractionalExponent_one ht f ∧
      (∀ᵐ x : ℝ ∂volume, ((fracLapSemigroup 1 t f : ℝ → ℂ) x).im = 0) ∧
      (∀ᵐ x : ℝ ∂volume, 0 ≤ ((fracLapSemigroup 1 t f : ℝ → ℂ) x).re) ∧
      (∀ᵐ x : ℝ ∂volume, ((fracLapSemigroup 1 t f : ℝ → ℂ) x).re ≤ 1) := by
  refine ⟨by rw [fracLapSemigroup_eq_stableConvOp fractionalExponent_one ht], ?_⟩
  exact ⟨(fracLapSemigroup_re_nonneg fractionalExponent_one t hf_real hf_nn).1,
    (fracLapSemigroup_re_nonneg fractionalExponent_one t hf_real hf_nn).2,
    fracLapSemigroup_re_le fractionalExponent_one t hf_le⟩

end FracLapTest
