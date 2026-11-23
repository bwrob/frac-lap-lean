/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.HalfLine.RestrictedAnalytic

/-!
# FracLapTest.RestrictedAnalyticTest

Anti-vacuity witnesses and concrete evaluations for `FracLap.HalfLine.RestrictedAnalytic`: the
smoothing estimates hold at `α = 1` for a nonzero datum, and the energy bound is attained
non-trivially.
-/

namespace FracLapTest

open FracLap MeasureTheory Set
open scoped NNReal InnerProductSpace

@[expose] public section

/-- At `α = 1` there is a nonzero rough datum `f` whose orbit at time `1` enters `H_0^{1/2}` with
the energy bound `B(v, v) ≤ ‖f‖²`. -/
example (μ : PositiveShift) :
    ∃ f : L2IoiR, f ≠ 0 ∧
      ∃ v : RestrictedGagliardoSpace 1,
        restrictedL2Map 1 v = restrictedFracLapSemigroup 1 fractionalExponent_one (1 : ℝ≥0) f ∧
          (restrictedGagliardoForm 1).form v v ≤ ‖f‖ ^ 2 / ((1 : ℝ≥0) : ℝ) := by
  obtain ⟨f, _, _, hpos⟩ := exists_restrictedFracLapSemigroup_nontrivial fractionalExponent_one μ
  refine ⟨f, ?_, restrictedFracLapSemigroup_exists_form_bound fractionalExponent_one f
    (t := 1) (by norm_num)⟩
  rintro rfl
  simp at hpos

/-- The `1/t` decay is a genuine bound: for `t = 2` it halves the constant. -/
example (f : L2IoiR) :
    ‖(restrictedFracLapSemigroup (1 / 2) ⟨by norm_num, by norm_num⟩).generator
      ⟨restrictedFracLapSemigroup (1 / 2) ⟨by norm_num, by norm_num⟩ 2 f,
        restrictedFracLapSemigroup_mem_generatorDomain_of_pos _ f (t := 2) (by norm_num)⟩‖ ≤
      ‖f‖ / 2 := by
  have := norm_generator_restrictedFracLapSemigroup_le (α := 1 / 2)
    ⟨by norm_num, by norm_num⟩ f (t := 2) (by norm_num)
  simpa using this

/-- Boundary check: smoothing is a statement about *positive* times; at `t = 0` the datum itself
need not lie in the domain, but strong continuity still gives `S(t) f → f`. -/
example (f : L2IoiR) :
    Filter.Tendsto (fun t : ℝ≥0 => restrictedFracLapSemigroup 1 fractionalExponent_one t f)
      (nhds 0) (nhds f) :=
  tendsto_restrictedFracLapSemigroup_zero fractionalExponent_one f

end

end FracLapTest
