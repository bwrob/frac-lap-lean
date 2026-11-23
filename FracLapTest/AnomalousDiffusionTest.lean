/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.AnomalousDiffusion
public import FracLapTest.HilleYosidaTest
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# FracLapTest.AnomalousDiffusionTest

Tests for generator uniqueness (`wholeLineSemigroup_eq_conv`) on the concrete damping
semigroups `expDecaySemigroup a ha`:
1. The hypotheses are satisfiable (a semigroup against itself).
2. Contrapositive: the identity semigroup (`a = 0`) and the unit damping semigroup (`a = 1`) are
   different semigroups, so they cannot have the same generator domain and generator. This rules
   out the theorem being a restatement of its hypotheses.
-/

@[expose] public section

namespace FracLapTest

open FracLap
open scoped NNReal

/-- The hypotheses of generator uniqueness hold for a semigroup against itself. -/
example (S : StronglyContinuousContractionSemigroup ℝ) : S = S :=
  wholeLineSemigroup_eq_conv S S rfl (fun _ _ _ => rfl)

/-- The damping semigroups with `a = 0` and `a = 1` differ at `t = 1`, `x = 1`. -/
theorem expDecay_zero_ne_one :
    expDecaySemigroup 0 le_rfl ≠ expDecaySemigroup 1 zero_le_one := by
  intro h
  have h1 : expDecaySemigroup 0 le_rfl 1 1 = expDecaySemigroup 1 zero_le_one 1 1 := by rw [h]
  rw [expDecaySemigroup_apply, expDecaySemigroup_apply] at h1
  have hlt : Real.exp (-1 * ((1 : ℝ≥0) : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hz : Real.exp (-0 * ((1 : ℝ≥0) : ℝ)) = 1 := by norm_num
  rw [hz] at h1
  linarith

/-- Contrapositive of generator uniqueness: the two damping semigroups do not share both the
generator domain and the generator. -/
theorem expDecay_zero_one_generators_differ :
    ¬ ((expDecaySemigroup 0 le_rfl).generatorDomain =
        (expDecaySemigroup 1 zero_le_one).generatorDomain ∧
      ∀ (f : ℝ) (hS : f ∈ (expDecaySemigroup 0 le_rfl).generatorDomain)
        (hT : f ∈ (expDecaySemigroup 1 zero_le_one).generatorDomain),
        (expDecaySemigroup 0 le_rfl).generator ⟨f, hS⟩ =
          (expDecaySemigroup 1 zero_le_one).generator ⟨f, hT⟩) :=
  fun h => expDecay_zero_ne_one (wholeLineSemigroup_eq_conv _ _ h.1 h.2)

end FracLapTest
