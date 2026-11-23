/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Basic
import Mathlib.Tactic.NormNum

/-!
# FracLapTest.BasicTest

Anti-vacuity sanity checks and negative counterexamples for `FracLap.Basic`.
-/

namespace FracLapTest

open FracLap

example : FractionalOrder (1 / 2 : ℝ) := fractionalOrder_half

example : FractionalOrder (1 / 4 : ℝ) := by
  constructor <;> norm_num

example : ¬ FractionalOrder (0 : ℝ) := by
  rintro ⟨h0, _⟩
  norm_num at h0

example : ¬ FractionalOrder (1 : ℝ) := by
  rintro ⟨_, h1⟩
  norm_num at h1

example : ¬ FractionalOrder (-1 : ℝ) := by
  rintro ⟨h0, _⟩
  norm_num at h0

end FracLapTest
