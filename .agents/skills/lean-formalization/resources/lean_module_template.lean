/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# FracLap.<Module>

Formalization of <Topic> following <CitationKey>.
-/

namespace FracLap

@[expose] public section

/-- Docstring stating the mathematical definition. -/
def MyDefinition (x : ℝ) : Prop :=
  0 < x

/-- Docstring matching `\begin{theorem}` in `blueprint/src/content.tex`. -/
theorem my_theorem {x : ℝ} (hx : MyDefinition x) : 0 ≤ x := by
  have h_pos : 0 < x := hx
  exact le_of_lt h_pos

end

end FracLap
