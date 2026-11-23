/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.GagliardoTools

/-!
# FracLapTest.GagliardoToolsTest

Instantiations of the nonlocal tools on the Gagliardo measure.
-/

namespace FracLapTest

open FracLap MeasureTheory

/-- Dissipativity along the Gagliardo measure for the identity `φ = id` (the `L²` energy is
nonnegative), and for `φ = spow 1` (the `L²` case of the signed-power family). -/
example (α : ℝ) (u : ℝ → ℝ)
    (h1 : Integrable (fun z : ℝ × ℝ => (u z.1 - u z.2) * u z.1) (gagliardoMeasure α))
    (h2 : Integrable (fun z : ℝ × ℝ => (u z.1 - u z.2) * u z.2) (gagliardoMeasure α)) :
    0 ≤ ∫ z, (u z.1 - u z.2) * u z.1 ∂(gagliardoMeasure α) :=
  gagliardo_dissipation_nonneg α u (φ := id) monotone_id h1 h2

/-- The Gagliardo weight is symmetric, which is what makes the measure swap-invariant. -/
example (α x y : ℝ) : gagliardoWeight α (x, y) = gagliardoWeight α (y, x) :=
  (gagliardoWeight_swap α (x, y)).symm

end FracLapTest
