/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.Interpolation
import Mathlib.Tactic.NormNum

/-!
# FracLapTest.InterpolationTest

Interpolation of fractional energies: endpoints and a concrete exponent triple.
-/

namespace FracLapTest

open FracLap

/-- Midpoint interpolation `E_1 ≤ E_{1/2}^{1/2} E_{3/2}^{1/2}`, since `1 = ½·½ + ½·3/2`. -/
example (f : L2C) :
    gagliardoEnergyC 1 f ≤ gagliardoEnergyC (1 / 2) f ^ (1 - (1 / 2 : ℝ)) *
      gagliardoEnergyC (3 / 2) f ^ (1 / 2 : ℝ) :=
  gagliardoEnergyC_interpolation (a := 1 / 2) (c := 3 / 2) (θ := 1 / 2)
    ⟨by norm_num, by norm_num⟩ fractionalExponent_one ⟨by norm_num, by norm_num⟩ (by norm_num)
    (by norm_num) (by norm_num) f

end FracLapTest
