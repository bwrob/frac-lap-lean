/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.FractionalAnalytic

/-!
# FracLapTest.FractionalAnalyticTest

Anti-vacuity witnesses, closed-form evaluations, boundary checks and negative counterexamples for
`FracLap.WholeLine.FractionalAnalytic`: the heat symbol `ψ(ξ) = ξ²`, the Taylor remainder bound
at explicit parameters, and the whole-line fractional heat semigroup at `α = 1`.
-/

namespace FracLapTest

open Complex FracLap
open scoped NNReal

@[expose] public section

/-- The heat symbol `ψ(ξ) = ξ²` is measurable and nonnegative. -/
theorem heatSymbol_measurable : Measurable (fun ξ : ℝ => ξ ^ 2) := by fun_prop

/-- The heat symbol is nonnegative. -/
theorem heatSymbol_nonneg : ∀ ξ : ℝ, 0 ≤ ξ ^ 2 := fun ξ => sq_nonneg ξ

/-- Closed form: at `z = 1`, `ξ = 1` the symbol is `exp (-1)`. -/
example : symFun (fun ξ : ℝ => ξ ^ 2) 1 1 = Complex.exp (-1) := by
  rw [symFun_of_re_nonneg _ (by simp)]
  simp

/-- Non-vacuity: the symbol is not identically `1`, so the semigroup is not trivial. -/
example : symFun (fun ξ : ℝ => ξ ^ 2) 1 1 ≠ 1 := by
  rw [symFun_of_re_nonneg _ (by simp)]
  simp only [Complex.ofReal_one, one_pow, mul_one]
  intro h
  have h1 : (Complex.exp (-1)).re = Real.exp (-1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_neg, Complex.exp_ofReal_re]
  have h2 := congrArg Complex.re h
  rw [h1] at h2
  have hlt : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  simp only [Complex.one_re] at h2
  linarith

/-- The symbol at purely imaginary time has modulus exactly `1` (boundary of the half-plane). -/
example : ‖symFun (fun ξ : ℝ => ξ ^ 2) Complex.I 1‖ = 1 := by
  rw [symFun_of_re_nonneg _ (by simp), Complex.norm_exp]
  simp

/-- The Taylor remainder bound at explicit parameters `a = 1`, `z = 1`, `h = 1/2`, `p = 1`. -/
example :
    ‖Complex.exp (-((1 + (1 / 2 : ℂ)) * ((1 : ℝ) : ℂ))) - Complex.exp (-((1 : ℂ) * ((1 : ℝ) : ℂ))) -
        (1 / 2 : ℂ) * (-(((1 : ℝ) : ℂ) * Complex.exp (-((1 : ℂ) * ((1 : ℝ) : ℂ)))))‖ ≤
      48 / 1 ^ 2 * ‖(1 / 2 : ℂ)‖ ^ 2 :=
  norm_exp_taylor_symbol (a := 1) one_pos (z := 1) (by simp) (by simp) (by norm_num)

/-- The fractional heat semigroup at `α = 1` maps `0` into the generator domain at time `1`. -/
example : (fracLapSemigroup 1) 1 (0 : L2C) ∈ (fracLapSemigroup 1).generatorDomain :=
  fracLapSemigroup_mem_generatorDomain_of_pos 1 0 (t := 1) one_pos

/-- The analytic extension at real time `1` is the real-time fractional heat semigroup. -/
example (f : L2C) :
    (fracLapAnalyticSemigroup 1).operator ((1 : ℝ≥0) : ℂ) f = fracLapSemigroup 1 1 f :=
  fracLapAnalyticSemigroup_ofReal_apply 1 1 f

/-- Contractivity of the complex-time operators on the closed right half-plane. -/
example (f : L2C) : ‖fourierOp (fun ξ : ℝ => ξ ^ 2) heatSymbol_measurable heatSymbol_nonneg
    (Complex.I + 1) f‖ ≤ ‖f‖ :=
  norm_fourierOp_apply_le _ _ _ _ f

end

end FracLapTest
