/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.HalfLine.ReflectedSemigroup
public import FracLap.WholeLine.StableHeatKernel
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum

/-!
# FracLapTest.StableHeatKernelTest

Anti-vacuity witnesses, closed-form evaluations, Fourier faithfulness checks, separation from
degenerate polynomial families, and unconditional semigroup/kernel domain instantiations for
`FracLap.WholeLine.StableHeatKernel`.
-/

namespace FracLapTest

open Complex FourierTransform FracLap Real

@[expose] public section

/-- Exact Cauchy closed-form match at `α = 1`, `x = 0`, `t = 1`: `P_1(0, 1) = 1 / π`. -/
example : (stableHeatKernel 1 fractionalExponent_one).P 0 1 = 1 / π := by
  rw [stableHeatKernel_one_eq_cauchy 0 one_pos]
  change 1 / (π * (1 ^ 2 + 0 ^ 2)) = 1 / π
  ring_nf

/-- Fourier faithfulness check at `α = 1`, `t = 1`, `ξ = 1`. -/
example :
    𝓕 (fun x : ℝ => (((stableHeatKernel 1 fractionalExponent_one).P x 1 : ℝ) : ℂ)) 1 =
      ((Real.exp (-1 * |2 * π * 1| ^ (1 : ℝ)) : ℝ) : ℂ) :=
  fourier_stableKernel_eq one_pos (by norm_num) one_pos 1

/-- Unit total mass check at `α = 3 / 2`, `t = 2`. -/
example :
    ∫ x : ℝ, (stableHeatKernel (3 / 2 : ℝ) ⟨by norm_num, by norm_num⟩).P x 2 = 1 :=
  (stableHeatKernel (3 / 2 : ℝ) ⟨by norm_num, by norm_num⟩).integral_eq_one 2 (by norm_num)

/-- Pointwise separation from the degenerate polynomial family
`Q_α(x, t) = t^(-1/α) (α / 2) (1 + |x t^(-1/α)|)^(-(1 + α))`: at `α = 1, x = 0, t = 1`,
`stableHeatKernel 1` evaluates to `1 / π`, which differs from `1 / 2`. The structural separation
is `fourier_stableKernel_eq` (the Fourier transform is `exp (-t |2π ξ|^α)`), which `Q_α` does not
satisfy; this example only checks one point value. -/
example :
    (stableHeatKernel 1 fractionalExponent_one).P 0 1 ≠
      (1 : ℝ) ^ (-1 / (1 : ℝ)) * ((1 : ℝ) / 2) *
        (1 + |(0 : ℝ) * (1 : ℝ) ^ (-1 / (1 : ℝ))|) ^ (-(1 + (1 : ℝ))) := by
  rw [stableHeatKernel_one_eq_cauchy 0 one_pos]
  change 1 / (π * (1 ^ 2 + 0 ^ 2)) ≠
    (1 : ℝ) ^ (-1 / (1 : ℝ)) * ((1 : ℝ) / 2) *
      (1 + |(0 : ℝ) * (1 : ℝ) ^ (-1 / (1 : ℝ))|) ^ (-(1 + (1 : ℝ)))
  have h1 : (1 : ℝ) / (π * (1 ^ 2 + 0 ^ 2)) = 1 / π := by ring_nf
  have h2 :
      (1 : ℝ) ^ (-1 / (1 : ℝ)) * ((1 : ℝ) / 2) *
          (1 + |(0 : ℝ) * (1 : ℝ) ^ (-1 / (1 : ℝ))|) ^ (-(1 + (1 : ℝ))) = 1 / 2 := by
    norm_num
  rw [h1, h2]
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  intro heq
  have hinv : π = 2 := by
    have hpi0 : π ≠ 0 := Real.pi_pos.ne'
    have h20 : (2 : ℝ) ≠ 0 := by norm_num
    field_simp at heq
    exact heq.symm
  linarith

/-- Unconditional instantiation of `fracHeatConv_nonneg` and `reflectedHeatKernel_bounds`
for any `0 < α < 2` using `stableHeatKernel α hα`. -/
example {α : ℝ} (hα : FractionalExponent α) (x : ℝ) :
    0 ≤ fracHeatConv (stableHeatKernel α hα) 1 (fun _ => 1) x ∧
      0 ≤ reflectedHeatKernel (stableHeatKernel α hα) 1 2 1 ∧
      reflectedHeatKernel (stableHeatKernel α hα) 1 2 1 ≤
        (stableHeatKernel α hα).P (1 - 2) 1 :=
  ⟨fracHeatConv_nonneg (stableHeatKernel α hα) one_pos (fun _ => zero_le_one) x,
    (reflectedHeatKernel_bounds (stableHeatKernel α hα) one_pos (by norm_num) one_pos).1,
    (reflectedHeatKernel_bounds (stableHeatKernel α hα) one_pos (by norm_num) one_pos).2⟩

/-- `C₀(ℝ, ℝ)` packaging (`thm:kernelprop` (1)): `stableKernelC0Map` agrees pointwise with
`stableKernel`, evaluates to `1 / π` at `α = 1, x = 0, t = 1`, and vanishes at infinity. -/
example :
    (stableKernelC0Map 1 1 fractionalExponent_one one_pos) 0 = 1 / π ∧
      Filter.Tendsto (stableKernelC0Map 1 1 fractionalExponent_one one_pos)
        (Filter.cocompact ℝ) (nhds 0) := by
  refine ⟨?_, tendsto_stableKernel_cocompact one_pos (by norm_num) one_pos⟩
  change stableKernel 1 0 1 = 1 / π
  change (stableHeatKernel 1 fractionalExponent_one).P 0 1 = 1 / π
  rw [stableHeatKernel_one_eq_cauchy 0 one_pos]
  change 1 / (π * (1 ^ 2 + 0 ^ 2)) = 1 / π
  ring_nf

end

end FracLapTest
