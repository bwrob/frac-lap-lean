/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.PointwiseEquivalence
public import FracLap.WholeLine.SobolevEquivalence
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# FracLapTest.SobolevEquivalenceTest

Anti-vacuity witnesses, closed-form symbol bounds, and concrete instantiations for
`FracLap.WholeLine.SobolevEquivalence`.
-/

namespace FracLapTest

open FracLap FourierTransform MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap ComplexInnerProductSpace

@[expose] public section

/-- Non-trivial smooth compactly supported Schwartz function in `𝓢(ℝ, ℂ)`. -/
noncomputable def sobolevBumpC : 𝓢(ℝ, ℂ) :=
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  (b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp b.contDiff)

/-- Smooth bump belongs to `MemFourierSobolev (α / 2)` (`H^(α/2)(ℝ)`), has finite Gagliardo
energy, and lies in Mathlib's `MemSobolev (α / 2) 2`. -/
example {α : ℝ} (hα : FractionalExponent α) :
    MemFourierSobolev (α / 2) (sobolevBumpC.toLp 2 volume : L2C) ∧
      gagliardoEnergyC α (sobolevBumpC.toLp 2 volume : L2C) < ∞ ∧
      MemSobolev (α / 2) 2 ((sobolevBumpC.toLp 2 volume : L2C) : 𝓢'(ℝ, ℂ)) := by
  have hfin : gagliardoEnergyC α (sobolevBumpC.toLp 2 volume : L2C) < ∞ :=
    gagliardoEnergyC_schwartz_lt_top hα sobolevBumpC
  exact ⟨(gagliardoEnergyC_lt_top_iff_memFourierSobolev hα _).mp hfin, hfin,
    (gagliardoEnergyC_lt_top_iff_memSobolev hα _).mp hfin⟩

/-- Nonnegativity, symmetry, and Friedrichs pairing verified on `sobolevBumpC` and
`gagliardoTentRestricted` / `GagliardoSpace α`. -/
example {α : ℝ} (hα : FractionalExponent α) :
    0 ≤ (@inner ℂ L2C _ (-((fracLapSemigroup α).generator
      ⟨(sobolevBumpC.toLp 2 volume : L2C),
        fracLapSemigroup_schwartz_mem_generatorDomain hα sobolevBumpC⟩))
      (sobolevBumpC.toLp 2 volume : L2C)).re ∧
    DenseRange (gagliardoL2Part α) ∧
    DenseRange (fun u : RestrictedGagliardoSpace α =>
      (⟨gagliardoL2Part α u.1, u.2⟩ : ↥l2ZeroSubmodule)) :=
  ⟨(inner_neg_generator_fracLapSemigroup_re_nonneg α _).1,
    denseRange_gagliardoL2Part hα,
    denseRange_restrictedGagliardoL2Zero hα⟩

/-- Isometric identification `l2ZeroIsoIoi` preserves norms of nonzero half-line functions:
the tent function extends to a nonzero element of `l2ZeroSubmodule`. -/
example : ∃ u : ↥l2ZeroSubmodule, u ≠ 0 ∧ ‖l2ZeroIsoIoi u‖ = ‖u‖ := by
  let t := gagliardoTentRestricted (α := 1) fractionalExponent_one
  refine ⟨⟨gagliardoL2Part 1 t.1, t.2⟩, ?_, l2ZeroIsoIoi.norm_map _⟩
  intro hzero
  have h0 : gagliardoL2Part 1 t.1 = 0 := congrArg Subtype.val hzero
  have h1 : gagliardoTentL2 = 0 := h0
  have h2 : (gagliardoTent : ℝ → ℝ) =ᵐ[volume] fun _ => 0 := by
    filter_upwards [memLp_gagliardoTent.coeFn_toLp, Lp.coeFn_zero ℝ 2 volume] with y hy hz
    have hy' : (gagliardoTentL2 : ℝ → ℝ) y = gagliardoTent y := hy
    rw [← hy', h1]
    exact hz
  have h4 := congrFun
    ((Continuous.ae_eq_iff_eq (volume : Measure ℝ) continuous_gagliardoTent
      continuous_const).mp h2) 1
  have h5 : gagliardoTent 1 = 1 := by simp [gagliardoTent]
  rw [h5] at h4
  exact one_ne_zero h4

end

end FracLapTest
