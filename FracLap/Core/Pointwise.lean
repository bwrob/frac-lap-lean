/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# FracLap.Core.Pointwise

Core pointwise definitions and properties of the 1D fractional Laplacian
`(-Δ)^(α / 2)` for `α ∈ (0, 2)`:
- `FractionalExponent α`: exponent range `0 < α ∧ α < 2`.
- `fracLapConstant α`: explicit normalizing constant
  `C(α) = 2^(α - 1) α Γ((1 + α) / 2) / (√π Γ(1 - α / 2))`.
- `secondDiff u x y`: second-order difference `u (x + y) + u (x - y) - 2 u x`.
- `fracLapSecondDiff α u x`: weighted second-difference integral representation
  `-(C(α) / 2) ∫ y, (u(x + y) + u(x - y) - 2 u(x)) / |y|^(1 + α)`.
- `oddExt u`: antisymmetric extension of a function `u : ℝ → ℝ` from `(0, ∞)` to `ℝ`.
- `IsOddFunc f` and `IsEvenFunc f`: pointwise parity predicates and composition properties.
- `reflectedFracLapSecondDiff α u x`: reflected half-line fractional Laplacian
  `(-Δ̃)^(α / 2) u(x) = (-Δ)^(α / 2) (oddExt u)(x)`.
- `reflectedKernel α x y`: reflected singular kernel
  `K_α(x, y) = |x - y|^(-(1 + α)) - |x + y|^(-(1 + α))` and its strict positivity
  for `x, y > 0`.
-/

namespace FracLap

open MeasureTheory Real

@[expose] public section

/-- A fractional Laplacian exponent `α ∈ (0, 2)` corresponding to operator
`(-Δ)^(α / 2)` of fractional order `s = α / 2 ∈ (0, 1)`. -/
def FractionalExponent (α : ℝ) : Prop :=
  0 < α ∧ α < 2

/-- The classical square-root Laplacian exponent `α = 1` lies in `(0, 2)`. -/
theorem fractionalExponent_one : FractionalExponent (1 : ℝ) := by
  constructor <;> norm_num

/-- If `α ∈ (0, 2)`, then `0 < (1 + α) / 2`. -/
theorem half_one_add_pos {α : ℝ} (hα : FractionalExponent α) : 0 < (1 + α) / 2 := by
  have h0 : 0 < α := hα.1
  linarith

/-- If `α ∈ (0, 2)`, then `0 < 1 - α / 2`. -/
theorem one_sub_half_pos {α : ℝ} (hα : FractionalExponent α) : 0 < 1 - α / 2 := by
  have h2 : α < 2 := hα.2
  linarith

/-- Explicit 1D fractional Laplacian normalizing constant
`C(α) = 2^(α - 1) α Γ((1 + α) / 2) / (√π Γ(1 - α / 2))`. -/
noncomputable def fracLapConstant (α : ℝ) : ℝ :=
  (2 : ℝ) ^ (α - 1) * α * Gamma ((1 + α) / 2) / (sqrt π * Gamma (1 - α / 2))

/-- For every `α ∈ (0, 2)`, the normalizing constant `C(α)` is strictly positive. -/
theorem fracLapConstant_pos {α : ℝ} (hα : FractionalExponent α) :
    0 < fracLapConstant α := by
  unfold fracLapConstant
  have h_pow : 0 < (2 : ℝ) ^ (α - 1) := by positivity
  have h_alpha : 0 < α := hα.1
  have h_g1 : 0 < Gamma ((1 + α) / 2) := Gamma_pos_of_pos (half_one_add_pos hα)
  have h_g2 : 0 < Gamma (1 - α / 2) := Gamma_pos_of_pos (one_sub_half_pos hα)
  have h_pi : 0 < sqrt π := sqrt_pos.mpr pi_pos
  positivity

private theorem continuousAt_real_Gamma_of_pos {s : ℝ} (hs : 0 < s) :
    ContinuousAt Real.Gamma s := by
  have hne : ∀ m : ℕ, (s : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hre := congr_arg Complex.re hm
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  exact (Complex.continuous_re.continuousAt.comp
    (Complex.continuousAt_Gamma (s : ℂ) hne)).comp Complex.continuous_ofReal.continuousAt

/-- As `α → 2⁻`, the Euler Gamma factor `Γ(1 - α / 2)` diverges to `+∞`. -/
theorem tendsto_gamma_one_sub_half_two :
    Filter.Tendsto (fun α : ℝ => Gamma (1 - α / 2)) (nhdsWithin 2 (Set.Iio 2)) Filter.atTop := by
  have h_eq : (fun α : ℝ => Gamma (1 - α / 2)) =ᶠ[nhdsWithin 2 (Set.Iio 2)]
      fun α => Gamma (2 - α / 2) * (1 - α / 2)⁻¹ := by
    filter_upwards [self_mem_nhdsWithin] with α (hα : α < 2)
    have h1 : (1 - α / 2 : ℝ) ≠ 0 := by linarith
    have hsum : (1 - α / 2 : ℝ) + 1 = 2 - α / 2 := by ring
    rw [eq_mul_inv_iff_mul_eq₀ h1, mul_comm, ← Gamma_add_one h1, hsum]
  refine Filter.Tendsto.congr' h_eq.symm ?_
  have hnum : Filter.Tendsto (fun α : ℝ => Gamma (2 - α / 2))
      (nhdsWithin 2 (Set.Iio 2)) (nhds (1 : ℝ)) := by
    have hlin : Filter.Tendsto (fun α : ℝ => (2 - α / 2 : ℝ))
        (nhdsWithin 2 (Set.Iio 2)) (nhds 1) := by
      have h : Filter.Tendsto (fun α : ℝ => (2 - α / 2 : ℝ)) (nhds 2) (nhds (2 - 2 / 2 : ℝ)) :=
        (continuous_const.sub (continuous_id.div_const 2)).continuousAt.tendsto
      norm_num at h
      exact h.mono_left nhdsWithin_le_nhds
    have hc := ((continuousAt_real_Gamma_of_pos one_pos).tendsto.comp hlin)
    simpa only [Function.comp_def, Gamma_one] using hc
  have hden : Filter.Tendsto (fun α : ℝ => (1 - α / 2 : ℝ))
      (nhdsWithin 2 (Set.Iio 2)) (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : Filter.Tendsto (fun α : ℝ => (1 - α / 2 : ℝ)) (nhds 2) (nhds (1 - 2 / 2 : ℝ)) :=
        (continuous_const.sub (continuous_id.div_const 2)).continuousAt.tendsto
      norm_num at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with α (hα : α < 2)
      change (0 : ℝ) < 1 - α / 2
      linarith
  exact hnum.pos_mul_atTop zero_lt_one (tendsto_inv_nhdsGT_zero.comp hden)

/-- **Endpoint limit as `α → 0⁺`** (`prop:constantexplicit`):
`lim_{α → 0⁺} C(α) = 0`. -/
theorem tendsto_fracLapConstant_zero :
    Filter.Tendsto fracLapConstant (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hpow : Filter.Tendsto (fun α : ℝ => (2 : ℝ) ^ (α - 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 : ℝ) ^ ((0 : ℝ) - 1))) :=
    ((Continuous.rpow continuous_const (continuous_id.sub continuous_const)
      (fun _ => Or.inl two_ne_zero)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hid : Filter.Tendsto (fun α : ℝ => α) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hg1 : Filter.Tendsto (fun α : ℝ => Gamma ((1 + α) / 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Gamma (1 / 2))) := by
    have hlin : Filter.Tendsto (fun α : ℝ => ((1 + α) / 2 : ℝ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) := by
      have h : Filter.Tendsto (fun α : ℝ => ((1 + α) / 2 : ℝ))
          (nhds 0) (nhds ((1 + (0 : ℝ)) / 2 : ℝ)) :=
        ((continuous_const.add continuous_id).div_const 2).continuousAt.tendsto
      norm_num at h
      exact h.mono_left nhdsWithin_le_nhds
    exact (continuousAt_real_Gamma_of_pos (by norm_num)).tendsto.comp hlin
  have hg2 : Filter.Tendsto (fun α : ℝ => Gamma (1 - α / 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hlin : Filter.Tendsto (fun α : ℝ => (1 - α / 2 : ℝ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have h : Filter.Tendsto (fun α : ℝ => (1 - α / 2 : ℝ)) (nhds 0) (nhds (1 - 0 / 2 : ℝ)) :=
        (continuous_const.sub (continuous_id.div_const 2)).continuousAt.tendsto
      norm_num at h
      exact h.mono_left nhdsWithin_le_nhds
    have hc := (continuousAt_real_Gamma_of_pos one_pos).tendsto.comp hlin
    simpa only [Function.comp_def, Gamma_one] using hc
  have hden_ne : sqrt π * 1 ≠ 0 := by positivity
  have hmain : Filter.Tendsto fracLapConstant (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((2 : ℝ) ^ ((0 : ℝ) - 1) * 0 * Gamma (1 / 2) / (sqrt π * 1))) :=
    (((hpow.mul hid).mul hg1).div (tendsto_const_nhds.mul hg2) hden_ne)
  simpa only [mul_zero, zero_mul, zero_div] using hmain

/-- **Endpoint limit as `α → 2⁻`** (`prop:constantexplicit`):
`lim_{α → 2⁻} C(α) = 0`. -/
theorem tendsto_fracLapConstant_two :
    Filter.Tendsto fracLapConstant (nhdsWithin 2 (Set.Iio 2)) (nhds 0) := by
  have h_eq : fracLapConstant =ᶠ[nhdsWithin 2 (Set.Iio 2)]
      fun α => (2 : ℝ) ^ (α - 1) * α * (1 - α / 2) * Gamma ((1 + α) / 2) /
        (sqrt π * Gamma (2 - α / 2)) := by
    filter_upwards [self_mem_nhdsWithin] with α (hα : α < 2)
    have h1 : (1 - α / 2 : ℝ) ≠ 0 := by linarith
    have hsum : (1 - α / 2 : ℝ) + 1 = 2 - α / 2 := by ring
    unfold fracLapConstant
    rw [show Gamma (2 - α / 2) = (1 - α / 2) * Gamma (1 - α / 2) from
      hsum ▸ Gamma_add_one h1]
    field_simp
  refine Filter.Tendsto.congr' h_eq.symm ?_
  have hpow : Filter.Tendsto (fun α : ℝ => (2 : ℝ) ^ (α - 1))
      (nhdsWithin 2 (Set.Iio 2)) (nhds ((2 : ℝ) ^ ((2 : ℝ) - 1))) :=
    ((Continuous.rpow continuous_const (continuous_id.sub continuous_const)
      (fun _ => Or.inl two_ne_zero)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hid : Filter.Tendsto (fun α : ℝ => α) (nhdsWithin 2 (Set.Iio 2)) (nhds 2) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hsub : Filter.Tendsto (fun α : ℝ => (1 - α / 2 : ℝ))
      (nhdsWithin 2 (Set.Iio 2)) (nhds 0) := by
    have h : Filter.Tendsto (fun α : ℝ => (1 - α / 2 : ℝ)) (nhds 2) (nhds (1 - 2 / 2 : ℝ)) :=
      (continuous_const.sub (continuous_id.div_const 2)).continuousAt.tendsto
    norm_num at h
    exact h.mono_left nhdsWithin_le_nhds
  have hg1 : Filter.Tendsto (fun α : ℝ => Gamma ((1 + α) / 2))
      (nhdsWithin 2 (Set.Iio 2)) (nhds (Gamma (3 / 2))) := by
    have hlin : Filter.Tendsto (fun α : ℝ => ((1 + α) / 2 : ℝ))
        (nhdsWithin 2 (Set.Iio 2)) (nhds (3 / 2)) := by
      have h : Filter.Tendsto (fun α : ℝ => ((1 + α) / 2 : ℝ))
          (nhds 2) (nhds ((1 + (2 : ℝ)) / 2 : ℝ)) :=
        ((continuous_const.add continuous_id).div_const 2).continuousAt.tendsto
      norm_num at h
      exact h.mono_left nhdsWithin_le_nhds
    exact (continuousAt_real_Gamma_of_pos (by norm_num)).tendsto.comp hlin
  have hg2 : Filter.Tendsto (fun α : ℝ => Gamma (2 - α / 2))
      (nhdsWithin 2 (Set.Iio 2)) (nhds 1) := by
    have hlin : Filter.Tendsto (fun α : ℝ => (2 - α / 2 : ℝ))
        (nhdsWithin 2 (Set.Iio 2)) (nhds 1) := by
      have h : Filter.Tendsto (fun α : ℝ => (2 - α / 2 : ℝ)) (nhds 2) (nhds (2 - 2 / 2 : ℝ)) :=
        (continuous_const.sub (continuous_id.div_const 2)).continuousAt.tendsto
      norm_num at h
      exact h.mono_left nhdsWithin_le_nhds
    have hc := (continuousAt_real_Gamma_of_pos one_pos).tendsto.comp hlin
    simpa only [Function.comp_def, Gamma_one] using hc
  have hden_ne : sqrt π * 1 ≠ 0 := by positivity
  have hmain : Filter.Tendsto
      (fun α : ℝ => (2 : ℝ) ^ (α - 1) * α * (1 - α / 2) * Gamma ((1 + α) / 2) /
        (sqrt π * Gamma (2 - α / 2)))
      (nhdsWithin 2 (Set.Iio 2))
      (nhds ((2 : ℝ) ^ ((2 : ℝ) - 1) * 2 * 0 * Gamma (3 / 2) / (sqrt π * 1))) :=
    ((((hpow.mul hid).mul hsub).mul hg1).div (tendsto_const_nhds.mul hg2) hden_ne)
  simpa only [mul_zero, zero_mul, zero_div] using hmain

/-- The symmetric second-order difference `u(x + y) + u(x - y) - 2 u(x)`. -/
def secondDiff (u : ℝ → ℝ) (x y : ℝ) : ℝ :=
  u (x + y) + u (x - y) - 2 * u x

/-- At a global maximum `x₀` of `u : ℝ → ℝ`, the second-order difference is nonpositive
for all jump sizes `y ∈ ℝ`. -/
theorem secondDiff_nonpos_of_isMax (u : ℝ → ℝ) (x₀ y : ℝ) (hmax : ∀ z : ℝ, u z ≤ u x₀) :
    secondDiff u x₀ y ≤ 0 := by
  unfold secondDiff
  have h1 : u (x₀ + y) ≤ u x₀ := hmax (x₀ + y)
  have h2 : u (x₀ - y) ≤ u x₀ := hmax (x₀ - y)
  linarith

/-- Pointwise fractional Laplacian `(-Δ)^(α / 2) u(x)` defined via the weighted
second-order difference integral without principal value. -/
noncomputable def fracLapSecondDiff (α : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(fracLapConstant α / 2) * ∫ y : ℝ, secondDiff u x y / |y| ^ (1 + α)

/-- A function `f : ℝ → ℝ` is odd if `f (-x) = -f x` for all `x ∈ ℝ`. -/
def IsOddFunc (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, f (-x) = -f x

/-- A function `f : ℝ → ℝ` is even if `f (-x) = f x` for all `x ∈ ℝ`. -/
def IsEvenFunc (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, f (-x) = f x

/-- Any odd function `f : ℝ → ℝ` vanishes at the origin: `f 0 = 0`. -/
theorem IsOddFunc.map_zero {f : ℝ → ℝ} (hf : IsOddFunc f) : f 0 = 0 := by
  have h0 : f (-0) = -f 0 := hf 0
  simp only [neg_zero] at h0
  linarith

/-- Antisymmetric (odd) extension `ũ : ℝ → ℝ` of a function `u : ℝ → ℝ` defined on `(0, ∞)`. -/
noncomputable def oddExt (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 < x then u x else if x < 0 then -u (-x) else 0

/-- The antisymmetric extension `oddExt u` vanishes at `0`. -/
@[simp]
theorem oddExt_zero (u : ℝ → ℝ) : oddExt u 0 = 0 := by
  simp [oddExt]

/-- The antisymmetric extension `oddExt u` agrees with `u` on `(0, ∞)`. -/
theorem oddExt_of_pos (u : ℝ → ℝ) {x : ℝ} (hx : 0 < x) : oddExt u x = u x := by
  simp [oddExt, hx]

/-- The antisymmetric extension `oddExt u` equals `-u(-x)` on `(-∞, 0)`. -/
theorem oddExt_of_neg (u : ℝ → ℝ) {x : ℝ} (hx : x < 0) : oddExt u x = -u (-x) := by
  have hnot : ¬ 0 < x := not_lt.mpr (le_of_lt hx)
  simp [oddExt, hnot, hx]

/-- For every `u : ℝ → ℝ`, `oddExt u` is an odd function on `ℝ`. -/
theorem isOddFunc_oddExt (u : ℝ → ℝ) : IsOddFunc (oddExt u) := by
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hpos : 0 < -x := neg_pos.mpr hx
    rw [oddExt_of_pos u hpos, oddExt_of_neg u hx, neg_neg]
  · simp [oddExt]
  · have hneg : -x < 0 := neg_lt_zero.mpr hx
    rw [oddExt_of_neg u hneg, oddExt_of_pos u hx, neg_neg]

/-- If `u ≥ 0` on `(0, ∞)` and `x₀ > 0` maximizes `u` on `(0, ∞)`, then `x₀` is a global
maximum of `oddExt u` on all of `ℝ`. -/
theorem oddExt_le_of_nonneg_of_isMaxOn_Ioi {u : ℝ → ℝ} {x₀ : ℝ}
    (hx₀ : 0 < x₀) (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ u x)
    (hmax : ∀ x : ℝ, 0 < x → u x ≤ u x₀) (z : ℝ) :
    oddExt u z ≤ oddExt u x₀ := by
  rw [oddExt_of_pos u hx₀]
  have hu0 : 0 ≤ u x₀ := hnonneg x₀ hx₀
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · rw [oddExt_of_neg u hz]
    have hpos : 0 < -z := neg_pos.mpr hz
    have h1 : 0 ≤ u (-z) := hnonneg (-z) hpos
    linarith
  · rw [oddExt_zero]
    exact hu0
  · rw [oddExt_of_pos u hz]
    exact hmax z hz

/-- Reflected half-line fractional Laplacian `(-Δ̃)^(α / 2) u(x)` defined via the whole-line
fractional Laplacian applied to the antisymmetric extension `oddExt u`. -/
noncomputable def reflectedFracLapSecondDiff (α : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  fracLapSecondDiff α (oddExt u) x

/-- The reflected half-line singular kernel
`K_α(x, y) = |x - y|^(-(1 + α)) - |x + y|^(-(1 + α))`. -/
noncomputable def reflectedKernel (α x y : ℝ) : ℝ :=
  1 / |x - y| ^ (1 + α) - 1 / |x + y| ^ (1 + α)

/-- For `x, y > 0` with `x ≠ y` and `α ∈ (0, 2)`, the reflected singular kernel is
strictly positive: `0 < K_α(x, y)`. -/
theorem reflectedKernel_pos {α x y : ℝ} (hα : FractionalExponent α)
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    0 < reflectedKernel α x y := by
  unfold reflectedKernel
  have h1a : 0 < 1 + α := by
    have h0 : 0 < α := hα.1
    linarith
  have hdiff_ne : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hdiff_pos : 0 < |x - y| := abs_pos.mpr hdiff_ne
  have hsum_pos : 0 < x + y := add_pos hx hy
  have hlt : |x - y| < |x + y| := by
    rw [abs_of_pos hsum_pos, abs_lt]
    constructor <;> linarith
  have hrpow : |x - y| ^ (1 + α) < |x + y| ^ (1 + α) :=
    rpow_lt_rpow (le_of_lt hdiff_pos) hlt h1a
  have hpow_pos : 0 < |x - y| ^ (1 + α) := rpow_pos_of_pos hdiff_pos (1 + α)
  have hdiv : 1 / |x + y| ^ (1 + α) < 1 / |x - y| ^ (1 + α) :=
    one_div_lt_one_div_of_lt hpow_pos hrpow
  linarith

end

end FracLap
