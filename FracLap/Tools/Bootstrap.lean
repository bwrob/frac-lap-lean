/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Order.IntermediateValue

/-!
# FracLap.Tools.Bootstrap

The continuity ("bootstrap") lemma of Karch--Droniou--Imbert (`lem:scat` in the fractal
Hamilton--Jacobi paper): if a continuous nonnegative function satisfies `g ≤ A + B g^p` with
`A^(p-1) B < p⁻¹ (1 - p⁻¹)^(p-1)` and starts below the threshold `x₀ = (p B)^(-1/(p-1))`, then it
never crosses the forbidden gap and `g ≤ A p / (p - 1)` for all times.

- `bootstrap_threshold_pos`: the gap condition `A < x₀ (1 - 1/p)`.
- `bootstrap_le`: `g ≤ x₀` on an order-connected set containing a time with `g ≤ x₀`.
- `bootstrap_bound`: the improved bound `g ≤ A p / (p - 1)`.
-/

namespace FracLap

open Set

@[expose] public section

/-- The threshold `x₀ = (p B)^(-1/(p-1))` of the bootstrap lemma. -/
noncomputable def bootstrapThreshold (B p : ℝ) : ℝ := (p * B) ^ (-1 / (p - 1))

/-- `B x₀^(p-1) = 1 / p`. -/
theorem bootstrapThreshold_pow {B p : ℝ} (hB : 0 < B) (hp : 1 < p) :
    bootstrapThreshold B p ^ (p - 1) = (p * B)⁻¹ := by
  have hpB : 0 < p * B := mul_pos (by linarith) hB
  unfold bootstrapThreshold
  rw [← Real.rpow_mul hpB.le]
  have : -1 / (p - 1) * (p - 1) = -1 := by
    field_simp
  rw [this, Real.rpow_neg_one]

/-- The smallness condition `A^(p-1) B < p⁻¹ (1 - p⁻¹)^(p-1)` says exactly that the function
`x ↦ x - A - B x^p` is positive at the threshold: `A < x₀ (1 - 1/p)`. -/
theorem bootstrap_threshold_pos {A B p : ℝ} (hA : 0 < A) (hB : 0 < B) (hp : 1 < p)
    (hsmall : A ^ (p - 1) * B < p⁻¹ * (1 - p⁻¹) ^ (p - 1)) :
    A < bootstrapThreshold B p * (1 - p⁻¹) := by
  have hp1 : 0 < p - 1 := by linarith
  have hp0 : 0 < p := by linarith
  have hx0 : 0 < bootstrapThreshold B p := Real.rpow_pos_of_pos (mul_pos hp0 hB) _
  have hq : 0 < 1 - p⁻¹ := by
    rw [sub_pos]
    exact inv_lt_one_of_one_lt₀ hp
  have hpow := bootstrapThreshold_pow hB hp
  have hlt : A ^ (p - 1) < (bootstrapThreshold B p * (1 - p⁻¹)) ^ (p - 1) := by
    rw [Real.mul_rpow hx0.le hq.le, hpow]
    have hBpos : 0 < B := hB
    calc A ^ (p - 1) = (A ^ (p - 1) * B) / B := by field_simp
      _ < (p⁻¹ * (1 - p⁻¹) ^ (p - 1)) / B := by gcongr
      _ = (p * B)⁻¹ * (1 - p⁻¹) ^ (p - 1) := by field_simp
  exact (Real.rpow_lt_rpow_iff hA.le (mul_pos hx0 hq).le hp1).mp hlt

/-- **The solution never crosses the forbidden gap**: on an order-connected set `J`, if `g` is
continuous, satisfies `g ≤ A + B g^p`, and is at most the threshold `x₀` at one time, then
`g ≤ x₀` everywhere on `J`. -/
theorem bootstrap_le {g : ℝ → ℝ} {J : Set ℝ} (hJ : J.OrdConnected) (hg : ContinuousOn g J)
    {A B p : ℝ} (hA : 0 < A) (hB : 0 < B) (hp : 1 < p)
    (hsmall : A ^ (p - 1) * B < p⁻¹ * (1 - p⁻¹) ^ (p - 1))
    (hineq : ∀ t ∈ J, g t ≤ A + B * g t ^ p)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) (h0 : g t₀ ≤ bootstrapThreshold B p) :
    ∀ t ∈ J, g t ≤ bootstrapThreshold B p := by
  intro t ht
  by_contra hcon
  replace hcon := not_le.mp hcon
  set x₀ := bootstrapThreshold B p with hx₀
  have hp0 : 0 < p := by linarith
  have hx0 : 0 < x₀ := Real.rpow_pos_of_pos (mul_pos hp0 hB) _
  have hpos := bootstrap_threshold_pos hA hB hp hsmall
  -- `x₀` is excluded: `x₀ > A + B x₀^p`
  have hbad : A + B * x₀ ^ p < x₀ := by
    have h1 : x₀ ^ p = x₀ * x₀ ^ (p - 1) := by
      rw [← Real.rpow_one_add' hx0.le (by linarith)]
      congr 1
      ring
    have e : B * (x₀ * (p * B)⁻¹) = x₀ * p⁻¹ := by field_simp
    have hpos' : A < x₀ * (1 - p⁻¹) := hpos
    have e2 : x₀ * (1 - p⁻¹) = x₀ - x₀ * p⁻¹ := by ring
    rw [h1, bootstrapThreshold_pow hB hp, e]
    linarith
  -- intermediate value on the segment between `t₀` and `t`
  have hsub : uIcc t₀ t ⊆ J := hJ.uIcc_subset ht₀ ht
  have hcont : ContinuousOn g (uIcc t₀ t) := hg.mono hsub
  have hivt : x₀ ∈ g '' uIcc t₀ t := by
    have := intermediate_value_uIcc hcont
    exact this (Set.mem_uIcc.mpr (Or.inl ⟨h0, hcon.le⟩))
  obtain ⟨s, hs, hgs⟩ := hivt
  have := hineq s (hsub hs)
  rw [hgs] at this
  linarith

/-- **Karch--Droniou--Imbert bootstrap lemma.** Under the hypotheses of `bootstrap_le`,
`g t ≤ A p / (p - 1)` for all `t ∈ J`. -/
theorem bootstrap_bound {g : ℝ → ℝ} {J : Set ℝ} (hJ : J.OrdConnected) (hg : ContinuousOn g J)
    {A B p : ℝ} (hA : 0 < A) (hB : 0 < B) (hp : 1 < p)
    (hsmall : A ^ (p - 1) * B < p⁻¹ * (1 - p⁻¹) ^ (p - 1))
    (hineq : ∀ t ∈ J, g t ≤ A + B * g t ^ p) (hg0 : ∀ t ∈ J, 0 ≤ g t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) (h0 : g t₀ ≤ bootstrapThreshold B p) :
    ∀ t ∈ J, g t ≤ A * p / (p - 1) := by
  intro t ht
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hx0 : 0 < bootstrapThreshold B p := Real.rpow_pos_of_pos (mul_pos hp0 hB) _
  have hle := bootstrap_le hJ hg hA hB hp hsmall hineq ht₀ h0 t ht
  have hgt := hg0 t ht
  have hpow : B * g t ^ (p - 1) ≤ p⁻¹ := by
    have h1 : g t ^ (p - 1) ≤ bootstrapThreshold B p ^ (p - 1) :=
      Real.rpow_le_rpow hgt hle hp1.le
    rw [bootstrapThreshold_pow hB hp] at h1
    calc B * g t ^ (p - 1) ≤ B * (p * B)⁻¹ := mul_le_mul_of_nonneg_left h1 hB.le
      _ = p⁻¹ := by field_simp
  have hmain := hineq t ht
  have h2 : B * g t ^ p = (B * g t ^ (p - 1)) * g t := by
    have e : g t ^ p = g t ^ (p - 1) * g t := by
      conv_lhs => rw [show p = (p - 1) + 1 by ring]
      rw [Real.rpow_add' hgt (by linarith), Real.rpow_one]
    rw [e]
    ring
  have h3 : B * g t ^ p ≤ g t / p := by
    rw [h2]
    calc (B * g t ^ (p - 1)) * g t ≤ p⁻¹ * g t := mul_le_mul_of_nonneg_right hpow hgt
      _ = g t / p := by ring
  rw [le_div_iff₀ hp1]
  have : g t * (1 - p⁻¹) ≤ A := by
    have : g t ≤ A + g t / p := by linarith
    nlinarith [this, inv_eq_one_div p, mul_inv_cancel₀ hp0.ne']
  have e : g t * (p - 1) = p * (g t * (1 - p⁻¹)) := by
    field_simp
  rw [e]
  nlinarith

end

end FracLap
