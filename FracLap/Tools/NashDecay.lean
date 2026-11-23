/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# FracLap.Tools.NashDecay

The ODE comparison step of the Carlen--Kusuoka--Stroock argument (Nash inequality implies
ultracontractive decay).

- `ode_decay`: if `u ≥ 0` is continuous on `[0, ∞)`, differentiable on `(0, ∞)` and
  `u′ ≤ -c u^(1+α)` with `c, α > 0`, then `u(t) ≤ (c α t)^(-1/α)` for `t > 0`.
- `nash_decay`: if `u′ = -2 E`, with `E` controlled below by the Nash inequality
  `u^(1+α) ≤ K E M^(2α)` (`M` an `L¹` bound preserved by the flow), then
  `u(t) ≤ (K M^(2α) / (2 α t))^(1/α)`; for `u = ‖T_t f‖₂²` this is the `L¹ → L²` decay
  `‖T_t f‖₂ ≲ t^(-1/(2α)) ‖f‖₁`.
-/

namespace FracLap

open Set

@[expose] public section

/-- **ODE comparison.** If `u ≥ 0` is continuous on `[0, ∞)`, differentiable on `(0, ∞)` with
`u′ ≤ -c u^(1+α)`, then `u(t)^(-α) ≥ c α t` whenever `u(t) > 0`, hence `u(t) ≤ (c α t)^(-1/α)`. -/
theorem ode_decay {u u' : ℝ → ℝ} {c α : ℝ} (hc : 0 < c) (hα : 0 < α)
    (hcont : ContinuousOn u (Ici 0)) (hnn : ∀ t, 0 ≤ t → 0 ≤ u t)
    (hd : ∀ t, 0 < t → HasDerivAt u (u' t) t)
    (hineq : ∀ t, 0 < t → u' t ≤ -c * u t ^ (1 + α)) :
    ∀ t, 0 < t → u t ≤ (c * α * t) ^ (-(1 / α)) := by
  intro t ht
  have hA : 0 < c * α * t := by positivity
  by_cases hu0 : u t = 0
  · rw [hu0]; exact (Real.rpow_nonneg hA.le _)
  have hupos : 0 < u t := lt_of_le_of_ne (hnn t ht.le) (Ne.symm hu0)
  -- `u` is antitone on `[0, ∞)`
  have hanti : AntitoneOn u (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont ?_ ?_
    · rw [interior_Ici]
      exact fun s hs => (hd s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro s hs
      rw [(hd s hs).deriv]
      refine (hineq s hs).trans ?_
      have : 0 ≤ u s ^ (1 + α) := Real.rpow_nonneg (hnn s hs.le) _
      nlinarith
  have hpos : ∀ s ∈ Icc 0 t, 0 < u s := fun s hs =>
    lt_of_lt_of_le hupos (hanti (mem_Ici.2 hs.1) (mem_Ici.2 ht.le) hs.2)
  -- `v = u^(-α)` grows at least linearly
  set v : ℝ → ℝ := fun s => u s ^ (-α) with hv
  have hvcont : ContinuousOn v (Icc 0 t) := by
    refine ContinuousOn.rpow_const (hcont.mono Icc_subset_Ici_self) fun s hs =>
      Or.inl (hpos s hs).ne'
  have hvder : ∀ s ∈ Ioo 0 t, HasDerivAt (fun s => v s - c * α * s)
      ((u' s * (-α) * u s ^ (-α - 1)) - c * α * 1) s := by
    intro s hs
    have h1 := (hd s hs.1).rpow_const (p := -α) (Or.inl (hpos s ⟨hs.1.le, hs.2.le⟩).ne')
    exact h1.sub ((hasDerivAt_id' s).const_mul (c * α))
  have hmono : MonotoneOn (fun s => v s - c * α * s) (Icc 0 t) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t) ?_ ?_ ?_
    · exact hvcont.sub (continuousOn_const.mul continuousOn_id)
    · rw [interior_Icc]
      exact fun s hs => (hvder s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hvder s hs).deriv]
      have hs' : 0 < u s := hpos s ⟨hs.1.le, hs.2.le⟩
      have hi := hineq s hs.1
      have hpow : u s ^ (-α - 1) * u s ^ (1 + α) = 1 := by
        rw [← Real.rpow_add hs', show -α - 1 + (1 + α) = 0 by ring, Real.rpow_zero]
      have : -α * u s ^ (-α - 1) * u' s ≥ α * c := by
        have h2 : 0 < α * u s ^ (-α - 1) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hi h2.le]
      nlinarith
  have hv0 : 0 ≤ v 0 := Real.rpow_nonneg (hnn 0 le_rfl) _
  have hmon := hmono (left_mem_Icc.2 ht.le) (right_mem_Icc.2 ht.le) ht.le
  simp only [mul_zero, sub_zero] at hmon
  have hvt : c * α * t ≤ u t ^ (-α) := by linarith
  -- invert
  have h3 : u t = (u t ^ (-α)) ^ (-(1 / α)) := by
    rw [← Real.rpow_mul hupos.le]
    have : -α * -(1 / α) = 1 := by field_simp
    rw [this, Real.rpow_one]
  rw [h3]
  have hneg : -(1 / α) ≤ 0 := by
    have : 0 < 1 / α := by positivity
    linarith
  exact Real.rpow_le_rpow_of_nonpos hA hvt hneg

/-- **Nash decay (abstract Carlen--Kusuoka--Stroock step).** Let `u ≥ 0` be continuous on
`[0, ∞)` with `u′ = -2 E` on `(0, ∞)`, where `E` satisfies the Nash-type inequality
`u^(1+α) ≤ K E M^(2α)` with constants `K, M, α > 0`. Then
`u(t) ≤ (K M^(2α) / (2 α t))^(1/α)`. For `u = ‖T_t f‖₂²`, `E` the Dirichlet energy of `T_t f`
and `M = ‖f‖₁` this is the decay `‖T_t f‖₂ ≤ C t^(-1/(2α)) ‖f‖₁`. -/
theorem nash_decay {u E : ℝ → ℝ} {K M α : ℝ} (hK : 0 < K) (hM : 0 < M) (hα : 0 < α)
    (hcont : ContinuousOn u (Ici 0)) (hnn : ∀ t, 0 ≤ t → 0 ≤ u t)
    (hd : ∀ t, 0 < t → HasDerivAt u (-2 * E t) t)
    (hnash : ∀ t, 0 < t → u t ^ (1 + α) ≤ K * E t * M ^ (2 * α)) :
    ∀ t, 0 < t → u t ≤ (K * M ^ (2 * α) / (2 * α * t)) ^ (1 / α) := by
  intro t ht
  have hMα : 0 < M ^ (2 * α) := Real.rpow_pos_of_pos hM _
  have hKM : 0 < K * M ^ (2 * α) := by positivity
  set c : ℝ := 2 / (K * M ^ (2 * α)) with hc
  have hcpos : 0 < c := by positivity
  have hmain := ode_decay (u := u) (u' := fun t => -2 * E t) (c := c) hcpos hα hcont hnn hd
    (fun s hs => by
      have h := hnash s hs
      have h2 : u s ^ (1 + α) / (K * M ^ (2 * α)) ≤ E s := by
        rw [div_le_iff₀ hKM]; linarith
      have : -c * u s ^ (1 + α) = -2 * (u s ^ (1 + α) / (K * M ^ (2 * α))) := by
        rw [hc]; ring
      rw [this]; linarith) t ht
  refine hmain.trans (le_of_eq ?_)
  have hA : 0 < c * α * t := by positivity
  have e : c * α * t = (K * M ^ (2 * α) / (2 * α * t))⁻¹ := by
    rw [hc]; field_simp
  rw [e, Real.rpow_neg (by positivity), Real.inv_rpow (by positivity), inv_inv]

end

end FracLap
