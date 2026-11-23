/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# FracLap.Tools.AbstractLemmas

Small abstract lemmas used across the nonlocal-diffusion literature.

- `bilinear_fixed_point`: Banach fixed point for small bilinear problems `u = y + B(u, u)`
  (Biler--Karch--Woyczyński, Xiao): if `‖B(u, v)‖ ≤ η ‖u‖ ‖v‖` and `‖y‖ < ε < 1/(4η)` there is a
  solution with `‖u‖ ≤ 2ε`, unique in the closed ball of radius `2ε`.
- `scaling_le_max`, `min_le_scaling`: scaling of a nonnegative, nondecreasing, concave function with
  `φ(0) ≥ 0` (Bernstein functions): `1 ∧ λ ≤ φ(λ t) / φ(t) ≤ 1 ∨ λ` (Kim--Song--Vondraček).
- `mul_deriv_le`: for such `φ` differentiable at `z > 0`, `0 ≤ φ'(z)` and `z φ'(z) ≤ φ(z)`.
-/

namespace FracLap

open Set

@[expose] public section

/-- **Small solutions of bilinear fixed-point problems.** Let `B` be bilinear with
`‖B u v‖ ≤ η ‖u‖ ‖v‖`, `0 < ε < 1 / (4 η)` and `‖y‖ < ε`. Then `u = y + B u u` has a solution with
`‖u‖ ≤ 2 ε`, and it is the only solution in the closed ball of radius `2 ε`. -/
theorem bilinear_fixed_point {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (B : X →L[ℝ] X →L[ℝ] X) {η ε : ℝ} (hη : 0 < η) (hB : ∀ u v, ‖B u v‖ ≤ η * ‖u‖ * ‖v‖)
    (hε : 0 < ε) (hεη : ε < 1 / (4 * η)) {y : X} (hy : ‖y‖ < ε) :
    ∃ u : X, u = y + B u u ∧ ‖u‖ ≤ 2 * ε ∧
      ∀ v : X, v = y + B v v → ‖v‖ ≤ 2 * ε → v = u := by
  have h4 : 4 * η * ε < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hεη
    linarith
  set K : NNReal := ⟨4 * η * ε, by positivity⟩ with hK
  have hK1 : K < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_one]
    exact h4
  let s : Set X := Metric.closedBall 0 (2 * ε)
  let T : X → X := fun u => y + B u u
  have hdiff : ∀ u v : X, ‖u‖ ≤ 2 * ε → ‖v‖ ≤ 2 * ε → ‖T u - T v‖ ≤ (4 * η * ε) * ‖u - v‖ := by
    intro u v hu hv
    have : T u - T v = B (u - v) u + B v (u - v) := by
      simp only [T, map_sub, sub_apply]
      abel
    rw [this]
    calc ‖B (u - v) u + B v (u - v)‖ ≤ ‖B (u - v) u‖ + ‖B v (u - v)‖ := norm_add_le _ _
      _ ≤ η * ‖u - v‖ * ‖u‖ + η * ‖v‖ * ‖u - v‖ := add_le_add (hB _ _) (hB _ _)
      _ ≤ η * ‖u - v‖ * (2 * ε) + η * (2 * ε) * ‖u - v‖ := by gcongr
      _ = (4 * η * ε) * ‖u - v‖ := by ring
  have hmaps : MapsTo T s s := by
    intro u hu
    have hu' : ‖u‖ ≤ 2 * ε := by simpa [s] using hu
    have : ‖T u‖ ≤ 2 * ε := by
      calc ‖T u‖ ≤ ‖y‖ + ‖B u u‖ := norm_add_le _ _
        _ ≤ ε + η * ‖u‖ * ‖u‖ := add_le_add hy.le (hB _ _)
        _ ≤ ε + η * (2 * ε) * (2 * ε) := by gcongr
        _ = ε + (4 * η * ε) * ε := by ring
        _ ≤ ε + 1 * ε := by gcongr
        _ = 2 * ε := by ring
    simpa [s] using this
  have hcontr : ContractingWith K (hmaps.restrict T s s) := by
    refine ⟨hK1, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    simp only [MapsTo.val_restrict_apply, Subtype.dist_eq, dist_eq_norm]
    exact hdiff a b (mem_closedBall_zero_iff.mp a.property) (mem_closedBall_zero_iff.mp b.property)
  have hcomplete : IsComplete s := Metric.isClosed_closedBall.isComplete
  obtain ⟨u, hus, hfix, -⟩ := hcontr.exists_fixedPoint' hcomplete hmaps
    (show (0 : X) ∈ s by simp [s, hε.le]) (edist_ne_top _ _)
  have hu' : ‖u‖ ≤ 2 * ε := by simpa [s] using hus
  refine ⟨u, hfix.eq.symm, hu', fun v hv hvb => ?_⟩
  have hd := hdiff v u hvb hu'
  have hv' : T v = v := hv.symm
  have hu'' : T u = u := hfix.eq
  rw [hv', hu''] at hd
  by_contra hne
  have hpos : 0 < ‖v - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  nlinarith

/-- A nonnegative, nondecreasing function concave on `[0, ∞)` with `φ(0) ≥ 0` satisfies
`φ(λ t) ≤ max 1 λ · φ(t)` for `t, λ > 0` (the Bernstein-function scaling upper bound). -/
theorem scaling_le_max {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ (Ici 0) φ) (hφ0 : 0 ≤ φ 0)
    (hmono : MonotoneOn φ (Ici 0)) {t : ℝ} (ht : 0 < t) {l : ℝ} (hl : 0 < l) :
    φ (l * t) ≤ max 1 l * φ t := by
  rcases le_total l 1 with h | h
  · rw [max_eq_left h, one_mul]
    exact hmono (mem_Ici.mpr (by positivity)) (mem_Ici.mpr ht.le) (by nlinarith)
  · rw [max_eq_right h]
    have h1 := hφ.2 (mem_Ici.mpr (by positivity : (0 : ℝ) ≤ l * t)) (mem_Ici.mpr le_rfl)
      (by positivity : (0 : ℝ) ≤ l⁻¹) (by
        have : 0 ≤ 1 - l⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ h)
        exact this) (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero] at h1
    have e : l⁻¹ * (l * t) = t := by field_simp
    rw [e] at h1
    have : l⁻¹ * φ (l * t) + (1 - l⁻¹) * φ 0 ≤ φ t := h1
    have h2 : l⁻¹ * φ (l * t) ≤ φ t := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ h)) hφ0]
    calc φ (l * t) = l * (l⁻¹ * φ (l * t)) := by field_simp
      _ ≤ l * φ t := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- Lower scaling bound: `min 1 λ · φ(t) ≤ φ(λ t)`. -/
theorem min_le_scaling {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ (Ici 0) φ) (hφ0 : 0 ≤ φ 0)
    (hmono : MonotoneOn φ (Ici 0)) {t : ℝ} (ht : 0 < t) {l : ℝ} (hl : 0 < l) :
    min 1 l * φ t ≤ φ (l * t) := by
  have h := scaling_le_max hφ hφ0 hmono (t := l * t) (by positivity) (l := l⁻¹) (by positivity)
  have e : l⁻¹ * (l * t) = t := by field_simp
  rw [e] at h
  rcases le_total l 1 with hl1 | hl1
  · rw [min_eq_right hl1]
    have : max 1 l⁻¹ = l⁻¹ := max_eq_right (one_le_inv₀ hl |>.mpr hl1)
    rw [this] at h
    calc l * φ t ≤ l * (l⁻¹ * φ (l * t)) := mul_le_mul_of_nonneg_left h hl.le
      _ = φ (l * t) := by field_simp
  · rw [min_eq_left hl1, one_mul]
    exact hmono (mem_Ici.mpr ht.le) (mem_Ici.mpr (by positivity)) (by nlinarith)

/-- **Derivative bounds for Bernstein-type functions.** If `φ` is nondecreasing and concave on
`[0, ∞)` with `φ(0) ≥ 0` and `φ` has derivative `d` at `z > 0`, then `0 ≤ d` and `z d ≤ φ(z)`.
(The companion estimate `-z φ''(z) ≤ 2 φ'(z)` holds for complete Bernstein functions only.) -/
theorem mul_deriv_le {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ (Ici 0) φ) (hφ0 : 0 ≤ φ 0)
    (hmono : MonotoneOn φ (Ici 0)) {z d : ℝ} (hz : 0 < z) (hd : HasDerivAt φ d z) :
    0 ≤ d ∧ z * d ≤ φ z := by
  refine ⟨?_, ?_⟩
  · have hmono' : Monotone (fun x => φ (max x 0)) := fun x y hxy =>
      hmono (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (le_max_right _ _))
        (max_le_max hxy le_rfl)
    have hd' : HasDerivAt (fun x => φ (max x 0)) d z := by
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hz] with x hx
      simp [max_eq_left (le_of_lt (mem_Ioi.mp hx))]
    exact hd'.nonneg_of_monotone hmono'
  · have h := hφ.le_slope_of_hasDerivAt (mem_Ici.mpr le_rfl) (mem_Ici.mpr hz.le) hz hd
    rw [slope_def_field] at h
    simp only [sub_zero] at h
    rw [le_div_iff₀ hz] at h
    linarith

end

end FracLap
