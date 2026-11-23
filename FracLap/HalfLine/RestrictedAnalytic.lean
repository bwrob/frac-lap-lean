/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Core.AnalyticSemigroup
public import FracLap.HalfLine.RestrictedSemigroup

/-!
# FracLap.HalfLine.RestrictedAnalytic

Parabolic smoothing and basic orbit properties of the restricted fractional heat semigroup on the
half-line (`cor:s0_properties`, and the smoothing consequences of analyticity used in the remark
after it).

The mathematical reason for smoothing: the Lax–Milgram resolvent `R_μ` of the *symmetric* form
`B_0^α` is self-adjoint, so `S_0(t)` is a limit of exponentials of symmetric nonpositive bounded
operators `G`; for such operators the spectral bound `sup_{λ ≥ 0} λ e^{-tλ} ≤ 1/t` gives
`‖G e^{tG}‖ ≤ 1/t`, which survives the limit and puts `S_0(t) u` in the generator domain.

* `restrictedFracLapSemigroup_mem_generatorDomain_of_pos`: `S_0(t) u ∈ D(A_0)` for every
  `u ∈ L²((0, ∞))` and `t > 0`.
* `norm_generator_restrictedFracLapSemigroup_le`: `‖A_0 S_0(t) u‖ ≤ ‖u‖ / t`.
* `restrictedFracLapSemigroup_exists_form_bound`: `S_0(t) u = ι v` with `v ∈ H_0^{α/2}` and
  `B_0^α(v, v) ≤ ‖u‖² / t`.
* `restrictedFracLapSemigroup_hasDerivAt_of_pos`: the orbit is differentiable on `(0, ∞)` with
  derivative `A_0 S_0(t) u`.
* `restrictedFracLapSemigroup_hasDerivWithinAt_Ici`: for `u ∈ D(A_0)` the right derivative exists
  for all `t ≥ 0`.
-/

namespace FracLap

open Filter MeasureTheory Set Topology
open scoped NNReal InnerProductSpace

@[expose] public section

/-- The restricted resolvent is symmetric (self-adjoint). -/
theorem restrictedFracLapResolvent_symm (α : ℝ) (hα : FractionalExponent α)
    (μ : PositiveShift) (x y : L2IoiR) :
    ⟪(restrictedFracLapResolvent α hα).operator μ x, y⟫_ℝ =
      ⟪x, (restrictedFracLapResolvent α hα).operator μ y⟫_ℝ :=
  inner_restrictedResolventOp_symm α μ x y

/-- **Immediate regularization**: `S_0(t) u ∈ D(A_0)` for every `u ∈ L²((0, ∞))`, `t > 0`. -/
theorem restrictedFracLapSemigroup_mem_generatorDomain_of_pos {α : ℝ}
    (hα : FractionalExponent α) (u : L2IoiR) {t : ℝ≥0} (ht : 0 < (t : ℝ)) :
    restrictedFracLapSemigroup α hα t u ∈ (restrictedFracLapSemigroup α hα).generatorDomain :=
  (restrictedFracLapResolvent α hα).generatedSemigroup_mem_generatorDomain_of_pos
    (restrictedFracLapResolvent_symm α hα) u ht

/-- **Generator bound of order `1/t` along the orbit**. -/
theorem norm_generator_restrictedFracLapSemigroup_le {α : ℝ} (hα : FractionalExponent α)
    (u : L2IoiR) {t : ℝ≥0} (ht : 0 < (t : ℝ)) :
    ‖(restrictedFracLapSemigroup α hα).generator
      ⟨restrictedFracLapSemigroup α hα t u,
        restrictedFracLapSemigroup_mem_generatorDomain_of_pos hα u ht⟩‖ ≤ ‖u‖ / (t : ℝ) :=
  (restrictedFracLapResolvent α hα).norm_generator_generatedSemigroup_of_pos_le
    (restrictedFracLapResolvent_symm α hα) u ht

/-- **Energy smoothing**: for every `u ∈ L²((0, ∞))` and `t > 0` the orbit point `S_0(t) u` is the
image of a function `v ∈ H_0^{α/2}` with `B_0^α(v, v) ≤ ‖u‖² / t`. -/
theorem restrictedFracLapSemigroup_exists_form_bound {α : ℝ} (hα : FractionalExponent α)
    (u : L2IoiR) {t : ℝ≥0} (ht : 0 < (t : ℝ)) :
    ∃ v : RestrictedGagliardoSpace α,
      restrictedL2Map α v = restrictedFracLapSemigroup α hα t u ∧
        (restrictedGagliardoForm α).form v v ≤ ‖u‖ ^ 2 / (t : ℝ) := by
  have hmem := restrictedFracLapSemigroup_mem_generatorDomain_of_pos hα u ht
  obtain ⟨v, hv, _⟩ := restrictedFracLapSemigroup_mem_generatorDomain_forward hα hmem
  refine ⟨v, hv, ?_⟩
  have h1 := inner_generator_restrictedFracLapSemigroup_eq_neg_form hα hmem v hv
  have h2 := norm_generator_restrictedFracLapSemigroup_le hα u ht
  have h3 := (restrictedFracLapSemigroup α hα).norm_apply_le t u
  have h4 : (restrictedGagliardoForm α).form v v =
      -⟪(restrictedFracLapSemigroup α hα).generator
        ⟨restrictedFracLapSemigroup α hα t u, hmem⟩,
        restrictedFracLapSemigroup α hα t u⟫_ℝ := by linarith
  rw [h4]
  calc -⟪(restrictedFracLapSemigroup α hα).generator ⟨restrictedFracLapSemigroup α hα t u, hmem⟩,
        restrictedFracLapSemigroup α hα t u⟫_ℝ
      ≤ ‖(restrictedFracLapSemigroup α hα).generator
          ⟨restrictedFracLapSemigroup α hα t u, hmem⟩‖ *
        ‖restrictedFracLapSemigroup α hα t u‖ := by
        have := real_inner_le_norm
          (-((restrictedFracLapSemigroup α hα).generator
            ⟨restrictedFracLapSemigroup α hα t u, hmem⟩))
          (restrictedFracLapSemigroup α hα t u)
        simpa only [inner_neg_left, norm_neg] using this
    _ ≤ (‖u‖ / (t : ℝ)) * ‖u‖ :=
        mul_le_mul h2 h3 (norm_nonneg _) (div_nonneg (norm_nonneg _) ht.le)
    _ = ‖u‖ ^ 2 / (t : ℝ) := by ring

/-- **Immediate time differentiability**: for every `u` the orbit `s ↦ S_0(s) u` is differentiable
at every `t > 0` with derivative `A_0 S_0(t) u`. -/
theorem restrictedFracLapSemigroup_hasDerivAt_of_pos {α : ℝ} (hα : FractionalExponent α)
    (u : L2IoiR) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => restrictedFracLapSemigroup α hα (Real.toNNReal s) u)
      ((restrictedFracLapSemigroup α hα).generator
        ⟨restrictedFracLapSemigroup α hα (Real.toNNReal t) u,
          restrictedFracLapSemigroup_mem_generatorDomain_of_pos hα u
            (by simpa [Real.coe_toNNReal t ht.le] using ht)⟩) t :=
  (restrictedFracLapResolvent α hα).generatedSemigroup_hasDerivAt_of_pos
    (restrictedFracLapResolvent_symm α hα) u ht

/-- **Evolution equation up to `t = 0` for data in the domain (`cor:s0_properties`, (1))**:
for `u ∈ D(A_0)` the right derivative of the orbit at every `t ≥ 0` is `A_0 S_0(t) u`. -/
theorem restrictedFracLapSemigroup_hasDerivWithinAt_Ici {α : ℝ} (hα : FractionalExponent α)
    (u : (restrictedFracLapSemigroup α hα).generatorDomain) (t : ℝ≥0) :
    HasDerivWithinAt (fun s : ℝ => restrictedFracLapSemigroup α hα (Real.toNNReal s) u)
      ((restrictedFracLapSemigroup α hα).generator
        ⟨restrictedFracLapSemigroup α hα t u,
          (restrictedFracLapSemigroup α hα).operator_mem_generatorDomain u t⟩)
      (Ici (t : ℝ)) t := by
  rw [(restrictedFracLapSemigroup α hα).generator_operator u t]
  exact (restrictedFracLapSemigroup α hα).hasDerivWithinAt_Ici u t

/-- **Strong continuity at `0` (`cor:s0_properties`, (2))**: `S_0(t) u → u` as `t → 0⁺`. -/
theorem tendsto_restrictedFracLapSemigroup_zero {α : ℝ} (hα : FractionalExponent α)
    (u : L2IoiR) :
    Tendsto (fun t : ℝ≥0 => restrictedFracLapSemigroup α hα t u) (𝓝 0) (𝓝 u) := by
  have h := (restrictedFracLapSemigroup α hα).continuous_orbit u
  have h0 := h.tendsto 0
  simpa using h0

end

end FracLap
