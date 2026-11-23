/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Core.Pointwise
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLap.HalfLine.MaximumPrinciples

Pointwise linear and nonlinear maximum principles for the fractional Laplacian on the
real line and the reflected fractional Laplacian on the half-line `(0, ∞)`:
- `fracLapSecondDiff_nonneg_of_isMax`: whole-line linear maximum principle
  `(-Δ)^(α / 2) v(x₀) ≥ 0` at a global maximum `x₀ ∈ ℝ`.
- `reflectedFracLapSecondDiff_nonneg_of_isMaxOn_Ioi`: half-line linear maximum principle
  `(-Δ̃)^(α / 2) u(x₀) ≥ 0` at a nonnegative global maximum `x₀ > 0`.
- `nlmpConstantC1`, `nlmpConstantC2`, `nlmpOptimalConstant`, `nlmpOptimalRadius`:
  constants and optimal cutoff scale for the Constantin–Vicol nonlinear maximum principle.
- `nlmp_scale_optimization` and `nonlinear_max_principle`:
  quantitative Constantin–Vicol nonlinear lower bound
  `(-Δ̃)^(α / 2) u(x₀) ≥ C(α) u(x₀)^(1 + α) / M^α` at a positive global maximum `x₀ > 0`.
- `reflectedFracLapSecondDiff_satisfiesCutoffAntiderivativeBound` and
  `reflectedFracLapSecondDiff_nonlinear_max_principle`: unconditional derivation of the
  Constantin–Vicol lower bound directly from `reflectedFracLapSecondDiff` and `IntegrableOn u`.
-/

namespace FracLap

open Filter MeasureTheory Real Set

@[expose] public section

/-- **Whole-Line Linear Maximum Principle**:
If `x₀ ∈ ℝ` is a global maximum point of `v : ℝ → ℝ` and `α ∈ (0, 2)`, then the
weighted second-difference fractional Laplacian satisfies `(-Δ)^(α / 2) v(x₀) ≥ 0`. -/
theorem fracLapSecondDiff_nonneg_of_isMax {α : ℝ} (hα : FractionalExponent α)
    (v : ℝ → ℝ) (x₀ : ℝ) (hmax : ∀ z : ℝ, v z ≤ v x₀) :
    0 ≤ fracLapSecondDiff α v x₀ := by
  unfold fracLapSecondDiff
  have hC : 0 < fracLapConstant α := fracLapConstant_pos hα
  have h_integrand : ∀ y : ℝ, secondDiff v x₀ y / |y| ^ (1 + α) ≤ 0 := by
    intro y
    have hnum : secondDiff v x₀ y ≤ 0 := secondDiff_nonpos_of_isMax v x₀ y hmax
    have hden : 0 ≤ |y| ^ (1 + α) := by positivity
    exact div_nonpos_of_nonpos_of_nonneg hnum hden
  have h_int : ∫ y : ℝ, secondDiff v x₀ y / |y| ^ (1 + α) ≤ 0 := by
    have h_neg_nonneg : 0 ≤ ∫ y : ℝ, -(secondDiff v x₀ y / |y| ^ (1 + α)) :=
      integral_nonneg fun y => neg_nonneg.mpr (h_integrand y)
    rw [integral_neg] at h_neg_nonneg
    linarith
  have h_pref : -(fracLapConstant α / 2) ≤ 0 := by linarith
  exact mul_nonneg_of_nonpos_of_nonpos h_pref h_int

/-- **Half-Line Linear Maximum Principle**:
Let `u : ℝ → ℝ` be nonnegative on `(0, ∞)` and let `x₀ > 0` be a global maximum point of `u`
on `(0, ∞)`. Then `(-Δ̃)^(α / 2) u(x₀) ≥ 0`. -/
theorem reflectedFracLapSecondDiff_nonneg_of_isMaxOn_Ioi {α : ℝ} (hα : FractionalExponent α)
    (u : ℝ → ℝ) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ u x)
    (hmax : ∀ x : ℝ, 0 < x → u x ≤ u x₀) :
    0 ≤ reflectedFracLapSecondDiff α u x₀ := by
  unfold reflectedFracLapSecondDiff
  have h_odd_max : ∀ z : ℝ, oddExt u z ≤ oddExt u x₀ :=
    oddExt_le_of_nonneg_of_isMaxOn_Ioi hx₀ hnonneg hmax
  exact fracLapSecondDiff_nonneg_of_isMax hα (oddExt u) x₀ h_odd_max

/-- Far-field tail constant `C₁(α) = C(α) / (α 2^(α - 1))` appearing in the
Constantin–Vicol nonlinear maximum principle (`2 ∫_{2R}^∞ y^(-1-α) dy`). -/
noncomputable def nlmpConstantC1 (α : ℝ) : ℝ :=
  fracLapConstant α / (α * (2 : ℝ) ^ (α - 1))

/-- For `α ∈ (0, 2)`, the far-field constant `C₁(α)` is strictly positive. -/
theorem nlmpConstantC1_pos {α : ℝ} (hα : FractionalExponent α) :
    0 < nlmpConstantC1 α := by
  unfold nlmpConstantC1
  have hC : 0 < fracLapConstant α := fracLapConstant_pos hα
  have h0 : 0 < α := hα.1
  have h2 : 0 < (2 : ℝ) ^ (α - 1) := by positivity
  positivity

/-- Integration-by-parts remainder constant `C₂(α) = C(α) (8 / α + 2)` appearing in the
Constantin–Vicol nonlinear maximum principle. -/
noncomputable def nlmpConstantC2 (α : ℝ) : ℝ :=
  fracLapConstant α * (8 / α + 2)

/-- For `α ∈ (0, 2)`, the remainder constant `C₂(α)` is strictly positive. -/
theorem nlmpConstantC2_pos {α : ℝ} (hα : FractionalExponent α) :
    0 < nlmpConstantC2 α := by
  unfold nlmpConstantC2
  have hC : 0 < fracLapConstant α := fracLapConstant_pos hα
  have h0 : 0 < α := hα.1
  positivity

/-- Optimal Constantin–Vicol constant
`C(α) = C₁(α)^(1 + α) / (2^(1 + α) C₂(α)^α)`. -/
noncomputable def nlmpOptimalConstant (α : ℝ) : ℝ :=
  nlmpConstantC1 α ^ (1 + α) / ((2 : ℝ) ^ (1 + α) * nlmpConstantC2 α ^ α)

/-- For `α ∈ (0, 2)`, the Constantin–Vicol nonlinear maximum principle constant
`nlmpOptimalConstant α` is strictly positive. -/
theorem nlmpOptimalConstant_pos {α : ℝ} (hα : FractionalExponent α) :
    0 < nlmpOptimalConstant α := by
  unfold nlmpOptimalConstant
  have hC1 : 0 < nlmpConstantC1 α := nlmpConstantC1_pos hα
  have hC2 : 0 < nlmpConstantC2 α := nlmpConstantC2_pos hα
  positivity

/-- Optimal cutoff scale `R = 2 C₂ M / (C₁ U₀)` balancing the far-field dissipation term
`C₁ U₀ / R^α` against the antiderivative integration-by-parts remainder `C₂ M / R^(1 + α)`. -/
noncomputable def nlmpOptimalRadius (C₁ C₂ U₀ M : ℝ) : ℝ :=
  2 * C₂ * M / (C₁ * U₀)

/-- If `C₁, C₂, U₀, M > 0`, the optimal cutoff radius `R = 2 C₂ M / (C₁ U₀)` is strictly
positive. -/
theorem nlmpOptimalRadius_pos {C₁ C₂ U₀ M : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hU₀ : 0 < U₀) (hM : 0 < M) :
    0 < nlmpOptimalRadius C₁ C₂ U₀ M := by
  unfold nlmpOptimalRadius
  positivity

/-- **Algebraic Scale Optimization Lemma for the Constantin–Vicol Bound**:
At the optimal cutoff radius `R = 2 C₂ M / (C₁ U₀)`, the difference between the far-field
lower bound `C₁ U₀ / R^α` and the antiderivative remainder `C₂ M / R^(1 + α)` equals
`(C₁^(1 + α) / (2^(1 + α) C₂^α)) * U₀^(1 + α) / M^α`. -/
theorem nlmp_scale_optimization {α C₁ C₂ U₀ M : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hU₀ : 0 < U₀) (hM : 0 < M) :
    let R := nlmpOptimalRadius C₁ C₂ U₀ M
    C₁ * U₀ / R ^ α - C₂ * M / R ^ (1 + α) =
      (C₁ ^ (1 + α) / ((2 : ℝ) ^ (1 + α) * C₂ ^ α)) * (U₀ ^ (1 + α) / M ^ α) := by
  intro R
  have hR_def : R = 2 * C₂ * M / (C₁ * U₀) := rfl
  have hR_pos : 0 < R := nlmpOptimalRadius_pos hC₁ hC₂ hU₀ hM
  have hR_ne : R ≠ 0 := ne_of_gt hR_pos
  have hR_pow_ne : R ^ α ≠ 0 := ne_of_gt (rpow_pos_of_pos hR_pos α)
  have h_rpow_one_add : R ^ (1 + α) = R * R ^ α := by
    rw [add_comm (1 : ℝ) α, rpow_add_one hR_ne α]
    ring
  have h_half : C₂ * M / R = C₁ * U₀ / 2 := by
    rw [hR_def]
    have hC₁_ne : C₁ ≠ 0 := ne_of_gt hC₁
    have hC₂_ne : C₂ ≠ 0 := ne_of_gt hC₂
    have hU₀_ne : U₀ ≠ 0 := ne_of_gt hU₀
    have hM_ne : M ≠ 0 := ne_of_gt hM
    field_simp
  have h_step1 : C₁ * U₀ / R ^ α - C₂ * M / R ^ (1 + α) = C₁ * U₀ / (2 * R ^ α) := by
    rw [h_rpow_one_add, ← div_div, h_half]
    ring
  rw [h_step1]
  have h_R_alpha : R ^ α = (2 : ℝ) ^ α * C₂ ^ α * M ^ α / (C₁ ^ α * U₀ ^ α) := by
    rw [hR_def, div_rpow (by positivity) (by positivity)]
    rw [mul_rpow (by positivity) (by positivity)]
    rw [mul_rpow (by positivity) (by positivity)]
    rw [mul_rpow (by positivity) (by positivity)]
  rw [h_R_alpha]
  have hC₁_one_add : C₁ ^ (1 + α) = C₁ * C₁ ^ α := by
    rw [add_comm (1 : ℝ) α, rpow_add_one (ne_of_gt hC₁) α]
    ring
  have hU₀_one_add : U₀ ^ (1 + α) = U₀ * U₀ ^ α := by
    rw [add_comm (1 : ℝ) α, rpow_add_one (ne_of_gt hU₀) α]
    ring
  have h2_one_add : (2 : ℝ) ^ (1 + α) = 2 * (2 : ℝ) ^ α := by
    rw [add_comm (1 : ℝ) α, rpow_add_one (by norm_num) α]
    ring
  rw [hC₁_one_add, hU₀_one_add, h2_one_add]
  have hC₁a_ne : C₁ ^ α ≠ 0 := ne_of_gt (rpow_pos_of_pos hC₁ α)
  have hC₂a_ne : C₂ ^ α ≠ 0 := ne_of_gt (rpow_pos_of_pos hC₂ α)
  have hU₀a_ne : U₀ ^ α ≠ 0 := ne_of_gt (rpow_pos_of_pos hU₀ α)
  have hMa_ne : M ^ α ≠ 0 := ne_of_gt (rpow_pos_of_pos hM α)
  have h2a_ne : (2 : ℝ) ^ α ≠ 0 := ne_of_gt (by positivity)
  field_simp

/-- Bundled cutoff-and-antiderivative hypothesis for the Constantin–Vicol decomposition:
for every cutoff scale `R > 0`, splitting the reflected singular integral with a smooth
radial cutoff `ϕ(y / R)` and integrating the antiderivative `U(x) = ∫_{-∞}^x ũ(s) ds`
(satisfying `‖U‖_{L^∞(ℝ)} ≤ M = ‖u‖_{L^1(0,∞)}`) by parts on `{|y| > R}` yields the
scale-dependent lower bound
`L ≥ C₁(α) u(x₀) / R^α - C₂(α) M / R^(1 + α)`. -/
def SatisfiesCutoffAntiderivativeBound (α L U₀ M : ℝ) : Prop :=
  ∀ R : ℝ, 0 < R →
    nlmpConstantC1 α * U₀ / R ^ α - nlmpConstantC2 α * M / R ^ (1 + α) ≤ L

/-- **Half-Line Constantin–Vicol Nonlinear Maximum Principle**:
Let `α ∈ (0, 2)`, let `U₀ = u(x₀) > 0` be the positive global maximum of `u` on `(0, ∞)`,
let `M = ‖u‖_{L^1(0, ∞)} > 0`, and let `L = (-Δ̃)^(α / 2) u(x₀)` satisfy the
cutoff-and-antiderivative decomposition bound `SatisfiesCutoffAntiderivativeBound α L U₀ M`.
Then
`(-Δ̃)^(α / 2) u(x₀) ≥ nlmpOptimalConstant α * U₀ ^ (1 + α) / M ^ α`
with `nlmpOptimalConstant α > 0`. -/
theorem nonlinear_max_principle {α L U₀ M : ℝ} (hα : FractionalExponent α)
    (hU₀ : 0 < U₀) (hM : 0 < M)
    (hdecomp : SatisfiesCutoffAntiderivativeBound α L U₀ M) :
    nlmpOptimalConstant α * (U₀ ^ (1 + α) / M ^ α) ≤ L := by
  have hC₁ : 0 < nlmpConstantC1 α := nlmpConstantC1_pos hα
  have hC₂ : 0 < nlmpConstantC2 α := nlmpConstantC2_pos hα
  let R := nlmpOptimalRadius (nlmpConstantC1 α) (nlmpConstantC2 α) U₀ M
  have hR_pos : 0 < R := nlmpOptimalRadius_pos hC₁ hC₂ hU₀ hM
  have h_bound_at_R :
      nlmpConstantC1 α * U₀ / R ^ α - nlmpConstantC2 α * M / R ^ (1 + α) ≤ L :=
    hdecomp R hR_pos
  have h_opt :
      nlmpConstantC1 α * U₀ / R ^ α - nlmpConstantC2 α * M / R ^ (1 + α) =
        nlmpOptimalConstant α * (U₀ ^ (1 + α) / M ^ α) :=
    nlmp_scale_optimization hC₁ hC₂ hU₀ hM
  linarith

/-- If `u : ℝ → ℝ` is integrable on `(0, ∞)`, then its antisymmetric extension `oddExt u`
is integrable on all of `ℝ`. -/
theorem integrable_oddExt_of_integrableOn_Ioi {u : ℝ → ℝ} (hint : IntegrableOn u (Ioi 0)) :
    Integrable (oddExt u) := by
  have hpos_Ioi : IntegrableOn (oddExt u) (Ioi 0) :=
    hint.congr_fun (fun x hx ↦ (oddExt_of_pos u hx).symm) measurableSet_Ioi
  have hpos_Ici : IntegrableOn (oddExt u) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hpos_Ioi
  have hneg_comp : IntegrableOn (fun x : ℝ ↦ -u (-x)) (Iio 0) := by
    have hcomp : IntegrableOn (fun x : ℝ ↦ u (-x)) (Neg.neg ⁻¹' Ioi (0 : ℝ)) :=
      (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg _)
        (Homeomorph.neg ℝ).measurableEmbedding).mpr hint
    have hpre : (Neg.neg ⁻¹' Ioi (0 : ℝ)) = Iio 0 := by
      ext x
      simp only [mem_preimage, mem_Ioi, Left.neg_pos_iff, mem_Iio]
    rw [hpre] at hcomp
    exact hcomp.neg
  have hneg_Iio : IntegrableOn (oddExt u) (Iio 0) :=
    hneg_comp.congr_fun (fun x hx ↦ (oddExt_of_neg u hx).symm) measurableSet_Iio
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ))]
  exact hneg_Iio.union hpos_Ici

/-- For nonnegative `u ∈ L¹(0, ∞)`, the `L¹(ℝ)` norm of the antisymmetric extension `oddExt u`
is exactly twice the `L¹(0, ∞)` norm of `u`. -/
theorem integral_abs_oddExt {u : ℝ → ℝ} (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ u x)
    (hint : IntegrableOn u (Ioi 0)) :
    ∫ z : ℝ, |oddExt u z| = 2 * ∫ x in Ioi (0 : ℝ), u x := by
  have hint_abs : Integrable (fun z : ℝ ↦ |oddExt u z|) :=
    (integrable_oddExt_of_integrableOn_Ioi hint).abs
  have hsplit : (∫ z : ℝ, |oddExt u z|) =
      (∫ z in Iio (0 : ℝ), |oddExt u z|) + ∫ z in Ici (0 : ℝ), |oddExt u z| := by
    have h := integral_add_compl (μ := volume) (measurableSet_Iio (a := (0 : ℝ))) hint_abs
    rw [compl_Iio] at h
    exact h.symm
  have hright : (∫ z in Ici (0 : ℝ), |oddExt u z|) = ∫ x in Ioi (0 : ℝ), u x := by
    rw [integral_Ici_eq_integral_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    rw [oddExt_of_pos u hx, abs_of_nonneg (hnonneg x hx)]
  have hleft : (∫ z in Iio (0 : ℝ), |oddExt u z|) = ∫ x in Ioi (0 : ℝ), u x := by
    have hcongr : (∫ z in Iio (0 : ℝ), |oddExt u z|) =
        ∫ z in Iio (0 : ℝ), u (-z) := by
      refine setIntegral_congr_fun measurableSet_Iio fun z hz ↦ ?_
      rw [oddExt_of_neg u hz, abs_neg, abs_of_nonneg (hnonneg (-z) (neg_pos.mpr hz))]
    rw [hcongr, ← integral_Iic_eq_integral_Iio]
    simpa only [neg_zero] using integral_comp_neg_Iic (0 : ℝ) u
  rw [hsplit, hleft, hright]
  ring

/-- For `α > 0` and `R > 0`, the singular kernel `|y|^(-(1 + α))` is integrable on the exterior
region `(-∞, -2R) ∪ (2R, ∞)`. -/
theorem integrableOn_inv_abs_rpow_exterior {α R : ℝ} (hα : 0 < α) (hR : 0 < R) :
    IntegrableOn (fun y : ℝ ↦ 1 / |y| ^ (1 + α)) (Iio (-2 * R) ∪ Ioi (2 * R)) := by
  have hlt : -(1 + α) < -1 := by linarith
  have h2R : 0 < 2 * R := by positivity
  have hrpow : IntegrableOn (fun y : ℝ ↦ y ^ (-(1 + α))) (Ioi (2 * R)) :=
    integrableOn_Ioi_rpow_of_lt hlt h2R
  have hpos : IntegrableOn (fun y : ℝ ↦ 1 / |y| ^ (1 + α)) (Ioi (2 * R)) := by
    refine hrpow.congr_fun (fun y hy ↦ ?_) measurableSet_Ioi
    have hy0 : 0 < y := h2R.trans hy
    dsimp only
    rw [abs_of_pos hy0, one_div, rpow_neg hy0.le]
  have hneg : IntegrableOn (fun y : ℝ ↦ 1 / |y| ^ (1 + α)) (Iio (-2 * R)) := by
    have hcomp : IntegrableOn (fun y : ℝ ↦ 1 / |-y| ^ (1 + α)) (Neg.neg ⁻¹' Ioi (2 * R)) :=
      (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg _)
        (Homeomorph.neg ℝ).measurableEmbedding).mpr hpos
    have hpre : (Neg.neg ⁻¹' Ioi (2 * R)) = Iio (-2 * R) := by
      ext y
      simp only [mem_preimage, mem_Ioi, mem_Iio, neg_mul]
      exact ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩
    rw [hpre] at hcomp
    refine hcomp.congr_fun (fun y _ ↦ ?_) measurableSet_Iio
    dsimp only
    rw [abs_neg]
  exact hneg.union hpos

/-- For `α > 0` and `R > 0`, the exterior tail integral satisfies
`∫_{(-∞, -2R) ∪ (2R, ∞)} |y|^(-(1 + α)) dy = 2 / (α (2R)^α)`. -/
theorem integral_inv_abs_rpow_exterior {α R : ℝ} (hα : 0 < α) (hR : 0 < R) :
    (∫ y in Iio (-2 * R) ∪ Ioi (2 * R), 1 / |y| ^ (1 + α)) = 2 / (α * (2 * R) ^ α) := by
  have hlt : -(1 + α) < -1 := by linarith
  have h2R : 0 < 2 * R := by positivity
  have hint_pos : IntegrableOn (fun y : ℝ ↦ 1 / |y| ^ (1 + α)) (Ioi (2 * R)) := by
    refine (integrableOn_Ioi_rpow_of_lt hlt h2R).congr_fun (fun y hy ↦ ?_) measurableSet_Ioi
    have hy0 : 0 < y := h2R.trans hy
    dsimp only
    rw [abs_of_pos hy0, one_div, rpow_neg hy0.le]
  have hint_neg : IntegrableOn (fun y : ℝ ↦ 1 / |y| ^ (1 + α)) (Iio (-2 * R)) :=
    (integrableOn_inv_abs_rpow_exterior hα hR).mono_set subset_union_left
  have hdisj : Disjoint (Iio (-2 * R)) (Ioi (2 * R)) := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    rw [mem_Iio] at hy1
    rw [mem_Ioi] at hy2
    linarith
  have hpos_val : (∫ y in Ioi (2 * R), 1 / |y| ^ (1 + α)) = 1 / (α * (2 * R) ^ α) := by
    have hcongr : (∫ y in Ioi (2 * R), 1 / |y| ^ (1 + α)) =
        ∫ y in Ioi (2 * R), y ^ (-(1 + α)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
      have hy0 : 0 < y := h2R.trans hy
      rw [abs_of_pos hy0, one_div, rpow_neg hy0.le]
    rw [hcongr, integral_Ioi_rpow_of_lt hlt h2R]
    have hexp : -(1 + α) + 1 = -α := by ring
    rw [hexp, rpow_neg h2R.le]
    have hα_ne : α ≠ 0 := ne_of_gt hα
    have hpow_ne : (2 * R) ^ α ≠ 0 := ne_of_gt (rpow_pos_of_pos h2R α)
    field_simp
  have hneg_val : (∫ y in Iio (-2 * R), 1 / |y| ^ (1 + α)) = 1 / (α * (2 * R) ^ α) := by
    have hneg_eq : (-2 * R) = -(2 * R) := by ring
    rw [hneg_eq, ← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi (2 * R)]
    have hcongr : (∫ x in Ioi (2 * R), 1 / |-x| ^ (1 + α)) =
        ∫ x in Ioi (2 * R), 1 / |x| ^ (1 + α) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
      rw [abs_neg]
    rw [hcongr, hpos_val]
  rw [setIntegral_union hdisj measurableSet_Ioi hint_neg hint_pos, hneg_val, hpos_val]
  ring

/-- **Unconditional Constantin–Vicol Cutoff-and-Mass Lower Bound**:
Let `α ∈ (0, 2)` and let `u ∈ L¹(0, ∞)` be nonnegative on `(0, ∞)` attaining a global
maximum at `x₀ > 0`, with integrable weighted second difference at `x₀`. Then
`(-Δ̃)^(α / 2) u(x₀)` satisfies `SatisfiesCutoffAntiderivativeBound α L (u x₀) ‖u‖_{L¹(0, ∞)}`.
-/
theorem reflectedFracLapSecondDiff_satisfiesCutoffAntiderivativeBound
    {α : ℝ} (hα : FractionalExponent α) {u : ℝ → ℝ} {x₀ : ℝ}
    (hx₀ : 0 < x₀)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ u x)
    (hmax : ∀ x : ℝ, 0 < x → u x ≤ u x₀)
    (hint_u : IntegrableOn u (Ioi 0))
    (hint_fl : Integrable (fun y : ℝ ↦ secondDiff (oddExt u) x₀ y / |y| ^ (1 + α))) :
    SatisfiesCutoffAntiderivativeBound α (reflectedFracLapSecondDiff α u x₀)
      (u x₀) (∫ x in Ioi (0 : ℝ), u x) := by
  intro R hR
  set S : Set ℝ := Iio (-2 * R) ∪ Ioi (2 * R)
  set v : ℝ → ℝ := oddExt u
  set M : ℝ := ∫ x in Ioi (0 : ℝ), u x
  have hC : 0 < fracLapConstant α := fracLapConstant_pos hα
  have hv_max : ∀ z : ℝ, v z ≤ v x₀ := oddExt_le_of_nonneg_of_isMaxOn_Ioi hx₀ hnonneg hmax
  have hv_x₀ : v x₀ = u x₀ := oddExt_of_pos u hx₀
  have hnonneg_integrand : ∀ y : ℝ, 0 ≤ -(secondDiff v x₀ y / |y| ^ (1 + α)) := by
    intro y
    have hnum : secondDiff v x₀ y ≤ 0 := secondDiff_nonpos_of_isMax v x₀ y hv_max
    have hden : 0 ≤ |y| ^ (1 + α) := by positivity
    exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hnum hden)
  have hset_le :
      (∫ y in S, -(secondDiff v x₀ y / |y| ^ (1 + α))) ≤
        ∫ y : ℝ, -(secondDiff v x₀ y / |y| ^ (1 + α)) :=
    setIntegral_le_integral hint_fl.neg (Eventually.of_forall hnonneg_integrand)
  have hrew : reflectedFracLapSecondDiff α u x₀ =
      (fracLapConstant α / 2) * ∫ y : ℝ, -(secondDiff v x₀ y / |y| ^ (1 + α)) := by
    unfold reflectedFracLapSecondDiff fracLapSecondDiff
    rw [integral_neg]
    change -(fracLapConstant α / 2) * ∫ y : ℝ, secondDiff v x₀ y / |y| ^ (1 + α) =
      (fracLapConstant α / 2) * -(∫ y : ℝ, secondDiff v x₀ y / |y| ^ (1 + α))
    ring
  have hlower :
      (fracLapConstant α / 2) * ∫ y in S, -(secondDiff v x₀ y / |y| ^ (1 + α)) ≤
        reflectedFracLapSecondDiff α u x₀ := by
    rw [hrew]
    exact mul_le_mul_of_nonneg_left hset_le (by linarith)
  have hS_meas : MeasurableSet S := measurableSet_Iio.union measurableSet_Ioi
  have hS_norm : ∀ y ∈ S, R < |y| := by
    intro y hy
    rcases hy with hy | hy
    · rw [mem_Iio] at hy
      have hneg : y < -R := by linarith
      exact lt_abs.mpr (Or.inr (by linarith))
    · rw [mem_Ioi] at hy
      have hpos : R < y := by linarith
      exact lt_abs.mpr (Or.inl hpos)
  have hS_rpow : ∀ y ∈ S, 1 / |y| ^ (1 + α) ≤ 1 / R ^ (1 + α) := by
    intro y hy
    have hR_lt : R < |y| := hS_norm y hy
    have h1a : 0 < 1 + α := by linarith [hα.1]
    have hpow : R ^ (1 + α) ≤ |y| ^ (1 + α) :=
      rpow_le_rpow hR.le hR_lt.le h1a.le
    exact one_div_le_one_div_of_le (rpow_pos_of_pos hR _) hpow
  have hint_v : Integrable v := integrable_oddExt_of_integrableOn_Ioi hint_u
  have hint_ext : IntegrableOn (fun y : ℝ ↦ (2 * u x₀) * (1 / |y| ^ (1 + α))) S :=
    (integrableOn_inv_abs_rpow_exterior hα.1 hR).const_mul (2 * u x₀)
  have hmeas_pow : Measurable (fun y : ℝ ↦ (|y| ^ (1 + α))⁻¹) :=
    (continuous_abs.rpow_const (fun _ ↦ Or.inr (by linarith [hα.1]))).measurable.inv
  have hint_p : IntegrableOn (fun y : ℝ ↦ v (x₀ + y) / |y| ^ (1 + α)) S := by
    have hdom : Integrable (fun y : ℝ ↦ (1 / R ^ (1 + α)) * |v (x₀ + y)|) :=
      (hint_v.comp_add_left x₀).abs.const_mul (1 / R ^ (1 + α))
    refine hdom.integrableOn.mono' ?_ ?_
    · have hmul : AEStronglyMeasurable
          (fun y : ℝ ↦ v (x₀ + y) * (|y| ^ (1 + α))⁻¹) (volume.restrict S) :=
        ((hint_v.comp_add_left x₀).aestronglyMeasurable.mul
          hmeas_pow.aestronglyMeasurable).restrict
      simpa only [div_eq_mul_inv] using hmul
    · filter_upwards [ae_restrict_mem hS_meas] with y hy
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : 0 ≤ |y| ^ (1 + α)),
        div_eq_inv_mul, ← one_div]
      exact mul_le_mul_of_nonneg_right (hS_rpow y hy) (abs_nonneg _)
  have hint_m : IntegrableOn (fun y : ℝ ↦ v (x₀ - y) / |y| ^ (1 + α)) S := by
    have hint_sub : Integrable (fun y : ℝ ↦ v (x₀ - y)) := by
      simpa only [sub_eq_add_neg] using (hint_v.comp_add_left x₀).comp_neg
    have hdom : Integrable (fun y : ℝ ↦ (1 / R ^ (1 + α)) * |v (x₀ - y)|) :=
      hint_sub.abs.const_mul (1 / R ^ (1 + α))
    refine hdom.integrableOn.mono' ?_ ?_
    · have hmul : AEStronglyMeasurable
          (fun y : ℝ ↦ v (x₀ - y) * (|y| ^ (1 + α))⁻¹) (volume.restrict S) :=
        (hint_sub.aestronglyMeasurable.mul hmeas_pow.aestronglyMeasurable).restrict
      simpa only [div_eq_mul_inv] using hmul
    · filter_upwards [ae_restrict_mem hS_meas] with y hy
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : 0 ≤ |y| ^ (1 + α)),
        div_eq_inv_mul, ← one_div]
      exact mul_le_mul_of_nonneg_right (hS_rpow y hy) (abs_nonneg _)
  have hdecomp :
      (∫ y in S, -(secondDiff v x₀ y / |y| ^ (1 + α))) =
        (∫ y in S, (2 * u x₀) * (1 / |y| ^ (1 + α))) -
          (∫ y in S, v (x₀ + y) / |y| ^ (1 + α)) -
          (∫ y in S, v (x₀ - y) / |y| ^ (1 + α)) := by
    have hfun : (fun y : ℝ ↦ -(secondDiff v x₀ y / |y| ^ (1 + α))) =
        (fun y : ℝ ↦ (2 * u x₀) * (1 / |y| ^ (1 + α)) -
          v (x₀ + y) / |y| ^ (1 + α) - v (x₀ - y) / |y| ^ (1 + α)) := by
      funext y
      unfold secondDiff
      rw [hv_x₀]
      ring
    rw [hfun]
    rw [integral_sub (f := fun y : ℝ ↦ (2 * u x₀) * (1 / |y| ^ (1 + α)) -
        v (x₀ + y) / |y| ^ (1 + α)) (g := fun y : ℝ ↦ v (x₀ - y) / |y| ^ (1 + α))
      (hint_ext.sub hint_p) hint_m]
    rw [integral_sub (f := fun y : ℝ ↦ (2 * u x₀) * (1 / |y| ^ (1 + α)))
      (g := fun y : ℝ ↦ v (x₀ + y) / |y| ^ (1 + α)) hint_ext hint_p]
  have hmain_eq :
      (fracLapConstant α / 2) * (∫ y in S, (2 * u x₀) * (1 / |y| ^ (1 + α))) =
        nlmpConstantC1 α * u x₀ / R ^ α := by
    rw [integral_const_mul, integral_inv_abs_rpow_exterior hα.1 hR]
    unfold nlmpConstantC1
    have h2R_pow : (2 * R) ^ α = (2 : ℝ) ^ α * R ^ α := mul_rpow (by norm_num) hR.le
    have h2_sub : (2 : ℝ) ^ (α - 1) = (2 : ℝ) ^ α / 2 := by
      rw [rpow_sub (by norm_num : (0 : ℝ) < 2), rpow_one]
    have hα_ne : α ≠ 0 := ne_of_gt hα.1
    have h2a_ne : (2 : ℝ) ^ α ≠ 0 := ne_of_gt (by positivity)
    have hRa_ne : R ^ α ≠ 0 := ne_of_gt (rpow_pos_of_pos hR α)
    rw [h2R_pow, h2_sub]
    field_simp
  have hbound_p : (∫ y in S, v (x₀ + y) / |y| ^ (1 + α)) ≤ 2 * M / R ^ (1 + α) := by
    have h1 : ∀ y ∈ S, v (x₀ + y) / |y| ^ (1 + α) ≤ (1 / R ^ (1 + α)) * |v (x₀ + y)| := by
      intro y hy
      calc
        v (x₀ + y) / |y| ^ (1 + α)
            ≤ |v (x₀ + y)| / |y| ^ (1 + α) :=
          div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
        _ = (1 / |y| ^ (1 + α)) * |v (x₀ + y)| := by rw [div_eq_mul_inv, one_div, mul_comm]
        _ ≤ (1 / R ^ (1 + α)) * |v (x₀ + y)| :=
          mul_le_mul_of_nonneg_right (hS_rpow y hy) (abs_nonneg _)
    have hint_dom : Integrable (fun y : ℝ ↦ (1 / R ^ (1 + α)) * |v (x₀ + y)|) :=
      (hint_v.comp_add_left x₀).abs.const_mul (1 / R ^ (1 + α))
    have hle1 :
        (∫ y in S, v (x₀ + y) / |y| ^ (1 + α)) ≤
          ∫ y in S, (1 / R ^ (1 + α)) * |v (x₀ + y)| :=
      setIntegral_mono_on hint_p hint_dom.integrableOn hS_meas h1
    have hle2 :
        (∫ y in S, (1 / R ^ (1 + α)) * |v (x₀ + y)|) ≤
          ∫ y : ℝ, (1 / R ^ (1 + α)) * |v (x₀ + y)| :=
      setIntegral_le_integral hint_dom
        (Eventually.of_forall fun y ↦ mul_nonneg (by positivity) (abs_nonneg _))
    have hval : (∫ y : ℝ, (1 / R ^ (1 + α)) * |v (x₀ + y)|) = 2 * M / R ^ (1 + α) := by
      rw [integral_const_mul, integral_add_left_eq_self (fun z : ℝ ↦ |v z|) x₀,
        integral_abs_oddExt hnonneg hint_u]
      ring
    linarith
  have hbound_m : (∫ y in S, v (x₀ - y) / |y| ^ (1 + α)) ≤ 2 * M / R ^ (1 + α) := by
    have h1 : ∀ y ∈ S, v (x₀ - y) / |y| ^ (1 + α) ≤ (1 / R ^ (1 + α)) * |v (x₀ - y)| := by
      intro y hy
      calc
        v (x₀ - y) / |y| ^ (1 + α)
            ≤ |v (x₀ - y)| / |y| ^ (1 + α) :=
          div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
        _ = (1 / |y| ^ (1 + α)) * |v (x₀ - y)| := by rw [div_eq_mul_inv, one_div, mul_comm]
        _ ≤ (1 / R ^ (1 + α)) * |v (x₀ - y)| :=
          mul_le_mul_of_nonneg_right (hS_rpow y hy) (abs_nonneg _)
    have hint_sub : Integrable (fun y : ℝ ↦ v (x₀ - y)) := by
      simpa only [sub_eq_add_neg] using (hint_v.comp_add_left x₀).comp_neg
    have hint_dom : Integrable (fun y : ℝ ↦ (1 / R ^ (1 + α)) * |v (x₀ - y)|) :=
      hint_sub.abs.const_mul (1 / R ^ (1 + α))
    have hle1 :
        (∫ y in S, v (x₀ - y) / |y| ^ (1 + α)) ≤
          ∫ y in S, (1 / R ^ (1 + α)) * |v (x₀ - y)| :=
      setIntegral_mono_on hint_m hint_dom.integrableOn hS_meas h1
    have hle2 :
        (∫ y in S, (1 / R ^ (1 + α)) * |v (x₀ - y)|) ≤
          ∫ y : ℝ, (1 / R ^ (1 + α)) * |v (x₀ - y)| :=
      setIntegral_le_integral hint_dom
        (Eventually.of_forall fun y ↦ mul_nonneg (by positivity) (abs_nonneg _))
    have hval : (∫ y : ℝ, (1 / R ^ (1 + α)) * |v (x₀ - y)|) = 2 * M / R ^ (1 + α) := by
      rw [integral_const_mul, integral_sub_left_eq_self (fun z : ℝ ↦ |v z|) volume x₀,
        integral_abs_oddExt hnonneg hint_u]
      ring
    linarith
  have hM_nonneg : 0 ≤ M :=
    setIntegral_nonneg measurableSet_Ioi fun x hx ↦ hnonneg x hx
  have hC2_ge : 2 * fracLapConstant α ≤ nlmpConstantC2 α := by
    unfold nlmpConstantC2
    have h8a : 0 ≤ 8 / α := div_nonneg (by norm_num) hα.1.le
    nlinarith
  have hrem_le :
      (fracLapConstant α / 2) *
          ((∫ y in S, v (x₀ + y) / |y| ^ (1 + α)) +
            ∫ y in S, v (x₀ - y) / |y| ^ (1 + α)) ≤
        nlmpConstantC2 α * M / R ^ (1 + α) := by
    have hsum_eq : 2 * M / R ^ (1 + α) + 2 * M / R ^ (1 + α) = 4 * M / R ^ (1 + α) := by ring
    have hsum :
        (∫ y in S, v (x₀ + y) / |y| ^ (1 + α)) +
            ∫ y in S, v (x₀ - y) / |y| ^ (1 + α) ≤
          4 * M / R ^ (1 + α) := by linarith [hbound_p, hbound_m, hsum_eq]
    have hmul :
        (fracLapConstant α / 2) *
            ((∫ y in S, v (x₀ + y) / |y| ^ (1 + α)) +
              ∫ y in S, v (x₀ - y) / |y| ^ (1 + α)) ≤
          (fracLapConstant α / 2) * (4 * M / R ^ (1 + α)) :=
      mul_le_mul_of_nonneg_left hsum (by linarith)
    have heq2 : (fracLapConstant α / 2) * (4 * M / R ^ (1 + α)) =
        (2 * fracLapConstant α) * (M / R ^ (1 + α)) := by ring
    have hleC2 :
        (2 * fracLapConstant α) * (M / R ^ (1 + α)) ≤
          nlmpConstantC2 α * (M / R ^ (1 + α)) :=
      mul_le_mul_of_nonneg_right hC2_ge (div_nonneg hM_nonneg (by positivity))
    have heqC2 : nlmpConstantC2 α * (M / R ^ (1 + α)) =
        nlmpConstantC2 α * M / R ^ (1 + α) := by ring
    linarith
  have hsplit_mul :
      (fracLapConstant α / 2) * ∫ y in S, -(secondDiff v x₀ y / |y| ^ (1 + α)) =
        (fracLapConstant α / 2) * (∫ y in S, (2 * u x₀) * (1 / |y| ^ (1 + α))) -
          (fracLapConstant α / 2) *
            ((∫ y in S, v (x₀ + y) / |y| ^ (1 + α)) +
              ∫ y in S, v (x₀ - y) / |y| ^ (1 + α)) := by
    rw [hdecomp]
    ring
  rw [hsplit_mul, hmain_eq] at hlower
  linarith

/-- **Unconditional Half-Line Constantin–Vicol Nonlinear Maximum Principle**:
For any `α ∈ (0, 2)` and nonnegative `u ∈ L¹(0, ∞)` attaining a strictly positive global
maximum at `x₀ > 0` with `‖u‖_{L¹(0, ∞)} > 0` and integrable weighted second difference at `x₀`,
`(-Δ̃)^(α / 2) u(x₀) ≥ nlmpOptimalConstant α * u(x₀)^(1 + α) / (∫₀^∞ u)^α`. -/
theorem reflectedFracLapSecondDiff_nonlinear_max_principle
    {α : ℝ} (hα : FractionalExponent α) {u : ℝ → ℝ} {x₀ : ℝ}
    (hx₀ : 0 < x₀) (hu₀ : 0 < u x₀)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ u x)
    (hmax : ∀ x : ℝ, 0 < x → u x ≤ u x₀)
    (hint_u : IntegrableOn u (Ioi 0))
    (hM : 0 < ∫ x in Ioi (0 : ℝ), u x)
    (hint_fl : Integrable (fun y : ℝ ↦ secondDiff (oddExt u) x₀ y / |y| ^ (1 + α))) :
    nlmpOptimalConstant α *
      (u x₀ ^ (1 + α) / (∫ x in Ioi (0 : ℝ), u x) ^ α) ≤
      reflectedFracLapSecondDiff α u x₀ :=
  nonlinear_max_principle hα hu₀ hM
    (reflectedFracLapSecondDiff_satisfiesCutoffAntiderivativeBound
      hα hx₀ hnonneg hmax hint_u hint_fl)

end

end FracLap
