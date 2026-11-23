/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# FracLap.Tools.CompleteBernstein

Derivative estimates for complete Bernstein functions in the Stieltjes representation
(Kim--Song--Vondraček, Kwaśnicki).

For `a, b ≥ 0` and a measure `σ` on `[0, ∞)` with `∫ (1 + s)⁻¹ dσ < ∞`, put
`f(z) = a + b z + ∫ z / (z + s) dσ(s)` for `z > 0`. Then `f` is smooth with
`f′(z) = b + ∫ s / (z + s)² dσ` and `f″(z) = -2 ∫ s / (z + s)³ dσ`, and

* `0 ≤ z f′(z) ≤ f(z)` (`cbf_mul_deriv_le`),
* `0 ≤ -z f″(z) ≤ 2 f′(z)` (`cbf_neg_mul_deriv2_le`).

The second estimate fails for general Bernstein functions (`1 - e^{-z}` at `z = 3`).
-/

namespace FracLap

open MeasureTheory Set

@[expose] public section

/-- The complete Bernstein function `a + b z + ∫ z / (z + s) dσ(s)`. -/
noncomputable def cbf (a b : ℝ) (σ : Measure ℝ) (z : ℝ) : ℝ :=
  a + b * z + ∫ s, z / (z + s) ∂σ

/-- The first derivative `b + ∫ s / (z + s)² dσ(s)`. -/
noncomputable def cbfDeriv (b : ℝ) (σ : Measure ℝ) (z : ℝ) : ℝ :=
  b + ∫ s, s / (z + s) ^ 2 ∂σ

/-- The second derivative `-2 ∫ s / (z + s)³ dσ(s)`. -/
noncomputable def cbfDeriv2 (σ : Measure ℝ) (z : ℝ) : ℝ :=
  -2 * ∫ s, s / (z + s) ^ 3 ∂σ

/-- Elementary bound: `1 / (c + s) ≤ max 1 (1/c) / (1 + s)` for `c > 0`, `s ≥ 0`. -/
theorem inv_add_le_max {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s) :
    1 / (c + s) ≤ max 1 (1 / c) / (1 + s) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rcases le_total c 1 with h | h
  · have : max 1 (1 / c) = 1 / c := max_eq_right (by rw [le_div_iff₀ hc]; linarith)
    rw [this]
    have : 1 / c * (c + s) = 1 + s / c := by field_simp
    rw [one_mul, this]
    have : s / c ≥ s := by rw [ge_iff_le, le_div_iff₀ hc]; nlinarith
    linarith
  · have : max 1 (1 / c) = 1 := max_eq_left (by rw [div_le_iff₀ hc]; linarith)
    rw [this]; linarith

/-- An a.e.-measurable function dominated by `K / (1 + s)` on `s ≥ 0` is `σ`-integrable. -/
theorem integrable_of_le_inv {σ : Measure ℝ} (hσ0 : ∀ᵐ s ∂σ, 0 ≤ s)
    (hint : Integrable (fun s : ℝ => 1 / (1 + s)) σ) {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g σ) {K : ℝ} (hbd : ∀ s, 0 ≤ s → ‖g s‖ ≤ K / (1 + s)) :
    Integrable g σ := by
  refine ((hint.const_mul K).mono' hg ?_)
  filter_upwards [hσ0] with s hs
  change ‖g s‖ ≤ K * (1 / (1 + s))
  rw [mul_one_div]
  exact hbd s hs

/-- Differentiation under the integral sign for parameter integrals against `σ` with an
`(1 + s)⁻¹`-type dominating function, uniformly for `z > z₀ / 2`. -/
theorem hasDerivAt_integral_sigma {σ : Measure ℝ} (hσ0 : ∀ᵐ s ∂σ, 0 ≤ s)
    (hint : Integrable (fun s : ℝ => 1 / (1 + s)) σ) {F F' : ℝ → ℝ → ℝ} {z₀ : ℝ} (hz₀ : 0 < z₀)
    (hFm : ∀ z, AEStronglyMeasurable (F z) σ) (hFi : Integrable (F z₀) σ)
    (hF'm : AEStronglyMeasurable (F' z₀) σ)
    (hbd : ∃ K : ℝ, ∀ z, z₀ / 2 < z → ∀ s, 0 ≤ s → ‖F' z s‖ ≤ K / (1 + s))
    (hdiff : ∀ s, 0 ≤ s → ∀ z, 0 < z → HasDerivAt (fun z => F z s) (F' z s) z) :
    Integrable (F' z₀) σ ∧ HasDerivAt (fun z => ∫ s, F z s ∂σ) (∫ s, F' z₀ s ∂σ) z₀ := by
  obtain ⟨K, hK⟩ := hbd
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Ioi (z₀ / 2))
    (bound := fun s => K * (1 / (1 + s))) (Ioi_mem_nhds (by linarith))
    (Filter.Eventually.of_forall hFm) hFi hF'm ?_ (hint.const_mul K) ?_
  · filter_upwards [hσ0] with s hs z hz
    change ‖F' z s‖ ≤ K * (1 / (1 + s))
    rw [mul_one_div]
    exact hK z hz s hs
  · filter_upwards [hσ0] with s hs z hz
    exact hdiff s hs z (lt_trans (by linarith) hz)

/-- `z / (z + s) ≤ max 1 z / (1 + s)` for `z > 0`, `s ≥ 0`. -/
theorem ratio_le_max {z s : ℝ} (hz : 0 < z) (hs : 0 ≤ s) :
    z / (z + s) ≤ max 1 z / (1 + s) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rcases le_total z 1 with h | h
  · rw [max_eq_left h]; nlinarith
  · rw [max_eq_right h]; nlinarith

/-- `s / (z + s)² ≤ 1 / (z + s)`. -/
theorem sq_ratio_le {z s : ℝ} (hz : 0 < z) (hs : 0 ≤ s) : s / (z + s) ^ 2 ≤ 1 / (z + s) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `s / (z + s)³ ≤ 1 / (c (z + s))` when `0 < c < z`. -/
theorem cube_ratio_le {z s c : ℝ} (hc : 0 < c) (hcz : c < z) (hs : 0 ≤ s) :
    s / (z + s) ^ 3 ≤ 1 / (c * (z + s)) := by
  have hz : 0 < z := hc.trans hcz
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 ≤ z + s := by positivity
  nlinarith [mul_nonneg h1 (sq_nonneg (z + s)), mul_nonneg hs (sq_nonneg (z + s)),
    mul_pos hc hz, sq_nonneg (z + s), mul_nonneg h1 hs]

/-- Pointwise derivative of `z ↦ z / (z + s)`. -/
theorem hasDerivAt_ratio {s z : ℝ} (hz : 0 < z) (hs : 0 ≤ s) :
    HasDerivAt (fun z => z / (z + s)) (s / (z + s) ^ 2) z := by
  have hne : z + s ≠ 0 := by positivity
  have h := HasDerivAt.fun_div (hasDerivAt_id' z) ((hasDerivAt_id' z).add_const s) hne
  convert h using 1
  field_simp
  ring

/-- Pointwise derivative of `z ↦ s / (z + s)²`. -/
theorem hasDerivAt_sq_ratio {s z : ℝ} (hz : 0 < z) (hs : 0 ≤ s) :
    HasDerivAt (fun z => s / (z + s) ^ 2) (-2 * s / (z + s) ^ 3) z := by
  have hne : z + s ≠ 0 := by positivity
  have h := HasDerivAt.fun_pow ((hasDerivAt_id' z).add_const s) 2
  have hne2 : (z + s) ^ 2 ≠ 0 := by positivity
  have h2 := HasDerivAt.fun_div (hasDerivAt_const z s) h hne2
  convert h2 using 1
  field_simp
  ring

theorem measurable_ratio (z : ℝ) : Measurable fun s : ℝ => z / (z + s) := by fun_prop

theorem measurable_ratio2 (z : ℝ) : Measurable fun s : ℝ => s / (z + s) ^ 2 := by fun_prop

theorem measurable_ratio3 (z : ℝ) : Measurable fun s : ℝ => s / (z + s) ^ 3 := by fun_prop

/-- Integrability of `s ↦ z / (z + s)` against `σ`. -/
theorem integrable_cbf_kernel {σ : Measure ℝ} (hσ0 : ∀ᵐ s ∂σ, 0 ≤ s)
    (hint : Integrable (fun s : ℝ => 1 / (1 + s)) σ) {z : ℝ} (hz : 0 < z) :
    Integrable (fun s : ℝ => z / (z + s)) σ := by
  refine integrable_of_le_inv hσ0 hint (measurable_ratio z).aestronglyMeasurable
    (K := max 1 z) fun s hs => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact ratio_le_max hz hs

/-- Integrability of `s ↦ s / (z + s)²` against `σ`. -/
theorem integrable_cbf_kernel_deriv {σ : Measure ℝ} (hσ0 : ∀ᵐ s ∂σ, 0 ≤ s)
    (hint : Integrable (fun s : ℝ => 1 / (1 + s)) σ) {z : ℝ} (hz : 0 < z) :
    Integrable (fun s : ℝ => s / (z + s) ^ 2) σ := by
  refine integrable_of_le_inv hσ0 hint
    (measurable_ratio2 z).aestronglyMeasurable (K := max 1 (1 / z)) fun s hs => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact (sq_ratio_le hz hs).trans (inv_add_le_max hz hs)

/-- Integrability of `s ↦ s / (z + s)³` against `σ`. -/
theorem integrable_cbf_kernel_deriv2 {σ : Measure ℝ} (hσ0 : ∀ᵐ s ∂σ, 0 ≤ s)
    (hint : Integrable (fun s : ℝ => 1 / (1 + s)) σ) {z : ℝ} (hz : 0 < z) :
    Integrable (fun s : ℝ => s / (z + s) ^ 3) σ := by
  refine integrable_of_le_inv hσ0 hint
    (measurable_ratio3 z).aestronglyMeasurable
    (K := 1 / (z / 2) * max 1 (1 / z)) fun s hs => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  calc s / (z + s) ^ 3 ≤ 1 / (z / 2 * (z + s)) := cube_ratio_le (by positivity) (by linarith) hs
    _ = 1 / (z / 2) * (1 / (z + s)) := by field_simp
    _ ≤ 1 / (z / 2) * (max 1 (1 / z) / (1 + s)) := by
        exact mul_le_mul_of_nonneg_left (inv_add_le_max hz hs) (by positivity)
    _ = _ := by ring

/-- `cbf` is differentiable on `(0, ∞)` with derivative `cbfDeriv`. -/
theorem hasDerivAt_cbf {a b : ℝ} {σ : Measure ℝ} (hσ0 : ∀ᵐ s ∂σ, 0 ≤ s)
    (hint : Integrable (fun s : ℝ => 1 / (1 + s)) σ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (cbf a b σ) (cbfDeriv b σ z) z := by
  have hF := hasDerivAt_integral_sigma (F := fun z s => z / (z + s))
    (F' := fun z s => s / (z + s) ^ 2) hσ0 hint hz
    (fun z => (measurable_ratio z).aestronglyMeasurable) (integrable_cbf_kernel hσ0 hint hz)
    (measurable_ratio2 z).aestronglyMeasurable
    ⟨max 1 (1 / (z / 2)), fun z' hz' s hs => ?_⟩ (fun s hs z' hz' => hasDerivAt_ratio hz' hs)
  · have h : HasDerivAt (fun z => a + b * z + ∫ s, z / (z + s) ∂σ)
        (0 + b * 1 + ∫ s, s / (z + s) ^ 2 ∂σ) z :=
      ((hasDerivAt_const z a).fun_add ((hasDerivAt_id' z).const_mul b)).fun_add hF.2
    have e : cbfDeriv b σ z = 0 + b * 1 + ∫ s, s / (z + s) ^ 2 ∂σ := by
      unfold cbfDeriv; ring
    rw [e]
    exact h
  · have hz'pos : 0 < z' := lt_trans (by linarith) hz'
    rw [Real.norm_of_nonneg (by positivity)]
    calc s / (z' + s) ^ 2 ≤ 1 / (z' + s) := sq_ratio_le hz'pos hs
      _ ≤ 1 / (z / 2 + s) := one_div_le_one_div_of_le (by positivity) (by linarith)
      _ ≤ _ := inv_add_le_max (by linarith) hs

/-- `cbfDeriv` is differentiable on `(0, ∞)` with derivative `cbfDeriv2`. -/
theorem hasDerivAt_cbfDeriv {b : ℝ} {σ : Measure ℝ} (hσ0 : ∀ᵐ s ∂σ, 0 ≤ s)
    (hint : Integrable (fun s : ℝ => 1 / (1 + s)) σ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (cbfDeriv b σ) (cbfDeriv2 σ z) z := by
  have hm3 : ∀ z : ℝ, Measurable fun s : ℝ => -2 * s / (z + s) ^ 3 := fun z => by fun_prop
  have hF := hasDerivAt_integral_sigma (F := fun z s => s / (z + s) ^ 2)
    (F' := fun z s => -2 * s / (z + s) ^ 3) hσ0 hint hz
    (fun z => (measurable_ratio2 z).aestronglyMeasurable)
    (integrable_cbf_kernel_deriv hσ0 hint hz) (hm3 z).aestronglyMeasurable
    ⟨2 * (1 / (z / 2)) * max 1 (1 / (z / 2)), fun z' hz' s hs => ?_⟩
    (fun s hs z' hz' => hasDerivAt_sq_ratio hz' hs)
  · have h : HasDerivAt (fun z => b + ∫ s, s / (z + s) ^ 2 ∂σ)
        (0 + ∫ s, -2 * s / (z + s) ^ 3 ∂σ) z :=
      (hasDerivAt_const z b).fun_add hF.2
    have e : cbfDeriv2 σ z = 0 + ∫ s, -2 * s / (z + s) ^ 3 ∂σ := by
      unfold cbfDeriv2
      have : ∀ s : ℝ, -2 * s / (z + s) ^ 3 = -2 * (s / (z + s) ^ 3) := fun s => by ring
      simp_rw [this]
      rw [integral_const_mul]; ring
    rw [e]
    exact h
  · have hz'pos : 0 < z' := lt_trans (by linarith) hz'
    have h1 : ‖-2 * s / (z' + s) ^ 3‖ = 2 * (s / (z' + s) ^ 3) := by
      rw [show -2 * s / (z' + s) ^ 3 = -(2 * (s / (z' + s) ^ 3)) by ring, norm_neg,
        Real.norm_of_nonneg (by positivity)]
    rw [h1]
    calc 2 * (s / (z' + s) ^ 3) ≤ 2 * (1 / (z / 2 * (z' + s))) :=
          mul_le_mul_of_nonneg_left (cube_ratio_le (by positivity) hz' hs) (by norm_num)
      _ = 2 * (1 / (z / 2)) * (1 / (z' + s)) := by field_simp
      _ ≤ 2 * (1 / (z / 2)) * (1 / (z / 2 + s)) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) (by linarith))
            (by positivity)
      _ ≤ 2 * (1 / (z / 2)) * (max 1 (1 / (z / 2)) / (1 + s)) :=
          mul_le_mul_of_nonneg_left (inv_add_le_max (by positivity) hs) (by positivity)
      _ = _ := by ring

/-- `0 ≤ f′`. -/
theorem cbfDeriv_nonneg {b : ℝ} (hb : 0 ≤ b) {σ : Measure ℝ} (hσ0 : ∀ᵐ s ∂σ, 0 ≤ s) {z : ℝ}
    (hz : 0 < z) : 0 ≤ cbfDeriv b σ z := by
  unfold cbfDeriv
  refine add_nonneg hb (integral_nonneg_of_ae ?_)
  filter_upwards [hσ0] with s hs
  positivity

/-- **First complete-Bernstein estimate**: `z f′(z) ≤ f(z)` (for `a ≥ 0`). -/
theorem cbf_mul_deriv_le {a b : ℝ} (ha : 0 ≤ a) {σ : Measure ℝ}
    (hσ0 : ∀ᵐ s ∂σ, 0 ≤ s) (hint : Integrable (fun s : ℝ => 1 / (1 + s)) σ) {z : ℝ}
    (hz : 0 < z) : z * cbfDeriv b σ z ≤ cbf a b σ z := by
  unfold cbfDeriv cbf
  have hi := integrable_cbf_kernel_deriv hσ0 hint hz
  have hk := integrable_cbf_kernel hσ0 hint hz
  have hle : ∫ s, z * (s / (z + s) ^ 2) ∂σ ≤ ∫ s, z / (z + s) ∂σ := by
    refine integral_mono_of_nonneg ?_ hk ?_
    · filter_upwards [hσ0] with s hs; positivity
    · filter_upwards [hσ0] with s hs
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      have h0 : 0 ≤ z + s := by positivity
      nlinarith [mul_nonneg (mul_nonneg hz.le hz.le) h0]
  rw [mul_add, integral_const_mul] at *
  nlinarith

/-- **Second complete-Bernstein estimate**: `0 ≤ -z f″(z) ≤ 2 f′(z)` (for `b ≥ 0`). -/
theorem cbf_neg_mul_deriv2_le {b : ℝ} (hb : 0 ≤ b) {σ : Measure ℝ}
    (hσ0 : ∀ᵐ s ∂σ, 0 ≤ s) (hint : Integrable (fun s : ℝ => 1 / (1 + s)) σ) {z : ℝ}
    (hz : 0 < z) : 0 ≤ -(z * cbfDeriv2 σ z) ∧ -(z * cbfDeriv2 σ z) ≤ 2 * cbfDeriv b σ z := by
  have hi2 := integrable_cbf_kernel_deriv hσ0 hint hz
  have hi3 := integrable_cbf_kernel_deriv2 hσ0 hint hz
  have hnn : 0 ≤ ∫ s, s / (z + s) ^ 3 ∂σ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hσ0] with s hs; positivity
  have hle : z * ∫ s, s / (z + s) ^ 3 ∂σ ≤ ∫ s, s / (z + s) ^ 2 ∂σ := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg ?_ hi2 ?_
    · filter_upwards [hσ0] with s hs; positivity
    · filter_upwards [hσ0] with s hs
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : 0 ≤ s * z := mul_nonneg hs hz.le
      nlinarith [mul_nonneg h1 (sq_nonneg (z + s)), mul_nonneg hs (sq_nonneg (z + s)),
        mul_nonneg (mul_nonneg hs hz.le) hs]
  have hd2 : cbfDeriv2 σ z = -2 * ∫ s, s / (z + s) ^ 3 ∂σ := rfl
  have hI : 0 ≤ ∫ s, s / (z + s) ^ 2 ∂σ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hσ0] with s hs; positivity
  refine ⟨?_, ?_⟩
  · rw [hd2]; nlinarith [mul_nonneg hz.le hnn]
  · unfold cbfDeriv
    rw [hd2]
    nlinarith

end

end FracLap
