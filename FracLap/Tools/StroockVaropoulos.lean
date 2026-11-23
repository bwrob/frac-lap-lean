/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import FracLap.Tools.Symmetrization
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# FracLap.Tools.StroockVaropoulos

The Stroock--Varopoulos inequality (Biler--Imbert--Karch, Prop. SV; Liskevich--Semenov;
Stroock--Varopoulos), in its two-point form. For `q > 1` write `φ(s) = sgn s |s|^(q-1)` and
`ψ(s) = sgn s |s|^(q/2)`. Then for all real `a, b`
`(4 (q - 1) / q²) (ψ a - ψ b)² ≤ (a - b) (φ a - φ b)`.

Integrating against any symmetric jump kernel gives the Stroock--Varopoulos inequality for the
corresponding nonlocal energy (see `FracLap.Tools.Symmetrization`).

- `sq_integral_le`: Cauchy--Schwarz on an interval, `(∫ f)² ≤ (b - a) ∫ f²`.
- `sv_pos`: the inequality for `0 < b ≤ a`, by Cauchy--Schwarz on `ψ' = (q/2) s^(q/2-1)`.
-/

namespace FracLap

open MeasureTheory Set intervalIntegral
open scoped ENNReal

@[expose] public section

/-- **Cauchy--Schwarz on an interval**: `(∫_a^b f)² ≤ (b - a) ∫_a^b f²` for continuous `f`. -/
theorem sq_integral_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    (∫ s in a..b, f s) ^ 2 ≤ (b - a) * ∫ s in a..b, f s ^ 2 := by
  have hf' : ContinuousOn f (uIcc a b) := by rwa [uIcc_of_le hab]
  have hi1 : IntervalIntegrable f volume a b := hf'.intervalIntegrable
  have hi2 : IntervalIntegrable (fun s => f s ^ 2) volume a b :=
    (hf'.pow 2).intervalIntegrable
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  set I := ∫ s in a..b, f s with hI
  set J := ∫ s in a..b, f s ^ 2 with hJ
  have hL : 0 < b - a := sub_pos.mpr hlt
  set m := I / (b - a) with hm
  have hnn : 0 ≤ ∫ s in a..b, (f s - m) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun s _ => sq_nonneg _
  have hexp : ∫ s in a..b, (f s - m) ^ 2 = J - 2 * m * I + m ^ 2 * (b - a) := by
    have : ∀ s, (f s - m) ^ 2 = f s ^ 2 - 2 * m * f s + m ^ 2 := fun s => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_add (hi2.sub (hi1.const_mul (2 * m))) intervalIntegrable_const,
      intervalIntegral.integral_sub hi2 (hi1.const_mul (2 * m)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hexp] at hnn
  have hmI : m * (b - a) = I := by rw [hm]; field_simp
  have : J - 2 * m * I + m ^ 2 * (b - a) = J - I ^ 2 / (b - a) := by
    rw [hm]; field_simp; ring
  rw [this] at hnn
  have h2 : I ^ 2 / (b - a) ≤ J := by linarith
  rw [div_le_iff₀ hL] at h2
  linarith

/-- FTC for a power on `[b, a]` with `0 < b`: `∫_b^a p s^(p-1) = a^p - b^p`. -/
theorem integral_rpow_deriv (p : ℝ) {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    ∫ s in b..a, p * s ^ (p - 1) = a ^ p - b ^ p := by
  have hpos : ∀ s ∈ uIcc b a, 0 < s := fun s hs => by
    rw [uIcc_of_le hab] at hs
    exact lt_of_lt_of_le hb hs.1
  refine integral_eq_sub_of_hasDerivAt (f := fun s : ℝ => s ^ p) (fun s hs => ?_) ?_
  · exact Real.hasDerivAt_rpow_const (Or.inl (hpos s hs).ne')
  · refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id fun s hs => ?_)
    exact Or.inl (hpos s hs).ne'

/-- **Stroock--Varopoulos, positive same-sign case**: for `q > 1` and `0 < b ≤ a`,
`(a^(q/2) - b^(q/2))² ≤ q² / (4 (q - 1)) · (a - b) (a^(q-1) - b^(q-1))`. -/
theorem sv_pos {q a b : ℝ} (hq : 1 < q) (hb : 0 < b) (hab : b ≤ a) :
    (a ^ (q / 2) - b ^ (q / 2)) ^ 2 ≤
      q ^ 2 / (4 * (q - 1)) * ((a - b) * (a ^ (q - 1) - b ^ (q - 1))) := by
  have hq1 : 0 < q - 1 := by linarith
  have hF : ∫ s in b..a, (q / 2) * s ^ (q / 2 - 1) = a ^ (q / 2) - b ^ (q / 2) :=
    integral_rpow_deriv (q / 2) hb hab
  have hG : ∫ s in b..a, (q - 1) * s ^ (q - 1 - 1) = a ^ (q - 1) - b ^ (q - 1) :=
    integral_rpow_deriv (q - 1) hb hab
  have hcont : ContinuousOn (fun s : ℝ => (q / 2) * s ^ (q / 2 - 1)) (Icc b a) := by
    refine continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id fun s hs => ?_)
    exact Or.inl (lt_of_lt_of_le hb hs.1).ne'
  have hcs := sq_integral_le hab hcont
  have hsq : ∀ s ∈ uIcc b a, ((q / 2) * s ^ (q / 2 - 1)) ^ 2 =
      q ^ 2 / (4 * (q - 1)) * ((q - 1) * s ^ (q - 1 - 1)) := by
    intro s hs
    have hs0 : 0 < s := by
      rw [uIcc_of_le hab] at hs
      exact lt_of_lt_of_le hb hs.1
    have e : (s ^ (q / 2 - 1)) ^ 2 = s ^ (q - 1 - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
      congr 1
      push_cast
      ring
    rw [mul_pow, e]
    field_simp
    norm_num
  have hint : ∫ s in b..a, ((q / 2) * s ^ (q / 2 - 1)) ^ 2 =
      q ^ 2 / (4 * (q - 1)) * (a ^ (q - 1) - b ^ (q - 1)) := by
    rw [intervalIntegral.integral_congr hsq, intervalIntegral.integral_const_mul, hG]
  rw [hF, hint] at hcs
  calc (a ^ (q / 2) - b ^ (q / 2)) ^ 2
      ≤ (a - b) * (q ^ 2 / (4 * (q - 1)) * (a ^ (q - 1) - b ^ (q - 1))) := hcs
    _ = q ^ 2 / (4 * (q - 1)) * ((a - b) * (a ^ (q - 1) - b ^ (q - 1))) := by ring

/-- The constant `q² / (4 (q - 1))` is at least `1`. -/
theorem one_le_sv_const {q : ℝ} (hq : 1 < q) : 1 ≤ q ^ 2 / (4 * (q - 1)) := by
  have hq1 : 0 < 4 * (q - 1) := by linarith
  rw [le_div_iff₀ hq1]
  nlinarith [sq_nonneg (q - 2)]

/-- `sv_pos` extended to `0 ≤ b ≤ a`. -/
theorem sv_nonneg {q a b : ℝ} (hq : 1 < q) (hb : 0 ≤ b) (hab : b ≤ a) :
    (a ^ (q / 2) - b ^ (q / 2)) ^ 2 ≤
      q ^ 2 / (4 * (q - 1)) * ((a - b) * (a ^ (q - 1) - b ^ (q - 1))) := by
  rcases hb.eq_or_lt with rfl | hb'
  · rcases hab.eq_or_lt with rfl | ha
    · simp
    · have h1 : (a ^ (q / 2)) ^ 2 = a ^ q := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
        congr 1
        push_cast
        ring
      have h2 : a * a ^ (q - 1) = a ^ q := by
        rw [← Real.rpow_one_add' ha.le (by linarith)]
        congr 1
        ring
      have hz : (0 : ℝ) ^ (q / 2) = 0 := Real.zero_rpow (by linarith)
      have hz' : (0 : ℝ) ^ (q - 1) = 0 := Real.zero_rpow (by linarith)
      rw [hz, hz', sub_zero, sub_zero, sub_zero, h1, h2]
      have := one_le_sv_const hq
      have hpos : 0 < a ^ q := Real.rpow_pos_of_pos ha q
      nlinarith
  · exact sv_pos hq hb' hab

/-- Signed power `spow p s = sgn s · |s|^p`. -/
noncomputable def spow (p s : ℝ) : ℝ := if 0 ≤ s then s ^ p else -((-s) ^ p)

/-- `spow` on nonnegative arguments. -/
theorem spow_of_nonneg (p : ℝ) {s : ℝ} (hs : 0 ≤ s) : spow p s = s ^ p := by
  simp [spow, hs]

/-- `spow` on negative arguments. -/
theorem spow_of_neg (p : ℝ) {s : ℝ} (hs : s < 0) : spow p s = -((-s) ^ p) := by
  simp [spow, not_le.mpr hs]

/-- `spow` is odd for positive exponents. -/
theorem spow_neg {p : ℝ} (hp : 0 < p) (s : ℝ) : spow p (-s) = -spow p s := by
  rcases lt_trichotomy s 0 with h | rfl | h
  · rw [spow_of_neg p h, spow_of_nonneg p (neg_nonneg.mpr h.le), neg_neg]
  · simp [spow, Real.zero_rpow hp.ne']
  · rw [spow_of_nonneg p h.le, spow_of_neg p (neg_lt_zero.mpr h), neg_neg]

/-- Opposite-sign case, by Cauchy--Schwarz in `ℝ²`: for `x, y ≥ 0`,
`(x^(q/2) + y^(q/2))² ≤ (x + y)(x^(q-1) + y^(q-1))`. -/
theorem sv_opposite {q x y : ℝ} (hq : 1 < q) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x ^ (q / 2) + y ^ (q / 2)) ^ 2 ≤ (x + y) * (x ^ (q - 1) + y ^ (q - 1)) := by
  have hsplit : ∀ z : ℝ, 0 ≤ z →
      z ^ (q / 2) = z ^ ((1 : ℝ) / 2) * z ^ ((q - 1) / 2) := fun z hz => by
    rw [← Real.rpow_add' hz (by linarith)]
    congr 1
    ring
  have hsq : ∀ (z r : ℝ), 0 ≤ z → (z ^ r) = (z ^ (r / 2)) ^ 2 := fun z r hz => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz]
    congr 1
    push_cast
    ring
  have e1 : x = (x ^ ((1 : ℝ) / 2)) ^ 2 := by
    have := hsq x 1 hx
    rwa [Real.rpow_one] at this
  have e2 : y = (y ^ ((1 : ℝ) / 2)) ^ 2 := by
    have := hsq y 1 hy
    rwa [Real.rpow_one] at this
  rw [hsplit x hx, hsplit y hy]
  set u := x ^ ((1 : ℝ) / 2)
  set u' := y ^ ((1 : ℝ) / 2)
  set v := x ^ ((q - 1) / 2)
  set v' := y ^ ((q - 1) / 2)
  have e3 : x ^ (q - 1) = v ^ 2 := hsq x (q - 1) hx
  have e4 : y ^ (q - 1) = v' ^ 2 := hsq y (q - 1) hy
  rw [e3, e4]
  conv_rhs => rw [e1, e2]
  nlinarith [sq_nonneg (u * v' - u' * v)]

/-- Nonnegative ordered case in terms of plain powers, with the sharp constant. -/
theorem sv_nn {q a b : ℝ} (hq : 1 < q) (hb : 0 ≤ b) (hba : b ≤ a) :
    4 * (q - 1) / q ^ 2 * (a ^ (q / 2) - b ^ (q / 2)) ^ 2 ≤
      (a - b) * (a ^ (q - 1) - b ^ (q - 1)) := by
  have hq1 : 0 < q - 1 := by linarith
  have hq0 : 0 < q := by linarith
  have hK : q ^ 2 / (4 * (q - 1)) * (4 * (q - 1) / q ^ 2) = 1 := by field_simp
  have hc0 : 0 ≤ 4 * (q - 1) / q ^ 2 := by positivity
  have h := sv_nonneg hq hb hba
  calc 4 * (q - 1) / q ^ 2 * (a ^ (q / 2) - b ^ (q / 2)) ^ 2
      ≤ 4 * (q - 1) / q ^ 2 *
          (q ^ 2 / (4 * (q - 1)) * ((a - b) * (a ^ (q - 1) - b ^ (q - 1)))) :=
        mul_le_mul_of_nonneg_left h hc0
    _ = (a - b) * (a ^ (q - 1) - b ^ (q - 1)) := by
        rw [← mul_assoc, mul_comm (4 * (q - 1) / q ^ 2), hK, one_mul]

/-- **Stroock--Varopoulos two-point inequality, ordered case**: for `q > 1` and `b ≤ a`,
`(4 (q - 1) / q²) (ψ a - ψ b)² ≤ (a - b) (φ a - φ b)` with `ψ = spow (q/2)`, `φ = spow (q-1)`. -/
theorem sv_two_point_of_le {q a b : ℝ} (hq : 1 < q) (hba : b ≤ a) :
    4 * (q - 1) / q ^ 2 * (spow (q / 2) a - spow (q / 2) b) ^ 2 ≤
      (a - b) * (spow (q - 1) a - spow (q - 1) b) := by
  have hq0 : 0 < q := by linarith
  have hc1 : 4 * (q - 1) / q ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg (q - 2)]
  rcases le_or_gt 0 b with hb | hb
  · rw [spow_of_nonneg _ hb, spow_of_nonneg _ (hb.trans hba), spow_of_nonneg _ hb,
      spow_of_nonneg _ (hb.trans hba)]
    exact sv_nn hq hb hba
  · rcases le_or_gt 0 a with ha | ha
    · rw [spow_of_nonneg _ ha, spow_of_neg _ hb, spow_of_nonneg _ ha, spow_of_neg _ hb]
      have h := sv_opposite hq ha (neg_nonneg.mpr hb.le)
      have e : (a ^ (q / 2) - -(-b) ^ (q / 2)) ^ 2 = (a ^ (q / 2) + (-b) ^ (q / 2)) ^ 2 := by
        ring
      have e' : (a - b) * (a ^ (q - 1) - -(-b) ^ (q - 1)) =
          (a + -b) * (a ^ (q - 1) + (-b) ^ (q - 1)) := by ring
      rw [e, e']
      have hnn : 0 ≤ (a ^ (q / 2) + (-b) ^ (q / 2)) ^ 2 := sq_nonneg _
      nlinarith
    · rw [spow_of_neg _ ha, spow_of_neg _ hb, spow_of_neg _ ha, spow_of_neg _ hb]
      have h := sv_nn hq (neg_nonneg.mpr ha.le) (neg_le_neg_iff.mpr hba)
      have e : (-(-a) ^ (q / 2) - -(-b) ^ (q / 2)) ^ 2 =
          ((-b) ^ (q / 2) - (-a) ^ (q / 2)) ^ 2 := by ring
      have e' : (a - b) * (-(-a) ^ (q - 1) - -(-b) ^ (q - 1)) =
          (-b - -a) * ((-b) ^ (q - 1) - (-a) ^ (q - 1)) := by ring
      rw [e, e']
      exact h

/-- **Stroock--Varopoulos two-point inequality**: for `q > 1` and all real `a, b`,
`(4 (q - 1) / q²) (ψ a - ψ b)² ≤ (a - b) (φ a - φ b)`, where `ψ = spow (q/2)` and
`φ = spow (q - 1)` are the signed powers `sgn s |s|^(q/2)` and `sgn s |s|^(q-1)`. -/
theorem sv_two_point {q : ℝ} (hq : 1 < q) (a b : ℝ) :
    4 * (q - 1) / q ^ 2 * (spow (q / 2) a - spow (q / 2) b) ^ 2 ≤
      (a - b) * (spow (q - 1) a - spow (q - 1) b) := by
  rcases le_total b a with h | h
  · exact sv_two_point_of_le hq h
  · have := sv_two_point_of_le hq h
    nlinarith [this]

/-- Version with `|·|^(q/2)` on the left: `(4 (q - 1) / q²) (|a|^(q/2) - |b|^(q/2))² ≤
(a - b) (φ a - φ b)`, as `||x| - |y|| ≤ |x - y|`. -/
theorem sv_two_point_abs {q : ℝ} (hq : 1 < q) (a b : ℝ) :
    4 * (q - 1) / q ^ 2 * (|a| ^ (q / 2) - |b| ^ (q / 2)) ^ 2 ≤
      (a - b) * (spow (q - 1) a - spow (q - 1) b) := by
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (by
    have : 0 < q := by linarith
    have : 0 < q - 1 := by linarith
    positivity)) (sv_two_point hq a b)
  have habs : ∀ s : ℝ, |spow (q / 2) s| = |s| ^ (q / 2) := by
    intro s
    rcases le_or_gt 0 s with hs | hs
    · rw [spow_of_nonneg _ hs, abs_of_nonneg hs, abs_of_nonneg (Real.rpow_nonneg hs _)]
    · rw [spow_of_neg _ hs, abs_neg, abs_of_neg hs,
        abs_of_nonneg (Real.rpow_nonneg (neg_nonneg.mpr hs.le) _)]
  rw [← habs a, ← habs b]
  set x := spow (q / 2) a
  set y := spow (q / 2) b
  have h := abs_abs_sub_abs_le_abs_sub x y
  calc (|x| - |y|) ^ 2 = (abs (|x| - |y|)) ^ 2 := (sq_abs _).symm
    _ ≤ (abs (x - y)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = (x - y) ^ 2 := sq_abs _

/-! ### Stroock--Varopoulos for nonlocal energies -/

variable {X : Type*} [MeasurableSpace X]

/-- **Stroock--Varopoulos inequality, lower-integral form.** For every weight `w` on `X × X` and
every measure `ν`, with `ψ = spow (q/2)` and `φ = spow (q - 1)`,
`(4 (q - 1) / q²) ∬ w (ψ u x - ψ u y)² ≤ ∬ w (u x - u y)(φ u x - φ u y)`.
No integrability or symmetry is needed. -/
theorem sv_lintegral {q : ℝ} (hq : 1 < q) (ν : Measure (X × X)) (w : X × X → ℝ≥0∞) (u : X → ℝ) :
    ENNReal.ofReal (4 * (q - 1) / q ^ 2) *
        ∫⁻ z, w z * ENNReal.ofReal ((spow (q / 2) (u z.1) - spow (q / 2) (u z.2)) ^ 2) ∂ν ≤
      ∫⁻ z, w z * ENNReal.ofReal
        ((u z.1 - u z.2) * (spow (q - 1) (u z.1) - spow (q - 1) (u z.2))) ∂ν := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun z => ?_
  have hc : 0 ≤ 4 * (q - 1) / q ^ 2 := by
    have : 0 < q := by linarith
    have : 0 < q - 1 := by linarith
    positivity
  calc ENNReal.ofReal (4 * (q - 1) / q ^ 2) *
        (w z * ENNReal.ofReal ((spow (q / 2) (u z.1) - spow (q / 2) (u z.2)) ^ 2))
      = w z * ENNReal.ofReal (4 * (q - 1) / q ^ 2 *
          (spow (q / 2) (u z.1) - spow (q / 2) (u z.2)) ^ 2) := by
        rw [ENNReal.ofReal_mul hc, mul_left_comm]
    _ ≤ _ := by
        refine mul_le_mul_right (ENNReal.ofReal_le_ofReal (sv_two_point hq _ _)) _

/-- **Stroock--Varopoulos inequality for a symmetric jump measure** (real-valued form): if
`ν` is invariant under `(x, y) ↦ (y, x)` and the relevant functions are integrable, then
`(2 (q - 1) / q²) ∬ (ψ u x - ψ u y)² dν ≤ ∬ (u x - u y) φ(u x) dν`. -/
theorem sv_integral {q : ℝ} (hq : 1 < q) {ν : Measure (X × X)}
    (hν : MeasurePreserving Prod.swap ν ν) (u : X → ℝ)
    (h1 : Integrable (fun z : X × X => (u z.1 - u z.2) * spow (q - 1) (u z.1)) ν)
    (h2 : Integrable (fun z : X × X => (u z.1 - u z.2) * spow (q - 1) (u z.2)) ν)
    (h3 : Integrable
      (fun z : X × X => (spow (q / 2) (u z.1) - spow (q / 2) (u z.2)) ^ 2) ν) :
    2 * (q - 1) / q ^ 2 * ∫ z, (spow (q / 2) (u z.1) - spow (q / 2) (u z.2)) ^ 2 ∂ν ≤
      ∫ z, (u z.1 - u z.2) * spow (q - 1) (u z.1) ∂ν := by
  have key := integral_sub_mul_eq_half hν u (spow (q - 1) ∘ u) h1 h2
  simp only [Function.comp] at key
  rw [key]
  have hint : Integrable (fun z : X × X =>
      (u z.1 - u z.2) * (spow (q - 1) (u z.1) - spow (q - 1) (u z.2))) ν := by
    refine (h1.sub h2).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply]
    ring
  have hle : 4 * (q - 1) / q ^ 2 * ∫ z, (spow (q / 2) (u z.1) - spow (q / 2) (u z.2)) ^ 2 ∂ν ≤
      ∫ z, (u z.1 - u z.2) * (spow (q - 1) (u z.1) - spow (q - 1) (u z.2)) ∂ν := by
    rw [← MeasureTheory.integral_const_mul]
    exact integral_mono (h3.const_mul _) hint fun z => sv_two_point hq _ _
  have : 2 * (q - 1) / q ^ 2 = 1 / 2 * (4 * (q - 1) / q ^ 2) := by ring
  rw [this, mul_assoc]
  exact mul_le_mul_of_nonneg_left hle (by norm_num)

/-! ### Generalized Stroock--Varopoulos -/

/-- **Generalized Stroock--Varopoulos, two-point form** (Stan--del Teso--Vázquez): if `ψ' = (Ψ')²`
with `Ψ'` continuous, then `(Ψ a - Ψ b)² ≤ (a - b)(ψ a - ψ b)`. -/
theorem gen_sv_two_point {ψ Ψ Ψ' : ℝ → ℝ} (hΨ' : Continuous Ψ')
    (hΨ : ∀ x, HasDerivAt Ψ (Ψ' x) x) (hψ : ∀ x, HasDerivAt ψ (Ψ' x ^ 2) x) (a b : ℝ) :
    (Ψ a - Ψ b) ^ 2 ≤ (a - b) * (ψ a - ψ b) := by
  have key : ∀ {x y : ℝ}, x ≤ y → (Ψ y - Ψ x) ^ 2 ≤ (y - x) * (ψ y - ψ x) := by
    intro x y hxy
    have h1 : ∫ s in x..y, Ψ' s = Ψ y - Ψ x :=
      integral_eq_sub_of_hasDerivAt (fun s _ => hΨ s) (hΨ'.intervalIntegrable x y)
    have h2 : ∫ s in x..y, Ψ' s ^ 2 = ψ y - ψ x :=
      integral_eq_sub_of_hasDerivAt (fun s _ => hψ s) ((hΨ'.pow 2).intervalIntegrable x y)
    have := sq_integral_le hxy hΨ'.continuousOn
    rwa [h1, h2] at this
  rcases le_total b a with h | h
  · exact key h
  · have := key h
    nlinarith [this]

/-- **Generalized Stroock--Varopoulos, lower-integral form.** -/
theorem gen_sv_lintegral {ψ Ψ Ψ' : ℝ → ℝ} (hΨ' : Continuous Ψ')
    (hΨ : ∀ x, HasDerivAt Ψ (Ψ' x) x) (hψ : ∀ x, HasDerivAt ψ (Ψ' x ^ 2) x)
    {X : Type*} [MeasurableSpace X] (ν : Measure (X × X)) (w : X × X → ℝ≥0∞) (u : X → ℝ) :
    ∫⁻ z, w z * ENNReal.ofReal ((Ψ (u z.1) - Ψ (u z.2)) ^ 2) ∂ν ≤
      ∫⁻ z, w z * ENNReal.ofReal ((u z.1 - u z.2) * (ψ (u z.1) - ψ (u z.2))) ∂ν :=
  lintegral_mono fun _ => mul_le_mul_right
    (ENNReal.ofReal_le_ofReal (gen_sv_two_point hΨ' hΨ hψ _ _)) _

/-- **Generalized Stroock--Varopoulos for a swap-invariant jump measure** (real form):
`∬ (Ψ u x - Ψ u y)² dν ≤ 2 ∬ (u x - u y) ψ(u x) dν`. -/
theorem gen_sv_integral {ψ Ψ Ψ' : ℝ → ℝ} (hΨ' : Continuous Ψ')
    (hΨ : ∀ x, HasDerivAt Ψ (Ψ' x) x) (hψ : ∀ x, HasDerivAt ψ (Ψ' x ^ 2) x)
    {X : Type*} [MeasurableSpace X] {ν : Measure (X × X)}
    (hν : MeasurePreserving Prod.swap ν ν) (u : X → ℝ)
    (h1 : Integrable (fun z : X × X => (u z.1 - u z.2) * ψ (u z.1)) ν)
    (h2 : Integrable (fun z : X × X => (u z.1 - u z.2) * ψ (u z.2)) ν)
    (h3 : Integrable (fun z : X × X => (Ψ (u z.1) - Ψ (u z.2)) ^ 2) ν) :
    ∫ z, (Ψ (u z.1) - Ψ (u z.2)) ^ 2 ∂ν ≤ 2 * ∫ z, (u z.1 - u z.2) * ψ (u z.1) ∂ν := by
  have key := integral_sub_mul_eq_half hν u (ψ ∘ u) h1 h2
  simp only [Function.comp] at key
  have hint : Integrable (fun z : X × X =>
      (u z.1 - u z.2) * (ψ (u z.1) - ψ (u z.2))) ν := by
    refine (h1.sub h2).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply]
    ring
  have hle : ∫ z, (Ψ (u z.1) - Ψ (u z.2)) ^ 2 ∂ν ≤
      ∫ z, (u z.1 - u z.2) * (ψ (u z.1) - ψ (u z.2)) ∂ν :=
    integral_mono h3 hint fun z => gen_sv_two_point hΨ' hΨ hψ _ _
  have : ∫ z, (u z.1 - u z.2) * (ψ (u z.1) - ψ (u z.2)) ∂ν =
      2 * ∫ z, (u z.1 - u z.2) * ψ (u z.1) ∂ν := by
    rw [key]
    ring
  linarith

end

end FracLap
