/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.FourierSemigroup
public import FracLap.WholeLine.GagliardoSymbolExact
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# FracLap.WholeLine.PointwiseEquivalence

Equivalence of the singular-integral and Fourier-multiplier definitions of `(-Δ)^(α/2)` on
Schwartz functions (Kwaśnicki).

For `0 < α < 2`, `φ ∈ 𝓢(ℝ; ℂ)` and `x ∈ ℝ`,
`(C(α)/2) ∫ (2 φ(x) - φ(x+y) - φ(x-y)) / |y|^(1+α) dy = ∫ |2π ξ|^α 𝓕φ(ξ) e^{2π i x ξ} dξ`.
The proof inserts the Fourier inversion formula, exchanges the integrals, and evaluates the kernel
integral by the exact symbol `∫ C |h|^(-1-α) (1 - cos (x h)) dh = |x|^α`.
-/

namespace FracLap

open Complex Filter FourierTransform MeasureTheory Real Set Topology
open scoped ENNReal NNReal SchwartzMap

@[expose] public section

/-- The integrand `C |h|^(-1-α) (1 - cos (x h))` of the exact-symbol identity. -/
noncomputable def cosKernel (α x h : ℝ) : ℝ :=
  fracLapConstant α * |h| ^ (-1 - α) * (1 - Real.cos (x * h))

theorem cosKernel_nonneg {α : ℝ} (hα : FractionalExponent α) (x h : ℝ) : 0 ≤ cosKernel α x h := by
  have hC := fracLapConstant_pos hα
  unfold cosKernel
  have := Real.cos_le_one (x * h)
  have : 0 ≤ |h| ^ (-1 - α) := Real.rpow_nonneg (abs_nonneg _) _
  positivity

theorem measurable_cosKernel (α x : ℝ) : Measurable (cosKernel α x) := by
  unfold cosKernel
  exact (measurable_const.mul (continuous_abs.measurable.pow_const _)).mul
    (measurable_const.sub (Real.continuous_cos.measurable.comp (measurable_const.mul
      measurable_id)))

/-- The kernel integral in Bochner form: `C |h|^(-1-α) (1 - cos (x h))` is integrable. -/
theorem integrable_cosKernel {α : ℝ} (hα : FractionalExponent α) (x : ℝ) :
    Integrable (cosKernel α x) := by
  refine ⟨(measurable_cosKernel α x).aestronglyMeasurable, ?_⟩
  have h := lintegral_kernel_one_sub_cos hα x
  have : ∀ h : ℝ, ‖cosKernel α x h‖ₑ = ENNReal.ofReal (cosKernel α x h) := fun h => by
    rw [← ofReal_norm, Real.norm_of_nonneg (cosKernel_nonneg hα x h)]
  change ∫⁻ h, ‖cosKernel α x h‖ₑ < ⊤
  simp_rw [this]
  change ∫⁻ h, ENNReal.ofReal (fracLapConstant α * |h| ^ (-1 - α) * (1 - Real.cos (x * h))) < ⊤
  rw [h]
  exact ENNReal.ofReal_lt_top

/-- The exact symbol in Bochner form: `∫ C |h|^(-1-α) (1 - cos (x h)) dh = |x|^α`. -/
theorem integral_cosKernel {α : ℝ} (hα : FractionalExponent α) (x : ℝ) :
    ∫ h : ℝ, cosKernel α x h = |x| ^ α := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (cosKernel_nonneg hα x))
    (measurable_cosKernel α x).aestronglyMeasurable]
  change (∫⁻ h, ENNReal.ofReal (fracLapConstant α * |h| ^ (-1 - α) *
    (1 - Real.cos (x * h)))).toReal = _
  rw [lintegral_kernel_one_sub_cos hα x, ENNReal.toReal_ofReal (by positivity)]

/-- Fourier inversion for a Schwartz function, in the form `φ z = ∫ 𝐞 (ξ z) 𝓕φ(ξ) dξ`. -/
theorem schwartz_fourier_inversion (φ : 𝓢(ℝ, ℂ)) (z : ℝ) :
    (φ : ℝ → ℂ) z = ∫ ξ : ℝ, (𝐞 (ξ * z) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ := by
  have h := congrFun (Continuous.fourierInv_fourier_eq (f := (φ : ℝ → ℂ)) φ.continuous
    φ.integrable (by
      have h1 : Integrable (⇑(𝓕 φ : 𝓢(ℝ, ℂ))) volume := (𝓕 φ : 𝓢(ℝ, ℂ)).integrable
      exact h1)) z
  rw [Real.fourierInv_eq] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [Circle.smul_def, smul_eq_mul, SchwartzMap.fourier_coe]
  congr 2
  simp [mul_comm]
  rfl

/-- `2 - 𝐞 t - 𝐞 (-t) = 2 (1 - cos (2π t))`. -/
theorem two_sub_fourierChar (t : ℝ) :
    (2 : ℂ) - (𝐞 t : ℂ) - (𝐞 (-t) : ℂ) = ((2 * (1 - Real.cos (2 * π * t)) : ℝ) : ℂ) := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply]
  push_cast
  have h : Complex.exp (2 * ↑π * ↑t * Complex.I) + Complex.exp (2 * ↑π * -↑t * Complex.I) =
      2 * Complex.cos (2 * ↑π * ↑t) := by
    rw [Complex.two_cos]; congr 1; ring_nf
  linear_combination -h

/-- A phase times a Schwartz function is integrable. -/
theorem integrable_phase_mul (ψ : 𝓢(ℝ, ℂ)) (z : ℝ) :
    Integrable (fun ξ : ℝ => (𝐞 (ξ * z) : ℂ) * ψ ξ) := by
  have h1 : Integrable (⇑ψ) volume := ψ.integrable
  refine h1.norm.mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact ((continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_id.mul continuous_const))).mul ψ.continuous).aestronglyMeasurable
  · simp

/-- A phase times an integrable function is integrable. -/
theorem integrable_phase_mul_of_integrable {g : ℝ → ℂ} (hg : Integrable g) (z : ℝ) :
    Integrable (fun ξ : ℝ => (𝐞 (ξ * z) : ℂ) * g ξ) := by
  refine hg.norm.mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact ((continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_id.mul continuous_const))).aestronglyMeasurable).mul hg.aestronglyMeasurable
  · simp

/-- **Second difference as a Fourier integral, general form**: if `u z = ∫ 𝐞 (ξ z) g ξ dξ` for
all `z` with `g` integrable, then
`2 u(x) - u(x+y) - u(x-y) = ∫ 𝐞 (ξ x) g(ξ) · 2 (1 - cos (2π ξ y)) dξ`. -/
theorem second_diff_fourier_of_inversion {g : ℝ → ℂ} (hg : Integrable g) {u : ℝ → ℂ}
    (hu : ∀ z, u z = ∫ ξ : ℝ, (𝐞 (ξ * z) : ℂ) * g ξ) (x y : ℝ) :
    2 * u x - u (x + y) - u (x - y) =
      ∫ ξ : ℝ, (𝐞 (ξ * x) : ℂ) * g ξ * ((2 * (1 - Real.cos (2 * π * (ξ * y))) : ℝ) : ℂ) := by
  have i1 := integrable_phase_mul_of_integrable hg x
  have i2 := integrable_phase_mul_of_integrable hg (x + y)
  have i3 := integrable_phase_mul_of_integrable hg (x - y)
  have i12 : Integrable (fun ξ : ℝ => 2 * ((𝐞 (ξ * x) : ℂ) * g ξ) -
      (𝐞 (ξ * (x + y)) : ℂ) * g ξ) := (i1.const_mul 2).sub i2
  have hpt : ∀ ξ : ℝ, (𝐞 (ξ * x) : ℂ) * g ξ * ((2 * (1 - Real.cos (2 * π * (ξ * y))) : ℝ) : ℂ) =
      2 * ((𝐞 (ξ * x) : ℂ) * g ξ) - (𝐞 (ξ * (x + y)) : ℂ) * g ξ -
        (𝐞 (ξ * (x - y)) : ℂ) * g ξ := fun ξ => by
    rw [← two_sub_fourierChar (ξ * y)]
    have a1 : (𝐞 (ξ * (x + y)) : ℂ) = (𝐞 (ξ * x) : ℂ) * (𝐞 (ξ * y) : ℂ) := by
      rw [mul_add, Real.fourierChar.map_add_eq_mul]; simp
    have a2 : (𝐞 (ξ * (x - y)) : ℂ) = (𝐞 (ξ * x) : ℂ) * (𝐞 (-(ξ * y)) : ℂ) := by
      rw [mul_sub, sub_eq_add_neg, Real.fourierChar.map_add_eq_mul]; simp
    rw [a1, a2]; ring
  simp_rw [hpt]
  rw [integral_sub i12 i3, integral_sub (i1.const_mul 2) i2, integral_const_mul, hu x,
    hu (x + y), hu (x - y)]

/-- **Second difference as a Fourier integral** (Schwartz case):
`2 φ(x) - φ(x+y) - φ(x-y) = ∫ 𝐞 (ξ x) 𝓕φ(ξ) · 2 (1 - cos (2π ξ y)) dξ`. -/
theorem second_diff_fourier (φ : 𝓢(ℝ, ℂ)) (x y : ℝ) :
    2 * (φ : ℝ → ℂ) x - φ (x + y) - φ (x - y) =
      ∫ ξ : ℝ, (𝐞 (ξ * x) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ *
        ((2 * (1 - Real.cos (2 * π * (ξ * y))) : ℝ) : ℂ) :=
  second_diff_fourier_of_inversion (𝓕 φ : 𝓢(ℝ, ℂ)).integrable
    (fun z => schwartz_fourier_inversion φ z) x y

/-- `|2π ξ|^α ‖ψ ξ‖` is integrable for a Schwartz function `ψ` and `0 < α < 2`. -/
theorem integrable_rpow_mul_schwartz {α : ℝ} (hα : FractionalExponent α) (ψ : 𝓢(ℝ, ℂ)) :
    Integrable (fun ξ : ℝ => |2 * π * ξ| ^ α * ‖ψ ξ‖) := by
  have h0 : Integrable (fun ξ : ℝ => ‖ξ‖ ^ 0 * ‖ψ ξ‖) := ψ.integrable_pow_mul volume 0
  have h2 : Integrable (fun ξ : ℝ => ‖ξ‖ ^ 2 * ‖ψ ξ‖) := ψ.integrable_pow_mul volume 2
  refine ((h0.add h2).const_mul ((2 * π) ^ 2)).mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact (((continuous_abs.comp (continuous_const.mul continuous_id)).measurable.pow_const
      α).mul ψ.continuous.measurable.norm).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    simp only [Real.norm_eq_abs, pow_zero, one_mul, Pi.add_apply]
    have hb : |2 * π * ξ| ^ α ≤ (2 * π) ^ 2 * (1 + |ξ| ^ 2) := by
      set a : ℝ := |2 * π * ξ| with ha
      have ha0 : 0 ≤ a := abs_nonneg _
      have hle : a ^ α ≤ 1 + a ^ 2 := by
        rcases le_total a 1 with h | h
        · have := Real.rpow_le_one ha0 h hα.1.le
          nlinarith [sq_nonneg a]
        · have : a ^ α ≤ a ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hα.2.le
          rw [Real.rpow_two] at this
          nlinarith [sq_nonneg a]
      refine hle.trans ?_
      have hs : a ^ 2 = (2 * π) ^ 2 * |ξ| ^ 2 := by
        rw [ha, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), mul_pow]
      have hpi : (1 : ℝ) ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three, Real.pi_pos]
      rw [hs]; nlinarith [sq_nonneg |ξ|]
    have := mul_le_mul_of_nonneg_right hb (norm_nonneg (ψ ξ))
    nlinarith

/-- **Singular integral = Fourier multiplier, general form.** Let `0 < α < 2`, let `g` be measurable
with `g` and `|2π ξ|^α ‖g ξ‖` integrable, and let `u z = ∫ 𝐞 (ξ z) g ξ dξ` for all `z`. Then
`(C(α)/2) ∫ (2 u(x) - u(x+y) - u(x-y)) / |y|^(1+α) dy = ∫ |2π ξ|^α 𝐞(ξ x) g(ξ) dξ`.
Only these integrability facts are used, not Schwartz decay; this covers the non-Schwartz iterates
`P_t f` of the fractional heat semigroup. -/
theorem fracLap_pointwise_eq_fourier_of_integrable {α : ℝ} (hα : FractionalExponent α)
    {g : ℝ → ℂ} (hgm : Measurable g) (hg : Integrable g)
    (hgα : Integrable (fun ξ : ℝ => |2 * π * ξ| ^ α * ‖g ξ‖)) {u : ℝ → ℂ}
    (hu : ∀ z, u z = ∫ ξ : ℝ, (𝐞 (ξ * z) : ℂ) * g ξ) (x : ℝ) :
    ((fracLapConstant α / 2 : ℝ) : ℂ) *
        ∫ y : ℝ, (2 * u x - u (x + y) - u (x - y)) / ((|y| ^ (1 + α) : ℝ) : ℂ) =
      ∫ ξ : ℝ, ((|2 * π * ξ| ^ α : ℝ) : ℂ) * ((𝐞 (ξ * x) : ℂ) * g ξ) := by
  have hC := fracLapConstant_pos hα
  -- the kernel `H y ξ`
  set H : ℝ → ℝ → ℂ := fun y ξ => (𝐞 (ξ * x) : ℂ) * g ξ * (cosKernel α (2 * π * ξ) y : ℂ) with hH
  have hkey : ∀ y : ℝ, ((fracLapConstant α / 2 : ℝ) : ℂ) *
      ((2 * u x - u (x + y) - u (x - y)) / ((|y| ^ (1 + α) : ℝ) : ℂ)) =
      ∫ ξ : ℝ, H y ξ := by
    intro y
    have hs := second_diff_fourier_of_inversion hg hu x y
    rw [hs, ← integral_div, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hH, cosKernel]
    have hy : (|y| ^ (1 + α) : ℝ) ≠ 0 ∨ y = 0 := by
      by_cases h : y = 0
      · exact Or.inr h
      · exact Or.inl (by positivity)
    rcases hy with hy | hy
    · have : |y| ^ (-1 - α) = ((|y| ^ (1 + α))⁻¹ : ℝ) := by
        rw [show (-1 - α) = -(1 + α) by ring, Real.rpow_neg (abs_nonneg _)]
      rw [this]
      push_cast
      rw [show (2 * (π : ℂ) * ξ * y) = 2 * π * (ξ * y) by ring]
      field_simp
    · subst hy; simp
  have hrw : ((fracLapConstant α / 2 : ℝ) : ℂ) *
      ∫ y : ℝ, (2 * u x - u (x + y) - u (x - y)) / ((|y| ^ (1 + α) : ℝ) : ℂ) =
      ∫ y : ℝ, ∫ ξ : ℝ, H y ξ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hkey)
  rw [hrw]
  have hmeas : Measurable (Function.uncurry H) := by
    have h1 : Measurable fun p : ℝ × ℝ => (𝐞 (p.2 * x) : ℂ) * g p.2 :=
      ((continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_snd.mul continuous_const))).measurable).mul (hgm.comp measurable_snd)
    have h2 : Measurable fun p : ℝ × ℝ => cosKernel α (2 * π * p.2) p.1 := by
      unfold cosKernel
      exact (measurable_const.mul (continuous_abs.measurable.pow_const _ |>.comp
        measurable_fst)).mul (measurable_const.sub (Real.continuous_cos.measurable.comp
          ((measurable_const.mul measurable_snd).mul measurable_fst)))
    exact h1.mul (Complex.measurable_ofReal.comp h2)
  have hnorm : ∀ ξ : ℝ, ∫ y : ℝ, ‖H y ξ‖ = |2 * π * ξ| ^ α * ‖g ξ‖ := fun ξ => by
    have : ∀ y : ℝ, ‖H y ξ‖ = ‖g ξ‖ * cosKernel α (2 * π * ξ) y := fun y => by
      simp only [hH, norm_mul, Complex.norm_real, Real.norm_of_nonneg (cosKernel_nonneg hα _ y)]
      simp
    simp_rw [this]
    rw [integral_const_mul, integral_cosKernel hα, mul_comm]
  have hint : Integrable (Function.uncurry H) (volume.prod volume) := by
    rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun ξ => ?_, ?_⟩
    · have h : Integrable (fun y : ℝ => H y ξ) :=
        ((integrable_cosKernel hα (2 * π * ξ)).ofReal (𝕜 := ℂ)).const_mul _
      exact h
    · exact hgα.congr (Eventually.of_forall fun ξ => (hnorm ξ).symm)
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [hH]
  rw [integral_const_mul, integral_complex_ofReal, integral_cosKernel hα]
  ring


/-- **Singular integral = Fourier multiplier** (Kwaśnicki's equivalence, Schwartz data): for
`0 < α < 2` and `φ ∈ 𝓢(ℝ; ℂ)`,
`(C(α)/2) ∫ (2 φ(x) - φ(x+y) - φ(x-y)) / |y|^(1+α) dy = ∫ |2π ξ|^α 𝐞(ξ x) 𝓕φ(ξ) dξ`. -/
theorem fracLap_pointwise_eq_fourier {α : ℝ} (hα : FractionalExponent α) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ((fracLapConstant α / 2 : ℝ) : ℂ) *
        ∫ y : ℝ, (2 * (φ : ℝ → ℂ) x - φ (x + y) - φ (x - y)) / ((|y| ^ (1 + α) : ℝ) : ℂ) =
      ∫ ξ : ℝ, ((|2 * π * ξ| ^ α : ℝ) : ℂ) * ((𝐞 (ξ * x) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) :=
  fracLap_pointwise_eq_fourier_of_integrable hα (𝓕 φ : 𝓢(ℝ, ℂ)).continuous.measurable
    (𝓕 φ : 𝓢(ℝ, ℂ)).integrable (integrable_rpow_mul_schwartz hα _)
    (fun z => schwartz_fourier_inversion φ z) x

/-- **The real second-difference operator agrees with the Fourier multiplier**: if `u : ℝ → ℝ`
is the real part datum of a Schwartz function `φ` (`φ x = u x`), then
`fracLapSecondDiff α u x = ∫ |2π ξ|^α 𝐞(ξ x) 𝓕φ(ξ) dξ`. -/
theorem fracLapSecondDiff_eq_fourier {α : ℝ} (hα : FractionalExponent α) {u : ℝ → ℝ}
    (φ : 𝓢(ℝ, ℂ)) (hφ : ∀ x, (φ : ℝ → ℂ) x = (u x : ℂ)) (x : ℝ) :
    (fracLapSecondDiff α u x : ℂ) =
      ∫ ξ : ℝ, ((|2 * π * ξ| ^ α : ℝ) : ℂ) * ((𝐞 (ξ * x) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) := by
  rw [← fracLap_pointwise_eq_fourier hα φ x]
  unfold fracLapSecondDiff
  have h : ∀ y : ℝ, (2 * (φ : ℝ → ℂ) x - φ (x + y) - φ (x - y)) / ((|y| ^ (1 + α) : ℝ) : ℂ) =
      ((-(secondDiff u x y / |y| ^ (1 + α)) : ℝ) : ℂ) := fun y => by
    simp only [hφ, secondDiff]
    push_cast
    ring
  simp_rw [h]
  rw [integral_complex_ofReal, integral_neg]
  push_cast
  ring

/-- **Multiplier Theorem (`thm:multiplier`, complex inverse-Fourier form)**:
For `0 < α < 2` and `φ ∈ 𝓢(ℝ; ℂ)`,
`(C(α)/2) ∫ (2 φ(x) - φ(x+y) - φ(x-y)) / |y|^(1+α) dy = 𝓕⁻ (ξ ↦ |2π ξ|^α 𝓕φ(ξ)) x`. -/
theorem fracLap_pointwise_eq_fourierInv {α : ℝ} (hα : FractionalExponent α) (φ : 𝓢(ℝ, ℂ))
    (x : ℝ) :
    ((fracLapConstant α / 2 : ℝ) : ℂ) *
        ∫ y : ℝ, (2 * (φ : ℝ → ℂ) x - φ (x + y) - φ (x - y)) / ((|y| ^ (1 + α) : ℝ) : ℂ) =
      𝓕⁻ (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) x := by
  rw [fracLap_pointwise_eq_fourier hα φ x, Real.fourierInv_eq]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  dsimp only [fracLapSymbol]
  rw [Circle.smul_def, smul_eq_mul, mul_left_comm ((|2 * π * ξ| ^ α : ℝ) : ℂ)]
  congr 1
  congr 2
  exact mul_comm (ξ : ℝ) x

/-- **Multiplier Theorem (`thm:multiplier`, real second-difference form)**:
If `u : ℝ → ℝ` agrees pointwise with `φ ∈ 𝓢(ℝ; ℂ)`, then
`fracLapSecondDiff α u x = 𝓕⁻ (ξ ↦ |2π ξ|^α 𝓕φ(ξ)) x` for every `x ∈ ℝ`. -/
theorem fracLapSecondDiff_eq_fourierInv {α : ℝ} (hα : FractionalExponent α) {u : ℝ → ℝ}
    (φ : 𝓢(ℝ, ℂ)) (hφ : ∀ x, (φ : ℝ → ℂ) x = (u x : ℂ)) (x : ℝ) :
    (fracLapSecondDiff α u x : ℂ) =
      𝓕⁻ (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) x := by
  rw [fracLapSecondDiff_eq_fourier hα φ hφ x, ← fracLap_pointwise_eq_fourier hα φ x,
    fracLap_pointwise_eq_fourierInv hα φ x]

/-- For `0 < α < 2` and a Schwartz function `φ : 𝓢(ℝ, ℂ)`, `ξ ↦ |2π ξ|^α 𝓕φ(ξ)` lies in
`L¹(ℝ; ℂ)`. -/
theorem integrable_fracLapSymbol_mul_fourier {α : ℝ} (hα : FractionalExponent α) (φ : 𝓢(ℝ, ℂ)) :
    Integrable (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) volume := by
  have hmeas :
      AEStronglyMeasurable (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ)
        volume := by
    have hpow : Measurable fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.measurable.comp (measurable_fracLapSymbol α)
    exact hpow.aestronglyMeasurable.mul (𝓕 φ : 𝓢(ℝ, ℂ)).continuous.aestronglyMeasurable
  refine (integrable_rpow_mul_schwartz hα (𝓕 φ)).mono' hmeas (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fracLapSymbol_nonneg α ξ)]
  exact le_rfl

/-- For `0 < α < 2` and `φ ∈ 𝓢(ℝ, ℂ)`, `ξ ↦ |2π ξ|^α 𝓕φ(ξ)` lies in `L²(ℝ; ℂ)`. -/
theorem memLp_two_fracLapSymbol_mul_fourier {α : ℝ} (hα : FractionalExponent α) (φ : 𝓢(ℝ, ℂ)) :
    MemLp (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) 2 volume := by
  let ψ : 𝓢(ℝ, ℂ) := 𝓕 φ
  have hmeas :
      AEStronglyMeasurable (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) * ψ ξ) volume :=
    (Complex.continuous_ofReal.measurable.comp
      (measurable_fracLapSymbol α)).aestronglyMeasurable.mul ψ.continuous.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ ξ : ℝ, ‖ψ ξ‖ ≤ C :=
    ⟨_, fun ξ => ψ.toBoundedContinuousFunction.norm_coe_le_norm ξ⟩
  have hC0 : 0 ≤ C := (norm_nonneg (ψ 0)).trans (hC 0)
  have h0 : Integrable (fun ξ : ℝ => ‖ξ‖ ^ 0 * ‖ψ ξ‖) volume := ψ.integrable_pow_mul volume 0
  have h4 : Integrable (fun ξ : ℝ => ‖ξ‖ ^ 4 * ‖ψ ξ‖) volume := ψ.integrable_pow_mul volume 4
  have hdom : Integrable
      (fun ξ : ℝ => 2 * ((2 * π) ^ 4 * C) * (‖ξ‖ ^ 0 * ‖ψ ξ‖ + ‖ξ‖ ^ 4 * ‖ψ ξ‖)) volume :=
    (h0.add h4).const_mul (2 * ((2 * π) ^ 4 * C))
  refine hdom.mono' (hmeas.norm.pow 2) (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fracLapSymbol_nonneg α ξ)]
  have hb : fracLapSymbol α ξ ≤ (2 * π) ^ 2 * (1 + |ξ| ^ 2) := by
    unfold fracLapSymbol
    set a : ℝ := |2 * π * ξ| with ha
    have ha0 : 0 ≤ a := abs_nonneg _
    have hle : a ^ α ≤ 1 + a ^ 2 := by
      rcases le_total a 1 with h | h
      · have := Real.rpow_le_one ha0 h hα.1.le
        nlinarith [sq_nonneg a]
      · have : a ^ α ≤ a ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hα.2.le
        rw [Real.rpow_two] at this
        nlinarith [sq_nonneg a]
    refine hle.trans ?_
    have hs : a ^ 2 = (2 * π) ^ 2 * |ξ| ^ 2 := by
      rw [ha, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), mul_pow]
    have hpi : (1 : ℝ) ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three, Real.pi_pos]
    rw [hs]
    nlinarith [sq_nonneg |ξ|]
  have h1 : fracLapSymbol α ξ * ‖ψ ξ‖ ≤ (2 * π) ^ 2 * (1 + |ξ| ^ 2) * ‖ψ ξ‖ :=
    mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have hsq1 : (fracLapSymbol α ξ * ‖ψ ξ‖) ^ 2 ≤ ((2 * π) ^ 2 * (1 + |ξ| ^ 2) * ‖ψ ξ‖) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (fracLapSymbol_nonneg α ξ) (norm_nonneg _)) h1 2
  have hsq2 : (1 + |ξ| ^ 2) ^ 2 ≤ 2 * (1 + |ξ| ^ 4) := by
    have : (1 - |ξ| ^ 2) ^ 2 ≥ 0 := sq_nonneg _
    linarith [show (1 + |ξ| ^ 2) ^ 2 = 2 * (1 + |ξ| ^ 4) - (1 - |ξ| ^ 2) ^ 2 by ring]
  have hsq3 : (1 + |ξ| ^ 4) * ‖ψ ξ‖ ^ 2 ≤ C * (‖ξ‖ ^ 0 * ‖ψ ξ‖ + ‖ξ‖ ^ 4 * ‖ψ ξ‖) := by
    have hleC : ‖ψ ξ‖ ^ 2 ≤ C * ‖ψ ξ‖ := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _)
    calc
      (1 + |ξ| ^ 4) * ‖ψ ξ‖ ^ 2 ≤ (1 + |ξ| ^ 4) * (C * ‖ψ ξ‖) :=
        mul_le_mul_of_nonneg_left hleC (by positivity)
      _ = C * (‖ξ‖ ^ 0 * ‖ψ ξ‖ + ‖ξ‖ ^ 4 * ‖ψ ξ‖) := by
        simp only [pow_zero, one_mul, Real.norm_eq_abs, pow_abs]
        ring
  calc
    (fracLapSymbol α ξ * ‖ψ ξ‖) ^ 2
        ≤ ((2 * π) ^ 2 * (1 + |ξ| ^ 2) * ‖ψ ξ‖) ^ 2 := hsq1
    _ = (2 * π) ^ 4 * ((1 + |ξ| ^ 2) ^ 2 * ‖ψ ξ‖ ^ 2) := by ring
    _ ≤ (2 * π) ^ 4 * (2 * (1 + |ξ| ^ 4) * ‖ψ ξ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq2 (sq_nonneg _)) (by positivity)
    _ = (2 * π) ^ 4 * (2 * ((1 + |ξ| ^ 4) * ‖ψ ξ‖ ^ 2)) := by ring
    _ ≤ (2 * π) ^ 4 * (2 * (C * (‖ξ‖ ^ 0 * ‖ψ ξ‖ + ‖ξ‖ ^ 4 * ‖ψ ξ‖))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq3 (by norm_num)) (by positivity)
    _ = 2 * ((2 * π) ^ 4 * C) * (‖ξ‖ ^ 0 * ‖ψ ξ‖ + ‖ξ‖ ^ 4 * ‖ψ ξ‖) := by ring

/-- Every Schwartz function `φ ∈ 𝓢(ℝ, ℂ)` lies in the infinitesimal generator domain of
`fracLapSemigroup α` for `0 < α < 2`. -/
theorem fracLapSemigroup_schwartz_mem_generatorDomain {α : ℝ} (hα : FractionalExponent α)
    (φ : 𝓢(ℝ, ℂ)) :
    (φ.toLp 2 volume : L2C) ∈ (fracLapSemigroup α).generatorDomain := by
  rw [fracLapSemigroup_mem_generatorDomain_iff]
  have hF : (𝓕 (φ.toLp 2 volume : L2C) : L2C) = (𝓕 φ).toLp 2 volume :=
    SchwartzMap.toLp_fourier_eq φ
  refine (memLp_two_fracLapSymbol_mul_fourier hα φ).ae_eq ?_
  filter_upwards [(𝓕 φ).coeFn_toLp 2 volume] with ξ hξ
  rw [hF, hξ]

/-- Helper: `L²` equality between `ξ ↦ |2π ξ|^α * 𝓕 (φ.toLp 2) ξ` and
`ξ ↦ |2π ξ|^α * (𝓕 φ) ξ`. -/
theorem toLp_fracLapSymbol_mul_fourier_eq {α : ℝ} (hα : FractionalExponent α) (φ : 𝓢(ℝ, ℂ))
    (hM : MemLp (fun ξ : ℝ =>
      ((fracLapSymbol α ξ : ℝ) : ℂ) * ((𝓕 (φ.toLp 2 volume : L2C) : L2C) : ℝ → ℂ) ξ)
      2 volume) :
    hM.toLp (fun ξ : ℝ =>
        ((fracLapSymbol α ξ : ℝ) : ℂ) * ((𝓕 (φ.toLp 2 volume : L2C) : L2C) : ℝ → ℂ) ξ) =
      (memLp_two_fracLapSymbol_mul_fourier hα φ).toLp
        (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) := by
  have hF : (𝓕 (φ.toLp 2 volume : L2C) : L2C) = (𝓕 φ).toLp 2 volume :=
    SchwartzMap.toLp_fourier_eq φ
  rw [Lp.ext_iff]
  filter_upwards [hM.coeFn_toLp, (memLp_two_fracLapSymbol_mul_fourier hα φ).coeFn_toLp,
    (𝓕 φ).coeFn_toLp 2 volume] with ξ h1 h2 h3
  have h1' : (hM.toLp (fun ζ : ℝ => ((fracLapSymbol α ζ : ℝ) : ℂ) *
      ((𝓕 (φ.toLp 2 volume : L2C) : L2C) : ℝ → ℂ) ζ) : ℝ → ℂ) ξ =
      ((fracLapSymbol α ξ : ℝ) : ℂ) * ((𝓕 (φ.toLp 2 volume : L2C) : L2C) : ℝ → ℂ) ξ := h1
  have h2' : ((memLp_two_fracLapSymbol_mul_fourier hα φ).toLp
      (fun ζ : ℝ => ((fracLapSymbol α ζ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ζ) : ℝ → ℂ) ξ =
      ((fracLapSymbol α ξ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ := h2
  have h3' : (((𝓕 φ).toLp 2 volume : L2C) : ℝ → ℂ) ξ = (𝓕 φ : 𝓢(ℝ, ℂ)) ξ := h3
  rw [h1', h2', hF, h3']

/-- **Action of the `fracLapSemigroup` Generator on Schwartz Functions**:
for `0 < α < 2` and `φ ∈ 𝓢(ℝ, ℂ)`,
`L(φ) = -𝓕⁻ (|2π ξ|^α 𝓕φ)` in `L²(ℝ; ℂ)`. -/
theorem generator_fracLapSemigroup_schwartz {α : ℝ} (hα : FractionalExponent α) (φ : 𝓢(ℝ, ℂ)) :
    (fracLapSemigroup α).generator
        ⟨(φ.toLp 2 volume : L2C), fracLapSemigroup_schwartz_mem_generatorDomain hα φ⟩ =
      -(𝓕⁻ ((memLp_two_fracLapSymbol_mul_fourier hα φ).toLp
        (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ))) := by
  have hM :
      MemLp (fun ξ : ℝ =>
        ((fracLapSymbol α ξ : ℝ) : ℂ) * ((𝓕 (φ.toLp 2 volume : L2C) : L2C) : ℝ → ℂ) ξ)
        2 volume :=
    (fracLapSemigroup_mem_generatorDomain_iff α (φ.toLp 2 volume)).mp
      (fracLapSemigroup_schwartz_mem_generatorDomain hα φ)
  rw [generator_fracLapSemigroup_of_memLp α (fracLapSemigroup_schwartz_mem_generatorDomain hα φ) hM,
    toLp_fracLapSymbol_mul_fourier_eq hα φ hM]

/-- **Pointwise Singular Integral = Negative Semigroup Generator (`thm:multiplier` in `L²`)**:
if real `u : ℝ → ℝ` agrees pointwise with `φ ∈ 𝓢(ℝ, ℂ)`, then `fracLapSecondDiff α u` agrees a.e.
with `-(fracLapSemigroup α).generator φ` in `L²(ℝ; ℂ)` (and hence lies in `L²`). -/
theorem fracLapSecondDiff_ae_eq_neg_generator {α : ℝ} (hα : FractionalExponent α) {u : ℝ → ℝ}
    (φ : 𝓢(ℝ, ℂ)) (hφ : ∀ x, (φ : ℝ → ℂ) x = (u x : ℂ)) :
    (fun x : ℝ => (fracLapSecondDiff α u x : ℂ)) =ᵐ[volume]
      ((-((fracLapSemigroup α).generator
        ⟨(φ.toLp 2 volume : L2C), fracLapSemigroup_schwartz_mem_generatorDomain hα φ⟩) : L2C) :
          ℝ → ℂ) := by
  rw [generator_fracLapSemigroup_schwartz hα φ, neg_neg]
  have h1 := integrable_fracLapSymbol_mul_fourier hα φ
  have h2 := memLp_two_fracLapSymbol_mul_fourier hα φ
  filter_upwards [(coeFn_fourierInv_toLp_ae_eq_of_integrable h1 h2).symm] with x hx
  rw [fracLapSecondDiff_eq_fourierInv hα φ hφ x]
  exact hx

/-! ### Explicit normalizing constant integral and endpoint strong `L²` limits -/

/-- **Explicit integral formula for `C(α)⁻¹`** (`prop:constantexplicit`):
for `0 < α < 2`, `∫ (1 - cos ω) / |ω|^(1 + α) dω = C(α)⁻¹`. -/
theorem integral_one_sub_cos_div_abs_rpow {α : ℝ} (hα : FractionalExponent α) :
    ∫ ω : ℝ, (1 - Real.cos ω) / |ω| ^ (1 + α) = (fracLapConstant α)⁻¹ := by
  have hpt : ∀ ω : ℝ, cosKernel α 1 ω = fracLapConstant α * ((1 - Real.cos ω) / |ω| ^ (1 + α)) := by
    intro ω
    unfold cosKernel
    rw [one_mul, show (-1 - α : ℝ) = -(1 + α) by ring, Real.rpow_neg (abs_nonneg ω),
      div_eq_mul_inv]
    ring
  have h1 := integral_cosKernel hα 1
  simp only [abs_one, Real.one_rpow] at h1
  simp_rw [hpt, integral_const_mul] at h1
  rw [mul_comm] at h1
  exact eq_inv_of_mul_eq_one_left h1

/-- **Explicit normalizing constant identity** (`prop:constantexplicit`):
`C(α) = (∫ (1 - cos ω) / |ω|^(1 + α) dω)⁻¹`. -/
theorem fracLapConstant_eq_inv_integral_cos {α : ℝ} (hα : FractionalExponent α) :
    fracLapConstant α = (∫ ω : ℝ, (1 - Real.cos ω) / |ω| ^ (1 + α))⁻¹ := by
  rw [integral_one_sub_cos_div_abs_rpow hα, inv_inv]

/-- Fourier transform of the Schwartz derivative `(SchwartzMap.derivCLM ℝ ℂ ψ)`:
`𝓕 (ψ') ξ = (2π i ξ) 𝓕 ψ ξ`. -/
private theorem fourier_schwartz_deriv (ψ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    ((𝓕 (SchwartzMap.derivCLM ℝ ℂ ψ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ =
      (2 * ↑Real.pi * Complex.I * (ξ : ℂ)) * ((𝓕 ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ := by
  have hderiv : deriv (ψ : ℝ → ℂ) = ((SchwartzMap.derivCLM ℝ ℂ ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    ext x
    exact (SchwartzMap.derivCLM_apply ℝ ψ x).symm
  have hf := Real.fourier_deriv (E := ℂ) ψ.integrable ψ.differentiable
    (hderiv ▸ (SchwartzMap.derivCLM ℝ ℂ ψ).integrable)
  have hfξ := congr_fun hf ξ
  rw [hderiv] at hfξ
  simpa [SchwartzMap.fourier_coe, smul_eq_mul] using hfξ

/-- Twice-differentiated Schwartz function `-φ''` has Fourier transform
`|2π ξ|² 𝓕 φ(ξ)`. -/
theorem fourier_neg_secondDeriv_schwartz (φ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    ((𝓕 (-(SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ φ))) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ =
      ((fracLapSymbol 2 ξ : ℝ) : ℂ) * ((𝓕 φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ := by
  have hcoe_neg : ((-(SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ φ)) : 𝓢(ℝ, ℂ)) :
      ℝ → ℂ) = -((SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ φ) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    ext x
    simp
  have hneg : ((𝓕 (-(SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ φ))) : 𝓢(ℝ, ℂ)) :
      ℝ → ℂ) ξ =
      -((𝓕 (SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ φ)) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ := by
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, hcoe_neg, Real.fourier_eq,
      Real.fourier_eq]
    simp only [Pi.neg_apply, smul_neg, integral_neg]
  rw [hneg, fourier_schwartz_deriv (SchwartzMap.derivCLM ℝ ℂ φ) ξ, fourier_schwartz_deriv φ ξ]
  have h2 : fracLapSymbol 2 ξ = (2 * Real.pi * ξ) ^ 2 := by
    unfold fracLapSymbol
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [h2]
  push_cast
  calc
    -(2 * ↑Real.pi * Complex.I * (ξ : ℂ) *
        (2 * ↑Real.pi * Complex.I * (ξ : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ))
        = (-(2 * ↑Real.pi * Complex.I * (ξ : ℂ)) ^ 2) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ := by ring
    _ = ((2 * ↑Real.pi * (ξ : ℂ)) ^ 2 * (-(Complex.I ^ 2))) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ := by ring
    _ = (2 * ↑Real.pi * (ξ : ℂ)) ^ 2 * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ := by rw [Complex.I_sq]; ring

/-- Uniform pointwise polynomial bound for `fracLapSymbol α ξ` on `0 ≤ α ≤ 2`:
`|2π ξ|^α ≤ 1 + (2π ξ)²`. -/
private theorem fracLapSymbol_le_one_add_sq {α : ℝ} (hα0 : 0 ≤ α) (hα2 : α ≤ 2) (ξ : ℝ) :
    fracLapSymbol α ξ ≤ 1 + (2 * Real.pi * ξ) ^ 2 := by
  unfold fracLapSymbol
  rcases le_total |2 * Real.pi * ξ| 1 with hle | hge
  · calc
      |2 * Real.pi * ξ| ^ α ≤ 1 := Real.rpow_le_one (abs_nonneg _) hle hα0
      _ ≤ 1 + (2 * Real.pi * ξ) ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
  · calc
      |2 * Real.pi * ξ| ^ α ≤ |2 * Real.pi * ξ| ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hge hα2
      _ = (2 * Real.pi * ξ) ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
      _ ≤ 1 + (2 * Real.pi * ξ) ^ 2 := le_add_of_nonneg_left zero_le_one

/-- `L²` norm squared as a Bochner integral on `L2C`. -/
private theorem l2c_norm_sq_eq_integral (g : L2C) :
    ‖g‖ ^ 2 = ∫ x : ℝ, ‖(g : ℝ → ℂ) x‖ ^ 2 := by
  have h1 : ‖g‖ ^ 2 = (@inner ℂ L2C _ g g).re := by
    have hs : @inner ℂ L2C _ g g = ((‖g‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [hs, Complex.ofReal_re]
  have h2 : (@inner ℂ L2C _ g g).re =
      ∫ x : ℝ, (@inner ℂ ℂ _ ((g : ℝ → ℂ) x) ((g : ℝ → ℂ) x)).re := by
    rw [MeasureTheory.L2.inner_def g g]
    exact (Complex.reCLM.integral_comp_comm (MeasureTheory.L2.integrable_inner g g)).symm
  rw [h1, h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hx : (@inner ℂ ℂ _ ((g : ℝ → ℂ) x) ((g : ℝ → ℂ) x)).re = ‖(g : ℝ → ℂ) x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    change (((‖(g : ℝ → ℂ) x‖ : ℝ) : ℂ) ^ 2).re = ‖(g : ℝ → ℂ) x‖ ^ 2
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  exact hx

section ClassicalLimit

open Classical in
/-- Dominated convergence helper in `L2C` for multiplier convergence of `|2π ξ|^α 𝓕 φ`. -/
private theorem tendsto_norm_toLp_fracLapSymbol_mul_fourier (φ : 𝓢(ℝ, ℂ)) {F : Filter ℝ}
    [F.IsCountablyGenerated] (hF_mem : Set.Ioo (0 : ℝ) 2 ∈ F)
    {limSym : ℝ → ℝ} (hlim_meas : Measurable limSym)
    (hlim_bd : ∀ ξ : ℝ, |limSym ξ| ≤ 1 + (2 * Real.pi * ξ) ^ 2)
    (hlim_mem : MemLp (fun ξ : ℝ => (limSym ξ : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) 2 volume)
    (hlim_ae : ∀ᵐ ξ : ℝ ∂volume, Filter.Tendsto (fun α : ℝ => fracLapSymbol α ξ) F
      (nhds (limSym ξ))) :
    Filter.Tendsto (fun α : ℝ =>
      if hα : FractionalExponent α then
        ‖(memLp_two_fracLapSymbol_mul_fourier hα φ).toLp
            (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) -
          hlim_mem.toLp (fun ξ : ℝ => (limSym ξ : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ)‖
      else 0) F (nhds 0) := by
  let ψ : 𝓢(ℝ, ℂ) := 𝓕 φ
  let C0 : ℝ := SchwartzMap.seminorm ℝ 0 0 ψ
  have hC0_bd : ∀ ξ : ℝ, ‖(ψ : ℝ → ℂ) ξ‖ ≤ C0 := fun ξ => by
    simpa [C0] using ψ.le_seminorm ℝ 0 0 ξ
  let bound : ℝ → ℝ := fun ξ =>
    (4 * C0) * (‖ξ‖ ^ 0 * ‖(ψ : ℝ → ℂ) ξ‖) +
    (8 * (2 * Real.pi) ^ 2 * C0) * (‖ξ‖ ^ 2 * ‖(ψ : ℝ → ℂ) ξ‖) +
    (4 * (2 * Real.pi) ^ 4 * C0) * (‖ξ‖ ^ 4 * ‖(ψ : ℝ → ℂ) ξ‖)
  have hbound_int : Integrable bound volume :=
    (((ψ.integrable_pow_mul volume 0).const_mul _).add
      ((ψ.integrable_pow_mul volume 2).const_mul _)).add
      ((ψ.integrable_pow_mul volume 4).const_mul _)
  let fn : ℝ → ℝ → ℝ := fun α ξ =>
    if _hα : FractionalExponent α then
      ‖((fracLapSymbol α ξ : ℝ) : ℂ) * (ψ : ℝ → ℂ) ξ - (limSym ξ : ℂ) * (ψ : ℝ → ℂ) ξ‖ ^ 2
    else 0
  have hfn_meas : ∀ᶠ α in F, AEStronglyMeasurable (fn α) volume := by
    filter_upwards [hF_mem] with α (hα : FractionalExponent α)
    have hm1 : Measurable fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.measurable.comp
        (((continuous_const.mul continuous_id).abs.rpow_const
          (fun _ => Or.inr (by linarith [hα.1] : 0 ≤ α))).measurable)
    have hm2 : Measurable fun ξ : ℝ => (limSym ξ : ℂ) :=
      Complex.continuous_ofReal.measurable.comp hlim_meas
    have hfn_eq : fn α = fun ξ : ℝ =>
        ‖((fracLapSymbol α ξ : ℝ) : ℂ) * (ψ : ℝ → ℂ) ξ -
          (limSym ξ : ℂ) * (ψ : ℝ → ℂ) ξ‖ ^ 2 := by
      funext ξ; simp [fn, hα]
    rw [hfn_eq]
    exact ((((hm1.mul ψ.continuous.measurable).sub
      (hm2.mul ψ.continuous.measurable)).norm).pow_const 2).aestronglyMeasurable
  have hfn_bd : ∀ᶠ α in F, ∀ᵐ ξ ∂volume, ‖fn α ξ‖ ≤ bound ξ := by
    filter_upwards [hF_mem] with α (hα : FractionalExponent α)
    refine Filter.Eventually.of_forall fun ξ => ?_
    have hfn_α : fn α ξ =
        ‖((fracLapSymbol α ξ : ℝ) : ℂ) * (ψ : ℝ → ℂ) ξ - (limSym ξ : ℂ) * (ψ : ℝ → ℂ) ξ‖ ^ 2 := by
      simp [fn, hα]
    rw [hfn_α, Real.norm_of_nonneg (sq_nonneg _)]
    have hdiff_eq :
        ((fracLapSymbol α ξ : ℝ) : ℂ) * (ψ : ℝ → ℂ) ξ - (limSym ξ : ℂ) * (ψ : ℝ → ℂ) ξ =
          ((fracLapSymbol α ξ - limSym ξ : ℝ) : ℂ) * (ψ : ℝ → ℂ) ξ := by
      push_cast; ring
    rw [hdiff_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    have hsym_nonneg : 0 ≤ fracLapSymbol α ξ := by unfold fracLapSymbol; positivity
    have hsym_bd : fracLapSymbol α ξ ≤ 1 + (2 * Real.pi * ξ) ^ 2 :=
      fracLapSymbol_le_one_add_sq hα.1.le hα.2.le ξ
    have habs_diff : |fracLapSymbol α ξ - limSym ξ| ≤ 2 * (1 + (2 * Real.pi * ξ) ^ 2) := by
      calc |fracLapSymbol α ξ - limSym ξ|
          ≤ |fracLapSymbol α ξ| + |limSym ξ| := abs_sub _ _
        _ = fracLapSymbol α ξ + |limSym ξ| := by rw [abs_of_nonneg hsym_nonneg]
        _ ≤ (1 + (2 * Real.pi * ξ) ^ 2) + (1 + (2 * Real.pi * ξ) ^ 2) :=
            add_le_add hsym_bd (hlim_bd ξ)
        _ = 2 * (1 + (2 * Real.pi * ξ) ^ 2) := by ring
    have hsq_diff : |fracLapSymbol α ξ - limSym ξ| ^ 2 ≤
        4 * (1 + (2 * Real.pi * ξ) ^ 2) ^ 2 := by
      calc |fracLapSymbol α ξ - limSym ξ| ^ 2
          ≤ (2 * (1 + (2 * Real.pi * ξ) ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) habs_diff 2
        _ = 4 * (1 + (2 * Real.pi * ξ) ^ 2) ^ 2 := by ring
    have hψ_sq : ‖(ψ : ℝ → ℂ) ξ‖ ^ 2 ≤ C0 * ‖(ψ : ℝ → ℂ) ξ‖ := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right (hC0_bd ξ) (norm_nonneg _)
    have hexpand : 4 * (1 + (2 * Real.pi * ξ) ^ 2) ^ 2 * (C0 * ‖(ψ : ℝ → ℂ) ξ‖) = bound ξ := by
      simp only [bound, Real.norm_eq_abs, pow_zero, one_mul, sq_abs]
      have h4 : |ξ| ^ 4 = ξ ^ 4 := by
        calc |ξ| ^ 4 = (|ξ| ^ 2) ^ 2 := by ring
          _ = (ξ ^ 2) ^ 2 := by rw [sq_abs]
          _ = ξ ^ 4 := by ring
      rw [h4]
      ring
    calc |fracLapSymbol α ξ - limSym ξ| ^ 2 * ‖(ψ : ℝ → ℂ) ξ‖ ^ 2
        ≤ (4 * (1 + (2 * Real.pi * ξ) ^ 2) ^ 2) * (C0 * ‖(ψ : ℝ → ℂ) ξ‖) :=
          mul_le_mul hsq_diff hψ_sq (sq_nonneg _) (by positivity)
      _ = bound ξ := hexpand
  have hfn_lim : ∀ᵐ ξ ∂volume, Filter.Tendsto (fun α : ℝ => fn α ξ) F (nhds 0) := by
    filter_upwards [hlim_ae] with ξ hξ
    have hsub : Filter.Tendsto
        (fun α : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) * (ψ : ℝ → ℂ) ξ -
          (limSym ξ : ℂ) * (ψ : ℝ → ℂ) ξ) F (nhds 0) := by
      have h0 : ((limSym ξ : ℝ) : ℂ) * (ψ : ℝ → ℂ) ξ - (limSym ξ : ℂ) * (ψ : ℝ → ℂ) ξ = 0 :=
        sub_self _
      exact h0 ▸ (((Complex.continuous_ofReal.continuousAt.tendsto.comp hξ).mul
        tendsto_const_nhds).sub tendsto_const_nhds)
    have hsq : Filter.Tendsto (fun α : ℝ =>
        ‖((fracLapSymbol α ξ : ℝ) : ℂ) * (ψ : ℝ → ℂ) ξ -
          (limSym ξ : ℂ) * (ψ : ℝ → ℂ) ξ‖ ^ 2) F (nhds 0) := by
      simpa using (hsub.norm.pow 2)
    refine Filter.Tendsto.congr' ?_ hsq
    filter_upwards [hF_mem] with α (hα : FractionalExponent α)
    simp [fn, hα]
  have hint_lim : Filter.Tendsto (fun α : ℝ => ∫ ξ : ℝ, fn α ξ) F (nhds 0) := by
    have h0 := MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
      hfn_meas hfn_bd hbound_int hfn_lim
    simpa using h0
  have hnorm_sq : Filter.Tendsto (fun α : ℝ =>
      (if hα : FractionalExponent α then
        ‖(memLp_two_fracLapSymbol_mul_fourier hα φ).toLp
            (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) -
          hlim_mem.toLp (fun ξ : ℝ => (limSym ξ : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ)‖
      else 0) ^ 2) F (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hint_lim
    filter_upwards [hF_mem] with α (hα : FractionalExponent α)
    have hd : (if h : FractionalExponent α then
        ‖(memLp_two_fracLapSymbol_mul_fourier h φ).toLp
            (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) -
          hlim_mem.toLp (fun ξ : ℝ => (limSym ξ : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ)‖
        else 0) ^ 2 =
        ‖(memLp_two_fracLapSymbol_mul_fourier hα φ).toLp
            (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) -
          hlim_mem.toLp (fun ξ : ℝ => (limSym ξ : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ)‖ ^ 2 := by
      simp [hα]
    rw [hd, l2c_norm_sq_eq_integral]
    refine integral_congr_ae ?_
    have hae1 := (memLp_two_fracLapSymbol_mul_fourier hα φ).coeFn_toLp
    have hae2 := hlim_mem.coeFn_toLp
    have hae_sub := Lp.coeFn_sub
      ((memLp_two_fracLapSymbol_mul_fourier hα φ).toLp
        (fun ξ : ℝ => ((fracLapSymbol α ξ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ))
      (hlim_mem.toLp (fun ξ : ℝ => (limSym ξ : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ))
    filter_upwards [hae1, hae2, hae_sub] with ξ h1 h2 h3
    have hfn_α : fn α ξ =
        ‖((fracLapSymbol α ξ : ℝ) : ℂ) * (ψ : ℝ → ℂ) ξ - (limSym ξ : ℂ) * (ψ : ℝ → ℂ) ξ‖ ^ 2 := by
      simp [fn, hα]
    rw [hfn_α, h3, Pi.sub_apply, h1, h2]
  have hsqrt := hnorm_sq.sqrt
  simp only [Real.sqrt_zero] at hsqrt
  refine Filter.Tendsto.congr' ?_ hsqrt
  refine Filter.Eventually.of_forall fun α => ?_
  dsimp only
  split_ifs with hα
  · exact Real.sqrt_sq (norm_nonneg _)
  · simp

open Classical in
/-- **Strong `L²` Limit as `α → 0⁺` (Generator Form, `cor:limit`)**:
for every `φ ∈ 𝓢(ℝ; ℂ)`, `-(fracLapSemigroup α).generator φ → φ` in `L²(ℝ; ℂ)` as `α → 0⁺`. -/
theorem tendsto_neg_generator_fracLapSemigroup_zero (φ : 𝓢(ℝ, ℂ)) :
    Filter.Tendsto (fun α : ℝ =>
      if hα : FractionalExponent α then
        ‖-((fracLapSemigroup α).generator
          ⟨(φ.toLp 2 volume : L2C), fracLapSemigroup_schwartz_mem_generatorDomain hα φ⟩) -
          (φ.toLp 2 volume : L2C)‖
      else 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hF_mem : Set.Ioo (0 : ℝ) 2 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Ioo_mem_nhdsGT (by norm_num)
  have h1_mem : MemLp (fun ξ : ℝ => ((1 : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) 2 volume := by
    simpa only [Complex.ofReal_one, one_mul] using (𝓕 φ).memLp 2 volume
  have hlim_ae : ∀ᵐ ξ : ℝ ∂volume, Filter.Tendsto (fun α : ℝ => fracLapSymbol α ξ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 : ℝ)) := by
    have hne : ∀ᵐ ξ : ℝ ∂volume, ξ ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [hne] with ξ hξ
    have hpos : 0 < |2 * Real.pi * ξ| := abs_pos.mpr (by positivity [Real.pi_pos, hξ])
    have hcont : ContinuousAt (fun α : ℝ => |2 * Real.pi * ξ| ^ α) 0 :=
      (continuous_const.rpow continuous_id (fun _ => Or.inl hpos.ne')).continuousAt
    have h0 : |2 * Real.pi * ξ| ^ (0 : ℝ) = 1 := Real.rpow_zero _
    simpa [fracLapSymbol, h0] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hspec := tendsto_norm_toLp_fracLapSymbol_mul_fourier φ hF_mem
    (limSym := fun _ => 1) measurable_const
    (fun ξ => by rw [abs_one]; linarith [sq_nonneg (2 * Real.pi * ξ)])
    h1_mem hlim_ae
  refine Filter.Tendsto.congr' ?_ hspec
  filter_upwards [hF_mem] with α (hα : FractionalExponent α)
  simp only [hα, ↓reduceDIte]
  have hF_inv : 𝓕⁻ (h1_mem.toLp (fun ξ : ℝ => ((1 : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ)) =
      (φ.toLp 2 volume : L2C) := by
    have htoLp : h1_mem.toLp (fun ξ : ℝ => ((1 : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) =
        ((𝓕 φ).toLp 2 volume : L2C) := by
      rw [Lp.ext_iff]
      filter_upwards [h1_mem.coeFn_toLp, (𝓕 φ).coeFn_toLp 2 volume] with ξ h1 h2
      rw [h1, h2]
      simp
    rw [htoLp, ← SchwartzMap.toLp_fourier_eq φ]
    exact (Lp.fourierTransformₗᵢ ℝ ℂ).symm_apply_apply (φ.toLp 2 volume : L2C)
  symm
  rw [generator_fracLapSemigroup_schwartz hα φ, neg_neg, ← hF_inv]
  change ‖(Lp.fourierTransformₗᵢ ℝ ℂ).symm _ - (Lp.fourierTransformₗᵢ ℝ ℂ).symm _‖ = _
  rw [← map_sub]
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map _

open Classical in
/-- **Strong `L²` Limit as `α → 0⁺` (`cor:limit`)**:
for a real function `u` matching a Schwartz function `φ ∈ 𝓢(ℝ; ℂ)`,
`‖(-Δ)^(α/2) u - u‖_{L²(ℝ)} → 0` as `α → 0⁺`. -/
theorem tendsto_fracLapSecondDiff_zero_L2 {u : ℝ → ℝ} (φ : 𝓢(ℝ, ℂ))
    (hφ : ∀ x, (φ : ℝ → ℂ) x = (u x : ℂ)) :
    Filter.Tendsto (fun α : ℝ =>
      if _hα : FractionalExponent α then
        MeasureTheory.eLpNorm (fun x : ℝ => (fracLapSecondDiff α u x : ℂ) - (u x : ℂ)) 2 volume
      else 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hgen := tendsto_neg_generator_fracLapSemigroup_zero φ
  have hgen_e : Filter.Tendsto (fun α : ℝ =>
      if hα : FractionalExponent α then
        ENNReal.ofReal ‖-((fracLapSemigroup α).generator
          ⟨(φ.toLp 2 volume : L2C), fracLapSemigroup_schwartz_mem_generatorDomain hα φ⟩) -
          (φ.toLp 2 volume : L2C)‖
      else 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hgen)
    simp only [Function.comp_def, ENNReal.ofReal_zero] at h0
    refine Filter.Tendsto.congr (fun α => ?_) h0
    by_cases hα' : FractionalExponent α <;> simp [hα']
  refine Filter.Tendsto.congr' ?_ hgen_e
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 2)] with α (hα : FractionalExponent α)
  simp only [hα, ↓reduceDIte]
  let gL2 : L2C := -((fracLapSemigroup α).generator
    ⟨(φ.toLp 2 volume : L2C), fracLapSemigroup_schwartz_mem_generatorDomain hα φ⟩)
  have hdiff_ae : (fun x : ℝ => (fracLapSecondDiff α u x : ℂ) - (u x : ℂ)) =ᵐ[volume]
      ((gL2 - (φ.toLp 2 volume : L2C) : L2C) : ℝ → ℂ) := by
    filter_upwards [fracLapSecondDiff_ae_eq_neg_generator hα φ hφ,
      φ.coeFn_toLp 2 volume, Lp.coeFn_sub gL2 (φ.toLp 2 volume : L2C)] with x hx1 hx2 hx3
    rw [hx3, Pi.sub_apply, hx1, hx2, hφ x]
  rw [eLpNorm_congr_ae hdiff_ae, ← Lp.eNorm_def]
  change ENNReal.ofReal ‖gL2 - (φ.toLp 2 volume : L2C)‖ = ‖gL2 - (φ.toLp 2 volume : L2C)‖ₑ
  exact ofReal_norm _

open Classical in
/-- **Strong `L²` Limit as `α → 2⁻` (Generator Form, `cor:limit`)**:
for every `φ ∈ 𝓢(ℝ; ℂ)`, `-(fracLapSemigroup α).generator φ → -φ''` in `L²(ℝ; ℂ)` as `α → 2⁻`. -/
theorem tendsto_neg_generator_fracLapSemigroup_two (φ : 𝓢(ℝ, ℂ)) :
    Filter.Tendsto (fun α : ℝ =>
      if hα : FractionalExponent α then
        ‖-((fracLapSemigroup α).generator
          ⟨(φ.toLp 2 volume : L2C), fracLapSemigroup_schwartz_mem_generatorDomain hα φ⟩) -
          ((-(SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ φ))).toLp 2 volume : L2C)‖
      else 0) (nhdsWithin 2 (Set.Iio 2)) (nhds 0) := by
  have hF_mem : Set.Ioo (0 : ℝ) 2 ∈ nhdsWithin (2 : ℝ) (Set.Iio 2) :=
    Ioo_mem_nhdsLT (by norm_num)
  let d2φ : 𝓢(ℝ, ℂ) := -(SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ φ))
  have h2_mem :
      MemLp (fun ξ : ℝ => ((fracLapSymbol 2 ξ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) 2 volume := by
    have heq : (fun ξ : ℝ => ((fracLapSymbol 2 ξ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) =
        ((𝓕 d2φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
      funext ξ
      exact (fourier_neg_secondDeriv_schwartz φ ξ).symm
    rw [heq]
    exact (𝓕 d2φ).memLp 2 volume
  have h2_meas : Measurable (fracLapSymbol 2) := by
    unfold fracLapSymbol
    fun_prop
  have h2_bd : ∀ ξ : ℝ, |fracLapSymbol 2 ξ| ≤ 1 + (2 * Real.pi * ξ) ^ 2 := fun ξ => by
    have hnonneg : 0 ≤ fracLapSymbol 2 ξ := by unfold fracLapSymbol; positivity
    rw [abs_of_nonneg hnonneg]
    exact fracLapSymbol_le_one_add_sq (by norm_num) le_rfl ξ
  have hlim_ae : ∀ᵐ ξ : ℝ ∂volume, Filter.Tendsto (fun α : ℝ => fracLapSymbol α ξ)
      (nhdsWithin 2 (Set.Iio 2)) (nhds (fracLapSymbol 2 ξ)) := by
    refine Filter.Eventually.of_forall fun ξ => ?_
    have hcont : ContinuousAt (fun α : ℝ => |2 * Real.pi * ξ| ^ α) 2 :=
      continuousAt_const.rpow continuousAt_id (Or.inr two_pos)
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hspec := tendsto_norm_toLp_fracLapSymbol_mul_fourier φ hF_mem h2_meas h2_bd h2_mem hlim_ae
  refine Filter.Tendsto.congr' ?_ hspec
  filter_upwards [hF_mem] with α (hα : FractionalExponent α)
  simp only [hα, ↓reduceDIte]
  have hF_inv : 𝓕⁻ (h2_mem.toLp (fun ξ : ℝ => ((fracLapSymbol 2 ξ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ)) =
      (d2φ.toLp 2 volume : L2C) := by
    have htoLp : h2_mem.toLp (fun ξ : ℝ => ((fracLapSymbol 2 ξ : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) =
        ((𝓕 d2φ).toLp 2 volume : L2C) := by
      rw [Lp.ext_iff]
      filter_upwards [h2_mem.coeFn_toLp, (𝓕 d2φ).coeFn_toLp 2 volume] with ξ h1 h2
      rw [h1, h2, fourier_neg_secondDeriv_schwartz]
    rw [htoLp, ← SchwartzMap.toLp_fourier_eq d2φ]
    exact (Lp.fourierTransformₗᵢ ℝ ℂ).symm_apply_apply (d2φ.toLp 2 volume : L2C)
  symm
  rw [generator_fracLapSemigroup_schwartz hα φ, neg_neg, ← hF_inv]
  change ‖(Lp.fourierTransformₗᵢ ℝ ℂ).symm _ - (Lp.fourierTransformₗᵢ ℝ ℂ).symm _‖ = _
  rw [← map_sub]
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map _

open Classical in
/-- **Strong `L²` Limit as `α → 2⁻` (`cor:limit`)**:
for a real function `u` matching a Schwartz function `φ ∈ 𝓢(ℝ; ℂ)`,
`‖(-Δ)^(α/2) u - (-u'')‖_{L²(ℝ)} → 0` as `α → 2⁻`. -/
theorem tendsto_fracLapSecondDiff_two_L2 {u : ℝ → ℝ} (φ : 𝓢(ℝ, ℂ))
    (hφ : ∀ x, (φ : ℝ → ℂ) x = (u x : ℂ)) :
    Filter.Tendsto (fun α : ℝ =>
      if _hα : FractionalExponent α then
        MeasureTheory.eLpNorm
          (fun x : ℝ => (fracLapSecondDiff α u x : ℂ) + deriv (deriv (φ : ℝ → ℂ)) x) 2 volume
      else 0) (nhdsWithin 2 (Set.Iio 2)) (nhds 0) := by
  let d2φ : 𝓢(ℝ, ℂ) := -(SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ φ))
  have hgen := tendsto_neg_generator_fracLapSemigroup_two φ
  have hgen_e : Filter.Tendsto (fun α : ℝ =>
      if hα : FractionalExponent α then
        ENNReal.ofReal ‖-((fracLapSemigroup α).generator
          ⟨(φ.toLp 2 volume : L2C), fracLapSemigroup_schwartz_mem_generatorDomain hα φ⟩) -
          (d2φ.toLp 2 volume : L2C)‖
      else 0) (nhdsWithin 2 (Set.Iio 2)) (nhds 0) := by
    have h0 := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hgen)
    simp only [Function.comp_def, ENNReal.ofReal_zero] at h0
    refine Filter.Tendsto.congr (fun α => ?_) h0
    by_cases hα' : FractionalExponent α <;> simp [hα', d2φ]
  refine Filter.Tendsto.congr' ?_ hgen_e
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 2)] with α (hα : FractionalExponent α)
  simp only [hα, ↓reduceDIte]
  let gL2 : L2C := -((fracLapSemigroup α).generator
    ⟨(φ.toLp 2 volume : L2C), fracLapSemigroup_schwartz_mem_generatorDomain hα φ⟩)
  have hd2 : ∀ x : ℝ, -(d2φ : ℝ → ℂ) x = deriv (deriv (φ : ℝ → ℂ)) x := by
    intro x
    have h1 : deriv (φ : ℝ → ℂ) = ((SchwartzMap.derivCLM ℝ ℂ φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
      ext y; exact (SchwartzMap.derivCLM_apply ℝ φ y).symm
    rw [show -(d2φ : ℝ → ℂ) x = (SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ φ) :
      ℝ → ℂ) x by dsimp [d2φ]; simp]
    rw [h1]
    exact SchwartzMap.derivCLM_apply ℝ (SchwartzMap.derivCLM ℝ ℂ φ) x
  have hdiff_ae :
      (fun x : ℝ => (fracLapSecondDiff α u x : ℂ) + deriv (deriv (φ : ℝ → ℂ)) x) =ᵐ[volume]
      ((gL2 - (d2φ.toLp 2 volume : L2C) : L2C) : ℝ → ℂ) := by
    filter_upwards [fracLapSecondDiff_ae_eq_neg_generator hα φ hφ,
      d2φ.coeFn_toLp 2 volume, Lp.coeFn_sub gL2 (d2φ.toLp 2 volume : L2C)] with x hx1 hx2 hx3
    rw [hx3, Pi.sub_apply, hx1, hx2, sub_eq_add_neg, hd2 x]
  rw [eLpNorm_congr_ae hdiff_ae, ← Lp.eNorm_def]
  change ENNReal.ofReal ‖gL2 - (d2φ.toLp 2 volume : L2C)‖ = ‖gL2 - (d2φ.toLp 2 volume : L2C)‖ₑ
  exact ofReal_norm _

end ClassicalLimit

end

end FracLap
