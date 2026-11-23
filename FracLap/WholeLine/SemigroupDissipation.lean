/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.Bernstein
public import FracLap.WholeLine.FourierSemigroup
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# FracLap.WholeLine.SemigroupDissipation

Energy dissipation for the fractional heat semigroup on `L²(ℝ; ℂ)`.

With `g = 𝓕 f` and `λ(ξ) = |2π ξ|^α`:
- `fourier_fracLapSemigroup_ae`: `𝓕 (T_t f) = exp(-t λ) 𝓕 f` almost everywhere;
- `lintegral_norm_sq_semigroup`: `‖T_t f‖² = ∫ exp(-2 t λ) |g|²`;
- `energy_semigroup`: `E_α(T_t f) = ∫ λ exp(-2 t λ) |g|²`.
-/

namespace FracLap

open Complex Filter FourierTransform MeasureTheory Real Set Topology
open scoped ENNReal NNReal

@[expose] public section

/-- On the Fourier side the semigroup is multiplication by `exp (-t |2π ξ|^α)`. -/
theorem fourier_fracLapSemigroup_ae (α : ℝ) (t : ℝ≥0) (f : L2C) :
    ∀ᵐ ξ : ℝ, ((𝓕 (fracLapSemigroup α t f) : L2C) : ℝ → ℂ) ξ =
      ((Real.exp (-(t : ℝ) * fracLapSymbol α ξ) : ℝ) : ℂ) * ((𝓕 f : L2C) : ℝ → ℂ) ξ := by
  have h : 𝓕 (fracLapSemigroup α t f) =
      expMultiplierSymbol (fracLapSymbol α) (measurable_fracLapSymbol α)
        (fracLapSymbol_nonneg α) t • 𝓕 f := by
    change 𝓕 (fourierMultiplierSemigroup (fracLapSymbol α) (measurable_fracLapSymbol α)
      (fracLapSymbol_nonneg α) t f) = _
    rw [fourierMultiplierSemigroup_apply, fourier_fourierInv_eq]
  rw [h]
  filter_upwards [Lp.coeFn_lpSMul (r := 2)
    (expMultiplierSymbol (fracLapSymbol α) (measurable_fracLapSymbol α)
      (fracLapSymbol_nonneg α) t) (𝓕 f),
    coeFn_toLpTop (expSymbol_aestronglyMeasurable (fracLapSymbol α)
      (measurable_fracLapSymbol α) t) zero_le_one
      (norm_expSymbol_le_one (fracLapSymbol α) (fracLapSymbol_nonneg α) t.coe_nonneg)]
    with ξ h1 h2
  rw [h1]
  change ((expMultiplierSymbol (fracLapSymbol α) (measurable_fracLapSymbol α)
      (fracLapSymbol_nonneg α) t : Lp (α := ℝ) ℂ ∞ volume) : ℝ → ℂ) ξ * _ = _
  rw [show ((expMultiplierSymbol (fracLapSymbol α) (measurable_fracLapSymbol α)
      (fracLapSymbol_nonneg α) t : Lp (α := ℝ) ℂ ∞ volume) : ℝ → ℂ) ξ =
      ((Real.exp (-(t : ℝ) * fracLapSymbol α ξ) : ℝ) : ℂ) from h2]

/-- `‖e z‖ₑ² = ofReal (e²)` for a positive real multiplier. -/
theorem enorm_real_mul_sq (e : ℝ) (z : ℂ) :
    ‖((e : ℝ) : ℂ) * z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (e ^ 2) * ‖z‖ₑ ^ (2 : ℝ) := by
  rw [enorm_rpow_two_eq_ofReal, enorm_rpow_two_eq_ofReal, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs, ENNReal.ofReal_mul (sq_nonneg e)]

/-- `‖T_t f‖² = ∫ exp (-2 t λ) ‖𝓕 f‖²` (lower integrals). -/
theorem lintegral_norm_sq_semigroup (α : ℝ) (t : ℝ≥0) (f : L2C) :
    ‖fracLapSemigroup α t f‖ₑ ^ (2 : ℝ) =
      ∫⁻ ξ, ENNReal.ofReal (Real.exp (-2 * (t : ℝ) * fracLapSymbol α ξ)) *
        ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) := by
  rw [← lintegral_enorm_sq_fourier]
  refine lintegral_congr_ae ?_
  filter_upwards [fourier_fracLapSemigroup_ae α t f] with ξ hξ
  rw [hξ, enorm_real_mul_sq, ← Real.exp_nat_mul]
  congr 3
  push_cast; ring

/-- `E_α(T_t f) = ∫ λ exp (-2 t λ) ‖𝓕 f‖²` (lower integrals). -/
theorem energy_semigroup {α : ℝ} (hα : FractionalExponent α) (t : ℝ≥0) (f : L2C) :
    gagliardoEnergyC α (fracLapSemigroup α t f) =
      ∫⁻ ξ, ENNReal.ofReal (fracLapSymbol α ξ) *
        (ENNReal.ofReal (Real.exp (-2 * (t : ℝ) * fracLapSymbol α ξ)) *
          ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ)) := by
  rw [gagliardoEnergyC_eq_lintegral hα]
  refine lintegral_congr_ae ?_
  filter_upwards [fourier_fracLapSemigroup_ae α t f] with ξ hξ
  rw [hξ, enorm_real_mul_sq, ← Real.exp_nat_mul]
  have : (((2 : ℕ) : ℝ) * (-(t : ℝ) * fracLapSymbol α ξ)) = -2 * (t : ℝ) * fracLapSymbol α ξ := by
    push_cast; ring
  rw [this]
  rfl

/-- The spectral mass `∫ exp (-2 t λ) ‖𝓕 f‖²`. -/
noncomputable def spectralMass (α : ℝ) (f : L2C) (t : ℝ) : ℝ :=
  ∫ ξ, Real.exp (-2 * t * fracLapSymbol α ξ) * ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2

/-- The spectral energy `∫ λ exp (-2 t λ) ‖𝓕 f‖²`. -/
noncomputable def spectralEnergy (α : ℝ) (f : L2C) (t : ℝ) : ℝ :=
  ∫ ξ, fracLapSymbol α ξ * (Real.exp (-2 * t * fracLapSymbol α ξ) *
    ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2)

/-- `‖𝓕 f‖²` is integrable. -/
theorem integrable_fourier_sq (f : L2C) :
    Integrable (fun ξ => ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2) :=
  (Lp.memLp (𝓕 f : L2C)).integrable_norm_pow (by norm_num)

theorem measurable_fourier_sq (f : L2C) :
    Measurable (fun ξ => ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2) :=
  ((Lp.stronglyMeasurable (𝓕 f : L2C)).measurable.norm).pow_const 2

/-- Integrability of the mass integrand for `t ≥ 0`. -/
theorem integrable_mass (α : ℝ) (f : L2C) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ξ => Real.exp (-2 * t * fracLapSymbol α ξ) *
      ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2) := by
  refine (integrable_fourier_sq f).mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact ((Real.continuous_exp.measurable.comp (measurable_const.mul
      (measurable_fracLapSymbol α))).mul (measurable_fourier_sq f)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    have : Real.exp (-2 * t * fracLapSymbol α ξ) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [fracLapSymbol_nonneg α ξ]
    nlinarith [sq_nonneg ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖]

/-- `x exp (-2 t x) ≤ 1 / (2 t)` for `t > 0`. -/
theorem mul_exp_le {x t : ℝ} (ht : 0 < t) :
    x * Real.exp (-2 * t * x) ≤ 1 / (2 * t) := by
  have h := Real.add_one_le_exp (2 * t * x)
  have hpos : 0 < Real.exp (2 * t * x) := Real.exp_pos _
  have e : Real.exp (-2 * t * x) = (Real.exp (2 * t * x))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [e, mul_inv_le_iff₀ hpos, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

/-- Integrability of the energy integrand for `t > 0`. -/
theorem integrable_energy (α : ℝ) (f : L2C) {t : ℝ} (ht : 0 < t) :
    Integrable (fun ξ => fracLapSymbol α ξ * (Real.exp (-2 * t * fracLapSymbol α ξ) *
      ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2)) := by
  refine ((integrable_fourier_sq f).const_mul (1 / (2 * t))).mono' ?_
    (Eventually.of_forall fun ξ => ?_)
  · exact ((measurable_fracLapSymbol α).mul ((Real.continuous_exp.measurable.comp
      (measurable_const.mul (measurable_fracLapSymbol α))).mul
      (measurable_fourier_sq f))).aestronglyMeasurable
  · have h0 := fracLapSymbol_nonneg α ξ
    rw [Real.norm_of_nonneg (by positivity)]
    have := mul_exp_le (x := fracLapSymbol α ξ) ht
    nlinarith [sq_nonneg ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖,
      mul_le_mul_of_nonneg_right this (sq_nonneg ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖)]

/-- The spectral mass is continuous on `[0, ∞)`. -/
theorem continuousOn_spectralMass (α : ℝ) (f : L2C) :
    ContinuousOn (spectralMass α f) (Ici 0) := by
  refine continuousOn_of_dominated (bound := fun ξ => ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2) ?_ ?_
    (integrable_fourier_sq f) ?_
  · intro t ht
    exact ((Real.continuous_exp.measurable.comp (measurable_const.mul
      (measurable_fracLapSymbol α))).mul (measurable_fourier_sq f)).aestronglyMeasurable
  · intro t ht
    exact Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (by positivity)]
      have : Real.exp (-2 * t * fracLapSymbol α ξ) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ t := ht
        nlinarith [fracLapSymbol_nonneg α ξ]
      nlinarith [sq_nonneg ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖]
  · exact Eventually.of_forall fun ξ => by fun_prop

/-- **Energy dissipation**: `d/dt ∫ exp (-2 t λ) ‖𝓕 f‖² = -2 ∫ λ exp (-2 t λ) ‖𝓕 f‖²`. -/
theorem hasDerivAt_spectralMass (α : ℝ) (f : L2C) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (spectralMass α f) (-2 * spectralEnergy α f t) t := by
  have hF := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun t ξ => Real.exp (-2 * t * fracLapSymbol α ξ) *
      ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2)
    (F' := fun t ξ => -2 * (fracLapSymbol α ξ * (Real.exp (-2 * t * fracLapSymbol α ξ) *
      ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2))) (x₀ := t) (s := Ioi (t / 2))
    (bound := fun ξ => (2 * (1 / (2 * (t / 2)))) * ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2)
    (Ioi_mem_nhds (by linarith)) ?_ (integrable_mass α f ht.le) ?_ ?_
    (((integrable_fourier_sq f).const_mul _)) ?_
  · have e : -2 * spectralEnergy α f t = ∫ ξ, -2 * (fracLapSymbol α ξ *
        (Real.exp (-2 * t * fracLapSymbol α ξ) * ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2)) := by
      unfold spectralEnergy; rw [integral_const_mul]
    rw [e]
    exact hF.2
  · exact Eventually.of_forall fun s => ((Real.continuous_exp.measurable.comp (measurable_const.mul
      (measurable_fracLapSymbol α))).mul (measurable_fourier_sq f)).aestronglyMeasurable
  · exact (measurable_const.mul ((measurable_fracLapSymbol α).mul
      ((Real.continuous_exp.measurable.comp (measurable_const.mul
        (measurable_fracLapSymbol α))).mul (measurable_fourier_sq f)))).aestronglyMeasurable
  · refine Eventually.of_forall fun ξ s hs => ?_
    have h0 := fracLapSymbol_nonneg α ξ
    have hs' : 0 < s := lt_trans (by linarith) hs
    have := mul_exp_le (x := fracLapSymbol α ξ) hs'
    have h1 : 1 / (2 * s) ≤ 1 / (2 * (t / 2)) :=
      one_div_le_one_div_of_le (by positivity) (by simp only [mem_Ioi] at hs; linarith)
    have hq := sq_nonneg ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖
    have hX : 0 ≤ fracLapSymbol α ξ * (Real.exp (-2 * s * fracLapSymbol α ξ) *
        ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2) := by positivity
    rw [show -2 * (fracLapSymbol α ξ * (Real.exp (-2 * s * fracLapSymbol α ξ) *
        ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2)) = -(2 * (fracLapSymbol α ξ *
        (Real.exp (-2 * s * fracLapSymbol α ξ) * ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2))) by ring,
      norm_neg, Real.norm_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right (this.trans h1) hq]
  · refine Eventually.of_forall fun ξ s hs => ?_
    have h1 : HasDerivAt (fun s : ℝ => -2 * s * fracLapSymbol α ξ) (-2 * 1 * fracLapSymbol α ξ) s :=
      (((hasDerivAt_id' s).const_mul (-2)).mul_const (fracLapSymbol α ξ))
    have h2 := (h1.exp).mul_const (‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2)
    convert h2 using 1
    ring

/-- `‖T_t f‖² = ∫ exp (-2 t λ) ‖𝓕 f‖²` as a real identity. -/
theorem norm_sq_semigroup (α : ℝ) (t : ℝ≥0) (f : L2C) :
    ‖fracLapSemigroup α t f‖ ^ 2 = spectralMass α f t := by
  have h := lintegral_norm_sq_semigroup α t f
  have hnn : 0 ≤ᵐ[volume] fun ξ => Real.exp (-2 * (t : ℝ) * fracLapSymbol α ξ) *
      ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2 := Eventually.of_forall fun ξ => by positivity
  have hR : ∫⁻ ξ, ENNReal.ofReal (Real.exp (-2 * (t : ℝ) * fracLapSymbol α ξ)) *
      ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (spectralMass α f t) := by
    unfold spectralMass
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_mass α f t.coe_nonneg) hnn]
    refine lintegral_congr fun ξ => ?_
    rw [enorm_rpow_two_eq_ofReal, ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [hR, enorm_rpow_two_eq_ofReal] at h
  have h0 : 0 ≤ spectralMass α f t := integral_nonneg_of_ae hnn
  exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) h0).1 h

/-- `E_α(T_t f)` is the spectral energy, and it is finite for `t > 0`. -/
theorem energy_semigroup_toReal {α : ℝ} (hα : FractionalExponent α) {t : ℝ≥0}
    (ht : 0 < (t : ℝ)) (f : L2C) :
    gagliardoEnergyC α (fracLapSemigroup α t f) =
      ENNReal.ofReal (spectralEnergy α f t) := by
  have hnn : 0 ≤ᵐ[volume] fun ξ => fracLapSymbol α ξ *
      (Real.exp (-2 * (t : ℝ) * fracLapSymbol α ξ) * ‖((𝓕 f : L2C) : ℝ → ℂ) ξ‖ ^ 2) :=
    Eventually.of_forall fun ξ => by have := fracLapSymbol_nonneg α ξ; positivity
  rw [energy_semigroup hα t f]
  unfold spectralEnergy
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_energy α f ht) hnn]
  refine lintegral_congr fun ξ => ?_
  rw [enorm_rpow_two_eq_ofReal, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (fracLapSymbol_nonneg α ξ)]

/-- At time `0` the spectral mass is `‖f‖²`. -/
theorem spectralMass_zero (α : ℝ) (f : L2C) : spectralMass α f 0 = ‖f‖ ^ 2 := by
  have h := norm_sq_semigroup α 0 f
  have h0 : fracLapSemigroup α 0 f = f := by simp
  rw [h0] at h
  simp at h
  exact h.symm

/-- **Hardy--Stein identity for `p = 2`** (energy identity): for `t ≥ 0`,
`‖f‖² - ‖T_t f‖² = 2 ∫₀ᵗ ∫ λ exp (-2 s λ) ‖𝓕 f‖² ds`, where the inner integral is `E_α(T_s f)`. -/
theorem hardy_stein_l2 (α : ℝ) (f : L2C) (t : ℝ≥0) :
    ‖f‖ ^ 2 - ‖fracLapSemigroup α t f‖ ^ 2 = 2 * ∫ s in (0 : ℝ)..t, spectralEnergy α f s := by
  rw [norm_sq_semigroup, ← spectralMass_zero α f]
  rcases eq_or_lt_of_le t.coe_nonneg with h0 | ht
  · have : (t : ℝ) = 0 := h0.symm
    rw [this]; simp
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) t, HasDerivAt (fun s => -spectralMass α f s)
      (2 * spectralEnergy α f x) x := fun x hx => by
    have := (hasDerivAt_spectralMass α f hx.1).neg
    convert this using 1; ring
  have hcont : ContinuousOn (fun s => -spectralMass α f s) (Icc (0 : ℝ) t) :=
    (continuousOn_spectralMass α f).neg.mono (fun x hx => hx.1)
  have hnn : ∀ x ∈ Ioo (0 : ℝ) t, 0 ≤ 2 * spectralEnergy α f x := by
    intro x hx
    unfold spectralEnergy
    refine mul_nonneg (by norm_num) (integral_nonneg fun ξ => ?_)
    have := fracLapSymbol_nonneg α ξ
    positivity
  have hint : IntervalIntegrable (fun s => 2 * spectralEnergy α f s) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
    exact intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv hnn
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.le hcont hderiv hint
  rw [intervalIntegral.integral_const_mul] at hftc
  linarith

end

end FracLap
