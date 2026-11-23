/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.FourierSemigroup
public import FracLap.WholeLine.GagliardoDensity
public import FracLap.WholeLine.GagliardoScaling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# FracLap.Tools.Nash

The fractional Nash inequality on `ℝ` (Biler--Imbert--Karch, `(N)`; Karch--Miao--Xu, Lemma 2.2):
`‖u‖₂^(2(1+α)) ≤ C E_α(u) ‖u‖₁^(2α)`, where `E_α` is the Gagliardo energy.

This file contains the elementary optimization step (`nash_optimize`): if
`S ≤ 2 R T + R^(-α) e` for every `R > 0`, then `S^(1+α) ≤ 3^(1+α) e T^α`.
-/

namespace FracLap

open Complex FourierTransform MeasureTheory Real Set
open scoped ENNReal

@[expose] public section

/-- **Optimization of the frequency cut-off.** If `S ≤ 2 R T + R^(-α) e` for all `R > 0` (with
`S, T, e ≥ 0` and `α > 0`), then `S^(1+α) ≤ 3^(1+α) e T^α`. -/
theorem nash_optimize {α S T e : ℝ} (hα : 0 < α) (hS : 0 ≤ S) (hT : 0 ≤ T) (he : 0 ≤ e)
    (h : ∀ R : ℝ, 0 < R → S ≤ 2 * R * T + R ^ (-α) * e) :
    S ^ (1 + α) ≤ 3 ^ (1 + α) * e * T ^ α := by
  have h1 : 0 < 1 + α := by linarith
  have hS0_of : S = 0 → S ^ (1 + α) ≤ 3 ^ (1 + α) * e * T ^ α := fun hS0 => by
    rw [hS0, Real.zero_rpow h1.ne']
    positivity
  rcases hT.eq_or_lt with rfl | hTpos
  · -- `T = 0`: `S ≤ R^(-α) e` for all `R`; let `R → ∞`
    refine hS0_of (le_antisymm ?_ hS)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    by_cases he0 : e = 0
    · have := h 1 one_pos
      simp [he0] at this
      linarith
    · have hepos : 0 < e := lt_of_le_of_ne he (Ne.symm he0)
      set R := (e / ε) ^ (1 / α) + 1 with hR
      have hRpos : 0 < R := by positivity
      have hbase : (e / ε) ^ (1 / α) < R := by linarith
      have hpow : e / ε < R ^ α := by
        calc e / ε = ((e / ε) ^ (1 / α)) ^ α := by
              rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hα.ne', Real.rpow_one]
          _ < R ^ α := Real.rpow_lt_rpow (by positivity) hbase hα
      have hlt : R ^ (-α) * e < ε := by
        rw [Real.rpow_neg hRpos.le]
        have hRa : 0 < R ^ α := Real.rpow_pos_of_pos hRpos _
        rw [inv_mul_eq_div, div_lt_iff₀ hRa]
        rw [div_lt_iff₀ hε] at hpow
        linarith
      have := h R hRpos
      simp at this
      linarith
  · by_cases he0 : e = 0
    · -- `e = 0`: `S ≤ 2 R T` for all `R`; let `R → 0`
      refine hS0_of (le_antisymm ?_ hS)
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have := h (ε / (2 * T)) (by positivity)
      rw [he0, mul_zero, add_zero] at this
      have e2 : 2 * (ε / (2 * T)) * T = ε := by field_simp
      linarith
    · have hepos : 0 < e := lt_of_le_of_ne he (Ne.symm he0)
      set R := (e / T) ^ (1 / (1 + α)) with hR
      have hRpos : 0 < R := Real.rpow_pos_of_pos (by positivity) _
      have hRpow : R ^ (1 + α) = e / T := by
        rw [hR, ← Real.rpow_mul (by positivity), one_div_mul_cancel h1.ne', Real.rpow_one]
      have hbound := h R hRpos
      have hkey : R ^ (-α) * e = R * T := by
        have hsplit : R ^ (1 + α) = R * R ^ α := by
          rw [Real.rpow_add hRpos, Real.rpow_one]
        rw [hsplit] at hRpow
        have hRa : 0 < R ^ α := Real.rpow_pos_of_pos hRpos _
        rw [Real.rpow_neg hRpos.le, inv_mul_eq_div, div_eq_iff hRa.ne']
        have : R * R ^ α * T = e := by
          field_simp at hRpow
          linarith
        nlinarith [this]
      rw [hkey] at hbound
      have hS3 : S ≤ 3 * R * T := by linarith
      calc S ^ (1 + α) ≤ (3 * R * T) ^ (1 + α) := Real.rpow_le_rpow hS hS3 h1.le
        _ = 3 ^ (1 + α) * (R ^ (1 + α)) * T ^ (1 + α) := by
            rw [Real.mul_rpow (by positivity) hTpos.le, Real.mul_rpow (by positivity) hRpos.le]
        _ = 3 ^ (1 + α) * (e / T) * T ^ (1 + α) := by rw [hRpow]
        _ = 3 ^ (1 + α) * e * T ^ α := by
            rw [Real.rpow_add hTpos, Real.rpow_one]
            field_simp

/-- Pointwise bound `‖𝓕 f ξ‖ₑ ≤ ‖f‖_{L¹}` for an `L¹ ∩ L²` function, almost everywhere. -/
theorem ae_enorm_fourier_le {f : L2C} (hf1 : Integrable (f : ℝ → ℂ)) :
    ∀ᵐ ξ : ℝ, ‖(𝓕 f : L2C) ξ‖ₑ ≤ ∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ := by
  have hae := coeFn_fourier_toLp_ae_eq_of_integrable hf1 (Lp.memLp f)
  rw [Lp.toLp_coeFn f (Lp.memLp f)] at hae
  filter_upwards [hae] with ξ hξ
  rw [hξ, ← ofReal_norm, ← ofReal_integral_norm_eq_lintegral_eNorm hf1]
  exact ENNReal.ofReal_le_ofReal (Real.norm_fourier_le_integral_norm _ ξ)

/-- **Fractional Nash inequality with a frequency cut-off** (`d = 1`): for `f ∈ L¹ ∩ L²(ℝ; ℂ)` and
every `R > 0`,
`‖f‖₂² ≤ 2R ‖f‖₁² + (R^α Λ_α(1))⁻¹ E_α(f)`,
where `E_α` is the Gagliardo energy and `Λ_α(1) ∈ (0, ∞)` is the constant of the Fourier symbol. -/
theorem nash_cut {α R : ℝ} (hα : FractionalExponent α) (hR : 0 < R) (f : L2C)
    (hf1 : Integrable (f : ℝ → ℂ)) :
    ‖f‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (2 * R) * (∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ) ^ (2 : ℝ) +
      (ENNReal.ofReal (R ^ α) * gagliardoSymbol α 1)⁻¹ * gagliardoEnergyC α f := by
  have hFm : Measurable ((𝓕 f : L2C) : ℝ → ℂ) := (Lp.stronglyMeasurable (𝓕 f : L2C)).measurable
  have hnorm : ‖(𝓕 f : L2C)‖ₑ = ‖f‖ₑ := by
    have := (Lp.fourierTransformₗᵢ ℝ ℂ).norm_map f
    rw [← ofReal_norm, ← ofReal_norm]
    exact congrArg ENNReal.ofReal this
  have hPl : ‖f‖ₑ ^ (2 : ℝ) = ∫⁻ ξ, ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) := by
    rw [lintegral_enorm_sq_eq (𝓕 f : L2C), hnorm]
  have hA : MeasurableSet (Icc (-R) R) := measurableSet_Icc
  rw [hPl, ← lintegral_add_compl _ hA]
  refine add_le_add ?_ ?_
  · -- low frequencies: `‖𝓕 f‖ ≤ ‖f‖₁`
    have hb := ae_enorm_fourier_le hf1
    calc ∫⁻ ξ in Icc (-R) R, ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ _ in Icc (-R) R, (∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ) ^ (2 : ℝ) :=
          lintegral_mono_ae (ae_restrict_of_ae
            (hb.mono fun ξ h => ENNReal.rpow_le_rpow h two_pos.le))
      _ = ENNReal.ofReal (2 * R) * (∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ) ^ (2 : ℝ) := by
          rw [setLIntegral_const, Real.volume_Icc, mul_comm]
          congr 2
          ring
  · -- high frequencies: `Λ_α(ξ) ≥ R^α Λ_α(1)` for `|ξ| > R`
    have hΛ1 := gagliardoSymbol_one_pos hα
    have hΛ1t := gagliardoSymbol_one_lt_top hα
    have hc0 : ENNReal.ofReal (R ^ α) * gagliardoSymbol α 1 ≠ 0 :=
      mul_ne_zero (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hR _)).ne' hΛ1.ne'
    have hctop : ENNReal.ofReal (R ^ α) * gagliardoSymbol α 1 ≠ ∞ :=
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hΛ1t).ne
    set c := ENNReal.ofReal (R ^ α) * gagliardoSymbol α 1 with hc
    have hmul : c * ∫⁻ ξ in (Icc (-R) R)ᶜ, ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) ≤ gagliardoEnergyC α f := by
      rw [← lintegral_const_mul _ (hFm.eNorm.pow_const _)]
      calc ∫⁻ ξ in (Icc (-R) R)ᶜ, c * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ)
          ≤ ∫⁻ ξ in (Icc (-R) R)ᶜ, gagliardoSymbol α ξ * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) := by
            refine setLIntegral_mono' hA.compl fun ξ hξ => ?_
            refine mul_le_mul_of_nonneg_right ?_ bot_le
            have hξR : R < |ξ| := by
              by_contra hcon
              exact hξ ⟨by linarith [abs_le.mp (not_lt.mp hcon)], by
                linarith [abs_le.mp (not_lt.mp hcon)]⟩
            have hξ0 : ξ ≠ 0 := by
              intro h0
              rw [h0, abs_zero] at hξR
              linarith
            rw [gagliardoSymbol_eq hα.1 hξ0]
            exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
              (Real.rpow_le_rpow hR.le hξR.le hα.1.le)) bot_le
        _ ≤ ∫⁻ ξ, gagliardoSymbol α ξ * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) := setLIntegral_le_lintegral _ _
        _ = gagliardoEnergyC α f := (lintegral_gagliardo_energy_fourier α f).symm
    calc ∫⁻ ξ in (Icc (-R) R)ᶜ, ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ)
        = c⁻¹ * (c * ∫⁻ ξ in (Icc (-R) R)ᶜ, ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
      _ ≤ c⁻¹ * gagliardoEnergyC α f := mul_le_mul_right hmul _

/-- Real-number form of `nash_cut`: with `N₁ = ∫ ‖f‖`, `Λ₁ = Λ_α(1)` and `E = E_α(f)` (finite),
`‖f‖² ≤ 2 R N₁² + R^(-α) (Λ₁⁻¹ E)` for every `R > 0`. -/
theorem nash_cut_real {α R : ℝ} (hα : FractionalExponent α) (hR : 0 < R) (f : L2C)
    (hf1 : Integrable (f : ℝ → ℂ)) (hE : gagliardoEnergyC α f ≠ ∞) :
    ‖f‖ ^ 2 ≤ 2 * R * (∫ x, ‖(f : ℝ → ℂ) x‖) ^ 2 +
      R ^ (-α) * ((gagliardoSymbol α 1).toReal⁻¹ * (gagliardoEnergyC α f).toReal) := by
  have hcut := nash_cut hα hR f hf1
  have hΛ1 := gagliardoSymbol_one_pos hα
  have hΛ1t := gagliardoSymbol_one_lt_top hα
  have hN1 : (∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ) ≠ ∞ := hf1.hasFiniteIntegral.ne
  have hN1r : (∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ).toReal = ∫ x, ‖(f : ℝ → ℂ) x‖ := by
    rw [integral_norm_eq_lintegral_eNorm hf1.aestronglyMeasurable]
  have hcpos : ENNReal.ofReal (R ^ α) * gagliardoSymbol α 1 ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hR _)).ne' hΛ1.ne'
  have hctop : ENNReal.ofReal (R ^ α) * gagliardoSymbol α 1 ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hΛ1t).ne
  have hRHS_ne : ENNReal.ofReal (2 * R) * (∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ) ^ (2 : ℝ) +
      (ENNReal.ofReal (R ^ α) * gagliardoSymbol α 1)⁻¹ * gagliardoEnergyC α f ≠ ∞ := by
    refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg
        (by norm_num) hN1)
    · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hcpos) hE
  have := ENNReal.toReal_mono hRHS_ne hcut
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hN1))
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hcpos) hE),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_mul] at this
  simp only [← ENNReal.toReal_rpow, Real.rpow_two, toReal_eNorm, hN1r,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * R),
    ENNReal.toReal_ofReal (Real.rpow_nonneg hR.le α)] at this
  have hΛr : 0 < (gagliardoSymbol α 1).toReal := ENNReal.toReal_pos hΛ1.ne' hΛ1t.ne
  have hRa : 0 < R ^ α := Real.rpow_pos_of_pos hR _
  have e : R ^ (-α) * ((gagliardoSymbol α 1).toReal⁻¹ * (gagliardoEnergyC α f).toReal) =
      (R ^ α * (gagliardoSymbol α 1).toReal)⁻¹ * (gagliardoEnergyC α f).toReal := by
    rw [Real.rpow_neg hR.le, mul_inv]
    ring
  rw [e]
  exact this

/-- **Fractional Nash inequality on `ℝ`** (`d = 1`, any `0 < α < 2`): for `f ∈ L¹ ∩ L²(ℝ; ℂ)` with
finite Gagliardo energy,
`(‖f‖₂²)^(1+α) ≤ 3^(1+α) Λ_α(1)⁻¹ E_α(f) (‖f‖₁²)^α`,
that is `‖f‖₂^(2(1+α)) ≤ C E_α(f) ‖f‖₁^(2α)`, with the explicit constant `C = 3^(1+α) / Λ_α(1)`. -/
theorem fractional_nash {α : ℝ} (hα : FractionalExponent α) (f : L2C)
    (hf1 : Integrable (f : ℝ → ℂ)) (hE : gagliardoEnergyC α f ≠ ∞) :
    (‖f‖ ^ 2) ^ (1 + α) ≤ 3 ^ (1 + α) *
      ((gagliardoSymbol α 1).toReal⁻¹ * (gagliardoEnergyC α f).toReal) *
        ((∫ x, ‖(f : ℝ → ℂ) x‖) ^ 2) ^ α := by
  have hΛr : 0 < (gagliardoSymbol α 1).toReal :=
    ENNReal.toReal_pos (gagliardoSymbol_one_pos hα).ne' (gagliardoSymbol_one_lt_top hα).ne
  refine nash_optimize hα.1 (sq_nonneg _) (sq_nonneg _)
    (mul_nonneg (inv_nonneg.mpr hΛr.le) ENNReal.toReal_nonneg) fun R hR => ?_
  exact nash_cut_real hα hR f hf1 hE

/-- **Fractional Nash inequality for real functions**: for `g ∈ L¹ ∩ L²(ℝ; ℝ)` with finite Gagliardo
energy, `(‖g‖₂²)^(1+α) ≤ 3^(1+α) Λ_α(1)⁻¹ E_α(g) (‖g‖₁²)^α`. -/
theorem fractional_nash_real {α : ℝ} (hα : FractionalExponent α) (g : L2R)
    (hg1 : Integrable (g : ℝ → ℝ)) (hE : gagliardoEnergyR α g ≠ ∞) :
    (‖g‖ ^ 2) ^ (1 + α) ≤ 3 ^ (1 + α) *
      ((gagliardoSymbol α 1).toReal⁻¹ * (gagliardoEnergyR α g).toReal) *
        ((∫ x, ‖(g : ℝ → ℝ) x‖) ^ 2) ^ α := by
  have hae := coeFn_ofRealL2 g
  have hf1 : Integrable ((ofRealL2 g : L2C) : ℝ → ℂ) := by
    have : Integrable (fun x : ℝ => (((g : ℝ → ℝ) x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.integrable_comp hg1
    exact this.congr (hae.mono fun x hx => hx.symm)
  have hnorm : ‖ofRealL2 g‖ = ‖g‖ := by
    have h := enorm_sq_ofRealL2 g
    have h2 : (ENNReal.ofReal ‖ofRealL2 g‖) ^ (2 : ℝ) = (ENNReal.ofReal ‖g‖) ^ (2 : ℝ) := by
      rwa [ofReal_norm, ofReal_norm]
    have h3 : ENNReal.ofReal ‖ofRealL2 g‖ = ENNReal.ofReal ‖g‖ :=
      (ENNReal.rpow_left_injective (by norm_num : (2 : ℝ) ≠ 0)) h2
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) (norm_nonneg _)).mp h3
  have hint : ∫ x, ‖((ofRealL2 g : L2C) : ℝ → ℂ) x‖ = ∫ x, ‖(g : ℝ → ℝ) x‖ := by
    refine integral_congr_ae (hae.mono fun x hx => ?_)
    beta_reduce
    rw [hx]
    exact Complex.norm_real _
  have hEc : gagliardoEnergyC α (ofRealL2 g) ≠ ∞ := by
    rwa [gagliardoEnergyC_ofRealL2]
  have := fractional_nash hα (ofRealL2 g) hf1 hEc
  rw [hnorm, hint, gagliardoEnergyC_ofRealL2] at this
  exact this

end

end FracLap
