/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.SemigroupDissipation
public import FracLap.WholeLine.StableSemigroup
public import FracLap.Tools.NashDecay
public import FracLap.Tools.NashConsequences

/-!
# FracLap.WholeLine.NashUltracontractivity

The Carlen--Kusuoka--Stroock argument for the fractional heat semigroup: the Nash inequality,
the energy dissipation `d/dt ‖T_t f‖² = -2 E_α(T_t f)` and the `L¹` contraction property give the
`L¹ → L²` decay `‖T_t f‖₂² ≤ (K ‖f‖₁^{2α} / (2 α t))^{1/α}` with `K = 3^{1+α} (2π)^{-α}`.

- `lintegral_enorm_convolution_le`: Young's inequality `‖K ⋆ f‖₁ ≤ ‖K‖₁ ‖f‖₁`.
- `integral_norm_semigroup_le`: `‖T_t u‖₁ ≤ ‖u‖₁` for Schwartz data `u`.
- `nash_l1_l2_decay`: the decay estimate.
-/

namespace FracLap

open Complex Filter FourierTransform MeasureTheory Real Set Topology
open scoped ENNReal NNReal SchwartzMap Convolution

@[expose] public section

/-- **Young's inequality in `L¹`**: `∫⁻ ‖(K ⋆ f)(x)‖ₑ ≤ (∫⁻ ‖K‖ₑ) (∫⁻ ‖f‖ₑ)`. -/
theorem lintegral_enorm_convolution_le {K f : ℝ → ℂ} (hK : AEStronglyMeasurable K volume)
    (hf : AEStronglyMeasurable f volume) :
    ∫⁻ x, ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖ₑ ≤
      (∫⁻ y, ‖K y‖ₑ) * ∫⁻ x, ‖f x‖ₑ := by
  have h1 : ∀ x, ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖ₑ ≤ ∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ := by
    intro x
    refine (eNorm_integral_le_lintegral_eNorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    simp [eNorm_mul]
  calc ∫⁻ x, ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖ₑ ≤ ∫⁻ x, ∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ :=
        lintegral_mono h1
    _ = ∫⁻ y, ∫⁻ x, ‖K y‖ₑ * ‖f (x - y)‖ₑ := by
        refine lintegral_lintegral_swap ?_
        have hfs : AEMeasurable (fun p : ℝ × ℝ => ‖f (p.1 - p.2)‖ₑ) (volume.prod volume) :=
          (hf.comp_quasiMeasurePreserving
            (quasiMeasurePreserving_sub volume volume)).aemeasurable.eNorm
        exact (hK.aemeasurable.eNorm.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume))).mul hfs
    _ = (∫⁻ y, ‖K y‖ₑ) * ∫⁻ x, ‖f x‖ₑ := by
        rw [← lintegral_mul_const'' _ hK.aemeasurable.eNorm]
        refine lintegral_congr fun y => ?_
        rw [lintegral_const_mul' _ _ eNorm_ne_top]
        congr 1
        exact lintegral_sub_right_eq_self (fun x => ‖f x‖ₑ) y

/-- The stable kernel has unit `L¹` norm. -/
theorem lintegral_enorm_stableKernel {α : ℝ} (hα : FractionalExponent α) {t : ℝ} (ht : 0 < t) :
    ∫⁻ y, ‖(((stableHeatKernel α hα).P y t : ℝ) : ℂ)‖ₑ = 1 := by
  have hint := (stableHeatKernel α hα).integrable_space t ht
  have hnn := (stableHeatKernel α hα).nonneg
  have : ∀ y, ‖(((stableHeatKernel α hα).P y t : ℝ) : ℂ)‖ₑ =
      ENNReal.ofReal ((stableHeatKernel α hα).P y t) := fun y => by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hnn y t ht)]
  simp_rw [this]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => hnn y t ht),
    (stableHeatKernel α hα).integral_eq_one t ht, ENNReal.ofReal_one]

/-- **`L¹` contractivity** of the fractional heat semigroup on Schwartz data. -/
theorem lintegral_norm_semigroup_le {α : ℝ} (hα : FractionalExponent α) {t : ℝ≥0}
    (ht : 0 < (t : ℝ)) (u : 𝓢(ℝ, ℂ)) :
    ∫⁻ x, ‖((fracLapSemigroup α t (u.toLp 2) : L2C) : ℝ → ℂ) x‖ₑ ≤ ∫⁻ x, ‖(u : ℝ → ℂ) x‖ₑ := by
  have hK : Integrable (fun x : ℝ => (((stableHeatKernel α hα).P x t : ℝ) : ℂ)) volume :=
    Complex.ofRealCLM.integrable_comp ((stableHeatKernel α hα).integrable_space t ht)
  rw [fracLapSemigroup_apply_schwartz hα ht u]
  have hae := MemLp.coeFn_toLp (memLp_two_convolution_schwartz hK u)
  calc ∫⁻ x, ‖((memLp_two_convolution_schwartz hK u).toLp _ : L2C) x‖ₑ
      = ∫⁻ x, ‖((fun x : ℝ => (((stableHeatKernel α hα).P x t : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul
          ℂ ℂ] (u : ℝ → ℂ)) x‖ₑ := lintegral_congr_ae (hae.mono fun x hx => by beta_reduce; rw [hx])
    _ ≤ (∫⁻ y, ‖(((stableHeatKernel α hα).P y t : ℝ) : ℂ)‖ₑ) * ∫⁻ x, ‖(u : ℝ → ℂ) x‖ₑ :=
        lintegral_enorm_convolution_le hK.aestronglyMeasurable u.continuous.aestronglyMeasurable
    _ = ∫⁻ x, ‖(u : ℝ → ℂ) x‖ₑ := by rw [lintegral_enorm_stableKernel hα ht, one_mul]

/-- The semigroup applied to Schwartz data is integrable, with `L¹` norm at most `‖u‖₁`. -/
theorem integrable_norm_semigroup {α : ℝ} (hα : FractionalExponent α) {t : ℝ≥0}
    (ht : 0 < (t : ℝ)) (u : 𝓢(ℝ, ℂ)) :
    Integrable ((fracLapSemigroup α t (u.toLp 2) : L2C) : ℝ → ℂ) ∧
      ∫ x, ‖((fracLapSemigroup α t (u.toLp 2) : L2C) : ℝ → ℂ) x‖ ≤ ∫ x, ‖(u : ℝ → ℂ) x‖ := by
  have hle := lintegral_norm_semigroup_le hα ht u
  have hu : Integrable (u : ℝ → ℂ) := u.integrable
  have hfin : ∫⁻ x, ‖(u : ℝ → ℂ) x‖ₑ < ⊤ := hu.2
  refine ⟨⟨(Lp.aestronglyMeasurable _), lt_of_le_of_lt hle hfin⟩, ?_⟩
  rw [integral_norm_eq_lintegral_eNorm (Lp.aestronglyMeasurable _),
    integral_norm_eq_lintegral_eNorm hu.1]
  exact ENNReal.toReal_mono hfin.ne hle

/-- **Nash ⇒ `L¹ → L²` decay for the fractional heat semigroup** (Schwartz data):
`‖T_t u‖₂² ≤ (3^(1+α) (2π)^(-α) ‖u‖₁^(2α) / (2 α t))^(1/α)`, i.e. `‖T_t u‖₂ ≲ t^(-1/(2α)) ‖u‖₁`. -/
theorem nash_l1_l2_decay {α : ℝ} (hα : FractionalExponent α) (u : 𝓢(ℝ, ℂ))
    (hM : 0 < ∫ x, ‖(u : ℝ → ℂ) x‖) {t : ℝ≥0} (ht : 0 < (t : ℝ)) :
    ‖fracLapSemigroup α t (u.toLp 2)‖ ^ 2 ≤
      (3 ^ (1 + α) * ((2 * π) ^ α)⁻¹ * (∫ x, ‖(u : ℝ → ℂ) x‖) ^ (2 * α) /
        (2 * α * t)) ^ (1 / α) := by
  set f : L2C := u.toLp 2 with hf
  set M : ℝ := ∫ x, ‖(u : ℝ → ℂ) x‖ with hMdef
  have hα0 : 0 < α := hα.1
  have hK : 0 < 3 ^ (1 + α) * ((2 * π) ^ α)⁻¹ := by positivity
  rw [norm_sq_semigroup]
  refine nash_decay (u := spectralMass α f) (E := spectralEnergy α f) hK hM hα0
    (continuousOn_spectralMass α f) (fun s hs => integral_nonneg fun ξ => by positivity)
    (fun s hs => hasDerivAt_spectralMass α f hs) ?_ t ht
  intro s hs
  set s' : ℝ≥0 := ⟨s, hs.le⟩ with hs'
  have hs'pos : 0 < (s' : ℝ) := hs
  obtain ⟨hg1, hgM⟩ := integrable_norm_semigroup hα hs'pos u
  have hgE : gagliardoEnergyC α (fracLapSemigroup α s' f) ≠ ⊤ := by
    rw [energy_semigroup_toReal hα hs'pos f]; exact ENNReal.ofReal_ne_top
  have hn := fractional_nash_explicit hα (fracLapSemigroup α s' f) hg1 hgE
  have hE0 : 0 ≤ spectralEnergy α f (s' : ℝ) := integral_nonneg fun ξ => by
    have := fracLapSymbol_nonneg α ξ; positivity
  rw [energy_semigroup_toReal hα hs'pos f, ENNReal.toReal_ofReal hE0, norm_sq_semigroup] at hn
  have hgM' : (∫ x, ‖((fracLapSemigroup α s' f : L2C) : ℝ → ℂ) x‖) ^ 2 ≤ M ^ 2 := by
    have h0 : 0 ≤ ∫ x, ‖((fracLapSemigroup α s' f : L2C) : ℝ → ℂ) x‖ := integral_nonneg fun x =>
      norm_nonneg _
    exact pow_le_pow_left₀ h0 hgM 2
  have hpow : ((∫ x, ‖((fracLapSemigroup α s' f : L2C) : ℝ → ℂ) x‖) ^ 2) ^ α ≤ M ^ (2 * α) := by
    calc ((∫ x, ‖((fracLapSemigroup α s' f : L2C) : ℝ → ℂ) x‖) ^ 2) ^ α ≤ (M ^ 2) ^ α :=
          Real.rpow_le_rpow (by positivity) hgM' hα0.le
      _ = M ^ (2 * α) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]; norm_num
  have hc : 0 ≤ 3 ^ (1 + α) * (((2 * π) ^ α)⁻¹ * spectralEnergy α f (s' : ℝ)) := by positivity
  calc spectralMass α f s ^ (1 + α)
      ≤ 3 ^ (1 + α) * (((2 * π) ^ α)⁻¹ * spectralEnergy α f (s' : ℝ)) *
        ((∫ x, ‖((fracLapSemigroup α s' f : L2C) : ℝ → ℂ) x‖) ^ 2) ^ α := hn
    _ ≤ 3 ^ (1 + α) * (((2 * π) ^ α)⁻¹ * spectralEnergy α f (s' : ℝ)) * M ^ (2 * α) :=
        mul_le_mul_of_nonneg_left hpow hc
    _ = 3 ^ (1 + α) * ((2 * π) ^ α)⁻¹ * spectralEnergy α f s * M ^ (2 * α) := by
        change _ = _ * spectralEnergy α f (s' : ℝ) * _
        ring

/-- **Sup bound for the heat kernel**: `P_α(x, t) ≤ t^(-1/α) P_α(0, 1)`. -/
theorem FractionalHeatKernel.le_sup {α : ℝ} (K : FractionalHeatKernel α) (x : ℝ) {t : ℝ}
    (ht : 0 < t) : K.P x t ≤ t ^ (-1 / α) * K.P 0 1 := by
  rw [K.self_similar x t ht]
  have h0 : |(0 : ℝ)| ≤ |x * t ^ (-1 / α)| := by rw [abs_zero]; exact abs_nonneg _
  exact mul_le_mul_of_nonneg_left (K.radial_antitone 0 _ 1 one_pos h0) (by positivity)

/-- **`L¹ → L^∞` bound**: for Schwartz data the convolution with the stable kernel satisfies
`‖(P_t ⋆ u)(x)‖ ≤ t^(-1/α) P(0, 1) ‖u‖₁` for every `x`. -/
theorem stable_conv_sup_le {α : ℝ} (hα : FractionalExponent α) {t : ℝ} (ht : 0 < t)
    (u : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖((fun y : ℝ => (((stableHeatKernel α hα).P y t : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (u : ℝ → ℂ)) x‖ ≤
      t ^ (-1 / α) * (stableHeatKernel α hα).P 0 1 * ∫ y, ‖(u : ℝ → ℂ) y‖ := by
  set S : ℝ := t ^ (-1 / α) * (stableHeatKernel α hα).P 0 1 with hS
  have hint : Integrable (fun y : ℝ => ‖(u : ℝ → ℂ) (x - y)‖) :=
    (u.integrable.norm.comp_sub_left x)
  have hbound : ∀ y : ℝ, ‖(ContinuousLinearMap.mul ℂ ℂ)
      ((((stableHeatKernel α hα).P y t : ℝ) : ℂ)) ((u : ℝ → ℂ) (x - y))‖ ≤
      S * ‖(u : ℝ → ℂ) (x - y)‖ := fun y => by
    simp only [ContinuousLinearMap.mul_apply', norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg ((stableHeatKernel α hα).nonneg y t ht)]
    exact mul_le_mul_of_nonneg_right ((stableHeatKernel α hα).le_sup y ht) (norm_nonneg _)
  have := norm_integral_le_of_norm_le (hint.const_mul S) (Eventually.of_forall hbound)
  rw [integral_const_mul, integral_sub_left_eq_self (fun y => ‖(u : ℝ → ℂ) y‖) volume x] at this
  exact this

end

end FracLap
