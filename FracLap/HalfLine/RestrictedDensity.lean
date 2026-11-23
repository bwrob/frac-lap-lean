/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.HalfLine.RestrictedDirichlet
public import FracLap.WholeLine.GagliardoMultiplier
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLap.HalfLine.RestrictedDensity

Density of Schwartz functions vanishing near `(-∞, 0]` in the exterior-Dirichlet space
`H^(α / 2)_0(0, ∞)`, combining the whole-line density theorem, continuity of translation in the
Gagliardo norm, and the multiplier estimate for the smooth cutoff:
- `gagliardoN2`, `gagliardoN2_add_le`: the squared norm `‖f‖² + E_α(f)` and its quasi-triangle
  inequality.
- `gagliardoN2_translate_sub`, `exists_translate_close`: `‖τ_{-s} f - f‖_{H^(α/2)} → 0` as
  `s → 0⁺`, by dominated convergence on the Fourier side.
- `exists_mulL2C`, `exists_gagliardoN2_mul_le`: multiplication by a bounded Lipschitz function.
- `exists_schwartz_close_restricted`: every element of `RestrictedGagliardoSpace α` is
  approximated by a real Schwartz function vanishing on some half-line `(-∞, δ]`, `δ > 0`.
-/

namespace FracLap

open Complex Filter FourierTransform MeasureTheory Real Set Topology
open scoped ENNReal NNReal ComplexInnerProductSpace SchwartzMap

@[expose] public section

/-- Quasi-triangle inequality for squared moduli in `[0, ∞]`. -/
theorem enorm_sq_add_le_two (u v : ℂ) :
    ‖u + v‖ₑ ^ (2 : ℝ) ≤ 2 * ‖u‖ₑ ^ (2 : ℝ) + 2 * ‖v‖ₑ ^ (2 : ℝ) := by
  rw [enorm_rpow_two_eq_ofReal, enorm_rpow_two_eq_ofReal, enorm_rpow_two_eq_ofReal]
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (norm_add_sq_le_two _ _)

/-- The `H^(α / 2)` norm squared of a complex `L²` function: `‖f‖² + E_α(f)`. -/
noncomputable def gagliardoN2 (α : ℝ) (f : L2C) : ℝ≥0∞ :=
  ‖f‖ₑ ^ (2 : ℝ) + gagliardoEnergyC α f

/-- Quasi-triangle inequality for the `H^(α / 2)` norm squared. -/
theorem gagliardoN2_add_le (α : ℝ) (a b : L2C) :
    gagliardoN2 α (a + b) ≤ 2 * gagliardoN2 α a + 2 * gagliardoN2 α b := by
  have ham : Measurable (a : ℝ → ℂ) := (Lp.stronglyMeasurable a).measurable
  have hbm : Measurable (b : ℝ → ℂ) := (Lp.stronglyMeasurable b).measurable
  have hnorm : ‖a + b‖ₑ ^ (2 : ℝ) ≤ 2 * ‖a‖ₑ ^ (2 : ℝ) + 2 * ‖b‖ₑ ^ (2 : ℝ) := by
    calc ‖a + b‖ₑ ^ (2 : ℝ) = ∫⁻ x, ‖((a + b : L2C) : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) :=
          (lintegral_enorm_sq_eq_general _).symm
      _ ≤ ∫⁻ x, (2 * ‖(a : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) + 2 * ‖(b : ℝ → ℂ) x‖ₑ ^ (2 : ℝ)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [Lp.coeFn_add a b] with x hx
          have hx' : ((a + b : L2C) : ℝ → ℂ) x = (a : ℝ → ℂ) x + (b : ℝ → ℂ) x := hx
          rw [hx']
          exact enorm_sq_add_le_two _ _
      _ = 2 * ‖a‖ₑ ^ (2 : ℝ) + 2 * ‖b‖ₑ ^ (2 : ℝ) := by
          rw [lintegral_add_left ((ham.eNorm.pow_const _).const_mul _),
            lintegral_const_mul _ (ham.eNorm.pow_const _),
            lintegral_const_mul _ (hbm.eNorm.pow_const _),
            lintegral_enorm_sq_eq_general, lintegral_enorm_sq_eq_general]
  have hE : gagliardoEnergyC α (a + b) ≤ 2 * gagliardoEnergyC α a + 2 * gagliardoEnergyC α b := by
    unfold gagliardoEnergyC
    have hwa : Measurable fun p : ℝ × ℝ => gagliardoWeight α p *
        ‖(a : ℝ → ℂ) p.1 - (a : ℝ → ℂ) p.2‖ₑ ^ (2 : ℝ) :=
      (measurable_gagliardoWeight α).mul
        ((((ham.comp measurable_fst).sub (ham.comp measurable_snd)).eNorm).pow_const _)
    have hwb : Measurable fun p : ℝ × ℝ => gagliardoWeight α p *
        ‖(b : ℝ → ℂ) p.1 - (b : ℝ → ℂ) p.2‖ₑ ^ (2 : ℝ) :=
      (measurable_gagliardoWeight α).mul
        ((((hbm.comp measurable_fst).sub (hbm.comp measurable_snd)).eNorm).pow_const _)
    calc ∫⁻ p : ℝ × ℝ, gagliardoWeight α p * ‖((a + b : L2C) : ℝ → ℂ) p.1 -
          ((a + b : L2C) : ℝ → ℂ) p.2‖ₑ ^ (2 : ℝ) ∂((volume : Measure ℝ).prod volume)
        ≤ ∫⁻ p : ℝ × ℝ, (2 * (gagliardoWeight α p *
            ‖(a : ℝ → ℂ) p.1 - (a : ℝ → ℂ) p.2‖ₑ ^ (2 : ℝ)) +
          2 * (gagliardoWeight α p * ‖(b : ℝ → ℂ) p.1 - (b : ℝ → ℂ) p.2‖ₑ ^ (2 : ℝ)))
            ∂((volume : Measure ℝ).prod volume) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_prod_fst (Lp.coeFn_add a b), ae_prod_snd (Lp.coeFn_add a b)]
            with p h1 h2
          have h1' : ((a + b : L2C) : ℝ → ℂ) p.1 = (a : ℝ → ℂ) p.1 + (b : ℝ → ℂ) p.1 := h1
          have h2' : ((a + b : L2C) : ℝ → ℂ) p.2 = (a : ℝ → ℂ) p.2 + (b : ℝ → ℂ) p.2 := h2
          rw [h1', h2']
          have hsq := enorm_sq_add_le_two ((a : ℝ → ℂ) p.1 - (a : ℝ → ℂ) p.2)
            ((b : ℝ → ℂ) p.1 - (b : ℝ → ℂ) p.2)
          have hrw : ((a : ℝ → ℂ) p.1 + (b : ℝ → ℂ) p.1) - ((a : ℝ → ℂ) p.2 + (b : ℝ → ℂ) p.2) =
              ((a : ℝ → ℂ) p.1 - (a : ℝ → ℂ) p.2) + ((b : ℝ → ℂ) p.1 - (b : ℝ → ℂ) p.2) := by ring
          rw [hrw]
          calc gagliardoWeight α p * _ ≤ gagliardoWeight α p * (2 * _ + 2 * _) := by gcongr
            _ = _ := by ring
      _ = 2 * ∫⁻ p : ℝ × ℝ, gagliardoWeight α p * ‖(a : ℝ → ℂ) p.1 - (a : ℝ → ℂ) p.2‖ₑ ^ (2 : ℝ)
            ∂((volume : Measure ℝ).prod volume) +
          2 * ∫⁻ p : ℝ × ℝ, gagliardoWeight α p * ‖(b : ℝ → ℂ) p.1 - (b : ℝ → ℂ) p.2‖ₑ ^ (2 : ℝ)
            ∂((volume : Measure ℝ).prod volume) := by
          rw [lintegral_add_left (hwa.const_mul _), lintegral_const_mul _ hwa,
            lintegral_const_mul _ hwb]
  unfold gagliardoN2
  calc ‖a + b‖ₑ ^ (2 : ℝ) + gagliardoEnergyC α (a + b)
      ≤ (2 * ‖a‖ₑ ^ (2 : ℝ) + 2 * ‖b‖ₑ ^ (2 : ℝ)) +
        (2 * gagliardoEnergyC α a + 2 * gagliardoEnergyC α b) := add_le_add hnorm hE
    _ = _ := by ring

/-- The `H^(α / 2)` norm squared of `τ_h f - f` as a spectral integral. -/
theorem gagliardoN2_translate_sub (α : ℝ) (h : ℝ) (f : L2C) :
    gagliardoN2 α (translateL2 h f - f) =
      ∫⁻ ξ, ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ)
        ∂gagliardoSpectralMeasure α := by
  set g : L2C := translateL2 h f - f with hg
  have hνac : gagliardoSpectralMeasure α ≪ (volume : Measure ℝ) :=
    withDensity_absolutelyContinuous _ _
  have hF : 𝓕 g = multOpCLM (translatePhase h) (𝓕 f) - 𝓕 f := by
    have hmap : (𝓕 g : L2C) = 𝓕 (translateL2 h f) - 𝓕 f :=
      (Lp.fourierTransformₗᵢ ℝ ℂ).map_sub (translateL2 h f) f
    rw [hmap, fourier_translateL2]
  have hR : ∀ᵐ ξ : ℝ ∂volume, (𝓕 g : L2C) ξ =
      (((𝐞 (h * ξ) : Circle) : ℂ) - 1) * (𝓕 f : L2C) ξ := by
    filter_upwards [Lp.coeFn_sub (multOpCLM (translatePhase h) (𝓕 f)) (𝓕 f),
      Lp.coeFn_lpSMul (r := 2) (translatePhase h) (𝓕 f), coeFn_translatePhase h]
      with ξ h1 h2 h3
    rw [hF]
    have h1' : ((multOpCLM (translatePhase h) (𝓕 f) - 𝓕 f : L2C) : ℝ → ℂ) ξ =
        (multOpCLM (translatePhase h) (𝓕 f) : ℝ → ℂ) ξ - (𝓕 f : L2C) ξ := h1
    rw [h1', multOpCLM_apply]
    simp only [smul_eq_mul, Pi.mul_apply] at h2
    rw [h2, h3]
    ring
  unfold gagliardoN2
  rw [norm_sq_add_energy_eq α g]
  refine lintegral_congr_ae ?_
  filter_upwards [hνac.ae_le hR] with ξ hξ
  rw [hξ, eNorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

/-- **Continuity of translation in the `H^(α / 2)` norm**: for `f ∈ L²` of finite Gagliardo energy,
`‖τ_{-s} f - f‖²_{H^(α/2)}` is arbitrarily small for small `s > 0`. -/
theorem exists_translate_close {α : ℝ} (f : L2C)
    (hE : gagliardoEnergyC α f < ∞) {η : ℝ} (hη : 0 < η) :
    ∃ s : ℝ, 0 < s ∧ gagliardoN2 α (translateL2 (-s) f - f) < ENNReal.ofReal η := by
  set ν := gagliardoSpectralMeasure α with hν
  have hFf : Measurable ((𝓕 f : L2C) : ℝ → ℂ) := (Lp.stronglyMeasurable (𝓕 f : L2C)).measurable
  set bound : ℝ → ℝ≥0∞ := fun ξ => 4 * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) with hbound
  have hfinF : ∫⁻ ξ, ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) ∂ν < ∞ := by
    rw [← norm_sq_add_energy_eq α f]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by
      rw [Lp.eNorm_def]; exact Lp.eLpNorm_ne_top f), hE⟩
  have hphase : ∀ ξ, Continuous fun h : ℝ => ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ) := by
    intro ξ
    have hc : Continuous fun h : ℝ => ((𝐞 (h * ξ) : Circle) : ℂ) :=
      continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp (continuous_id.mul continuous_const))
    exact (ENNReal.continuous_rpow_const.comp (hc.sub continuous_const).eNorm)
  have hbd2 : ∀ h ξ : ℝ, ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ) ≤ 4 := by
    intro h ξ
    rw [enorm_rpow_two_eq_ofReal]
    have h2 : ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ ≤ 2 := by
      calc ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ ≤ ‖((𝐞 (h * ξ) : Circle) : ℂ)‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
        _ = 2 := by rw [Circle.norm_coe]; norm_num
    have : ENNReal.ofReal (‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ ^ 2) ≤ ENNReal.ofReal 4 :=
      ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg (((𝐞 (h * ξ) : Circle) : ℂ) - 1)])
    simpa using this
  have hlim : Tendsto (fun h : ℝ => ∫⁻ ξ, ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ) *
      ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) ∂ν) (𝓝 0) (𝓝 0) := by
    have key := tendsto_lintegral_filter_of_dominated_convergence (μ := ν) (l := 𝓝 (0 : ℝ))
      (F := fun (h : ℝ) ξ => ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ) *
        ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ)) (f := fun _ => 0) bound
      (Filter.Eventually.of_forall fun h => by
        have hc : Continuous fun ξ : ℝ => ((𝐞 (h * ξ) : Circle) : ℂ) :=
          continuous_subtype_val.comp
            (Real.continuous_fourierChar.comp (continuous_const.mul continuous_id))
        exact ((hc.sub continuous_const).eNorm.measurable.pow_const _).mul
          (hFf.eNorm.pow_const _))
      (Filter.Eventually.of_forall fun h => Filter.Eventually.of_forall fun ξ => by
        simp only [hbound]
        exact mul_le_mul' (hbd2 h ξ) le_rfl)
      (by
        simp only [hbound]
        rw [lintegral_const_mul _ (hFf.eNorm.pow_const _)]
        exact ENNReal.mul_ne_top (by norm_num) hfinF.ne)
      (Filter.Eventually.of_forall fun ξ => by
        have hfin : ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) ≠ ∞ :=
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) eNorm_ne_top).ne
        have h0 : Tendsto (fun h : ℝ => ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ))
            (𝓝 0) (𝓝 0) := by
          have := (hphase ξ).tendsto 0
          simpa using this
        have := ENNReal.Tendsto.mul_const h0 (Or.inr hfin)
        simpa using this)
    simpa using key
  have hev : ∀ᶠ h in 𝓝 (0 : ℝ), ∫⁻ ξ, ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ) *
      ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) ∂ν < ENNReal.ofReal η :=
    (tendsto_order.1 hlim).2 _ (ENNReal.ofReal_pos.2 hη)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ / 2, by positivity, ?_⟩
  rw [gagliardoN2_translate_sub]
  exact hball (by rw [Real.dist_eq]; simp [abs_of_pos (by positivity : 0 < δ / 2)]; linarith)

/-- Multiplication of an `L²(ℝ; ℂ)` function by a bounded measurable real function. -/
theorem exists_mulL2C {θ : ℝ → ℝ} (hθ : Measurable θ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, |θ x| ≤ B) (f : L2C) :
    ∃ g : L2C, ∀ᵐ x : ℝ ∂volume, (g : ℝ → ℂ) x = (θ x : ℂ) * (f : ℝ → ℂ) x := by
  have hm : Measurable fun x : ℝ => (θ x : ℂ) := Complex.measurable_ofReal.comp hθ
  have hbdd : ∀ x, ‖(θ x : ℂ)‖ ≤ B := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hB x
  refine ⟨multOpCLM (toLpTop (m := fun x : ℝ => (θ x : ℂ)) hm.aestronglyMeasurable hB0 hbdd) f, ?_⟩
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (toLpTop (m := fun x : ℝ => (θ x : ℂ))
      hm.aestronglyMeasurable hB0 hbdd) f,
    coeFn_toLpTop (m := fun x : ℝ => (θ x : ℂ)) hm.aestronglyMeasurable hB0 hbdd] with x h1 h2
  rw [multOpCLM_apply]
  simp only [smul_eq_mul, Pi.mul_apply] at h1
  rw [h1, h2]

/-- Multiplication by a bounded function contracts the squared `L²` norm up to `B²`. -/
theorem enorm_sq_mul_le {θ : ℝ → ℝ} {B : ℝ} (hB : ∀ x, |θ x| ≤ B) (f g : L2C)
    (hfg : ∀ᵐ x : ℝ ∂volume, (g : ℝ → ℂ) x = (θ x : ℂ) * (f : ℝ → ℂ) x) :
    ‖g‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (B ^ 2) * ‖f‖ₑ ^ (2 : ℝ) := by
  have hfm : Measurable (f : ℝ → ℂ) := (Lp.stronglyMeasurable f).measurable
  rw [← lintegral_enorm_sq_eq_general, ← lintegral_enorm_sq_eq_general,
    ← lintegral_const_mul _ (hfm.eNorm.pow_const _)]
  refine lintegral_mono_ae ?_
  filter_upwards [hfg] with x hx
  rw [hx, eNorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  refine mul_le_mul' ?_ le_rfl
  rw [enorm_rpow_two_eq_ofReal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2

/-- **Multiplier bound for the `H^(α / 2)` norm squared**: for bounded Lipschitz `θ` there is
`C ≥ 0` with `N²(θ f) ≤ C N²(f)`. -/
theorem exists_gagliardoN2_mul_le {α : ℝ} (hα : FractionalExponent α) {θ : ℝ → ℝ}
    (hθ : Measurable θ) {B L : ℝ} (hB : ∀ x, |θ x| ≤ B)
    (hL : ∀ x y, |θ x - θ y| ≤ L * |x - y|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : L2C,
      (∀ᵐ x : ℝ ∂volume, (g : ℝ → ℂ) x = (θ x : ℂ) * (f : ℝ → ℂ) x) →
        gagliardoN2 α g ≤ ENNReal.ofReal C * gagliardoN2 α f := by
  set M := max (L ^ 2) (4 * B ^ 2) with hM
  have hM0 : 0 ≤ M := le_trans (sq_nonneg L) (le_max_left _ _)
  set K0r := (∫⁻ h, gagliardoKernel α h).toReal with hK0r
  have hK0 : (∫⁻ h, gagliardoKernel α h) = ENNReal.ofReal K0r :=
    (ENNReal.ofReal_toReal (lintegral_gagliardoKernel_lt_top hα).ne).symm
  have hK0r : 0 ≤ K0r := ENNReal.toReal_nonneg
  refine ⟨3 * B ^ 2 + 2 * M * K0r, by positivity, fun f g hfg => ?_⟩
  have h1 := enorm_sq_mul_le hB f g hfg
  have h2 := gagliardoEnergyC_mul_le hα hθ hB hL f g hfg
  rw [hK0] at h2
  unfold gagliardoN2
  set C := 3 * B ^ 2 + 2 * M * K0r with hC
  calc ‖g‖ₑ ^ (2 : ℝ) + gagliardoEnergyC α g
      ≤ ENNReal.ofReal (B ^ 2) * ‖f‖ₑ ^ (2 : ℝ) +
        (ENNReal.ofReal (2 * B ^ 2) * gagliardoEnergyC α f +
          ENNReal.ofReal (2 * M) * ENNReal.ofReal K0r * ‖f‖ₑ ^ (2 : ℝ)) := add_le_add h1 h2
    _ = (ENNReal.ofReal (B ^ 2) + ENNReal.ofReal (2 * M) * ENNReal.ofReal K0r) * ‖f‖ₑ ^ (2 : ℝ) +
        ENNReal.ofReal (2 * B ^ 2) * gagliardoEnergyC α f := by ring
    _ ≤ ENNReal.ofReal C * ‖f‖ₑ ^ (2 : ℝ) + ENNReal.ofReal C * gagliardoEnergyC α f := by
        refine add_le_add (mul_le_mul' ?_ le_rfl) (mul_le_mul' ?_ le_rfl)
        · rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg B])
        · exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg B, mul_nonneg hM0 hK0r])
    _ = ENNReal.ofReal C * (‖f‖ₑ ^ (2 : ℝ) + gagliardoEnergyC α f) := by ring

/-- **Density in the exterior-Dirichlet space `H^(α / 2)_0(0, ∞)`**: every `u` in the restricted
Gagliardo space is approximated, in the Gagliardo norm, by a real Schwartz function `ψ` that
vanishes on a half-line `(-∞, δ]` with `δ > 0`. -/
theorem exists_schwartz_close_restricted {α : ℝ} (hα : FractionalExponent α)
    (u : RestrictedGagliardoSpace α) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ψ : 𝓢(ℝ, ℝ)) (δ : ℝ), 0 < δ ∧ (∀ x, x ≤ δ → ψ x = 0) ∧
      ∃ hψ : gagliardoEnergyR α (ψ.toLp 2 volume : L2R) < ∞,
        ‖gagliardoMk (ψ.toLp 2 volume : L2R) hψ - (u : GagliardoSpace α)‖ < ε := by
  set g0 : L2R := gagliardoL2Part α (u : GagliardoSpace α) with hg0
  have hu0 : ∀ᵐ x : ℝ ∂volume, x ≤ 0 → (g0 : ℝ → ℝ) x = 0 := u.2
  have hu := ofReal_norm_sq_gagliardoSpace α (u : GagliardoSpace α)
  have hEg0 : gagliardoEnergyR α g0 < ∞ :=
    lt_of_le_of_lt le_add_self (hu ▸ ENNReal.ofReal_lt_top)
  set f : L2C := ofRealL2 g0 with hf
  have hEf : gagliardoEnergyC α f < ∞ := by
    rw [hf, gagliardoEnergyC_ofRealL2]; exact hEg0
  have hN2f : gagliardoN2 α f < ∞ :=
    ENNReal.add_lt_top.2 ⟨ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by
      rw [Lp.eNorm_def]; exact Lp.eLpNorm_ne_top f), hEf⟩
  -- Step 1: translate to the right
  obtain ⟨s, hs, hsclose⟩ := exists_translate_close f hEf (η := ε ^ 2 / 4) (by positivity)
  set fs : L2C := translateL2 (-s) f with hfs
  have hfs0 : ∀ᵐ x : ℝ ∂volume, x ≤ s → (fs : ℝ → ℂ) x = 0 := by
    filter_upwards [coeFn_translateL2 (-s) f,
      (measurePreserving_add_right (volume : Measure ℝ) (-s)).quasiMeasurePreserving.ae
        (coeFn_ofRealL2 g0),
      (measurePreserving_add_right (volume : Measure ℝ) (-s)).quasiMeasurePreserving.ae hu0]
      with x h1 h2 h3 hx
    have h1' : (fs : ℝ → ℂ) x = (f : ℝ → ℂ) (x + -s) := h1
    have h2' : (f : ℝ → ℂ) (x + -s) = (((g0 : ℝ → ℝ) (x + -s) : ℝ) : ℂ) := h2
    rw [h1', h2', h3 (by linarith)]
    simp
  have hN2fs : gagliardoN2 α fs < ∞ := by
    have h := gagliardoN2_add_le α (fs - f) f
    rw [sub_add_cancel] at h
    refine lt_of_le_of_lt h ?_
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) (lt_trans hsclose
      ENNReal.ofReal_lt_top), ENNReal.mul_lt_top (by simp) hN2f⟩
  have hEfs : gagliardoEnergyC α fs < ∞ := lt_of_le_of_lt le_add_self hN2fs
  -- Step 2: the cutoff
  set θ : ℝ → ℝ := cutoffStep s with hθ
  have hθm : Measurable θ := (contDiff_cutoffStep hs).continuous.measurable
  obtain ⟨L, hL⟩ := exists_lipschitz_cutoffStep hs
  obtain ⟨C, hC0, hCmul⟩ := exists_gagliardoN2_mul_le hα hθm (B := 1) (abs_cutoffStep_le s) hL
  -- Step 3: Schwartz approximation of the shifted function
  obtain ⟨φc, hφc⟩ := exists_schwartz_close_complex hα fs hEfs
    (ε := ε ^ 2 / 4 / (C + 1)) (by positivity)
  obtain ⟨g, hg⟩ := exists_mulL2C hθm zero_le_one (abs_cutoffStep_le s) (φc.toLp 2 volume : L2C)
  have hθfs : ∀ᵐ x : ℝ ∂volume, (θ x : ℂ) * (fs : ℝ → ℂ) x = (fs : ℝ → ℂ) x := by
    filter_upwards [hfs0] with x hx
    rcases le_or_gt s x with h | h
    · rw [hθ, cutoffStep_eq_one hs h]; simp
    · rw [hx h.le]; simp
  have hdiff : ∀ᵐ x : ℝ ∂volume, ((g - fs : L2C) : ℝ → ℂ) x =
      (θ x : ℂ) * (((φc.toLp 2 volume : L2C) - fs : L2C) : ℝ → ℂ) x := by
    filter_upwards [hg, Lp.coeFn_sub g fs, Lp.coeFn_sub (φc.toLp 2 volume : L2C) fs, hθfs]
      with x h1 h2 h3 h4
    have h2' : ((g - fs : L2C) : ℝ → ℂ) x = (g : ℝ → ℂ) x - (fs : ℝ → ℂ) x := h2
    have h3' : (((φc.toLp 2 volume : L2C) - fs : L2C) : ℝ → ℂ) x =
        ((φc.toLp 2 volume : L2C) : ℝ → ℂ) x - (fs : ℝ → ℂ) x := h3
    rw [h2', h3', h1, mul_sub, h4]
  have hN2a : gagliardoN2 α (g - fs) ≤
      ENNReal.ofReal C * gagliardoN2 α ((φc.toLp 2 volume : L2C) - fs) := hCmul _ _ hdiff
  have hN2a' : gagliardoN2 α (g - fs) ≤ ENNReal.ofReal (ε ^ 2 / 4) := by
    refine hN2a.trans ?_
    calc ENNReal.ofReal C * gagliardoN2 α ((φc.toLp 2 volume : L2C) - fs)
        ≤ ENNReal.ofReal C * ENNReal.ofReal (ε ^ 2 / 4 / (C + 1)) := by
          gcongr; exact hφc.le
      _ = ENNReal.ofReal (C * (ε ^ 2 / 4 / (C + 1))) := (ENNReal.ofReal_mul hC0).symm
      _ ≤ ENNReal.ofReal (ε ^ 2 / 4) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg ε]
  have htot : gagliardoN2 α (g - f) < ENNReal.ofReal (ε ^ 2) := by
    have h := gagliardoN2_add_le α (g - fs) (fs - f)
    rw [sub_add_sub_cancel] at h
    refine lt_of_le_of_lt h ?_
    have hq : (4 : ℝ≥0∞) * ENNReal.ofReal (ε ^ 2 / 4) = ENNReal.ofReal (ε ^ 2) := by
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    rw [← hq]
    calc 2 * gagliardoN2 α (g - fs) + 2 * gagliardoN2 α (fs - f)
        < 2 * ENNReal.ofReal (ε ^ 2 / 4) + 2 * ENNReal.ofReal (ε ^ 2 / 4) := by
          have hle : 2 * gagliardoN2 α (g - fs) ≤ 2 * ENNReal.ofReal (ε ^ 2 / 4) :=
            mul_le_mul' le_rfl hN2a'
          refine ENNReal.add_lt_add_of_le_of_lt ?_ hle ?_
          · exact (lt_of_le_of_lt hle (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top)).ne
          · have h2 := (ENNReal.mul_lt_mul_left (by norm_num : (2 : ℝ≥0∞) ≠ 0)
              (by norm_num : (2 : ℝ≥0∞) ≠ ∞)) hsclose
            rwa [mul_comm _ (2 : ℝ≥0∞), mul_comm _ (2 : ℝ≥0∞)] at h2
      _ = 4 * ENNReal.ofReal (ε ^ 2 / 4) := by ring
  -- Step 4: the real Schwartz function `ψ = θ · Re φ`
  have hTG : θ.HasTemperateGrowth := hasTemperateGrowth_cutoffStep hs
  set ψ0 : 𝓢(ℝ, ℝ) := SchwartzMap.postcompCLM Complex.reCLM φc with hψ0
  set ψ : 𝓢(ℝ, ℝ) := SchwartzMap.smulLeftCLM ℝ θ ψ0 with hψ
  have hψx : ∀ x, ψ x = θ x * (φc x).re := fun x => by
    rw [hψ, SchwartzMap.smulLeftCLM_apply_apply hTG]
    simp [hψ0]
  have hψL : (ψ.toLp 2 volume : L2R) = reL2 g := by
    rw [Lp.ext_iff]
    filter_upwards [ψ.coeFn_toLp 2 volume, coeFn_reL2 g, hg, φc.coeFn_toLp 2 volume]
      with x h1 h2 h3 h4
    have h1' : (ψ.toLp 2 volume : L2R) x = ψ x := h1
    have h4' : ((φc.toLp 2 volume : L2C) : ℝ → ℂ) x = φc x := h4
    rw [h1', h2, h3, h4', hψx, Complex.re_ofReal_mul]
  have hN2g : gagliardoN2 α g < ∞ := by
    have h := gagliardoN2_add_le α (g - fs) fs
    rw [sub_add_cancel] at h
    refine lt_of_le_of_lt h ?_
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) (lt_of_le_of_lt hN2a'
      ENNReal.ofReal_lt_top), ENNReal.mul_lt_top (by simp) hN2fs⟩
  have hEψ : gagliardoEnergyR α (ψ.toLp 2 volume : L2R) < ∞ := by
    rw [hψL]
    exact lt_of_le_of_lt (gagliardoEnergyR_reL2_le α g) (lt_of_le_of_lt le_add_self hN2g)
  refine ⟨ψ, s / 2, by positivity, fun x hx => ?_, hEψ, ?_⟩
  · rw [hψx, hθ, cutoffStep_eq_zero hs hx, zero_mul]
  set v : GagliardoSpace α := gagliardoMk (ψ.toLp 2 volume : L2R) hEψ with hv
  set D : L2C := g - f with hD
  have hL2 : gagliardoL2Part α (v - (u : GagliardoSpace α)) = reL2 D := by
    rw [map_sub, hD, map_sub, hf, reL2_ofRealL2, ← hψL]
    rfl
  have hnorm := ofReal_norm_sq_gagliardoSpace α (v - (u : GagliardoSpace α))
  rw [hL2] at hnorm
  have hlt : ENNReal.ofReal (‖v - (u : GagliardoSpace α)‖ ^ 2) < ENNReal.ofReal (ε ^ 2) := by
    rw [hnorm]
    calc ENNReal.ofReal (‖reL2 D‖ ^ 2) + gagliardoEnergyR α (reL2 D)
        ≤ ‖D‖ₑ ^ (2 : ℝ) + gagliardoEnergyC α D := by
          gcongr
          · rw [← enorm_rpow_two_eq_ofReal]
            exact enorm_sq_reL2_le D
          · exact gagliardoEnergyR_reL2_le α D
      _ < ENNReal.ofReal (ε ^ 2) := htot
  have := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hlt
  exact lt_of_pow_lt_pow_left₀ 2 hε.le this

end

end FracLap
