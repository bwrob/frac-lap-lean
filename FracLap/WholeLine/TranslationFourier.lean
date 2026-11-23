/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.FourierSemigroup
import Mathlib.Tactic.FunProp

/-!
# FracLap.WholeLine.TranslationFourier

Translations on `L²(ℝ; ℂ)` and their Fourier-side description, the first ingredient in the
Fourier characterization of the Gagliardo seminorm (Di Nezza–Palatucci–Valdinoci,
*Hitchhiker's guide*, Prop. 3.4):
- `fourier_comp_add_right_real`: `𝓕 (f (· + h)) ξ = 𝐞 (h ξ) 𝓕 f ξ` for every `f : ℝ → ℂ`.
- `translateL2`, `coeFn_translateL2`: the translation isometry `f ↦ f (· + h)` on `L²(ℝ; ℂ)`.
- `translatePhase`, `coeFn_translatePhase`: the phase symbol `ξ ↦ 𝐞 (h ξ)` as an `L^∞` element.
- `fourier_translateL2`: `𝓕 (translateL2 h f) = translatePhase h · 𝓕 f` in `L²(ℝ; ℂ)`.
- `lintegral_enorm_sq_eq`: squared `L²` norm as a lintegral.
- `lintegral_enorm_sq_translate_sub`: `∫ ‖f(y + h) - f(y)‖² dy = ∫ ‖𝐞(h ξ) - 1‖² ‖𝓕 f(ξ)‖² dξ`.
-/

namespace FracLap

open Complex Filter FourierTransform MeasureTheory Real Set Topology
open scoped ENNReal NNReal ComplexInnerProductSpace SchwartzMap

@[expose] public section

/-- **Fourier transform of a translate on `ℝ`**: `𝓕 (f (· + h)) ξ = 𝐞 (h ξ) 𝓕 f ξ`. -/
theorem fourier_comp_add_right_real (f : ℝ → ℂ) (h ξ : ℝ) :
    𝓕 (fun x : ℝ => f (x + h)) ξ = ((𝐞 (h * ξ) : Circle) : ℂ) * 𝓕 f ξ := by
  simp only [Real.fourier_real_eq]
  calc ∫ v : ℝ, 𝐞 (-(v * ξ)) • f (v + h)
      = ∫ u : ℝ, 𝐞 (-((u - h) * ξ)) • f u := by
        rw [← integral_add_right_eq_self (fun u : ℝ => 𝐞 (-((u - h) * ξ)) • f u) h]
        simp only [add_sub_cancel_right]
    _ = ∫ u : ℝ, ((𝐞 (h * ξ) : Circle) : ℂ) * (𝐞 (-(u * ξ)) • f u) := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        dsimp only
        rw [show -((u - h) * ξ) = h * ξ + -(u * ξ) by ring, AddChar.map_add_eq_mul,
          mul_smul, Circle.smul_def, smul_eq_mul]
    _ = ((𝐞 (h * ξ) : Circle) : ℂ) * ∫ u : ℝ, 𝐞 (-(u * ξ)) • f u := integral_const_mul _ _


/-- Translation isometry `f ↦ (x ↦ f(x + h))` on `L²(ℝ; ℂ)`. -/
noncomputable def translateL2 (h : ℝ) : L2C →ₗᵢ[ℝ] L2C :=
  Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := ℂ) (p := 2)
    (μ := (volume : Measure ℝ)) (μb := (volume : Measure ℝ))
    (fun x : ℝ => x + h) (measurePreserving_add_right (volume : Measure ℝ) h)

/-- Pointwise a.e. characterization of `translateL2 h f`. -/
theorem coeFn_translateL2 (h : ℝ) (f : L2C) :
    (translateL2 h f : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => (f : ℝ → ℂ) (x + h) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right (volume : Measure ℝ) h)

/-- The phase symbol `ξ ↦ 𝐞 (h ξ)` as an element of `L^∞(ℝ; ℂ)`. -/
noncomputable def translatePhase (h : ℝ) : Lp (α := ℝ) ℂ ∞ volume :=
  toLpTop (m := fun ξ : ℝ => ((𝐞 (h * ξ) : Circle) : ℂ))
    (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    zero_le_one fun _ => (Circle.norm_coe _).le

/-- A.e. values of the phase multiplier. -/
theorem coeFn_translatePhase (h : ℝ) :
    (translatePhase h : ℝ → ℂ) =ᵐ[volume] fun ξ : ℝ => ((𝐞 (h * ξ) : Circle) : ℂ) :=
  coeFn_toLpTop _ _ _

/-- **Fourier transform of a translate on `L²(ℝ; ℂ)`**: translation by `h` is conjugated by `𝓕`
into multiplication by the phase `ξ ↦ 𝐞 (h ξ)`. -/
theorem fourier_translateL2 (h : ℝ) (f : L2C) :
    𝓕 (translateL2 h f) = multOpCLM (translatePhase h) (𝓕 f) := by
  let p : L2C → Prop := fun g => 𝓕 (translateL2 h g) = multOpCLM (translatePhase h) (𝓕 g)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact ((Lp.fourierTransformₗᵢ ℝ ℂ).continuous).comp (translateL2 h).continuous
    · exact (multOpCLM (translatePhase h)).continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous
  · intro φ
    dsimp only [p]
    have hg : (fun x : ℝ => x + h).HasTemperateGrowth := by fun_prop
    have hanti : AntilipschitzWith 1 (fun x : ℝ => x + h) :=
      (isometry_add_right h).antilipschitzWith
    let ψ : 𝓢(ℝ, ℂ) := SchwartzMap.compCLMOfAntilipschitz ℂ hg hanti φ
    have hψ : ∀ x, ψ x = φ (x + h) := fun x => rfl
    have htoLp_eq : (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) φ = φ.toLp 2 := rfl
    have htrans : translateL2 h (φ.toLp 2) = ψ.toLp 2 := by
      rw [Lp.ext_iff]
      filter_upwards [coeFn_translateL2 h (φ.toLp 2),
        (measurePreserving_add_right (volume : Measure ℝ) h).quasiMeasurePreserving.ae
          (φ.coeFn_toLp 2 volume), ψ.coeFn_toLp 2 volume] with x h1 h2 h3
      have h1' : (translateL2 h (φ.toLp 2) : ℝ → ℂ) x = (φ.toLp 2 : ℝ → ℂ) (x + h) := h1
      have h2' : (φ.toLp 2 : ℝ → ℂ) (x + h) = φ (x + h) := h2
      have h3' : (ψ.toLp 2 : ℝ → ℂ) x = ψ x := h3
      rw [h1', h2', h3', hψ]
    have hfour : ∀ ξ, 𝓕 ψ ξ = ((𝐞 (h * ξ) : Circle) : ℂ) * 𝓕 φ ξ := by
      intro ξ
      rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
      exact fourier_comp_add_right_real (⇑φ) h ξ
    rw [htoLp_eq, htrans, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq,
      multOpCLM_apply]
    rw [Lp.ext_iff]
    filter_upwards [(𝓕 ψ).coeFn_toLp 2 volume,
      Lp.coeFn_lpSMul (r := 2) (translatePhase h) ((𝓕 φ).toLp 2),
      (𝓕 φ).coeFn_toLp 2 volume, coeFn_translatePhase h] with ξ h1 h2 h3 h4
    have h1' : ((𝓕 ψ).toLp 2 : ℝ → ℂ) ξ = 𝓕 ψ ξ := h1
    have h3' : ((𝓕 φ).toLp 2 : ℝ → ℂ) ξ = 𝓕 φ ξ := h3
    simp only [smul_eq_mul, Pi.mul_apply] at h2
    change ((𝓕 ψ).toLp 2 : ℝ → ℂ) ξ = ((translatePhase h • (𝓕 φ).toLp 2 : L2C) : ℝ → ℂ) ξ
    rw [h1', h2, h3', h4, hfour]


/-- For `g ∈ L²`, `∫ ‖g‖ₑ² = ‖g‖ₑ²` (squared `L²` norm as a lintegral). -/
theorem lintegral_enorm_sq_eq {E : Type*} [NormedAddCommGroup E] (g : Lp (α := ℝ) E 2 volume) :
    ∫⁻ x, ‖(g : ℝ → E) x‖ₑ ^ (2 : ℝ) = ‖g‖ₑ ^ (2 : ℝ) := by
  rw [lintegral_rpow_eNorm_eq_rpow_eLpNorm' (μ := (volume : Measure ℝ)) two_pos, Lp.eNorm_def,
    eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top]
  · norm_num
  · exact Lp.aestronglyMeasurable g

/-- **`L²` translation modulus on the Fourier side**: for `f ∈ L²(ℝ; ℂ)`,
`∫ ‖f(y + h) - f(y)‖² dy = ∫ ‖𝐞(h ξ) - 1‖² ‖𝓕 f(ξ)‖² dξ`. -/
theorem lintegral_enorm_sq_translate_sub (h : ℝ) (f : L2C) :
    ∫⁻ y, ‖(f : ℝ → ℂ) (y + h) - (f : ℝ → ℂ) y‖ₑ ^ (2 : ℝ) =
      ∫⁻ ξ, ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) := by
  set g : L2C := translateL2 h f - f with hg
  have hL : ∫⁻ y, ‖(f : ℝ → ℂ) (y + h) - (f : ℝ → ℂ) y‖ₑ ^ (2 : ℝ) =
      ∫⁻ y, ‖(g : ℝ → ℂ) y‖ₑ ^ (2 : ℝ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (translateL2 h f) f, coeFn_translateL2 h f] with y h1 h2
    have h1' : (g : ℝ → ℂ) y = (translateL2 h f : ℝ → ℂ) y - (f : ℝ → ℂ) y := h1
    rw [h1', h2]
  have hnorm : ‖(𝓕 g : L2C)‖ₑ = ‖g‖ₑ := by
    have := (Lp.fourierTransformₗᵢ ℝ ℂ).norm_map g
    rw [← ofReal_norm, ← ofReal_norm]
    exact congrArg ENNReal.ofReal this
  have hF : 𝓕 g = multOpCLM (translatePhase h) (𝓕 f) - 𝓕 f := by
    have hmap : (𝓕 g : L2C) = 𝓕 (translateL2 h f) - 𝓕 f :=
      (Lp.fourierTransformₗᵢ ℝ ℂ).map_sub (translateL2 h f) f
    rw [hmap, fourier_translateL2]
  have hR : ∀ᵐ ξ : ℝ ∂volume, (𝓕 g : L2C) ξ =
      (((𝐞 (h * ξ) : Circle) : ℂ) - 1) * (𝓕 f : L2C) ξ := by
    filter_upwards [Lp.coeFn_sub (multOpCLM (translatePhase h) (𝓕 f)) (𝓕 f),
      Lp.coeFn_lpSMul (r := 2) (translatePhase h) (𝓕 f), coeFn_translatePhase h] with ξ h1 h2 h3
    rw [hF]
    have h1' : ((multOpCLM (translatePhase h) (𝓕 f) - 𝓕 f : L2C) : ℝ → ℂ) ξ =
        (multOpCLM (translatePhase h) (𝓕 f) : ℝ → ℂ) ξ - (𝓕 f : L2C) ξ := h1
    rw [h1', multOpCLM_apply]
    simp only [smul_eq_mul, Pi.mul_apply] at h2
    rw [h2, h3]
    ring
  rw [hL, lintegral_enorm_sq_eq g, ← hnorm, ← lintegral_enorm_sq_eq (𝓕 g : L2C)]
  refine lintegral_congr_ae ?_
  filter_upwards [hR] with ξ hξ
  rw [hξ, eNorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

end

end FracLap
