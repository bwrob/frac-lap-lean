/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Tools.Young
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# FracLap.Tools.BernsteinLp

Bernstein's inequality in `L^p`, `1 ≤ p < ∞` (Danchin; Abidi--Hmidi): there is an absolute constant
`C` such that every Schwartz function `φ` whose Fourier transform vanishes outside `[-R, R]`
satisfies `‖φ′‖_p ≤ C R ‖φ‖_p`.

The proof writes `φ′ = D_R ⋆ φ` with `D_R(x) = R² D₁(R x)` and `𝓕 D₁(η) = 2π i η χ(η)` for a smooth
cutoff `χ ≡ 1` on `[-1, 1]`, and applies Young's inequality with `‖D_R‖₁ = R ‖D₁‖₁`.
-/

namespace FracLap

open Complex Filter FourierTransform MeasureTheory Real Set Topology
open scoped ENNReal NNReal SchwartzMap Convolution

@[expose] public section

/-- Scaling of the Fourier transform: `𝓕 (R² g(R ·)) (ξ) = R 𝓕 g (ξ / R)`. -/
theorem fourier_scale_sq (g : ℝ → ℂ) {R : ℝ} (hR : 0 < R) (ξ : ℝ) :
    𝓕 (fun x : ℝ => ((R ^ 2 : ℝ) : ℂ) * g (R * x)) ξ = (R : ℂ) * 𝓕 g (ξ / R) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  set G : ℝ → ℂ := fun y => (𝐞 (-(y * (ξ / R))) : Circle) • g y with hG
  have h1 : ∀ x : ℝ, (𝐞 (-(x * ξ)) : Circle) • (((R ^ 2 : ℝ) : ℂ) * g (R * x)) =
      ((R ^ 2 : ℝ) : ℂ) * G (R * x) := by
    intro x
    have : (x * ξ) = (R * x) * (ξ / R) := by field_simp
    simp only [hG, Circle.smul_def, smul_eq_mul, this]; ring
  have hint : (∫ x : ℝ, (𝐞 (-(x * ξ)) : Circle) • (((R ^ 2 : ℝ) : ℂ) * g (R * x))) =
      ∫ x : ℝ, ((R ^ 2 : ℝ) : ℂ) * G (R * x) :=
    integral_congr_ae (Filter.Eventually.of_forall h1)
  rw [hint, integral_const_mul, Measure.integral_comp_mul_left G R, abs_of_pos (inv_pos.2 hR),
    Complex.real_smul]
  push_cast
  field_simp

/-- A smooth bump `χ ≡ 1` on `[-1, 1]`, supported in `[-2, 2]`. -/
noncomputable def bernBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

theorem bernBump_one {η : ℝ} (h : |η| ≤ 1) : bernBump η = 1 :=
  bernBump.one_of_mem_closedBall (by simpa [bernBump, Real.dist_eq] using h)

/-- The underlying function of the Schwartz symbol, `η ↦ 2π i η χ(η)`. -/
noncomputable def bernSymbolFun (η : ℝ) : ℂ := (2 * π * I * η : ℂ) * (bernBump η : ℂ)

theorem hasCompactSupport_bernSymbolFun : HasCompactSupport bernSymbolFun := by
  have h : HasCompactSupport (fun η : ℝ => (bernBump η : ℂ)) :=
    bernBump.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  refine h.mono' ?_
  intro η hη
  refine subset_tsupport _ ?_
  intro h0
  apply hη
  simp [bernSymbolFun, h0]

theorem contDiff_bernSymbolFun : ContDiff ℝ (⊤ : ℕ∞) bernSymbolFun := by
  unfold bernSymbolFun
  refine ContDiff.mul (contDiff_const.mul (Complex.ofRealCLM.contDiff)) ?_
  exact Complex.ofRealCLM.contDiff.comp bernBump.contDiff

/-- The Schwartz symbol `η ↦ 2π i η χ(η)`. -/
noncomputable def bernSymbol : 𝓢(ℝ, ℂ) :=
  hasCompactSupport_bernSymbolFun.toSchwartzMap contDiff_bernSymbolFun

theorem bernSymbol_apply (η : ℝ) : (bernSymbol : ℝ → ℂ) η = bernSymbolFun η := rfl

/-- The base kernel `D₁ = 𝓕⁻ (2π i η χ(η))`. -/
noncomputable def bernKernel₁ : 𝓢(ℝ, ℂ) := 𝓕⁻ bernSymbol

theorem fourier_bernKernel₁ (η : ℝ) :
    𝓕 (bernKernel₁ : ℝ → ℂ) η = bernSymbolFun η := by
  have h : 𝓕 bernKernel₁ = bernSymbol := FourierInvPair.fourier_fourierInv_eq bernSymbol
  have := congrArg (fun F : 𝓢(ℝ, ℂ) => (F : ℝ → ℂ) η) h
  simpa [SchwartzMap.fourier_coe, bernSymbol_apply] using this

/-- The scaled kernel `D_R(x) = R² D₁(R x)`. -/
noncomputable def bernKernel (R : ℝ) : ℝ → ℂ := fun x => ((R ^ 2 : ℝ) : ℂ) * bernKernel₁ (R * x)

theorem integrable_bernKernel {R : ℝ} (hR : 0 < R) : Integrable (bernKernel R) := by
  unfold bernKernel
  refine Integrable.const_mul ?_ _
  exact (bernKernel₁.integrable.comp_mul_left' hR.ne')

theorem fourier_bernKernel {R : ℝ} (hR : 0 < R) (ξ : ℝ) :
    𝓕 (bernKernel R) ξ = (2 * π * I * ξ : ℂ) * (bernBump (ξ / R) : ℂ) := by
  unfold bernKernel
  rw [fourier_scale_sq _ hR, fourier_bernKernel₁]
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  simp only [bernSymbolFun]
  push_cast
  field_simp

/-- **Band-limited derivative as a convolution**: if `𝓕 φ` vanishes outside `[-R, R]`, then
`φ′ = D_R ⋆ φ`. -/
theorem deriv_eq_bernKernel_conv {R : ℝ} (hR : 0 < R) (φ : 𝓢(ℝ, ℂ))
    (hband : ∀ ξ : ℝ, R < |ξ| → 𝓕 (φ : ℝ → ℂ) ξ = 0) :
    deriv (φ : ℝ → ℂ) = bernKernel R ⋆[ContinuousLinearMap.mul ℂ ℂ] (φ : ℝ → ℂ) := by
  set K := bernKernel R with hKdef
  have hK : Integrable K := integrable_bernKernel hR
  set F2 : 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℂ ℂ φ with hF2
  have hF2eq : (F2 : ℝ → ℂ) = deriv (φ : ℝ → ℂ) := by
    funext x; simp [hF2, SchwartzMap.derivCLM_apply]
  have hF2int : Integrable (deriv (φ : ℝ → ℂ)) := by rw [← hF2eq]; exact F2.integrable
  have hF2cont : Continuous (deriv (φ : ℝ → ℂ)) := by rw [← hF2eq]; exact F2.continuous
  have hFd : 𝓕 (deriv (φ : ℝ → ℂ)) = fun ξ : ℝ => (2 * π * I * ξ) • 𝓕 (φ : ℝ → ℂ) ξ :=
    Real.fourier_deriv φ.integrable φ.differentiable hF2int
  set F1 : ℝ → ℂ := K ⋆[ContinuousLinearMap.mul ℂ ℂ] (φ : ℝ → ℂ) with hF1
  have hF1int : Integrable F1 := hK.integrable_convolution _ φ.integrable
  have hF1cont : Continuous F1 := by
    refine BddAbove.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℂ ℂ) ?_
      hK φ.continuous
    obtain ⟨C, hC⟩ : ∃ C, ∀ x : ℝ, ‖(φ : ℝ → ℂ) x‖ ≤ C :=
      ⟨_, fun x => (φ.toBoundedContinuousFunction).norm_coe_le_norm x⟩
    exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  have hFF : 𝓕 F1 = 𝓕 (deriv (φ : ℝ → ℂ)) := by
    funext ξ
    rw [hF1, Real.fourier_mul_convolution_eq hK φ.integrable ξ, hFd, hKdef,
      fourier_bernKernel hR ξ]
    by_cases h : R < |ξ|
    · simp only [hband ξ h, smul_eq_mul, mul_zero]
    · push Not at h
      have : |ξ / R| ≤ 1 := by
        rw [abs_div, abs_of_pos hR, div_le_one hR]; exact h
      rw [bernBump_one this]
      simp [smul_eq_mul]
  have hF2fourier : Integrable (𝓕 (deriv (φ : ℝ → ℂ))) := by
    rw [← hF2eq]
    have := (𝓕 F2).integrable (μ := volume)
    simpa [SchwartzMap.fourier_coe] using this
  calc deriv (φ : ℝ → ℂ) = 𝓕⁻ (𝓕 (deriv (φ : ℝ → ℂ))) :=
        (hF2cont.fourierInv_fourier_eq hF2int hF2fourier).symm
    _ = 𝓕⁻ (𝓕 F1) := by rw [hFF]
    _ = F1 := hF1cont.fourierInv_fourier_eq hF1int (by rw [hFF]; exact hF2fourier)

/-- The absolute Bernstein constant `C₁ = ‖D₁‖₁`. -/
noncomputable def bernConst : ℝ := ∫ x : ℝ, ‖(bernKernel₁ : ℝ → ℂ) x‖

theorem integral_norm_bernKernel {R : ℝ} (hR : 0 < R) :
    ∫ x : ℝ, ‖bernKernel R x‖ = R * bernConst := by
  have : ∀ x : ℝ, ‖bernKernel R x‖ = R ^ 2 * (fun y : ℝ => ‖(bernKernel₁ : ℝ → ℂ) y‖) (R * x) :=
    fun x => by
      unfold bernKernel
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  simp_rw [this]
  have hsc := Measure.integral_comp_mul_left (fun y : ℝ => ‖(bernKernel₁ : ℝ → ℂ) y‖) R
  rw [integral_const_mul, hsc, abs_of_pos (inv_pos.2 hR), smul_eq_mul]
  unfold bernConst
  field_simp

/-- **Bernstein's inequality in `L^p`** (`1 ≤ p < ∞`): for a Schwartz function whose Fourier
transform vanishes outside `[-R, R]`,
`∫ ‖φ′‖^p ≤ (C R)^p ∫ ‖φ‖^p` with the absolute constant `C = bernConst`. -/
theorem bernstein_Lp {p : ℝ} (hp : 1 ≤ p) {R : ℝ} (hR : 0 < R) (φ : 𝓢(ℝ, ℂ))
    (hband : ∀ ξ : ℝ, R < |ξ| → 𝓕 (φ : ℝ → ℂ) ξ = 0) :
    ∫⁻ x, ‖deriv (φ : ℝ → ℂ) x‖ₑ ^ p ≤
      ENNReal.ofReal (R * bernConst) ^ p * ∫⁻ x, ‖(φ : ℝ → ℂ) x‖ₑ ^ p := by
  have hK := integrable_bernKernel hR
  have hA : ∫⁻ y, ‖bernKernel R y‖ₑ = ENNReal.ofReal (R * bernConst) := by
    rw [← integral_norm_bernKernel hR, ofReal_integral_norm_eq_lintegral_eNorm hK]
  have h := lintegral_rpow_convolution_le' hp hK.aestronglyMeasurable
    φ.continuous.aestronglyMeasurable (by rw [hA]; exact ENNReal.ofReal_ne_top)
  rw [hA] at h
  rw [deriv_eq_bernKernel_conv hR φ hband]
  exact h

/-- The constant `C = ‖D₁‖₁` is positive. -/
theorem bernConst_pos : 0 < bernConst := by
  unfold bernConst
  refine (integral_pos_iff_support_of_nonneg (fun x => norm_nonneg _)
    bernKernel₁.integrable.norm).2 ?_
  have hopen : IsOpen (Function.support fun x : ℝ => ‖(bernKernel₁ : ℝ → ℂ) x‖) := by
    have : (Function.support fun x : ℝ => ‖(bernKernel₁ : ℝ → ℂ) x‖) =
        (fun x => (bernKernel₁ : ℝ → ℂ) x) ⁻¹' {0}ᶜ := by
      ext x; simp
    rw [this]
    exact isOpen_compl_singleton.preimage bernKernel₁.continuous
  refine hopen.measure_pos volume ?_
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hz : ∀ x : ℝ, (bernKernel₁ : ℝ → ℂ) x = 0 := fun x => by
    by_contra h
    have : x ∈ Function.support fun x : ℝ => ‖(bernKernel₁ : ℝ → ℂ) x‖ := by simpa using h
    rw [hne] at this; exact this
  have h1 := fourier_bernKernel₁ 1
  have h0 : 𝓕 (bernKernel₁ : ℝ → ℂ) 1 = 0 := by
    have : (bernKernel₁ : ℝ → ℂ) = fun _ => 0 := funext hz
    rw [this, Real.fourier_real_eq]; simp
  rw [h0] at h1
  have hb : bernBump 1 = 1 := bernBump_one (by simp)
  simp only [bernSymbolFun, hb] at h1
  have : (2 * (π : ℂ) * I * ((1 : ℝ) : ℂ)) * ((1 : ℝ) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  exact this (by simpa using h1.symm)

/-- **Bernstein's inequality in `L^∞`**: `‖φ′‖_∞ ≤ C R ‖φ‖_∞` for band-limited Schwartz `φ`. -/
theorem bernstein_Linfty {R : ℝ} (hR : 0 < R) (φ : 𝓢(ℝ, ℂ))
    (hband : ∀ ξ : ℝ, R < |ξ| → 𝓕 (φ : ℝ → ℂ) ξ = 0) {M : ℝ}
    (hM : ∀ x : ℝ, ‖(φ : ℝ → ℂ) x‖ ≤ M) (x : ℝ) :
    ‖deriv (φ : ℝ → ℂ) x‖ ≤ R * bernConst * M := by
  have hK := integrable_bernKernel hR
  rw [deriv_eq_bernKernel_conv hR φ hband, convolution_def]
  have hint : Integrable (fun y : ℝ => ‖bernKernel R y‖ * M) :=
    hK.norm.mul_const M
  have h := norm_integral_le_of_norm_le hint
    (f := fun y : ℝ => (ContinuousLinearMap.mul ℂ ℂ) (bernKernel R y) ((φ : ℝ → ℂ) (x - y)))
    (Filter.Eventually.of_forall fun y => by
      simp only [ContinuousLinearMap.mul_apply', norm_mul]
      exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))
  rw [integral_mul_const, integral_norm_bernKernel hR] at h
  exact h

end

end FracLap
