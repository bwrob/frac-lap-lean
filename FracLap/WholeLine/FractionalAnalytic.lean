/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Core.AnalyticSemigroup
public import FracLap.WholeLine.FourierSemigroup

/-!
# FracLap.WholeLine.FractionalAnalytic

Analyticity of Fourier multiplier semigroups on `L²(ℝ; ℂ)` (`thm:s_analytic`).

For a measurable symbol `ψ ≥ 0` the complex-time family
`T(z) = 𝓕⁻¹ ∘ M_{exp(-zψ)} ∘ 𝓕` is a holomorphic semigroup on the open right half-plane. The
mathematical reason: for `Re z ≥ a > 0` the symbol `exp(-zψ)` has modulus `exp(-aψ) ≤ 1`, and a
Taylor expansion of the exponential in `z` produces a remainder bounded by `|h|² ψ² exp(-aψ/2)`,
which is uniformly small because `ψ² exp(-aψ/2) ≤ 16/a²`. Hence `z ↦ T(z)` is differentiable in
operator norm, with derivative the multiplier `-ψ exp(-zψ)`.

* `cMultCLM`, `cFM`: `ℂ`-linear multiplication and Fourier multiplier operators.
* `fourierAnalyticSemigroup`: the `AnalyticSemigroup L2C` on the sector `Σ_{π/2}`.
* `fourierAnalyticSemigroup_real_apply`: on real times it agrees with `fourierMultiplierSemigroup`.
* `fracLapAnalyticSemigroup`: the case `ψ = |2πξ|^α`.
* `fracLapSemigroup_mem_generatorDomain_of_pos`: `S(t) f ∈ D(A)` for every `f ∈ L²`, `t > 0`.
-/

namespace FracLap

open Complex Filter FourierTransform MeasureTheory Set Topology
open scoped ENNReal NNReal ComplexInnerProductSpace

@[expose] public section

/-! ### 1. `ℂ`-linear multiplication and Fourier multiplier operators -/

/-- Multiplication by `m ∈ L^∞(ℝ; ℂ)` as a `ℂ`-linear operator on `L²(ℝ; ℂ)`. -/
noncomputable def cMultCLM (m : Lp (α := ℝ) ℂ ∞ volume) : L2C →L[ℂ] L2C :=
  LinearMap.mkContinuous
    { toFun := fun f => (m • f : L2C)
      map_add' := fun f g => Lp.add_smul m f g
      map_smul' := fun c f => by
        simpa only [RingHom.id_apply] using (Lp.smul_comm (r := 2) c m f).symm }
    ‖m‖ (fun f => Lp.norm_smul_le m f)

/-- Unfolding `cMultCLM`. -/
theorem cMultCLM_apply (m : Lp (α := ℝ) ℂ ∞ volume) (f : L2C) : cMultCLM m f = (m • f : L2C) := by
  simp only [cMultCLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]

/-- The `L²` Fourier transform as a `ℂ`-linear operator. -/
noncomputable def fourierCL : L2C →L[ℂ] L2C :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap

/-- The `L²` inverse Fourier transform as a `ℂ`-linear operator. -/
noncomputable def fourierInvCL : L2C →L[ℂ] L2C :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- `ℂ`-linear Fourier multiplier `𝓕⁻¹ ∘ M_m ∘ 𝓕`. -/
noncomputable def cFM (m : Lp (α := ℝ) ℂ ∞ volume) : L2C →L[ℂ] L2C :=
  fourierInvCL.comp ((cMultCLM m).comp fourierCL)

/-- Inverse after forward Fourier transform is the identity. -/
theorem fourierInvCL_fourierCL (f : L2C) : fourierInvCL (fourierCL f) = f :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm_apply_apply f

/-- Forward after inverse Fourier transform is the identity. -/
theorem fourierCL_fourierInvCL (f : L2C) : fourierCL (fourierInvCL f) = f :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply f

/-- The inverse Fourier transform preserves the `L²` norm. -/
theorem norm_fourierInvCL (f : L2C) : ‖fourierInvCL f‖ = ‖f‖ :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map f

/-- The Fourier transform preserves the `L²` norm. -/
theorem norm_fourierCL (f : L2C) : ‖fourierCL f‖ = ‖f‖ :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).norm_map f

/-- `cFM` applied to a function. -/
theorem cFM_apply (m : Lp (α := ℝ) ℂ ∞ volume) (f : L2C) :
    cFM m f = fourierInvCL ((m • fourierCL f : L2C)) := by
  simp only [cFM, ContinuousLinearMap.comp_apply, cMultCLM_apply]

/-- The `ℝ`-restriction of `cFM` is the existing Fourier multiplier. -/
theorem cFM_eq_fourierMultiplier (m : Lp (α := ℝ) ℂ ∞ volume) (f : L2C) :
    cFM m f = fourierMultiplier m f := by
  rw [cFM_apply, fourierMultiplier_apply]
  rfl

/-- Norm bound for `cFM`: `‖cFM m f‖ ≤ ‖m‖ ‖f‖`. -/
theorem norm_cFM_apply_le (m : Lp (α := ℝ) ℂ ∞ volume) (f : L2C) :
    ‖cFM m f‖ ≤ ‖m‖ * ‖f‖ := by
  rw [cFM_apply, norm_fourierInvCL]
  exact (Lp.norm_smul_le m (fourierCL f)).trans (by rw [norm_fourierCL])

/-- The `L^∞` norm of an element bounded almost everywhere. -/
theorem norm_Lp_top_le {m : Lp (α := ℝ) ℂ ∞ volume} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ ξ ∂volume, ‖(m : ℝ → ℂ) ξ‖ ≤ C) : ‖m‖ ≤ C := by
  rw [Lp.norm_def]
  have he : eLpNorm (m : ℝ → ℂ) ∞ volume ≤ ENNReal.ofReal C := by
    rw [eLpNorm_exponent_top]
    · exact eLpNormEssSup_le_of_ae_bound hb
    · exact Lp.aestronglyMeasurable m
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq (ENNReal.toReal_ofReal hC)

/-! ### 2. `L²` norm of a product and pointwise exponential estimates -/

/-- `‖f‖² = ∫ |f|²` on `L²(ℝ; ℂ)`. -/
theorem norm_sq_eq_integral (f : L2C) : ‖f‖ ^ 2 = ∫ ξ : ℝ, ‖(f : ℝ → ℂ) ξ‖ ^ 2 := by
  have hx : ‖f‖ ^ 2 = (⟪f, f⟫ : ℂ).re := by
    simpa only [RCLike.re_to_complex] using (inner_self_eq_norm_sq (𝕜 := ℂ) f).symm
  have hint : (∫ ξ : ℝ, (⟪(f : ℝ → ℂ) ξ, (f : ℝ → ℂ) ξ⟫ : ℂ)).re =
      ∫ ξ : ℝ, (⟪(f : ℝ → ℂ) ξ, (f : ℝ → ℂ) ξ⟫ : ℂ).re :=
    (Complex.reCLM.integral_comp_comm (L2.integrable_inner f f)).symm
  rw [hx, L2.inner_def, hint]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [inner_self_eq_norm_sq_to_K]
  simp only [Complex.coe_algebraMap, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- `‖m • g‖² = ∫ |m|² |g|²`: Plancherel for multiplication operators. -/
theorem norm_sq_smul (m : Lp (α := ℝ) ℂ ∞ volume) (g : L2C) :
    ‖(m • g : L2C)‖ ^ 2 =
      ∫ ξ : ℝ, ‖(m : ℝ → ℂ) ξ‖ ^ 2 * ‖(g : ℝ → ℂ) ξ‖ ^ 2 := by
  rw [norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_lpSMul (r := 2) m g] with ξ h
  have h' : ((m • g : L2C) : ℝ → ℂ) ξ = (m : ℝ → ℂ) ξ * (g : ℝ → ℂ) ξ := h
  rw [h', norm_mul, mul_pow]

/-- `y e^{-y} ≤ 1`: the exponential beats any linear growth. -/
theorem mul_exp_neg_le_one (y : ℝ) : y * Real.exp (-y) ≤ 1 := by
  have h := Real.add_one_le_exp y
  have hpos := Real.exp_pos (-y)
  calc y * Real.exp (-y) ≤ Real.exp y * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right (by linarith) hpos.le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- `p e^{-a p / 4} ≤ 4 / a`. -/
theorem mul_exp_neg_quarter_le {a : ℝ} (ha : 0 < a) (p : ℝ) :
    p * Real.exp (-(a * p / 4)) ≤ 4 / a := by
  have h := mul_exp_neg_le_one (a * p / 4)
  rw [le_div_iff₀ ha]
  have : p * Real.exp (-(a * p / 4)) * a = 4 * (a * p / 4 * Real.exp (-(a * p / 4))) := by ring
  rw [this]
  linarith

/-- `p e^{-a p} ≤ 1 / a`. -/
theorem mul_exp_neg_le_inv {a : ℝ} (ha : 0 < a) (p : ℝ) :
    p * Real.exp (-(a * p)) ≤ 1 / a := by
  have h := mul_exp_neg_le_one (a * p)
  rw [le_div_iff₀ ha]
  have : p * Real.exp (-(a * p)) * a = a * p * Real.exp (-(a * p)) := by ring
  rw [this]
  exact h

/-- A Taylor bound for the complex exponential valid for all arguments:
`‖e^w - 1 - w‖ ≤ 3 ‖w‖² e^{max (Re w) 0}`. -/
theorem norm_exp_sub_one_sub_le (w : ℂ) :
    ‖Complex.exp w - 1 - w‖ ≤ 3 * ‖w‖ ^ 2 * Real.exp (max w.re 0) := by
  have hE : 1 ≤ Real.exp (max w.re 0) := Real.one_le_exp (le_max_right _ _)
  by_cases h1 : ‖w‖ ≤ 1
  · have := Complex.norm_exp_sub_one_sub_id_le h1
    nlinarith [sq_nonneg ‖w‖]
  · replace h1 := not_le.mp h1
    have hn : ‖Complex.exp w - 1 - w‖ ≤ ‖Complex.exp w‖ + 1 + ‖w‖ := by
      calc ‖Complex.exp w - 1 - w‖ ≤ ‖Complex.exp w - 1‖ + ‖w‖ := norm_sub_le _ _
        _ ≤ (‖Complex.exp w‖ + ‖(1 : ℂ)‖) + ‖w‖ := by gcongr; exact norm_sub_le _ _
        _ = ‖Complex.exp w‖ + 1 + ‖w‖ := by rw [norm_one]
    have hexpn : ‖Complex.exp w‖ ≤ Real.exp (max w.re 0) := by
      rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (le_max_left _ _)
    have hX1 : 1 ≤ ‖w‖ ^ 2 := by nlinarith
    have hX2 : ‖w‖ ≤ ‖w‖ ^ 2 := by nlinarith
    have hXE : Real.exp (max w.re 0) ≤ ‖w‖ ^ 2 * Real.exp (max w.re 0) := by nlinarith
    have hXE' : 1 ≤ ‖w‖ ^ 2 * Real.exp (max w.re 0) := by nlinarith
    have hXE'' : ‖w‖ ≤ ‖w‖ ^ 2 * Real.exp (max w.re 0) := by nlinarith
    nlinarith

/-- Pointwise Taylor remainder of the symbol `p ↦ e^{-z p}` in the complex time `z`. -/
theorem norm_exp_taylor_symbol {a : ℝ} (ha : 0 < a) {z h : ℂ} (hz : z.re = a)
    (hh : ‖h‖ ≤ a / 2) {p : ℝ} (hp : 0 ≤ p) :
    ‖Complex.exp (-((z + h) * (p : ℂ))) - Complex.exp (-(z * (p : ℂ))) -
        h * (-((p : ℂ) * Complex.exp (-(z * (p : ℂ)))))‖ ≤ 48 / a ^ 2 * ‖h‖ ^ 2 := by
  set w : ℂ := -(h * (p : ℂ)) with hw
  have hfac : Complex.exp (-((z + h) * (p : ℂ))) - Complex.exp (-(z * (p : ℂ))) -
      h * (-((p : ℂ) * Complex.exp (-(z * (p : ℂ))))) =
        Complex.exp (-(z * (p : ℂ))) * (Complex.exp w - 1 - w) := by
    have : -((z + h) * (p : ℂ)) = -(z * (p : ℂ)) + w := by rw [hw]; ring
    rw [this, Complex.exp_add, hw]
    ring
  rw [hfac, norm_mul]
  have hexp0 : ‖Complex.exp (-(z * (p : ℂ)))‖ = Real.exp (-(a * p)) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, hz]
  have hwnorm : ‖w‖ = ‖h‖ * p := by
    rw [hw, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
  have hwre : max w.re 0 ≤ a * p / 2 := by
    refine max_le ?_ (by positivity)
    have hre : w.re = -(h.re * p) := by simp [hw, Complex.mul_re]
    have hh' : -h.re ≤ a / 2 := by
      have := Complex.abs_re_le_norm h
      have := neg_abs_le h.re
      linarith
    rw [hre]
    nlinarith
  have hT := norm_exp_sub_one_sub_le w
  have hE : Real.exp (max w.re 0) ≤ Real.exp (a * p / 2) := Real.exp_le_exp.mpr hwre
  have hq : p * Real.exp (-(a * p / 4)) ≤ 4 / a := mul_exp_neg_quarter_le ha p
  have hq0 : 0 ≤ p * Real.exp (-(a * p / 4)) := by positivity
  have hexp_sq : Real.exp (-(a * p)) * Real.exp (a * p / 2) =
      Real.exp (-(a * p / 4)) ^ 2 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc ‖Complex.exp (-(z * (p : ℂ)))‖ * ‖Complex.exp w - 1 - w‖
      ≤ Real.exp (-(a * p)) * (3 * ‖w‖ ^ 2 * Real.exp (a * p / 2)) := by
        rw [hexp0]
        refine mul_le_mul_of_nonneg_left (hT.trans ?_) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hE (by positivity)
    _ = 3 * ‖h‖ ^ 2 * (p * Real.exp (-(a * p / 4))) ^ 2 := by
        rw [hwnorm]
        have := hexp_sq
        calc Real.exp (-(a * p)) * (3 * (‖h‖ * p) ^ 2 * Real.exp (a * p / 2))
            = 3 * ‖h‖ ^ 2 * p ^ 2 * (Real.exp (-(a * p)) * Real.exp (a * p / 2)) := by ring
          _ = _ := by rw [this]; ring
    _ ≤ 3 * ‖h‖ ^ 2 * (4 / a) ^ 2 := by
        gcongr
    _ = 48 / a ^ 2 * ‖h‖ ^ 2 := by
        field_simp
        ring

/-! ### 3. Complex-time symbols and the semigroup law -/

/-- Linearity of `cMultCLM` in the symbol: difference. -/
theorem cMultCLM_sub (m₁ m₂ : Lp (α := ℝ) ℂ ∞ volume) (f : L2C) :
    cMultCLM (m₁ - m₂) f = cMultCLM m₁ f - cMultCLM m₂ f := by
  simp only [cMultCLM_apply, sub_eq_add_neg, Lp.smul_add, Lp.neg_smul]

/-- Linearity of `cMultCLM` in the symbol: scalar multiples. -/
theorem cMultCLM_smul (c : ℂ) (m : Lp (α := ℝ) ℂ ∞ volume) (f : L2C) :
    cMultCLM (c • m) f = c • cMultCLM m f := by
  simp only [cMultCLM_apply]
  exact Lp.smul_assoc c m f

/-- `cFM` is additive in the symbol (difference form). -/
theorem cFM_sub_apply (m₁ m₂ : Lp (α := ℝ) ℂ ∞ volume) (f : L2C) :
    cFM (m₁ - m₂) f = cFM m₁ f - cFM m₂ f := by
  simp only [cFM, ContinuousLinearMap.comp_apply, cMultCLM_sub, map_sub]

/-- `cFM` is homogeneous in the symbol. -/
theorem cFM_smul_apply (c : ℂ) (m : Lp (α := ℝ) ℂ ∞ volume) (f : L2C) :
    cFM (c • m) f = c • cFM m f := by
  simp only [cFM, ContinuousLinearMap.comp_apply, cMultCLM_smul, map_smul]

/-- The complex-time symbol `ξ ↦ exp (-z ψ ξ)` (set to `1` outside `Re z ≥ 0`, where it is not
bounded). -/
noncomputable def symFun (ψ : ℝ → ℝ) (z : ℂ) (ξ : ℝ) : ℂ :=
  if 0 ≤ z.re then Complex.exp (-(z * (ψ ξ : ℂ))) else 1

/-- On `Re z ≥ 0` the symbol is the exponential. -/
theorem symFun_of_re_nonneg (ψ : ℝ → ℝ) {z : ℂ} (hz : 0 ≤ z.re) (ξ : ℝ) :
    symFun ψ z ξ = Complex.exp (-(z * (ψ ξ : ℂ))) := by
  unfold symFun
  simp [hz]

/-- The symbol is bounded by `1`. -/
theorem norm_symFun_le_one (ψ : ℝ → ℝ) (hn : ∀ ξ, 0 ≤ ψ ξ) (z : ℂ) (ξ : ℝ) :
    ‖symFun ψ z ξ‖ ≤ 1 := by
  unfold symFun
  split_ifs with h
  · rw [Complex.norm_exp]
    refine Real.exp_le_one_iff.mpr ?_
    have : (-(z * (ψ ξ : ℂ))).re = -(z.re * ψ ξ) := by simp [Complex.mul_re]
    rw [this]
    nlinarith [hn ξ]
  · simp

/-- Measurability of the symbol. -/
theorem aestronglyMeasurable_symFun (ψ : ℝ → ℝ) (hm : Measurable ψ) (z : ℂ) :
    AEStronglyMeasurable (symFun ψ z) volume := by
  unfold symFun
  split_ifs
  · exact (Complex.continuous_exp.measurable.comp
      ((measurable_const.mul (Complex.measurable_ofReal.comp hm)).neg)).aestronglyMeasurable
  · exact aestronglyMeasurable_const

/-- The symbol as an element of `L^∞(ℝ; ℂ)`. -/
noncomputable def symElt (ψ : ℝ → ℝ) (hm : Measurable ψ) (hn : ∀ ξ, 0 ≤ ψ ξ) (z : ℂ) :
    Lp (α := ℝ) ℂ ∞ volume :=
  toLpTop (aestronglyMeasurable_symFun ψ hm z) zero_le_one (norm_symFun_le_one ψ hn z)

/-- Almost-everywhere description of `symElt`. -/
theorem coeFn_symElt (ψ : ℝ → ℝ) (hm : Measurable ψ) (hn : ∀ ξ, 0 ≤ ψ ξ) (z : ℂ) :
    (symElt ψ hm hn z : ℝ → ℂ) =ᵐ[volume] symFun ψ z :=
  coeFn_toLpTop (aestronglyMeasurable_symFun ψ hm z) zero_le_one (norm_symFun_le_one ψ hn z)

/-- `‖symElt z‖_∞ ≤ 1`. -/
theorem norm_symElt_le_one (ψ : ℝ → ℝ) (hm : Measurable ψ) (hn : ∀ ξ, 0 ≤ ψ ξ) (z : ℂ) :
    ‖symElt ψ hm hn z‖ ≤ 1 :=
  norm_toLpTop_le (aestronglyMeasurable_symFun ψ hm z) zero_le_one (norm_symFun_le_one ψ hn z)

/-- Symbols multiply: `symElt z₁ • symElt z₂ • g = symElt (z₁ + z₂) • g` for `Re z ≥ 0`. -/
theorem symElt_smul_smul (ψ : ℝ → ℝ) (hm : Measurable ψ) (hn : ∀ ξ, 0 ≤ ψ ξ) {z₁ z₂ : ℂ}
    (h₁ : 0 ≤ z₁.re) (h₂ : 0 ≤ z₂.re) (g : L2C) :
    (symElt ψ hm hn z₁ • (symElt ψ hm hn z₂ • g : L2C) : L2C) =
      (symElt ψ hm hn (z₁ + z₂) • g : L2C) := by
  have h₁₂ : 0 ≤ (z₁ + z₂).re := by rw [Complex.add_re]; linarith
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (symElt ψ hm hn z₁) (symElt ψ hm hn z₂ • g : L2C),
    Lp.coeFn_lpSMul (r := 2) (symElt ψ hm hn z₂) g,
    Lp.coeFn_lpSMul (r := 2) (symElt ψ hm hn (z₁ + z₂)) g, coeFn_symElt ψ hm hn z₁,
    coeFn_symElt ψ hm hn z₂, coeFn_symElt ψ hm hn (z₁ + z₂)] with ξ a b c d e f
  have a' : ((symElt ψ hm hn z₁ • (symElt ψ hm hn z₂ • g : L2C) : L2C) : ℝ → ℂ) ξ =
      (symElt ψ hm hn z₁ : ℝ → ℂ) ξ * ((symElt ψ hm hn z₂ • g : L2C) : ℝ → ℂ) ξ := a
  have b' : ((symElt ψ hm hn z₂ • g : L2C) : ℝ → ℂ) ξ =
      (symElt ψ hm hn z₂ : ℝ → ℂ) ξ * (g : ℝ → ℂ) ξ := b
  have c' : ((symElt ψ hm hn (z₁ + z₂) • g : L2C) : ℝ → ℂ) ξ =
      (symElt ψ hm hn (z₁ + z₂) : ℝ → ℂ) ξ * (g : ℝ → ℂ) ξ := c
  rw [a', b', c', d, e, f, symFun_of_re_nonneg ψ h₁, symFun_of_re_nonneg ψ h₂,
    symFun_of_re_nonneg ψ h₁₂, ← mul_assoc, ← Complex.exp_add]
  congr 3
  ring

/-- At time `0` the symbol is `1`. -/
theorem symElt_zero_smul (ψ : ℝ → ℝ) (hm : Measurable ψ) (hn : ∀ ξ, 0 ≤ ψ ξ) (g : L2C) :
    (symElt ψ hm hn 0 • g : L2C) = g := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (symElt ψ hm hn 0) g,
    coeFn_symElt ψ hm hn 0] with ξ a d
  have a' : ((symElt ψ hm hn 0 • g : L2C) : ℝ → ℂ) ξ =
      (symElt ψ hm hn 0 : ℝ → ℂ) ξ * (g : ℝ → ℂ) ξ := a
  rw [a', d, symFun_of_re_nonneg ψ (by simp)]
  simp

/-- The complex-time Fourier multiplier operator `T(z) = 𝓕⁻¹ M_{exp(-zψ)} 𝓕`. -/
noncomputable def fourierOp (ψ : ℝ → ℝ) (hm : Measurable ψ) (hn : ∀ ξ, 0 ≤ ψ ξ) (z : ℂ) :
    L2C →L[ℂ] L2C :=
  cFM (symElt ψ hm hn z)

/-- `T(0) = I`. -/
theorem fourierOp_zero (ψ : ℝ → ℝ) (hm : Measurable ψ) (hn : ∀ ξ, 0 ≤ ψ ξ) :
    fourierOp ψ hm hn 0 = ContinuousLinearMap.id ℂ L2C := by
  ext1 f
  rw [fourierOp, cFM_apply, symElt_zero_smul, fourierInvCL_fourierCL]
  rfl

/-- The semigroup law `T(z₁ + z₂) = T(z₁) T(z₂)` for `Re z_i ≥ 0`. -/
theorem fourierOp_add (ψ : ℝ → ℝ) (hm : Measurable ψ) (hn : ∀ ξ, 0 ≤ ψ ξ) {z₁ z₂ : ℂ}
    (h₁ : 0 ≤ z₁.re) (h₂ : 0 ≤ z₂.re) :
    fourierOp ψ hm hn (z₁ + z₂) = (fourierOp ψ hm hn z₁).comp (fourierOp ψ hm hn z₂) := by
  ext1 f
  simp only [fourierOp, ContinuousLinearMap.comp_apply, cFM_apply, fourierCL_fourierInvCL,
    symElt_smul_smul ψ hm hn h₁ h₂]

/-- Norm bound `‖T(z)‖ ≤ 1`. -/
theorem norm_fourierOp_apply_le (ψ : ℝ → ℝ) (hm : Measurable ψ) (hn : ∀ ξ, 0 ≤ ψ ξ) (z : ℂ)
    (f : L2C) : ‖fourierOp ψ hm hn z f‖ ≤ ‖f‖ := by
  have := norm_cFM_apply_le (symElt ψ hm hn z) f
  calc ‖fourierOp ψ hm hn z f‖ ≤ ‖symElt ψ hm hn z‖ * ‖f‖ := this
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right (norm_symElt_le_one ψ hm hn z) (norm_nonneg _)
    _ = ‖f‖ := one_mul _

/-! ### 4. Complex differentiability and sectorial continuity at `0` -/

/-- The derivative symbol `ξ ↦ -ψ(ξ) exp (-z ψ(ξ))`. -/
noncomputable def dSymFun (ψ : ℝ → ℝ) (z : ℂ) (ξ : ℝ) : ℂ :=
  -((ψ ξ : ℂ) * Complex.exp (-(z * (ψ ξ : ℂ))))

/-- The derivative symbol is bounded by `1 / Re z` for `Re z > 0`. -/
theorem norm_dSymFun_le (ψ : ℝ → ℝ) (hn : ∀ ξ, 0 ≤ ψ ξ) {z : ℂ} (hz : 0 < z.re) (ξ : ℝ) :
    ‖dSymFun ψ z ξ‖ ≤ 1 / z.re := by
  unfold dSymFun
  rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hn ξ),
    Complex.norm_exp]
  have : (-(z * (ψ ξ : ℂ))).re = -(z.re * ψ ξ) := by simp [Complex.mul_re]
  rw [this]
  exact mul_exp_neg_le_inv hz (ψ ξ)

/-- Measurability of the derivative symbol. -/
theorem aestronglyMeasurable_dSymFun (ψ : ℝ → ℝ) (hm : Measurable ψ) (z : ℂ) :
    AEStronglyMeasurable (dSymFun ψ z) volume := by
  unfold dSymFun
  exact (((Complex.measurable_ofReal.comp hm).mul (Complex.continuous_exp.measurable.comp
    ((measurable_const.mul (Complex.measurable_ofReal.comp hm)).neg))).neg).aestronglyMeasurable

/-- The derivative symbol as an element of `L^∞(ℝ; ℂ)` (for `Re z > 0`). -/
noncomputable def dSymElt (ψ : ℝ → ℝ) (hm : Measurable ψ) (hn : ∀ ξ, 0 ≤ ψ ξ) {z : ℂ}
    (hz : 0 < z.re) : Lp (α := ℝ) ℂ ∞ volume :=
  toLpTop (aestronglyMeasurable_dSymFun ψ hm z) (one_div_nonneg.mpr hz.le)
    (norm_dSymFun_le ψ hn hz)

/-- Almost-everywhere description of `dSymElt`. -/
theorem coeFn_dSymElt (ψ : ℝ → ℝ) (hm : Measurable ψ) (hn : ∀ ξ, 0 ≤ ψ ξ) {z : ℂ}
    (hz : 0 < z.re) : (dSymElt ψ hm hn hz : ℝ → ℂ) =ᵐ[volume] dSymFun ψ z :=
  coeFn_toLpTop (aestronglyMeasurable_dSymFun ψ hm z) (one_div_nonneg.mpr hz.le)
    (norm_dSymFun_le ψ hn hz)

/-- **Holomorphy of the orbit (`thm:s_analytic`)**: for `Re z > 0` the orbit
`w ↦ T(w) f` is complex differentiable at `z`, with derivative the multiplier `-ψ e^{-zψ}`. -/
theorem hasDerivAt_fourierOp (ψ : ℝ → ℝ) (hm : Measurable ψ) (hn : ∀ ξ, 0 ≤ ψ ξ) {z : ℂ}
    (hz : 0 < z.re) (f : L2C) :
    HasDerivAt (fun w : ℂ => fourierOp ψ hm hn w f) (cFM (dSymElt ψ hm hn hz) f) z := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hbound : ∀ h : ℂ, ‖h‖ ≤ z.re / 2 →
      ‖fourierOp ψ hm hn (z + h) f - fourierOp ψ hm hn z f - h • cFM (dSymElt ψ hm hn hz) f‖ ≤
        (48 / z.re ^ 2 * ‖f‖) * ‖h‖ ^ 2 := by
    intro h hh
    have hre : 0 ≤ (z + h).re := by
      have := neg_abs_le h.re
      have := Complex.abs_re_le_norm h
      rw [Complex.add_re]
      linarith
    have hlin : fourierOp ψ hm hn (z + h) f - fourierOp ψ hm hn z f -
        h • cFM (dSymElt ψ hm hn hz) f =
        cFM (symElt ψ hm hn (z + h) - symElt ψ hm hn z - h • dSymElt ψ hm hn hz) f := by
      rw [cFM_sub_apply, cFM_sub_apply, cFM_smul_apply]
      rfl
    rw [hlin]
    have hr : ‖symElt ψ hm hn (z + h) - symElt ψ hm hn z - h • dSymElt ψ hm hn hz‖ ≤
        48 / z.re ^ 2 * ‖h‖ ^ 2 := by
      refine norm_Lp_top_le (by positivity) ?_
      filter_upwards [Lp.coeFn_sub (symElt ψ hm hn (z + h) - symElt ψ hm hn z)
          (h • dSymElt ψ hm hn hz),
        Lp.coeFn_sub (symElt ψ hm hn (z + h)) (symElt ψ hm hn z),
        Lp.coeFn_smul h (dSymElt ψ hm hn hz), coeFn_symElt ψ hm hn (z + h),
        coeFn_symElt ψ hm hn z, coeFn_dSymElt ψ hm hn hz] with ξ h1 h2 h3 h4 h5 h6
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3
      rw [h1, h2, h3, h4, h5, h6, symFun_of_re_nonneg ψ hre, symFun_of_re_nonneg ψ hz.le]
      unfold dSymFun
      exact norm_exp_taylor_symbol hz rfl hh (hn ξ)
    calc ‖cFM (symElt ψ hm hn (z + h) - symElt ψ hm hn z - h • dSymElt ψ hm hn hz) f‖
        ≤ ‖symElt ψ hm hn (z + h) - symElt ψ hm hn z - h • dSymElt ψ hm hn hz‖ * ‖f‖ :=
          norm_cFM_apply_le _ _
      _ ≤ (48 / z.re ^ 2 * ‖h‖ ^ 2) * ‖f‖ :=
          mul_le_mul_of_nonneg_right hr (norm_nonneg _)
      _ = (48 / z.re ^ 2 * ‖f‖) * ‖h‖ ^ 2 := by ring
  refine (Asymptotics.IsBigO.of_bound (48 / z.re ^ 2 * ‖f‖) ?_).trans_isLittleO
    (Asymptotics.isLittleO_pow_id (n := 2) one_lt_two)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (half_pos hz)] with h hh
  have hh' : ‖h‖ ≤ z.re / 2 := by
    simpa only [Metric.mem_ball, dist_zero_right] using (mem_ball_zero_iff.mp hh).le
  rw [norm_pow]
  exact hbound h hh'

/-- **Sectorial strong continuity at `0`**: `T(z) f → f` as `z → 0` with `Re z > 0`. -/
theorem tendsto_fourierOp_zero (ψ : ℝ → ℝ) (hm : Measurable ψ) (hn : ∀ ξ, 0 ≤ ψ ξ) (f : L2C) :
    Tendsto (fun z : ℂ => fourierOp ψ hm hn z f) (𝓝[{z : ℂ | 0 < z.re}] 0) (𝓝 f) := by
  set g : L2C := fourierCL f with hg
  have hgint : Integrable (fun ξ : ℝ => ‖(g : ℝ → ℂ) ξ‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  have hsq : Tendsto (fun z : ℂ =>
      ∫ ξ : ℝ, ‖symFun ψ z ξ - 1‖ ^ 2 * ‖(g : ℝ → ℂ) ξ‖ ^ 2)
      (𝓝[{z : ℂ | 0 < z.re}] 0) (𝓝 0) := by
    have hdom := tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := 𝓝[{z : ℂ | 0 < z.re}] 0)
      (F := fun (z : ℂ) (ξ : ℝ) => ‖symFun ψ z ξ - 1‖ ^ 2 * ‖(g : ℝ → ℂ) ξ‖ ^ 2)
      (f := fun _ : ℝ => (0 : ℝ)) (bound := fun ξ => 4 * ‖(g : ℝ → ℂ) ξ‖ ^ 2)
      (Eventually.of_forall fun z =>
        (((aestronglyMeasurable_symFun ψ hm z).sub aestronglyMeasurable_const).norm.pow 2).mul
          ((Lp.aestronglyMeasurable g).norm.pow 2))
      (Eventually.of_forall fun z => Eventually.of_forall fun ξ => by
        have h1 : ‖symFun ψ z ξ - 1‖ ≤ 2 := by
          calc ‖symFun ψ z ξ - 1‖ ≤ ‖symFun ψ z ξ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ ≤ 1 + 1 := by rw [norm_one]; exact add_le_add (norm_symFun_le_one ψ hn z ξ) le_rfl
            _ = 2 := by norm_num
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have : ‖symFun ψ z ξ - 1‖ ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        nlinarith [sq_nonneg ‖(g : ℝ → ℂ) ξ‖])
      (hgint.const_mul 4)
      (Eventually.of_forall fun ξ => by
        have hcont : Tendsto (fun z : ℂ => Complex.exp (-(z * (ψ ξ : ℂ)))) (𝓝 0) (𝓝 1) := by
          have : Continuous (fun z : ℂ => Complex.exp (-(z * (ψ ξ : ℂ)))) := by fun_prop
          simpa using this.tendsto 0
        have hev : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.re}] 0, 0 ≤ z.re :=
          eventually_mem_nhdsWithin.mono fun z hz => le_of_lt hz
        have hlim : Tendsto (fun z : ℂ => symFun ψ z ξ) (𝓝[{z : ℂ | 0 < z.re}] 0) (𝓝 1) :=
          (hcont.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun z hz =>
            (symFun_of_re_nonneg ψ hz ξ).symm)
        have h2 := ((hlim.sub_const 1).norm.pow 2).mul_const (‖(g : ℝ → ℂ) ξ‖ ^ 2)
        simpa using h2)
    simpa only [integral_zero] using hdom
  have hnorm : Tendsto (fun z : ℂ => ‖fourierOp ψ hm hn z f - f‖)
      (𝓝[{z : ℂ | 0 < z.re}] 0) (𝓝 0) := by
    refine tendsto_zero_of_nonneg_sq_le (fun _ => norm_nonneg _) (fun z => ?_) hsq
    have hdiff : fourierOp ψ hm hn z f - f =
        fourierInvCL ((symElt ψ hm hn z • g : L2C) - g) := by
      rw [map_sub, fourierOp, cFM_apply, hg, fourierInvCL_fourierCL]
    rw [hdiff, norm_fourierInvCL, norm_sq_eq_integral]
    refine le_of_eq (integral_congr_ae ?_)
    filter_upwards [Lp.coeFn_sub (symElt ψ hm hn z • g : L2C) g,
      Lp.coeFn_lpSMul (r := 2) (symElt ψ hm hn z) g, coeFn_symElt ψ hm hn z] with ξ h1 h2 h3
    have h2' : ((symElt ψ hm hn z • g : L2C) : ℝ → ℂ) ξ =
        (symElt ψ hm hn z : ℝ → ℂ) ξ * (g : ℝ → ℂ) ξ := h2
    simp only [Pi.sub_apply] at h1
    rw [h1, h2', h3, ← sub_one_mul, norm_mul, mul_pow]
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

/-! ### 5. The analytic semigroup and its real-time restriction -/

/-- **Fourier multiplier analytic semigroup (`thm:s_analytic`)**: for a measurable `ψ ≥ 0`,
`T(z) = 𝓕⁻¹ M_{exp(-zψ)} 𝓕` is an analytic semigroup on `L²(ℝ; ℂ)` on the sector `Σ_{π/2}`. -/
noncomputable def fourierAnalyticSemigroup (ψ : ℝ → ℝ) (hm : Measurable ψ)
    (hn : ∀ ξ, 0 ≤ ψ ξ) : AnalyticSemigroup L2C where
  delta := Real.pi / 2
  delta_pos := Real.pi_div_two_pos
  delta_le := le_rfl
  operator := fourierOp ψ hm hn
  operator_zero := fourierOp_zero ψ hm hn
  operator_add {z₁ z₂} h₁ h₂ := by
    have e₁ : 0 < z₁.re := by rw [openSector_pi_div_two] at h₁; exact h₁
    have e₂ : 0 < z₂.re := by rw [openSector_pi_div_two] at h₂; exact h₂
    exact fourierOp_add ψ hm hn e₁.le e₂.le
  differentiableOn f z hz := by
    have e : 0 < z.re := by rw [openSector_pi_div_two] at hz; exact hz
    exact (hasDerivAt_fourierOp ψ hm hn e f).differentiableAt.differentiableWithinAt
  tendsto_zero {δ'} _ hlt f := by
    exact (tendsto_fourierOp_zero ψ hm hn f).mono_left
      (nhdsWithin_mono _ (openSector_subset_re_pos hlt.le))

/-- On real times the symbol `symElt t` is the real exponential symbol. -/
theorem symElt_ofReal (ψ : ℝ → ℝ) (hm : Measurable ψ) (hn : ∀ ξ, 0 ≤ ψ ξ) (t : ℝ≥0) :
    symElt ψ hm hn (t : ℂ) = expMultiplierSymbol ψ hm hn t := by
  refine Lp.ext ?_
  filter_upwards [coeFn_symElt ψ hm hn (t : ℂ),
    coeFn_toLpTop (expSymbol_aestronglyMeasurable ψ hm t) zero_le_one
      (norm_expSymbol_le_one ψ hn t.coe_nonneg)] with ξ h1 h2
  have h2' : (expMultiplierSymbol ψ hm hn t : ℝ → ℂ) ξ =
      ((Real.exp (-(t : ℝ) * ψ ξ) : ℝ) : ℂ) := h2
  rw [h1, h2', symFun_of_re_nonneg ψ (by simp), Complex.ofReal_exp]
  push_cast
  ring_nf

/-- On real times the analytic semigroup is the Fourier multiplier semigroup. -/
theorem fourierOp_ofReal_apply (ψ : ℝ → ℝ) (hm : Measurable ψ) (hn : ∀ ξ, 0 ≤ ψ ξ)
    (t : ℝ≥0) (f : L2C) :
    fourierOp ψ hm hn (t : ℂ) f = fourierMultiplierSemigroup ψ hm hn t f := by
  rw [fourierOp, cFM_eq_fourierMultiplier, symElt_ofReal]
  rfl

/-- **Immediate regularization (`prop:analytic_domain`, whole-line multipliers)**: `T(t) f` lies in
the generator domain for every `f ∈ L²` and `t > 0`. -/
theorem fourierMultiplierSemigroup_mem_generatorDomain_of_pos (ψ : ℝ → ℝ) (hm : Measurable ψ)
    (hn : ∀ ξ, 0 ≤ ψ ξ) (f : L2C) {t : ℝ≥0} (ht : 0 < (t : ℝ)) :
    fourierMultiplierSemigroup ψ hm hn t f ∈
      (fourierMultiplierSemigroup ψ hm hn).generatorDomain :=
  (fourierAnalyticSemigroup ψ hm hn).real_orbit_mem_generatorDomain
    (fourierMultiplierSemigroup ψ hm hn)
    (fun s y => (fourierOp_ofReal_apply ψ hm hn s y).symm) f ht

/-- **Generator on the orbit**: `A (T(t) f) = 𝓕⁻¹ (-ψ e^{-tψ} 𝓕 f)` for `t > 0`. -/
theorem generator_fourierMultiplierSemigroup_apply (ψ : ℝ → ℝ) (hm : Measurable ψ)
    (hn : ∀ ξ, 0 ≤ ψ ξ) (f : L2C) {t : ℝ≥0} (ht : 0 < (t : ℝ)) :
    (fourierMultiplierSemigroup ψ hm hn).generator
        ⟨fourierMultiplierSemigroup ψ hm hn t f,
          fourierMultiplierSemigroup_mem_generatorDomain_of_pos ψ hm hn f ht⟩ =
      cFM (dSymElt ψ hm hn (z := (t : ℂ)) (by simpa using ht)) f := by
  have hre : 0 < ((t : ℝ) : ℂ).re := by simpa using ht
  have h := (fourierAnalyticSemigroup ψ hm hn).generator_real_orbit_eq
    (fourierMultiplierSemigroup ψ hm hn)
    (fun s y => (fourierOp_ofReal_apply ψ hm hn s y).symm) f ht
  exact h.trans (hasDerivAt_fourierOp ψ hm hn hre f).deriv

/-- **The fractional heat semigroup is analytic (`thm:s_analytic`)**: `ψ = |2π ξ|^α`. -/
noncomputable def fracLapAnalyticSemigroup (α : ℝ) : AnalyticSemigroup L2C :=
  fourierAnalyticSemigroup (fracLapSymbol α) (measurable_fracLapSymbol α)
    (fracLapSymbol_nonneg α)

/-- The analytic semigroup extends the real-time fractional heat semigroup. -/
theorem fracLapAnalyticSemigroup_ofReal_apply (α : ℝ) (t : ℝ≥0) (f : L2C) :
    (fracLapAnalyticSemigroup α).operator (t : ℂ) f = fracLapSemigroup α t f :=
  fourierOp_ofReal_apply (fracLapSymbol α) (measurable_fracLapSymbol α)
    (fracLapSymbol_nonneg α) t f

/-- **`S_α(t) L² ⊆ D(A_α)` for `t > 0`** (`thm:s_analytic`): the fractional heat semigroup maps
every `L²` function into the generator domain. -/
theorem fracLapSemigroup_mem_generatorDomain_of_pos (α : ℝ) (f : L2C) {t : ℝ≥0}
    (ht : 0 < (t : ℝ)) :
    fracLapSemigroup α t f ∈ (fracLapSemigroup α).generatorDomain :=
  fourierMultiplierSemigroup_mem_generatorDomain_of_pos (fracLapSymbol α)
    (measurable_fracLapSymbol α) (fracLapSymbol_nonneg α) f ht

/-- Smooth dependence on time for the fractional heat orbit on `(0, ∞)`: the real-time orbit
`s ↦ S_α(s) f` is `C^∞`. -/
theorem fracLapSemigroup_contDiffOn_orbit (α : ℝ) (f : L2C) :
    ContDiffOn ℝ ⊤ (fun s : ℝ => fracLapSemigroup α (Real.toNNReal s) f) (Ioi 0) :=
  ((fracLapAnalyticSemigroup α).contDiffOn_real_orbit f).congr fun s hs => by
    rw [← fracLapAnalyticSemigroup_ofReal_apply, Real.coe_toNNReal s (le_of_lt hs)]

/-- **Non-vacuity witness**: the analytic fractional heat semigroup is not the identity at time
`1`. Take `f` with Fourier transform the indicator of `[1, 2]`; the symbol `e^{-|2π ξ|^α}` is
strictly below `1` there. -/
theorem exists_fracLapAnalyticSemigroup_nontrivial (α : ℝ) :
    ∃ f : L2C, (fracLapAnalyticSemigroup α).operator 1 f ≠ f := by
  let g : L2C := indicatorConstLp 2 (measurableSet_Icc (a := (1 : ℝ)) (b := 2)) (by simp)
    (1 : ℂ)
  refine ⟨fourierInvCL g, fun h => ?_⟩
  have h1 : (symElt (fracLapSymbol α) (measurable_fracLapSymbol α) (fracLapSymbol_nonneg α) 1 • g :
      L2C) = g := by
    have h2 := congrArg fourierCL h
    simp only [fracLapAnalyticSemigroup, fourierAnalyticSemigroup, fourierOp, cFM_apply,
      fourierCL_fourierInvCL] at h2
    exact h2
  have hae : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ∉ Icc (1 : ℝ) 2 := by
    filter_upwards [Lp.coeFn_lpSMul (r := 2)
        (symElt (fracLapSymbol α) (measurable_fracLapSymbol α) (fracLapSymbol_nonneg α) 1) g,
      coeFn_symElt (fracLapSymbol α) (measurable_fracLapSymbol α) (fracLapSymbol_nonneg α) 1,
      indicatorConstLp_coeFn (p := 2) (s := Icc (1 : ℝ) 2) (μ := volume) (c := (1 : ℂ))
        (hs := measurableSet_Icc) (hμs := by simp),
      Lp.ext_iff.mp h1] with ξ a b c d hξ
    have a' : ((symElt (fracLapSymbol α) (measurable_fracLapSymbol α) (fracLapSymbol_nonneg α) 1 •
        g : L2C) : ℝ → ℂ) ξ =
        (symElt (fracLapSymbol α) (measurable_fracLapSymbol α) (fracLapSymbol_nonneg α) 1 :
          ℝ → ℂ) ξ * (g : ℝ → ℂ) ξ := a
    have hg : (g : ℝ → ℂ) ξ = 1 := by
      have : (g : ℝ → ℂ) ξ = (Icc (1 : ℝ) 2).indicator (fun _ => (1 : ℂ)) ξ := c
      rw [this, Set.indicator_of_mem hξ]
    rw [a', hg, b, symFun_of_re_nonneg _ (by simp), mul_one] at d
    have hpos : 0 < fracLapSymbol α ξ := by
      unfold fracLapSymbol
      have hξ0 : 0 < ξ := by linarith [hξ.1]
      exact Real.rpow_pos_of_pos (abs_pos.mpr (by positivity)) α
    have hn : ‖Complex.exp (-((1 : ℂ) * (fracLapSymbol α ξ : ℂ)))‖ < 1 := by
      rw [Complex.norm_exp]
      refine Real.exp_lt_one_iff.mpr ?_
      have : (-((1 : ℂ) * (fracLapSymbol α ξ : ℂ))).re = -fracLapSymbol α ξ := by simp
      rw [this]
      linarith
    rw [d, norm_one] at hn
    exact lt_irrefl _ hn
  have h0 : volume (Icc (1 : ℝ) 2) = 0 := measure_eq_zero_iff_ae_notMem.mpr hae
  simp at h0

end

end FracLap
