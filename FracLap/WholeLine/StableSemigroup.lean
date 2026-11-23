/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.FourierSemigroup
public import FracLap.WholeLine.StableHeatKernel
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# FracLap.WholeLine.StableSemigroup

The bridge between the two descriptions of the whole-line fractional heat semigroup: the `L²`
Fourier-multiplier semigroup `fracLapSemigroup α` (symbol `exp (-t |2π ξ|^α)`) and convolution with
the concrete stable kernel `stableHeatKernel α`.

- `memLp_two_convolution_schwartz`: `K ⋆ u ∈ L²` for `K ∈ L¹` and a Schwartz function `u`.
- `fracLapSemigroup_apply_schwartz`: for `0 < α < 2`, `t > 0` and a Schwartz datum `u`,
  `fracLapSemigroup α t u = P_α(·, t) ⋆ u` in `L²(ℝ; ℂ)`.
- `memLp_two_stable_convolution`, `stableConvOp`, `fracLapSemigroup_eq_stableConvOp`,
  `fracLapSemigroup_apply_ae_eq_conv`: extension of the convolution realization from Schwartz
  data to the full Hilbert space `L²(ℝ; ℂ)` (`prop:s_equals_t`).
- `fracLapSemigroup_re_nonneg`, `fracLapSemigroup_re_le`: Markov positivity and `L^∞`
  contractivity on `L²(ℝ; ℂ)` (`thm:s_markov`).
-/

namespace FracLap

open Complex Filter FourierTransform MeasureTheory Real Set Topology
open scoped ENNReal NNReal SchwartzMap ComplexInnerProductSpace Convolution

@[expose] public section

/-- The convolution of an integrable kernel with a Schwartz function is square integrable. -/
theorem memLp_two_convolution_schwartz {K : ℝ → ℂ} (hK : Integrable K volume) (u : 𝓢(ℝ, ℂ)) :
    MemLp (K ⋆[ContinuousLinearMap.mul ℂ ℂ] (u : ℝ → ℂ)) 2 volume := by
  have h1 : Integrable (K ⋆[ContinuousLinearMap.mul ℂ ℂ] (u : ℝ → ℂ)) volume :=
    hK.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) u.integrable
  obtain ⟨C, hC⟩ : ∃ C, ∀ x : ℝ, ‖(u : ℝ → ℂ) x‖ ≤ C :=
    ⟨_, fun x => (u.toBoundedContinuousFunction).norm_coe_le_norm x⟩
  have hbd : ∀ x : ℝ, ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] (u : ℝ → ℂ)) x‖ ≤ (∫ y, ‖K y‖) * C := by
    intro x
    have hKint : Integrable (fun y => ‖K y‖) := hK.norm
    have := norm_integral_le_of_norm_le (hKint.mul_const C)
      (f := fun y => (ContinuousLinearMap.mul ℂ ℂ) (K y) ((u : ℝ → ℂ) (x - y)))
      (Filter.Eventually.of_forall fun y => by
        simp only [ContinuousLinearMap.mul_apply', norm_mul]
        exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
    rw [integral_mul_const] at this
    exact this
  rw [memLp_two_iff_integrable_sq_norm h1.aestronglyMeasurable]
  refine (h1.norm.const_mul ((∫ y, ‖K y‖) * C)).mono' (h1.norm.aestronglyMeasurable.pow 2)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_pow, norm_norm, sq]
  exact mul_le_mul_of_nonneg_right (hbd x) (norm_nonneg _)

/-- **The stable kernel realizes the Fourier-multiplier semigroup**: for `0 < α < 2`, `t > 0` and a
Schwartz datum `u`, the `L²` semigroup `fracLapSemigroup α t` applied to `u` equals the convolution
`P_α(·, t) ⋆ u` with the concrete stable kernel `stableHeatKernel α`. -/
theorem fracLapSemigroup_apply_schwartz {α : ℝ} (hα : FractionalExponent α) {t : ℝ≥0}
    (ht : 0 < (t : ℝ)) (u : 𝓢(ℝ, ℂ)) :
    fracLapSemigroup α t (u.toLp 2) =
      (memLp_two_convolution_schwartz
        (K := fun x : ℝ => (((stableHeatKernel α hα).P x t : ℝ) : ℂ))
        (Complex.ofRealCLM.integrable_comp
          ((stableHeatKernel α hα).integrable_space t ht)) u).toLp
        ((fun x : ℝ => (((stableHeatKernel α hα).P x t : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
          (u : ℝ → ℂ)) := by
  have hK : Integrable (fun x : ℝ => (((stableHeatKernel α hα).P x t : ℝ) : ℂ)) volume :=
    Complex.ofRealCLM.integrable_comp ((stableHeatKernel α hα).integrable_space t ht)
  have hm : ((expMultiplierSymbol (fracLapSymbol α) (measurable_fracLapSymbol α)
      (fracLapSymbol_nonneg α) t : Lp (α := ℝ) ℂ ∞ volume) : ℝ → ℂ) =ᵐ[volume]
      𝓕 (fun x : ℝ => (((stableHeatKernel α hα).P x t : ℝ) : ℂ)) := by
    filter_upwards [coeFn_toLpTop (expSymbol_aestronglyMeasurable (fracLapSymbol α)
      (measurable_fracLapSymbol α) t) zero_le_one
      (norm_expSymbol_le_one (fracLapSymbol α) (fracLapSymbol_nonneg α) t.coe_nonneg)] with ξ h
    have h' : ((expMultiplierSymbol (fracLapSymbol α) (measurable_fracLapSymbol α)
        (fracLapSymbol_nonneg α) t : Lp (α := ℝ) ℂ ∞ volume) : ℝ → ℂ) ξ =
        ((Real.exp (-(t : ℝ) * fracLapSymbol α ξ) : ℝ) : ℂ) := h
    rw [h']
    exact (fourier_stableKernel_eq hα.1 hα.2 ht ξ).symm
  · exact fourierMultiplier_eq_conv_toLp hK hm u (memLp_two_convolution_schwartz hK u)

/-! ### Full `L²(ℝ; ℂ)` convolution realization (`prop:s_equals_t`) and Markov (`thm:s_markov`) -/

/-- For `0 < α < 2` and `t > 0`, the complexified stable kernel `P_α(·, t)` lies in `L²(ℝ; ℂ)`. -/
theorem memLp_two_stableKernel {α : ℝ} (hα : FractionalExponent α) {t : ℝ} (ht : 0 < t) :
    MemLp (fun x : ℝ => ((stableKernel α x t : ℝ) : ℂ)) 2 volume := by
  let K : ℝ → ℂ := fun x => ((stableKernel α x t : ℝ) : ℂ)
  have hK1 : Integrable K volume :=
    Complex.ofRealCLM.integrable_comp ((stableHeatKernel α hα).integrable_space t ht)
  have hK_bd : ∀ x : ℝ, ‖K x‖ ≤ stableKernel α 0 t := fun x => by
    have hnn := stableKernel_nonneg hα.1 hα.2 ht x
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    exact stableKernel_antitone hα.1 hα.2 ht (by simp [abs_nonneg x])
  rw [memLp_two_iff_integrable_sq_norm hK1.aestronglyMeasurable]
  refine (hK1.norm.const_mul (stableKernel α 0 t)).mono'
    (hK1.norm.aestronglyMeasurable.pow 2) (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_pow, norm_norm, sq, mul_comm]
  exact mul_le_mul_of_nonneg_right (hK_bd x) (norm_nonneg _)

/-- For `0 < α < 2`, `t > 0`, and any `f ∈ L²(ℝ; ℂ)`, convolution with `stableKernel α · t` lies
in `L²(ℝ; ℂ)` with `eLpNorm` bounded by `eLpNorm f 2`. -/
theorem memLp_two_stable_convolution {α : ℝ} (hα : FractionalExponent α) {t : ℝ} (ht : 0 < t)
    (f : L2C) :
    MemLp ((fun x : ℝ => ((stableKernel α x t : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
      (f : ℝ → ℂ)) 2 volume ∧
      eLpNorm ((fun x : ℝ => ((stableKernel α x t : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (f : ℝ → ℂ)) 2 volume ≤ eLpNorm (f : ℝ → ℂ) 2 volume := by
  let K : ℝ → ℂ := fun x => ((stableKernel α x t : ℝ) : ℂ)
  have hK_meas : AEStronglyMeasurable K volume :=
    (Complex.continuous_ofReal.comp (continuous_stableKernel hα.1 ht)).aestronglyMeasurable
  have hf_meas : AEStronglyMeasurable (f : ℝ → ℂ) volume := Lp.aestronglyMeasurable f
  have hKf_meas : AEStronglyMeasurable (K ⋆[ContinuousLinearMap.mul ℂ ℂ] (f : ℝ → ℂ)) volume :=
    hK_meas.convolution (ContinuousLinearMap.mul ℂ ℂ) hf_meas
  have hK_enorm : ∫⁻ y : ℝ, ‖K y‖ₑ = 1 := by
    have hnn : ∀ y : ℝ, 0 ≤ stableKernel α y t := fun y => stableKernel_nonneg hα.1 hα.2 ht y
    have heq : (fun y : ℝ => ‖K y‖ₑ) = fun y : ℝ => ENNReal.ofReal (stableKernel α y t) := by
      ext y
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hnn y)]
    rw [heq, ← ofReal_integral_eq_lintegral_ofReal
      (integrable_stableKernel hα.1 hα.2 ht) (Filter.Eventually.of_forall hnn),
      integral_stableKernel_eq_one hα.1 hα.2 ht, ENNReal.ofReal_one]
  have hKm : AEMeasurable (fun y => ‖K y‖ₑ) volume := hK_meas.aemeasurable.eNorm
  have hp2 : (2 : ℝ).HolderConjugate 2 := by
    constructor <;> norm_num
  have hpt : ∀ x : ℝ, ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] (f : ℝ → ℂ)) x‖ₑ ^ (2 : ℝ) ≤
      1 * ∫⁻ y, ‖K y‖ₑ * ‖(f : ℝ → ℂ) (x - y)‖ₑ ^ (2 : ℝ) := by
    intro x
    have h1 : ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] (f : ℝ → ℂ)) x‖ₑ ≤
        ∫⁻ y, ‖K y‖ₑ * ‖(f : ℝ → ℂ) (x - y)‖ₑ := by
      refine (eNorm_integral_le_lintegral_eNorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun y => ?_
      simp [eNorm_mul]
    have hfx : AEMeasurable (fun y => ‖(f : ℝ → ℂ) (x - y)‖ₑ) volume :=
      (hf_meas.comp_quasiMeasurePreserving
        (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving).aemeasurable.eNorm
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hp2
      (f := fun y => ‖(f : ℝ → ℂ) (x - y)‖ₑ * ‖K y‖ₑ ^ (1 / (2 : ℝ)))
      (g := fun y => ‖K y‖ₑ ^ (1 / (2 : ℝ)))
      (hfx.mul (hKm.pow_const _)) (hKm.pow_const _)
    have e1 : ∀ y : ℝ, (‖(f : ℝ → ℂ) (x - y)‖ₑ * ‖K y‖ₑ ^ (1 / (2 : ℝ))) *
        ‖K y‖ₑ ^ (1 / (2 : ℝ)) = ‖K y‖ₑ * ‖(f : ℝ → ℂ) (x - y)‖ₑ := fun y => by
      rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity),
        show (1 / (2 : ℝ)) + 1 / 2 = 1 by norm_num, ENNReal.rpow_one, mul_comm]
    have e2 : ∀ y : ℝ, (‖(f : ℝ → ℂ) (x - y)‖ₑ * ‖K y‖ₑ ^ (1 / (2 : ℝ))) ^ (2 : ℝ) =
        ‖K y‖ₑ * ‖(f : ℝ → ℂ) (x - y)‖ₑ ^ (2 : ℝ) := fun y => by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
        show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one, mul_comm]
    have e3 : ∀ y : ℝ, (‖K y‖ₑ ^ (1 / (2 : ℝ))) ^ (2 : ℝ) = ‖K y‖ₑ := fun y => by
      rw [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one]
    simp only [Pi.mul_apply, e1, e2, e3] at hH
    have hΨ := ENNReal.rpow_le_rpow (h1.trans hH) (by norm_num : (0 : ℝ) ≤ 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_one,
      hK_enorm, mul_one] at hΨ
    simpa only [one_mul] using hΨ
  have hYoung : ∫⁻ x, ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] (f : ℝ → ℂ)) x‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) := by
    calc
      ∫⁻ x, ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] (f : ℝ → ℂ)) x‖ₑ ^ (2 : ℝ)
          ≤ ∫⁻ x, 1 * ∫⁻ y, ‖K y‖ₑ * ‖(f : ℝ → ℂ) (x - y)‖ₑ ^ (2 : ℝ) := lintegral_mono hpt
      _ = ∫⁻ x, ∫⁻ y, ‖K y‖ₑ * ‖(f : ℝ → ℂ) (x - y)‖ₑ ^ (2 : ℝ) := by simp_rw [one_mul]
      _ = ∫⁻ y, ∫⁻ x, ‖K y‖ₑ * ‖(f : ℝ → ℂ) (x - y)‖ₑ ^ (2 : ℝ) := by
          have hm : AEMeasurable (Function.uncurry fun x y : ℝ =>
              ‖K y‖ₑ * ‖(f : ℝ → ℂ) (x - y)‖ₑ ^ (2 : ℝ)) (volume.prod volume) :=
            (hKm.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_snd)).mul
              (((hf_meas.comp_quasiMeasurePreserving
                (quasiMeasurePreserving_sub volume volume)).aemeasurable.eNorm).pow_const 2)
          exact lintegral_lintegral_swap hm
      _ = ∫⁻ y, ‖K y‖ₑ * ∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) := by
          refine lintegral_congr fun y => ?_
          rw [lintegral_const_mul' _ _ eNorm_ne_top]
          congr 1
          exact lintegral_sub_right_eq_self (fun x => ‖(f : ℝ → ℂ) x‖ₑ ^ (2 : ℝ)) y
      _ = (∫⁻ y, ‖K y‖ₑ) * ∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) :=
          lintegral_mul_const'' _ hKm
      _ = ∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) := by rw [hK_enorm, one_mul]
  have heLp_le : eLpNorm (K ⋆[ContinuousLinearMap.mul ℂ ℂ] (f : ℝ → ℂ)) 2 volume ≤
      eLpNorm (f : ℝ → ℂ) 2 volume := by
    have h1 := lintegral_rpow_eNorm_eq_rpow_eLpNorm' (μ := volume)
      (f := K ⋆[ContinuousLinearMap.mul ℂ ℂ] (f : ℝ → ℂ)) two_pos
    have h2 := lintegral_rpow_eNorm_eq_rpow_eLpNorm' (μ := volume)
      (f := (f : ℝ → ℂ)) two_pos
    rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top,
      eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top]
    · simp only [ENNReal.toReal_ofNat]
      refine (ENNReal.rpow_le_rpow_iff two_pos).mp ?_
      rw [← h1, ← h2]
      exact hYoung
    · exact hf_meas
    · exact hKf_meas
  exact ⟨lt_of_le_of_lt heLp_le (Lp.eLpNorm_lt_top f), heLp_le⟩

/-- Convolution with `stableKernel α · t` as an `ℝ`-linear contraction on `L²(ℝ; ℂ)`. -/
noncomputable def stableConvOp (α : ℝ) (hα : FractionalExponent α) {t : ℝ} (ht : 0 < t) :
    L2C →L[ℝ] L2C :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        (memLp_two_stable_convolution hα ht f).1.toLp
          ((fun x : ℝ => ((stableKernel α x t : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
            (f : ℝ → ℂ))
      map_add' := fun f g => by
        let K : ℝ → ℂ := fun x => ((stableKernel α x t : ℝ) : ℂ)
        have hK2 : MemLp K 2 volume := memLp_two_stableKernel hα ht
        have hex_f := ConvolutionExists.of_memLp_memLp (L := ContinuousLinearMap.mul ℂ ℂ) hK2
          (Lp.memLp f)
        have hex_g := ConvolutionExists.of_memLp_memLp (L := ContinuousLinearMap.mul ℂ ℂ) hK2
          (Lp.memLp g)
        rw [Lp.ext_iff]
        filter_upwards [(memLp_two_stable_convolution hα ht (f + g)).1.coeFn_toLp,
          Lp.coeFn_add
            ((memLp_two_stable_convolution hα ht f).1.toLp
              (K ⋆[ContinuousLinearMap.mul ℂ ℂ] (f : ℝ → ℂ)))
            ((memLp_two_stable_convolution hα ht g).1.toLp
              (K ⋆[ContinuousLinearMap.mul ℂ ℂ] (g : ℝ → ℂ))),
          (memLp_two_stable_convolution hα ht f).1.coeFn_toLp,
          (memLp_two_stable_convolution hα ht g).1.coeFn_toLp] with x h1 h2 h3 h4
        have hfg :
            (K ⋆[ContinuousLinearMap.mul ℂ ℂ] ((f + g : L2C) : ℝ → ℂ)) x =
              (K ⋆[ContinuousLinearMap.mul ℂ ℂ] ((f : ℝ → ℂ) + (g : ℝ → ℂ))) x :=
          congrFun (convolution_congr (ContinuousLinearMap.mul ℂ ℂ) EventuallyEq.rfl
            (Lp.coeFn_add f g)) x
        rw [h1, hfg, (hex_f x).distrib_add (hex_g x), h2, Pi.add_apply, h3, h4]
      map_smul' := fun c f => by
        let K : ℝ → ℂ := fun x => ((stableKernel α x t : ℝ) : ℂ)
        rw [Lp.ext_iff, RingHom.id_apply]
        filter_upwards [(memLp_two_stable_convolution hα ht (c • f)).1.coeFn_toLp,
          Lp.coeFn_smul c
            ((memLp_two_stable_convolution hα ht f).1.toLp
              (K ⋆[ContinuousLinearMap.mul ℂ ℂ] (f : ℝ → ℂ))),
          (memLp_two_stable_convolution hα ht f).1.coeFn_toLp] with x h1 h2 h3
        have hcf :
            (K ⋆[ContinuousLinearMap.mul ℂ ℂ] ((c • f : L2C) : ℝ → ℂ)) x =
              (K ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun y => (c : ℂ) * (f : ℝ → ℂ) y)) x := by
          refine congrFun (convolution_congr (ContinuousLinearMap.mul ℂ ℂ) EventuallyEq.rfl ?_) x
          filter_upwards [Lp.coeFn_smul c f] with y hy
          exact hy
        have hsm :
            (K ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun y => (c : ℂ) * (f : ℝ → ℂ) y)) x =
              (c : ℂ) * (K ⋆[ContinuousLinearMap.mul ℂ ℂ] (f : ℝ → ℂ)) x :=
          congrFun (convolution_smul (L := ContinuousLinearMap.mul ℂ ℂ) (f := K)
            (g := (f : ℝ → ℂ)) (y := (c : ℂ))) x
        rw [h1, hcf, hsm, h2, Pi.smul_apply, h3]
        rfl }
    1
    (fun f => by
      change ‖(memLp_two_stable_convolution hα ht f).1.toLp _‖ ≤ 1 * ‖f‖
      rw [one_mul, Lp.norm_def, Lp.norm_def,
        eLpNorm_congr_ae (memLp_two_stable_convolution hα ht f).1.coeFn_toLp]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
        (memLp_two_stable_convolution hα ht f).2)

/-- **Whole-Line Semigroup–Kernel Identity (`prop:s_equals_t`)**: for all `0 < α < 2` and
`t > 0`, `fracLapSemigroup α t = stableConvOp α hα ht` on the entire Hilbert space `L²(ℝ; ℂ)`. -/
theorem fracLapSemigroup_eq_stableConvOp {α : ℝ} (hα : FractionalExponent α) {t : ℝ≥0}
    (ht : 0 < (t : ℝ)) :
    fracLapSemigroup α t = stableConvOp α hα ht := by
  ext1 f
  refine congrFun ((SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2)
    ENNReal.ofNat_ne_top).equalizer (fracLapSemigroup α t).continuous
      (stableConvOp α hα ht).continuous ?_) f
  ext1 u
  let hK_int : Integrable (fun x : ℝ => (((stableHeatKernel α hα).P x t : ℝ) : ℂ)) volume :=
    Complex.ofRealCLM.integrable_comp ((stableHeatKernel α hα).integrable_space t ht)
  change fracLapSemigroup α t (u.toLp 2) = stableConvOp α hα ht (u.toLp 2)
  rw [fracLapSemigroup_apply_schwartz hα ht u]
  change (memLp_two_convolution_schwartz hK_int u).toLp _ = stableConvOp α hα ht (u.toLp 2)
  rw [Lp.ext_iff]
  filter_upwards [(memLp_two_convolution_schwartz hK_int u).coeFn_toLp,
    (memLp_two_stable_convolution hα ht (u.toLp 2)).1.coeFn_toLp] with x h1 h2
  have hconv :
      ((fun y : ℝ => (((stableHeatKernel α hα).P y t : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
          (u : ℝ → ℂ)) x =
        ((fun y : ℝ => ((stableKernel α y t : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
          ((u.toLp 2 : L2C) : ℝ → ℂ)) x :=
    congrFun (convolution_congr (ContinuousLinearMap.mul ℂ ℂ) EventuallyEq.rfl
      (u.coeFn_toLp 2 volume).symm) x
  have h1' : ((memLp_two_convolution_schwartz hK_int u).toLp
      ((fun y : ℝ => (((stableHeatKernel α hα).P y t : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (u : ℝ → ℂ)) : ℝ → ℂ) x =
      ((fun y : ℝ => (((stableHeatKernel α hα).P y t : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (u : ℝ → ℂ)) x := h1
  have h2' : ((stableConvOp α hα ht (u.toLp 2) : L2C) : ℝ → ℂ) x =
      ((fun y : ℝ => ((stableKernel α y t : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        ((u.toLp 2 : L2C) : ℝ → ℂ)) x := h2
  rw [h1', h2', hconv]

/-- **Pointwise a.e. convolution formula on all of `L²(ℝ; ℂ)` (`prop:s_equals_t`)**: for all
`0 < α < 2`, `t > 0`, `f ∈ L²(ℝ; ℂ)`,
`(fracLapSemigroup α t f) x = ∫ P_α(x - y, t) f(y) dy` a.e. -/
theorem fracLapSemigroup_apply_ae_eq_conv {α : ℝ} (hα : FractionalExponent α) {t : ℝ≥0}
    (ht : 0 < (t : ℝ)) (f : L2C) :
    (fracLapSemigroup α t f : ℝ → ℂ) =ᵐ[volume]
      ((fun x : ℝ => ((stableKernel α x t : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (f : ℝ → ℂ)) := by
  rw [fracLapSemigroup_eq_stableConvOp hα ht]
  exact (memLp_two_stable_convolution hα ht f).1.coeFn_toLp

/-- **Markov Positivity and Reality Preservation (`thm:s_markov`)**: if `f ∈ L²(ℝ; ℂ)` is
real-valued and `0 ≤ (f x).re` a.e., then `fracLapSemigroup α t f` is real-valued and nonnegative
a.e. for all `t ≥ 0`. -/
theorem fracLapSemigroup_re_nonneg {α : ℝ} (hα : FractionalExponent α) (t : ℝ≥0) {f : L2C}
    (hf_real : ∀ᵐ x : ℝ ∂volume, ((f : ℝ → ℂ) x).im = 0)
    (hf_nn : ∀ᵐ x : ℝ ∂volume, 0 ≤ ((f : ℝ → ℂ) x).re) :
    (∀ᵐ x : ℝ ∂volume, ((fracLapSemigroup α t f : ℝ → ℂ) x).im = 0) ∧
      (∀ᵐ x : ℝ ∂volume, 0 ≤ ((fracLapSemigroup α t f : ℝ → ℂ) x).re) := by
  by_cases ht : (t : ℝ) = 0
  · have ht0 : t = 0 := NNReal.eq ht
    subst ht0
    rw [(fracLapSemigroup α).zero_apply]
    exact ⟨hf_real, hf_nn⟩
  · have htp : 0 < (t : ℝ) := lt_of_le_of_ne t.coe_nonneg (Ne.symm ht)
    let K : ℝ → ℂ := fun x => ((stableKernel α x t : ℝ) : ℂ)
    have hK2 : MemLp K 2 volume := memLp_two_stableKernel hα htp
    have hex := ConvolutionExists.of_memLp_memLp (L := ContinuousLinearMap.mul ℂ ℂ) hK2 (Lp.memLp f)
    have hre : ∀ x : ℝ,
        0 ≤ ((K ⋆[ContinuousLinearMap.mul ℂ ℂ] (f : ℝ → ℂ)) x).re := fun x => by
      have hint : Integrable (fun y : ℝ => K y * (f : ℝ → ℂ) (x - y)) volume := hex x
      rw [convolution_mul, ← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hint]
      simp only [Complex.reCLM_apply]
      refine integral_nonneg_of_ae ?_
      have hf_nn' := (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae hf_nn
      filter_upwards [hf_nn'] with y hy
      simp only [K, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg (stableKernel_nonneg hα.1 hα.2 htp y) hy
    have him : ∀ x : ℝ,
        ((K ⋆[ContinuousLinearMap.mul ℂ ℂ] (f : ℝ → ℂ)) x).im = 0 := fun x => by
      have hint : Integrable (fun y : ℝ => K y * (f : ℝ → ℂ) (x - y)) volume := hex x
      rw [convolution_mul, ← Complex.imCLM_apply, ← Complex.imCLM.integral_comp_comm hint]
      simp only [Complex.imCLM_apply]
      refine integral_eq_zero_of_ae ?_
      have hf_real' :=
        (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae hf_real
      filter_upwards [hf_real'] with y hy
      simp only [K, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hy,
        mul_zero, Pi.zero_apply]
    refine ⟨?_, ?_⟩
    · filter_upwards [fracLapSemigroup_apply_ae_eq_conv hα htp f] with x hx
      rw [hx, him x]
    · filter_upwards [fracLapSemigroup_apply_ae_eq_conv hα htp f] with x hx
      rw [hx]
      exact hre x

/-- **Markov `L^∞`-Contractivity (`thm:s_markov`)**: if `f ∈ L²(ℝ; ℂ)` satisfies `(f x).re ≤ M`
a.e., then `(fracLapSemigroup α t f x).re ≤ M` a.e. for all `t ≥ 0`. -/
theorem fracLapSemigroup_re_le {α : ℝ} (hα : FractionalExponent α) (t : ℝ≥0) {M : ℝ}
    {f : L2C}
    (hf_le : ∀ᵐ x : ℝ ∂volume, ((f : ℝ → ℂ) x).re ≤ M) :
    ∀ᵐ x : ℝ ∂volume, ((fracLapSemigroup α t f : ℝ → ℂ) x).re ≤ M := by
  by_cases ht : (t : ℝ) = 0
  · have ht0 : t = 0 := NNReal.eq ht
    subst ht0
    simpa only [(fracLapSemigroup α).zero_apply] using hf_le
  · have htp : 0 < (t : ℝ) := lt_of_le_of_ne t.coe_nonneg (Ne.symm ht)
    let K : ℝ → ℂ := fun x => ((stableKernel α x t : ℝ) : ℂ)
    have hK2 : MemLp K 2 volume := memLp_two_stableKernel hα htp
    have hex := ConvolutionExists.of_memLp_memLp (L := ContinuousLinearMap.mul ℂ ℂ) hK2 (Lp.memLp f)
    have hK_int : Integrable (fun y : ℝ => stableKernel α y t) volume :=
      (stableHeatKernel α hα).integrable_space t htp
    filter_upwards [fracLapSemigroup_apply_ae_eq_conv hα htp f] with x hx
    rw [hx]
    have hint : Integrable (fun y : ℝ => K y * (f : ℝ → ℂ) (x - y)) volume := hex x
    rw [convolution_mul, ← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hint]
    simp only [Complex.reCLM_apply]
    have hf_le' := (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae hf_le
    calc
      ∫ y : ℝ, (K y * (f : ℝ → ℂ) (x - y)).re
          ≤ ∫ y : ℝ, stableKernel α y t * M := by
        refine integral_mono_ae ?_ (hK_int.mul_const M) ?_
        · exact hint.re
        · filter_upwards [hf_le'] with y hy
          simp only [K, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
          exact mul_le_mul_of_nonneg_left hy (stableKernel_nonneg hα.1 hα.2 htp y)
      _ = M := by
        rw [integral_mul_const, integral_stableKernel_eq_one hα.1 hα.2 htp, one_mul]

end

end FracLap
