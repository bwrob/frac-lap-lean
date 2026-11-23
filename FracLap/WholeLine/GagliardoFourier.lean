/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.HalfLine.RestrictedDirichlet
public import FracLap.WholeLine.TranslationFourier
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLap.WholeLine.GagliardoFourier

Fourier-side description of the Gagliardo energy and density of Schwartz functions in
`H^(α / 2)(ℝ)`, following Di Nezza–Palatucci–Valdinoci (*Hitchhiker's guide*, Prop. 3.4) but
avoiding the closed form `|ξ|^α` of the symbol:
- `gagliardoSymbol`: `Λ_α(ξ) = ∫ w(h) ‖𝐞(h ξ) - 1‖² dh`, with `measurable_gagliardoSymbol` and the
  polynomial bound `one_add_gagliardoSymbol_le`.
- `lintegral_gagliardo_energy_eq_complex`, `lintegral_gagliardo_energy_fourier`:
  `∬ w ‖f(x) - f(y)‖² = ∫ Λ_α ‖𝓕 f‖²` for `f ∈ L²(ℝ; ℂ)`.
- `gagliardoSpectralMeasure`: `(1 + Λ_α) dξ`, with temperate growth and finiteness on compacts.
- `norm_sq_add_energy_eq`: `‖f‖² + E_α(f) = ∫ ‖𝓕 f‖² dν_α`.
- `exists_schwartz_close_complex`: Schwartz functions are dense in `H^(α / 2)(ℝ; ℂ)`.
-/

namespace FracLap

open Complex Filter FourierTransform MeasureTheory Real Set Topology
open scoped ENNReal NNReal ComplexInnerProductSpace SchwartzMap

@[expose] public section

/-- Complex-valued version of `lintegral_gagliardo_energy_eq`. -/
theorem lintegral_gagliardo_energy_eq_complex (α : ℝ) {g : ℝ → ℂ} (hg : Measurable g) :
    ∫⁻ p : ℝ × ℝ, gagliardoWeight α p * ‖g p.1 - g p.2‖ₑ ^ (2 : ℝ)
      ∂((volume : Measure ℝ).prod volume) =
      ∫⁻ h : ℝ, gagliardoWeight α (h, 0) * ∫⁻ y, ‖g (y + h) - g y‖ₑ ^ (2 : ℝ) := by
  have hdiff : Measurable fun p : ℝ × ℝ => ‖g p.1 - g p.2‖ₑ ^ (2 : ℝ) :=
    (((hg.comp measurable_fst).sub (hg.comp measurable_snd)).eNorm).pow_const _
  have hf : Measurable fun p : ℝ × ℝ => gagliardoWeight α p * ‖g p.1 - g p.2‖ₑ ^ (2 : ℝ) :=
    (measurable_gagliardoWeight α).mul hdiff
  have hWm : Measurable fun h : ℝ => gagliardoWeight α (h, 0) :=
    (measurable_gagliardoWeight α).comp (measurable_id.prodMk measurable_const)
  set G : ℝ → ℝ → ℝ≥0∞ :=
    fun y h => gagliardoWeight α (h, 0) * ‖g (h + y) - g y‖ₑ ^ (2 : ℝ) with hG
  have hGm : Measurable (Function.uncurry G) := by
    simp only [hG]
    refine hWm.comp measurable_snd |>.mul ?_
    exact (((hg.comp (measurable_snd.add measurable_fst)).sub
      (hg.comp measurable_fst)).eNorm).pow_const _
  have step1 : ∫⁻ p : ℝ × ℝ, gagliardoWeight α p * ‖g p.1 - g p.2‖ₑ ^ (2 : ℝ)
        ∂((volume : Measure ℝ).prod volume) = ∫⁻ y, ∫⁻ h, G y h := by
    rw [lintegral_prod_symm _ hf.aemeasurable]
    refine lintegral_congr fun y => ?_
    rw [← lintegral_sub_right_eq_self (fun h => G y h) y]
    refine lintegral_congr fun x => ?_
    simp only [hG, gagliardoWeight, sub_zero, sub_add_cancel]
  rw [step1, lintegral_lintegral_swap hGm.aemeasurable]
  refine lintegral_congr fun h => ?_
  have hm : Measurable fun y : ℝ => ‖g (h + y) - g y‖ₑ ^ (2 : ℝ) :=
    (((hg.comp (measurable_const.add measurable_id)).sub hg).eNorm).pow_const _
  simp only [hG]
  rw [lintegral_const_mul _ hm]
  simp only [add_comm h]

/-- The Fourier-side weight of the Gagliardo energy:
`Λ_α(ξ) = ∫ w(h) ‖𝐞(h ξ) - 1‖² dh`, with `w(h) = C(α) / (2 |h|^(1 + α))`. -/
noncomputable def gagliardoSymbol (α ξ : ℝ) : ℝ≥0∞ :=
  ∫⁻ h : ℝ, gagliardoWeight α (h, 0) * ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ)

/-- Measurability of the Fourier-side weight. -/
theorem measurable_gagliardoSymbol (α : ℝ) : Measurable (gagliardoSymbol α) := by
  unfold gagliardoSymbol
  have hWm : Measurable fun h : ℝ => gagliardoWeight α (h, 0) :=
    (measurable_gagliardoWeight α).comp (measurable_id.prodMk measurable_const)
  have hphase : Measurable fun q : ℝ × ℝ => ((𝐞 (q.2 * q.1) : Circle) : ℂ) :=
    (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (continuous_snd.mul continuous_fst))).measurable
  refine Measurable.lintegral_prod_right' (f := fun q : ℝ × ℝ =>
    gagliardoWeight α (q.2, 0) * ‖((𝐞 (q.2 * q.1) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ)) ?_
  exact (hWm.comp measurable_snd).mul (((hphase.sub measurable_const).eNorm).pow_const _)

/-- **Fourier formula for the Gagliardo energy**: for `f ∈ L²(ℝ; ℂ)`,
`∬ w(x - y) ‖f(x) - f(y)‖² dx dy = ∫ Λ_α(ξ) ‖𝓕 f(ξ)‖² dξ` in `[0, ∞]`. -/
theorem lintegral_gagliardo_energy_fourier (α : ℝ) (f : L2C) :
    ∫⁻ p : ℝ × ℝ, gagliardoWeight α p * ‖(f : ℝ → ℂ) p.1 - (f : ℝ → ℂ) p.2‖ₑ ^ (2 : ℝ)
      ∂((volume : Measure ℝ).prod volume) =
      ∫⁻ ξ, gagliardoSymbol α ξ * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) := by
  have hf : Measurable (f : ℝ → ℂ) := (Lp.stronglyMeasurable f).measurable
  have hFf : Measurable ((𝓕 f : L2C) : ℝ → ℂ) := (Lp.stronglyMeasurable (𝓕 f : L2C)).measurable
  have hWm : Measurable fun h : ℝ => gagliardoWeight α (h, 0) :=
    (measurable_gagliardoWeight α).comp (measurable_id.prodMk measurable_const)
  have hphase : Measurable fun q : ℝ × ℝ => ((𝐞 (q.1 * q.2) : Circle) : ℂ) :=
    (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (continuous_fst.mul continuous_snd))).measurable
  rw [lintegral_gagliardo_energy_eq_complex α hf]
  have step : ∀ h : ℝ, gagliardoWeight α (h, 0) *
      ∫⁻ y, ‖(f : ℝ → ℂ) (y + h) - (f : ℝ → ℂ) y‖ₑ ^ (2 : ℝ)
      = ∫⁻ ξ, gagliardoWeight α (h, 0) *
        (‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ₑ ^ (2 : ℝ) * ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ)) := by
    intro h
    rw [lintegral_enorm_sq_translate_sub h f, lintegral_const_mul]
    exact ((((hphase.comp (measurable_const.prodMk measurable_id)).sub
      measurable_const).eNorm).pow_const _).mul
      (hFf.eNorm.pow_const _)
  simp_rw [step]
  rw [lintegral_lintegral_swap]
  · refine lintegral_congr fun ξ => ?_
    unfold gagliardoSymbol
    rw [← lintegral_mul_const]
    · refine lintegral_congr fun h => ?_
      ring
    · exact hWm.mul (((hphase.comp (measurable_id.prodMk measurable_const)).sub
        measurable_const).eNorm.pow_const _)
  · refine Measurable.aemeasurable ?_
    refine (hWm.comp measurable_fst).mul ?_
    refine ((((hphase.sub measurable_const).eNorm).pow_const _)).mul ?_
    exact (hFf.comp measurable_snd).eNorm.pow_const _

/-- For a complex number, `‖z‖ₑ ^ 2 = ofReal (‖z‖ ^ 2)`. -/
theorem enorm_rpow_two_eq_ofReal {E : Type*} [SeminormedAddGroup E] (z : E) :
    ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  norm_cast

/-- The squared chord `‖𝐞(h ξ) - 1‖²` is at most `4 π² (1 + ξ²) min(h², 1)`. -/
theorem norm_fourierChar_sub_one_sq_le (h ξ : ℝ) :
    ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ ^ 2 ≤ 4 * π ^ 2 * (1 + ξ ^ 2) * min (h ^ 2) 1 := by
  have hexp : ((𝐞 (h * ξ) : Circle) : ℂ) =
      Complex.exp (Complex.I * ((2 * π * (h * ξ) : ℝ) : ℂ)) := by
    rw [Real.fourierChar_apply, mul_comm]
  have h1 : ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ ≤ |2 * π * (h * ξ)| := by
    rw [hexp]
    simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * π * (h * ξ))
  have h2 : ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ ≤ 2 := by
    calc ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ ≤ ‖((𝐞 (h * ξ) : Circle) : ℂ)‖ + ‖(1 : ℂ)‖ :=
          norm_sub_le _ _
      _ = 2 := by rw [Circle.norm_coe]; norm_num
  have hpi : 1 ≤ π := by linarith [Real.two_le_pi]
  have hn : 0 ≤ ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ := norm_nonneg _
  rcases le_total (h ^ 2) 1 with hh | hh
  · rw [min_eq_left hh]
    have : ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ ^ 2 ≤ |2 * π * (h * ξ)| ^ 2 :=
      pow_le_pow_left₀ hn h1 2
    rw [sq_abs] at this
    calc _ ≤ (2 * π * (h * ξ)) ^ 2 := this
      _ = 4 * π ^ 2 * (h ^ 2 * ξ ^ 2) := by ring
      _ ≤ 4 * π ^ 2 * (1 + ξ ^ 2) * h ^ 2 := by nlinarith [sq_nonneg ξ, sq_nonneg h, sq_nonneg π]
      _ = _ := by ring
  · rw [min_eq_right hh]
    have : ‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ hn h2 2
    nlinarith [sq_nonneg ξ, sq_nonneg π]

/-- The Gagliardo weight times `ofReal x` is `ofReal` of the real product. -/
theorem gagliardoWeight_mul_ofReal {α : ℝ} (hα : FractionalExponent α) (h x : ℝ) :
    gagliardoWeight α (h, 0) * ENNReal.ofReal x =
      ENNReal.ofReal (fracLapConstant α / (2 * |h| ^ (1 + α)) * x) := by
  have hC := fracLapConstant_pos hα
  have hnn : 0 ≤ fracLapConstant α / (2 * |h| ^ (1 + α)) := by positivity
  simp only [gagliardoWeight, sub_zero]
  rw [← ENNReal.ofReal_mul hnn]

/-- **Polynomial bound on the Fourier-side weight**: `Λ_α(ξ) ≤ 4 π² (1 + ξ²) ∫ k_α`. -/
theorem gagliardoSymbol_le {α : ℝ} (hα : FractionalExponent α) (ξ : ℝ) :
    gagliardoSymbol α ξ ≤
      ENNReal.ofReal (4 * π ^ 2 * (1 + ξ ^ 2)) * ∫⁻ h, gagliardoKernel α h := by
  unfold gagliardoSymbol
  rw [← lintegral_const_mul _ (measurable_gagliardoKernel α)]
  refine lintegral_mono fun h => ?_
  rw [enorm_rpow_two_eq_ofReal]
  have hb := norm_fourierChar_sub_one_sq_le h ξ
  have hmin : 0 ≤ min (h ^ 2) 1 := le_min (sq_nonneg h) zero_le_one
  calc gagliardoWeight α (h, 0) * ENNReal.ofReal (‖((𝐞 (h * ξ) : Circle) : ℂ) - 1‖ ^ 2)
      ≤ gagliardoWeight α (h, 0) * ENNReal.ofReal (4 * π ^ 2 * (1 + ξ ^ 2) * min (h ^ 2) 1) := by
        gcongr
    _ = ENNReal.ofReal (4 * π ^ 2 * (1 + ξ ^ 2)) * gagliardoKernel α h := by
        rw [gagliardoWeight_mul_ofReal hα h _, gagliardoKernel,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- The constant in the polynomial bound `1 + Λ_α(ξ) ≤ C (1 + ξ²)`. -/
noncomputable def gagliardoSymbolConst (α : ℝ) : ℝ :=
  1 + 4 * π ^ 2 * (∫⁻ h, gagliardoKernel α h).toReal

/-- The polynomial-bound constant is at least `1`. -/
theorem one_le_gagliardoSymbolConst (α : ℝ) : 1 ≤ gagliardoSymbolConst α := by
  unfold gagliardoSymbolConst
  have h0 : 0 ≤ (∫⁻ h, gagliardoKernel α h).toReal := ENNReal.toReal_nonneg
  nlinarith [sq_nonneg π, mul_nonneg (sq_nonneg π) h0]

/-- **Polynomial bound**: `1 + Λ_α(ξ) ≤ C (1 + ξ²)`. -/
theorem one_add_gagliardoSymbol_le {α : ℝ} (hα : FractionalExponent α) (ξ : ℝ) :
    1 + gagliardoSymbol α ξ ≤ ENNReal.ofReal (gagliardoSymbolConst α * (1 + ξ ^ 2)) := by
  have hK : (∫⁻ h, gagliardoKernel α h) = ENNReal.ofReal (∫⁻ h, gagliardoKernel α h).toReal :=
    (ENNReal.ofReal_toReal (lintegral_gagliardoKernel_lt_top hα).ne).symm
  set K := (∫⁻ h, gagliardoKernel α h).toReal with hKdef
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  calc 1 + gagliardoSymbol α ξ
      ≤ 1 + ENNReal.ofReal (4 * π ^ 2 * (1 + ξ ^ 2)) * ENNReal.ofReal K := by
        gcongr
        exact (gagliardoSymbol_le hα ξ).trans_eq (by rw [hK])
    _ = ENNReal.ofReal (1 + 4 * π ^ 2 * (1 + ξ ^ 2) * K) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add zero_le_one (by positivity)]
    _ ≤ ENNReal.ofReal (gagliardoSymbolConst α * (1 + ξ ^ 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        unfold gagliardoSymbolConst
        nlinarith [sq_nonneg ξ, mul_nonneg (sq_nonneg π) hK0,
          mul_nonneg (mul_nonneg (sq_nonneg π) hK0) (sq_nonneg ξ)]

/-- The spectral measure `(1 + Λ_α(ξ)) dξ` carrying the `H^(α / 2)` norm on the Fourier side. -/
noncomputable def gagliardoSpectralMeasure (α : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity fun ξ => 1 + gagliardoSymbol α ξ

/-- `ν`-density bound: `(1 + x²) (1 + |x|)^(-4) ≤ (1 + |x|)^(-2)`. -/
theorem one_add_sq_mul_rpow_le (x : ℝ) :
    (1 + x ^ 2) * (1 + |x|) ^ (-(4 : ℝ)) ≤ (1 + |x|) ^ (-(2 : ℝ)) := by
  have ht : 0 < 1 + |x| := by positivity
  rw [Real.rpow_neg ht.le, Real.rpow_neg ht.le,
    show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, Real.rpow_natCast]
  calc (1 + x ^ 2) * ((1 + |x|) ^ 4)⁻¹ ≤ (1 + |x|) ^ 2 * ((1 + |x|) ^ 4)⁻¹ := by
        gcongr
        nlinarith [sq_abs x, abs_nonneg x]
    _ = ((1 + |x|) ^ 2)⁻¹ := by field_simp

/-- The spectral measure has temperate growth. -/
theorem gagliardoSpectralMeasure_hasTemperateGrowth {α : ℝ} (hα : FractionalExponent α) :
    (gagliardoSpectralMeasure α).HasTemperateGrowth := by
  refine ⟨⟨4, ?_⟩⟩
  have hmeas : Measurable fun ξ : ℝ => 1 + gagliardoSymbol α ξ :=
    measurable_const.add (measurable_gagliardoSymbol α)
  have hcont : Continuous fun x : ℝ => (1 + ‖x‖) ^ (-((4 : ℕ) : ℝ)) :=
    (continuous_const.add continuous_norm).rpow_const fun x =>
      Or.inl (by change (1 + ‖x‖) ≠ 0; positivity)
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  unfold gagliardoSpectralMeasure
  rw [HasFiniteIntegral]
  have hm : Measurable fun x : ℝ => ‖(1 + ‖x‖) ^ (-((4 : ℕ) : ℝ))‖ₑ := hcont.measurable.eNorm
  rw [lintegral_withDensity_eq_lintegral_mul _ hmeas hm]
  have hint : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(2 : ℝ))) volume := by
    apply integrable_one_add_norm; norm_num
  have hbound : ∀ x : ℝ, (1 + gagliardoSymbol α x) * ‖(1 + ‖x‖) ^ (-((4 : ℕ) : ℝ))‖ₑ ≤
      ENNReal.ofReal (gagliardoSymbolConst α) * ENNReal.ofReal ((1 + ‖x‖) ^ (-(2 : ℝ))) := by
    intro x
    have hpos : 0 < (1 + ‖x‖) ^ (-((4 : ℕ) : ℝ)) := by positivity
    have hc : 0 ≤ gagliardoSymbolConst α := by linarith [one_le_gagliardoSymbolConst α]
    rw [Real.eNorm_eq_ofReal hpos.le]
    calc (1 + gagliardoSymbol α x) * ENNReal.ofReal ((1 + ‖x‖) ^ (-((4 : ℕ) : ℝ)))
        ≤ ENNReal.ofReal (gagliardoSymbolConst α * (1 + x ^ 2)) *
            ENNReal.ofReal ((1 + ‖x‖) ^ (-((4 : ℕ) : ℝ))) := by
          gcongr
          exact one_add_gagliardoSymbol_le hα x
      _ = ENNReal.ofReal (gagliardoSymbolConst α * (1 + x ^ 2) *
            (1 + ‖x‖) ^ (-((4 : ℕ) : ℝ))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (gagliardoSymbolConst α * (1 + ‖x‖) ^ (-(2 : ℝ))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := one_add_sq_mul_rpow_le x
          rw [Real.norm_eq_abs]
          calc gagliardoSymbolConst α * (1 + x ^ 2) * (1 + |x|) ^ (-((4 : ℕ) : ℝ))
              = gagliardoSymbolConst α * ((1 + x ^ 2) * (1 + |x|) ^ (-(4 : ℝ))) := by
                push_cast; ring
            _ ≤ gagliardoSymbolConst α * (1 + |x|) ^ (-(2 : ℝ)) := by gcongr
      _ = _ := by rw [ENNReal.ofReal_mul hc]
  have key : ∫⁻ x : ℝ, (1 + gagliardoSymbol α x) * ‖(1 + ‖x‖) ^ (-((4 : ℕ) : ℝ))‖ₑ < ∞ :=
    calc ∫⁻ x : ℝ, (1 + gagliardoSymbol α x) * ‖(1 + ‖x‖) ^ (-((4 : ℕ) : ℝ))‖ₑ
        ≤ ∫⁻ x : ℝ, ENNReal.ofReal (gagliardoSymbolConst α) *
            ENNReal.ofReal ((1 + ‖x‖) ^ (-(2 : ℝ))) := lintegral_mono hbound
      _ = ENNReal.ofReal (gagliardoSymbolConst α) *
            ∫⁻ x : ℝ, ENNReal.ofReal ((1 + ‖x‖) ^ (-(2 : ℝ))) :=
          lintegral_const_mul _ (by fun_prop)
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint.lintegral_lt_top
  exact key

/-- The spectral measure is finite on compact sets. -/
theorem gagliardoSpectralMeasure_isFiniteMeasureOnCompacts {α : ℝ} (hα : FractionalExponent α) :
    IsFiniteMeasureOnCompacts (gagliardoSpectralMeasure α) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  have hmeas : Measurable fun ξ : ℝ => 1 + gagliardoSymbol α ξ :=
    measurable_const.add (measurable_gagliardoSymbol α)
  calc gagliardoSpectralMeasure α K ≤ gagliardoSpectralMeasure α (Metric.closedBall 0 R) :=
        measure_mono hR
    _ = ∫⁻ x in Metric.closedBall (0 : ℝ) R, 1 + gagliardoSymbol α x := by
        unfold gagliardoSpectralMeasure
        rw [withDensity_apply _ Metric.isClosed_closedBall.measurableSet]
    _ ≤ ∫⁻ _ in Metric.closedBall (0 : ℝ) R,
          ENNReal.ofReal (gagliardoSymbolConst α * (1 + R ^ 2)) := by
        refine setLIntegral_mono' Metric.isClosed_closedBall.measurableSet fun x hx => ?_
        refine (one_add_gagliardoSymbol_le hα x).trans (ENNReal.ofReal_le_ofReal ?_)
        have hxR : |x| ≤ R := by simpa [Real.dist_eq] using hx
        have hc : 0 ≤ gagliardoSymbolConst α := by linarith [one_le_gagliardoSymbolConst α]
        have : x ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
        gcongr
    _ < ∞ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top

/-- For `g ∈ L²(μ)`, `∫ ‖g‖ₑ² dμ = ‖g‖ₑ²` (squared `L²` norm as a lintegral), any measure. -/
theorem lintegral_enorm_sq_eq_measure {E : Type*} [NormedAddCommGroup E] {μ : Measure ℝ}
    (g : Lp (α := ℝ) E 2 μ) :
    ∫⁻ x, ‖(g : ℝ → E) x‖ₑ ^ (2 : ℝ) ∂μ = ‖g‖ₑ ^ (2 : ℝ) := by
  rw [lintegral_rpow_eNorm_eq_rpow_eLpNorm' (μ := μ) two_pos, Lp.eNorm_def,
    eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top]
  · norm_num
  · exact Lp.aestronglyMeasurable g

/-- The Gagliardo energy of a complex `L²` function. -/
noncomputable def gagliardoEnergyC (α : ℝ) (f : L2C) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ, gagliardoWeight α p * ‖(f : ℝ → ℂ) p.1 - (f : ℝ → ℂ) p.2‖ₑ ^ (2 : ℝ)
    ∂((volume : Measure ℝ).prod volume)

/-- **The `H^(α / 2)` norm on the Fourier side**: `‖f‖² + E_α(f) = ∫ ‖𝓕 f‖² dν_α`. -/
theorem norm_sq_add_energy_eq (α : ℝ) (f : L2C) :
    ‖f‖ₑ ^ (2 : ℝ) + gagliardoEnergyC α f =
      ∫⁻ ξ, ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) ∂gagliardoSpectralMeasure α := by
  have hFf : Measurable ((𝓕 f : L2C) : ℝ → ℂ) := (Lp.stronglyMeasurable (𝓕 f : L2C)).measurable
  have hmeas : Measurable fun ξ : ℝ => 1 + gagliardoSymbol α ξ :=
    measurable_const.add (measurable_gagliardoSymbol α)
  unfold gagliardoSpectralMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ hmeas (hFf.eNorm.pow_const _)]
  simp only [Pi.mul_apply, add_mul, one_mul]
  rw [lintegral_add_left (hFf.eNorm.pow_const _), lintegral_enorm_sq_eq_measure (𝓕 f : L2C)]
  have hnorm : ‖(𝓕 f : L2C)‖ₑ = ‖f‖ₑ := by
    have := (Lp.fourierTransformₗᵢ ℝ ℂ).norm_map f
    rw [← ofReal_norm, ← ofReal_norm]
    exact congrArg ENNReal.ofReal this
  rw [hnorm, gagliardoEnergyC, lintegral_gagliardo_energy_fourier]

/-- **Density of Schwartz functions in `H^(α / 2)(ℝ; ℂ)`**: for `f ∈ L²(ℝ; ℂ)` with finite
Gagliardo energy and every `ε > 0` there is a Schwartz function `φ` with
`‖φ - f‖² + E_α(φ - f) < ε`. -/
theorem exists_schwartz_close_complex {α : ℝ} (hα : FractionalExponent α) (f : L2C)
    (hE : gagliardoEnergyC α f < ∞) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : 𝓢(ℝ, ℂ), ‖(φ.toLp 2 volume : L2C) - f‖ₑ ^ (2 : ℝ) +
      gagliardoEnergyC α ((φ.toLp 2 volume : L2C) - f) <
      ENNReal.ofReal ε := by
  have := gagliardoSpectralMeasure_hasTemperateGrowth hα
  have := gagliardoSpectralMeasure_isFiniteMeasureOnCompacts hα
  set ν := gagliardoSpectralMeasure α with hν
  have hνac : ν ≪ (volume : Measure ℝ) := withDensity_absolutelyContinuous _ _
  -- the Fourier transform of `f` lies in `L²(ν)`
  have hfin : ∫⁻ ξ, ‖(𝓕 f : L2C) ξ‖ₑ ^ (2 : ℝ) ∂ν < ∞ := by
    rw [← norm_sq_add_energy_eq α f]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.rpow_lt_top_of_nonneg (by norm_num) eNorm_ne_top,
      hE⟩
  have hlt : eLpNorm ((𝓕 f : L2C) : ℝ → ℂ) 2 ν < ∞ := by
    rw [eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top (by norm_num) ENNReal.ofNat_ne_top]
    · simpa using hfin
    · exact (Lp.aestronglyMeasurable (𝓕 f : L2C)).mono_ac hνac
  have hψ : MemLp ((𝓕 f : L2C) : ℝ → ℂ) 2 ν := hlt
  let ψν : Lp (α := ℝ) ℂ 2 ν := hψ.toLp _
  have hd : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 ν) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  obtain ⟨χ, hχ⟩ := Metric.denseRange_iff.1 hd ψν (Real.sqrt ε) (Real.sqrt_pos.2 hε)
  refine ⟨𝓕⁻ χ, ?_⟩
  set φ : 𝓢(ℝ, ℂ) := 𝓕⁻ χ with hφ
  set g : L2C := (φ.toLp 2 volume : L2C) - f with hg
  have hFφ : 𝓕 (φ.toLp 2 volume : L2C) = (χ.toLp 2 volume : L2C) := by
    rw [hφ, ← SchwartzMap.toLp_fourierInv_eq]
    exact fourier_fourierInv_eq _
  have hFg : (𝓕 g : L2C) = (χ.toLp 2 volume : L2C) - 𝓕 f := by
    have hmap : (𝓕 g : L2C) = 𝓕 (φ.toLp 2 volume : L2C) - 𝓕 f :=
      (Lp.fourierTransformₗᵢ ℝ ℂ).map_sub _ _
    rw [hmap, hFφ]
  -- N²(g) = ∫ ‖χ - ψ‖² dν
  have hae : ((𝓕 g : L2C) : ℝ → ℂ) =ᵐ[ν] fun ξ => (χ : ℝ → ℂ) ξ - ((𝓕 f : L2C) : ℝ → ℂ) ξ := by
    refine hνac.ae_le ?_
    rw [hFg]
    filter_upwards [Lp.coeFn_sub (χ.toLp 2 volume : L2C) (𝓕 f : L2C),
      χ.coeFn_toLp 2 volume] with ξ h1 h2
    have h1' := h1
    have h2' : ((χ.toLp 2 volume : L2C) : ℝ → ℂ) ξ = χ ξ := h2
    simp only [Pi.sub_apply] at h1'
    rw [h1', h2']
  have hae2 : ((χ.toLp 2 ν - ψν : Lp (α := ℝ) ℂ 2 ν) : ℝ → ℂ) =ᵐ[ν]
      fun ξ => (χ : ℝ → ℂ) ξ - ((𝓕 f : L2C) : ℝ → ℂ) ξ := by
    filter_upwards [Lp.coeFn_sub (χ.toLp 2 ν) ψν, χ.coeFn_toLp 2 ν, hψ.coeFn_toLp] with ξ h1 h2 h3
    have h1' := h1
    have h2' : ((χ.toLp 2 ν : Lp (α := ℝ) ℂ 2 ν) : ℝ → ℂ) ξ = χ ξ := h2
    have h3' : (ψν : ℝ → ℂ) ξ = ((𝓕 f : L2C) : ℝ → ℂ) ξ := h3
    simp only [Pi.sub_apply] at h1'
    rw [h1', h2', h3']
  have hmain : ‖g‖ₑ ^ (2 : ℝ) + gagliardoEnergyC α g = ‖χ.toLp 2 ν - ψν‖ₑ ^ (2 : ℝ) := by
    rw [norm_sq_add_energy_eq α g, ← lintegral_enorm_sq_eq_measure (χ.toLp 2 ν - ψν)]
    refine lintegral_congr_ae ?_
    filter_upwards [hae, hae2] with ξ h1 h2
    rw [h1, h2]
  rw [hmain]
  have hd' : ‖χ.toLp 2 ν - ψν‖ < Real.sqrt ε := by
    rw [← dist_eq_norm, dist_comm]; exact hχ
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    ENNReal.ofReal_lt_ofReal_iff hε, Real.rpow_two]
  calc ‖χ.toLp 2 ν - ψν‖ ^ 2 < Real.sqrt ε ^ 2 :=
        pow_lt_pow_left₀ hd' (norm_nonneg _) (by norm_num)
    _ = ε := Real.sq_sqrt hε.le

end

end FracLap
