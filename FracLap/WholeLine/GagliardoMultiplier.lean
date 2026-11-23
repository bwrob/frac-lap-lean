/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.GagliardoDensity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLap.WholeLine.GagliardoMultiplier

Multiplication by a bounded Lipschitz function is bounded on the Gagliardo energy, and a smooth
cutoff with the required regularity:
- `lintegral_gagliardo_shear`: Tonelli plus the shear `(x, y) ↦ (x - y, y)` for arbitrary jointly
  measurable integrands.
- `gagliardoEnergyC_mul_le`: if `g = θ f` a.e. with `θ` bounded by `B` and `L`-Lipschitz, then
  `E(g) ≤ 2 B² E(f) + 2 M (∫ k_α) ‖f‖²`, `M = max (L²) (4 B²)`.
- `cutoffStep`: the smooth step `θ_ε` vanishing on `(-∞, ε / 2]` and equal to `1` on `[ε, ∞)`,
  with temperate growth and Lipschitz bound.
-/

namespace FracLap

open Complex Filter FourierTransform MeasureTheory Real Set Topology
open scoped ENNReal NNReal ComplexInnerProductSpace SchwartzMap ContDiff

@[expose] public section

/-- **General shear identity**: for jointly measurable `G`,
`∬ w(x - y) G(x, y) = ∫ w(h) (∫ G(y + h, y) dy) dh`. -/
theorem lintegral_gagliardo_shear (α : ℝ) {G : ℝ → ℝ → ℝ≥0∞}
    (hG : Measurable (Function.uncurry G)) :
    ∫⁻ p : ℝ × ℝ, gagliardoWeight α p * G p.1 p.2 ∂((volume : Measure ℝ).prod volume) =
      ∫⁻ h : ℝ, gagliardoWeight α (h, 0) * ∫⁻ y, G (y + h) y := by
  have hf : Measurable fun p : ℝ × ℝ => gagliardoWeight α p * G p.1 p.2 :=
    (measurable_gagliardoWeight α).mul hG
  have hWm : Measurable fun h : ℝ => gagliardoWeight α (h, 0) :=
    (measurable_gagliardoWeight α).comp (measurable_id.prodMk measurable_const)
  set H : ℝ → ℝ → ℝ≥0∞ := fun y h => gagliardoWeight α (h, 0) * G (h + y) y with hH
  have hHm : Measurable (Function.uncurry H) := by
    simp only [hH]
    refine (hWm.comp measurable_snd).mul ?_
    exact hG.comp ((measurable_snd.add measurable_fst).prodMk measurable_fst)
  have step1 : ∫⁻ p : ℝ × ℝ, gagliardoWeight α p * G p.1 p.2
        ∂((volume : Measure ℝ).prod volume) = ∫⁻ y, ∫⁻ h, H y h := by
    rw [lintegral_prod_symm _ hf.aemeasurable]
    refine lintegral_congr fun y => ?_
    rw [← lintegral_sub_right_eq_self (fun h => H y h) y]
    refine lintegral_congr fun x => ?_
    simp only [hH, gagliardoWeight, sub_zero, sub_add_cancel]
  rw [step1, lintegral_lintegral_swap hHm.aemeasurable]
  refine lintegral_congr fun h => ?_
  have hm : Measurable fun y : ℝ => G (h + y) y :=
    hG.comp ((measurable_const.add measurable_id).prodMk measurable_id)
  simp only [hH]
  rw [lintegral_const_mul _ hm]
  simp only [add_comm h]

/-- Real inequality `(a + b)² ≤ 2 a² + 2 b²` for norms of a sum. -/
theorem norm_add_sq_le_two (u v : ℂ) : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h := norm_add_le u v
  nlinarith [norm_nonneg u, norm_nonneg v, sq_nonneg (‖u‖ - ‖v‖), norm_nonneg (u + v)]

/-- Pointwise bound for a product: `‖θx fx - θy fy‖² ≤ 2 θx² ‖fx - fy‖² + 2 (θx - θy)² ‖fy‖²`. -/
theorem norm_mul_sub_mul_sq_le (a b : ℝ) (u v : ℂ) :
    ‖(a : ℂ) * u - (b : ℂ) * v‖ ^ 2 ≤ 2 * a ^ 2 * ‖u - v‖ ^ 2 + 2 * (a - b) ^ 2 * ‖v‖ ^ 2 := by
  have h : (a : ℂ) * u - (b : ℂ) * v = (a : ℂ) * (u - v) + ((a - b : ℝ) : ℂ) * v := by
    push_cast; ring
  rw [h]
  refine (norm_add_sq_le_two _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  nlinarith [sq_abs a, sq_abs (a - b), sq_nonneg ‖u - v‖, sq_nonneg ‖v‖]

/-- A bounded `L`-Lipschitz `θ` satisfies `(θ(y + h) - θ y)² ≤ M min(h², 1)` with
`M = max (L²) (4 B²)`. -/
theorem sq_sub_le_of_lipschitz {θ : ℝ → ℝ} {B L : ℝ} (hB : ∀ x, |θ x| ≤ B)
    (hL : ∀ x y, |θ x - θ y| ≤ L * |x - y|) (y h : ℝ) :
    (θ (y + h) - θ y) ^ 2 ≤ max (L ^ 2) (4 * B ^ 2) * min (h ^ 2) 1 := by
  have h1 : (θ (y + h) - θ y) ^ 2 ≤ L ^ 2 * h ^ 2 := by
    have := hL (y + h) y
    rw [add_sub_cancel_left] at this
    rw [← sq_abs (θ (y + h) - θ y), ← sq_abs h, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have h2 : (θ (y + h) - θ y) ^ 2 ≤ 4 * B ^ 2 := by
    have : |θ (y + h) - θ y| ≤ 2 * B := by
      calc |θ (y + h) - θ y| ≤ |θ (y + h)| + |θ y| := abs_sub _ _
        _ ≤ B + B := add_le_add (hB _) (hB _)
        _ = 2 * B := by ring
    rw [← sq_abs, show 4 * B ^ 2 = (2 * B) ^ 2 by ring]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  rcases le_total (h ^ 2) 1 with hh | hh
  · rw [min_eq_left hh]
    calc _ ≤ L ^ 2 * h ^ 2 := h1
      _ ≤ max (L ^ 2) (4 * B ^ 2) * h ^ 2 := by gcongr; exact le_max_left _ _
  · rw [min_eq_right hh]
    calc _ ≤ 4 * B ^ 2 := h2
      _ ≤ max (L ^ 2) (4 * B ^ 2) * 1 := by rw [mul_one]; exact le_max_right _ _

/-- **Multiplier estimate**: if `g = θ f` a.e. with `θ` bounded by `B` and `L`-Lipschitz, then
`E(g) ≤ 2 B² E(f) + 2 M (∫ k_α) ‖f‖²` with `M = max (L²) (4 B²)`. -/
theorem gagliardoEnergyC_mul_le {α : ℝ} (hα : FractionalExponent α) {θ : ℝ → ℝ}
    (hθ : Measurable θ) {B L : ℝ} (hB : ∀ x, |θ x| ≤ B)
    (hL : ∀ x y, |θ x - θ y| ≤ L * |x - y|) (f g : L2C)
    (hfg : ∀ᵐ x : ℝ ∂volume, (g : ℝ → ℂ) x = (θ x : ℂ) * (f : ℝ → ℂ) x) :
    gagliardoEnergyC α g ≤ ENNReal.ofReal (2 * B ^ 2) * gagliardoEnergyC α f +
      ENNReal.ofReal (2 * max (L ^ 2) (4 * B ^ 2)) * (∫⁻ h, gagliardoKernel α h) *
        ‖f‖ₑ ^ (2 : ℝ) := by
  set M := max (L ^ 2) (4 * B ^ 2) with hM
  have hM0 : 0 ≤ M := le_trans (sq_nonneg L) (le_max_left _ _)
  have hfm : Measurable (f : ℝ → ℂ) := (Lp.stronglyMeasurable f).measurable
  set G : ℝ → ℝ → ℝ≥0∞ :=
    fun x y => ‖(f : ℝ → ℂ) y‖ₑ ^ (2 : ℝ) * ENNReal.ofReal ((θ x - θ y) ^ 2) with hG
  have hGm : Measurable (Function.uncurry G) := by
    simp only [hG]
    refine (((hfm.comp measurable_snd).eNorm).pow_const _).mul
      (ENNReal.measurable_ofReal.comp ?_)
    exact ((hθ.comp measurable_fst).sub (hθ.comp measurable_snd)).pow_const 2
  have hdiffm : Measurable fun p : ℝ × ℝ =>
      ‖(f : ℝ → ℂ) p.1 - (f : ℝ → ℂ) p.2‖ₑ ^ (2 : ℝ) :=
    (((hfm.comp measurable_fst).sub (hfm.comp measurable_snd)).eNorm).pow_const _
  have hA : gagliardoEnergyC α g = ∫⁻ p : ℝ × ℝ, gagliardoWeight α p *
      ‖(θ p.1 : ℂ) * (f : ℝ → ℂ) p.1 - (θ p.2 : ℂ) * (f : ℝ → ℂ) p.2‖ₑ ^ (2 : ℝ)
      ∂((volume : Measure ℝ).prod volume) := by
    unfold gagliardoEnergyC
    refine lintegral_congr_ae ?_
    filter_upwards [ae_prod_fst hfg, ae_prod_snd hfg] with p h1 h2
    rw [h1, h2]
  have hB' : ∀ x, θ x ^ 2 ≤ B ^ 2 := fun x => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
  have hpt : ∀ p : ℝ × ℝ, gagliardoWeight α p *
      ‖(θ p.1 : ℂ) * (f : ℝ → ℂ) p.1 - (θ p.2 : ℂ) * (f : ℝ → ℂ) p.2‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (2 * B ^ 2) * (gagliardoWeight α p *
        ‖(f : ℝ → ℂ) p.1 - (f : ℝ → ℂ) p.2‖ₑ ^ (2 : ℝ)) +
      ENNReal.ofReal 2 * (gagliardoWeight α p * G p.1 p.2) := by
    intro p
    simp only [hG, enorm_rpow_two_eq_ofReal]
    have hbd := norm_mul_sub_mul_sq_le (θ p.1) (θ p.2) ((f : ℝ → ℂ) p.1) ((f : ℝ → ℂ) p.2)
    have hbd' : ‖(θ p.1 : ℂ) * (f : ℝ → ℂ) p.1 - (θ p.2 : ℂ) * (f : ℝ → ℂ) p.2‖ ^ 2 ≤
        2 * B ^ 2 * ‖(f : ℝ → ℂ) p.1 - (f : ℝ → ℂ) p.2‖ ^ 2 +
          2 * (θ p.1 - θ p.2) ^ 2 * ‖(f : ℝ → ℂ) p.2‖ ^ 2 := by
      refine hbd.trans ?_
      have := hB' p.1
      nlinarith [sq_nonneg ‖(f : ℝ → ℂ) p.1 - (f : ℝ → ℂ) p.2‖]
    calc gagliardoWeight α p * ENNReal.ofReal
          (‖(θ p.1 : ℂ) * (f : ℝ → ℂ) p.1 - (θ p.2 : ℂ) * (f : ℝ → ℂ) p.2‖ ^ 2)
        ≤ gagliardoWeight α p * ENNReal.ofReal
          (2 * B ^ 2 * ‖(f : ℝ → ℂ) p.1 - (f : ℝ → ℂ) p.2‖ ^ 2 +
            2 * (θ p.1 - θ p.2) ^ 2 * ‖(f : ℝ → ℂ) p.2‖ ^ 2) := by
          gcongr
      _ = ENNReal.ofReal (2 * B ^ 2) * (gagliardoWeight α p *
            ENNReal.ofReal (‖(f : ℝ → ℂ) p.1 - (f : ℝ → ℂ) p.2‖ ^ 2)) +
          ENNReal.ofReal 2 * (gagliardoWeight α p * (ENNReal.ofReal (‖(f : ℝ → ℂ) p.2‖ ^ 2) *
            ENNReal.ofReal ((θ p.1 - θ p.2) ^ 2))) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity)]
          ring
  have hwdiff : Measurable fun p : ℝ × ℝ => gagliardoWeight α p *
      ‖(f : ℝ → ℂ) p.1 - (f : ℝ → ℂ) p.2‖ₑ ^ (2 : ℝ) := (measurable_gagliardoWeight α).mul hdiffm
  have hwG : Measurable fun p : ℝ × ℝ => gagliardoWeight α p * G p.1 p.2 :=
    (measurable_gagliardoWeight α).mul hGm
  have hshear := lintegral_gagliardo_shear α hGm
  have hper : ∀ h : ℝ, gagliardoWeight α (h, 0) * ∫⁻ y, G (y + h) y ≤
      ‖f‖ₑ ^ (2 : ℝ) * (ENNReal.ofReal M * gagliardoKernel α h) := by
    intro h
    have hin : ∫⁻ y, G (y + h) y ≤ ‖f‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (M * min (h ^ 2) 1) := by
      calc ∫⁻ y, G (y + h) y
          ≤ ∫⁻ y, ‖(f : ℝ → ℂ) y‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (M * min (h ^ 2) 1) := by
            refine lintegral_mono fun y => ?_
            simp only [hG]
            gcongr
            exact sq_sub_le_of_lipschitz hB hL y h
        _ = ‖f‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (M * min (h ^ 2) 1) := by
            rw [lintegral_mul_const _ ((hfm.eNorm).pow_const _), lintegral_enorm_sq_eq_general f]
    calc gagliardoWeight α (h, 0) * ∫⁻ y, G (y + h) y
        ≤ gagliardoWeight α (h, 0) * (‖f‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (M * min (h ^ 2) 1)) := by
          gcongr
      _ = ‖f‖ₑ ^ (2 : ℝ) * (gagliardoWeight α (h, 0) * ENNReal.ofReal (M * min (h ^ 2) 1)) := by
          ring
      _ = ‖f‖ₑ ^ (2 : ℝ) * (ENNReal.ofReal M * gagliardoKernel α h) := by
          rw [gagliardoWeight_mul_ofReal hα h, gagliardoKernel,
            ← ENNReal.ofReal_mul hM0]
          congr 2
          ring
  have hsecond : ∫⁻ p : ℝ × ℝ, gagliardoWeight α p * G p.1 p.2
      ∂((volume : Measure ℝ).prod volume) ≤
      ‖f‖ₑ ^ (2 : ℝ) * (ENNReal.ofReal M * ∫⁻ h, gagliardoKernel α h) := by
    rw [hshear]
    calc ∫⁻ h : ℝ, gagliardoWeight α (h, 0) * ∫⁻ y, G (y + h) y
        ≤ ∫⁻ h : ℝ, ‖f‖ₑ ^ (2 : ℝ) * (ENNReal.ofReal M * gagliardoKernel α h) :=
          lintegral_mono hper
      _ = ‖f‖ₑ ^ (2 : ℝ) * ∫⁻ h : ℝ, ENNReal.ofReal M * gagliardoKernel α h :=
          lintegral_const_mul _ (measurable_const.mul (measurable_gagliardoKernel α))
      _ = ‖f‖ₑ ^ (2 : ℝ) * (ENNReal.ofReal M * ∫⁻ h, gagliardoKernel α h) := by
          rw [lintegral_const_mul _ (measurable_gagliardoKernel α)]
  rw [hA]
  calc ∫⁻ p : ℝ × ℝ, gagliardoWeight α p *
        ‖(θ p.1 : ℂ) * (f : ℝ → ℂ) p.1 - (θ p.2 : ℂ) * (f : ℝ → ℂ) p.2‖ₑ ^ (2 : ℝ)
        ∂((volume : Measure ℝ).prod volume)
      ≤ ∫⁻ p : ℝ × ℝ, (ENNReal.ofReal (2 * B ^ 2) * (gagliardoWeight α p *
          ‖(f : ℝ → ℂ) p.1 - (f : ℝ → ℂ) p.2‖ₑ ^ (2 : ℝ)) +
          ENNReal.ofReal 2 * (gagliardoWeight α p * G p.1 p.2))
          ∂((volume : Measure ℝ).prod volume) := lintegral_mono hpt
    _ = ENNReal.ofReal (2 * B ^ 2) * gagliardoEnergyC α f +
        ENNReal.ofReal 2 * ∫⁻ p : ℝ × ℝ, gagliardoWeight α p * G p.1 p.2
          ∂((volume : Measure ℝ).prod volume) := by
        rw [lintegral_add_left (hwdiff.const_mul _), lintegral_const_mul _ hwdiff,
          lintegral_const_mul _ hwG]
        rfl
    _ ≤ ENNReal.ofReal (2 * B ^ 2) * gagliardoEnergyC α f +
        ENNReal.ofReal 2 * (‖f‖ₑ ^ (2 : ℝ) * (ENNReal.ofReal M * ∫⁻ h, gagliardoKernel α h)) := by
        gcongr
    _ = ENNReal.ofReal (2 * B ^ 2) * gagliardoEnergyC α f +
        ENNReal.ofReal (2 * M) * (∫⁻ h, gagliardoKernel α h) * ‖f‖ₑ ^ (2 : ℝ) := by
        have h2M : ENNReal.ofReal (2 * M) = ENNReal.ofReal 2 * ENNReal.ofReal M :=
          ENNReal.ofReal_mul (by norm_num)
        rw [h2M]
        ring

/-- The smooth cutoff `θ_ε(x) = smoothTransition ((2 x - ε) / ε)`: it vanishes for `x ≤ ε / 2`
and equals `1` for `x ≥ ε`. -/
noncomputable def cutoffStep (ε x : ℝ) : ℝ := Real.smoothTransition ((2 * x - ε) / ε)

/-- The cutoff is smooth. -/
theorem contDiff_cutoffStep {ε : ℝ} (_hε : 0 < ε) : ContDiff ℝ ∞ (cutoffStep ε) := by
  unfold cutoffStep
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

/-- The cutoff vanishes for `x ≤ ε / 2`. -/
theorem cutoffStep_eq_zero {ε x : ℝ} (hε : 0 < ε) (hx : x ≤ ε / 2) : cutoffStep ε x = 0 := by
  unfold cutoffStep
  apply Real.smoothTransition.zero_of_nonpos
  rw [div_nonpos_iff]
  right
  exact ⟨by linarith, hε.le⟩

/-- The cutoff equals `1` for `x ≥ ε`. -/
theorem cutoffStep_eq_one {ε x : ℝ} (hε : 0 < ε) (hx : ε ≤ x) : cutoffStep ε x = 1 := by
  unfold cutoffStep
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ hε]
  linarith

/-- The cutoff is nonnegative. -/
theorem cutoffStep_nonneg (ε x : ℝ) : 0 ≤ cutoffStep ε x := Real.smoothTransition.nonneg _

/-- The cutoff is at most `1`. -/
theorem cutoffStep_le_one (ε x : ℝ) : cutoffStep ε x ≤ 1 := Real.smoothTransition.le_one _

/-- The cutoff is bounded by `1` in absolute value. -/
theorem abs_cutoffStep_le (ε x : ℝ) : |cutoffStep ε x| ≤ 1 := by
  rw [abs_of_nonneg (cutoffStep_nonneg ε x)]; exact cutoffStep_le_one ε x

/-- `fderiv` of the cutoff has compact support. -/
theorem hasCompactSupport_fderiv_cutoffStep {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (fderiv ℝ (cutoffStep ε)) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := ε / 2) (b := ε)) fun x hx => ?_
  rw [mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · have : cutoffStep ε =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact cutoffStep_eq_zero hε hy.le
    rw [this.fderiv_eq]; simp
  · have : cutoffStep ε =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact cutoffStep_eq_one hε hy.le
    rw [this.fderiv_eq]; simp

/-- The cutoff has temperate growth. -/
theorem hasTemperateGrowth_cutoffStep {ε : ℝ} (hε : 0 < ε) :
    (cutoffStep ε).HasTemperateGrowth := by
  have hsmooth := contDiff_cutoffStep hε
  have hder : (fderiv ℝ (cutoffStep ε)).HasTemperateGrowth :=
    (hasCompactSupport_fderiv_cutoffStep hε).hasTemperateGrowth
      (hsmooth.fderiv_right (by simp))
  exact Function.HasTemperateGrowth.of_fderiv hder
    (hsmooth.differentiable (by simp)) (k := 0) (C := 1) (fun x => by
      simpa using abs_cutoffStep_le ε x)

/-- The cutoff is Lipschitz. -/
theorem exists_lipschitz_cutoffStep {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, ∀ x y, |cutoffStep ε x - cutoffStep ε y| ≤ L * |x - y| := by
  have hsmooth := contDiff_cutoffStep hε
  have hcont : Continuous (fderiv ℝ (cutoffStep ε)) := hsmooth.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := (hcont.norm).bounded_above_of_compact_support
    (hasCompactSupport_fderiv_cutoffStep hε).norm
  refine ⟨max C 0, fun x y => ?_⟩
  have hlip : LipschitzWith (max C 0).toNNReal (cutoffStep ε) := by
    refine lipschitzWith_of_nnNorm_fderiv_le (hsmooth.differentiable (by simp)) fun z => ?_
    have h1 : ‖fderiv ℝ (cutoffStep ε) z‖ ≤ max C 0 := by
      have := hC z
      rw [norm_norm] at this
      exact this.trans (le_max_left _ _)
    rw [← NNReal.coe_le_coe, coe_nnNorm, Real.coe_toNNReal _ (le_max_right _ _)]
    exact h1
  have := hlip.dist_le_mul x y
  simpa [Real.dist_eq, Real.coe_toNNReal _ (le_max_right _ _)] using this

end

end FracLap
