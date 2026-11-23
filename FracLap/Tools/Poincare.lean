/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# FracLap.Tools.Poincare

Nonlocal Poincaré inequalities for general kernels (Felsinger--Kassmann--Voigt, Foghem,
Rutkowski, Di Pierro--Savin--Valdinoci).

- `variance_identity`: `∬_{I×I} (u x - u y)² = 2 |I| ∫_I (u - ū)²`.
- `poincare_of_lower_bound`: if a measure `ν` on `ℝ × ℝ` dominates `m` times Lebesgue measure on
  `I × I` then `∫_I |u - ū|² ≤ (2 m |I|)⁻¹ ∫ |u x - u y|² dν`.
  Only the lower bound of the kernel on `I × I` matters, so kernels with singular parts (atoms,
  fractional singularities) are covered.
- `poincare_gagliardo_interval`: for the fractional kernel `C/2 |x-y|^(-1-α)` on an interval of
  length `L` the constant is `L^(α) / C`, i.e. `∫_I |u-ū|² ≤ L^α C⁻¹ ∬_{I×I} ...`.
-/

namespace FracLap

open MeasureTheory Set
open scoped ENNReal

@[expose] public section

/-- Integrability of the squared increment on `I × I` for `u ∈ L²(I)`. -/
theorem integrable_sq_sub_restrict {I : Set ℝ} (hfin : volume I ≠ ⊤) {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict I)) :
    Integrable (fun p : ℝ × ℝ => (u p.1 - u p.2) ^ 2)
      ((volume.restrict I).prod (volume.restrict I)) := by
  have hμfin : IsFiniteMeasure (volume.restrict I) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfin⟩
  have hu1 : Integrable u (volume.restrict I) := hu.integrable one_le_two
  have hu2 : Integrable (fun x => u x ^ 2) (volume.restrict I) := hu.integrable_sq
  have hA : Integrable (fun p : ℝ × ℝ => u p.1 ^ 2 * 1)
      ((volume.restrict I).prod (volume.restrict I)) := hu2.mul_prod (integrable_const (1 : ℝ))
  have hB : Integrable (fun p : ℝ × ℝ => 1 * u p.2 ^ 2)
      ((volume.restrict I).prod (volume.restrict I)) := (integrable_const (1 : ℝ)).mul_prod hu2
  have hC : Integrable (fun p : ℝ × ℝ => u p.1 * u p.2)
      ((volume.restrict I).prod (volume.restrict I)) := hu1.mul_prod hu1
  have := (hA.add hB).sub (hC.const_mul 2)
  refine this.congr (ae_of_all _ fun p => ?_)
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

/-- **Variance identity** on a set `I` of finite positive measure:
`∬_{I×I} (u x - u y)² dx dy = 2 |I| ∫_I (u - ū)²` with `ū = |I|⁻¹ ∫_I u`. -/
theorem variance_identity {I : Set ℝ} (hfin : volume I ≠ ⊤)
    (hpos : 0 < volume I) {u : ℝ → ℝ} (hu : MemLp u 2 (volume.restrict I)) :
    ∫ p in I ×ˢ I, (u p.1 - u p.2) ^ 2 ∂(volume.prod volume) =
      2 * (volume I).toReal *
        ∫ x in I, (u x - (∫ y in I, u y) / (volume I).toReal) ^ 2 := by
  set μ : Measure ℝ := volume.restrict I with hμ
  have hμfin : IsFiniteMeasure μ :=
    ⟨by rw [hμ, Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfin⟩
  set L : ℝ := (volume I).toReal with hL
  have hLpos : 0 < L := ENNReal.toReal_pos hpos.ne' hfin
  have hμuniv : μ.real univ = L := by simp [hμ, hL, Measure.real]
  have hu1 : Integrable u μ := hu.integrable one_le_two
  have hu2 : Integrable (fun x => u x ^ 2) μ := hu.integrable_sq
  have hrestrict : (volume.prod volume).restrict (I ×ˢ I) = μ.prod μ := by
    rw [hμ, Measure.prod_restrict]
  rw [hrestrict]
  have hA : Integrable (fun p : ℝ × ℝ => u p.1 ^ 2 * 1) (μ.prod μ) :=
    hu2.mul_prod (integrable_const (1 : ℝ))
  have hB : Integrable (fun p : ℝ × ℝ => 1 * u p.2 ^ 2) (μ.prod μ) :=
    (integrable_const (1 : ℝ)).mul_prod hu2
  have hC : Integrable (fun p : ℝ × ℝ => u p.1 * u p.2) (μ.prod μ) := hu1.mul_prod hu1
  have hexp : ∀ p : ℝ × ℝ, (u p.1 - u p.2) ^ 2 =
      u p.1 ^ 2 * 1 + 1 * u p.2 ^ 2 - 2 * (u p.1 * u p.2) := fun p => by ring
  simp_rw [hexp]
  have hAB : Integrable (fun p : ℝ × ℝ => u p.1 ^ 2 * 1 + 1 * u p.2 ^ 2) (μ.prod μ) := hA.add hB
  have hC2 : Integrable (fun p : ℝ × ℝ => 2 * (u p.1 * u p.2)) (μ.prod μ) := hC.const_mul 2
  have e1 : ∫ p : ℝ × ℝ, u p.1 ^ 2 * 1 ∂(μ.prod μ) = (∫ x, u x ^ 2 ∂μ) * L := by
    rw [integral_prod_mul (fun x => u x ^ 2) (fun _ => (1 : ℝ)), integral_const, hμuniv,
      smul_eq_mul, mul_one]
  have e2 : ∫ p : ℝ × ℝ, 1 * u p.2 ^ 2 ∂(μ.prod μ) = L * ∫ x, u x ^ 2 ∂μ := by
    rw [integral_prod_mul (fun _ => (1 : ℝ)) (fun x => u x ^ 2), integral_const, hμuniv,
      smul_eq_mul, mul_one]
  have e3 : ∫ p : ℝ × ℝ, 2 * (u p.1 * u p.2) ∂(μ.prod μ) = 2 * (∫ x, u x ∂μ) ^ 2 := by
    rw [integral_const_mul, integral_prod_mul (fun x => u x) (fun x => u x)]
    ring
  rw [integral_sub (f := fun p : ℝ × ℝ => u p.1 ^ 2 * 1 + 1 * u p.2 ^ 2)
    (g := fun p : ℝ × ℝ => 2 * (u p.1 * u p.2)) hAB hC2,
    integral_add (f := fun p : ℝ × ℝ => u p.1 ^ 2 * 1) (g := fun p : ℝ × ℝ => 1 * u p.2 ^ 2) hA hB,
    e1, e2, e3]
  -- right-hand side
  set m : ℝ := (∫ y, u y ∂μ) / L with hm_def
  have hint1 : Integrable (fun x => u x ^ 2 - 2 * m * u x) μ := hu2.sub (hu1.const_mul _)
  have hm : ∫ x, (u x - m) ^ 2 ∂μ = ∫ x, u x ^ 2 ∂μ - (∫ x, u x ∂μ) ^ 2 / L := by
    have e : ∀ x, (u x - m) ^ 2 = (u x ^ 2 - 2 * m * u x) + m ^ 2 := fun x => by ring
    simp_rw [e]
    rw [integral_add (f := fun x => u x ^ 2 - 2 * m * u x) (g := fun _ => m ^ 2) hint1
      (integrable_const _), integral_sub (f := fun x => u x ^ 2) (g := fun x => 2 * m * u x) hu2
      (hu1.const_mul _), integral_const_mul, integral_const]
    rw [hμuniv, smul_eq_mul, hm_def]
    field_simp
    ring
  change _ = 2 * L * ∫ x, (u x - m) ^ 2 ∂μ
  rw [hm]
  field_simp
  ring

/-- **Nonlocal Poincaré inequality for a general jump measure.** If a measure `ν` on `ℝ × ℝ`
dominates `m` times Lebesgue measure on `I × I` (`m > 0`, `I` of finite positive measure) and
`u ∈ L²(I)`, then `∫_I (u - ū)² ≤ (2 m |I|)⁻¹ ∫ (u x - u y)² dν`. -/
theorem poincare_of_lower_bound {I : Set ℝ} (hfin : volume I ≠ ⊤) (hpos : 0 < volume I)
    {u : ℝ → ℝ} (hu : MemLp u 2 (volume.restrict I)) {ν : Measure (ℝ × ℝ)} {m : ℝ}
    (hm : 0 < m)
    (hν : ENNReal.ofReal m • (volume.prod volume).restrict (I ×ˢ I) ≤ ν) :
    ENNReal.ofReal (∫ x in I, (u x - (∫ y in I, u y) / (volume I).toReal) ^ 2) ≤
      ENNReal.ofReal (1 / (2 * m * (volume I).toReal)) *
        ∫⁻ p, ENNReal.ofReal ((u p.1 - u p.2) ^ 2) ∂ν := by
  set L : ℝ := (volume I).toReal with hL
  have hLpos : 0 < L := ENNReal.toReal_pos hpos.ne' hfin
  have hid := variance_identity hfin hpos hu
  have hint := integrable_sq_sub_restrict hfin hu
  have hrestrict : (volume.prod volume).restrict (I ×ˢ I) =
      (volume.restrict I).prod (volume.restrict I) := by rw [Measure.prod_restrict]
  have hlint : ∫⁻ p, ENNReal.ofReal ((u p.1 - u p.2) ^ 2)
      ∂((volume.prod volume).restrict (I ×ˢ I)) =
      ENNReal.ofReal (∫ p in I ×ˢ I, (u p.1 - u p.2) ^ 2 ∂(volume.prod volume)) := by
    rw [hrestrict, ← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun p => sq_nonneg _)]
  have hmono : ENNReal.ofReal m * ∫⁻ p, ENNReal.ofReal ((u p.1 - u p.2) ^ 2)
      ∂((volume.prod volume).restrict (I ×ˢ I)) ≤
      ∫⁻ p, ENNReal.ofReal ((u p.1 - u p.2) ^ 2) ∂ν := by
    have := lintegral_mono' hν (le_refl fun p : ℝ × ℝ => ENNReal.ofReal ((u p.1 - u p.2) ^ 2))
    rwa [lintegral_smul_measure] at this
  rw [hlint] at hmono
  have hvar : ∫ p in I ×ˢ I, (u p.1 - u p.2) ^ 2 ∂(volume.prod volume) =
      2 * L * ∫ x in I, (u x - (∫ y in I, u y) / L) ^ 2 := hid
  rw [hvar] at hmono
  have h2L : 0 < 2 * L := by positivity
  have hnn : 0 ≤ ∫ x in I, (u x - (∫ y in I, u y) / L) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have e : ENNReal.ofReal (2 * L * ∫ x in I, (u x - (∫ y in I, u y) / L) ^ 2) =
      ENNReal.ofReal (2 * L) * ENNReal.ofReal (∫ x in I, (u x - (∫ y in I, u y) / L) ^ 2) :=
    ENNReal.ofReal_mul h2L.le
  rw [e, ← mul_assoc, ← ENNReal.ofReal_mul hm.le] at hmono
  have hc : 0 < m * (2 * L) := by positivity
  calc ENNReal.ofReal (∫ x in I, (u x - (∫ y in I, u y) / L) ^ 2)
      = ENNReal.ofReal (1 / (m * (2 * L))) *
          (ENNReal.ofReal (m * (2 * L)) *
            ENNReal.ofReal (∫ x in I, (u x - (∫ y in I, u y) / L) ^ 2)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        have : 1 / (m * (2 * L)) * (m * (2 * L)) = 1 := by field_simp
        rw [this, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (1 / (m * (2 * L))) *
          ∫⁻ p, ENNReal.ofReal ((u p.1 - u p.2) ^ 2) ∂ν := by gcongr
    _ = ENNReal.ofReal (1 / (2 * m * L)) *
          ∫⁻ p, ENNReal.ofReal ((u p.1 - u p.2) ^ 2) ∂ν := by
        congr 2; ring

/-- **Poincaré inequality for a kernel bounded below on `I × I`.** If `J ≥ m` on `I × I` then
`∫_I (u - ū)² ≤ (2 m |I|)⁻¹ ∬ J(x, y) (u x - u y)² dx dy`. Only the restriction of `J` to
`I × I` enters, so any behaviour of `J` away from the diagonal band (singularities, atoms in the
sense of measures dominating Lebesgue measure) is allowed. -/
theorem poincare_of_kernel_lower_bound {I : Set ℝ} (hfin : volume I ≠ ⊤)
    (hpos : 0 < volume I) {u : ℝ → ℝ} (hu : MemLp u 2 (volume.restrict I)) {m : ℝ} (hm : 0 < m)
    (hum : Measurable u) {J : ℝ × ℝ → ℝ≥0∞} (hJm : Measurable J)
    (hJ : ∀ᵐ p ∂((volume.prod volume).restrict (I ×ˢ I)), ENNReal.ofReal m ≤ J p) :
    ENNReal.ofReal (∫ x in I, (u x - (∫ y in I, u y) / (volume I).toReal) ^ 2) ≤
      ENNReal.ofReal (1 / (2 * m * (volume I).toReal)) *
        ∫⁻ p, J p * ENNReal.ofReal ((u p.1 - u p.2) ^ 2) ∂(volume.prod volume) := by
  have hν : ENNReal.ofReal m • (volume.prod volume).restrict (I ×ˢ I) ≤
      (volume.prod volume).withDensity J := by
    refine Measure.le_iff.2 fun A hA => ?_
    rw [smul_apply, Measure.restrict_apply hA, withDensity_apply _ hA, smul_eq_mul]
    calc ENNReal.ofReal m * (volume.prod volume) (A ∩ I ×ˢ I)
        = ∫⁻ _ in A ∩ I ×ˢ I, ENNReal.ofReal m ∂(volume.prod volume) := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ p in A ∩ I ×ˢ I, J p ∂(volume.prod volume) :=
          lintegral_mono_ae (ae_restrict_of_ae_restrict_of_subset inter_subset_right hJ)
      _ ≤ ∫⁻ p in A, J p ∂(volume.prod volume) :=
          lintegral_mono_set inter_subset_left
  have := poincare_of_lower_bound hfin hpos hu hm hν
  have hg : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal ((u p.1 - u p.2) ^ 2)) := by
    have : Measurable (fun p : ℝ × ℝ => (u p.1 - u p.2) ^ 2) :=
      ((hum.comp measurable_fst).sub (hum.comp measurable_snd)).pow_const 2
    exact ENNReal.measurable_ofReal.comp this
  rw [lintegral_withDensity_eq_lintegral_mul _ hJm hg] at this
  exact this

/-- The diagonal of `ℝ × ℝ` is null for the product Lebesgue measure. -/
theorem volume_prod_diagonal : (volume.prod volume) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} := measurableSet_eq_fun measurable_fst
    measurable_snd
  rw [Measure.prod_apply hm]
  have : ∀ x : ℝ, volume (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0 := fun x => by
    have : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {x} := by
      ext y; simp [eq_comm]
    rw [this]; exact Real.volume_singleton
  simp

/-- **Fractional Poincaré inequality on an interval.** For `u ∈ L²(a, b)` and the kernel
`J(x, y) = (C/2) |x - y|^(-(1+α))` with `C > 0`, `α > 0`,
`∫_a^b (u - ū)² ≤ ((b-a)^α / C) ∬ J(x, y) (u x - u y)² dx dy`. -/
theorem poincare_gagliardo_interval {a b α C : ℝ} (hab : a < b) (hα : 0 < α) (hC : 0 < C)
    {u : ℝ → ℝ} (hum : Measurable u) (hu : MemLp u 2 (volume.restrict (Icc a b))) :
    ENNReal.ofReal (∫ x in Icc a b, (u x - (∫ y in Icc a b, u y) / (b - a)) ^ 2) ≤
      ENNReal.ofReal ((b - a) ^ α / C) *
        ∫⁻ p, ENNReal.ofReal (C / 2 * |p.1 - p.2| ^ (-(1 + α))) *
          ENNReal.ofReal ((u p.1 - u p.2) ^ 2) ∂(volume.prod volume) := by
  have hL : 0 < b - a := sub_pos.2 hab
  have hvol : (volume (Icc a b)).toReal = b - a := by simp [Real.volume_Icc, hL.le]
  set m : ℝ := C / 2 * (b - a) ^ (-(1 + α)) with hm
  have hmpos : 0 < m := by positivity
  have hJm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (C / 2 * |p.1 - p.2| ^ (-(1 + α)))) := by
    refine ENNReal.measurable_ofReal.comp ?_
    have hd : Measurable (fun p : ℝ × ℝ => |p.1 - p.2|) :=
      continuous_abs.measurable.comp (measurable_fst.sub measurable_snd)
    exact measurable_const.mul (hd.pow_const _)
  have hJ : ∀ᵐ p ∂((volume.prod volume).restrict (Icc a b ×ˢ Icc a b)),
      ENNReal.ofReal m ≤ ENNReal.ofReal (C / 2 * |p.1 - p.2| ^ (-(1 + α))) := by
    have hnull : ∀ᵐ p ∂(volume.prod volume), p ∉ {p : ℝ × ℝ | p.1 = p.2} :=
      measure_eq_zero_iff_ae_notMem.1 volume_prod_diagonal
    have hmem : ∀ᵐ p ∂((volume.prod volume).restrict (Icc a b ×ˢ Icc a b)),
        p ∈ Icc a b ×ˢ Icc a b := ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
    filter_upwards [ae_restrict_of_ae hnull, hmem] with p hp hpm
    refine ENNReal.ofReal_le_ofReal ?_
    have hne : 0 < |p.1 - p.2| := abs_pos.2 (sub_ne_zero.2 hp)
    have hle : |p.1 - p.2| ≤ b - a := by
      rw [abs_le]; constructor <;> linarith [hpm.1.1, hpm.1.2, hpm.2.1, hpm.2.2]
    have : (b - a) ^ (-(1 + α)) ≤ |p.1 - p.2| ^ (-(1 + α)) :=
      Real.rpow_le_rpow_of_nonpos hne hle (by linarith)
    rw [hm]
    gcongr
  have hfin : volume (Icc a b) ≠ ⊤ := by simp [Real.volume_Icc]
  have hpos : 0 < volume (Icc a b) := by simpa [Real.volume_Icc] using hL
  have := poincare_of_kernel_lower_bound (u := u) hfin hpos hu hmpos hum hJm hJ
  rw [hvol] at this
  refine this.trans (le_of_eq ?_)
  congr 2
  rw [hm]
  have h1 : (b - a) ^ (-(1 + α)) * (b - a) = (b - a) ^ (-α) := by
    rw [← Real.rpow_add_one hL.ne']; congr 1; ring
  have h2 : (b - a) ^ (-α) = ((b - a) ^ α)⁻¹ := Real.rpow_neg hL.le α
  have h3 : 2 * (C / 2 * (b - a) ^ (-(1 + α))) * (b - a) = C * ((b - a) ^ α)⁻¹ := by
    rw [← h2, ← h1]; ring
  rw [h3]
  field_simp

end

end FracLap
