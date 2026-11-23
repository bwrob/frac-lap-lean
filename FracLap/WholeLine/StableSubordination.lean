/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# FracLap.WholeLine.StableSubordination

Gaussian mixtures in the frequency variable and a closure calculus for positivity and radial
monotonicity of Fourier inversions. This is the analytic engine behind the positivity and
unimodality of the stable kernel.

A *Gaussian mixture* is a function `ξ ↦ ∫ exp (-ξ² s) dm(s)` with `m` a finite measure on `[0, ∞)`.
For `σ > 0` the Gaussian-regularized cosine transform of a mixture is an explicit mixture of
Gaussians in `a`, hence nonnegative and decreasing in `|a|`. This property (`IsGaussMonotone`)
passes to bounded pointwise limits, and mixtures are closed under sums, nonnegative multiples and
products.

- `integral_exp_neg_mul_sq_mul_cos`: `∫ exp (-b ξ²) cos (a ξ) dξ = √(π / b) exp (-a² / (4 b))`.
- `gaussMixture`: the mixture of a measure; `gaussMixture_mul`, `gaussMixture_add`.
- `IsGaussMix`: closure under sums, nonnegative multiples and products.
- `integral_gauss_cos_mul_gaussMixture`: the regularized cosine transform of a mixture.
- `IsGaussMonotone`: the property, `IsGaussMix.isGaussMonotone`, and `IsGaussMonotone.of_tendsto`.
-/

namespace FracLap

open MeasureTheory Set Filter Topology
open scoped NNReal

@[expose] public section

/-! ### The Gaussian cosine integral -/

/-- `∫ exp (-b ξ²) cos (a ξ) dξ = √(π / b) exp (-a² / (4 b))` for `b > 0`. -/
theorem integral_exp_neg_mul_sq_mul_cos {b : ℝ} (hb : 0 < b) (a : ℝ) :
    ∫ ξ : ℝ, Real.exp (-b * ξ ^ 2) * Real.cos (a * ξ) =
      √(Real.pi / b) * Real.exp (-a ^ 2 / (4 * b)) := by
  have hb' : 0 < (b : ℂ).re := by simpa using hb
  have h := fourierIntegral_gaussian hb' (a : ℂ)
  have hint : Integrable (fun x : ℝ => Complex.exp (Complex.I * (a : ℂ) * x) *
      Complex.exp (-(b : ℂ) * x ^ 2)) := by
    have := integrable_cexp_quadratic hb' (Complex.I * (a : ℂ)) 0
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [add_zero, ← Complex.exp_add]
    congr 1
    ring
  have hre := congrArg Complex.re h
  have hI := integral_re hint
  simp only [RCLike.re_to_complex] at hI
  rw [← hI] at hre
  have hLHS : ∀ x : ℝ, (Complex.exp (Complex.I * (a : ℂ) * x) *
      Complex.exp (-(b : ℂ) * x ^ 2)).re = Real.exp (-b * x ^ 2) * Real.cos (a * x) := by
    intro x
    rw [← Complex.exp_add, show Complex.I * (a : ℂ) * x + -(b : ℂ) * x ^ 2 =
        ((-b * x ^ 2 : ℝ) : ℂ) + ((a * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  simp only [hLHS] at hre
  rw [hre]
  have hπ : ((Real.pi : ℂ) / (b : ℂ)) = ((Real.pi / b : ℝ) : ℂ) := by push_cast; rfl
  rw [hπ, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow
    (div_pos Real.pi_pos hb).le, show -(a : ℂ) ^ 2 / (4 * (b : ℂ)) =
      ((-a ^ 2 / (4 * b) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp,
    ← Complex.ofReal_mul, Complex.ofReal_re, Real.sqrt_eq_rpow, one_div]

/-! ### Gaussian mixtures -/

/-- The Gaussian mixture `ξ ↦ ∫ exp (-ξ² s) dm(s)` of a measure `m` on `[0, ∞)`. -/
noncomputable def gaussMixture (m : Measure ℝ≥0) (ξ : ℝ) : ℝ :=
  ∫ s, Real.exp (-(ξ ^ 2) * (s : ℝ)) ∂m

/-- The mixture integrand is integrable for a finite measure. -/
theorem integrable_exp_neg_sq_mul (m : Measure ℝ≥0) [IsFiniteMeasure m] (ξ : ℝ) :
    Integrable (fun s : ℝ≥0 => Real.exp (-(ξ ^ 2) * (s : ℝ))) m := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (Filter.Eventually.of_forall fun s => ?_)
  · exact (by fun_prop :
      Continuous fun s : ℝ≥0 => Real.exp (-(ξ ^ 2) * (s : ℝ))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have : 0 ≤ ξ ^ 2 * (s : ℝ) := mul_nonneg (sq_nonneg _) s.coe_nonneg
    linarith

/-- Mixtures are nonnegative. -/
theorem gaussMixture_nonneg (m : Measure ℝ≥0) (ξ : ℝ) : 0 ≤ gaussMixture m ξ :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- Mixtures of a finite measure are bounded by its total mass. -/
theorem gaussMixture_le (m : Measure ℝ≥0) [IsFiniteMeasure m] (ξ : ℝ) :
    gaussMixture m ξ ≤ m.real univ := by
  have h : gaussMixture m ξ ≤ ∫ _ : ℝ≥0, (1 : ℝ) ∂m := by
    refine integral_mono (integrable_exp_neg_sq_mul m ξ) (integrable_const 1) fun s => ?_
    rw [Real.exp_le_one_iff]
    have : 0 ≤ ξ ^ 2 * (s : ℝ) := mul_nonneg (sq_nonneg _) s.coe_nonneg
    linarith
  simpa using h

/-- Mixtures add with the measures. -/
theorem gaussMixture_add (m₁ m₂ : Measure ℝ≥0) [IsFiniteMeasure m₁] [IsFiniteMeasure m₂] (ξ : ℝ) :
    gaussMixture (m₁ + m₂) ξ = gaussMixture m₁ ξ + gaussMixture m₂ ξ :=
  integral_add_measure (integrable_exp_neg_sq_mul m₁ ξ) (integrable_exp_neg_sq_mul m₂ ξ)

/-- Mixtures scale with nonnegative multiples of the measure. -/
theorem gaussMixture_smul (m : Measure ℝ≥0) {c : ℝ} (hc : 0 ≤ c) (ξ : ℝ) :
    gaussMixture (ENNReal.ofReal c • m) ξ = c * gaussMixture m ξ := by
  unfold gaussMixture
  rw [integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul]

/-- The unit point mass at `0` has the constant mixture `1`. -/
theorem gaussMixture_dirac_zero (ξ : ℝ) : gaussMixture (Measure.dirac (0 : ℝ≥0)) ξ = 1 := by
  simp [gaussMixture]

/-- The sum-pushforward of the product of two measures (the additive convolution on `[0, ∞)`). -/
noncomputable def mixMul (m₁ m₂ : Measure ℝ≥0) : Measure ℝ≥0 :=
  (m₁.prod m₂).map fun p => p.1 + p.2

instance (m₁ m₂ : Measure ℝ≥0) [IsFiniteMeasure m₁] [IsFiniteMeasure m₂] :
    IsFiniteMeasure (mixMul m₁ m₂) := by
  unfold mixMul
  infer_instance

/-- **Products of mixtures are mixtures**: the Laplace transform turns convolution into product. -/
theorem gaussMixture_mixMul (m₁ m₂ : Measure ℝ≥0) [IsFiniteMeasure m₁] [IsFiniteMeasure m₂]
    (ξ : ℝ) : gaussMixture (mixMul m₁ m₂) ξ = gaussMixture m₁ ξ * gaussMixture m₂ ξ := by
  unfold gaussMixture mixMul
  rw [integral_map (by fun_prop : Measurable fun p : ℝ≥0 × ℝ≥0 => p.1 + p.2).aemeasurable
    (by fun_prop : Continuous fun s : ℝ≥0 => Real.exp (-(ξ ^ 2) * (s : ℝ))).aestronglyMeasurable]
  have : ∀ p : ℝ≥0 × ℝ≥0, Real.exp (-(ξ ^ 2) * ((p.1 + p.2 : ℝ≥0) : ℝ)) =
      Real.exp (-(ξ ^ 2) * (p.1 : ℝ)) * Real.exp (-(ξ ^ 2) * (p.2 : ℝ)) := by
    intro p
    rw [← Real.exp_add, NNReal.coe_add, mul_add]
  simp_rw [this]
  exact integral_prod_mul (μ := m₁) (ν := m₂) (fun s : ℝ≥0 => Real.exp (-(ξ ^ 2) * (s : ℝ)))
    (fun s : ℝ≥0 => Real.exp (-(ξ ^ 2) * (s : ℝ)))

/-- A function is a *Gaussian mixture* if it is `ξ ↦ ∫ exp (-ξ² s) dm(s)` for a finite measure
`m` on `[0, ∞)`. -/
def IsGaussMix (F : ℝ → ℝ) : Prop :=
  ∃ m : Measure ℝ≥0, IsFiniteMeasure m ∧ ∀ ξ, F ξ = gaussMixture m ξ

/-- Nonnegative constants are mixtures. -/
theorem IsGaussMix.const {c : ℝ} (hc : 0 ≤ c) : IsGaussMix fun _ => c :=
  ⟨ENNReal.ofReal c • Measure.dirac 0, Measure.smul_finite _ ENNReal.ofReal_ne_top, fun ξ => by
    rw [gaussMixture_smul _ hc, gaussMixture_dirac_zero, mul_one]⟩

/-- Sums of mixtures are mixtures. -/
theorem IsGaussMix.add {F G : ℝ → ℝ} (hF : IsGaussMix F) (hG : IsGaussMix G) :
    IsGaussMix fun ξ => F ξ + G ξ := by
  obtain ⟨m₁, h₁, e₁⟩ := hF
  obtain ⟨m₂, h₂, e₂⟩ := hG
  exact ⟨m₁ + m₂, inferInstance, fun ξ => by
    change F ξ + G ξ = _
    rw [e₁, e₂, gaussMixture_add]⟩

/-- Nonnegative multiples of mixtures are mixtures. -/
theorem IsGaussMix.const_mul {F : ℝ → ℝ} (hF : IsGaussMix F) {c : ℝ} (hc : 0 ≤ c) :
    IsGaussMix fun ξ => c * F ξ := by
  obtain ⟨m, h, e⟩ := hF
  exact ⟨ENNReal.ofReal c • m, Measure.smul_finite _ ENNReal.ofReal_ne_top, fun ξ => by
    change c * F ξ = _
    rw [e, gaussMixture_smul _ hc]⟩

/-- Products of mixtures are mixtures. -/
theorem IsGaussMix.mul {F G : ℝ → ℝ} (hF : IsGaussMix F) (hG : IsGaussMix G) :
    IsGaussMix fun ξ => F ξ * G ξ := by
  obtain ⟨m₁, h₁, e₁⟩ := hF
  obtain ⟨m₂, h₂, e₂⟩ := hG
  exact ⟨mixMul m₁ m₂, inferInstance, fun ξ => by
    change F ξ * G ξ = _
    rw [e₁, e₂, gaussMixture_mixMul]⟩

/-! ### Gaussian-regularized cosine transform -/

/-- The Gaussian-regularized cosine transform `∫ exp (-σ ξ²) cos (a ξ) F(ξ) dξ`. -/
noncomputable def gaussCos (σ a : ℝ) (F : ℝ → ℝ) : ℝ :=
  ∫ ξ : ℝ, Real.exp (-σ * ξ ^ 2) * Real.cos (a * ξ) * F ξ

/-- The regularized cosine transform of a mixture is an explicit mixture of Gaussians in `a`. -/
theorem gaussCos_gaussMixture {σ : ℝ} (hσ : 0 < σ) (a : ℝ) (m : Measure ℝ≥0)
    [IsFiniteMeasure m] :
    gaussCos σ a (gaussMixture m) =
      ∫ s : ℝ≥0, √(Real.pi / (σ + s)) * Real.exp (-a ^ 2 / (4 * (σ + s))) ∂m := by
  unfold gaussCos gaussMixture
  have hmul : ∀ ξ : ℝ, Real.exp (-σ * ξ ^ 2) * Real.cos (a * ξ) *
      ∫ s : ℝ≥0, Real.exp (-(ξ ^ 2) * (s : ℝ)) ∂m =
      ∫ s : ℝ≥0, Real.exp (-σ * ξ ^ 2) * Real.cos (a * ξ) * Real.exp (-(ξ ^ 2) * (s : ℝ)) ∂m :=
    fun ξ => (integral_const_mul _ _).symm
  simp_rw [hmul]
  have hint : Integrable (Function.uncurry fun (ξ : ℝ) (s : ℝ≥0) =>
      Real.exp (-σ * ξ ^ 2) * Real.cos (a * ξ) * Real.exp (-(ξ ^ 2) * (s : ℝ)))
      (volume.prod m) := by
    have hg : Integrable (fun ξ : ℝ => Real.exp (-σ * ξ ^ 2)) := by
      simpa [neg_mul] using integrable_exp_neg_mul_sq hσ
    have hb : Integrable (fun z : ℝ × ℝ≥0 => Real.exp (-σ * z.1 ^ 2) * (1 : ℝ))
        (volume.prod m) := Integrable.mul_prod hg (integrable_const (1 : ℝ))
    refine hb.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (by fun_prop : Continuous fun z : ℝ × ℝ≥0 => Real.exp (-σ * z.1 ^ 2) *
        Real.cos (a * z.1) * Real.exp (-(z.1 ^ 2) * (z.2 : ℝ))).aestronglyMeasurable
    · simp only [Real.norm_eq_abs, mul_one]
      change |Real.exp (-σ * z.1 ^ 2) * Real.cos (a * z.1) * Real.exp (-z.1 ^ 2 * (z.2 : ℝ))| ≤ _
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      have h1 : |Real.cos (a * z.1)| ≤ 1 := Real.abs_cos_le_one _
      have h2 : Real.exp (-(z.1 ^ 2) * (z.2 : ℝ)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ z.1 ^ 2 * (z.2 : ℝ) := mul_nonneg (sq_nonneg _) z.2.coe_nonneg
        linarith
      have h3 := Real.exp_pos (-σ * z.1 ^ 2)
      calc Real.exp (-σ * z.1 ^ 2) * |Real.cos (a * z.1)| * Real.exp (-(z.1 ^ 2) * (z.2 : ℝ))
          ≤ Real.exp (-σ * z.1 ^ 2) * 1 * 1 := by gcongr
        _ = Real.exp (-σ * z.1 ^ 2) := by ring
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  have hb : 0 < σ + (s : ℝ) := by positivity
  have := integral_exp_neg_mul_sq_mul_cos hb a
  change _ = √(Real.pi / (σ + (s : ℝ))) * Real.exp (-a ^ 2 / (4 * (σ + (s : ℝ))))
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  beta_reduce
  have hexp : Real.exp (-(σ + (s : ℝ)) * ξ ^ 2) =
      Real.exp (-σ * ξ ^ 2) * Real.exp (-ξ ^ 2 * (s : ℝ)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hexp]
  ring

/-! ### Positivity and monotonicity of the regularized transform -/

/-- A function `F` is *Gaussian monotone* if its Gaussian-regularized cosine transform is
nonnegative and nonincreasing in `a ≥ 0`, for every regularization `σ > 0`. -/
def IsGaussMonotone (F : ℝ → ℝ) : Prop :=
  ∀ σ a b : ℝ, 0 < σ → 0 ≤ a → a ≤ b → 0 ≤ gaussCos σ b F ∧ gaussCos σ b F ≤ gaussCos σ a F

/-- The Gaussian profile `s ↦ √(π / (σ + s)) exp (-a² / (4 (σ + s)))` is integrable. -/
theorem integrable_gaussProfile {σ : ℝ} (hσ : 0 < σ) (a : ℝ) (m : Measure ℝ≥0)
    [IsFiniteMeasure m] :
    Integrable (fun s : ℝ≥0 => √(Real.pi / (σ + s)) * Real.exp (-a ^ 2 / (4 * (σ + s)))) m := by
  refine Integrable.mono' (integrable_const √(Real.pi / σ)) ?_
    (Filter.Eventually.of_forall fun s => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    have h1 : ∀ s : ℝ≥0, σ + (s : ℝ) ≠ 0 := fun s => by positivity
    have h2 : ∀ s : ℝ≥0, 4 * (σ + (s : ℝ)) ≠ 0 := fun s => by positivity
    have hc : Continuous fun s : ℝ≥0 => σ + (s : ℝ) := continuous_const.add NNReal.continuous_coe
    exact (Real.continuous_sqrt.comp (continuous_const.div hc h1)).mul
      (Real.continuous_exp.comp (continuous_const.div (continuous_const.mul hc) h2))
  · have hs : 0 < σ + (s : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : √(Real.pi / (σ + s)) ≤ √(Real.pi / σ) := by
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_left Real.pi_pos.le hσ (by linarith [s.coe_nonneg])
    have h2 : Real.exp (-a ^ 2 / (4 * (σ + s))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg a]) (by positivity)
    calc √(Real.pi / (σ + s)) * Real.exp (-a ^ 2 / (4 * (σ + s)))
        ≤ √(Real.pi / σ) * 1 := mul_le_mul h1 h2 (Real.exp_pos _).le (Real.sqrt_nonneg _)
      _ = √(Real.pi / σ) := mul_one _

/-- **Gaussian mixtures are Gaussian monotone.** -/
theorem IsGaussMix.isGaussMonotone {F : ℝ → ℝ} (hF : IsGaussMix F) : IsGaussMonotone F := by
  obtain ⟨m, hm, e⟩ := hF
  have hFm : F = gaussMixture m := funext e
  subst hFm
  intro σ a b hσ ha hab
  rw [gaussCos_gaussMixture hσ a m, gaussCos_gaussMixture hσ b m]
  refine ⟨integral_nonneg fun s => by positivity, ?_⟩
  refine integral_mono (integrable_gaussProfile hσ b m) (integrable_gaussProfile hσ a m)
    fun s => ?_
  have hs : 0 < σ + (s : ℝ) := by positivity
  have hsq : a ^ 2 ≤ b ^ 2 := by nlinarith
  gcongr

/-- Gaussian monotonicity passes to bounded pointwise limits of measurable functions. -/
theorem IsGaussMonotone.of_tendsto {Fn : ℕ → ℝ → ℝ} {F : ℝ → ℝ} {C : ℝ}
    (hmeas : ∀ n, Measurable (Fn n)) (hbound : ∀ n ξ, |Fn n ξ| ≤ C)
    (hlim : ∀ ξ, Tendsto (fun n => Fn n ξ) atTop (𝓝 (F ξ)))
    (h : ∀ n, IsGaussMonotone (Fn n)) : IsGaussMonotone F := by
  have hFmeas : Measurable F := measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 hlim)
  intro σ a b hσ ha hab
  have hconv : ∀ x : ℝ, Tendsto (fun n => gaussCos σ x (Fn n)) atTop (𝓝 (gaussCos σ x F)) := by
    intro x
    have hg : Integrable (fun ξ : ℝ => C * Real.exp (-σ * ξ ^ 2)) := by
      have : Integrable (fun ξ : ℝ => Real.exp (-σ * ξ ^ 2)) := by
        simpa [neg_mul] using integrable_exp_neg_mul_sq hσ
      exact this.const_mul C
    refine tendsto_integral_of_dominated_convergence (fun ξ => C * Real.exp (-σ * ξ ^ 2))
      (fun n => ?_) hg (fun n => ?_) (Filter.Eventually.of_forall fun ξ => ?_)
    · exact (by fun_prop : Measurable fun ξ : ℝ => Real.exp (-σ * ξ ^ 2) * Real.cos (x * ξ)).mul
        (hmeas n) |>.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have h1 : |Real.cos (x * ξ)| ≤ 1 := Real.abs_cos_le_one _
      have h2 := hbound n ξ
      have h3 := Real.exp_pos (-σ * ξ ^ 2)
      have hC : 0 ≤ C := (abs_nonneg _).trans h2
      calc Real.exp (-σ * ξ ^ 2) * |Real.cos (x * ξ)| * |Fn n ξ|
          ≤ Real.exp (-σ * ξ ^ 2) * 1 * C := by gcongr
        _ = C * Real.exp (-σ * ξ ^ 2) := by ring
    · exact ((hlim ξ).const_mul _)
  have h1 := hconv b
  have h2 := hconv a
  exact ⟨ge_of_tendsto' h1 fun n => (h n σ a b hσ ha hab).1,
    le_of_tendsto_of_tendsto' h1 h2 fun n => (h n σ a b hσ ha hab).2⟩

/-! ### Compound-Poisson type exponentials -/

/-- Mixtures are continuous in the frequency. -/
theorem continuous_gaussMixture (m : Measure ℝ≥0) [IsFiniteMeasure m] :
    Continuous (gaussMixture m) := by
  unfold gaussMixture
  refine continuous_of_dominated (bound := fun _ => 1) (fun ξ => ?_) (fun ξ => ?_)
    (integrable_const 1) ?_
  · exact (by fun_prop :
      Continuous fun s : ℝ≥0 => Real.exp (-(ξ ^ 2) * (s : ℝ))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have : 0 ≤ ξ ^ 2 * (s : ℝ) := mul_nonneg (sq_nonneg _) s.coe_nonneg
    linarith
  · refine Filter.Eventually.of_forall fun s => ?_
    fun_prop

/-- A mixture never exceeds its value at frequency `0`. -/
theorem gaussMixture_le_zero (m : Measure ℝ≥0) [IsFiniteMeasure m] (ξ : ℝ) :
    gaussMixture m ξ ≤ gaussMixture m 0 := by
  unfold gaussMixture
  refine integral_mono (integrable_exp_neg_sq_mul m ξ) (integrable_exp_neg_sq_mul m 0) fun s => ?_
  rw [Real.exp_le_exp]
  have : 0 ≤ ξ ^ 2 * (s : ℝ) := mul_nonneg (sq_nonneg _) s.coe_nonneg
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_mul]
  linarith

/-- Powers of mixtures are mixtures. -/
theorem IsGaussMix.pow {F : ℝ → ℝ} (hF : IsGaussMix F) (n : ℕ) : IsGaussMix fun ξ => F ξ ^ n := by
  induction n with
  | zero => simpa using IsGaussMix.const (zero_le_one' ℝ)
  | succ k ih =>
    simpa [pow_succ] using ih.mul hF

/-- **Exponentials of compound-Poisson type.** For a finite measure `m` with mixture `H` and
`t ≥ 0`, the function `ξ ↦ exp (-t (H 0 - H ξ))` is Gaussian monotone. It is the bounded pointwise
limit of the mixtures `exp (-t H 0) (1 + t H / n)^n`. -/
theorem isGaussMonotone_exp_sub (m : Measure ℝ≥0) [IsFiniteMeasure m] {t : ℝ} (ht : 0 ≤ t) :
    IsGaussMonotone fun ξ => Real.exp (-t * (gaussMixture m 0 - gaussMixture m ξ)) := by
  set H := gaussMixture m with hH
  have hHc : Continuous H := continuous_gaussMixture m
  have hmix : ∀ n : ℕ, IsGaussMix fun ξ => Real.exp (-t * H 0) * (1 + t / n * H ξ) ^ n := by
    intro n
    have h1 : IsGaussMix fun ξ => 1 + t / n * H ξ :=
      (IsGaussMix.const zero_le_one).add
        (IsGaussMix.const_mul ⟨m, inferInstance, fun ξ => rfl⟩ (by positivity))
    exact (IsGaussMix.const (Real.exp_pos _).le).mul (h1.pow n)
  refine IsGaussMonotone.of_tendsto (C := 1) (Fn := fun n ξ =>
    Real.exp (-t * H 0) * (1 + t / n * H ξ) ^ n) (fun n => ?_) (fun n ξ => ?_) (fun ξ => ?_)
    (fun n => (hmix n).isGaussMonotone)
  · exact (by fun_prop : Continuous fun ξ => Real.exp (-t * H 0) *
      (1 + t / n * H ξ) ^ n).measurable
  · have hH0 : 0 ≤ H ξ := gaussMixture_nonneg m ξ
    have hle : H ξ ≤ H 0 := gaussMixture_le_zero m ξ
    have hbase : 0 ≤ 1 + t / n * H ξ := by positivity
    rw [abs_of_nonneg (by positivity)]
    have h1 : (1 + t / n * H ξ) ^ n ≤ Real.exp (t * H ξ) := by
      have := Real.one_add_div_pow_le_exp (m := n) (x := t * H ξ) (by
        have : 0 ≤ t * H ξ := by positivity
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [pow_zero]
        exact Real.one_le_exp (by positivity)
      · rwa [show t / n * H ξ = t * H ξ / n by ring]
    calc Real.exp (-t * H 0) * (1 + t / n * H ξ) ^ n
        ≤ Real.exp (-t * H 0) * Real.exp (t * H ξ) := by gcongr
      _ = Real.exp (-t * (H 0 - H ξ)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ t * (H 0 - H ξ) := mul_nonneg ht (by linarith)
        linarith
  · have h := (Real.tendsto_one_add_div_pow_exp (t * H ξ)).const_mul (Real.exp (-t * H 0))
    have h2 : ∀ n : ℕ, Real.exp (-t * H 0) * (1 + t / n * H ξ) ^ n =
        Real.exp (-t * H 0) * (1 + t * H ξ / n) ^ n := fun n => by ring_nf
    simp_rw [h2]
    convert h using 2
    rw [← Real.exp_add]
    ring_nf

end

end FracLap
