/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Core.Pointwise
public import FracLap.Core.Semigroups
public import FracLap.Core.C0Semigroup
public import FracLap.Core.ContractiveResolvent
public import FracLap.Core.HilleYosidaGeneration
public import FracLap.Core.HilleYosidaCorrespondence
public import FracLap.Core.LpExtension
public import FracLap.Core.FourierSobolev
public import FracLap.WholeLine.AnomalousDiffusion
public import FracLap.WholeLine.ClassicalKernels
public import FracLap.HalfLine.ReflectedSemigroup
public import FracLap.HalfLine.RestrictedDirichlet
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLapTest.HalfLineTest

Anti-vacuity positive witnesses and negative counterexamples for:
- `FracLap.Core.Pointwise` (`FractionalExponent`, `fracLapConstant`, `secondDiff`, `oddExt`,
  `IsOddFunc`, `IsEvenFunc`, `reflectedKernel`)
- `FracLap.Core.Semigroups` (`ContractionSemigroup`, `OddSubspaceConjugation`,
  `SymmetricAccretiveForm`, `IsMarkovDirichletForm`)
- `FracLap.WholeLine.AnomalousDiffusion` (`fourierResolventSymbol_bounds`,
  `fourierSemigroupSymbol_add`, `symmetricAccretiveFormOfSqrt`)
- `FracLap.HalfLine.ReflectedSemigroup` (`reflectedContractionSemigroup`)
- `FracLap.HalfLine.RestrictedDirichlet` (`VanishesOnNeg`, `restrictSymmetricAccretiveForm`,
  `restrictedForm_isMarkovDirichletForm`, `gagliardoWeight_pos`, `gagliardoForm`,
  `restrictedGagliardoForm_isMarkovDirichletForm`, `gagliardoTent`,
  `exists_restrictedGagliardoForm_pos`)
-/

namespace FracLapTest

open FracLap Real
open scoped ENNReal NNReal

@[expose] public section

/-! ### 1. FractionalExponent & Normalizing Constant Anti-Vacuity -/

example : FractionalExponent (1 : ℝ) := fractionalExponent_one

example : FractionalExponent (3 / 2 : ℝ) := by
  constructor <;> norm_num

example : ¬ FractionalExponent (0 : ℝ) := by
  rintro ⟨h0, _⟩
  norm_num at h0

example : ¬ FractionalExponent (2 : ℝ) := by
  rintro ⟨_, h2⟩
  norm_num at h2

example : 0 < fracLapConstant (1 : ℝ) :=
  fracLapConstant_pos fractionalExponent_one

/-- Exact closed-form value at `α = 1`: `C(1) = 1 / π`. -/
example : fracLapConstant (1 : ℝ) = Real.pi⁻¹ := by
  unfold fracLapConstant
  have h0 : (1 + (1 : ℝ)) / 2 = 1 := by norm_num
  have h1 : 1 - (1 : ℝ) / 2 = 1 / 2 := by norm_num
  have h2 : (1 : ℝ) - 1 = 0 := by norm_num
  rw [h0, h1, h2, Real.rpow_zero, Real.Gamma_one, Real.Gamma_one_half_eq]
  have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  calc 1 * 1 * 1 / (Real.sqrt Real.pi * Real.sqrt Real.pi)
      = 1 / Real.pi := by rw [hsq]; ring
    _ = Real.pi⁻¹ := one_div _

/-- Endpoint boundary behavior of `C(α)` and `Γ(1 - α / 2)`. -/
example : Filter.Tendsto fracLapConstant (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto fracLapConstant (nhdsWithin 2 (Set.Iio 2)) (nhds 0) ∧
    Filter.Tendsto (fun α : ℝ => Real.Gamma (1 - α / 2))
      (nhdsWithin 2 (Set.Iio 2)) Filter.atTop :=
  ⟨tendsto_fracLapConstant_zero, tendsto_fracLapConstant_two, tendsto_gamma_one_sub_half_two⟩

/-! ### 2. Odd Extension, Second Difference, and Reflected Singular Kernel Anti-Vacuity -/

/-- Positive witness: `oddExt (fun x => x)` is the identity `x ↦ x`, which is odd. -/
example : IsOddFunc (oddExt (fun x : ℝ => x)) :=
  isOddFunc_oddExt (fun x : ℝ => x)

/-- Negative counterexample: the constant function `1` is not odd. -/
example : ¬ IsOddFunc (fun _ : ℝ => (1 : ℝ)) := by
  intro h
  have h0 : (1 : ℝ) = 0 := h.map_zero
  norm_num at h0

/-- Positive witness: the constant function `1` is even. -/
example : IsEvenFunc (fun _ : ℝ => (1 : ℝ)) := by
  intro _
  rfl

/-- Negative counterexample: `x ↦ x` is not even. -/
example : ¬ IsEvenFunc (fun x : ℝ => x) := by
  intro h
  have h1 : (-1 : ℝ) = 1 := h 1
  norm_num at h1

/-- Positive witness: at the maximum `x₀ = 0` of `u(x) = -x^2`, `secondDiff u 0 y = -2 y^2 ≤ 0`. -/
example (y : ℝ) : secondDiff (fun x : ℝ => -(x ^ 2)) 0 y ≤ 0 := by
  apply secondDiff_nonpos_of_isMax
  intro z
  have h : 0 ≤ z ^ 2 := sq_nonneg z
  linarith

/-- Negative counterexample: at the minimum `x₀ = 0` of `u(x) = x^2`, `secondDiff u 0 1 = 2 > 0`. -/
example : ¬ (secondDiff (fun x : ℝ => x ^ 2) 0 1 ≤ 0) := by
  unfold secondDiff
  norm_num

/-- Positive witness: `reflectedKernel 1 1 2 > 0`. -/
example : 0 < reflectedKernel 1 1 2 :=
  reflectedKernel_pos fractionalExponent_one (by norm_num) (by norm_num) (by norm_num)

/-- Negative counterexample: on the diagonal `x = y`, `reflectedKernel 1 1 1` is not positive. -/
example : ¬ (0 < reflectedKernel 1 1 1) := by
  unfold reflectedKernel
  have h0 : |(1 : ℝ) - 1| ^ (1 + (1 : ℝ)) = 0 := by norm_num
  have hpos : 0 < 1 / |(1 : ℝ) + 1| ^ (1 + (1 : ℝ)) := by positivity
  rw [h0, div_zero]
  linarith

/-! ### 3. Concrete Witness for `ContractionSemigroup`, `OddSubspaceConjugation`,
`SymmetricAccretiveForm`, and `IsMarkovDirichletForm` -/

/-- Concrete scalar contraction semigroup `T(t) u = u` on `ℝ`. -/
def idContractionSemigroup : ContractionSemigroup ℝ where
  T _ u := u
  normE u := |u|
  normE_nonneg u := abs_nonneg u
  map_zero_time _ := rfl
  map_add_time _ _ _ _ _ := rfl
  contractive _ _ _ := le_rfl

/-- Concrete odd subspace conjugation witness between `H = ℝ` and `E = ℝ × ℝ`
(representing a function on `(-∞, 0) ∪ (0, ∞)` by its left and right values `(u_neg, u_pos)`
with oddness `u_neg = -u_pos` and norm `√(u_neg^2 + u_pos^2)`). -/
noncomputable def twoPointOddConjugation :
    OddSubspaceConjugation (ℝ × ℝ) ℝ
      (fun p : ℝ × ℝ => sqrt (p.1 ^ 2 + p.2 ^ 2))
      (fun u : ℝ => |u|) where
  IsOdd p := p.1 = -p.2
  extOp u := (-u, u)
  restOp p := p.2
  extOp_isOdd _ := rfl
  restOp_extOp _ := rfl
  extOp_restOp_of_isOdd p hp := by
    ext
    · exact hp.symm
    · rfl
  norm_extOp u := by
    have h1 : (-u) ^ 2 + u ^ 2 = 2 * u ^ 2 := by ring
    rw [h1, sqrt_mul (by norm_num), sqrt_sq_eq_abs]
  norm_restOp_of_isOdd p hp := by
    have h1 : p.1 ^ 2 + p.2 ^ 2 = 2 * p.2 ^ 2 := by
      rw [hp]
      ring
    rw [h1, sqrt_mul (by norm_num), sqrt_sq_eq_abs]

/-- Concrete witness for `SymmetricAccretiveForm ℝ`: `B(u, v) = u * v`. -/
def scalarSquareForm : SymmetricAccretiveForm ℝ :=
  symmetricAccretiveFormOfSqrt id (fun x y : ℝ => x * y)
    (fun x y => mul_comm x y)
    (fun x => mul_self_nonneg x)
    (fun x y => by
      have h : (x * y) ^ 2 = (x * x) * (y * y) := by ring
      linarith)

/-- Positive witness: `scalarSquareForm` satisfies both Beurling–Deny Markov conditions
under `u ↦ |u|` and `u ↦ min (|u|) 1` on nonnegative scalars (or `u ↦ |u|` and
`u ↦ max 0 (min u 1)`). Here we check `u ↦ |u|` and `u ↦ if |u| ≤ 1 then u else 0`. -/
example : IsMarkovDirichletForm scalarSquareForm
    (fun u : ℝ => |u|) (fun u : ℝ => if |u| ≤ 1 then u else 0) where
  form_abs_le u := by
    change |u| * |u| ≤ u * u
    rw [abs_mul_abs_self]
  form_capOne_le u := by
    change (if |u| ≤ 1 then u else 0) * (if |u| ≤ 1 then u else 0) ≤ u * u
    split_ifs
    · exact le_rfl
    · simp [mul_self_nonneg u]

/-! ### 4. Exterior-Dirichlet Condition `VanishesOnNeg` Anti-Vacuity -/

/-- Positive witness: `u(x) = max x 0` satisfies `VanishesOnNeg`. -/
theorem vanishesOnNeg_max_zero : VanishesOnNeg (fun x : ℝ => max x 0) := by
  intro x hx
  exact max_eq_right (le_of_lt hx)

/-- Negative counterexample: `u(x) = 1` does not satisfy `VanishesOnNeg`. -/
example : ¬ VanishesOnNeg (fun _ : ℝ => (1 : ℝ)) := by
  intro h
  have h1 : (1 : ℝ) = 0 := h (-1) (by norm_num)
  norm_num at h1

/-! ### 5. Onboarded `C0Semigroup`, `LpExtension`, and `FourierSobolev` -/

/-- Concrete `StronglyContinuousContractionSemigroup ℝ`: the identity semigroup `S(t) = id`. -/
noncomputable def idC0Semigroup : StronglyContinuousContractionSemigroup ℝ where
  operator _ := ContinuousLinearMap.id ℝ ℝ
  operator_zero := rfl
  operator_add _ _ := rfl
  opNorm_le_one _ := ContinuousLinearMap.norm_id_le
  continuous_orbit _ := continuous_const

/-- Positive witness: the generator domain of `idC0Semigroup` is dense in `ℝ`. -/
example : Dense (idC0Semigroup.generatorDomain : Set ℝ) :=
  idC0Semigroup.dense_generatorDomain

/-- Positive witness: the Hille--Yosida contractive resolvent of `idC0Semigroup` is non-vacuous
and its generated semigroup recovers `idC0Semigroup` with norm-1 resolvent at `μ = 1`. -/
example :
    idC0Semigroup.toContractiveResolvent.generatedSemigroup = idC0Semigroup ∧
      ‖idC0Semigroup.toContractiveResolvent.operator ⟨1, by norm_num⟩‖ ≤ 1 :=
  ⟨idC0Semigroup.generatedSemigroup_toContractiveResolvent, by
    simpa using idC0Semigroup.toContractiveResolvent.opNorm_le_inv ⟨1, by norm_num⟩⟩

/-- Positive witness: for any `R : ContractiveResolvent ℝ`, taking the resolvent of the Yosida
generated semigroup recovers `R`. -/
example :
    idC0Semigroup.toContractiveResolvent.generatedSemigroup.toContractiveResolvent =
      idC0Semigroup.toContractiveResolvent :=
  ContractiveResolvent.toContractiveResolvent_generatedSemigroup
    idC0Semigroup.toContractiveResolvent

/-- Positive witness: `exists_smooth_exterior_cutoff` produces a smooth cutoff `ϕ : ℝ → ℝ`
vanishing on `[-1, 1]` and equal to `1` on `{|x| ≥ 2}`. -/
example : ∃ ϕ : ℝ → ℝ, ϕ 0 = 0 ∧ ϕ 3 = 1 := by
  obtain ⟨ϕ, _, _, h0, h1⟩ := exists_smooth_exterior_cutoff
  exact ⟨ϕ, h0 0 (by norm_num), h1 3 (by norm_num)⟩

/-- Positive witness: Bessel symbol equivalence bounds at `α = 1`, `ξ = 2`. -/
example :
    (1 / 2 : ℝ) * (1 + |(2 : ℝ)| ^ (2 * (1 : ℝ))) ≤ (1 + (2 : ℝ) ^ 2) ^ (1 : ℝ) ∧
      (1 + (2 : ℝ) ^ 2) ^ (1 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) * (1 + |(2 : ℝ)| ^ (2 * (1 : ℝ))) :=
  ⟨half_mul_le_besselSymbol (by norm_num) 2, besselSymbol_le_two_rpow_mul (by norm_num) 2⟩

/-! ### 6. Classical α = 1 (Cauchy) and α = 2 (Gaussian) fractional heat kernels -/

/-- Closed-form kernel evaluations at `x = 0`, `t = 1` for `cauchyHeatKernel` and
`gaussianHeatKernel`. -/
example :
    cauchyHeatKernel.P 0 1 = 1 / Real.pi ∧
      gaussianHeatKernel.P 0 1 = 1 / Real.sqrt (4 * Real.pi) := by
  constructor
  · change 1 / (Real.pi * (1 ^ 2 + 0 ^ 2)) = 1 / Real.pi
    ring_nf
  · change (1 / Real.sqrt (4 * Real.pi * 1)) * Real.exp (-0 ^ 2 / (4 * 1)) =
      1 / Real.sqrt (4 * Real.pi)
    norm_num

/-- Exact Fourier inversion evaluations at `x = 0`, `t = 1` for `α = 1` and `α = 2`. -/
example :
    fourierInvFracSemigroupSymbol 1 1 0 = (1 / Real.pi : ℂ) ∧
      fourierInvFracSemigroupSymbol 2 1 0 = ((1 / Real.sqrt (4 * Real.pi) : ℝ) : ℂ) := by
  rw [fourierInvFracSemigroupSymbol_one one_pos 0,
    fourierInvFracSemigroupSymbol_two one_pos 0]
  constructor
  · change (((1 / (Real.pi * (1 ^ 2 + 0 ^ 2)) : ℝ)) : ℂ) = (1 / Real.pi : ℂ)
    push_cast
    ring_nf
  · change (((((1 / Real.sqrt (4 * Real.pi * 1)) * Real.exp (-0 ^ 2 / (4 * 1)) : ℝ)) : ℂ)) =
      ((1 / Real.sqrt (4 * Real.pi) : ℝ) : ℂ)
    norm_num

/-- Positivity and sub-Markov domination of the reflected kernel hold concretely for both
`cauchyHeatKernel` (`α = 1`) and `gaussianHeatKernel` (`α = 2`). -/
example :
    (0 ≤ reflectedHeatKernel cauchyHeatKernel 1 2 1 ∧
      reflectedHeatKernel cauchyHeatKernel 1 2 1 ≤ cauchyHeatKernel.P (1 - 2) 1) ∧
    (0 ≤ reflectedHeatKernel gaussianHeatKernel 1 2 1 ∧
      reflectedHeatKernel gaussianHeatKernel 1 2 1 ≤ gaussianHeatKernel.P (1 - 2) 1) :=
  ⟨reflectedHeatKernel_bounds cauchyHeatKernel one_pos (by norm_num) one_pos,
    reflectedHeatKernel_bounds gaussianHeatKernel one_pos (by norm_num) one_pos⟩

/-! ### 7. Concrete `L²(0, ∞; ℂ)` reflected fractional Laplacian semigroup and resolvent -/

/-- Concrete unit-norm half-line test function `1_{(0, 1)} ∈ L²((0, ∞); ℂ)`. -/
noncomputable def unitBoxIoiL2 : L2IoiC :=
  MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
    (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) 1))
    (by
      have hle : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioi (0 : ℝ) := fun _ hx => hx.1
      rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo,
        Set.inter_eq_left.mpr hle, Real.volume_Ioo]
      norm_num)
    (1 : ℂ)

/-- Concrete `unitBoxIoiL2` has `L²(0, ∞; ℂ)` norm equal to `1`. -/
theorem norm_unitBoxIoiL2 : ‖unitBoxIoiL2‖ = 1 := by
  have hle : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioi (0 : ℝ) := fun _ hx => hx.1
  rw [unitBoxIoiL2, MeasureTheory.norm_indicatorConstLp (by norm_num) (by norm_num),
    MeasureTheory.measureReal_def,
    MeasureTheory.Measure.restrict_apply measurableSet_Ioo,
    Set.inter_eq_left.mpr hle, Real.volume_Ioo]
  simp

/-- Positive conjugation witnesses on `unitBoxIoiL2`: `IsOddL2`, `√2`-norm scaling, and
exact restriction round-trip `restIoiL2 (oddExtL2 unitBoxIoiL2) = unitBoxIoiL2`. -/
example :
    IsOddL2 (oddExtL2 unitBoxIoiL2) ∧
      ‖oddExtL2 unitBoxIoiL2‖ = Real.sqrt 2 ∧
      restIoiL2 (oddExtL2 unitBoxIoiL2) = unitBoxIoiL2 := by
  refine ⟨oddExtL2_isOddL2 unitBoxIoiL2, ?_, restIoiL2_oddExtL2 unitBoxIoiL2⟩
  rw [norm_oddExtL2, norm_unitBoxIoiL2, mul_one]

/-- Time-zero, semigroup composition, and contraction checks for `reflectedFracLapSemigroup`. -/
example (α : ℝ) (s t : ℝ≥0) :
    reflectedFracLapSemigroup α 0 unitBoxIoiL2 = unitBoxIoiL2 ∧
      reflectedFracLapSemigroup 1 s (reflectedFracLapSemigroup 1 t unitBoxIoiL2) =
        reflectedFracLapSemigroup 1 (s + t) unitBoxIoiL2 ∧
      ‖reflectedFracLapSemigroup α t unitBoxIoiL2‖ ≤ 1 := by
  refine ⟨(reflectedFracLapSemigroup α).zero_apply unitBoxIoiL2, ?_, ?_⟩
  · rw [← ContinuousLinearMap.comp_apply, ← (reflectedFracLapSemigroup 1).operator_add]
  · calc
      ‖reflectedFracLapSemigroup α t unitBoxIoiL2‖ ≤ ‖unitBoxIoiL2‖ :=
        (reflectedFracLapSemigroup α).norm_apply_le t unitBoxIoiL2
      _ = 1 := norm_unitBoxIoiL2

/-- Exact concrete Hille–Yosida generation and Laplace resolvent checks at `α = 1` and `α = 2`. -/
example (μ : PositiveShift) :
    (reflectedFracLapResolvent 1).generatedSemigroup = reflectedFracLapSemigroup 1 ∧
      (reflectedFracLapResolvent 2).generatedSemigroup = reflectedFracLapSemigroup 2 ∧
      (reflectedFracLapSemigroup 1).resolvent μ = (reflectedFracLapResolvent 1).operator μ := by
  refine ⟨reflectedFracLapResolvent_generatedSemigroup_eq 1,
    reflectedFracLapResolvent_generatedSemigroup_eq 2, ?_⟩
  rw [reflectedFracLapSemigroup, reflectedC0Semigroup_resolvent_eq]
  unfold fracLapSemigroup
  rw [fourierMultiplierSemigroup_resolvent_eq (fracLapSymbol 1) (measurable_fracLapSymbol 1)
    (fracLapSymbol_nonneg 1) μ]
  rfl

/-- **Non-vacuity check on `L²(0, ∞; ℂ)`**: `reflectedFracLapSemigroup 1 1` acts strictly
non-trivially on `unitBoxIoiL2` (since every nonzero frequency satisfies `exp(-|2πξ|) < 1`). -/
theorem reflectedFracLapSemigroup_one_nontrivial :
    reflectedFracLapSemigroup 1 1 unitBoxIoiL2 ≠ unitBoxIoiL2 := by
  intro heq
  have heq_ext :
      oddExtL2 (reflectedFracLapSemigroup 1 1 unitBoxIoiL2) = oddExtL2 unitBoxIoiL2 :=
    congrArg oddExtL2 heq
  have hodd : IsOddL2 (fracLapSemigroup 1 1 (oddExtL2 unitBoxIoiL2)) :=
    fracLapSemigroup_isOddL2 1 1 (oddExtL2_isOddL2 unitBoxIoiL2)
  change oddExtL2 (restIoiL2 (fracLapSemigroup 1 1 (oddExtL2 unitBoxIoiL2))) =
    oddExtL2 unitBoxIoiL2 at heq_ext
  rw [oddExtL2_restIoiL2_of_isOddL2 hodd] at heq_ext
  have hF :
      FourierTransform.fourier (fracLapSemigroup 1 1 (oddExtL2 unitBoxIoiL2)) =
        FourierTransform.fourier (oddExtL2 unitBoxIoiL2) :=
    congrArg (fun x : L2C => FourierTransform.fourier x) heq_ext
  change
      FourierTransform.fourier
        (FourierTransform.fourierInv
          (expMultiplierSymbol (fracLapSymbol 1) (measurable_fracLapSymbol 1)
            (fracLapSymbol_nonneg 1) 1 • FourierTransform.fourier (oddExtL2 unitBoxIoiL2))) =
      FourierTransform.fourier (oddExtL2 unitBoxIoiL2) at hF
  rw [FourierTransform.fourier_fourierInv_eq] at hF
  have hae :
      ((expMultiplierSymbol (fracLapSymbol 1) (measurable_fracLapSymbol 1)
          (fracLapSymbol_nonneg 1) 1 •
          FourierTransform.fourier (oddExtL2 unitBoxIoiL2) : L2C) : ℝ → ℂ) =ᵐ[
            MeasureTheory.volume]
        ((FourierTransform.fourier (oddExtL2 unitBoxIoiL2) : L2C) : ℝ → ℂ) :=
    MeasureTheory.Lp.ext_iff.mp hF
  have hne0 : ∀ᵐ ξ : ℝ ∂MeasureTheory.volume, ξ ≠ (0 : ℝ) := by
    rw [MeasureTheory.ae_iff]
    have hset : {ξ : ℝ | ¬ ξ ≠ 0} = ({0} : Set ℝ) := by
      ext ξ
      simp
    rw [hset, MeasureTheory.measure_singleton]
  have hF_zero :
      ((FourierTransform.fourier (oddExtL2 unitBoxIoiL2) : L2C) : ℝ → ℂ) =ᵐ[
          MeasureTheory.volume] (0 : ℝ → ℂ) := by
    filter_upwards [hae, hne0,
      MeasureTheory.Lp.coeFn_lpSMul (r := 2)
        (expMultiplierSymbol (fracLapSymbol 1) (measurable_fracLapSymbol 1)
          (fracLapSymbol_nonneg 1) 1)
        (FourierTransform.fourier (oddExtL2 unitBoxIoiL2)),
      coeFn_toLpTop
        (expSymbol_aestronglyMeasurable (fracLapSymbol 1) (measurable_fracLapSymbol 1)
          (1 : ℝ≥0))
        zero_le_one
        (norm_expSymbol_le_one (fracLapSymbol 1) (fracLapSymbol_nonneg 1)
          (1 : ℝ≥0).coe_nonneg)]
      with ξ h1 hξ hsmul hexp
    have hsmul' :
        ((expMultiplierSymbol (fracLapSymbol 1) (measurable_fracLapSymbol 1)
            (fracLapSymbol_nonneg 1) 1 •
            FourierTransform.fourier (oddExtL2 unitBoxIoiL2) : L2C) : ℝ → ℂ) ξ =
          (expMultiplierSymbol (fracLapSymbol 1) (measurable_fracLapSymbol 1)
            (fracLapSymbol_nonneg 1) 1 : ℝ → ℂ) ξ *
            ((FourierTransform.fourier (oddExtL2 unitBoxIoiL2) : L2C) : ℝ → ℂ) ξ := hsmul
    have hexp' :
        (expMultiplierSymbol (fracLapSymbol 1) (measurable_fracLapSymbol 1)
            (fracLapSymbol_nonneg 1) 1 : ℝ → ℂ) ξ =
          (Real.exp (-((1 : ℝ≥0) : ℝ) * fracLapSymbol 1 ξ) : ℂ) := hexp
    have hmul :
        ((Real.exp (-((1 : ℝ≥0) : ℝ) * fracLapSymbol 1 ξ) : ℝ) : ℂ) *
            ((FourierTransform.fourier (oddExtL2 unitBoxIoiL2) : L2C) : ℝ → ℂ) ξ =
          ((FourierTransform.fourier (oddExtL2 unitBoxIoiL2) : L2C) : ℝ → ℂ) ξ := by
      rw [← hexp', ← hsmul', h1]
    have hcoeff_ne :
        ((Real.exp (-((1 : ℝ≥0) : ℝ) * fracLapSymbol 1 ξ) : ℝ) : ℂ) - 1 ≠ 0 := by
      intro hc
      have hreal : Real.exp (-((1 : ℝ≥0) : ℝ) * fracLapSymbol 1 ξ) = 1 := by
        have hC := congrArg Complex.re (sub_eq_zero.mp hc)
        simpa only [Complex.ofReal_re, Complex.one_re] using hC
      have hsym : 0 < fracLapSymbol 1 ξ := by
        unfold fracLapSymbol
        rw [rpow_one]
        have h2pi : 0 < |2 * Real.pi * ξ| := abs_pos.mpr (by positivity)
        exact h2pi
      have hlt : Real.exp (-((1 : ℝ≥0) : ℝ) * fracLapSymbol 1 ξ) < 1 := by
        rw [NNReal.coe_one, neg_one_mul]
        exact Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    have hfac :
        (((Real.exp (-((1 : ℝ≥0) : ℝ) * fracLapSymbol 1 ξ) : ℝ) : ℂ) - 1) *
          ((FourierTransform.fourier (oddExtL2 unitBoxIoiL2) : L2C) : ℝ → ℂ) ξ = 0 := by
      rw [sub_one_mul, hmul, sub_self]
    exact (mul_eq_zero.mp hfac).resolve_left hcoeff_ne
  have hF_lp : FourierTransform.fourier (oddExtL2 unitBoxIoiL2) = 0 := by
    rw [MeasureTheory.Lp.ext_iff]
    filter_upwards [hF_zero, MeasureTheory.Lp.coeFn_zero ℂ 2 MeasureTheory.volume] with ξ h1 h2
    exact h1.trans h2.symm
  have hnorm_zero : ‖oddExtL2 unitBoxIoiL2‖ = 0 := by
    rw [← MeasureTheory.Lp.norm_fourier_eq, hF_lp, norm_zero]
  rw [norm_oddExtL2, norm_unitBoxIoiL2, mul_one] at hnorm_zero
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith


/-! ### 8. Concrete Gagliardo Dirichlet form `B^α` and restricted form `B^α_0` -/

/-- Sanity check: at `α = 1` the Gagliardo weight is strictly positive at the off-diagonal
point `(1, 0)`. This does not by itself show that the measure or form is nonzero. -/
example : 0 < gagliardoWeight 1 (1, 0) :=
  gagliardoWeight_pos fractionalExponent_one (by norm_num)

/-- Boundary check: the Gagliardo weight vanishes on the diagonal `x = y`. -/
example (x : ℝ) : gagliardoWeight 1 (x, x) = 0 := by
  change ENNReal.ofReal (fracLapConstant 1 / (2 * |x - x| ^ (1 + (1 : ℝ)))) = 0
  rw [sub_self, abs_zero, Real.zero_rpow (by norm_num), mul_zero, div_zero,
    ENNReal.ofReal_zero]

/-- Negative counterexample justifying the `FractionalExponent α` hypothesis: at `α = 0`
the normalizing constant vanishes, so the Gagliardo weight is identically zero. -/
example (p : ℝ × ℝ) : gagliardoWeight 0 p = 0 := by
  change ENNReal.ofReal (fracLapConstant 0 / (2 * |p.1 - p.2| ^ (1 + (0 : ℝ)))) = 0
  unfold fracLapConstant
  rw [mul_zero, zero_mul, zero_div, zero_div, ENNReal.ofReal_zero]

/-- Closed-form evaluation: the Dirichlet energy is the squared `L²(gagliardoMeasure α)` norm
of the difference-quotient component. -/
theorem gagliardoForm_self_eq_norm_sq (α : ℝ) (u : GagliardoSpace α) :
    (gagliardoForm α).form u u = ‖gagliardoDiffPart α u‖ ^ 2 :=
  real_inner_self_eq_norm_sq _

/-- Quadratic scaling `B^α(c u, c u) = c² B^α(u, u)`: the form is genuinely quadratic. -/
example (α c : ℝ) (u : GagliardoSpace α) :
    (gagliardoForm α).form (c • u) (c • u) = c ^ 2 * (gagliardoForm α).form u u := by
  rw [gagliardoForm_self_eq_norm_sq, gagliardoForm_self_eq_norm_sq, map_smul, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs]

/-- Concrete evaluation at the origin: `B^α(0, 0) = 0`. -/
example (α : ℝ) : (gagliardoForm α).form 0 0 = 0 := by
  rw [gagliardoForm_self_eq_norm_sq, map_zero, norm_zero]
  norm_num

/-- Concrete Markov witness: the exterior-Dirichlet form `B^1_0` on `H^(1/2)_0(0, ∞)` satisfies
both Beurling–Deny conditions with the concrete modulus and unit truncation. -/
example : IsMarkovDirichletForm (restrictedGagliardoForm 1) (restrictedGagliardoAbs 1)
    (restrictedGagliardoCapOne 1) :=
  restrictedGagliardoForm_isMarkovDirichletForm fractionalExponent_one

/-- The concrete modulus `gagliardoAbs` acts pointwise a.e. on the `L²` component. -/
example (α : ℝ) (u : GagliardoSpace α) :
    (gagliardoL2Part α (gagliardoAbs α u) : ℝ → ℝ) =ᵐ[MeasureTheory.volume]
      fun x => |(gagliardoL2Part α u : ℝ → ℝ) x| :=
  coeFn_gagliardoCompLip_l2Part α lipschitzWith_abs_real abs_zero u

/-! ### 9. Non-vacuity witness: the tent function in `H^(α / 2)_0(0, ∞)` -/

/-- Closed-form evaluations of the tent function: apex `1` at `x = 1`, linear slopes, and
vanishing at the endpoints and outside `[0, 2]`. -/
example : gagliardoTent 1 = 1 ∧ gagliardoTent (1 / 2) = 1 / 2 ∧ gagliardoTent (3 / 2) = 1 / 2 ∧
    gagliardoTent 0 = 0 ∧ gagliardoTent 2 = 0 ∧ gagliardoTent (-5) = 0 ∧ gagliardoTent 7 = 0 := by
  unfold gagliardoTent
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Negative counterexample: the tent function is not the zero function, so the witness
is not a degenerate element. -/
example : gagliardoTent ≠ fun _ => 0 := by
  intro h
  have h1 : gagliardoTent 1 = 0 := congrFun h 1
  have h2 : gagliardoTent 1 = 1 := by norm_num [gagliardoTent]
  rw [h2] at h1
  exact one_ne_zero h1

/-- Translation estimate (boundary case `h = 0`): the `L²` increment of a function by a zero
translation vanishes, consistent with the bound `4 min(0², 1) = 0`. -/
example : ∫⁻ y, ENNReal.ofReal ((gagliardoTent (y + 0) - gagliardoTent y) ^ 2) = 0 := by
  simp

/-- Positive witness at `α = 1`: the exterior-Dirichlet space `H^(1/2)_0(0, ∞)` contains a
nonzero element with strictly positive energy, so `restrictedGagliardoForm 1` is not
identically zero and the Markov property above is not vacuous. -/
example : ∃ u : RestrictedGagliardoSpace 1, u ≠ 0 ∧ 0 < (restrictedGagliardoForm 1).form u u :=
  exists_restrictedGagliardoForm_pos fractionalExponent_one

/-- The same witness works for every exponent in `(0, 2)`, e.g. `α = 1 / 2` and `α = 3 / 2`. -/
example : (∃ u : RestrictedGagliardoSpace (1 / 2), 0 < (restrictedGagliardoForm (1 / 2)).form u u) ∧
    (∃ u : RestrictedGagliardoSpace (3 / 2), 0 < (restrictedGagliardoForm (3 / 2)).form u u) :=
  ⟨(exists_restrictedGagliardoForm_pos ⟨by norm_num, by norm_num⟩).imp fun _ h => h.2,
    (exists_restrictedGagliardoForm_pos ⟨by norm_num, by norm_num⟩).imp fun _ h => h.2⟩

/-- Boundary check for the energy identity: a constant function has zero Gagliardo energy,
matching zero translation modulus on the right-hand side. -/
example (α c : ℝ) :
    ∫⁻ p : ℝ × ℝ, gagliardoWeight α p * ENNReal.ofReal (((fun _ : ℝ => c) p.1 - c) ^ 2)
      ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume) = 0 := by
  simp

/-- Closed-form instance of the energy identity: it rewrites the tent's Gagliardo energy as a
translation-modulus integral. -/
example (α : ℝ) :
    ∫⁻ p : ℝ × ℝ, gagliardoWeight α p * ENNReal.ofReal
        ((gagliardoTent p.1 - gagliardoTent p.2) ^ 2)
      ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume) =
    ∫⁻ h : ℝ, gagliardoWeight α (h, 0) *
      ∫⁻ y, ENNReal.ofReal ((gagliardoTent (y + h) - gagliardoTent y) ^ 2) :=
  lintegral_gagliardo_energy_eq α continuous_gagliardoTent.measurable

/-- Reflected half-line semigroup (`thm:halffracsemi`): generator characterization via
`oddExtL2`, reflected heat kernel realization `P_α(x - y, t) - P_α(x + y, t)`, and
sub-Markov positivity preservation on `(0, ∞)`. -/
example {α : ℝ} (hα : FractionalExponent α) {t : NNReal} (ht : 0 < (t : ℝ)) (u : L2IoiC)
    (hu_real : ∀ᵐ y : ℝ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
      (Set.Ioi (0 : ℝ)), (u y).im = 0)
    (hu_nn : ∀ᵐ y : ℝ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
      (Set.Ioi (0 : ℝ)), 0 ≤ (u y).re) :
    (u ∈ (reflectedFracLapSemigroup α).generatorDomain ↔
      oddExtL2 u ∈ (fracLapSemigroup α).generatorDomain) ∧
      (∀ᵐ x : ℝ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi (0 : ℝ)),
        ((reflectedFracLapSemigroup α t u : L2IoiC) : ℝ → ℂ) x =
          ∫ y in Set.Ioi (0 : ℝ),
            ((reflectedHeatKernel (stableHeatKernel α hα) x y t : ℝ) : ℂ) *
              (u : ℝ → ℂ) y) ∧
      (∀ᵐ x : ℝ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi (0 : ℝ)),
        0 ≤ ((reflectedFracLapSemigroup α t u : ℝ → ℂ) x).re) :=
  ⟨reflectedFracLapSemigroup_mem_generatorDomain_iff α u,
    reflectedFracLapSemigroup_apply_ae_eq_reflectedHeatKernel hα ht u,
    (reflectedFracLapSemigroup_re_nonneg hα t hu_real hu_nn).2⟩

end

end FracLapTest
