/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Core.C0Semigroup
public import FracLap.Core.Pointwise
public import FracLap.Core.Semigroups
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLap.WholeLine.AnomalousDiffusion

Whole-line fractional heat kernel `P_α(x, t)`, convolution semigroup `S(t)`,
Fourier multiplier resolvent/semigroup symbols, and whole-line fractional Dirichlet form `B^α`:
- `FractionalHeatKernel α`: bundled fractional heat kernel `P_α(x, t)` encoding spatial
  evenness, self-similar scaling `t^(-1 / α) P_α(x t^(-1 / α), 1)`, positivity, radial
  monotonicity, algebraic decay `P_α(x, 1) ≤ C / (1 + |x|)^(1 + α)`, and unit total mass
  `∫ x, P_α(x, t) = 1`.
- `FractionalHeatKernel.integral_sub_eq_one`: translation-invariant unit mass
  `∫ y, P_α(x - y, t) = 1`.
- `fourierResolventSymbol_bounds` and `fourierSemigroupSymbol_add`:
  frequency-space Hille–Yosida resolvent bound `0 < 1 / (λ + |ξ|^α) ≤ 1 / λ` and
  exponential symbol law `e^(-(s + t)|ξ|^α) = e^(-s|ξ|^α) e^(-t|ξ|^α)`.
- `wholeLineSemigroup_eq_conv` and `wholeLineSemigroup_apply_eq_conv`: generator uniqueness
  `S = T` (and `S t u = T t u`) for strongly continuous contraction semigroups with equal
  generator domain and generator.
- `fracHeatConv_nonneg` and `fracHeatConv_le_const`: Markov positivity preservation and
  `L^∞` contractivity `0 ≤ u₀ ≤ M ⟹ 0 ≤ P_α(·, t) * u₀ ≤ M`.
- `fourierFracLap_symm_nonneg` and `symmetricAccretiveFormOfSqrt`:
  nonnegative self-adjoint Fourier symbol and induced symmetric accretive Dirichlet form `B^α`.
-/

namespace FracLap

open MeasureTheory Real
open scoped NNReal

@[expose] public section

/-- Bundled fractional heat kernel `P_α(x, t)` on `ℝ × (0, ∞)` for `α ∈ (0, 2]`. -/
structure FractionalHeatKernel (α : ℝ) where
  /-- Kernel evaluation `P_α(x, t)`. -/
  P : ℝ → ℝ → ℝ
  /-- Algebraic decay constant `C(α) > 0` at `t = 1`. -/
  decayConst : ℝ
  /-- Strict positivity of `decayConst`. -/
  decayConst_pos : 0 < decayConst
  /-- Spatial evenness `P_α(-x, t) = P_α(x, t)` for all `x ∈ ℝ` and `t > 0`. -/
  even_space : ∀ x t : ℝ, 0 < t → P (-x) t = P x t
  /-- Self-similar scaling `P_α(x, t) = t^(-1 / α) P_α(x t^(-1 / α), 1)`. -/
  self_similar : ∀ x t : ℝ, 0 < t → P x t = t ^ (-1 / α) * P (x * t ^ (-1 / α)) 1
  /-- Pointwise nonnegativity `0 ≤ P_α(x, t)` for `t > 0`. -/
  nonneg : ∀ x t : ℝ, 0 < t → 0 ≤ P x t
  /-- Radial monotonicity on `[0, ∞)` (from Bochner Gaussian subordination):
  `P_α(b, t) ≤ P_α(a, t)` whenever `|a| ≤ |b|` and `t > 0`. -/
  radial_antitone : ∀ a b t : ℝ, 0 < t → |a| ≤ |b| → P b t ≤ P a t
  /-- Heavy-tailed algebraic decay bound at unit time:
  `P_α(x, 1) ≤ C / (1 + |x|)^(1 + α)`. -/
  decay_unit_time : ∀ x : ℝ, P x 1 ≤ decayConst / (1 + |x|) ^ (1 + α)
  /-- Integrability of `x ↦ P_α(x, t)` for `t > 0`. -/
  integrable_space : ∀ t : ℝ, 0 < t → Integrable (fun x : ℝ => P x t)
  /-- Unit total mass `∫ x, P_α(x, t) = 1` for all `t > 0`. -/
  integral_eq_one : ∀ t : ℝ, 0 < t → (∫ x : ℝ, P x t) = 1

/-- **Translation-Invariant Unit Mass**:
For every `x ∈ ℝ` and `t > 0`, `∫ y, P_α(x - y, t) = 1`. -/
theorem FractionalHeatKernel.integral_sub_eq_one {α : ℝ} (K : FractionalHeatKernel α)
    (x : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ y : ℝ, K.P (x - y) t) = 1 := by
  rw [integral_sub_left_eq_self (fun y : ℝ => K.P y t) volume x]
  exact K.integral_eq_one t ht

/-- Whole-line fractional heat convolution operator
`(T(t) u₀)(x) = ∫ y, P_α(x - y, t) u₀(y)`. -/
noncomputable def fracHeatConv {α : ℝ} (K : FractionalHeatKernel α) (t : ℝ)
    (u₀ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, K.P (x - y) t * u₀ y

/-- **Fourier Resolvent Bound**:
For every spectral frequency `ξ ∈ ℝ`, order `α > 0`, and spectral parameter `λ > 0`,
the Fourier multiplier resolvent symbol `(λ + |ξ|^α)⁻¹` satisfies
`0 < 1 / (λ + |ξ|^α) ≤ 1 / λ`. -/
theorem fourierResolventSymbol_bounds {α lam : ℝ} (hlam : 0 < lam) (ξ : ℝ) :
    0 < 1 / (lam + |ξ| ^ α) ∧ 1 / (lam + |ξ| ^ α) ≤ 1 / lam := by
  have hpow : 0 ≤ |ξ| ^ α := by positivity
  have hsum : lam ≤ lam + |ξ| ^ α := by linarith
  have hsum_pos : 0 < lam + |ξ| ^ α := by linarith
  refine ⟨by positivity, ?_⟩
  exact one_div_le_one_div_of_le hlam hsum

/-- **Frequency-Space Semigroup Law**:
The Fourier multiplier symbol `m_α(t, ξ) = exp(-t |ξ|^α)` satisfies
`m_α(s + t, ξ) = m_α(s, ξ) * m_α(t, ξ)`. -/
theorem fourierSemigroupSymbol_add (α s t ξ : ℝ) :
    exp (-(s + t) * |ξ| ^ α) = exp (-s * |ξ| ^ α) * exp (-t * |ξ| ^ α) := by
  rw [← exp_add]
  ring_nf

/-- **Identification of Abstract and Convolution Semigroups (Generator Uniqueness)**:
two strongly continuous contraction semigroups `S, T` on a real Banach space `E` with the same
generator domain and the same generator on it are equal, `S = T`. This is the whole-line form of
`StronglyContinuousContractionSemigroup.ext_of_generator`, used to identify an abstractly
generated semigroup with the convolution semigroup once their generators agree. -/
theorem wholeLineSemigroup_eq_conv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (S T : StronglyContinuousContractionSemigroup E)
    (hdom : S.generatorDomain = T.generatorDomain)
    (hgen : ∀ (f : E) (hS : f ∈ S.generatorDomain) (hT : f ∈ T.generatorDomain),
      S.generator ⟨f, hS⟩ = T.generator ⟨f, hT⟩) :
    S = T :=
  S.ext_of_generator T hdom hgen

/-- **Pointwise form of generator uniqueness**: under the hypotheses of
`wholeLineSemigroup_eq_conv`, `S t u = T t u` for every `t ≥ 0` and `u ∈ E`. -/
theorem wholeLineSemigroup_apply_eq_conv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (S T : StronglyContinuousContractionSemigroup E)
    (hdom : S.generatorDomain = T.generatorDomain)
    (hgen : ∀ (f : E) (hS : f ∈ S.generatorDomain) (hT : f ∈ T.generatorDomain),
      S.generator ⟨f, hS⟩ = T.generator ⟨f, hT⟩)
    (t : ℝ≥0) (u : E) : S t u = T t u := by
  rw [wholeLineSemigroup_eq_conv S T hdom hgen]

/-- **Whole-Line Markov Semigroup Positivity Preservation**:
If `u₀(y) ≥ 0` for all `y ∈ ℝ`, then `(T(t) u₀)(x) ≥ 0` for all `x ∈ ℝ` and `t > 0`. -/
theorem fracHeatConv_nonneg {α : ℝ} (K : FractionalHeatKernel α) {t : ℝ} (ht : 0 < t)
    {u₀ : ℝ → ℝ} (hu₀ : ∀ y : ℝ, 0 ≤ u₀ y) (x : ℝ) :
    0 ≤ fracHeatConv K t u₀ x := by
  unfold fracHeatConv
  refine integral_nonneg fun y => ?_
  exact mul_nonneg (K.nonneg (x - y) t ht) (hu₀ y)

/-- **Whole-Line Markov Semigroup Sub-Markov Upper Bound**:
If `u₀(y) ≤ M` for all `y ∈ ℝ` and `y ↦ P_α(x - y, t) u₀(y)` is integrable, then
`(T(t) u₀)(x) ≤ M` for all `x ∈ ℝ` and `t > 0`. -/
theorem fracHeatConv_le_const {α : ℝ} (K : FractionalHeatKernel α) {t : ℝ} (ht : 0 < t)
    {u₀ : ℝ → ℝ} {M : ℝ} (hu₀ : ∀ y : ℝ, u₀ y ≤ M) (x : ℝ)
    (hint : Integrable (fun y : ℝ => K.P (x - y) t * u₀ y)) :
    fracHeatConv K t u₀ x ≤ M := by
  unfold fracHeatConv
  have hP_int : Integrable (fun y : ℝ => K.P (x - y) t) :=
    (K.integrable_space t ht).comp_sub_left x
  have hPM_int : Integrable (fun y : ℝ => K.P (x - y) t * M) :=
    hP_int.mul_const M
  have h_le : ∀ y : ℝ, K.P (x - y) t * u₀ y ≤ K.P (x - y) t * M := fun y =>
    mul_le_mul_of_nonneg_left (hu₀ y) (K.nonneg (x - y) t ht)
  have h_mono :
      (∫ y : ℝ, K.P (x - y) t * u₀ y) ≤ ∫ y : ℝ, K.P (x - y) t * M :=
    integral_mono hint hPM_int h_le
  have h_const : (∫ y : ℝ, K.P (x - y) t * M) = M := by
    rw [integral_mul_const, K.integral_sub_eq_one x ht, one_mul]
  linarith

/-- **Symmetry and Nonnegativity of the Fractional Laplacian Fourier Symbol**:
In frequency space, the multiplier `|ξ|^α` is symmetric and nonnegative:
`(|ξ|^α * uHat ξ) * vHat ξ = uHat ξ * (|ξ|^α * vHat ξ)` and `0 ≤ |ξ|^α * (uHat ξ)^2`. -/
theorem fourierFracLap_symm_nonneg (α : ℝ) (uHat vHat : ℝ → ℝ) (ξ : ℝ) :
    (|ξ| ^ α * uHat ξ) * vHat ξ = uHat ξ * (|ξ| ^ α * vHat ξ) ∧
      0 ≤ |ξ| ^ α * (uHat ξ) ^ 2 := by
  refine ⟨by ring, ?_⟩
  have h1 : 0 ≤ |ξ| ^ α := by positivity
  have h2 : 0 ≤ (uHat ξ) ^ 2 := sq_nonneg (uHat ξ)
  positivity

/-- **Quadratic Form Induced by the Fractional Square-Root Operator**:
Any inner-product bilinear form `B(u, v) = ⟪T u, T v⟫` induced by a map `T : V → H`
(modeling `(-Δ)^(α / 4) : H^(α / 2)(ℝ) → L²(ℝ)`) into a space equipped with a symmetric,
nonnegative, Cauchy–Schwarz inner product `innerH` defines a `SymmetricAccretiveForm V`. -/
def symmetricAccretiveFormOfSqrt {V H : Type*} (T : V → H) (innerH : H → H → ℝ)
    (hsymm : ∀ x y : H, innerH x y = innerH y x)
    (hnonneg : ∀ x : H, 0 ≤ innerH x x)
    (hcs : ∀ x y : H, (innerH x y) ^ 2 ≤ innerH x x * innerH y y) :
    SymmetricAccretiveForm V where
  form u v := innerH (T u) (T v)
  symm u v := hsymm (T u) (T v)
  accretive u := hnonneg (T u)
  cauchy_schwarz_sq u v := hcs (T u) (T v)

end

end FracLap
