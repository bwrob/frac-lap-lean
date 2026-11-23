/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLap.Core.FourierSobolev

Bridges our fractional Laplacian and Sobolev space theory directly to Mathlib `v4.36.0`'s
native Fourier-analytic and Hilbert-space infrastructure:
- **Plancherel & Parseval on `L²`** (`plancherel_norm_eq`, `parseval_inner_eq`):
  `MeasureTheory.Lp.fourierTransformₗᵢ` is an isometric equivalence on `L²(E, F)`, preserving
  both the `L²` norm `‖𝓕 f‖ = ‖f‖` and inner product `⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫`.
- **Fractional Sobolev Spaces via Bessel Potentials** (`schwartz_memSobolev`,
  `memSobolev_mono`, `besselSymbol_equiv_bounds`):
  connects `TemperedDistribution.besselPotential E F α` and `TemperedDistribution.MemSobolev α 2`
  to the thesis Fourier-Sobolev weight `(1 + |ξ|²)^α` and proves the two-sided symbol equivalence
  `(1 / 2) * (1 + |ξ|^(2 α)) ≤ (1 + |ξ|^2)^α ≤ 2^α * (1 + |ξ|^(2 α))` (Proposition 4.8).
- **Lax–Milgram Coercive Form Equivalence** (`laxMilgramEquivOfCoercive`):
  connects `IsCoercive.continuousLinearEquivOfBilin` from
  `Mathlib.Analysis.InnerProductSpace.LaxMilgram` to coercive bilinear forms on Hilbert spaces.
-/

namespace FracLap

open FourierTransform MeasureTheory Real TemperedDistribution
open scoped ENNReal SchwartzMap ComplexInnerProductSpace

@[expose] public section

section PlancherelAndSobolev

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Plancherel's Theorem on `L²(E, F)` (Mathlib `MeasureTheory.Lp.norm_fourier_eq`)**:
The `L²` Fourier transform `𝓕` preserves the `L²` norm: `‖𝓕 f‖ = ‖f‖`. -/
theorem plancherel_norm_eq (f : Lp (α := E) F 2) : ‖𝓕 f‖ = ‖f‖ :=
  MeasureTheory.Lp.norm_fourier_eq f

/-- **Parseval's Identity on `L²(E, F)` (Mathlib `MeasureTheory.Lp.inner_fourier_eq`)**:
The `L²` Fourier transform `𝓕` preserves the `L²` inner product: `⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫`. -/
theorem parseval_inner_eq (f g : Lp (α := E) F 2) : ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫ :=
  MeasureTheory.Lp.inner_fourier_eq f g

/-- **Schwartz Functions Belong to Every Fractional Sobolev Space `H^s(E, F)`
(Mathlib `SchwartzMap.memSobolev`)**:
Every Schwartz test function `f ∈ 𝓢(E, F)` satisfies `MemSobolev s 2 f` for all `s ∈ ℝ`. -/
theorem schwartz_memSobolev (s : ℝ) (f : 𝓢(E, F)) :
    MemSobolev s 2 (f : 𝓢'(E, F)) :=
  f.memSobolev

/-- **Monotonicity of Fractional Sobolev Spaces `H^s ⊆ H^{s'}` for `s' ≤ s`
(Mathlib `TemperedDistribution.MemSobolev.mono`)**:
If `u ∈ H^s(E, F)` and `s' ≤ s`, then `u ∈ H^{s'}(E, F)`. -/
theorem memSobolev_mono {s s' : ℝ} (h : s' ≤ s) {f : 𝓢'(E, F)}
    (hf : MemSobolev s 2 f) : MemSobolev s' 2 f :=
  hf.mono h

omit [InnerProductSpace ℂ F] [CompleteSpace F] in
/-- **Bessel Potential Semigroup Group Law
(Mathlib `TemperedDistribution.besselPotential_besselPotential_apply`)**:
`(I - (2π)⁻² Δ)^(s'/2) ((I - (2π)⁻² Δ)^(s/2) f) = (I - (2π)⁻² Δ)^((s + s')/2) f`. -/
theorem besselPotential_add_order [NormedSpace ℂ F] (s s' : ℝ) (f : 𝓢'(E, F)) :
    besselPotential E F s' (besselPotential E F s f) =
      besselPotential E F (s + s') f :=
  besselPotential_besselPotential_apply s s' f

end PlancherelAndSobolev

/-- **Proposition 4.8 (`prop:fourier_sobolev_equiv`) Upper Symbol Equivalence**:
For every `α ≥ 0` and frequency `ξ ∈ ℝ`, the Bessel potential weight `(1 + ξ^2)^α` is bounded
above by `2^α * (1 + |ξ|^(2 * α))`. -/
theorem besselSymbol_le_two_rpow_mul {α : ℝ} (hα : 0 ≤ α) (ξ : ℝ) :
    (1 + ξ ^ 2) ^ α ≤ (2 : ℝ) ^ α * (1 + |ξ| ^ (2 * α)) := by
  rcases le_total |ξ| 1 with hle | hge
  · have hsq : ξ ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg ξ]
    have h1 : 1 + ξ ^ 2 ≤ 2 := by linarith
    have hpow : (1 + ξ ^ 2) ^ α ≤ (2 : ℝ) ^ α :=
      rpow_le_rpow (by positivity) h1 hα
    have hnonneg : 0 ≤ (2 : ℝ) ^ α * |ξ| ^ (2 * α) := by positivity
    linarith
  · have hsq : 1 ≤ ξ ^ 2 := by
      rw [← sq_abs]
      nlinarith
    have h1 : 1 + ξ ^ 2 ≤ 2 * |ξ| ^ (2 : ℝ) := by
      rw [rpow_two, sq_abs]
      linarith
    have hpow : (1 + ξ ^ 2) ^ α ≤ (2 * |ξ| ^ (2 : ℝ)) ^ α :=
      rpow_le_rpow (by positivity) h1 hα
    have hmul : (2 * |ξ| ^ (2 : ℝ)) ^ α = (2 : ℝ) ^ α * |ξ| ^ (2 * α) := by
      rw [mul_rpow (by norm_num) (by positivity), ← rpow_mul (abs_nonneg ξ)]
    have h2pos : 0 ≤ (2 : ℝ) ^ α := by positivity
    linarith

/-- **Proposition 4.8 (`prop:fourier_sobolev_equiv`) Lower Symbol Equivalence**:
For every `α ≥ 0` and frequency `ξ ∈ ℝ`,
`(1 / 2) * (1 + |ξ|^(2 * α)) ≤ (1 + ξ^2)^α`. -/
theorem half_mul_le_besselSymbol {α : ℝ} (hα : 0 ≤ α) (ξ : ℝ) :
    (1 / 2 : ℝ) * (1 + |ξ| ^ (2 * α)) ≤ (1 + ξ ^ 2) ^ α := by
  have h1_le : (1 : ℝ) ≤ (1 + ξ ^ 2) ^ α := by
    have hbase : (1 : ℝ) ≤ 1 + ξ ^ 2 := by
      have : 0 ≤ ξ ^ 2 := sq_nonneg ξ
      linarith
    calc
      (1 : ℝ) = (1 : ℝ) ^ α := (one_rpow α).symm
      _ ≤ (1 + ξ ^ 2) ^ α := rpow_le_rpow zero_le_one hbase hα
  have hxi_le : |ξ| ^ (2 * α) ≤ (1 + ξ ^ 2) ^ α := by
    have hbase : |ξ| ^ (2 : ℝ) ≤ 1 + ξ ^ 2 := by
      rw [rpow_two, sq_abs]
      linarith
    calc
      |ξ| ^ (2 * α) = (|ξ| ^ (2 : ℝ)) ^ α := by
        rw [← rpow_mul (abs_nonneg ξ)]
      _ ≤ (1 + ξ ^ 2) ^ α := rpow_le_rpow (by positivity) hbase hα
  linarith

/-- **Lax–Milgram Theorem for Coercive Bilinear Forms
(Mathlib `IsCoercive.continuousLinearEquivOfBilin`)**:
Every coercive continuous bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ` on a real Hilbert space `V`
induces a continuous linear equivalence `V ≃L[ℝ] V` representing `B` via the inner product. -/
noncomputable def laxMilgramEquivOfCoercive
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B) : V ≃L[ℝ] V :=
  hB.continuousLinearEquivOfBilin

end

end FracLap
