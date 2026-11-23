/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# FracLap.Tools.Symmetrization

The symmetrization argument for nonlocal energies (Karch--Chasseigne--Ignat, Remark on the
"symmetrization argument", used throughout the proof of the Kato-type inequality), for a jump
measure `ν` on `X × X` invariant under the swap `(x, y) ↦ (y, x)`.

- `integral_swap_eq`: `∫ h(y, x) dν = ∫ h(x, y) dν`.
- `integral_sub_mul_eq_half`: `∬ (u x - u y) g x dν = (1/2) ∬ (u x - u y)(g x - g y) dν`.
- `integral_sub_mul_comp_nonneg`: dissipation of any monotone function of `u`:
  `∬ (u x - u y) φ(u x) dν ≥ 0` for monotone `φ` (Beurling--Deny / Kato-type inequality at the level
  of the jump measure).
-/

namespace FracLap

open MeasureTheory

@[expose] public section

variable {X : Type*} [MeasurableSpace X]

/-- For a swap-invariant measure, integrals are unchanged by exchanging the two variables. -/
theorem integral_swap_eq {ν : Measure (X × X)} (hν : MeasurePreserving Prod.swap ν ν)
    (h : X × X → ℝ) : ∫ z, h z.swap ∂ν = ∫ z, h z ∂ν :=
  (show MeasurePreserving (MeasurableEquiv.prodComm (α := X) (β := X)) ν ν from hν).integral_comp'
    h

/-- **Symmetrization identity**: for a swap-invariant jump measure `ν` and suitably integrable
`u, g`, `∬ (u x - u y) g x dν = (1/2) ∬ (u x - u y)(g x - g y) dν`. -/
theorem integral_sub_mul_eq_half {ν : Measure (X × X)} (hν : MeasurePreserving Prod.swap ν ν)
    (u g : X → ℝ) (h1 : Integrable (fun z : X × X => (u z.1 - u z.2) * g z.1) ν)
    (h2 : Integrable (fun z : X × X => (u z.1 - u z.2) * g z.2) ν) :
    ∫ z, (u z.1 - u z.2) * g z.1 ∂ν = (1 / 2) * ∫ z, (u z.1 - u z.2) * (g z.1 - g z.2) ∂ν := by
  have hswap := integral_swap_eq hν (fun z : X × X => (u z.1 - u z.2) * g z.1)
  have hneg : ∫ z, (u z.2 - u z.1) * g z.2 ∂ν = -∫ z, (u z.1 - u z.2) * g z.2 ∂ν := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  have hsplit : ∫ z, (u z.1 - u z.2) * (g z.1 - g z.2) ∂ν =
      ∫ z, (u z.1 - u z.2) * g z.1 ∂ν - ∫ z, (u z.1 - u z.2) * g z.2 ∂ν := by
    rw [← integral_sub h1 h2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  simp only [Prod.fst_swap, Prod.snd_swap] at hswap
  rw [hsplit]
  rw [hneg] at hswap
  linarith

/-- **Dissipation of monotone functionals** (Kato/Beurling--Deny type): for a swap-invariant jump
measure and monotone `φ`, `∬ (u x - u y) φ(u x) dν ≥ 0`. For `φ = sgn` this is the `L¹`
contraction property, for `φ = (· )_+` positivity preservation, for `φ = u ↦ |u|^(q-2) u` the
`L^q` dissipativity. -/
theorem integral_sub_mul_comp_nonneg {ν : Measure (X × X)}
    (hν : MeasurePreserving Prod.swap ν ν) (u : X → ℝ) {φ : ℝ → ℝ} (hφ : Monotone φ)
    (h1 : Integrable (fun z : X × X => (u z.1 - u z.2) * φ (u z.1)) ν)
    (h2 : Integrable (fun z : X × X => (u z.1 - u z.2) * φ (u z.2)) ν) :
    0 ≤ ∫ z, (u z.1 - u z.2) * φ (u z.1) ∂ν := by
  have key := integral_sub_mul_eq_half hν u (φ ∘ u) h1 h2
  simp only [Function.comp] at key
  rw [key]
  refine mul_nonneg (by norm_num) (integral_nonneg fun z => ?_)
  rcases le_total (u z.2) (u z.1) with h | h
  · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (hφ h))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h) (sub_nonpos.mpr (hφ h))

end

end FracLap
