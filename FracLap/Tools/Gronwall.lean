/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# FracLap.Tools.Gronwall

A Gronwall-type lemma with a weakly singular kernel (Brandolese, Karch).

- `integral_sub_rpow_neg`: `∫₀ᵗ (t - τ)^(-a) dτ = t^(1-a) / (1-a)` for `0 < a < 1`.
- `gronwall_singular`: if `h ≥ 0` is locally bounded on `[0, ∞)` and
  `h(t) ≤ C₁ (1+t) + C₂ ∫₀ᵗ (t-τ)^(-a) (1+τ)^(-b) h(τ) dτ` with `0 < a < 1`, `b > 0`, `a + b > 1`,
  then `h(t) ≤ C (1+t)` for some constant `C`.
-/

namespace FracLap

open Set MeasureTheory intervalIntegral

@[expose] public section

/-- The kernel `τ ↦ (t - τ)^(-a)` is interval integrable on `[0, t]` for `a < 1`. -/
theorem intervalIntegrable_sub_rpow_neg {a : ℝ} (ha : a < 1) (t : ℝ) :
    IntervalIntegrable (fun τ : ℝ => (t - τ) ^ (-a)) volume 0 t := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) (r := -a)
    (by linarith)).comp_sub_left t
  simpa using h.symm

/-- `∫₀ᵗ (t - τ)^(-a) dτ = t^(1-a) / (1-a)` for `a < 1`. -/
theorem integral_sub_rpow_neg {a : ℝ} (ha : a < 1) (t : ℝ) :
    ∫ τ in (0 : ℝ)..t, (t - τ) ^ (-a) = t ^ (1 - a) / (1 - a) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-a)) t,
    integral_rpow (Or.inl (by linarith))]
  have h1 : (-a + 1) = 1 - a := by ring
  simp only [sub_self, sub_zero, h1]
  rw [Real.zero_rpow (by linarith)]
  simp

/-- Pointwise bound for the singular integral when `h(s) ≤ M (1 + s)` on `[0, t]`: with
`0 < b' ≤ b` and `b' ≤ 1`,
`∫₀ᵗ (t-τ)^(-a) (1+τ)^(-b) h(τ) dτ ≤ M (1+t)^(1-b') t^(1-a) / (1-a)`. -/
theorem integral_singular_le {h : ℝ → ℝ} {a b b' M t : ℝ} (ha1 : a < 1)
    (hb'b : b' ≤ b) (hb'1 : b' ≤ 1) (ht : 0 ≤ t) (hnn : ∀ s, 0 ≤ s → s ≤ t → 0 ≤ h s)
    (hM : ∀ s, 0 ≤ s → s ≤ t → h s ≤ M * (1 + s)) :
    ∫ τ in (0 : ℝ)..t, (t - τ) ^ (-a) * (1 + τ) ^ (-b) * h τ ≤
      M * (1 + t) ^ (1 - b') * (t ^ (1 - a) / (1 - a)) := by
  have hM0 : 0 ≤ M := by
    have h1 := hM 0 le_rfl ht
    have h2 := hnn 0 le_rfl ht
    nlinarith
  have hint : IntervalIntegrable (fun τ : ℝ => (t - τ) ^ (-a) * (M * (1 + t) ^ (1 - b')))
      volume 0 t := (intervalIntegrable_sub_rpow_neg ha1 t).mul_const _
  have e : M * (1 + t) ^ (1 - b') * (t ^ (1 - a) / (1 - a)) =
      (∫ τ in (0 : ℝ)..t, (t - τ) ^ (-a)) * (M * (1 + t) ^ (1 - b')) := by
    rw [integral_sub_rpow_neg ha1 t]; ring
  rw [e, ← intervalIntegral.integral_mul_const,
    intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le ht]
  refine integral_mono_of_nonneg ?_ hint.1 ?_
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun τ hτ => ?_)
    have hh := hnn τ hτ.1.le hτ.2
    have h0 : 0 ≤ t - τ := by linarith [hτ.2]
    have h1 : 0 ≤ 1 + τ := by linarith [hτ.1]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg h0 _) (Real.rpow_nonneg h1 _)) hh
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun τ hτ => ?_)
    have hτ0 : 0 ≤ τ := hτ.1.le
    have hk : 0 ≤ (t - τ) ^ (-a) := Real.rpow_nonneg (by linarith [hτ.2]) _
    have h1 : (1 + τ) ^ (-b) ≤ (1 + τ) ^ (-b') :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : (1 + τ) ^ (-b') * h τ ≤ M * (1 + t) ^ (1 - b') := by
      calc (1 + τ) ^ (-b') * h τ ≤ (1 + τ) ^ (-b') * (M * (1 + τ)) :=
            mul_le_mul_of_nonneg_left (hM τ hτ0 hτ.2) (by positivity)
        _ = M * (1 + τ) ^ (1 - b') := by
            have : (1 + τ) ^ (1 - b') = (1 + τ) ^ (-b') * (1 + τ) := by
              rw [sub_eq_add_neg, Real.rpow_add (by linarith), Real.rpow_one, mul_comm]
            rw [this]; ring
        _ ≤ M * (1 + t) ^ (1 - b') :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) (by linarith [hτ.2])
              (by linarith)) hM0
    have h3 : (1 + τ) ^ (-b) * h τ ≤ M * (1 + t) ^ (1 - b') :=
      le_trans (mul_le_mul_of_nonneg_right h1 (hnn τ hτ0 hτ.2)) h2
    calc (t - τ) ^ (-a) * (1 + τ) ^ (-b) * h τ = (t - τ) ^ (-a) * ((1 + τ) ^ (-b) * h τ) := by ring
      _ ≤ (t - τ) ^ (-a) * (M * (1 + t) ^ (1 - b')) := mul_le_mul_of_nonneg_left h3 hk

/-- Power bookkeeping: `(1+s)^(1-b') s^(1-a) ≤ (1+s)^(1-a-b') (1+s)`. -/
theorem pow_bookkeeping {a b' s : ℝ} (ha1 : a < 1) (hs : 0 ≤ s) :
    (1 + s) ^ (1 - b') * s ^ (1 - a) ≤ (1 + s) ^ (1 - a - b') * (1 + s) := by
  have h1 : s ^ (1 - a) ≤ (1 + s) ^ (1 - a) :=
    Real.rpow_le_rpow hs (by linarith) (by linarith)
  calc (1 + s) ^ (1 - b') * s ^ (1 - a) ≤ (1 + s) ^ (1 - b') * (1 + s) ^ (1 - a) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by linarith) _)
    _ = (1 + s) ^ (1 - a - b') * (1 + s) := by
        rw [← Real.rpow_add (by linarith), ← Real.rpow_add_one (by linarith)]
        congr 1; ring

/-- **Gronwall inequality with a weakly singular kernel** (Brandolese). Let `h ≥ 0` be locally
bounded on `[0, ∞)` and satisfy
`h(t) ≤ C₁ (1 + t) + C₂ ∫₀ᵗ (t-τ)^(-a) (1+τ)^(-b) h(τ) dτ` for `t ≥ 0`, where `0 < a < 1`,
`b > 0` and `a + b > 1`. Then `h(t) ≤ C (1 + t)` for some constant `C`. -/
theorem gronwall_singular {h : ℝ → ℝ} {C₁ C₂ a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb : 0 < b)
    (hab : 1 < a + b) (hC₂ : 0 ≤ C₂) (hnn : ∀ t, 0 ≤ t → 0 ≤ h t)
    (hloc : ∀ T, ∃ B, ∀ t, 0 ≤ t → t ≤ T → h t ≤ B)
    (hineq : ∀ t, 0 ≤ t →
      h t ≤ C₁ * (1 + t) + C₂ * ∫ τ in (0 : ℝ)..t, (t - τ) ^ (-a) * (1 + τ) ^ (-b) * h τ) :
    ∃ C : ℝ, ∀ t, 0 ≤ t → h t ≤ C * (1 + t) := by
  -- reduce to the exponent `b' = min b 1`
  set b' : ℝ := min b 1 with hb'
  have hb'b : b' ≤ b := min_le_left _ _
  have hb'1 : b' ≤ 1 := min_le_right _ _
  have hb'0 : 0 < b' := lt_min hb one_pos
  have hab' : 1 < a + b' := by
    rcases le_total b 1 with h1 | h1
    · rw [hb', min_eq_left h1]; exact hab
    · rw [hb', min_eq_right h1]; linarith
  set δ : ℝ := a + b' - 1 with hδ
  have hδ0 : 0 < δ := by linarith
  -- the factor `C₂ (1+s)^(-δ) / (1-a)` is eventually `≤ 1/2`
  have hten : Filter.Tendsto (fun s : ℝ => C₂ * (1 + s) ^ (-δ) / (1 - a)) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun s : ℝ => (1 + s) ^ (-δ)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hδ0).comp (Filter.tendsto_atTop_add_const_left _ 1
        Filter.tendsto_id)
    simpa [mul_div_assoc] using (h1.const_mul C₂).div_const (1 - a)
  obtain ⟨T₀', hT₀'⟩ := Filter.eventually_atTop.1 (hten.eventually_lt_const
    (show (0 : ℝ) < 1 / 2 by norm_num))
  set T₀ : ℝ := max T₀' 0 with hT₀
  have hT₀0 : 0 ≤ T₀ := le_max_right _ _
  have hκ : ∀ s, T₀ ≤ s → C₂ * (1 + s) ^ (-δ) / (1 - a) ≤ 1 / 2 := fun s hs =>
    (hT₀' s (le_trans (le_max_left _ _) hs)).le
  obtain ⟨B₀, hB₀⟩ := hloc T₀
  have hB₀' : ∀ t, 0 ≤ t → t ≤ T₀ → h t / (1 + t) ≤ max B₀ 0 := by
    intro t ht ht'
    calc h t / (1 + t) ≤ h t := div_le_self (hnn t ht) (by linarith)
      _ ≤ B₀ := hB₀ t ht ht'
      _ ≤ max B₀ 0 := le_max_left _ _
  refine ⟨max (max B₀ 0) (2 * C₁), fun t₀ ht₀ => ?_⟩
  -- supremum of `h(s)/(1+s)` over `[0, t₀]`
  obtain ⟨B, hB⟩ := hloc t₀
  set S : Set ℝ := (fun s => h s / (1 + s)) '' Icc 0 t₀ with hS
  have hSbdd : BddAbove S := by
    refine ⟨max B 0, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    calc h s / (1 + s) ≤ h s := div_le_self (hnn s hs.1) (by linarith [hs.1])
      _ ≤ B := hB s hs.1 hs.2
      _ ≤ max B 0 := le_max_left _ _
  have hSne : S.Nonempty := ⟨_, ⟨0, ⟨le_rfl, ht₀⟩, rfl⟩⟩
  set M : ℝ := sSup S with hMdef
  have hMs : ∀ s, 0 ≤ s → s ≤ t₀ → h s ≤ M * (1 + s) := by
    intro s hs hs'
    have : h s / (1 + s) ≤ M := le_csSup hSbdd ⟨s, ⟨hs, hs'⟩, rfl⟩
    rwa [div_le_iff₀ (by linarith)] at this
  have hM0 : 0 ≤ M := by
    have := hMs 0 le_rfl ht₀
    have := hnn 0 le_rfl
    nlinarith
  -- `M ≤ max B₀⁺ (C₁ + M / 2)`
  have hMle : M ≤ max (max B₀ 0) (C₁ + M / 2) := by
    refine csSup_le hSne ?_
    rintro _ ⟨s, hs, rfl⟩
    rcases le_total s T₀ with hsT | hsT
    · exact le_trans (hB₀' s hs.1 hsT) (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      have hs1 : 0 < 1 + s := by linarith [hs.1]
      have hI := integral_singular_le (h := h) (a := a) (b := b) (b' := b') (M := M) (t := s)
        ha1 hb'b hb'1 hs.1 (fun r hr hr' => hnn r hr)
        (fun r hr hr' => hMs r hr (hr'.trans hs.2))
      have hbk := pow_bookkeeping (a := a) (b' := b') ha1 hs.1
      have h1a : 0 < 1 - a := by linarith
      have hκs := hκ s hsT
      rw [div_le_iff₀ hs1]
      have e1 : 1 - a - b' = -δ := by rw [hδ]; ring
      rw [e1] at hbk
      calc h s ≤ C₁ * (1 + s) + C₂ * ∫ τ in (0 : ℝ)..s,
            (s - τ) ^ (-a) * (1 + τ) ^ (-b) * h τ := hineq s hs.1
        _ ≤ C₁ * (1 + s) + C₂ * (M * (1 + s) ^ (1 - b') * (s ^ (1 - a) / (1 - a))) := by
            gcongr
        _ = C₁ * (1 + s) + M * (C₂ * ((1 + s) ^ (1 - b') * s ^ (1 - a)) / (1 - a)) := by
            ring
        _ ≤ C₁ * (1 + s) + M * (C₂ * ((1 + s) ^ (-δ) * (1 + s)) / (1 - a)) := by
            gcongr
        _ = C₁ * (1 + s) + M * (C₂ * (1 + s) ^ (-δ) / (1 - a)) * (1 + s) := by ring
        _ ≤ C₁ * (1 + s) + M * (1 / 2) * (1 + s) := by gcongr
        _ = (C₁ + M / 2) * (1 + s) := by ring
  have hMK : M ≤ max (max B₀ 0) (2 * C₁) := by
    rcases max_cases (max B₀ 0) (C₁ + M / 2) with ⟨h2, _⟩ | ⟨h2, _⟩
    · rw [h2] at hMle
      exact le_trans hMle (le_max_left _ _)
    · rw [h2] at hMle
      exact le_trans (by linarith) (le_max_right _ _)
  calc h t₀ ≤ M * (1 + t₀) := hMs t₀ ht₀ le_rfl
    _ ≤ max (max B₀ 0) (2 * C₁) * (1 + t₀) :=
        mul_le_mul_of_nonneg_right hMK (by linarith)

end

end FracLap
