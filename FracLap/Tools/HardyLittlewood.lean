/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# FracLap.Tools.HardyLittlewood

The centered Hardy--Littlewood maximal function on `ℝ` for `[0, ∞]`-valued functions and its
weak type `(1, 1)` inequality (Vitali covering with constant `5`).

- `hlMax g x = sup_{r > 0} (2r)⁻¹ ∫_{[x-r, x+r]} g`.
- `hlMax_weak_type`: `|{hlMax g > λ}| ≤ 5 λ⁻¹ ∫ g`.
-/

namespace FracLap

open MeasureTheory Set Metric
open scoped ENNReal

@[expose] public section

/-- The centered Hardy--Littlewood maximal function of `g : ℝ → ℝ≥0∞`. -/
noncomputable def hlMax (g : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ⨆ r : {r : ℝ // 0 < r}, (ENNReal.ofReal (2 * r.1))⁻¹ * ∫⁻ y in Icc (x - r.1) (x + r.1), g y

/-- **Weak type `(1, 1)`** of the maximal function: `|{M g > λ}| ≤ 5 λ⁻¹ ∫ g`. -/
theorem hlMax_weak_type (g : ℝ → ℝ≥0∞) {l : ℝ≥0∞} (hl : l ≠ 0) (hl' : l ≠ ⊤) :
    volume {x : ℝ | l < hlMax g x} ≤ 5 * l⁻¹ * ∫⁻ y, g y := by
  set G : ℝ≥0∞ := ∫⁻ y, g y with hG
  by_cases hGt : G = ⊤
  · rw [hGt, ENNReal.mul_top (by simp [hl'])]; exact le_top
  set E : Set ℝ := {x | l < hlMax g x} with hE
  have hex : ∀ x : E, ∃ r : ℝ, 0 < r ∧
      l * ENNReal.ofReal (2 * r) ≤ ∫⁻ y in Icc (x.1 - r) (x.1 + r), g y := by
    intro x
    have hx : l < hlMax g x.1 := x.2
    unfold hlMax at hx
    obtain ⟨⟨r, hr⟩, hlt⟩ := lt_iSup_iff.1 hx
    refine ⟨r, hr, ?_⟩
    have ha0 : ENNReal.ofReal (2 * r) ≠ 0 := by simp [hr]
    have hat : ENNReal.ofReal (2 * r) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc l * ENNReal.ofReal (2 * r) = ENNReal.ofReal (2 * r) * l := mul_comm _ _
      _ ≤ ENNReal.ofReal (2 * r) * ((ENNReal.ofReal (2 * r))⁻¹ *
            ∫⁻ y in Icc (x.1 - r) (x.1 + r), g y) :=
          mul_le_mul_of_nonneg_left hlt.le bot_le
      _ = _ := by rw [← mul_assoc, ENNReal.mul_inv_cancel ha0 hat, one_mul]
  choose r hr0 hrl using hex
  -- radii are bounded
  set R : ℝ := (G * l⁻¹).toReal with hR
  have hGfin : G * l⁻¹ ≠ ⊤ := ENNReal.mul_ne_top hGt (ENNReal.inv_ne_top.2 hl)
  have hrR : ∀ a : E, r a ≤ R := by
    intro a
    have h1 : l * ENNReal.ofReal (2 * r a) ≤ G :=
      (hrl a).trans (setLIntegral_le_lintegral _ _)
    have h2 : ENNReal.ofReal (2 * r a) ≤ G * l⁻¹ := by
      rw [mul_comm] at h1
      calc ENNReal.ofReal (2 * r a) = ENNReal.ofReal (2 * r a) * l * l⁻¹ := by
            rw [mul_assoc, ENNReal.mul_inv_cancel hl hl', mul_one]
        _ ≤ G * l⁻¹ := by gcongr
    have h3 := (ENNReal.ofReal_le_iff_le_toReal hGfin).1 h2
    have := hr0 a
    linarith
  obtain ⟨u, -, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
    (univ : Set E) (fun a : E => a.1) r R (fun a _ => hrR a) 5 (by norm_num)
  have hu : u.Countable := hdisj.countable_of_nonempty_interior fun a _ => by
    rw [interior_closedBall _ (hr0 a).ne']
    exact nonempty_ball.2 (hr0 a)
  have : Countable u := hu.to_subtype
  have hEcov : E ⊆ ⋃ b ∈ u, closedBall (b : ℝ) (5 * r b) := by
    intro x hx
    obtain ⟨b, hb, hsub⟩ := hcov ⟨x, hx⟩ (mem_univ _)
    refine mem_biUnion hb (hsub ?_)
    exact mem_closedBall_self (hr0 _).le
  have hball : ∀ b : E, closedBall (b : ℝ) (r b) = Icc (b.1 - r b) (b.1 + r b) :=
    fun b => Real.closedBall_eq_Icc
  have hmeasB : ∀ b : u, MeasurableSet (closedBall ((b : E) : ℝ) (r b)) := fun b =>
    measurableSet_closedBall
  have hdisj' : Pairwise (Function.onFun Disjoint fun b : u => closedBall ((b : E) : ℝ) (r b)) := by
    intro b c hbc
    exact hdisj b.2 c.2 (fun h => hbc (Subtype.ext h))
  have hsumI : ∑' b : u, ∫⁻ y in closedBall ((b : E) : ℝ) (r b), g y ≤ G := by
    rw [← lintegral_iUnion hmeasB hdisj']
    exact setLIntegral_le_lintegral _ _
  calc volume E ≤ volume (⋃ b ∈ u, closedBall (b : ℝ) (5 * r b)) := measure_mono hEcov
    _ ≤ ∑' b : u, volume (closedBall ((b : E) : ℝ) (5 * r b)) := measure_biUnion_le _ hu _
    _ ≤ ∑' b : u, 5 * l⁻¹ * ∫⁻ y in closedBall ((b : E) : ℝ) (r b), g y := by
        refine tsum_le_tsum fun b => ?_
        rw [Real.volume_closedBall]
        have hI := hrl b
        rw [← hball b] at hI
        have hb0 : 0 < r b := hr0 b
        have h5 : ENNReal.ofReal (2 * r b) ≤ l⁻¹ * ∫⁻ y in closedBall ((b : E) : ℝ) (r b), g y := by
          calc ENNReal.ofReal (2 * r b) = l⁻¹ * (l * ENNReal.ofReal (2 * r b)) := by
                rw [← mul_assoc, mul_comm l⁻¹ l, ENNReal.mul_inv_cancel hl hl', one_mul]
            _ ≤ l⁻¹ * ∫⁻ y in closedBall ((b : E) : ℝ) (r b), g y :=
                mul_le_mul_of_nonneg_left hI bot_le
        calc ENNReal.ofReal (2 * (5 * r b)) = 5 * ENNReal.ofReal (2 * r b) := by
              rw [show 2 * (5 * r b) = 5 * (2 * r b) by ring,
                ENNReal.ofReal_mul (by norm_num)]; simp
          _ ≤ 5 * (l⁻¹ * ∫⁻ y in closedBall ((b : E) : ℝ) (r b), g y) :=
              mul_le_mul_of_nonneg_left h5 bot_le
          _ = _ := by rw [mul_assoc]
    _ = 5 * l⁻¹ * ∑' b : u, ∫⁻ y in closedBall ((b : E) : ℝ) (r b), g y := by
        rw [ENNReal.tsum_mul_left]
    _ ≤ 5 * l⁻¹ * G := by gcongr

/-- The superlevel sets of the maximal function are open. -/
theorem isOpen_hlMax_gt (g : ℝ → ℝ≥0∞) (t : ℝ≥0∞) : IsOpen {x : ℝ | t < hlMax g x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx' : t < hlMax g x := hx
  unfold hlMax at hx'
  obtain ⟨⟨r, hr⟩, hlt⟩ := lt_iSup_iff.1 hx'
  set I : ℝ≥0∞ := ∫⁻ y in Icc (x - r) (x + r), g y with hI
  have hcont : Filter.Tendsto (fun δ : ℝ => (ENNReal.ofReal (2 * (r + δ)))⁻¹ * I)
      (nhds 0) (nhds ((ENNReal.ofReal (2 * r))⁻¹ * I)) := by
    have h1 : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal (2 * (r + δ))) (nhds 0)
        (nhds (ENNReal.ofReal (2 * r))) := by
      refine (ENNReal.tendsto_ofReal ?_)
      have : Filter.Tendsto (fun δ : ℝ => 2 * (r + δ)) (nhds 0) (nhds (2 * (r + 0))) :=
        (tendsto_const_nhds.add Filter.tendsto_id).const_mul 2
      simpa using this
    have h2 : Filter.Tendsto (fun δ : ℝ => (ENNReal.ofReal (2 * (r + δ)))⁻¹) (nhds 0)
        (nhds (ENNReal.ofReal (2 * r))⁻¹) := tendsto_inv_iff.2 h1
    exact ENNReal.Tendsto.mul_const h2 (Or.inl (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top))
  have hev : ∀ᶠ δ in nhds (0 : ℝ), t < (ENNReal.ofReal (2 * (r + δ)))⁻¹ * I :=
    hcont.eventually (lt_mem_nhds hlt)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  -- choose a positive radius `δ < ε`
  set δ : ℝ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδε : dist δ 0 < ε := by simp [hδ, abs_of_pos hε]; linarith
  have hB := hball hδε
  refine Metric.mem_nhds_iff.2 ⟨δ, hδ0, fun x' hx' => ?_⟩
  change t < hlMax g x'
  have hd : |x' - x| < δ := by simpa [Real.dist_eq] using hx'
  have hsub : Icc (x - r) (x + r) ⊆ Icc (x' - (r + δ)) (x' + (r + δ)) := by
    intro y hy
    rw [abs_lt] at hd
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  unfold hlMax
  refine lt_of_lt_of_le hB ?_
  refine le_iSup_of_le ⟨r + δ, by linarith⟩ ?_
  exact mul_le_mul_of_nonneg_left (lintegral_mono_set hsub) bot_le

theorem measurable_hlMax (g : ℝ → ℝ≥0∞) : Measurable (hlMax g) := by
  refine measurable_of_Ioi fun t => ?_
  exact (isOpen_hlMax_gt g t).measurableSet

/-- Splitting at height `s`: `M g ≤ M (g · 1_{g > s}) + s`. -/
theorem hlMax_le_add_split (g : ℝ → ℝ≥0∞) (s : ℝ≥0∞) (x : ℝ) :
    hlMax g x ≤ hlMax (fun y => if s < g y then g y else 0) x + s := by
  unfold hlMax
  refine iSup_le fun ⟨r, hr⟩ => ?_
  have ha0 : ENNReal.ofReal (2 * r) ≠ 0 := by simp [hr]
  have hat : ENNReal.ofReal (2 * r) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt : ∀ y, g y ≤ (if s < g y then g y else 0) + s := fun y => by
    by_cases h : s < g y
    · simp [h]
    · simp only [h, ↓reduceIte, zero_add]; exact not_lt.1 h
  have hvol : volume (Icc (x - r) (x + r)) = ENNReal.ofReal (2 * r) := by
    rw [Real.volume_Icc]; congr 1; ring
  have h1 : ∫⁻ y in Icc (x - r) (x + r), g y ≤
      (∫⁻ y in Icc (x - r) (x + r), (if s < g y then g y else 0)) +
        s * ENNReal.ofReal (2 * r) := by
    calc ∫⁻ y in Icc (x - r) (x + r), g y
        ≤ ∫⁻ y in Icc (x - r) (x + r), ((if s < g y then g y else 0) + s) := lintegral_mono hpt
      _ = _ := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, hvol]
  calc (ENNReal.ofReal (2 * r))⁻¹ * ∫⁻ y in Icc (x - r) (x + r), g y
      ≤ (ENNReal.ofReal (2 * r))⁻¹ * ((∫⁻ y in Icc (x - r) (x + r),
          (if s < g y then g y else 0)) + s * ENNReal.ofReal (2 * r)) :=
        mul_le_mul_of_nonneg_left h1 bot_le
    _ = (ENNReal.ofReal (2 * r))⁻¹ * (∫⁻ y in Icc (x - r) (x + r),
          (if s < g y then g y else 0)) + s := by
        rw [mul_add, mul_comm s, ← mul_assoc, ENNReal.inv_mul_cancel ha0 hat, one_mul]
    _ ≤ _ := by
        gcongr
        exact le_iSup_of_le ⟨r, hr⟩ le_rfl

/-- `∫₀^a t^q dt` as a lower integral. -/
theorem lintegral_rpow_Ioo {a : ℝ} (ha : 0 ≤ a) {q : ℝ} (hq : -1 < q) :
    ∫⁻ t in Ioo 0 a, ENNReal.ofReal (t ^ q) = ENNReal.ofReal (a ^ (q + 1) / (q + 1)) := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ q) volume 0 a :=
    intervalIntegral.intervalIntegrable_rpow' hq
  have h1 : ∫⁻ t in Ioo 0 a, ENNReal.ofReal (t ^ q) = ∫⁻ t in Ioc 0 a, ENNReal.ofReal (t ^ q) :=
    setLIntegral_congr Ioo_ae_eq_Ioc
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le ha, integral_rpow (Or.inl hq)]
    simp [Real.zero_rpow (by linarith : q + 1 ≠ 0)]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).1 hint
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le q

/-- The maximal function of an `L¹` function is finite almost everywhere. -/
theorem hlMax_ae_ne_top {g : ℝ → ℝ≥0∞} (hg1 : ∫⁻ y, g y ≠ ⊤) : ∀ᵐ x, hlMax g x ≠ ⊤ := by
  have hnull : volume {x : ℝ | hlMax g x = ⊤} = 0 := by
    refine le_antisymm ?_ bot_le
    have hnb : ∀ n : ℕ, 0 < n → volume {x : ℝ | hlMax g x = ⊤} ≤
        5 * ((n : ℝ≥0∞))⁻¹ * ∫⁻ y, g y := fun n hn =>
      (measure_mono (fun x hx => by
        simp only [mem_ofPred_eq] at hx ⊢
        rw [hx]; exact ENNReal.natCast_lt_top n)).trans
        (hlMax_weak_type g (Nat.cast_ne_zero.2 hn.ne') (ENNReal.natCast_ne_top n))
    have ht : Filter.Tendsto (fun n : ℕ => 5 * ((n : ℝ≥0∞))⁻¹ * ∫⁻ y, g y) Filter.atTop
        (nhds 0) := by
      have h0 := ENNReal.Tendsto.const_mul (a := 5) ENNReal.tendsto_inv_nat_nhds_zero
        (Or.inr (by norm_num))
      have h1 := ENNReal.Tendsto.mul_const h0 (Or.inr hg1)
      simpa using h1
    exact ge_of_tendsto ht (Filter.eventually_atTop.2 ⟨1, fun n hn => hnb n (by omega)⟩)
  exact measure_eq_zero_iff_ae_notMem.1 hnull

/-- **Distribution inequality** for the maximal function of `g = ofReal ∘ h`: for `t > 0`,
`|{M g > t}| ≤ 5 (t/2)⁻¹ ∫ g 1_{g > t/2}`. -/
theorem hlMax_distribution (g : ℝ → ℝ≥0∞) {t : ℝ} (ht : 0 < t) :
    volume {a : ℝ | ENNReal.ofReal t < hlMax g a} ≤
      5 * (ENNReal.ofReal (t / 2))⁻¹ * ∫⁻ y, (if ENNReal.ofReal (t / 2) < g y then g y else 0) := by
  have hs0 : ENNReal.ofReal (t / 2) ≠ 0 := by simp [ht]
  have hst : ENNReal.ofReal (t / 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  refine le_trans (measure_mono ?_) (hlMax_weak_type _ hs0 hst)
  intro a ha
  simp only [mem_ofPred_eq] at ha ⊢
  have h2 := hlMax_le_add_split g (ENNReal.ofReal (t / 2)) a
  have h3 : ENNReal.ofReal (t / 2) + ENNReal.ofReal (t / 2) <
      hlMax (fun y => if ENNReal.ofReal (t / 2) < g y then g y else 0) a +
        ENNReal.ofReal (t / 2) := by
    calc ENNReal.ofReal (t / 2) + ENNReal.ofReal (t / 2) = ENNReal.ofReal t := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
      _ < hlMax g a := ha
      _ ≤ _ := h2
  exact (ENNReal.add_lt_add_iff_right hst).1 h3

/-- **Strong type `(p, p)`** of the Hardy--Littlewood maximal function, `p > 1`:
`∫ (M g)^p ≤ (10 p 2^(p-1) / (p-1)) ∫ g^p` for `g = ofReal ∘ h`, `h ≥ 0` measurable, `g ∈ L¹`. -/
theorem hlMax_strong_type {p : ℝ} (hp : 1 < p) {h : ℝ → ℝ} (hm : Measurable h)
    (hnn : ∀ x, 0 ≤ h x) (h1 : ∫⁻ y, ENNReal.ofReal (h y) ≠ ⊤) :
    ∫⁻ x, hlMax (fun y => ENNReal.ofReal (h y)) x ^ p ≤
      ENNReal.ofReal (10 * p * 2 ^ (p - 1) / (p - 1)) * ∫⁻ y, ENNReal.ofReal (h y) ^ p := by
  set g : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (h y) with hgdef
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp hm
  have hp0 : 0 < p := by linarith
  have hM : Measurable (hlMax g) := measurable_hlMax g
  have hMfin := hlMax_ae_ne_top h1
  set f : ℝ → ℝ := fun x => (hlMax g x).toReal with hf
  have hf_meas : Measurable f := hM.ennreal_toReal
  have e1 : ∫⁻ x, hlMax g x ^ p = ∫⁻ x, ENNReal.ofReal (f x ^ p) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hMfin] with x hx
    have hx' : hlMax g x ≠ ⊤ := hx
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp0.le, ENNReal.ofReal_toReal hx']
  rw [e1, lintegral_rpow_eq_lintegral_meas_lt_mul volume (Filter.Eventually.of_forall
    fun x => ENNReal.toReal_nonneg) hf_meas.aemeasurable hp0]
  -- pointwise bound on the integrand of the layer-cake formula
  set g₁ : ℝ → ℝ → ℝ≥0∞ := fun t y => if ENNReal.ofReal (t / 2) < g y then g y else 0 with hg₁
  have hbound : ∀ t ∈ Ioi (0 : ℝ), volume {a : ℝ | t < f a} * ENNReal.ofReal (t ^ (p - 1)) ≤
      ∫⁻ y, 10 * (g₁ t y * ENNReal.ofReal (t ^ (p - 2))) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hsub : {a : ℝ | t < f a} ⊆ {a : ℝ | ENNReal.ofReal t < hlMax g a} := by
      intro a ha
      simp only [mem_ofPred_eq, hf] at ha ⊢
      have hne : hlMax g a ≠ ⊤ := by
        intro htop; rw [htop] at ha; simp at ha; linarith
      exact (ENNReal.ofReal_lt_iff_lt_toReal ht0.le hne).2 ha
    have hd := (measure_mono hsub).trans (hlMax_distribution g ht0)
    have hpow : (ENNReal.ofReal (t / 2))⁻¹ * ENNReal.ofReal (t ^ (p - 1)) =
        2 * ENNReal.ofReal (t ^ (p - 2)) := by
      rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      have : (t / 2)⁻¹ * t ^ (p - 1) = 2 * t ^ (p - 2) := by
        rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add_one ht0.ne']
        field_simp
      rw [this, ENNReal.ofReal_mul (by norm_num)]
      simp
    calc volume {a : ℝ | t < f a} * ENNReal.ofReal (t ^ (p - 1))
        ≤ (5 * (ENNReal.ofReal (t / 2))⁻¹ * ∫⁻ y, g₁ t y) * ENNReal.ofReal (t ^ (p - 1)) :=
          mul_le_mul_of_nonneg_right hd bot_le
      _ = 10 * ((ENNReal.ofReal (t ^ (p - 2))) * ∫⁻ y, g₁ t y) := by
          calc (5 * (ENNReal.ofReal (t / 2))⁻¹ * ∫⁻ y, g₁ t y) * ENNReal.ofReal (t ^ (p - 1))
              = 5 * (∫⁻ y, g₁ t y) * ((ENNReal.ofReal (t / 2))⁻¹ *
                  ENNReal.ofReal (t ^ (p - 1))) := by ring
            _ = _ := by rw [hpow]; ring
      _ = ∫⁻ y, 10 * (g₁ t y * ENNReal.ofReal (t ^ (p - 2))) := by
          rw [lintegral_const_mul' _ _ (by norm_num), lintegral_mul_const' _ _
            ENNReal.ofReal_ne_top]
          ring
  have hmeas : AEMeasurable (Function.uncurry fun (t y : ℝ) =>
      10 * (g₁ t y * ENNReal.ofReal (t ^ (p - 2))))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    refine Measurable.aemeasurable ?_
    have hcond : MeasurableSet {q : ℝ × ℝ | ENNReal.ofReal (q.1 / 2) < g q.2} :=
      measurableSet_lt (ENNReal.measurable_ofReal.comp (measurable_fst.div_const 2))
        (hgm.comp measurable_snd)
    have hg₁m : Measurable (fun q : ℝ × ℝ => g₁ q.1 q.2) :=
      Measurable.ite hcond (hgm.comp measurable_snd) measurable_const
    exact measurable_const.mul (hg₁m.mul (ENNReal.measurable_ofReal.comp
      (measurable_fst.pow_const _)))
  have hinner : ∀ y : ℝ, ∫⁻ t in Ioi (0 : ℝ), 10 * (g₁ t y * ENNReal.ofReal (t ^ (p - 2))) =
      10 * ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) * ENNReal.ofReal (h y) ^ p := by
    intro y
    have hy0 : 0 ≤ h y := hnn y
    have hcongr : ∀ t ∈ Ioi (0 : ℝ), 10 * (g₁ t y * ENNReal.ofReal (t ^ (p - 2))) =
        (Iio (2 * h y)).indicator (fun t : ℝ => 10 * (g y * ENNReal.ofReal (t ^ (p - 2)))) t := by
      intro t ht
      have ht0 : 0 < t := ht
      by_cases hlt : t < 2 * h y
      · have : ENNReal.ofReal (t / 2) < g y := by
          rw [hgdef]
          exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
        simp only [hg₁, this, ↓reduceIte, Set.indicator_of_mem (show t ∈ Iio (2 * h y) from hlt)]
      · have : ¬ ENNReal.ofReal (t / 2) < g y := by
          rw [hgdef]
          intro hh
          have := (ENNReal.ofReal_lt_ofReal_iff'.1 hh).1
          linarith
        simp only [hg₁, this, ↓reduceIte, zero_mul, mul_zero,
          Set.indicator_of_notMem (show t ∉ Iio (2 * h y) from hlt)]
    rw [setLIntegral_congr_fun measurableSet_Ioi hcongr, lintegral_indicator measurableSet_Iio,
      Measure.restrict_restrict measurableSet_Iio, inter_comm, Ioi_inter_Iio]
    rw [lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_rpow_Ioo (by linarith) (by linarith : (-1 : ℝ) < p - 2)]
    rw [show p - 2 + 1 = p - 1 by ring, ENNReal.ofReal_rpow_of_nonneg hy0 hp0.le,
      ← ENNReal.ofReal_mul hy0]
    have hp1 : p - 1 ≠ 0 := by linarith
    have key : h y * ((2 * h y) ^ (p - 1) / (p - 1)) = 2 ^ (p - 1) / (p - 1) * h y ^ p := by
      rw [Real.mul_rpow (by norm_num) hy0]
      rcases hy0.eq_or_lt with h0 | hpos
      · rw [← h0]; simp [Real.zero_rpow hp0.ne', zero_mul, mul_zero]
      · have : h y ^ p = h y * h y ^ (p - 1) := by
          rw [← Real.rpow_one_add' hy0 (by linarith)]; congr 1; ring
        rw [this]; ring
    rw [key, ENNReal.ofReal_mul (by positivity)]
    ring
  calc ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), volume {a : ℝ | t < f a} *
        ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
          ∫⁻ y, 10 * (g₁ t y * ENNReal.ofReal (t ^ (p - 2))) :=
        mul_le_mul_of_nonneg_left (setLIntegral_mono' measurableSet_Ioi hbound) bot_le
    _ = ENNReal.ofReal p * ∫⁻ y, ∫⁻ t in Ioi (0 : ℝ),
          10 * (g₁ t y * ENNReal.ofReal (t ^ (p - 2))) := by
        rw [lintegral_lintegral_swap hmeas]
    _ = ENNReal.ofReal p * ∫⁻ y, 10 * ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) *
          ENNReal.ofReal (h y) ^ p := by
        congr 1
        exact lintegral_congr hinner
    _ = ENNReal.ofReal (10 * p * 2 ^ (p - 1) / (p - 1)) * ∫⁻ y, ENNReal.ofReal (h y) ^ p := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top),
          ← mul_assoc]
        congr 1
        rw [show (10 : ℝ≥0∞) = ENNReal.ofReal 10 by simp,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10),
          ← ENNReal.ofReal_mul hp0.le]
        congr 1
        ring

/-- **Level sets of a symmetric decreasing function**: for a symmetric order-interval `A ⊂ ℝ`
of finite measure, `∫_A g(x - y) dy ≤ |A| · M g (x)`. -/
theorem lintegral_symm_set_le {A : Set ℝ}
    (hsym : ∀ y ∈ A, ∀ z : ℝ, |z| ≤ |y| → z ∈ A) (hAfin : volume A ≠ ⊤) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) (x : ℝ) :
    ∫⁻ y in A, g (x - y) ≤ volume A * hlMax g x := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  have hbdd : BddAbove ((fun y : ℝ => |y|) '' A) := by
    by_contra hnb
    rw [not_bddAbove_iff] at hnb
    have hall : ∀ N : ℝ, Icc (-N) N ⊆ A := by
      intro N z hz
      obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := hnb N
      exact hsym y hy z ((abs_le.2 hz).trans hlt.le)
    apply hAfin
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    calc (r : ℝ≥0∞) = ENNReal.ofReal (2 * ((r : ℝ) / 2)) := by
          rw [show 2 * ((r : ℝ) / 2) = r by ring, ENNReal.ofReal_coe_nnreal]
      _ = volume (Icc (-((r : ℝ) / 2)) ((r : ℝ) / 2)) := by
          rw [Real.volume_Icc]; congr 1; ring
      _ ≤ volume A := measure_mono (hall _)
  set ρ : ℝ := sSup ((fun y : ℝ => |y|) '' A) with hρ
  have himne : ((fun y : ℝ => |y|) '' A).Nonempty := hne.image _
  have hρ0 : 0 ≤ ρ := by
    obtain ⟨y, hy⟩ := hne
    exact (abs_nonneg y).trans (le_csSup hbdd ⟨y, hy, rfl⟩)
  have hsub1 : A ⊆ Icc (-ρ) ρ := fun y hy =>
    abs_le.1 (le_csSup hbdd ⟨y, hy, rfl⟩)
  have hsub2 : Ioo (-ρ) ρ ⊆ A := by
    intro z hz
    have hzlt : |z| < ρ := abs_lt.2 hz
    obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup himne hzlt
    exact hsym y hy z hlt.le
  have hvol : ENNReal.ofReal (2 * ρ) ≤ volume A := by
    calc ENNReal.ofReal (2 * ρ) = volume (Ioo (-ρ) ρ) := by
          rw [Real.volume_Ioo]; congr 1; ring
      _ ≤ volume A := measure_mono hsub2
  have hpre : (fun y : ℝ => x - y) ⁻¹' Icc (x - ρ) (x + ρ) = Icc (-ρ) ρ := by
    ext y; simp only [mem_preimage, mem_Icc]; constructor <;> intro h <;> constructor <;>
      linarith [h.1, h.2]
  have hI : ∫⁻ y in Icc (-ρ) ρ, g (x - y) = ∫⁻ y in Icc (x - ρ) (x + ρ), g y := by
    have hmp : MeasurePreserving (fun y : ℝ => x - y) volume volume :=
      Measure.measurePreserving_sub_left (volume : Measure ℝ) x
    have := hmp.setLIntegral_comp_preimage (s := Icc (x - ρ) (x + ρ)) measurableSet_Icc hg
    rwa [hpre] at this
  have hball : ∫⁻ y in Icc (x - ρ) (x + ρ), g y ≤ ENNReal.ofReal (2 * ρ) * hlMax g x := by
    rcases hρ0.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have ha0 : ENNReal.ofReal (2 * ρ) ≠ 0 := by simp [hpos]
      have hat : ENNReal.ofReal (2 * ρ) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hle : (ENNReal.ofReal (2 * ρ))⁻¹ * ∫⁻ y in Icc (x - ρ) (x + ρ), g y ≤ hlMax g x :=
        le_iSup_of_le (⟨ρ, hpos⟩ : {r : ℝ // 0 < r}) le_rfl
      calc ∫⁻ y in Icc (x - ρ) (x + ρ), g y
          = ENNReal.ofReal (2 * ρ) * ((ENNReal.ofReal (2 * ρ))⁻¹ *
              ∫⁻ y in Icc (x - ρ) (x + ρ), g y) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel ha0 hat, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left hle bot_le
  calc ∫⁻ y in A, g (x - y) ≤ ∫⁻ y in Icc (-ρ) ρ, g (x - y) := lintegral_mono_set hsub1
    _ = ∫⁻ y in Icc (x - ρ) (x + ρ), g y := hI
    _ ≤ ENNReal.ofReal (2 * ρ) * hlMax g x := hball
    _ ≤ volume A * hlMax g x := mul_le_mul_of_nonneg_right hvol bot_le

/-- **Domination by the maximal function** (Stein): for `K ≥ 0` symmetric decreasing with
`∫ K < ∞`, `∫ K(y) g(x - y) dy ≤ (∫ K) · M g (x)`. -/
theorem lintegral_mul_le_hlMax {K : ℝ → ℝ} (hKm : Measurable K) (hnn : ∀ y, 0 ≤ K y)
    (hdec : ∀ a b : ℝ, |a| ≤ |b| → K b ≤ K a) (hK : ∫⁻ y, ENNReal.ofReal (K y) ≠ ⊤)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (K y) * g (x - y) ≤ (∫⁻ y, ENNReal.ofReal (K y)) * hlMax g x := by
  set A : ℝ → Set ℝ := fun s => {y : ℝ | s < K y} with hA
  have hAm : ∀ s, MeasurableSet (A s) := fun s => measurableSet_lt measurable_const hKm
  have hlayer : ∀ y : ℝ, ENNReal.ofReal (K y) =
      ∫⁻ s in Ioi (0 : ℝ), {s : ℝ | s < K y}.indicator (fun _ => (1 : ℝ≥0∞)) s := by
    intro y
    rw [show {s : ℝ | s < K y} = Iio (K y) from rfl,
      lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
      one_mul, Iio_inter_Ioi, Real.volume_Ioo, sub_zero]
  have hAfin : ∀ s : ℝ, 0 < s → volume (A s) ≠ ⊤ := by
    intro s hs
    have hMk := mul_meas_ge_le_lintegral₀ (μ := volume)
      (f := fun y => ENNReal.ofReal (K y)) (ENNReal.measurable_ofReal.comp hKm).aemeasurable
      (ENNReal.ofReal s)
    have hsub : A s ⊆ {y | ENNReal.ofReal s ≤ ENNReal.ofReal (K y)} := fun y hy =>
      ENNReal.ofReal_le_ofReal (le_of_lt hy)
    have hlt : ENNReal.ofReal s * volume (A s) < ⊤ :=
      lt_of_le_of_lt ((mul_le_mul_of_nonneg_left (measure_mono hsub) bot_le).trans hMk)
        (lt_top_iff_ne_top.2 hK)
    intro htop
    rw [htop, ENNReal.mul_top (by simp [hs])] at hlt
    exact lt_irrefl _ hlt
  have hsymm : ∀ s : ℝ, ∀ y ∈ A s, ∀ z : ℝ, |z| ≤ |y| → z ∈ A s := fun s y hy z hz =>
    lt_of_lt_of_le hy (hdec z y hz)
  have hmeas : AEMeasurable (Function.uncurry fun (s y : ℝ) =>
      {s : ℝ | s < K y}.indicator (fun _ => (1 : ℝ≥0∞)) s * g (x - y))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    refine Measurable.aemeasurable ?_
    have hset : MeasurableSet {q : ℝ × ℝ | q.1 < K q.2} :=
      measurableSet_lt measurable_fst (hKm.comp measurable_snd)
    have h1 : Measurable fun q : ℝ × ℝ =>
        {s : ℝ | s < K q.2}.indicator (fun _ => (1 : ℝ≥0∞)) q.1 := by
      have : (fun q : ℝ × ℝ => {s : ℝ | s < K q.2}.indicator (fun _ => (1 : ℝ≥0∞)) q.1) =
          {q : ℝ × ℝ | q.1 < K q.2}.indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext q; simp [Set.indicator]
      rw [this]; exact measurable_const.indicator hset
    exact h1.mul (hg.comp (measurable_const.sub measurable_snd))
  calc ∫⁻ y, ENNReal.ofReal (K y) * g (x - y)
      = ∫⁻ y, (∫⁻ s in Ioi (0 : ℝ), {s : ℝ | s < K y}.indicator (fun _ => (1 : ℝ≥0∞)) s) *
          g (x - y) := by simp_rw [← hlayer]
    _ = ∫⁻ y, ∫⁻ s in Ioi (0 : ℝ), {s : ℝ | s < K y}.indicator (fun _ => (1 : ℝ≥0∞)) s *
          g (x - y) := by
        refine lintegral_congr fun y => ?_
        exact (lintegral_mul_const'' _
          ((measurable_const.indicator (measurableSet_Iio (a := K y))).aemeasurable)).symm
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ y, {s : ℝ | s < K y}.indicator (fun _ => (1 : ℝ≥0∞)) s *
          g (x - y) := by
        exact (lintegral_lintegral_swap hmeas).symm
    _ ≤ ∫⁻ s in Ioi (0 : ℝ), volume (A s) * hlMax g x := by
        refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
        have hs0 : 0 < s := hs
        have hind : ∀ y : ℝ, {s : ℝ | s < K y}.indicator (fun _ => (1 : ℝ≥0∞)) s * g (x - y) =
            (A s).indicator (fun y => g (x - y)) y := by
          intro y
          by_cases hy : s < K y
          · have : y ∈ A s := hy
            simp [Set.indicator, hy, this]
          · have : y ∉ A s := hy
            simp [Set.indicator, hy, this]
        simp_rw [hind]
        rw [lintegral_indicator (hAm s)]
        exact lintegral_symm_set_le (hsymm s) (hAfin s hs0) hg x
    _ = (∫⁻ s in Ioi (0 : ℝ), volume (A s)) * hlMax g x := by
        refine lintegral_mul_const'' _ ?_
        have hanti : Antitone fun s : ℝ => volume (A s) := fun s s' hss' =>
          measure_mono (fun y hy => lt_of_le_of_lt hss' hy)
        exact hanti.measurable.aemeasurable
    _ = (∫⁻ y, ENNReal.ofReal (K y)) * hlMax g x := by
        rw [lintegral_eq_lintegral_meas_lt volume (Filter.Eventually.of_forall hnn)
          hKm.aemeasurable]

end

end FracLap
