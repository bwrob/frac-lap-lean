/-
Copyright (c) 2026 Alejandro Soto Franco, Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco, Bartosz Wróblewski
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Topology.Compactness.Compact

/-!
# FracLap.Core.LpExtension

Measure-theoretic `Lp` zero-extension isometry and smooth compact cutoff existence,
onboarded from Alejandro Soto Franco's `alejandro-soto-franco/EllipticPDE`
(`EllipticPdes.Analysis.LpExtendByZero` and `EllipticPdes.Analysis.SmoothCutoff`)
and specialized to the half-line `(0, ∞)` and Constantin–Vicol radial cutoffs:
- `memLp_indicator_extend` and `lpExtendByZero`: extending a class in
  `Lp ℝ p (μ.restrict s)` by zero outside a measurable set `s` is a linear isometry
  `Lp ℝ p (μ.restrict s) →ₗᵢ[ℝ] Lp ℝ p μ`.
- `coeFn_lpExtendByZero` and `lpExtendByZero_ae_eq_zero`: the zero-extended `Lp` class
  agrees almost everywhere with `s.indicator f` and vanishes almost everywhere off `s`.
- `halfLineL2ExtendByZero`: the canonical linear isometry
  `Lp ℝ 2 (volume.restrict (Set.Ioi (0 : ℝ))) →ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ)`
  embedding `L²(0, ∞)` into `L²_0(ℝ) ⊂ L²(ℝ)` in Section 5.3.
- `exists_contDiff_one_on_compact`: existence of a smooth cutoff `χ ∈ C_c^∞(E)` taking values
  in `[0, 1]`, equal to `1` on a compact set `K`, and compactly supported inside an open
  neighborhood `U ⊇ K` (used to construct the smooth cutoff `ϕ` in Appendix A).
-/

namespace FracLap

open Filter MeasureTheory Set
open scoped ENNReal

@[expose] public section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} {s : Set α}

/-- The indicator `s.indicator f` of an `Lp` class on the restricted measure `μ.restrict s`
belongs to `MemLp` for the ambient measure `μ`. -/
theorem memLp_indicator_extend (hs : MeasurableSet s) (f : Lp ℝ p (μ.restrict s)) :
    MemLp (s.indicator (f : α → ℝ)) p μ := by
  rw [memLp_iff, eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]
  exact Lp.memLp f

variable [Fact (1 ≤ p)]

variable (μ p s) in
/-- **Extension by Zero as an `Lp` Linear Isometry**:
Sends an equivalence class `f ∈ Lp ℝ p (μ.restrict s)` to its zero extension in `Lp ℝ p μ`,
preserving the `Lp` norm `‖lpExtendByZero μ p s hs f‖ = ‖f‖`. -/
noncomputable def lpExtendByZero (hs : MeasurableSet s) :
    Lp ℝ p (μ.restrict s) →ₗᵢ[ℝ] Lp ℝ p μ where
  toFun f := (memLp_indicator_extend hs f).toLp (s.indicator (f : α → ℝ))
  map_add' f g := by
    rw [Lp.ext_iff]
    have hr : ∀ᵐ x ∂(μ.restrict s), (⇑(f + g) : α → ℝ) x = (⇑f + ⇑g) x := Lp.coeFn_add f g
    have h5 : ∀ᵐ x ∂μ, x ∈ s → (⇑(f + g) : α → ℝ) x = (⇑f + ⇑g) x := (ae_restrict_iff' hs).mp hr
    filter_upwards [MemLp.coeFn_toLp (memLp_indicator_extend hs (f + g)),
      Lp.coeFn_add ((memLp_indicator_extend hs f).toLp (s.indicator (f : α → ℝ)))
        ((memLp_indicator_extend hs g).toLp (s.indicator (g : α → ℝ))),
      MemLp.coeFn_toLp (memLp_indicator_extend hs f),
      MemLp.coeFn_toLp (memLp_indicator_extend hs g), h5] with x h1 h2 h3 h4 h5x
    rw [h1, h2, Pi.add_apply, h3, h4]
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxs, Set.indicator_of_mem hxs, h5x hxs,
        Pi.add_apply]
    · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs,
        add_zero]
  map_smul' c f := by
    rw [Lp.ext_iff]
    have hr : ∀ᵐ x ∂(μ.restrict s), (⇑(c • f) : α → ℝ) x = (c • ⇑f) x := Lp.coeFn_smul c f
    have h4 : ∀ᵐ x ∂μ, x ∈ s → (⇑(c • f) : α → ℝ) x = (c • ⇑f) x := (ae_restrict_iff' hs).mp hr
    filter_upwards [MemLp.coeFn_toLp (memLp_indicator_extend hs (c • f)),
      Lp.coeFn_smul c ((memLp_indicator_extend hs f).toLp (s.indicator (f : α → ℝ))),
      MemLp.coeFn_toLp (memLp_indicator_extend hs f), h4] with x h1 h2 h3 h4x
    rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3]
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxs, h4x hxs, Pi.smul_apply]
    · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs, smul_zero]
  norm_map' f := by
    change ‖(memLp_indicator_extend hs f).toLp (s.indicator (f : α → ℝ))‖ = ‖f‖
    rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet, Lp.norm_def]

/-- The zero extension `lpExtendByZero μ p s hs f` is represented almost everywhere by
`s.indicator f`. -/
theorem coeFn_lpExtendByZero (hs : MeasurableSet s) (f : Lp ℝ p (μ.restrict s)) :
    (lpExtendByZero μ p s hs f : α → ℝ) =ᵐ[μ] s.indicator (f : α → ℝ) :=
  MemLp.coeFn_toLp (memLp_indicator_extend hs f)

/-- The zero extension `lpExtendByZero μ p s hs f` vanishes almost everywhere outside `s`. -/
theorem lpExtendByZero_ae_eq_zero (hs : MeasurableSet s) (f : Lp ℝ p (μ.restrict s)) :
    ∀ᵐ x ∂μ, x ∉ s → (lpExtendByZero μ p s hs f : α → ℝ) x = 0 := by
  filter_upwards [coeFn_lpExtendByZero hs f] with x hx hxs
  rw [hx, Set.indicator_of_notMem hxs]

/-- **Half-Line `L²(0, ∞) →ₗᵢ[ℝ] L²(ℝ)` Zero-Extension Isometry**:
Specializes `lpExtendByZero` to `s = Set.Ioi (0 : ℝ)` and `p = 2`, providing the canonical
isometric embedding of `L²(0, ∞)` into `L²_0(ℝ) ⊂ L²(ℝ)`. -/
noncomputable def halfLineL2ExtendByZero :
    Lp ℝ 2 ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) →ₗᵢ[ℝ]
      Lp ℝ 2 (volume : Measure ℝ) :=
  lpExtendByZero (volume : Measure ℝ) 2 (Set.Ioi (0 : ℝ)) measurableSet_Ioi

/-- Every zero-extended half-line `L²(0, ∞)` function vanishes almost everywhere on `(-∞, 0]`. -/
theorem halfLineL2ExtendByZero_ae_zero_of_nonpos
    (f : Lp ℝ 2 ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) :
    ∀ᵐ x : ℝ ∂volume, x ≤ 0 → (halfLineL2ExtendByZero f : ℝ → ℝ) x = 0 := by
  filter_upwards [lpExtendByZero_ae_eq_zero measurableSet_Ioi f] with x hx hx_le
  have hnot : x ∉ Set.Ioi (0 : ℝ) := not_lt.mpr hx_le
  exact hx hnot

/-- **Existence of a Smooth Compact Cutoff between a Compact Set and an Open Set**:
Given a compact set `K` inside an open set `U` of a finite-dimensional real normed space `E`,
there exists a smooth function `χ ∈ C^∞(E, ℝ)` with compact support inside `U`, values in
`[0, 1]`, and `χ(y) = 1` for all `y ∈ K`. -/
theorem exists_contDiff_one_on_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ y ∈ K, χ y = 1) ∧ ∀ y : E, χ y ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hf, hfI, hsupp, h1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (isOpen_interior (s := L)) hK.isClosed hKL
  have hts : tsupport f ⊆ L := by
    rw [tsupport, hsupp]
    exact closure_minimal interior_subset hLc.isClosed
  exact ⟨f, hf, hLc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hLU,
    fun y hy => (h1 y).1 hy, fun y => hfI ⟨y, rfl⟩⟩

/-- **Existence of a Smooth Exterior Cutoff for the Constantin–Vicol Decomposition**:
There exists a smooth function `ϕ : ℝ → ℝ` taking values in `[0, 1]` such that `ϕ(x) = 0` for
`x ∈ [-1, 1]` and `ϕ(x) = 1` for `|x| ≥ 2`. -/
theorem exists_smooth_exterior_cutoff :
    ∃ ϕ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ϕ ∧
      (∀ x : ℝ, ϕ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x : ℝ, |x| ≤ 1 → ϕ x = 0) ∧
      (∀ x : ℝ, 2 ≤ |x| → ϕ x = 1) := by
  have hK : IsCompact (Icc (-1 : ℝ) 1) := isCompact_Icc
  have hU : IsOpen (Ioo (-2 : ℝ) 2) := isOpen_Ioo
  have hKU : Icc (-1 : ℝ) 1 ⊆ Ioo (-2 : ℝ) 2 := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨by linarith, by linarith⟩
  obtain ⟨χ, hχ_smooth, _, hχ_supp, hχ_one, hχ_range⟩ :=
    exists_contDiff_one_on_compact hK hU hKU
  refine ⟨fun x : ℝ => 1 - χ x, contDiff_const.sub hχ_smooth, ?_, ?_, ?_⟩
  · intro x
    have hx := hχ_range x
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  · intro x hx
    dsimp only
    have hx_mem : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx
    rw [hχ_one x hx_mem, sub_self]
  · intro x hx
    dsimp only
    have hnot_U : x ∉ Ioo (-2 : ℝ) 2 := by
      intro hmem
      have habs : |x| < 2 := abs_lt.mpr hmem
      linarith
    have hnot_tsupp : x ∉ tsupport χ := fun h => hnot_U (hχ_supp h)
    have hzero : χ x = 0 := image_eq_zero_of_notMem_tsupport hnot_tsupp
    rw [hzero, sub_zero]

end

end FracLap
