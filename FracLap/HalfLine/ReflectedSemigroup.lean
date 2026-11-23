/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.WholeLine.AnomalousDiffusion
public import FracLap.WholeLine.FourierSemigroup
public import FracLap.WholeLine.StableSemigroup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLap.HalfLine.ReflectedSemigroup

Reflected (spectral Dirichlet) fractional Laplacian `(-Δ̃)^(α / 2)` and its contraction
semigroup `S̃(t) = R S(t) E` on the half-line `(0, ∞)`:
- `fracHeatConv_isOdd_of_isOdd`: the whole-line fractional heat convolution `P_α(·, t) * f`
  preserves odd parity (`(S(t) f)(-x) = -(S(t) f)(x)`).
- `reflectedHeatKernel`: the reflected Dirichlet fractional heat kernel
  `P_α^D(x, y, t) = P_α(x - y, t) - P_α(x + y, t)`.
- `reflectedHeatKernel_bounds`: pointwise positivity and sub-Markov domination
  `0 ≤ P_α^D(x, y, t) ≤ P_α(x - y, t)` for all `x, y > 0` and `t > 0`.
- `reflectedContractionSemigroup`: isometric conjugation `S̃(t) = R ∘ S(t) ∘ E` via
  antisymmetric extension `E : L²(0, ∞) → L²_odd(ℝ)` and restriction
  `R : L²_odd(ℝ) → L²(0, ∞)` produces a contraction `C₀`-semigroup on the half-line.
- `L2IoiC`, `reflectL2`, `IsOddL2`, `oddExtL2`, `restIoiL2`, `halfLineOddConjugation`:
  concrete `L²(0, ∞; ℂ) ⇄ L²_odd(ℝ; ℂ)` isometric conjugation.
- `fourier_reflectL2`, `reflectL2_fourierMultiplier_of_even`: odd-invariance of even Fourier
  multipliers via `L²`-reflection commutation of the Fourier transform.
- `reflectedC0Semigroup`, `reflectedContractiveResolvent`, `reflectedFracLapSemigroup`,
  `reflectedFracLapResolvent`, `reflectedFracLapResolvent_generatedSemigroup_eq`:
  concrete half-line reflected `C₀`-contraction semigroup, contractive resolvent, and exact
  Hille–Yosida identification.
-/

namespace FracLap

open Complex Filter FourierTransform MeasureTheory Real Set Topology
open scoped ENNReal NNReal ComplexInnerProductSpace SchwartzMap Convolution

@[expose] public section

/-- **Odd Parity Invariance of the Whole-Line Fractional Heat Semigroup**:
Because `P_α(·, t)` is even, the whole-line fractional heat convolution `fracHeatConv K t`
maps odd functions to odd functions: `(T(t) f)(-x) = -(T(t) f)(x)`. -/
theorem fracHeatConv_isOdd_of_isOdd {α : ℝ} (K : FractionalHeatKernel α) {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : IsOddFunc f) :
    IsOddFunc (fracHeatConv K t f) := by
  intro x
  unfold fracHeatConv
  have h_sub :
      (∫ y : ℝ, K.P (-x - y) t * f y) = ∫ y : ℝ, K.P (-x - -y) t * f (-y) := by
    rw [← integral_neg_eq_self (fun y : ℝ => K.P (-x - y) t * f y) volume]
  rw [h_sub, ← integral_neg]
  congr 1
  ext y
  have h_even : K.P (-x - -y) t = K.P (x - y) t := by
    have h_arg : -x - -y = -(x - y) := by ring
    rw [h_arg, K.even_space (x - y) t ht]
  rw [h_even, hf y]
  ring

/-- The reflected Dirichlet fractional heat kernel on `(0, ∞) × (0, ∞)`:
`P_α^D(x, y, t) = P_α(x - y, t) - P_α(x + y, t)`. -/
noncomputable def reflectedHeatKernel {α : ℝ} (K : FractionalHeatKernel α)
    (x y t : ℝ) : ℝ :=
  K.P (x - y) t - K.P (x + y) t

/-- **Positivity and Sub-Markov Domination of the Reflected Fractional Heat Kernel**:
For all `x, y > 0` and `t > 0`, `0 ≤ P_α^D(x, y, t) ≤ P_α(x - y, t)`. -/
theorem reflectedHeatKernel_bounds {α : ℝ} (K : FractionalHeatKernel α)
    {x y t : ℝ} (hx : 0 < x) (hy : 0 < y) (ht : 0 < t) :
    0 ≤ reflectedHeatKernel K x y t ∧ reflectedHeatKernel K x y t ≤ K.P (x - y) t := by
  unfold reflectedHeatKernel
  have h_abs_le : |x - y| ≤ |x + y| := by
    have hsum_pos : 0 < x + y := add_pos hx hy
    rw [abs_of_pos hsum_pos, abs_le]
    constructor <;> linarith
  have h_mono : K.P (x + y) t ≤ K.P (x - y) t :=
    K.radial_antitone (x - y) (x + y) t ht h_abs_le
  have h_nonneg : 0 ≤ K.P (x + y) t := K.nonneg (x + y) t ht
  constructor <;> linarith

/-- **Reflected Half-Line Contraction Semigroup Conjugation (`S̃(t) = R ∘ S(t) ∘ E`)**:
Given a whole-line contraction `C₀`-semigroup `S` on `E` and an `OddSubspaceConjugation`
between `E` and the half-line space `H` such that `S.T t` leaves the odd subspace invariant,
the conjugated family `S̃(t) u = R (S(t) (E u))` forms a contraction `C₀`-semigroup on `H`. -/
noncomputable def reflectedContractionSemigroup {E H : Type*}
    (S : ContractionSemigroup E) (normH : H → ℝ) (hnormH : ∀ u : H, 0 ≤ normH u)
    (C : OddSubspaceConjugation E H S.normE normH)
    (h_inv : ∀ t : ℝ, 0 ≤ t → ∀ f : E, C.IsOdd f → C.IsOdd (S.T t f)) :
    ContractionSemigroup H where
  T t u := C.restOp (S.T t (C.extOp u))
  normE := normH
  normE_nonneg := hnormH
  map_zero_time u := by
    rw [S.map_zero_time (C.extOp u), C.restOp_extOp u]
  map_add_time s t hs ht u := by
    have h_odd : C.IsOdd (S.T t (C.extOp u)) :=
      h_inv t ht (C.extOp u) (C.extOp_isOdd u)
    rw [C.extOp_restOp_of_isOdd (S.T t (C.extOp u)) h_odd]
    rw [S.map_add_time s t hs ht (C.extOp u)]
  contractive t ht u := by
    have h_odd : C.IsOdd (S.T t (C.extOp u)) :=
      h_inv t ht (C.extOp u) (C.extOp_isOdd u)
    have h_rest : sqrt 2 * normH (C.restOp (S.T t (C.extOp u))) =
        S.normE (S.T t (C.extOp u)) :=
      C.norm_restOp_of_isOdd (S.T t (C.extOp u)) h_odd
    have h_cont : S.normE (S.T t (C.extOp u)) ≤ S.normE (C.extOp u) :=
      S.contractive t ht (C.extOp u)
    have h_ext : S.normE (C.extOp u) = sqrt 2 * normH u := C.norm_extOp u
    have h_sqrt2_pos : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
    have h_ineq : sqrt 2 * normH (C.restOp (S.T t (C.extOp u))) ≤ sqrt 2 * normH u := by
      linarith
    exact le_of_mul_le_mul_left h_ineq h_sqrt2_pos

/-! ### 1. Concrete `L²(0, ∞; ℂ)` space and whole-line reflection isometry -/

/-- Concrete half-line complex Hilbert space `L²((0, ∞); ℂ)` with Lebesgue measure. -/
noncomputable abbrev L2IoiC := Lp (α := ℝ) ℂ 2 ((volume : Measure ℝ).restrict (Ioi (0 : ℝ)))

/-- Reflection isometry `f ↦ (x ↦ f(-x))` on `L²(ℝ; ℂ)` over `ℝ`. -/
noncomputable def reflectL2 : L2C →ₗᵢ[ℝ] L2C :=
  Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := ℂ) (p := 2)
    (μ := (volume : Measure ℝ)) (μb := (volume : Measure ℝ))
    Neg.neg (Measure.measurePreserving_neg (volume : Measure ℝ))

/-- Pointwise a.e. characterization of `reflectL2 f`. -/
theorem coeFn_reflectL2 (f : L2C) :
    (reflectL2 f : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => (f : ℝ → ℂ) (-x) :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg (volume : Measure ℝ))

/-- Reflection on `L²(ℝ; ℂ)` is an involution: `reflectL2 (reflectL2 f) = f`. -/
theorem reflectL2_reflectL2 (f : L2C) : reflectL2 (reflectL2 f) = f := by
  rw [Lp.ext_iff]
  have h1 := coeFn_reflectL2 (reflectL2 f)
  have h2 :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      (coeFn_reflectL2 f)
  filter_upwards [h1, h2] with x hx1 hx2
  change (reflectL2 f : ℝ → ℂ) (-x) = (f : ℝ → ℂ) (- -x) at hx2
  rw [hx1, hx2, neg_neg]

/-- Oddness predicate on `L²(ℝ; ℂ)`: `reflectL2 f = -f`. -/
def IsOddL2 (f : L2C) : Prop :=
  reflectL2 f = -f

/-- Characterization of `IsOddL2` in terms of pointwise a.e. antisymmetry. -/
theorem isOddL2_iff_ae (f : L2C) :
    IsOddL2 f ↔ ∀ᵐ x : ℝ ∂volume, (f : ℝ → ℂ) (-x) = -(f : ℝ → ℂ) x := by
  rw [IsOddL2, Lp.ext_iff]
  constructor
  · intro h
    filter_upwards [h, coeFn_reflectL2 f, Lp.coeFn_neg f] with x hx href hneg
    have h1 : (reflectL2 f : ℝ → ℂ) x = (f : ℝ → ℂ) (-x) := href
    have h2 : ((-f : L2C) : ℝ → ℂ) x = -(f : ℝ → ℂ) x := hneg
    rw [← h1, hx, h2]
  · intro h
    filter_upwards [h, coeFn_reflectL2 f, Lp.coeFn_neg f] with x hx href hneg
    have h1 : (reflectL2 f : ℝ → ℂ) x = (f : ℝ → ℂ) (-x) := href
    have h2 : ((-f : L2C) : ℝ → ℂ) x = -(f : ℝ → ℂ) x := hneg
    rw [h1, h2, hx]

/-! ### 2. Complex zero-extension, odd extension `oddExtL2`, and restriction `restIoiL2` -/

/-- Extending `u ∈ L²(0, ∞; ℂ)` by zero outside `(0, ∞)` produces an `L²(ℝ; ℂ)` function. -/
theorem memLp_indicator_IoiC (u : L2IoiC) :
    MemLp ((Ioi (0 : ℝ)).indicator (u : ℝ → ℂ)) 2 (volume : Measure ℝ) := by
  rw [memLp_iff, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioi.nullMeasurableSet]
  exact Lp.memLp u

/-- Zero-extension linear isometry `L²(0, ∞; ℂ) →ₗᵢ[ℝ] L²(ℝ; ℂ)`. -/
noncomputable def extendByZeroIoiC : L2IoiC →ₗᵢ[ℝ] L2C where
  toFun u := (memLp_indicator_IoiC u).toLp ((Ioi (0 : ℝ)).indicator (u : ℝ → ℂ))
  map_add' u v := by
    rw [Lp.ext_iff]
    have hr : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))),
        ((u + v : L2IoiC) : ℝ → ℂ) x = (u : ℝ → ℂ) x + (v : ℝ → ℂ) x :=
      Lp.coeFn_add u v
    have h5 : ∀ᵐ x : ℝ ∂volume,
        x ∈ Ioi (0 : ℝ) → ((u + v : L2IoiC) : ℝ → ℂ) x = (u : ℝ → ℂ) x + (v : ℝ → ℂ) x :=
      (ae_restrict_iff' measurableSet_Ioi).mp hr
    filter_upwards [MemLp.coeFn_toLp (memLp_indicator_IoiC (u + v)),
      Lp.coeFn_add
        ((memLp_indicator_IoiC u).toLp ((Ioi (0 : ℝ)).indicator (u : ℝ → ℂ)))
        ((memLp_indicator_IoiC v).toLp ((Ioi (0 : ℝ)).indicator (v : ℝ → ℂ))),
      MemLp.coeFn_toLp (memLp_indicator_IoiC u),
      MemLp.coeFn_toLp (memLp_indicator_IoiC v), h5] with x h1 h2 h3 h4 h5x
    rw [h1, h2, Pi.add_apply, h3, h4]
    by_cases hxs : x ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxs, Set.indicator_of_mem hxs, h5x hxs]
    · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs,
        Set.indicator_of_notMem hxs, add_zero]
  map_smul' c u := by
    rw [Lp.ext_iff]
    have hr : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))),
        ((c • u : L2IoiC) : ℝ → ℂ) x = c • (u : ℝ → ℂ) x :=
      Lp.coeFn_smul c u
    have h4 : ∀ᵐ x : ℝ ∂volume,
        x ∈ Ioi (0 : ℝ) → ((c • u : L2IoiC) : ℝ → ℂ) x = c • (u : ℝ → ℂ) x :=
      (ae_restrict_iff' measurableSet_Ioi).mp hr
    filter_upwards [MemLp.coeFn_toLp (memLp_indicator_IoiC (c • u)),
      Lp.coeFn_smul c
        ((memLp_indicator_IoiC u).toLp ((Ioi (0 : ℝ)).indicator (u : ℝ → ℂ))),
      MemLp.coeFn_toLp (memLp_indicator_IoiC u), h4] with x h1 h2 h3 h4x
    rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3]
    by_cases hxs : x ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxs, h4x hxs]
    · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs, smul_zero]
  norm_map' u := by
    change ‖(memLp_indicator_IoiC u).toLp ((Ioi (0 : ℝ)).indicator (u : ℝ → ℂ))‖ = ‖u‖
    rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioi.nullMeasurableSet,
      Lp.norm_def]

/-- Pointwise a.e. characterization of `extendByZeroIoiC u`. -/
theorem coeFn_extendByZeroIoiC (u : L2IoiC) :
    (extendByZeroIoiC u : ℝ → ℂ) =ᵐ[volume] (Ioi (0 : ℝ)).indicator (u : ℝ → ℂ) :=
  MemLp.coeFn_toLp (memLp_indicator_IoiC u)

/-- Antisymmetric (odd) extension operator `E : L²(0, ∞; ℂ) →L[ℝ] L²(ℝ; ℂ)`. -/
noncomputable def oddExtL2 : L2IoiC →L[ℝ] L2C :=
  extendByZeroIoiC.toContinuousLinearMap -
    reflectL2.toContinuousLinearMap.comp extendByZeroIoiC.toContinuousLinearMap

/-- Unfolding `oddExtL2 u`. -/
theorem oddExtL2_apply (u : L2IoiC) :
    oddExtL2 u = extendByZeroIoiC u - reflectL2 (extendByZeroIoiC u) :=
  rfl

/-- Every odd extension `oddExtL2 u` lies in the odd subspace `IsOddL2`. -/
theorem oddExtL2_isOddL2 (u : L2IoiC) : IsOddL2 (oddExtL2 u) := by
  unfold IsOddL2
  rw [oddExtL2_apply, reflectL2.map_sub, reflectL2_reflectL2]
  abel

/-- Disjointness of positive and negative half-line supports makes `extendByZeroIoiC u` orthogonal
to its reflection `reflectL2 (extendByZeroIoiC u)` in `L²(ℝ; ℂ)`. -/
theorem inner_extendByZeroIoiC_reflectL2 (u : L2IoiC) :
    ⟪extendByZeroIoiC u, reflectL2 (extendByZeroIoiC u)⟫ = 0 := by
  rw [L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  have hrefl :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      (coeFn_extendByZeroIoiC u)
  filter_upwards [coeFn_extendByZeroIoiC u, coeFn_reflectL2 (extendByZeroIoiC u), hrefl]
    with x h1 h2 h3
  change ⟪(extendByZeroIoiC u : ℝ → ℂ) x, (reflectL2 (extendByZeroIoiC u) : ℝ → ℂ) x⟫ = (0 : ℂ)
  have h1' : (extendByZeroIoiC u : ℝ → ℂ) x = (Ioi (0 : ℝ)).indicator (u : ℝ → ℂ) x := h1
  have h2' : (reflectL2 (extendByZeroIoiC u) : ℝ → ℂ) x = (extendByZeroIoiC u : ℝ → ℂ) (-x) := h2
  have h3' : (extendByZeroIoiC u : ℝ → ℂ) (-x) = (Ioi (0 : ℝ)).indicator (u : ℝ → ℂ) (-x) := h3
  rw [h2', h3', h1']
  by_cases hx : 0 < x
  · have hnot : -x ∉ Ioi (0 : ℝ) := not_lt.mpr (by linarith)
    rw [Set.indicator_of_notMem hnot, inner_zero_right]
  · have hnot : x ∉ Ioi (0 : ℝ) := hx
    rw [Set.indicator_of_notMem hnot, inner_zero_left]

/-- Scaled isometry of odd extension: `‖oddExtL2 u‖ = √2 * ‖u‖`. -/
theorem norm_oddExtL2 (u : L2IoiC) : ‖oddExtL2 u‖ = sqrt 2 * ‖u‖ := by
  have hzero : ⟪extendByZeroIoiC u, reflectL2 (extendByZeroIoiC u)⟫ = 0 :=
    inner_extendByZeroIoiC_reflectL2 u
  have hzero' : ⟪reflectL2 (extendByZeroIoiC u), extendByZeroIoiC u⟫ = 0 := by
    rw [← inner_conj_symm, hzero, map_zero]
  have hsq :
      ‖oddExtL2 u‖ ^ 2 = (sqrt 2 * ‖u‖) ^ 2 := by
    rw [oddExtL2_apply, norm_sq_eq_re_inner (𝕜 := ℂ), inner_sub_sub_self, hzero, hzero',
      sub_zero, sub_zero, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
      reflectL2.norm_map, extendByZeroIoiC.norm_map]
    simp only [Complex.coe_algebraMap, map_add, RCLike.re_to_complex,
      ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- Restriction operator `R : L²(ℝ; ℂ) →L[ℝ] L²(0, ∞; ℂ)`. -/
noncomputable def restIoiL2 : L2C →L[ℝ] L2IoiC :=
  LinearMap.mkContinuous
    { toFun := fun f => ((Lp.memLp f).restrict (Ioi (0 : ℝ))).toLp (f : ℝ → ℂ)
      map_add' := fun f g => by
        rw [Lp.ext_iff]
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).restrict (Ioi (0 : ℝ))),
          Lp.coeFn_add
            (((Lp.memLp f).restrict (Ioi (0 : ℝ))).toLp (f : ℝ → ℂ))
            (((Lp.memLp g).restrict (Ioi (0 : ℝ))).toLp (g : ℝ → ℂ)),
          MemLp.coeFn_toLp ((Lp.memLp f).restrict (Ioi (0 : ℝ))),
          MemLp.coeFn_toLp ((Lp.memLp g).restrict (Ioi (0 : ℝ))),
          ae_restrict_of_ae (Lp.coeFn_add f g)] with x h1 h2 h3 h4 hadd
        rw [h1, h2, Pi.add_apply, h3, h4, hadd, Pi.add_apply]
      map_smul' := fun c f => by
        rw [Lp.ext_iff]
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).restrict (Ioi (0 : ℝ))),
          Lp.coeFn_smul c (((Lp.memLp f).restrict (Ioi (0 : ℝ))).toLp (f : ℝ → ℂ)),
          MemLp.coeFn_toLp ((Lp.memLp f).restrict (Ioi (0 : ℝ))),
          ae_restrict_of_ae (Lp.coeFn_smul c f)] with x h1 h2 h3 hsmul
        rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3, hsmul, Pi.smul_apply] }
    1
    (fun f => by
      change ‖((Lp.memLp f).restrict (Ioi (0 : ℝ))).toLp (f : ℝ → ℂ)‖ ≤ 1 * ‖f‖
      rw [one_mul, Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
        (eLpNorm_restrict_le _ 2 volume (Ioi (0 : ℝ))))

/-- Pointwise a.e. characterization of `restIoiL2 f` on `(0, ∞)`. -/
theorem coeFn_restIoiL2 (f : L2C) :
    (restIoiL2 f : ℝ → ℂ) =ᵐ[(volume : Measure ℝ).restrict (Ioi (0 : ℝ))] (f : ℝ → ℂ) :=
  MemLp.coeFn_toLp ((Lp.memLp f).restrict (Ioi (0 : ℝ)))

/-- Restricting the odd extension recovers the original half-line function: `R (E u) = u`. -/
theorem restIoiL2_oddExtL2 (u : L2IoiC) : restIoiL2 (oddExtL2 u) = u := by
  rw [Lp.ext_iff]
  have hrefl :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      (coeFn_extendByZeroIoiC u)
  filter_upwards [coeFn_restIoiL2 (oddExtL2 u),
    ae_restrict_of_ae (Lp.coeFn_sub (extendByZeroIoiC u) (reflectL2 (extendByZeroIoiC u))),
    ae_restrict_of_ae (coeFn_extendByZeroIoiC u),
    ae_restrict_of_ae (coeFn_reflectL2 (extendByZeroIoiC u)),
    ae_restrict_of_ae hrefl,
    ae_restrict_mem measurableSet_Ioi] with x hrest hsub hext href hextr hx
  have h1 : (restIoiL2 (oddExtL2 u) : ℝ → ℂ) x = (oddExtL2 u : ℝ → ℂ) x := hrest
  have h2 : (oddExtL2 u : ℝ → ℂ) x =
      (extendByZeroIoiC u : ℝ → ℂ) x - (reflectL2 (extendByZeroIoiC u) : ℝ → ℂ) x := hsub
  have h3 : (extendByZeroIoiC u : ℝ → ℂ) x = (u : ℝ → ℂ) x := by
    simpa only [Set.indicator_of_mem hx] using hext
  have hnot : -x ∉ Ioi (0 : ℝ) := not_lt.mpr (by linarith [hx.out])
  have h4 : (reflectL2 (extendByZeroIoiC u) : ℝ → ℂ) x = 0 := by
    have h4a : (reflectL2 (extendByZeroIoiC u) : ℝ → ℂ) x = (extendByZeroIoiC u : ℝ → ℂ) (-x) :=
      href
    have h4b : (extendByZeroIoiC u : ℝ → ℂ) (-x) = (Ioi (0 : ℝ)).indicator (u : ℝ → ℂ) (-x) :=
      hextr
    rw [h4a, h4b, Set.indicator_of_notMem hnot]
  rw [h1, h2, h3, h4, sub_zero]

/-- Extending the restriction of an odd function recovers it: `E (R f) = f` for `IsOddL2 f`. -/
theorem oddExtL2_restIoiL2_of_isOddL2 {f : L2C} (hf : IsOddL2 f) :
    oddExtL2 (restIoiL2 f) = f := by
  rw [Lp.ext_iff]
  have hrest :
      ∀ᵐ x : ℝ ∂volume, x ∈ Ioi (0 : ℝ) → (restIoiL2 f : ℝ → ℂ) x = (f : ℝ → ℂ) x :=
    (ae_restrict_iff' measurableSet_Ioi).mp (coeFn_restIoiL2 f)
  have hrest_neg :
      ∀ᵐ x : ℝ ∂volume, -x ∈ Ioi (0 : ℝ) → (restIoiL2 f : ℝ → ℂ) (-x) = (f : ℝ → ℂ) (-x) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hrest
  have hext_neg :
      ∀ᵐ x : ℝ ∂volume, (extendByZeroIoiC (restIoiL2 f) : ℝ → ℂ) (-x) =
        (Ioi (0 : ℝ)).indicator (restIoiL2 f : ℝ → ℂ) (-x) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      (coeFn_extendByZeroIoiC (restIoiL2 f))
  have hne0 : ∀ᵐ x : ℝ ∂volume, x ≠ (0 : ℝ) := by
    rw [ae_iff]
    have hset : {x : ℝ | ¬ x ≠ 0} = ({0} : Set ℝ) := by
      ext x
      simp
    rw [hset, measure_singleton]
  filter_upwards [Lp.coeFn_sub (extendByZeroIoiC (restIoiL2 f))
      (reflectL2 (extendByZeroIoiC (restIoiL2 f))),
    coeFn_extendByZeroIoiC (restIoiL2 f),
    coeFn_reflectL2 (extendByZeroIoiC (restIoiL2 f)),
    hext_neg, hrest, hrest_neg, (isOddL2_iff_ae f).mp hf, hne0]
    with x hsub hext href hextn hr hrn hodd hx0
  have hsub' :
      (oddExtL2 (restIoiL2 f) : ℝ → ℂ) x =
        (extendByZeroIoiC (restIoiL2 f) : ℝ → ℂ) x -
          (reflectL2 (extendByZeroIoiC (restIoiL2 f)) : ℝ → ℂ) x := hsub
  have href' :
      (reflectL2 (extendByZeroIoiC (restIoiL2 f)) : ℝ → ℂ) x =
        (Ioi (0 : ℝ)).indicator (restIoiL2 f : ℝ → ℂ) (-x) := by
    have ha : (reflectL2 (extendByZeroIoiC (restIoiL2 f)) : ℝ → ℂ) x =
        (extendByZeroIoiC (restIoiL2 f) : ℝ → ℂ) (-x) := href
    exact ha.trans hextn
  rw [hsub', hext, href']
  rcases lt_trichotomy x 0 with hneg | rfl | hpos
  · have hx_not : x ∉ Ioi (0 : ℝ) := not_lt.mpr hneg.le
    have hnx_mem : -x ∈ Ioi (0 : ℝ) := by exact neg_pos.mpr hneg
    rw [Set.indicator_of_notMem hx_not, Set.indicator_of_mem hnx_mem, hrn hnx_mem, hodd]
    ring
  · exact (hx0 rfl).elim
  · have hx_mem : x ∈ Ioi (0 : ℝ) := hpos
    have hnx_not : -x ∉ Ioi (0 : ℝ) := not_lt.mpr (by linarith)
    rw [Set.indicator_of_mem hx_mem, Set.indicator_of_notMem hnx_not, hr hx_mem, sub_zero]

/-- Scaled isometry of restriction on odd functions: `√2 * ‖R f‖ = ‖f‖`. -/
theorem norm_restIoiL2_of_isOddL2 {f : L2C} (hf : IsOddL2 f) :
    sqrt 2 * ‖restIoiL2 f‖ = ‖f‖ := by
  rw [← norm_oddExtL2 (restIoiL2 f), oddExtL2_restIoiL2_of_isOddL2 hf]

/-- **Concrete Isometric Odd-Subspace Conjugation `L²(0, ∞; ℂ) ⇄ L²_odd(ℝ; ℂ)`**:
realizes `OddSubspaceConjugation` concretely via `oddExtL2` and `restIoiL2`. -/
noncomputable def halfLineOddConjugation :
    OddSubspaceConjugation L2C L2IoiC (fun f : L2C => ‖f‖) (fun u : L2IoiC => ‖u‖) where
  IsOdd := IsOddL2
  extOp := oddExtL2
  restOp := restIoiL2
  extOp_isOdd := oddExtL2_isOddL2
  restOp_extOp := restIoiL2_oddExtL2
  extOp_restOp_of_isOdd _ hf := oddExtL2_restIoiL2_of_isOddL2 hf
  norm_extOp := norm_oddExtL2
  norm_restOp_of_isOdd _ hf := norm_restIoiL2_of_isOddL2 hf

/-! ### 3. Reflection commutation of Fourier transforms and even multipliers -/

/-- **Fourier Reflection Commutation on `L²(ℝ; ℂ)`**:
`𝓕 (reflectL2 f) = reflectL2 (𝓕 f)` for every `f ∈ L²(ℝ; ℂ)`. -/
theorem fourier_reflectL2 (f : L2C) : 𝓕 (reflectL2 f) = reflectL2 (𝓕 f) := by
  let p : L2C → Prop := fun g => 𝓕 (reflectL2 g) = reflectL2 (𝓕 g)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact ((Lp.fourierTransformₗᵢ ℝ ℂ).continuous).comp reflectL2.continuous
    · exact reflectL2.continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous
  · intro φ
    dsimp only [p]
    let φneg : 𝓢(ℝ, ℂ) :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) φ
    have htoLp_eq : (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) φ = φ.toLp 2 := rfl
    have href_schwartz : reflectL2 (φ.toLp 2) = φneg.toLp 2 := by
      rw [Lp.ext_iff]
      filter_upwards [coeFn_reflectL2 (φ.toLp 2),
        (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
          (φ.coeFn_toLp 2 volume),
        φneg.coeFn_toLp 2 volume] with x href hφn hφneg
      have h1 : (reflectL2 (φ.toLp 2) : ℝ → ℂ) x = (φ.toLp 2 : ℝ → ℂ) (-x) := href
      have h2 : (φ.toLp 2 : ℝ → ℂ) (-x) = φ (-x) := hφn
      have h3 : (φneg.toLp 2 : ℝ → ℂ) x = φneg x := hφneg
      have h4 : φneg x = φ (-x) := rfl
      rw [h1, h2, h3, h4]
    have hfour_schwartz : 𝓕 φneg =
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) (𝓕 φ) := by
      ext ξ
      simp only [SchwartzMap.fourier_coe, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        Function.comp_apply, ContinuousLinearEquiv.neg_apply]
      change (∫ y : ℝ, 𝐞 (-inner ℝ y ξ) • φ (-y)) = ∫ y : ℝ, 𝐞 (-inner ℝ y (-ξ)) • φ y
      rw [← integral_neg_eq_self (fun y : ℝ => 𝐞 (-inner ℝ y (-ξ)) • φ y) volume]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only
      rw [inner_neg_neg]
    rw [htoLp_eq, href_schwartz, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq,
      hfour_schwartz]
    symm
    rw [Lp.ext_iff]
    filter_upwards [coeFn_reflectL2 ((𝓕 φ).toLp 2),
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
        ((𝓕 φ).coeFn_toLp 2 volume),
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (ContinuousLinearEquiv.neg ℝ) (𝓕 φ)).coeFn_toLp 2 volume]
      with ξ href h1 h2
    have h1' : (reflectL2 ((𝓕 φ).toLp 2) : ℝ → ℂ) ξ = ((𝓕 φ).toLp 2 : ℝ → ℂ) (-ξ) := href
    have h2' : ((𝓕 φ).toLp 2 : ℝ → ℂ) (-ξ) = (𝓕 φ) (-ξ) := h1
    have h3' :
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (ContinuousLinearEquiv.neg ℝ) (𝓕 φ)).toLp 2 : ℝ → ℂ) ξ = (𝓕 φ) (-ξ) := h2
    rw [h1', h2', h3']

/-- **Inverse Fourier Reflection Commutation on `L²(ℝ; ℂ)`**:
`𝓕⁻ (reflectL2 f) = reflectL2 (𝓕⁻ f)` for every `f ∈ L²(ℝ; ℂ)`. -/
theorem fourierInv_reflectL2 (f : L2C) : 𝓕⁻ (reflectL2 f) = reflectL2 (𝓕⁻ f) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change 𝓕 (𝓕⁻ (reflectL2 f)) = 𝓕 (reflectL2 (𝓕⁻ f))
  rw [fourier_fourierInv_eq, fourier_reflectL2, fourier_fourierInv_eq]

/-- An even `L^∞` Fourier multiplier commutes with `reflectL2` on `L²(ℝ; ℂ)`. -/
theorem reflectL2_fourierMultiplier_of_even {m : Lp (α := ℝ) ℂ ∞ volume}
    (hm_even : ∀ᵐ ξ : ℝ ∂volume, (m : ℝ → ℂ) (-ξ) = (m : ℝ → ℂ) ξ) (f : L2C) :
    reflectL2 (fourierMultiplier m f) = fourierMultiplier m (reflectL2 f) := by
  rw [fourierMultiplier_apply, fourierMultiplier_apply, ← fourierInv_reflectL2,
    fourier_reflectL2]
  congr 1
  rw [Lp.ext_iff]
  have hm_refl :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hm_even
  filter_upwards [coeFn_reflectL2 (m • 𝓕 f : L2C),
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      (Lp.coeFn_lpSMul (r := 2) m (𝓕 f)),
    Lp.coeFn_lpSMul (r := 2) m (reflectL2 (𝓕 f)),
    coeFn_reflectL2 (𝓕 f), hm_even, hm_refl] with ξ href hsm1 hsm2 hrefF hme hmr
  have href' : (reflectL2 (m • 𝓕 f : L2C) : ℝ → ℂ) ξ = ((m • 𝓕 f : L2C) : ℝ → ℂ) (-ξ) := href
  have hsm1' : ((m • 𝓕 f : L2C) : ℝ → ℂ) (-ξ) = (m : ℝ → ℂ) (-ξ) * ((𝓕 f : L2C) : ℝ → ℂ) (-ξ) :=
    hsm1
  have hsm2' :
      ((m • reflectL2 (𝓕 f) : L2C) : ℝ → ℂ) ξ =
        (m : ℝ → ℂ) ξ * (reflectL2 (𝓕 f) : ℝ → ℂ) ξ := hsm2
  have hrefF' : (reflectL2 (𝓕 f) : ℝ → ℂ) ξ = ((𝓕 f : L2C) : ℝ → ℂ) (-ξ) := hrefF
  rw [href', hsm1', hsm2', hrefF', hme]

/-- An even `L^∞` Fourier multiplier leaves `IsOddL2` invariant. -/
theorem fourierMultiplier_isOddL2_of_even {m : Lp (α := ℝ) ℂ ∞ volume}
    (hm_even : ∀ᵐ ξ : ℝ ∂volume, (m : ℝ → ℂ) (-ξ) = (m : ℝ → ℂ) ξ)
    {f : L2C} (hf : IsOddL2 f) :
    IsOddL2 (fourierMultiplier m f) := by
  unfold IsOddL2 at hf ⊢
  rw [reflectL2_fourierMultiplier_of_even hm_even f, hf, ContinuousLinearMap.map_neg]

/-- For an even measurable nonnegative symbol `ψ`, `fourierMultiplierSemigroup` commutes with
reflection `reflectL2`. -/
theorem fourierMultiplierSemigroup_reflectL2 (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ)
    (hψ_nonneg : ∀ ξ, 0 ≤ ψ ξ) (hψ_even : ∀ ξ, ψ (-ξ) = ψ ξ) (t : ℝ≥0) (f : L2C) :
    reflectL2 (fourierMultiplierSemigroup ψ hψ_meas hψ_nonneg t f) =
      fourierMultiplierSemigroup ψ hψ_meas hψ_nonneg t (reflectL2 f) := by
  refine reflectL2_fourierMultiplier_of_even ?_ f
  have h1 := coeFn_toLpTop (expSymbol_aestronglyMeasurable ψ hψ_meas t) zero_le_one
    (norm_expSymbol_le_one ψ hψ_nonneg t.coe_nonneg)
  have h2 := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h1
  filter_upwards [h1, h2] with ξ h1x h2x
  have h1' :
      (expMultiplierSymbol ψ hψ_meas hψ_nonneg t : ℝ → ℂ) ξ =
        ((Real.exp (-(t : ℝ) * ψ ξ) : ℝ) : ℂ) := h1x
  have h2' :
      (expMultiplierSymbol ψ hψ_meas hψ_nonneg t : ℝ → ℂ) (-ξ) =
        ((Real.exp (-(t : ℝ) * ψ (-ξ)) : ℝ) : ℂ) := h2x
  change (expMultiplierSymbol ψ hψ_meas hψ_nonneg t : ℝ → ℂ) (-ξ) =
    (expMultiplierSymbol ψ hψ_meas hψ_nonneg t : ℝ → ℂ) ξ
  rw [h1', h2', hψ_even ξ]

/-- For an even measurable nonnegative symbol `ψ`, `fourierMultiplierSemigroup` leaves
`IsOddL2` invariant. -/
theorem fourierMultiplierSemigroup_isOddL2 (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ)
    (hψ_nonneg : ∀ ξ, 0 ≤ ψ ξ) (hψ_even : ∀ ξ, ψ (-ξ) = ψ ξ) (t : ℝ≥0)
    {f : L2C} (hf : IsOddL2 f) :
    IsOddL2 (fourierMultiplierSemigroup ψ hψ_meas hψ_nonneg t f) := by
  unfold IsOddL2 at hf ⊢
  rw [fourierMultiplierSemigroup_reflectL2 ψ hψ_meas hψ_nonneg hψ_even t f, hf,
    ContinuousLinearMap.map_neg]

/-- For an even measurable nonnegative symbol `ψ`, `fourierMultiplierResolvent` commutes with
reflection `reflectL2`. -/
theorem fourierMultiplierResolvent_reflectL2 (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ)
    (hψ_nonneg : ∀ ξ, 0 ≤ ψ ξ) (hψ_even : ∀ ξ, ψ (-ξ) = ψ ξ)
    (μ : PositiveShift) (f : L2C) :
    reflectL2 ((fourierMultiplierResolvent ψ hψ_meas hψ_nonneg).operator μ f) =
      (fourierMultiplierResolvent ψ hψ_meas hψ_nonneg).operator μ (reflectL2 f) := by
  refine reflectL2_fourierMultiplier_of_even ?_ f
  have h1 := coeFn_toLpTop (resSymbol_aestronglyMeasurable ψ hψ_meas μ) (inv_nonneg.mpr μ.2.le)
    (norm_resSymbol_le_inv ψ hψ_nonneg μ)
  have h2 := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h1
  filter_upwards [h1, h2] with ξ h1x h2x
  have h1' :
      (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ : ℝ → ℂ) ξ =
        ((((μ : ℝ) + ψ ξ)⁻¹ : ℝ) : ℂ) := h1x
  have h2' :
      (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ : ℝ → ℂ) (-ξ) =
        ((((μ : ℝ) + ψ (-ξ))⁻¹ : ℝ) : ℂ) := h2x
  change (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ : ℝ → ℂ) (-ξ) =
    (resMultiplierSymbol ψ hψ_meas hψ_nonneg μ : ℝ → ℂ) ξ
  rw [h1', h2', hψ_even ξ]

/-- Evenness of the fractional Laplacian Fourier symbol `|2 π ξ|^α`. -/
theorem fracLapSymbol_even (α ξ : ℝ) : fracLapSymbol α (-ξ) = fracLapSymbol α ξ := by
  unfold fracLapSymbol
  rw [mul_neg, abs_neg]

/-- The whole-line fractional heat semigroup `fracLapSemigroup α` preserves `IsOddL2`. -/
theorem fracLapSemigroup_isOddL2 (α : ℝ) (t : ℝ≥0) {f : L2C} (hf : IsOddL2 f) :
    IsOddL2 (fracLapSemigroup α t f) :=
  fourierMultiplierSemigroup_isOddL2 (fracLapSymbol α) (measurable_fracLapSymbol α)
    (fracLapSymbol_nonneg α) (fracLapSymbol_even α) t hf

/-- The whole-line fractional Laplacian resolvent `fracLapResolvent α` commutes with `reflectL2`. -/
theorem fracLapResolvent_reflectL2 (α : ℝ) (μ : PositiveShift) (f : L2C) :
    reflectL2 ((fracLapResolvent α).operator μ f) =
      (fracLapResolvent α).operator μ (reflectL2 f) :=
  fourierMultiplierResolvent_reflectL2 (fracLapSymbol α) (measurable_fracLapSymbol α)
    (fracLapSymbol_nonneg α) (fracLapSymbol_even α) μ f

/-! ### 4. Concrete reflected half-line `C₀`-semigroup, resolvent, and Hille–Yosida theorem -/

/-- **Concrete Reflected Half-Line `C₀`-Contraction Semigroup**:
conjugates an odd-invariant `StronglyContinuousContractionSemigroup L2C` via `oddExtL2` and
`restIoiL2` to produce a `StronglyContinuousContractionSemigroup L2IoiC`. -/
noncomputable def reflectedC0Semigroup (S : StronglyContinuousContractionSemigroup L2C)
    (h_inv : ∀ t : ℝ≥0, ∀ f : L2C, IsOddL2 f → IsOddL2 (S t f)) :
    StronglyContinuousContractionSemigroup L2IoiC where
  operator t := restIoiL2.comp ((S t).comp oddExtL2)
  operator_zero := by
    ext1 u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, S.zero_apply,
      restIoiL2_oddExtL2]
  operator_add s t := by
    ext1 u
    change restIoiL2 (S (s + t) (oddExtL2 u)) =
      restIoiL2 (S s (oddExtL2 (restIoiL2 (S t (oddExtL2 u)))))
    have h_odd : IsOddL2 (S t (oddExtL2 u)) := h_inv t (oddExtL2 u) (oddExtL2_isOddL2 u)
    rw [oddExtL2_restIoiL2_of_isOddL2 h_odd,
      ← ContinuousLinearMap.comp_apply (S s) (S t) (oddExtL2 u), ← S.operator_add]
  opNorm_le_one t := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
    rw [one_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    have h_odd : IsOddL2 (S t (oddExtL2 u)) := h_inv t (oddExtL2 u) (oddExtL2_isOddL2 u)
    have h_sqrt2_pos : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
    have h_ineq : sqrt 2 * ‖restIoiL2 (S t (oddExtL2 u))‖ ≤ sqrt 2 * ‖u‖ := by
      calc
        sqrt 2 * ‖restIoiL2 (S t (oddExtL2 u))‖ = ‖S t (oddExtL2 u)‖ :=
          norm_restIoiL2_of_isOddL2 h_odd
        _ ≤ ‖oddExtL2 u‖ := S.norm_apply_le t (oddExtL2 u)
        _ = sqrt 2 * ‖u‖ := norm_oddExtL2 u
    exact le_of_mul_le_mul_left h_ineq h_sqrt2_pos
  continuous_orbit u := by
    change Continuous fun t : ℝ≥0 => restIoiL2 (S t (oddExtL2 u))
    exact restIoiL2.continuous.comp (S.continuous_orbit (oddExtL2 u))

/-- Unfolding `(reflectedC0Semigroup S h_inv t u)`. -/
theorem reflectedC0Semigroup_apply (S : StronglyContinuousContractionSemigroup L2C)
    (h_inv : ∀ t : ℝ≥0, ∀ f : L2C, IsOddL2 f → IsOddL2 (S t f)) (t : ℝ≥0) (u : L2IoiC) :
    reflectedC0Semigroup S h_inv t u = restIoiL2 (S t (oddExtL2 u)) :=
  rfl

/-- Odd-part projection of a reflection-commuting contractive resolvent yields an
`L²(0, ∞; ℂ)` contractive resolvent. -/
noncomputable def reflectedContractiveResolvent (R : ContractiveResolvent L2C)
    (h_comm : ∀ μ : PositiveShift, ∀ f : L2C,
      reflectL2 (R.operator μ f) = R.operator μ (reflectL2 f)) :
    ContractiveResolvent L2IoiC where
  operator μ := restIoiL2.comp ((R.operator μ).comp oddExtL2)
  resolvent_identity α β := by
    ext1 u
    change restIoiL2 (R.operator α (oddExtL2 u)) - restIoiL2 (R.operator β (oddExtL2 u)) =
      ((β : ℝ) - (α : ℝ)) •
        restIoiL2 (R.operator α (oddExtL2 (restIoiL2 (R.operator β (oddExtL2 u)))))
    have h_odd : IsOddL2 (R.operator β (oddExtL2 u)) := by
      unfold IsOddL2
      rw [h_comm β (oddExtL2 u), oddExtL2_isOddL2 u, ContinuousLinearMap.map_neg]
    rw [oddExtL2_restIoiL2_of_isOddL2 h_odd, ← map_sub]
    have hres := DFunLike.congr_fun (R.resolvent_identity α β) (oddExtL2 u)
    simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply] at hres
    rw [hres, map_smul]
  opNorm_le_inv α := by
    refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr α.2.le) fun u => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    have h_odd : IsOddL2 (R.operator α (oddExtL2 u)) := by
      unfold IsOddL2
      rw [h_comm α (oddExtL2 u), oddExtL2_isOddL2 u, ContinuousLinearMap.map_neg]
    have h_sqrt2_pos : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
    have h_ineq : sqrt 2 * ‖restIoiL2 (R.operator α (oddExtL2 u))‖ ≤
        sqrt 2 * ((α : ℝ)⁻¹ * ‖u‖) := by
      calc
        sqrt 2 * ‖restIoiL2 (R.operator α (oddExtL2 u))‖ = ‖R.operator α (oddExtL2 u)‖ :=
          norm_restIoiL2_of_isOddL2 h_odd
        _ ≤ ‖R.operator α‖ * ‖oddExtL2 u‖ := (R.operator α).le_opNorm _
        _ ≤ (α : ℝ)⁻¹ * (sqrt 2 * ‖u‖) := by
          rw [norm_oddExtL2 u]
          exact mul_le_mul_of_nonneg_right (R.opNorm_le_inv α) (by positivity)
        _ = sqrt 2 * ((α : ℝ)⁻¹ * ‖u‖) := by ring
    exact le_of_mul_le_mul_left h_ineq h_sqrt2_pos
  denseRange α := by
    rw [Metric.denseRange_iff]
    intro g ε hε
    have hsqrt2_pos : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
    obtain ⟨x, hx⟩ := Metric.denseRange_iff.mp (R.denseRange α) (oddExtL2 g) (sqrt 2 * ε)
      (mul_pos hsqrt2_pos hε)
    let x_odd : L2C := (1 / 2 : ℝ) • (x - reflectL2 x)
    have hx_odd_isOdd : IsOddL2 x_odd := by
      unfold IsOddL2
      simp only [x_odd, map_smul, reflectL2.map_sub, reflectL2_reflectL2]
      rw [← smul_neg]
      congr 1
      abel
    let u : L2IoiC := restIoiL2 x_odd
    refine ⟨u, ?_⟩
    have hu_ext : oddExtL2 u = x_odd := oddExtL2_restIoiL2_of_isOddL2 hx_odd_isOdd
    have hR_odd : R.operator α (oddExtL2 u) =
        (1 / 2 : ℝ) • (R.operator α x - reflectL2 (R.operator α x)) := by
      rw [hu_ext]
      simp only [x_odd, map_smul, map_sub, h_comm α x]
    have hdiff_odd : IsOddL2 (R.operator α (oddExtL2 u) - oddExtL2 g) := by
      unfold IsOddL2
      have h1 : IsOddL2 (R.operator α (oddExtL2 u)) := by
        unfold IsOddL2
        rw [h_comm α (oddExtL2 u), oddExtL2_isOddL2 u, ContinuousLinearMap.map_neg]
      rw [reflectL2.map_sub, h1, oddExtL2_isOddL2 g]
      abel
    have hnorm_half :
        ‖R.operator α (oddExtL2 u) - oddExtL2 g‖ ≤ ‖R.operator α x - oddExtL2 g‖ := by
      have havg :
          (1 / 2 : ℝ) • ((R.operator α x - oddExtL2 g) -
            reflectL2 (R.operator α x - oddExtL2 g)) =
            R.operator α (oddExtL2 u) - oddExtL2 g := by
        have hodd_g : reflectL2 (oddExtL2 g) = -oddExtL2 g := oddExtL2_isOddL2 g
        rw [reflectL2.map_sub, hodd_g, hR_odd]
        module
      rw [← havg, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      have htri :
          ‖(R.operator α x - oddExtL2 g) - reflectL2 (R.operator α x - oddExtL2 g)‖ ≤
            ‖R.operator α x - oddExtL2 g‖ + ‖reflectL2 (R.operator α x - oddExtL2 g)‖ :=
        norm_sub_le _ _
      rw [reflectL2.norm_map] at htri
      linarith
    have hdist_eq :
        dist g (restIoiL2 (R.operator α (oddExtL2 u))) =
          (sqrt 2)⁻¹ * ‖R.operator α (oddExtL2 u) - oddExtL2 g‖ := by
      rw [dist_comm, dist_eq_norm]
      have hsub : restIoiL2 (R.operator α (oddExtL2 u)) - g =
          restIoiL2 (R.operator α (oddExtL2 u) - oddExtL2 g) := by
        rw [map_sub, restIoiL2_oddExtL2 g]
      rw [hsub]
      have hnorm := norm_restIoiL2_of_isOddL2 hdiff_odd
      calc
        ‖restIoiL2 (R.operator α (oddExtL2 u) - oddExtL2 g)‖
            = (sqrt 2)⁻¹ * (sqrt 2 * ‖restIoiL2 (R.operator α (oddExtL2 u) - oddExtL2 g)‖) := by
              field_simp
        _ = (sqrt 2)⁻¹ * ‖R.operator α (oddExtL2 u) - oddExtL2 g‖ := by rw [hnorm]
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hdist_eq]
    have hx_norm : ‖R.operator α x - oddExtL2 g‖ < sqrt 2 * ε := by
      rw [dist_comm] at hx
      simpa only [dist_eq_norm] using hx
    calc
      (sqrt 2)⁻¹ * ‖R.operator α (oddExtL2 u) - oddExtL2 g‖
          ≤ (sqrt 2)⁻¹ * ‖R.operator α x - oddExtL2 g‖ :=
        mul_le_mul_of_nonneg_left hnorm_half (inv_nonneg.mpr hsqrt2_pos.le)
      _ < (sqrt 2)⁻¹ * (sqrt 2 * ε) :=
        mul_lt_mul_of_pos_left hx_norm (inv_pos.mpr hsqrt2_pos)
      _ = ε := by field_simp

/-- The Laplace-transform resolvent of `reflectedC0Semigroup S h_inv` equals the reflection
conjugation of `S.resolvent μ`. -/
theorem reflectedC0Semigroup_resolvent_eq (S : StronglyContinuousContractionSemigroup L2C)
    (h_inv : ∀ t : ℝ≥0, ∀ f : L2C, IsOddL2 f → IsOddL2 (S t f)) (μ : PositiveShift) :
    (reflectedC0Semigroup S h_inv).resolvent μ =
      restIoiL2.comp ((S.resolvent μ).comp oddExtL2) := by
  ext1 u
  rw [StronglyContinuousContractionSemigroup.resolvent_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, StronglyContinuousContractionSemigroup.resolvent_apply]
  have hcomm :=
    (restIoiL2.integral_comp_comm (S.integrableOn_laplaceIntegrand μ.2 (oddExtL2 u))).symm
  rw [hcomm]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [StronglyContinuousContractionSemigroup.laplaceIntegrand_apply,
    StronglyContinuousContractionSemigroup.laplaceIntegrand_apply, map_smul,
    reflectedC0Semigroup_apply]

/-- **Concrete Half-Line Reflected Fractional Heat `C₀`-Contraction Semigroup on
`L²(0, ∞; ℂ)`**: `S̃_α(t) u = restIoiL2 (fracLapSemigroup α t (oddExtL2 u))`. -/
noncomputable def reflectedFracLapSemigroup (α : ℝ) :
    StronglyContinuousContractionSemigroup L2IoiC :=
  reflectedC0Semigroup (fracLapSemigroup α) (fun t _ hf => fracLapSemigroup_isOddL2 α t hf)

/-- **Concrete Half-Line Reflected Fractional Laplacian Contractive Resolvent on
`L²(0, ∞; ℂ)`**: `R̃_{μ, α} u = restIoiL2 ((fracLapResolvent α).operator μ (oddExtL2 u))`. -/
noncomputable def reflectedFracLapResolvent (α : ℝ) : ContractiveResolvent L2IoiC :=
  reflectedContractiveResolvent (fracLapResolvent α) (fracLapResolvent_reflectL2 α)

/-- **Exact Hille–Yosida Generation of the Concrete Reflected Half-Line Semigroup**:
`(reflectedFracLapResolvent α).generatedSemigroup = reflectedFracLapSemigroup α`. -/
theorem reflectedFracLapResolvent_generatedSemigroup_eq (α : ℝ) :
    (reflectedFracLapResolvent α).generatedSemigroup = reflectedFracLapSemigroup α := by
  have hres :
      (reflectedFracLapSemigroup α).toContractiveResolvent = reflectedFracLapResolvent α := by
    rw [StronglyContinuousContractionSemigroup.toContractiveResolvent]
    cases hR : reflectedFracLapResolvent α
    simp only [ContractiveResolvent.mk.injEq]
    funext μ
    calc
      (reflectedFracLapSemigroup α).resolvent μ
          = restIoiL2.comp (((fracLapSemigroup α).resolvent μ).comp oddExtL2) :=
        reflectedC0Semigroup_resolvent_eq (fracLapSemigroup α)
          (fun t _ hf => fracLapSemigroup_isOddL2 α t hf) μ
      _ = restIoiL2.comp (((fracLapResolvent α).operator μ).comp oddExtL2) := by
        unfold fracLapSemigroup fracLapResolvent
        rw [fourierMultiplierSemigroup_resolvent_eq (fracLapSymbol α) (measurable_fracLapSymbol α)
          (fracLapSymbol_nonneg α) μ]
      _ = (reflectedFracLapResolvent α).operator μ := rfl
      _ = _ := by rw [hR]
  rw [← hres]
  exact (reflectedFracLapSemigroup α).generatedSemigroup_toContractiveResolvent

/-- Whole-line fractional heat semigroup viewed as a `ContractionSemigroup L2C`. -/
noncomputable def fracLapContractionSemigroup (α : ℝ) : ContractionSemigroup L2C where
  T t f := fracLapSemigroup α (Real.toNNReal t) f
  normE f := ‖f‖
  normE_nonneg := norm_nonneg
  map_zero_time f := by
    rw [Real.toNNReal_zero, (fracLapSemigroup α).zero_apply]
  map_add_time s t hs ht f := by
    rw [← ContinuousLinearMap.comp_apply, ← (fracLapSemigroup α).operator_add,
      Real.toNNReal_add hs ht]
  contractive t _ f := (fracLapSemigroup α).norm_apply_le _ f

/-- Reflected fractional heat semigroup on `L²(0, ∞; ℂ)` via `reflectedContractionSemigroup`
and `halfLineOddConjugation`. -/
noncomputable def reflectedFracLapContractionSemigroup (α : ℝ) :
    ContractionSemigroup L2IoiC :=
  reflectedContractionSemigroup (fracLapContractionSemigroup α) (fun u => ‖u‖) norm_nonneg
    halfLineOddConjugation (fun t _ _ hf => fracLapSemigroup_isOddL2 α (Real.toNNReal t) hf)

/-- **Generator Domain of `reflectedC0Semigroup`**: `u ∈ D(Ã)` iff `oddExtL2 u ∈ D(A)`. -/
theorem mem_generatorDomain_reflectedC0Semigroup_iff
    (S : StronglyContinuousContractionSemigroup L2C)
    (h_inv : ∀ t : ℝ≥0, ∀ f : L2C, IsOddL2 f → IsOddL2 (S t f)) (u : L2IoiC) :
    u ∈ (reflectedC0Semigroup S h_inv).generatorDomain ↔ oddExtL2 u ∈ S.generatorDomain := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨oddExtL2 g, ?_⟩
    have hcont := (oddExtL2.continuous.tendsto g).comp hg
    refine hcont.congr fun t => ?_
    change oddExtL2 ((t : ℝ)⁻¹ • (restIoiL2 (S t (oddExtL2 u)) - u)) =
      (t : ℝ)⁻¹ • (S t (oddExtL2 u) - oddExtL2 u)
    have h_odd : IsOddL2 (S t (oddExtL2 u)) := h_inv t (oddExtL2 u) (oddExtL2_isOddL2 u)
    rw [map_smul, map_sub, oddExtL2_restIoiL2_of_isOddL2 h_odd]
  · rintro ⟨G, hG⟩
    refine ⟨restIoiL2 G, ?_⟩
    have hcont := (restIoiL2.continuous.tendsto G).comp hG
    refine hcont.congr fun t => ?_
    change restIoiL2 ((t : ℝ)⁻¹ • (S t (oddExtL2 u) - oddExtL2 u)) =
      (t : ℝ)⁻¹ • (restIoiL2 (S t (oddExtL2 u)) - u)
    rw [map_smul, map_sub, restIoiL2_oddExtL2 u]

/-- **Generator Formula for `reflectedC0Semigroup`**: on `D(Ã)`,
`Ã u = restIoiL2 (A (oddExtL2 u))`. -/
theorem generator_reflectedC0Semigroup (S : StronglyContinuousContractionSemigroup L2C)
    (h_inv : ∀ t : ℝ≥0, ∀ f : L2C, IsOddL2 f → IsOddL2 (S t f)) {u : L2IoiC}
    (hu : u ∈ (reflectedC0Semigroup S h_inv).generatorDomain) :
    (reflectedC0Semigroup S h_inv).generator ⟨u, hu⟩ =
      restIoiL2 (S.generator ⟨oddExtL2 u,
        (mem_generatorDomain_reflectedC0Semigroup_iff S h_inv u).mp hu⟩) := by
  refine (reflectedC0Semigroup S h_inv).generator_eq_of_tendsto ⟨u, hu⟩ ?_
  have hS := S.tendsto_generator
    ⟨oddExtL2 u, (mem_generatorDomain_reflectedC0Semigroup_iff S h_inv u).mp hu⟩
  have hcont := (restIoiL2.continuous.tendsto _).comp hS
  refine hcont.congr fun t => ?_
  change restIoiL2 (S.differenceQuotient (oddExtL2 u) t) =
    (reflectedC0Semigroup S h_inv).differenceQuotient u t
  rw [StronglyContinuousContractionSemigroup.differenceQuotient_apply,
    StronglyContinuousContractionSemigroup.differenceQuotient_apply,
    map_smul, map_sub, restIoiL2_oddExtL2 u, reflectedC0Semigroup_apply]

/-- **Generator Domain of `reflectedFracLapSemigroup α` (`thm:halffracsemi`)**:
`u ∈ D(-(−Δ̃)^(α/2))` iff `oddExtL2 u ∈ D(-(−Δ)^(α/2))`. -/
theorem reflectedFracLapSemigroup_mem_generatorDomain_iff (α : ℝ) (u : L2IoiC) :
    u ∈ (reflectedFracLapSemigroup α).generatorDomain ↔
      oddExtL2 u ∈ (fracLapSemigroup α).generatorDomain :=
  mem_generatorDomain_reflectedC0Semigroup_iff (fracLapSemigroup α)
    (fun t _ hf => fracLapSemigroup_isOddL2 α t hf) u

/-- **Generator Action of `reflectedFracLapSemigroup α` (`thm:halffracsemi`)**:
`Ã_α u = restIoiL2 (A_α (oddExtL2 u))`. -/
theorem generator_reflectedFracLapSemigroup (α : ℝ) {u : L2IoiC}
    (hu : u ∈ (reflectedFracLapSemigroup α).generatorDomain) :
    (reflectedFracLapSemigroup α).generator ⟨u, hu⟩ =
      restIoiL2 ((fracLapSemigroup α).generator ⟨oddExtL2 u,
        (reflectedFracLapSemigroup_mem_generatorDomain_iff α u).mp hu⟩) :=
  generator_reflectedC0Semigroup (fracLapSemigroup α)
    (fun t _ hf => fracLapSemigroup_isOddL2 α t hf) hu

/-- **Method of Images / Reflected Heat Kernel (`thm:halffracsemi`, `eq:halffracsemi`)**:
for `0 < α < 2`, `t > 0`, and `u ∈ L²((0, ∞); ℂ)`, `(reflectedFracLapSemigroup α t u)(x)` equals
`∫_{(0, ∞)} (P_α(x - y, t) - P_α(x + y, t)) u(y) dy` for almost every `x ∈ (0, ∞)`. -/
theorem reflectedFracLapSemigroup_apply_ae_eq_reflectedHeatKernel {α : ℝ}
    (hα : FractionalExponent α) {t : ℝ≥0} (ht : 0 < (t : ℝ)) (u : L2IoiC) :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ)),
      ((reflectedFracLapSemigroup α t u : L2IoiC) : ℝ → ℂ) x =
        ∫ y in Ioi (0 : ℝ),
          ((reflectedHeatKernel (stableHeatKernel α hα) x y t : ℝ) : ℂ) * (u : ℝ → ℂ) y := by
  have hrest := coeFn_restIoiL2 (fracLapSemigroup α t (oddExtL2 u))
  have hconv := ae_restrict_of_ae (s := Ioi (0 : ℝ))
    (fracLapSemigroup_apply_ae_eq_conv hα ht (oddExtL2 u))
  have href_ext :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      (coeFn_extendByZeroIoiC u)
  have hodd_ae :
      (oddExtL2 u : ℝ → ℂ) =ᵐ[volume] fun z : ℝ =>
        (Ioi (0 : ℝ)).indicator (u : ℝ → ℂ) z - (Ioi (0 : ℝ)).indicator (u : ℝ → ℂ) (-z) := by
    filter_upwards [Lp.coeFn_sub (extendByZeroIoiC u) (reflectL2 (extendByZeroIoiC u)),
      coeFn_extendByZeroIoiC u, coeFn_reflectL2 (extendByZeroIoiC u), href_ext] with z hs he hr hre
    have hs' : (oddExtL2 u : ℝ → ℂ) z =
        (extendByZeroIoiC u : ℝ → ℂ) z - (reflectL2 (extendByZeroIoiC u) : ℝ → ℂ) z := hs
    have hr' : (reflectL2 (extendByZeroIoiC u) : ℝ → ℂ) z = (extendByZeroIoiC u : ℝ → ℂ) (-z) := hr
    rw [hs', he, hr', hre]
  let K : ℝ → ℂ := fun x => ((stableKernel α x t : ℝ) : ℂ)
  have hK2 : MemLp K 2 volume := memLp_two_stableKernel hα ht
  filter_upwards [hrest, hconv] with x hx_rest hx_conv
  change (restIoiL2 (fracLapSemigroup α t (oddExtL2 u)) : ℝ → ℂ) x = _
  rw [hx_rest, hx_conv]
  have hconv_swap :
      (K ⋆[ContinuousLinearMap.mul ℂ ℂ] (oddExtL2 u : ℝ → ℂ)) x =
        ∫ z : ℝ, K (x - z) * (oddExtL2 u : ℝ → ℂ) z := by
    rw [convolution_mul]
    rw [← integral_sub_left_eq_self (fun z : ℝ => K (x - z) * (oddExtL2 u : ℝ → ℂ) z) volume x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring_nf
  rw [hconv_swap]
  have hK_sub : MemLp (fun z : ℝ => K (x - z)) 2 volume := by
    have hmp := Measure.measurePreserving_sub_left (volume : Measure ℝ) x
    exact hK2.comp_measurePreserving hmp
  have hint1 : Integrable (fun z : ℝ => K (x - z) * (Ioi (0 : ℝ)).indicator (u : ℝ → ℂ) z)
      volume :=
    hK_sub.integrable_mul ((Lp.memLp (extendByZeroIoiC u)).ae_eq (coeFn_extendByZeroIoiC u))
  have hint2 : Integrable (fun z : ℝ => K (x - z) * (Ioi (0 : ℝ)).indicator (u : ℝ → ℂ) (-z))
      volume :=
    hK_sub.integrable_mul ((Lp.memLp (reflectL2 (extendByZeroIoiC u))).ae_eq
      (coeFn_reflectL2 (extendByZeroIoiC u) |>.trans href_ext))
  have hcongr_odd :
      ∫ z : ℝ, K (x - z) * (oddExtL2 u : ℝ → ℂ) z =
        ∫ z : ℝ, (K (x - z) * (Ioi (0 : ℝ)).indicator (u : ℝ → ℂ) z -
          K (x - z) * (Ioi (0 : ℝ)).indicator (u : ℝ → ℂ) (-z)) := by
    refine integral_congr_ae ?_
    filter_upwards [hodd_ae] with z hz
    rw [hz, mul_sub]
  rw [hcongr_odd, integral_sub hint1 hint2]
  have hint2_neg :
      (∫ z : ℝ, K (x - z) * (Ioi (0 : ℝ)).indicator (u : ℝ → ℂ) (-z)) =
        ∫ y : ℝ, K (x + y) * (Ioi (0 : ℝ)).indicator (u : ℝ → ℂ) y := by
    rw [← integral_neg_eq_self
      (fun y : ℝ => K (x + y) * (Ioi (0 : ℝ)).indicator (u : ℝ → ℂ) y) volume]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring_nf
  rw [hint2_neg]
  have hint2' : Integrable (fun y : ℝ => K (x + y) * (Ioi (0 : ℝ)).indicator (u : ℝ → ℂ) y)
      volume := by
    have := hint2.comp_neg
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    ring_nf
  rw [← integral_sub hint1 hint2']
  have h_ind :
      (fun y : ℝ => K (x - y) * (Ioi (0 : ℝ)).indicator (u : ℝ → ℂ) y -
          K (x + y) * (Ioi (0 : ℝ)).indicator (u : ℝ → ℂ) y) =
        (Ioi (0 : ℝ)).indicator (fun y : ℝ =>
          ((reflectedHeatKernel (stableHeatKernel α hα) x y t : ℝ) : ℂ) * (u : ℝ → ℂ) y) := by
    ext y
    by_cases hy : y ∈ Ioi (0 : ℝ)
    · simp only [Set.indicator_of_mem hy, reflectedHeatKernel, stableHeatKernel, K]
      push_cast
      ring
    · simp only [Set.indicator_of_notMem hy, mul_zero, sub_self]
  rw [h_ind, integral_indicator measurableSet_Ioi]

/-- **Sub-Markov Positivity of `reflectedFracLapSemigroup α` (`thm:halffracsemi`)**:
if `u ∈ L²((0, ∞); ℂ)` is real-valued and `0 ≤ (u y).re` a.e. on `(0, ∞)`, then
`reflectedFracLapSemigroup α t u` is real-valued and `0 ≤ (·).re` a.e. for all `t ≥ 0`. -/
theorem reflectedFracLapSemigroup_re_nonneg {α : ℝ} (hα : FractionalExponent α) (t : ℝ≥0)
    {u : L2IoiC}
    (hu_real : ∀ᵐ y : ℝ ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ)), ((u : ℝ → ℂ) y).im = 0)
    (hu_nn : ∀ᵐ y : ℝ ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ)), 0 ≤ ((u : ℝ → ℂ) y).re) :
    (∀ᵐ x : ℝ ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ)),
      ((reflectedFracLapSemigroup α t u : ℝ → ℂ) x).im = 0) ∧
      (∀ᵐ x : ℝ ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ)),
        0 ≤ ((reflectedFracLapSemigroup α t u : ℝ → ℂ) x).re) := by
  by_cases ht : (t : ℝ) = 0
  · have ht0 : t = 0 := NNReal.eq ht
    subst ht0
    simpa only [(reflectedFracLapSemigroup α).zero_apply] using ⟨hu_real, hu_nn⟩
  · have htp : 0 < (t : ℝ) := lt_of_le_of_ne t.coe_nonneg (Ne.symm ht)
    have hK_int : ∀ x : ℝ,
        IntegrableOn (fun y : ℝ =>
          ((reflectedHeatKernel (stableHeatKernel α hα) x y t : ℝ) : ℂ) * (u : ℝ → ℂ) y)
          (Ioi (0 : ℝ)) volume := fun x => by
      let K : ℝ → ℂ := fun z => ((stableKernel α z t : ℝ) : ℂ)
      have hK2 : MemLp K 2 volume := memLp_two_stableKernel hα htp
      have hKm : MemLp (fun y : ℝ => K (x - y)) 2 ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))) :=
        (hK2.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)).restrict _
      have hKp : MemLp (fun y : ℝ => K (x + y)) 2
          ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))) := by
        have hmp := measurePreserving_add_left volume x
        exact (hK2.comp_measurePreserving hmp).restrict _
      have hu2 : MemLp (u : ℝ → ℂ) 2 ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))) := Lp.memLp u
      have hsub := ((hKm.sub hKp).integrable_mul hu2)
      refine hsub.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only [Pi.mul_apply, Pi.sub_apply, reflectedHeatKernel, stableHeatKernel, K]
      push_cast
      ring
    have hae := reflectedFracLapSemigroup_apply_ae_eq_reflectedHeatKernel hα htp u
    refine ⟨?_, ?_⟩
    · filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with x hx _
      rw [hx, ← Complex.imCLM_apply, ← Complex.imCLM.integral_comp_comm (hK_int x)]
      simp only [Complex.imCLM_apply]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hu_real] with y hy
      simp [Complex.mul_im, hy]
    · filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with x hx hx0
      rw [hx, ← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm (hK_int x)]
      simp only [Complex.reCLM_apply]
      refine integral_nonneg_of_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi, hu_nn] with y hy0 hy
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg (reflectedHeatKernel_bounds (stableHeatKernel α hα) hx0 hy0 htp).1 hy

/-- **Sub-Markov `L^∞`-Contractivity of `reflectedFracLapSemigroup α` (`thm:halffracsemi`)**:
if `u ∈ L²((0, ∞); ℂ)` is real-valued with `0 ≤ (u y).re ≤ M` a.e. on `(0, ∞)`, then
`((reflectedFracLapSemigroup α t u : ℝ → ℂ) x).re ≤ M` a.e. on `(0, ∞)` for all `t ≥ 0`. -/
theorem reflectedFracLapSemigroup_re_le {α : ℝ} (hα : FractionalExponent α) (t : ℝ≥0) {M : ℝ}
    (hM : 0 ≤ M) {u : L2IoiC}
    (hu_nn : ∀ᵐ y : ℝ ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ)), 0 ≤ ((u : ℝ → ℂ) y).re)
    (hu_le : ∀ᵐ y : ℝ ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ)), ((u : ℝ → ℂ) y).re ≤ M) :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ)),
      ((reflectedFracLapSemigroup α t u : ℝ → ℂ) x).re ≤ M := by
  have hodd_le : ∀ᵐ x : ℝ ∂volume, ((oddExtL2 u : ℝ → ℂ) x).re ≤ M := by
    have href_ext :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
        (coeFn_extendByZeroIoiC u)
    have hnn_all : ∀ᵐ x : ℝ ∂volume, x ∈ Ioi (0 : ℝ) → 0 ≤ ((u : ℝ → ℂ) x).re :=
      (ae_restrict_iff' measurableSet_Ioi).mp hu_nn
    have hle_all : ∀ᵐ x : ℝ ∂volume, x ∈ Ioi (0 : ℝ) → ((u : ℝ → ℂ) x).re ≤ M :=
      (ae_restrict_iff' measurableSet_Ioi).mp hu_le
    have hnn_neg : ∀ᵐ x : ℝ ∂volume, -x ∈ Ioi (0 : ℝ) → 0 ≤ ((u : ℝ → ℂ) (-x)).re :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hnn_all
    filter_upwards [Lp.coeFn_sub (extendByZeroIoiC u) (reflectL2 (extendByZeroIoiC u)),
      coeFn_extendByZeroIoiC u, coeFn_reflectL2 (extendByZeroIoiC u), href_ext,
      hle_all, hnn_neg] with x hs he hr hre hlex hnnx
    have hs' : (oddExtL2 u : ℝ → ℂ) x =
        (extendByZeroIoiC u : ℝ → ℂ) x - (reflectL2 (extendByZeroIoiC u) : ℝ → ℂ) x := hs
    have hr' : (reflectL2 (extendByZeroIoiC u) : ℝ → ℂ) x = (extendByZeroIoiC u : ℝ → ℂ) (-x) := hr
    rw [hs', he, hr', hre, Complex.sub_re]
    rcases le_or_gt x 0 with hx0 | hx0
    · have hnot : x ∉ Ioi (0 : ℝ) := not_lt.mpr hx0
      rw [Set.indicator_of_notMem hnot, Complex.zero_re, zero_sub]
      by_cases hnx : -x ∈ Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hnx]
        linarith [hnnx hnx]
      · rw [Set.indicator_of_notMem hnx, Complex.zero_re, neg_zero]
        exact hM
    · have hnx : -x ∉ Ioi (0 : ℝ) := not_lt.mpr (by linarith)
      rw [Set.indicator_of_mem hx0, Set.indicator_of_notMem hnx, Complex.zero_re, sub_zero]
      exact hlex hx0
  have hS_le := ae_restrict_of_ae (s := Ioi (0 : ℝ)) (fracLapSemigroup_re_le hα t hodd_le)
  filter_upwards [coeFn_restIoiL2 (fracLapSemigroup α t (oddExtL2 u)), hS_le] with x hx1 hx2
  change ((restIoiL2 (fracLapSemigroup α t (oddExtL2 u)) : ℝ → ℂ) x).re ≤ M
  rw [hx1]
  exact hx2

end

end FracLap
