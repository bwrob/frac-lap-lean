/-
Copyright (c) 2026 Bartosz Wróblewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bartosz Wróblewski
-/
module

public import FracLap.Core.FourierSobolev
public import FracLap.Core.HilleYosidaCorrespondence
public import FracLap.Core.LpExtension
public import FracLap.Core.Semigroups
public import FracLap.WholeLine.AnomalousDiffusion
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FracLap.HalfLine.RestrictedDirichlet

Restricted (homogeneous exterior-Dirichlet) half-line spaces `L²_0(ℝ)` and `H^(α / 2)_0(ℝ)`,
restricted fractional Dirichlet form `B^α_0`, concrete Gagliardo Sobolev space construction,
Beurling–Deny Markovianity, and the Markov semigroup `S₀(t)`:
- `VanishesOnNeg u`: exterior Dirichlet condition `u(x) = 0` for all `x < 0`.
- `vanishesOnNeg_linear_comb`: linear subspace closure of `VanishesOnNeg`.
- `restrictSymmetricAccretiveForm`: restricting a symmetric, accretive, continuous bilinear
  form `B^α` to a subspace `V₀ ↪ V` yields a symmetric, accretive, continuous bilinear form
  `B^α_0` on `V₀`.
- `vanishesOnNeg_abs` and `vanishesOnNeg_min_one`: the normal contractions `u ↦ |u|` and
  `u ↦ u ∧ 1` preserve the homogeneous exterior condition `VanishesOnNeg`.
- `restrictedForm_isMarkovDirichletForm`: the restricted form `B^α_0` on `H^(α / 2)_0(ℝ)`
  inherits both Beurling–Deny Markov form criteria from `B^α`.
- `restrictedSemigroup_orbit_properties`: orbits `u(t) = S₀(t) u₀` satisfy `u(0) = u₀` and
  vanish identically on `(-∞, 0)` for all `t ≥ 0`.
- `gagliardoMeasure`, `GagliardoSpace`, `gagliardoForm`, `gagliardoForm_isMarkovDirichletForm`:
  concrete Gagliardo fractional Sobolev Hilbert space `H^(α / 2)(ℝ)` and Markov Dirichlet form.
- `RestrictedGagliardoSpace`, `restrictedGagliardoForm`,
  `restrictedGagliardoForm_isMarkovDirichletForm`: concrete exterior-Dirichlet form domain
  `H^(α / 2)_0(0, ∞)` and concrete `IsMarkovDirichletForm` instance.
- `gagliardoTentRestricted` and `exists_restrictedGagliardoForm_pos`: explicit nonzero tent
  function in `H^(α / 2)_0(0, ∞)` witnessing non-vacuity of `restrictedGagliardoForm α`.
-/

namespace FracLap

open Filter MeasureTheory Real Set Topology
open scoped ENNReal NNReal InnerProductSpace

@[expose] public section

/-- A function `u : ℝ → ℝ` satisfies the homogeneous exterior-Dirichlet condition on `(-∞, 0)`
if `u x = 0` for all `x < 0`. -/
def VanishesOnNeg (u : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, x < 0 → u x = 0

/-- **Linear Subspace Closure of `VanishesOnNeg`**:
The exterior-Dirichlet condition `VanishesOnNeg` is preserved under linear combinations. -/
theorem vanishesOnNeg_linear_comb {u v : ℝ → ℝ} (hu : VanishesOnNeg u) (hv : VanishesOnNeg v)
    (a b : ℝ) :
    VanishesOnNeg (fun x : ℝ => a * u x + b * v x) := by
  intro x hx
  dsimp only
  rw [hu x hx, hv x hx]
  ring

/-- **Restricted Symmetric Accretive Form**:
Restricting a symmetric, accretive, continuous bilinear form `B` on an ambient form domain `V`
along an embedding `ι : V₀ → V` (modeling `H^(α / 2)_0(ℝ) ↪ H^(α / 2)(ℝ)`) yields a
symmetric, accretive, continuous bilinear form `B₀` on `V₀`. -/
def restrictSymmetricAccretiveForm {V V₀ : Type*} (B : SymmetricAccretiveForm V)
    (ι : V₀ → V) : SymmetricAccretiveForm V₀ where
  form u v := B.form (ι u) (ι v)
  symm u v := B.symm (ι u) (ι v)
  accretive u := B.accretive (ι u)
  cauchy_schwarz_sq u v := B.cauchy_schwarz_sq (ι u) (ι v)

/-- **Exterior-Dirichlet Invariance under Modulus**:
If `u : ℝ → ℝ` vanishes on `(-∞, 0)`, then `|u|` also vanishes on `(-∞, 0)`. -/
theorem vanishesOnNeg_abs {u : ℝ → ℝ} (hu : VanishesOnNeg u) :
    VanishesOnNeg (fun x : ℝ => |u x|) := by
  intro x hx
  dsimp only
  rw [hu x hx, abs_zero]

/-- **Exterior-Dirichlet Invariance under Unit Truncation**:
If `u : ℝ → ℝ` vanishes on `(-∞, 0)`, then `u ∧ 1 = min u 1` also vanishes on `(-∞, 0)`. -/
theorem vanishesOnNeg_min_one {u : ℝ → ℝ} (hu : VanishesOnNeg u) :
    VanishesOnNeg (fun x : ℝ => min (u x) 1) := by
  intro x hx
  dsimp only
  rw [hu x hx]
  exact min_eq_left (by norm_num)

/-- **Inheritance of Beurling–Deny Markov Form Conditions by the Restricted Form `B^α_0`**:
If an ambient symmetric accretive form `B` on `V` (modeling `B^α` on `H^(α / 2)(ℝ)`) satisfies
the Beurling–Deny Markov form criteria with respect to `absOp` and `capOneOp`, and the
subspace embedding `ι : V₀ → V` (modeling `H^(α / 2)_0(ℝ) ↪ H^(α / 2)(ℝ)`) intertwines the
restricted truncations `absOp₀, capOneOp₀ : V₀ → V₀`, then the restricted form `B₀` on `V₀`
also satisfies both Beurling–Deny conditions. -/
theorem restrictedForm_isMarkovDirichletForm {V V₀ : Type*}
    (B : SymmetricAccretiveForm V) (absOp capOneOp : V → V)
    (hB : IsMarkovDirichletForm B absOp capOneOp)
    (ι : V₀ → V) (absOp₀ capOneOp₀ : V₀ → V₀)
    (h_abs : ∀ u : V₀, ι (absOp₀ u) = absOp (ι u))
    (h_cap : ∀ u : V₀, ι (capOneOp₀ u) = capOneOp (ι u)) :
    IsMarkovDirichletForm (restrictSymmetricAccretiveForm B ι) absOp₀ capOneOp₀ where
  form_abs_le u := by
    change B.form (ι (absOp₀ u)) (ι (absOp₀ u)) ≤ B.form (ι u) (ι u)
    rw [h_abs u]
    exact hB.form_abs_le (ι u)
  form_capOne_le u := by
    change B.form (ι (capOneOp₀ u)) (ι (capOneOp₀ u)) ≤ B.form (ι u) (ι u)
    rw [h_cap u]
    exact hB.form_capOne_le (ι u)

/-- **Orbit Properties of the Restricted Semigroup `S₀(t)`**:
Every trajectory `u(t) = S₀(t) u₀` of a contraction semigroup on the exterior-Dirichlet
subspace `{v : ℝ → ℝ // VanishesOnNeg v}` satisfies `S₀(0) u₀ = u₀` and vanishes identically on
`(-∞, 0)` for all `t ≥ 0`. -/
theorem restrictedSemigroup_orbit_properties
    (S₀ : ContractionSemigroup {v : ℝ → ℝ // VanishesOnNeg v})
    (u₀ : {v : ℝ → ℝ // VanishesOnNeg v}) (t : ℝ) :
    S₀.T 0 u₀ = u₀ ∧ ∀ x : ℝ, x < 0 → (S₀.T t u₀).1 x = 0 :=
  ⟨S₀.map_zero_time u₀, (S₀.T t u₀).2⟩

/-! ### 1. Real `L²` spaces, half-line restriction, and the Gagliardo kernel measure -/

/-- Concrete whole-line real Hilbert space `L²(ℝ; ℝ)`. -/
noncomputable abbrev L2R := Lp (α := ℝ) ℝ 2 (volume : Measure ℝ)

/-- Concrete half-line real Hilbert space `L²((0, ∞); ℝ)`. -/
noncomputable abbrev L2IoiR := Lp (α := ℝ) ℝ 2 ((volume : Measure ℝ).restrict (Ioi (0 : ℝ)))

/-- Gagliardo singular kernel density `C(α) / (2 |x - y|^(1 + α))` as an `ℝ≥0∞`-valued weight
on `ℝ × ℝ`. Note that on the diagonal `x = y`, division by zero yields `0` in `ℝ`. -/
noncomputable def gagliardoWeight (α : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (fracLapConstant α / (2 * |p.1 - p.2| ^ (1 + α)))

/-- Measurability of `gagliardoWeight α` on `ℝ × ℝ`. -/
theorem measurable_gagliardoWeight (α : ℝ) : Measurable (gagliardoWeight α) :=
  ENNReal.continuous_ofReal.measurable.comp
    (measurable_const.div
      (measurable_const.mul
        ((continuous_abs.comp (continuous_fst.sub continuous_snd)).measurable.pow_const
          (1 + α))))

/-- **Non-degeneracy of the Gagliardo weight**: for `α ∈ (0, 2)` the weight is strictly positive
off the diagonal, `0 < C(α) / (2 |x - y|^(1 + α))` whenever `x ≠ y`. -/
theorem gagliardoWeight_pos {α : ℝ} (hα : FractionalExponent α) {x y : ℝ} (hxy : x ≠ y) :
    0 < gagliardoWeight α (x, y) := by
  have hC : 0 < fracLapConstant α := fracLapConstant_pos hα
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  change 0 < ENNReal.ofReal (fracLapConstant α / (2 * |x - y| ^ (1 + α)))
  exact ENNReal.ofReal_pos.mpr (by positivity)

/-- The Gagliardo fractional measure `(C(α) / (2 |x - y|^(1 + α))) dx dy` on `ℝ × ℝ`. -/
noncomputable def gagliardoMeasure (α : ℝ) : Measure (ℝ × ℝ) :=
  ((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity (gagliardoWeight α)

/-- Concrete weighted `L²(ℝ × ℝ; gagliardoMeasure α)` space for fractional difference quotients. -/
noncomputable abbrev L2Gagliardo (α : ℝ) := Lp (α := ℝ × ℝ) ℝ 2 (gagliardoMeasure α)

/-- `gagliardoMeasure α` is absolutely continuous with respect to Lebesgue product measure. -/
theorem gagliardoMeasure_ac (α : ℝ) :
    gagliardoMeasure α ≪ (volume : Measure ℝ).prod (volume : Measure ℝ) :=
  withDensity_absolutelyContinuous _ _

/-- Restriction operator `L²(ℝ; ℝ) →L[ℝ] L²((0, ∞); ℝ)`. -/
noncomputable def restIoiR : L2R →L[ℝ] L2IoiR :=
  LinearMap.mkContinuous
    { toFun := fun f => ((Lp.memLp f).restrict (Ioi (0 : ℝ))).toLp (f : ℝ → ℝ)
      map_add' := fun f g => by
        rw [Lp.ext_iff]
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).restrict (Ioi (0 : ℝ))),
          Lp.coeFn_add
            (((Lp.memLp f).restrict (Ioi (0 : ℝ))).toLp (f : ℝ → ℝ))
            (((Lp.memLp g).restrict (Ioi (0 : ℝ))).toLp (g : ℝ → ℝ)),
          MemLp.coeFn_toLp ((Lp.memLp f).restrict (Ioi (0 : ℝ))),
          MemLp.coeFn_toLp ((Lp.memLp g).restrict (Ioi (0 : ℝ))),
          ae_restrict_of_ae (Lp.coeFn_add f g)] with x h1 h2 h3 h4 hadd
        rw [h1, h2, Pi.add_apply, h3, h4, hadd, Pi.add_apply]
      map_smul' := fun c f => by
        rw [Lp.ext_iff]
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).restrict (Ioi (0 : ℝ))),
          Lp.coeFn_smul c (((Lp.memLp f).restrict (Ioi (0 : ℝ))).toLp (f : ℝ → ℝ)),
          MemLp.coeFn_toLp ((Lp.memLp f).restrict (Ioi (0 : ℝ))),
          ae_restrict_of_ae (Lp.coeFn_smul c f)] with x h1 h2 h3 hsmul
        rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3, hsmul, Pi.smul_apply] }
    1
    (fun f => by
      change ‖((Lp.memLp f).restrict (Ioi (0 : ℝ))).toLp (f : ℝ → ℝ)‖ ≤ 1 * ‖f‖
      rw [one_mul, Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
        (eLpNorm_restrict_le _ 2 volume (Ioi (0 : ℝ))))

/-- Pointwise a.e. characterization of `restIoiR f` on `(0, ∞)`. -/
theorem coeFn_restIoiR (f : L2R) :
    (restIoiR f : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Ioi (0 : ℝ))] (f : ℝ → ℝ) :=
  MemLp.coeFn_toLp ((Lp.memLp f).restrict (Ioi (0 : ℝ)))

/-- Restricting the zero extension recovers the original half-line `L²` function. -/
theorem restIoiR_halfLineL2ExtendByZero (f : L2IoiR) :
    restIoiR (halfLineL2ExtendByZero f) = f := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_restIoiR (halfLineL2ExtendByZero f),
    ae_restrict_of_ae (coeFn_lpExtendByZero measurableSet_Ioi f),
    ae_restrict_mem measurableSet_Ioi] with x hrest hext hx
  have h1 : (restIoiR (halfLineL2ExtendByZero f) : ℝ → ℝ) x =
      (halfLineL2ExtendByZero f : ℝ → ℝ) x := hrest
  have h2 : (halfLineL2ExtendByZero f : ℝ → ℝ) x =
      (Ioi (0 : ℝ)).indicator (f : ℝ → ℝ) x := hext
  rw [h1, h2, Set.indicator_of_mem hx]

/-- Re-extending the restriction of a function vanishing a.e. on `(-∞, 0]` recovers it. -/
theorem halfLineL2ExtendByZero_restIoiR_of_ae_zero {u : L2R}
    (hu : ∀ᵐ x : ℝ ∂volume, x ≤ 0 → (u : ℝ → ℝ) x = 0) :
    halfLineL2ExtendByZero (restIoiR u) = u := by
  rw [Lp.ext_iff]
  have hr : ∀ᵐ x : ℝ ∂volume, x ∈ Ioi (0 : ℝ) → (restIoiR u : ℝ → ℝ) x = (u : ℝ → ℝ) x :=
    (ae_restrict_iff' measurableSet_Ioi).mp (coeFn_restIoiR u)
  filter_upwards [coeFn_lpExtendByZero measurableSet_Ioi (restIoiR u), hr, hu]
    with x hext hr_x hu_x
  have h1 : (halfLineL2ExtendByZero (restIoiR u) : ℝ → ℝ) x =
      (Ioi (0 : ℝ)).indicator (restIoiR u : ℝ → ℝ) x := hext
  rw [h1]
  by_cases hx : 0 < x
  · rw [Set.indicator_of_mem hx, hr_x hx]
  · rw [Set.indicator_of_notMem hx, (hu_x (not_lt.mp hx)).symm]

/-- Adjoint identity between zero extension `halfLineL2ExtendByZero` and restriction `restIoiR`. -/
theorem inner_halfLineL2ExtendByZero_eq_restIoiR (f : L2IoiR) (u : L2R) :
    ⟪halfLineL2ExtendByZero f, u⟫_ℝ = ⟪f, restIoiR u⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  have hL :
      (∫ x : ℝ, ⟪(halfLineL2ExtendByZero f : ℝ → ℝ) x, (u : ℝ → ℝ) x⟫_ℝ) =
        ∫ x : ℝ, (Ioi (0 : ℝ)).indicator
          (fun y => ⟪(f : ℝ → ℝ) y, (u : ℝ → ℝ) y⟫_ℝ) x := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_lpExtendByZero measurableSet_Ioi f] with x hext
    have h1 : (halfLineL2ExtendByZero f : ℝ → ℝ) x =
        (Ioi (0 : ℝ)).indicator (f : ℝ → ℝ) x := hext
    rw [h1]
    by_cases hx : 0 < x
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, inner_zero_left]
  rw [hL, integral_indicator measurableSet_Ioi]
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mp (coeFn_restIoiR u)] with x hrest hx
  have hrest' : (restIoiR u : ℝ → ℝ) x = (u : ℝ → ℝ) x := hrest hx
  rw [hrest']

/-! ### 2. Concrete Gagliardo fractional Sobolev Hilbert space `H^(α / 2)(ℝ)` -/

/-- Ambient Hilbert product `L²(ℝ; ℝ) × L²(ℝ × ℝ; gagliardoMeasure α)` for the Gagliardo graph. -/
noncomputable abbrev GagliardoAmbient (α : ℝ) := WithLp 2 (L2R × L2Gagliardo α)

/-- Lift a `volume`-a.e. property on `ℝ` along the first coordinate to `gagliardoMeasure α`. -/
theorem ae_fst_gagliardoMeasure {α : ℝ} {P : ℝ → Prop} (h : ∀ᵐ x : ℝ ∂volume, P x) :
    ∀ᵐ p : ℝ × ℝ ∂gagliardoMeasure α, P p.1 :=
  ae_iff.mpr (gagliardoMeasure_ac α (ae_iff.mp (Measure.quasiMeasurePreserving_fst.ae h)))

/-- Lift a `volume`-a.e. property on `ℝ` along the second coordinate to `gagliardoMeasure α`. -/
theorem ae_snd_gagliardoMeasure {α : ℝ} {P : ℝ → Prop} (h : ∀ᵐ x : ℝ ∂volume, P x) :
    ∀ᵐ p : ℝ × ℝ ∂gagliardoMeasure α, P p.2 :=
  ae_iff.mpr (gagliardoMeasure_ac α (ae_iff.mp (Measure.quasiMeasurePreserving_snd.ae h)))

/-- Closed linear subspace of `(u, F) ∈ GagliardoAmbient α` satisfying `F(x, y) = u(x) - u(y)`
for `(gagliardoMeasure α)`-a.e. `(x, y)`. -/
noncomputable def gagliardoSubmodule (α : ℝ) : Submodule ℝ (GagliardoAmbient α) where
  carrier := {x | ∀ᵐ p : ℝ × ℝ ∂gagliardoMeasure α,
    ((WithLp.ofLp x).2 : ℝ × ℝ → ℝ) p =
      ((WithLp.ofLp x).1 : ℝ → ℝ) p.1 - ((WithLp.ofLp x).1 : ℝ → ℝ) p.2}
  zero_mem' := by
    have h0 : ((0 : L2R) : ℝ → ℝ) =ᵐ[volume] 0 := Lp.coeFn_zero ℝ 2 volume
    have hF0 : ((0 : L2Gagliardo α) : ℝ × ℝ → ℝ) =ᵐ[gagliardoMeasure α] 0 :=
      Lp.coeFn_zero ℝ 2 (gagliardoMeasure α)
    filter_upwards [hF0, ae_fst_gagliardoMeasure h0, ae_snd_gagliardoMeasure h0]
      with p hF h1 h2
    change ((0 : L2Gagliardo α) : ℝ × ℝ → ℝ) p =
      ((0 : L2R) : ℝ → ℝ) p.1 - ((0 : L2R) : ℝ → ℝ) p.2
    rw [hF, h1, h2, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply, sub_zero]
  add_mem' := by
    intro x y hx hy
    have hx1 : ∀ᵐ p : ℝ × ℝ ∂gagliardoMeasure α,
        ((WithLp.ofLp x).2 : ℝ × ℝ → ℝ) p =
          ((WithLp.ofLp x).1 : ℝ → ℝ) p.1 - ((WithLp.ofLp x).1 : ℝ → ℝ) p.2 := hx
    have hy1 : ∀ᵐ p : ℝ × ℝ ∂gagliardoMeasure α,
        ((WithLp.ofLp y).2 : ℝ × ℝ → ℝ) p =
          ((WithLp.ofLp y).1 : ℝ → ℝ) p.1 - ((WithLp.ofLp y).1 : ℝ → ℝ) p.2 := hy
    have hadd_u := Lp.coeFn_add (WithLp.ofLp x).1 (WithLp.ofLp y).1
    have hadd_F := Lp.coeFn_add (WithLp.ofLp x).2 (WithLp.ofLp y).2
    filter_upwards [hx1, hy1, hadd_F, ae_fst_gagliardoMeasure hadd_u,
      ae_snd_gagliardoMeasure hadd_u] with p hxp hyp hF h1 h2
    change (((WithLp.ofLp x).2 + (WithLp.ofLp y).2 : L2Gagliardo α) : ℝ × ℝ → ℝ) p =
      (((WithLp.ofLp x).1 + (WithLp.ofLp y).1 : L2R) : ℝ → ℝ) p.1 -
        (((WithLp.ofLp x).1 + (WithLp.ofLp y).1 : L2R) : ℝ → ℝ) p.2
    rw [hF, h1, h2, Pi.add_apply, Pi.add_apply, Pi.add_apply, hxp, hyp]
    ring
  smul_mem' := by
    intro c x hx
    have hx1 : ∀ᵐ p : ℝ × ℝ ∂gagliardoMeasure α,
        ((WithLp.ofLp x).2 : ℝ × ℝ → ℝ) p =
          ((WithLp.ofLp x).1 : ℝ → ℝ) p.1 - ((WithLp.ofLp x).1 : ℝ → ℝ) p.2 := hx
    have hsm_u := Lp.coeFn_smul c (WithLp.ofLp x).1
    have hsm_F := Lp.coeFn_smul c (WithLp.ofLp x).2
    filter_upwards [hx1, hsm_F, ae_fst_gagliardoMeasure hsm_u,
      ae_snd_gagliardoMeasure hsm_u] with p hxp hF h1 h2
    change ((c • (WithLp.ofLp x).2 : L2Gagliardo α) : ℝ × ℝ → ℝ) p =
      ((c • (WithLp.ofLp x).1 : L2R) : ℝ → ℝ) p.1 -
        ((c • (WithLp.ofLp x).1 : L2R) : ℝ → ℝ) p.2
    rw [hF, h1, h2, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, hxp]
    ring

/-- The Gagliardo graph subspace `gagliardoSubmodule α` is closed in `GagliardoAmbient α`. -/
theorem isClosed_gagliardoSubmodule (α : ℝ) :
    IsClosed (gagliardoSubmodule α : Set (GagliardoAmbient α)) := by
  refine IsSeqClosed.isClosed fun seq lim hmem htend => ?_
  have hu_tend :
      Tendsto (fun n : ℕ => (WithLp.ofLp (seq n)).1) atTop (𝓝 (WithLp.ofLp lim).1) :=
    continuous_fst.continuousAt.tendsto.comp
      ((WithLp.prod_continuous_ofLp 2 L2R (L2Gagliardo α)).continuousAt.tendsto.comp htend)
  have hF_tend :
      Tendsto (fun n : ℕ => (WithLp.ofLp (seq n)).2) atTop (𝓝 (WithLp.ofLp lim).2) :=
    continuous_snd.continuousAt.tendsto.comp
      ((WithLp.prod_continuous_ofLp 2 L2R (L2Gagliardo α)).continuousAt.tendsto.comp htend)
  have hu_meas :
      TendstoInMeasure (volume : Measure ℝ)
        (fun n : ℕ => ((WithLp.ofLp (seq n)).1 : ℝ → ℝ)) atTop
        ((WithLp.ofLp lim).1 : ℝ → ℝ) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
    have heq :
        (fun n : ℕ =>
            eLpNorm (((WithLp.ofLp (seq n)).1 : ℝ → ℝ) - ((WithLp.ofLp lim).1 : ℝ → ℝ)) 2
              (volume : Measure ℝ)) =
          fun n : ℕ => ENNReal.ofReal (dist (WithLp.ofLp (seq n)).1 (WithLp.ofLp lim).1) := by
      funext n
      rw [← Lp.edist_def, Lp.edist_dist]
    rw [heq]
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_iff_dist_tendsto_zero.mp hu_tend)
  obtain ⟨φ, hφ_mono, hφ_ae⟩ := hu_meas.exists_seq_tendsto_ae
  have hF_meas :
      TendstoInMeasure (gagliardoMeasure α)
        (fun k : ℕ => ((WithLp.ofLp (seq (φ k))).2 : ℝ × ℝ → ℝ)) atTop
        ((WithLp.ofLp lim).2 : ℝ × ℝ → ℝ) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
    have heq :
        (fun k : ℕ =>
            eLpNorm
              (((WithLp.ofLp (seq (φ k))).2 : ℝ × ℝ → ℝ) - ((WithLp.ofLp lim).2 : ℝ × ℝ → ℝ))
              2 (gagliardoMeasure α)) =
          fun k : ℕ =>
            ENNReal.ofReal (dist (WithLp.ofLp (seq (φ k))).2 (WithLp.ofLp lim).2) := by
      funext k
      rw [← Lp.edist_def, Lp.edist_dist]
    rw [heq]
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_iff_dist_tendsto_zero.mp (hF_tend.comp hφ_mono.tendsto_atTop))
  obtain ⟨ψ, hψ_mono, hψ_ae⟩ := hF_meas.exists_seq_tendsto_ae
  have hae_rel :
      ∀ᵐ p : ℝ × ℝ ∂gagliardoMeasure α, ∀ j : ℕ,
        ((WithLp.ofLp (seq (φ (ψ j)))).2 : ℝ × ℝ → ℝ) p =
          ((WithLp.ofLp (seq (φ (ψ j)))).1 : ℝ → ℝ) p.1 -
            ((WithLp.ofLp (seq (φ (ψ j)))).1 : ℝ → ℝ) p.2 :=
    ae_all_iff.mpr fun j => hmem (φ (ψ j))
  change ∀ᵐ p : ℝ × ℝ ∂gagliardoMeasure α,
    ((WithLp.ofLp lim).2 : ℝ × ℝ → ℝ) p =
      ((WithLp.ofLp lim).1 : ℝ → ℝ) p.1 - ((WithLp.ofLp lim).1 : ℝ → ℝ) p.2
  filter_upwards [hae_rel, hψ_ae, ae_fst_gagliardoMeasure hφ_ae,
    ae_snd_gagliardoMeasure hφ_ae] with p hp_rel hpF hp1 hp2
  have hp1' :
      Tendsto (fun j : ℕ => ((WithLp.ofLp (seq (φ (ψ j)))).1 : ℝ → ℝ) p.1) atTop
        (𝓝 (((WithLp.ofLp lim).1 : ℝ → ℝ) p.1)) :=
    hp1.comp hψ_mono.tendsto_atTop
  have hp2' :
      Tendsto (fun j : ℕ => ((WithLp.ofLp (seq (φ (ψ j)))).1 : ℝ → ℝ) p.2) atTop
        (𝓝 (((WithLp.ofLp lim).1 : ℝ → ℝ) p.2)) :=
    hp2.comp hψ_mono.tendsto_atTop
  have hsub :
      Tendsto (fun j : ℕ => ((WithLp.ofLp (seq (φ (ψ j)))).2 : ℝ × ℝ → ℝ) p) atTop
        (𝓝 (((WithLp.ofLp lim).1 : ℝ → ℝ) p.1 - ((WithLp.ofLp lim).1 : ℝ → ℝ) p.2)) :=
    (hp1'.sub hp2').congr fun j => (hp_rel j).symm
  exact tendsto_nhds_unique hpF hsub

/-- Concrete fractional Sobolev Hilbert space `H^(α / 2)(ℝ)` realized as the closed Gagliardo
graph subspace inside `L²(ℝ; ℝ) × L²(ℝ × ℝ; gagliardoMeasure α)`. -/
noncomputable abbrev GagliardoSpace (α : ℝ) := ↥(gagliardoSubmodule α)

/-- Completeness of `GagliardoSpace α`, inherited from closedness in `GagliardoAmbient α`. -/
noncomputable instance instCompleteSpaceGagliardoSpace (α : ℝ) :
    CompleteSpace (GagliardoSpace α) :=
  (isClosed_gagliardoSubmodule α).completeSpace_coe

/-- Continuous linear map extracting the `L²(ℝ; ℝ)` component of `u : GagliardoSpace α`. -/
noncomputable def gagliardoL2Part (α : ℝ) : GagliardoSpace α →L[ℝ] L2R :=
  (ContinuousLinearMap.fst ℝ L2R (L2Gagliardo α)).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ L2R (L2Gagliardo α)).toContinuousLinearMap.comp
      (gagliardoSubmodule α).subtypeL)

/-- Continuous linear map extracting the Gagliardo difference-quotient component of
`u : GagliardoSpace α`. -/
noncomputable def gagliardoDiffPart (α : ℝ) : GagliardoSpace α →L[ℝ] L2Gagliardo α :=
  (ContinuousLinearMap.snd ℝ L2R (L2Gagliardo α)).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ L2R (L2Gagliardo α)).toContinuousLinearMap.comp
      (gagliardoSubmodule α).subtypeL)

/-- Unfolding the squared Hilbert norm on `GagliardoSpace α`:
`‖u‖^2 = ‖u_L2‖^2 + ‖u_diff‖^2`. -/
theorem norm_sq_gagliardoSpace (α : ℝ) (u : GagliardoSpace α) :
    ‖u‖ ^ 2 = ‖gagliardoL2Part α u‖ ^ 2 + ‖gagliardoDiffPart α u‖ ^ 2 := by
  change ‖(u : GagliardoAmbient α)‖ ^ 2 =
    ‖(WithLp.ofLp (u : GagliardoAmbient α)).1‖ ^ 2 +
      ‖(WithLp.ofLp (u : GagliardoAmbient α)).2‖ ^ 2
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rfl

/-- Unfolding the Hilbert inner product on `GagliardoSpace α`. -/
theorem inner_gagliardoSpace (α : ℝ) (u v : GagliardoSpace α) :
    ⟪u, v⟫_ℝ = ⟪gagliardoL2Part α u, gagliardoL2Part α v⟫_ℝ +
      ⟪gagliardoDiffPart α u, gagliardoDiffPart α v⟫_ℝ :=
  rfl

/-! ### 3. Concrete Gagliardo Dirichlet form and Beurling–Deny Markov criteria -/

/-- **Concrete Fractional Dirichlet Form `B^α` on `GagliardoSpace α`**:
`B^α(u, v) = (C(α) / 2) ∫∫ ((u(x) - u(y))(v(x) - v(y))) / |x - y|^(1 + α) dx dy`. -/
noncomputable def gagliardoForm (α : ℝ) : SymmetricAccretiveForm (GagliardoSpace α) :=
  symmetricAccretiveFormOfSqrt (gagliardoDiffPart α) (fun x y : L2Gagliardo α => ⟪x, y⟫_ℝ)
    (fun x y => real_inner_comm y x) (fun _ => real_inner_self_nonneg)
    (fun x y => by rw [sq]; exact real_inner_mul_inner_self_le x y)

/-- Pointwise `1`-Lipschitz modulus map `t ↦ |t|` on `ℝ`. -/
theorem lipschitzWith_abs_real : LipschitzWith 1 (abs : ℝ → ℝ) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_sub_abs_le_abs_sub a b

/-- Pointwise `1`-Lipschitz unit-truncation map `t ↦ min t 1` on `ℝ`. -/
theorem lipschitzWith_min_one_real : LipschitzWith 1 (fun t : ℝ => min t 1) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_min_one_sub_min_one_le a b

/-- Lift a `1`-Lipschitz normal contraction `φ : ℝ → ℝ` (`φ 0 = 0`) into `GagliardoSpace α`. -/
noncomputable def gagliardoCompLip (α : ℝ) {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ) (hφ0 : φ 0 = 0)
    (u : GagliardoSpace α) : GagliardoSpace α :=
  let uL2 : L2R := hφ.compLp hφ0 (gagliardoL2Part α u)
  let diffFn : ℝ × ℝ → ℝ := fun p => (uL2 : ℝ → ℝ) p.1 - (uL2 : ℝ → ℝ) p.2
  have hq1 : QuasiMeasurePreserving Prod.fst (gagliardoMeasure α) (volume : Measure ℝ) :=
    Measure.quasiMeasurePreserving_fst.mono_left (gagliardoMeasure_ac α)
  have hq2 : QuasiMeasurePreserving Prod.snd (gagliardoMeasure α) (volume : Measure ℝ) :=
    Measure.quasiMeasurePreserving_snd.mono_left (gagliardoMeasure_ac α)
  have hmeas : AEStronglyMeasurable diffFn (gagliardoMeasure α) :=
    ((Lp.aestronglyMeasurable uL2).comp_quasiMeasurePreserving hq1).sub
      ((Lp.aestronglyMeasurable uL2).comp_quasiMeasurePreserving hq2)
  have hmem_diff : MemLp diffFn 2 (gagliardoMeasure α) := by
    refine (Lp.memLp (gagliardoDiffPart α u)).mono hmeas ?_
    have hcomp := hφ.coeFn_compLp hφ0 (gagliardoL2Part α u)
    filter_upwards [u.2, ae_fst_gagliardoMeasure hcomp, ae_snd_gagliardoMeasure hcomp]
      with p hp h1 h2
    have h1' : (uL2 : ℝ → ℝ) p.1 = φ ((gagliardoL2Part α u : ℝ → ℝ) p.1) := h1
    have h2' : (uL2 : ℝ → ℝ) p.2 = φ ((gagliardoL2Part α u : ℝ → ℝ) p.2) := h2
    have hp' : (gagliardoDiffPart α u : ℝ × ℝ → ℝ) p =
        (gagliardoL2Part α u : ℝ → ℝ) p.1 - (gagliardoL2Part α u : ℝ → ℝ) p.2 := hp
    dsimp only [diffFn]
    rw [h1', h2', hp', Real.norm_eq_abs, Real.norm_eq_abs]
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      hφ.dist_le_mul ((gagliardoL2Part α u : ℝ → ℝ) p.1) ((gagliardoL2Part α u : ℝ → ℝ) p.2)
  ⟨WithLp.toLp 2 (uL2, hmem_diff.toLp diffFn), hmem_diff.coeFn_toLp⟩

/-- Lattice modulus normal contraction `u ↦ |u|` on `GagliardoSpace α`. -/
noncomputable def gagliardoAbs (α : ℝ) : GagliardoSpace α → GagliardoSpace α :=
  gagliardoCompLip α lipschitzWith_abs_real abs_zero

/-- Unit-truncation normal contraction `u ↦ u ∧ 1` on `GagliardoSpace α`. -/
noncomputable def gagliardoCapOne (α : ℝ) : GagliardoSpace α → GagliardoSpace α :=
  gagliardoCompLip α lipschitzWith_min_one_real (min_eq_left zero_le_one)

/-- Pointwise a.e. characterization of the `L²` part of `gagliardoCompLip`. -/
theorem coeFn_gagliardoCompLip_l2Part (α : ℝ) {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ)
    (hφ0 : φ 0 = 0) (u : GagliardoSpace α) :
    (gagliardoL2Part α (gagliardoCompLip α hφ hφ0 u) : ℝ → ℝ) =ᵐ[volume]
      fun x => φ ((gagliardoL2Part α u : ℝ → ℝ) x) :=
  hφ.coeFn_compLp hφ0 (gagliardoL2Part α u)

/-- Every normal contraction `gagliardoCompLip α hφ hφ0` contracts the Dirichlet energy
`gagliardoForm α`. -/
theorem gagliardoForm_compLip_le (α : ℝ) {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ) (hφ0 : φ 0 = 0)
    (u : GagliardoSpace α) :
    (gagliardoForm α).form (gagliardoCompLip α hφ hφ0 u) (gagliardoCompLip α hφ hφ0 u) ≤
      (gagliardoForm α).form u u := by
  change ⟪gagliardoDiffPart α (gagliardoCompLip α hφ hφ0 u),
      gagliardoDiffPart α (gagliardoCompLip α hφ hφ0 u)⟫_ℝ ≤
    ⟪gagliardoDiffPart α u, gagliardoDiffPart α u⟫_ℝ
  rw [L2.inner_def, L2.inner_def]
  refine integral_mono_ae ?_ ?_ ?_
  · exact L2.integrable_inner _ _
  · exact L2.integrable_inner _ _
  · have hcomp := coeFn_gagliardoCompLip_l2Part α hφ hφ0 u
    filter_upwards [(gagliardoCompLip α hφ hφ0 u).2, u.2,
      ae_fst_gagliardoMeasure hcomp, ae_snd_gagliardoMeasure hcomp] with p hp_lip hp_u h1 h2
    have hdiff_lip :
        (gagliardoDiffPart α (gagliardoCompLip α hφ hφ0 u) : ℝ × ℝ → ℝ) p =
          φ ((gagliardoL2Part α u : ℝ → ℝ) p.1) - φ ((gagliardoL2Part α u : ℝ → ℝ) p.2) := by
      have hp' : (gagliardoDiffPart α (gagliardoCompLip α hφ hφ0 u) : ℝ × ℝ → ℝ) p =
          (gagliardoL2Part α (gagliardoCompLip α hφ hφ0 u) : ℝ → ℝ) p.1 -
            (gagliardoL2Part α (gagliardoCompLip α hφ hφ0 u) : ℝ → ℝ) p.2 := hp_lip
      rw [hp', h1, h2]
    have hdiff_u :
        (gagliardoDiffPart α u : ℝ × ℝ → ℝ) p =
          (gagliardoL2Part α u : ℝ → ℝ) p.1 - (gagliardoL2Part α u : ℝ → ℝ) p.2 := hp_u
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hdiff_lip, hdiff_u,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    have hdist :
        |φ ((gagliardoL2Part α u : ℝ → ℝ) p.1) - φ ((gagliardoL2Part α u : ℝ → ℝ) p.2)| ≤
          |(gagliardoL2Part α u : ℝ → ℝ) p.1 - (gagliardoL2Part α u : ℝ → ℝ) p.2| := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
        hφ.dist_le_mul ((gagliardoL2Part α u : ℝ → ℝ) p.1) ((gagliardoL2Part α u : ℝ → ℝ) p.2)
    rw [← sq_abs (φ ((gagliardoL2Part α u : ℝ → ℝ) p.1) - φ ((gagliardoL2Part α u : ℝ → ℝ) p.2)),
      ← sq_abs ((gagliardoL2Part α u : ℝ → ℝ) p.1 - (gagliardoL2Part α u : ℝ → ℝ) p.2)]
    exact pow_le_pow_left₀ (abs_nonneg _) hdist 2

/-- **Concrete Beurling–Deny Markov Dirichlet Form on `GagliardoSpace α`**:
for `α ∈ (0, 2)`, the fractional Gagliardo Dirichlet form `gagliardoForm α` satisfies both
Beurling–Deny normal contraction criteria under `gagliardoAbs α` (`u ↦ |u|`) and
`gagliardoCapOne α` (`u ↦ u ∧ 1`).

The proof does not use `_hα`; the hypothesis scopes the statement to `α ∈ (0, 2)`, where
`C(α) > 0` (see `gagliardoWeight_pos`). At `α = 0`, `C(0) = 0` and the form vanishes
identically. -/
@[nolint unusedArguments]
theorem gagliardoForm_isMarkovDirichletForm {α : ℝ} (_hα : FractionalExponent α) :
    IsMarkovDirichletForm (gagliardoForm α) (gagliardoAbs α) (gagliardoCapOne α) where
  form_abs_le := gagliardoForm_compLip_le α lipschitzWith_abs_real abs_zero
  form_capOne_le := gagliardoForm_compLip_le α lipschitzWith_min_one_real (min_eq_left zero_le_one)

/-! ### 4. Concrete restricted exterior-Dirichlet space `H^(α / 2)_0(0, ∞)` -/

/-- Closed linear subspace of `GagliardoSpace α` consisting of functions vanishing a.e. on
`(-∞, 0]`, modeling `H^(α / 2)_0(0, ∞)`. -/
noncomputable def restrictedGagliardoSubmodule (α : ℝ) : Submodule ℝ (GagliardoSpace α) where
  carrier := {u | ∀ᵐ x : ℝ ∂volume, x ≤ 0 → (gagliardoL2Part α u : ℝ → ℝ) x = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℝ 2 volume] with x hx _
    change ((0 : L2R) : ℝ → ℝ) x = 0
    exact hx
  add_mem' := by
    intro u v hu hv
    have hu1 : ∀ᵐ x : ℝ ∂volume, x ≤ 0 → (gagliardoL2Part α u : ℝ → ℝ) x = 0 := hu
    have hv1 : ∀ᵐ x : ℝ ∂volume, x ≤ 0 → (gagliardoL2Part α v : ℝ → ℝ) x = 0 := hv
    filter_upwards [hu1, hv1, Lp.coeFn_add (gagliardoL2Part α u) (gagliardoL2Part α v)]
      with x hux hvx hadd hx
    change ((gagliardoL2Part α u + gagliardoL2Part α v : L2R) : ℝ → ℝ) x = 0
    rw [hadd, Pi.add_apply, hux hx, hvx hx, add_zero]
  smul_mem' := by
    intro c u hu
    have hu1 : ∀ᵐ x : ℝ ∂volume, x ≤ 0 → (gagliardoL2Part α u : ℝ → ℝ) x = 0 := hu
    filter_upwards [hu1, Lp.coeFn_smul c (gagliardoL2Part α u)] with x hux hsm hx
    change ((c • gagliardoL2Part α u : L2R) : ℝ → ℝ) x = 0
    rw [hsm, Pi.smul_apply, hux hx, smul_zero]

/-- Auxiliary restriction map from `GagliardoSpace α` to `L²((-∞, 0]; ℝ)` whose kernel is
`restrictedGagliardoSubmodule α`. -/
noncomputable def restrictedNegMap (α : ℝ) :
    GagliardoSpace α →L[ℝ] Lp (α := ℝ) ℝ 2 ((volume : Measure ℝ).restrict (Iic (0 : ℝ))) :=
  (Lp.LpToLpOfMeasureLeSMul (p := 2) (E := ℝ) (μ := (volume : Measure ℝ).restrict (Iic (0 : ℝ)))
    (ν := (volume : Measure ℝ)) (c := 1) ENNReal.one_ne_top
    (by simpa only [one_smul] using Measure.restrict_le_self)).comp (gagliardoL2Part α)

/-- Closedness of `restrictedGagliardoSubmodule α` via identification with
`LinearMap.ker (restrictedNegMap α)`. -/
theorem isClosed_restrictedGagliardoSubmodule (α : ℝ) :
    IsClosed (restrictedGagliardoSubmodule α : Set (GagliardoSpace α)) := by
  have hker :
      (restrictedGagliardoSubmodule α : Set (GagliardoSpace α)) =
        ((restrictedNegMap α : GagliardoSpace α →ₗ[ℝ]
          Lp (α := ℝ) ℝ 2 ((volume : Measure ℝ).restrict (Iic (0 : ℝ)))).ker :
            Set (GagliardoSpace α)) := by
    ext u
    rw [SetLike.mem_coe, SetLike.mem_coe, LinearMap.mem_ker, Lp.ext_iff]
    change (∀ᵐ x : ℝ ∂volume, x ≤ 0 → (gagliardoL2Part α u : ℝ → ℝ) x = 0) ↔
      (restrictedNegMap α u : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic (0 : ℝ))]
        ((0 : Lp (α := ℝ) ℝ 2 ((volume : Measure ℝ).restrict (Iic (0 : ℝ)))) : ℝ → ℝ)
    have hcoeff :
        (restrictedNegMap α u : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic (0 : ℝ))]
          (gagliardoL2Part α u : ℝ → ℝ) :=
      Lp.coeFn_LpToLpOfMeasureLeSMul _ _ (gagliardoL2Part α u)
    have hzero :
        ((0 : Lp (α := ℝ) ℝ 2 ((volume : Measure ℝ).restrict (Iic (0 : ℝ)))) : ℝ → ℝ) =ᵐ[
            (volume : Measure ℝ).restrict (Iic (0 : ℝ))] 0 :=
      Lp.coeFn_zero ℝ 2 _
    change (∀ᵐ x : ℝ ∂volume, x ∈ Iic (0 : ℝ) → (gagliardoL2Part α u : ℝ → ℝ) x = 0) ↔ _
    rw [← ae_restrict_iff' measurableSet_Iic]
    constructor
    · intro h
      filter_upwards [h, hcoeff, hzero] with x hx hc hz
      rw [hc, hz]
      exact hx
    · intro h
      filter_upwards [h, hcoeff, hzero] with x hx hc hz
      rw [← hc, hx, hz]
      rfl
  rw [hker]
  exact ContinuousLinearMap.isClosed_ker (restrictedNegMap α)

/-- Concrete exterior-Dirichlet fractional Sobolev Hilbert space `H^(α / 2)_0(0, ∞)`. -/
noncomputable abbrev RestrictedGagliardoSpace (α : ℝ) := ↥(restrictedGagliardoSubmodule α)

/-- Completeness instance for `RestrictedGagliardoSpace α`. -/
noncomputable instance instCompleteSpaceRestrictedGagliardoSpace (α : ℝ) :
    CompleteSpace (RestrictedGagliardoSpace α) :=
  (isClosed_restrictedGagliardoSubmodule α).completeSpace_coe

/-- Lift `gagliardoCompLip` into `RestrictedGagliardoSpace α`, preserving vanishing on
`(-∞, 0]`. -/
noncomputable def restrictedGagliardoCompLip (α : ℝ) {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ)
    (hφ0 : φ 0 = 0) (u : RestrictedGagliardoSpace α) : RestrictedGagliardoSpace α :=
  ⟨gagliardoCompLip α hφ hφ0 u.1, by
    filter_upwards [u.2, coeFn_gagliardoCompLip_l2Part α hφ hφ0 u.1] with x hx hcomp hx0
    rw [hcomp, hx hx0, hφ0]⟩

/-- Lattice modulus `u ↦ |u|` on `RestrictedGagliardoSpace α`. -/
noncomputable def restrictedGagliardoAbs (α : ℝ) :
    RestrictedGagliardoSpace α → RestrictedGagliardoSpace α :=
  restrictedGagliardoCompLip α lipschitzWith_abs_real abs_zero

/-- Unit truncation `u ↦ u ∧ 1` on `RestrictedGagliardoSpace α`. -/
noncomputable def restrictedGagliardoCapOne (α : ℝ) :
    RestrictedGagliardoSpace α → RestrictedGagliardoSpace α :=
  restrictedGagliardoCompLip α lipschitzWith_min_one_real (min_eq_left zero_le_one)

/-- **Concrete Restricted Fractional Dirichlet Form `B^α_0` on `RestrictedGagliardoSpace α`**. -/
noncomputable def restrictedGagliardoForm (α : ℝ) :
    SymmetricAccretiveForm (RestrictedGagliardoSpace α) :=
  restrictSymmetricAccretiveForm (gagliardoForm α) Subtype.val

/-- **Concrete Restricted Markov Dirichlet Form**:
for `α ∈ (0, 2)`, `restrictedGagliardoForm α` satisfies both Beurling–Deny Markov conditions on
`RestrictedGagliardoSpace α`. -/
theorem restrictedGagliardoForm_isMarkovDirichletForm {α : ℝ} (hα : FractionalExponent α) :
    IsMarkovDirichletForm (restrictedGagliardoForm α) (restrictedGagliardoAbs α)
      (restrictedGagliardoCapOne α) :=
  restrictedForm_isMarkovDirichletForm (gagliardoForm α) (gagliardoAbs α) (gagliardoCapOne α)
    (gagliardoForm_isMarkovDirichletForm hα) Subtype.val
    (restrictedGagliardoAbs α) (restrictedGagliardoCapOne α)
    (fun _ => rfl) (fun _ => rfl)

/-! ### 4b. Truncated Gagliardo kernel and translation-bound criterion -/

/-- Truncated Gagliardo kernel `C(α) min(h², 1) / (2 |h|^(1+α))`. -/
noncomputable def gagliardoKernel (α h : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (fracLapConstant α / (2 * |h| ^ (1 + α)) * min (h ^ 2) 1)

/-- The truncated Gagliardo kernel is even. -/
theorem gagliardoKernel_neg (α h : ℝ) : gagliardoKernel α (-h) = gagliardoKernel α h := by
  simp only [gagliardoKernel, abs_neg, neg_sq]

/-- The truncated Gagliardo kernel has finite integral over `(0, ∞)` for `α ∈ (0, 2)`:
near `0` it behaves like `h ^ (1 - α)` and near `∞` like `h ^ (-1 - α)`. -/
theorem lintegral_gagliardoKernel_Ioi_lt_top {α : ℝ} (hα : FractionalExponent α) :
    ∫⁻ h in Ioi (0 : ℝ), gagliardoKernel α h < ∞ := by
  have hC : 0 < fracLapConstant α := fracLapConstant_pos hα
  have hα0 : 0 < α := hα.1
  have hα2 : α < 2 := hα.2
  set C := fracLapConstant α with hCdef
  have h1 : ∫⁻ h in Ioc (0 : ℝ) 1, gagliardoKernel α h ≤
      ∫⁻ h in Ioc (0 : ℝ) 1, ENNReal.ofReal (C / 2 * h ^ (1 - α)) := by
    refine setLIntegral_mono' measurableSet_Ioc fun h hh => ?_
    unfold gagliardoKernel
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hpos : 0 < h := hh.1
    have hmin : min (h ^ 2) 1 = h ^ 2 := min_eq_left (by nlinarith [hh.2])
    have hpow : h ^ (1 - α) = h ^ 2 / h ^ (1 + α) := by
      rw [show (1 - α) = 2 - (1 + α) by ring, Real.rpow_sub hpos]
      norm_cast
    rw [abs_of_pos hpos, hmin, hpow]
    ring
  have h2 : ∫⁻ h in Ioi (1 : ℝ), gagliardoKernel α h ≤
      ∫⁻ h in Ioi (1 : ℝ), ENNReal.ofReal (C / 2 * h ^ (-(1 + α))) := by
    refine setLIntegral_mono' measurableSet_Ioi fun h hh => ?_
    unfold gagliardoKernel
    refine ENNReal.ofReal_le_ofReal ?_
    have hpos : 0 < h := lt_trans one_pos hh
    have hpw : 0 < h ^ (1 + α) := Real.rpow_pos_of_pos hpos _
    rw [abs_of_pos hpos, Real.rpow_neg hpos.le]
    calc C / (2 * h ^ (1 + α)) * min (h ^ 2) 1 ≤ C / (2 * h ^ (1 + α)) * 1 :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = C / 2 * (h ^ (1 + α))⁻¹ := by field_simp
  have i1 : IntegrableOn (fun h : ℝ => C / 2 * h ^ (1 - α)) (Ioc (0 : ℝ) 1) :=
    ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (by linarith : -1 < 1 - α)).1).const_mul _
  have i2 : IntegrableOn (fun h : ℝ => C / 2 * h ^ (-(1 + α))) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -(1 + α) < -1) one_pos).const_mul _
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  calc ∫⁻ h in Ioc (0 : ℝ) 1 ∪ Ioi 1, gagliardoKernel α h
      ≤ (∫⁻ h in Ioc (0 : ℝ) 1, gagliardoKernel α h) +
        ∫⁻ h in Ioi (1 : ℝ), gagliardoKernel α h :=
        lintegral_union_le _ _ _
    _ < ∞ := ENNReal.add_lt_top.mpr
        ⟨lt_of_le_of_lt h1 i1.setLIntegral_lt_top, lt_of_le_of_lt h2 i2.setLIntegral_lt_top⟩

/-- The truncated Gagliardo kernel has finite integral over `ℝ` for `α ∈ (0, 2)`. -/
theorem lintegral_gagliardoKernel_lt_top {α : ℝ} (hα : FractionalExponent α) :
    ∫⁻ h, gagliardoKernel α h < ∞ := by
  rw [← lintegral_add_compl _ (measurableSet_Ioi (a := (0 : ℝ))), compl_Ioi]
  have hneg : ∫⁻ h in Iic (0 : ℝ), gagliardoKernel α h =
      ∫⁻ h in Ioi (0 : ℝ), gagliardoKernel α h := by
    have := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.neg ℝ).measurableEmbedding (gagliardoKernel α) (Ici (0 : ℝ))
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Ici 0 = Iic 0 := by ext x; simp
    simp only [gagliardoKernel_neg] at this
    rw [hpre] at this
    rw [this]
    exact setLIntegral_congr Ioi_ae_eq_Ici.symm
  rw [hneg]
  exact ENNReal.add_lt_top.mpr ⟨lintegral_gagliardoKernel_Ioi_lt_top hα,
    lintegral_gagliardoKernel_Ioi_lt_top hα⟩

/-- Measurability of the truncated Gagliardo kernel. -/
theorem measurable_gagliardoKernel (α : ℝ) : Measurable (gagliardoKernel α) := by
  unfold gagliardoKernel
  fun_prop

/-- **Gagliardo energy as an `L²` translation modulus**: for measurable `u`,
`∬ w(x - y) (u(x) - u(y))² dx dy = ∫ w(h) (∫ (u(y + h) - u(y))² dy) dh`, where
`w(h) = C(α) / (2 |h|^(1 + α))`. This is Tonelli together with the shear `(x, y) ↦ (x - y, y)`;
it is an identity in `[0, ∞]` and needs no range hypothesis on `α`. -/
theorem lintegral_gagliardo_energy_eq (α : ℝ) {u : ℝ → ℝ} (hu : Measurable u) :
    ∫⁻ p : ℝ × ℝ, gagliardoWeight α p * ENNReal.ofReal ((u p.1 - u p.2) ^ 2)
      ∂((volume : Measure ℝ).prod volume) =
      ∫⁻ h : ℝ, gagliardoWeight α (h, 0) * ∫⁻ y, ENNReal.ofReal ((u (y + h) - u y) ^ 2) := by
  have hdiff : Measurable fun p : ℝ × ℝ => ENNReal.ofReal ((u p.1 - u p.2) ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (((hu.comp measurable_fst).sub (hu.comp measurable_snd)).pow_const 2)
  have hf : Measurable fun p : ℝ × ℝ =>
      gagliardoWeight α p * ENNReal.ofReal ((u p.1 - u p.2) ^ 2) :=
    (measurable_gagliardoWeight α).mul hdiff
  have hWm : Measurable fun h : ℝ => gagliardoWeight α (h, 0) :=
    (measurable_gagliardoWeight α).comp (measurable_id.prodMk measurable_const)
  set G : ℝ → ℝ → ℝ≥0∞ :=
    fun y h => gagliardoWeight α (h, 0) * ENNReal.ofReal ((u (h + y) - u y) ^ 2) with hG
  have hGm : Measurable (Function.uncurry G) := by
    simp only [hG]
    refine hWm.comp measurable_snd |>.mul (ENNReal.measurable_ofReal.comp ?_)
    exact ((hu.comp (measurable_snd.add measurable_fst)).sub (hu.comp measurable_fst)).pow_const 2
  have step1 : ∫⁻ p : ℝ × ℝ, gagliardoWeight α p * ENNReal.ofReal ((u p.1 - u p.2) ^ 2)
        ∂((volume : Measure ℝ).prod volume) = ∫⁻ y, ∫⁻ h, G y h := by
    rw [lintegral_prod_symm _ hf.aemeasurable]
    refine lintegral_congr fun y => ?_
    rw [← lintegral_sub_right_eq_self (fun h => G y h) y]
    refine lintegral_congr fun x => ?_
    simp only [hG, gagliardoWeight, sub_zero, sub_add_cancel]
  rw [step1, lintegral_lintegral_swap hGm.aemeasurable]
  refine lintegral_congr fun h => ?_
  have hm : Measurable fun y : ℝ => ENNReal.ofReal ((u (h + y) - u y) ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (((hu.comp (measurable_const.add measurable_id)).sub hu).pow_const 2)
  simp only [hG]
  rw [lintegral_const_mul _ hm]
  simp only [add_comm h]

/-- **Translation-bound criterion for membership in `H^(α / 2)(ℝ)`**: if `u` is measurable and
`∫ |u(y + h) - u(y)|² dy ≤ K min(h², 1)` for all `h`, then the Gagliardo energy of `u` is finite.
It combines `lintegral_gagliardo_energy_eq` with `lintegral_gagliardoKernel_lt_top`. -/
theorem lintegral_gagliardo_diff_sq_lt_top {α : ℝ} (hα : FractionalExponent α) {u : ℝ → ℝ}
    (hu : Measurable u) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (htrans : ∀ h : ℝ, ∫⁻ y, ENNReal.ofReal ((u (y + h) - u y) ^ 2) ≤
      K * ENNReal.ofReal (min (h ^ 2) 1)) :
    ∫⁻ p : ℝ × ℝ, gagliardoWeight α p * ENNReal.ofReal ((u p.1 - u p.2) ^ 2)
      ∂((volume : Measure ℝ).prod volume) < ∞ := by
  rw [lintegral_gagliardo_energy_eq α hu]
  have step : ∀ h : ℝ, gagliardoWeight α (h, 0) * ∫⁻ y, ENNReal.ofReal ((u (y + h) - u y) ^ 2) ≤
      K * gagliardoKernel α h := by
    intro h
    calc gagliardoWeight α (h, 0) * ∫⁻ y, ENNReal.ofReal ((u (y + h) - u y) ^ 2)
        ≤ gagliardoWeight α (h, 0) * (K * ENNReal.ofReal (min (h ^ 2) 1)) := by
          gcongr; exact htrans h
      _ = K * gagliardoKernel α h := by
          have hnn : 0 ≤ fracLapConstant α / (2 * |h| ^ (1 + α)) := by
            have hC : 0 < fracLapConstant α := fracLapConstant_pos hα
            positivity
          simp only [gagliardoKernel, gagliardoWeight, sub_zero, ENNReal.ofReal_mul hnn]
          ring
  calc ∫⁻ h : ℝ, gagliardoWeight α (h, 0) * ∫⁻ y, ENNReal.ofReal ((u (y + h) - u y) ^ 2)
      ≤ ∫⁻ h, K * gagliardoKernel α h := lintegral_mono step
    _ = K * ∫⁻ h, gagliardoKernel α h := lintegral_const_mul _ (measurable_gagliardoKernel α)
    _ < ∞ := ENNReal.mul_lt_top hK.lt_top (lintegral_gagliardoKernel_lt_top hα)

/-! ### 5. Non-vacuity witness: the tent function in `H^(α / 2)_0(0, ∞)` -/

/-- The tent function `max 0 (1 - |x - 1|)`, supported on `[0, 2]`. -/
noncomputable def gagliardoTent (x : ℝ) : ℝ := max 0 (1 - |x - 1|)

/-- The tent function is continuous. -/
theorem continuous_gagliardoTent : Continuous gagliardoTent := by
  unfold gagliardoTent; fun_prop

/-- The tent function is nonnegative. -/
theorem gagliardoTent_nonneg (x : ℝ) : 0 ≤ gagliardoTent x := le_max_left _ _

/-- The tent function is bounded by `1`. -/
theorem gagliardoTent_le_one (x : ℝ) : gagliardoTent x ≤ 1 :=
  max_le zero_le_one (by linarith [abs_nonneg (x - 1)])

/-- The tent function vanishes outside `(0, 2)`. -/
theorem gagliardoTent_eq_zero {x : ℝ} (hx : x ∉ Ioo (0 : ℝ) 2) : gagliardoTent x = 0 := by
  have h1 : 1 ≤ |x - 1| := by
    by_contra hlt
    replace hlt := not_le.mp hlt
    rw [abs_lt] at hlt
    exact hx ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
  exact max_eq_left (by linarith)

/-- The tent function is `1`-Lipschitz. -/
theorem abs_gagliardoTent_sub_le (x y : ℝ) : |gagliardoTent x - gagliardoTent y| ≤ |x - y| := by
  unfold gagliardoTent
  calc |max 0 (1 - |x - 1|) - max 0 (1 - |y - 1|)|
      ≤ max |(0 : ℝ) - 0| |(1 - |x - 1|) - (1 - |y - 1|)| := abs_max_sub_max_le_max _ _ _ _
    _ ≤ |x - y| := by
        refine max_le (by simp) ?_
        have := abs_abs_sub_abs_le_abs_sub (y - 1) (x - 1)
        rw [show (1 - |x - 1|) - (1 - |y - 1|) = |y - 1| - |x - 1| by ring]
        calc |(|y - 1| - |x - 1|)| ≤ |(y - 1) - (x - 1)| := this
          _ = |x - y| := by rw [show (y - 1) - (x - 1) = -(x - y) by ring, abs_neg]

/-- Pointwise bound `(tent x - tent y)² ≤ min((x - y)², 1)`. -/
theorem gagliardoTent_sq_sub_le (x y : ℝ) :
    (gagliardoTent x - gagliardoTent y) ^ 2 ≤ min ((x - y) ^ 2) 1 := by
  refine le_min ?_ ?_
  · have h := abs_gagliardoTent_sub_le x y
    rw [← sq_abs (x - y)]
    exact sq_le_sq' (by linarith [abs_le.mp h]) (by linarith [abs_le.mp h, le_abs_self (x - y)])
  · have h0x := gagliardoTent_nonneg x
    have h1x := gagliardoTent_le_one x
    have h0y := gagliardoTent_nonneg y
    have h1y := gagliardoTent_le_one y
    nlinarith

/-- Translation estimate for the tent function:
`∫ |tent(y + h) - tent(y)|² dy ≤ 4 min(h², 1)`. -/
theorem gagliardoTent_translation (h : ℝ) :
    ∫⁻ y, ENNReal.ofReal ((gagliardoTent (y + h) - gagliardoTent y) ^ 2) ≤
      4 * ENNReal.ofReal (min (h ^ 2) 1) := by
  set S : Set ℝ := Ioo 0 2 ∪ Ioo (-h) (2 - h) with hS
  have hpt : ∀ y, ENNReal.ofReal ((gagliardoTent (y + h) - gagliardoTent y) ^ 2) ≤
      S.indicator (fun _ => ENNReal.ofReal (min (h ^ 2) 1)) y := by
    intro y
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy]
      refine ENNReal.ofReal_le_ofReal ?_
      simpa using gagliardoTent_sq_sub_le (y + h) y
    · rw [Set.indicator_of_notMem hy]
      have hy1 : y ∉ Ioo (0 : ℝ) 2 := fun hh => hy (Or.inl hh)
      have hy2 : y + h ∉ Ioo (0 : ℝ) 2 := fun hh =>
        hy (Or.inr ⟨by linarith [hh.1], by linarith [hh.2]⟩)
      rw [gagliardoTent_eq_zero hy1, gagliardoTent_eq_zero hy2]
      simp
  calc ∫⁻ y, ENNReal.ofReal ((gagliardoTent (y + h) - gagliardoTent y) ^ 2)
      ≤ ∫⁻ y, S.indicator (fun _ => ENNReal.ofReal (min (h ^ 2) 1)) y := lintegral_mono hpt
    _ = ENNReal.ofReal (min (h ^ 2) 1) * volume S :=
        lintegral_indicator_const (measurableSet_Ioo.union measurableSet_Ioo) _
    _ ≤ ENNReal.ofReal (min (h ^ 2) 1) * 4 := by
        gcongr
        calc volume S ≤ volume (Ioo (0 : ℝ) 2) + volume (Ioo (-h) (2 - h)) := measure_union_le _ _
          _ = ENNReal.ofReal 2 + ENNReal.ofReal 2 := by
              rw [Real.volume_Ioo, Real.volume_Ioo]; congr 2 <;> ring_nf
          _ = 4 := by
              rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
    _ = 4 * ENNReal.ofReal (min (h ^ 2) 1) := mul_comm _ _


/-- The squared tent difference quotient is integrable for `gagliardoMeasure α`. -/
theorem integrable_gagliardoTent_diff_sq {α : ℝ} (hα : FractionalExponent α) :
    Integrable (fun p : ℝ × ℝ => (gagliardoTent p.1 - gagliardoTent p.2) ^ 2)
      (gagliardoMeasure α) := by
  have hcont := continuous_gagliardoTent
  refine ⟨((hcont.comp continuous_fst).sub (hcont.comp continuous_snd)).pow 2
    |>.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => sq_nonneg _)]
  have hg : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal ((gagliardoTent p.1 - gagliardoTent p.2) ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (((hcont.measurable.comp measurable_fst).sub
        (hcont.measurable.comp measurable_snd)).pow_const 2)
  unfold gagliardoMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_gagliardoWeight α) hg]
  exact lintegral_gagliardo_diff_sq_lt_top hα hcont.measurable (K := 4) (by norm_num)
    gagliardoTent_translation


/-- The tent function lies in `L²(ℝ)`. -/
theorem memLp_gagliardoTent : MemLp gagliardoTent 2 (volume : Measure ℝ) :=
  continuous_gagliardoTent.memLp_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 2))
      fun _ hx => gagliardoTent_eq_zero fun h => hx ⟨h.1.le, h.2.le⟩)

/-- The tent function as an element of `L²(ℝ; ℝ)`. -/
noncomputable def gagliardoTentL2 : L2R := memLp_gagliardoTent.toLp gagliardoTent

/-- The difference quotient `(x, y) ↦ tent x - tent y` lies in `L²(gagliardoMeasure α)`. -/
theorem memLp_gagliardoTentDiff {α : ℝ} (hα : FractionalExponent α) :
    MemLp (fun p : ℝ × ℝ => gagliardoTent p.1 - gagliardoTent p.2) 2 (gagliardoMeasure α) :=
  (memLp_two_iff_integrable_sq
    ((continuous_gagliardoTent.comp continuous_fst).sub
      (continuous_gagliardoTent.comp continuous_snd)).aestronglyMeasurable).2
    (integrable_gagliardoTent_diff_sq hα)

/-- The tent difference quotient as an element of `L²(ℝ × ℝ; gagliardoMeasure α)`. -/
noncomputable def gagliardoTentDiffL2 {α : ℝ} (hα : FractionalExponent α) : L2Gagliardo α :=
  (memLp_gagliardoTentDiff hα).toLp _

/-- The pair (tent, tent difference quotient) lies in the Gagliardo graph subspace. -/
theorem gagliardoTent_mem {α : ℝ} (hα : FractionalExponent α) :
    (WithLp.toLp 2 (gagliardoTentL2, gagliardoTentDiffL2 hα) : GagliardoAmbient α) ∈
      gagliardoSubmodule α := by
  change ∀ᵐ p : ℝ × ℝ ∂gagliardoMeasure α, (gagliardoTentDiffL2 hα : ℝ × ℝ → ℝ) p =
    (gagliardoTentL2 : ℝ → ℝ) p.1 - (gagliardoTentL2 : ℝ → ℝ) p.2
  filter_upwards [(memLp_gagliardoTentDiff hα).coeFn_toLp,
    ae_fst_gagliardoMeasure memLp_gagliardoTent.coeFn_toLp,
    ae_snd_gagliardoMeasure memLp_gagliardoTent.coeFn_toLp] with p h1 h2 h3
  have h1' : (gagliardoTentDiffL2 hα : ℝ × ℝ → ℝ) p = gagliardoTent p.1 - gagliardoTent p.2 := h1
  have h2' : (gagliardoTentL2 : ℝ → ℝ) p.1 = gagliardoTent p.1 := h2
  have h3' : (gagliardoTentL2 : ℝ → ℝ) p.2 = gagliardoTent p.2 := h3
  rw [h1', h2', h3']

/-- The tent function as an element of `H^(α / 2)(ℝ)`. -/
noncomputable def gagliardoTentSpace {α : ℝ} (hα : FractionalExponent α) : GagliardoSpace α :=
  ⟨_, gagliardoTent_mem hα⟩

/-- The tent function vanishes on `(-∞, 0]`, so it lies in `H^(α / 2)_0(0, ∞)`. -/
theorem gagliardoTentSpace_mem_restricted {α : ℝ} (hα : FractionalExponent α) :
    gagliardoTentSpace hα ∈ restrictedGagliardoSubmodule α := by
  change ∀ᵐ y : ℝ ∂volume, y ≤ 0 → (gagliardoTentL2 : ℝ → ℝ) y = 0
  filter_upwards [memLp_gagliardoTent.coeFn_toLp] with y hy hy0
  rw [gagliardoTentL2, hy]
  exact gagliardoTent_eq_zero fun h => absurd h.1 (not_lt.mpr hy0)

/-- The tent element of `H^(α / 2)_0(0, ∞)`. -/
noncomputable def gagliardoTentRestricted {α : ℝ} (hα : FractionalExponent α) :
    RestrictedGagliardoSpace α :=
  ⟨gagliardoTentSpace hα, gagliardoTentSpace_mem_restricted hα⟩

/-- The tent element of the exterior-Dirichlet space is nonzero. -/
theorem gagliardoTentRestricted_ne_zero {α : ℝ} (hα : FractionalExponent α) :
    gagliardoTentRestricted hα ≠ 0 := by
  intro h0
  have h1 : gagliardoTentL2 = 0 := by
    have h' : gagliardoL2Part α ((0 : RestrictedGagliardoSpace α) : GagliardoSpace α) = 0 := by
      simp
    exact (congrArg (fun v : RestrictedGagliardoSpace α => gagliardoL2Part α v.1) h0).trans h'
  have h2 : (gagliardoTent : ℝ → ℝ) =ᵐ[volume] fun _ => 0 := by
    filter_upwards [memLp_gagliardoTent.coeFn_toLp] with y hy
    have hy' : (gagliardoTentL2 : ℝ → ℝ) y = gagliardoTent y := hy
    calc gagliardoTent y = (gagliardoTentL2 : ℝ → ℝ) y := hy'.symm
      _ = ((0 : L2R) : ℝ → ℝ) y := by rw [h1]
      _ = 0 := by simp
  have h4 := congrFun
    ((Continuous.ae_eq_iff_eq (volume : Measure ℝ) continuous_gagliardoTent
      continuous_const).mp h2) 1
  have h5 : gagliardoTent 1 = 1 := by simp [gagliardoTent]
  rw [h5] at h4
  exact one_ne_zero h4

/-- The tent difference quotient is a nonzero element of `L²(gagliardoMeasure α)`. -/
theorem gagliardoTentDiffL2_ne_zero {α : ℝ} (hα : FractionalExponent α) :
    gagliardoTentDiffL2 hα ≠ 0 := by
  intro h0
  set F : ℝ × ℝ → ℝ := fun p => gagliardoTent p.1 - gagliardoTent p.2 with hFdef
  have hFc : Continuous F :=
    (continuous_gagliardoTent.comp continuous_fst).sub
      (continuous_gagliardoTent.comp continuous_snd)
  have hae : F =ᵐ[gagliardoMeasure α] 0 := by
    filter_upwards [(memLp_gagliardoTentDiff hα).coeFn_toLp, Lp.coeFn_zero ℝ 2 (gagliardoMeasure α)]
      with p h1 h2
    have h1' : (gagliardoTentDiffL2 hα : ℝ × ℝ → ℝ) p = F p := h1
    rw [← h1', h0]
    simpa using h2
  unfold gagliardoMeasure at hae
  rw [Filter.EventuallyEq, ae_withDensity_iff (measurable_gagliardoWeight α)] at hae
  have hS : IsOpen {p : ℝ × ℝ | F p ≠ 0} := hFc.isOpen_preimage _ isOpen_compl_singleton
  have hne : {p : ℝ × ℝ | F p ≠ 0}.Nonempty := ⟨(1, 3), by
    have h1 : gagliardoTent 1 = 1 := by simp [gagliardoTent]
    have h3 : gagliardoTent 3 = 0 := gagliardoTent_eq_zero fun h => by linarith [h.2]
    simp [hFdef, h1, h3]⟩
  have hpos : 0 < ((volume : Measure ℝ).prod (volume : Measure ℝ)) {p : ℝ × ℝ | F p ≠ 0} :=
    hS.measure_pos _ hne
  refine hpos.ne' (measure_eq_zero_iff_ae_notMem.mpr ?_)
  filter_upwards [hae] with p hp hFp
  have hxy : p.1 ≠ p.2 := fun hxy => hFp (by simp [hFdef, hxy])
  exact hFp (hp (gagliardoWeight_pos hα hxy).ne')

/-- **Non-vacuity of the concrete restricted Dirichlet form**: for `α ∈ (0, 2)` the exterior-
Dirichlet space `H^(α / 2)_0(0, ∞)` contains a nonzero element `u` with strictly positive
energy `B^α_0(u, u) > 0`, so `restrictedGagliardoForm α` is not identically zero. -/
theorem exists_restrictedGagliardoForm_pos {α : ℝ} (hα : FractionalExponent α) :
    ∃ u : RestrictedGagliardoSpace α, u ≠ 0 ∧ 0 < (restrictedGagliardoForm α).form u u := by
  refine ⟨gagliardoTentRestricted hα, gagliardoTentRestricted_ne_zero hα, ?_⟩
  change 0 < ⟪gagliardoDiffPart α (gagliardoTentSpace hα),
    gagliardoDiffPart α (gagliardoTentSpace hα)⟫_ℝ
  rw [real_inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.mpr (gagliardoTentDiffL2_ne_zero hα)) 2

end

end FracLap
