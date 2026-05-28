import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Minimal Manifold Form API

This module starts the M3 layer: a small, mathlib-shaped API for differential
forms on manifolds.  The definitions are intentionally thin.  They use
mathlib's tangent spaces, manifold derivative, extended charts, and
`ContinuousAlternatingMap` representation, so later local integration theorems
can talk to the M1/M2 Euclidean Stokes layer without exposing the cubical
backend.
-/

noncomputable section

open Set
open scoped Topology
open scoped Manifold

namespace Stokes

universe u v w u' v' w'

/-- A `k`-form on a normed model vector space. -/
abbrev ModelForm (E : Type u) [NormedAddCommGroup E] [NormedSpace Real E] (k : Nat) :=
  E -> E [⋀^Fin k]→L[Real] Real

/--
A `k`-form on a manifold modeled by `I`.

This is the bare fiberwise representation.  Smoothness is a separate predicate,
expressed chartwise by `ManifoldForm.ChartwiseSmooth`.
-/
abbrev ManifoldForm {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type v} [TopologicalSpace H] (I : ModelWithCorners Real E H)
    (M : Type w) [TopologicalSpace M] [ChartedSpace H M] (k : Nat) :=
  ∀ x : M, (TangentSpace I x) [⋀^Fin k]→L[Real] Real

namespace ContinuousAlternatingMap

/--
Alternatization as a continuous linear map from continuous multilinear maps to
continuous alternating maps.

This is a small local bridge: mathlib exposes alternatization as an additive
map, while the smoothness proof below needs a bundled continuous linear map.
-/
noncomputable def alternatizationCLM (E G : Type*) [NormedAddCommGroup E]
    [NormedSpace Real E] [NormedAddCommGroup G] [NormedSpace Real G] (k : Nat) :
    ContinuousMultilinearMap Real (fun _ : Fin k => E) G →L[Real]
      E [⋀^Fin k]→L[Real] G :=
  ContinuousAlternatingMap.liftCLM
    (∑ σ : Equiv.Perm (Fin k),
      (Equiv.Perm.sign σ : ℤ) •
        (ContinuousMultilinearMap.domDomCongrₗᵢ Real E G σ :
          ContinuousMultilinearMap Real (fun _ : Fin k => E) G →L[Real]
            ContinuousMultilinearMap Real (fun _ : Fin k => E) G))
    (by
      intro f v i j hv hne
      simpa [ContinuousMultilinearMap.alternatization_apply_apply, Function.comp_def]
        using (ContinuousMultilinearMap.alternatization f).map_eq_zero_of_eq v hv hne)

@[simp]
theorem alternatizationCLM_apply (E G : Type*) [NormedAddCommGroup E]
    [NormedSpace Real E] [NormedAddCommGroup G] [NormedSpace Real G] (k : Nat)
    (f : ContinuousMultilinearMap Real (fun _ : Fin k => E) G) (m : Fin k → E) :
    alternatizationCLM E G k f m = ContinuousMultilinearMap.alternatization f m := by
  simp [alternatizationCLM, ContinuousMultilinearMap.alternatization_apply_apply,
    ContinuousMultilinearMap.domDomCongrₗᵢ, Function.comp_def, Units.smul_def]

theorem alternatizationCLM_apply_continuousAlternating {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup G] [NormedSpace Real G] {k : Nat}
    (f : E [⋀^Fin k]→L[Real] G) :
    alternatizationCLM E G k f.1 =
      (Nat.factorial k : Real) • f := by
  ext m
  rw [alternatizationCLM_apply]
  rw [show (ContinuousMultilinearMap.alternatization f.toContinuousMultilinearMap) m =
      (MultilinearMap.alternatization f.toMultilinearMap) m by
    exact congrArg (fun a : E [⋀^Fin k]→ₗ[Real] G => a m)
      (ContinuousMultilinearMap.alternatization_apply_toAlternatingMap
        (R := Real) f.toContinuousMultilinearMap)]
  change (MultilinearMap.alternatization f.toMultilinearMap) m =
    (Nat.factorial k : Real) • f m
  rw [Nat.cast_smul_eq_nsmul]
  have h :=
    AlternatingMap.coe_alternatization (R := Real) (ι := Fin k)
      (M := E) (N' := G) f.toAlternatingMap
  simpa [Fintype.card_fin] using congrArg (fun a : E [⋀^Fin k]→ₗ[Real] G => a m) h

/--
The pullback operation `(η, g) ↦ η.compContinuousLinearMap g` is smooth.

The proof factors through mathlib's smooth multilinear pullback operation and
then alternatizes.  On the diagonal where all argument maps are the same,
alternatization is multiplication by `k!`.
-/
theorem contDiff_compContinuousLinearMap {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    {k : Nat} :
    ContDiff Real ⊤
      (fun p : (F [⋀^Fin k]→L[Real] Real) × (E →L[Real] F) =>
        p.1.compContinuousLinearMap p.2) := by
  let L := alternatizationCLM E Real k
  let c : Real := (Nat.factorial k : Real)⁻¹
  let Φ :
      ((Fin k → E →L[Real] F) ×
        ContinuousMultilinearMap Real (fun _ : Fin k => F) Real) →
        ContinuousMultilinearMap Real (fun _ : Fin k => E) Real :=
    fun q => q.2.compContinuousLinearMap q.1
  have hΦ : ContDiff Real ⊤ Φ := by
    rw [← contDiffOn_univ]
    exact ContinuousMultilinearMap.cpolynomialOn_uncurry_compContinuousLinearMap.contDiffOn
  have hdiag :
      ContDiff Real ⊤
        (fun p : (F [⋀^Fin k]→L[Real] Real) × (E →L[Real] F) =>
          ((fun _ : Fin k => p.2), p.1.1)) := by
    apply ContDiff.prodMk
    · rw [contDiff_pi]
      intro _
      exact contDiff_snd
    · exact
        ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM (𝕜 := Real) Real :
            (F [⋀^Fin k]→L[Real] Real) →L[Real]
              ContinuousMultilinearMap Real (fun _ : Fin k => F) Real).contDiff.comp
          contDiff_fst)
  have hΦcomp :
      ContDiff Real ⊤
        (fun p : (F [⋀^Fin k]→L[Real] Real) × (E →L[Real] F) =>
          Φ ((fun _ : Fin k => p.2), p.1.1)) :=
    hΦ.comp hdiag
  have hsmooth :
      ContDiff Real ⊤
        (fun p : (F [⋀^Fin k]→L[Real] Real) × (E →L[Real] F) =>
          c • L (Φ ((fun _ : Fin k => p.2), p.1.1))) :=
    (L.contDiff.comp hΦcomp).const_smul c
  convert hsmooth using 1
  funext p
  change p.1.compContinuousLinearMap p.2 =
    c • L (p.1.1.compContinuousLinearMap fun _ : Fin k => p.2)
  have hL :
      L (p.1.1.compContinuousLinearMap fun _ : Fin k => p.2) =
        (Nat.factorial k : Real) • (p.1.compContinuousLinearMap p.2) := by
    simpa using
      (alternatizationCLM_apply_continuousAlternating (E := E) (G := Real) (k := k)
        (p.1.compContinuousLinearMap p.2))
  symm
  rw [hL]
  have hfac : (Nat.factorial k : Real) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  simp [c, hfac, smul_smul]

theorem contDiffOn_compContinuousLinearMap {X E F : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    {k : Nat} {s : Set X}
    {f : X → F [⋀^Fin k]→L[Real] Real}
    {g : X → E →L[Real] F}
    (hf : ContDiffOn Real ⊤ f s) (hg : ContDiffOn Real ⊤ g s) :
    ContDiffOn Real ⊤ (fun x => (f x).compContinuousLinearMap (g x)) s :=
  contDiff_compContinuousLinearMap.comp_contDiffOn (hf.prodMk hg)

end ContinuousAlternatingMap

namespace ManifoldForm

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners Real E H)
variable {k : Nat}

/--
The derivative of the inverse of an extended chart, viewed as a linear map from
the model vector space into the tangent space of the manifold.
-/
def chartInverseDeriv (x0 : M) (y : E) :
    E →L[Real] TangentSpace I ((extChartAt I x0).symm y) :=
  (mfderivWithin (𝓘(Real, E)) I (extChartAt I x0).symm (range I) y).comp
    ((NormedSpace.fromTangentSpace (𝕜 := Real) y).symm :
      E →L[Real] TangentSpace (𝓘(Real, E)) y)

/--
The derivative of an extended chart, viewed as a linear map from the tangent
space of the manifold to the model vector space.
-/
def chartDeriv (x0 x : M) : TangentSpace I x →L[Real] E :=
  (NormedSpace.fromTangentSpace (𝕜 := Real) ((extChartAt I x0) x) :
      TangentSpace (𝓘(Real, E)) ((extChartAt I x0) x) ≃L[Real] E).toContinuousLinearMap.comp
    (mfderiv I (𝓘(Real, E)) (extChartAt I x0) x)

/--
Derivative of the coordinate change from the chart at `x0` to the chart at
`x1`, expressed at model coordinate `y` of the `x0`-chart.
-/
def chartTransitionDeriv (x0 x1 : M) (y : E) : E →L[Real] E :=
  (chartDeriv I x1 ((extChartAt I x0).symm y)).comp (chartInverseDeriv I x0 y)

/-- The overlap of the `x0` chart with the source of the `x1` chart, in `x0` coordinates. -/
def chartOverlap (x0 x1 : M) : Set E :=
  {y | (extChartAt I x0).symm y ∈ (extChartAt I x1).source}

/-- Coordinate change from the `x0` chart to the `x1` chart. -/
def chartTransition (x0 x1 : M) (y : E) : E :=
  (extChartAt I x1) ((extChartAt I x0).symm y)

/-- The source of the coordinate transition as a partial equivalence. -/
def chartTransitionSource (x0 x1 : M) : Set E :=
  ((extChartAt I x0).symm ≫ extChartAt I x1).source

theorem chartTransitionSource_eq (x0 x1 : M) :
    chartTransitionSource I x0 x1 =
      (extChartAt I x0).target ∩ chartOverlap I x0 x1 := by
  ext y
  simp [chartTransitionSource, chartOverlap, PartialEquiv.trans_source]

/-- The concrete coordinate change is injective on its partial-equivalence source. -/
theorem chartTransition_injOn_source (x0 x1 : M) :
    InjOn (chartTransition I x0 x1) (chartTransitionSource I x0 x1) := by
  intro y hy z hz h
  have hy' : y ∈ (extChartAt I x0).target ∩ chartOverlap I x0 x1 := by
    rwa [chartTransitionSource_eq] at hy
  have hz' : z ∈ (extChartAt I x0).target ∩ chartOverlap I x0 x1 := by
    rwa [chartTransitionSource_eq] at hz
  have hsymm :
      (extChartAt I x0).symm y = (extChartAt I x0).symm z := by
    exact (extChartAt I x1).injOn hy'.2 hz'.2 (by
      simpa [chartTransition] using h)
  calc
    y = (extChartAt I x0) ((extChartAt I x0).symm y) := by
      exact (extChartAt I x0).right_inv hy'.1 |>.symm
    _ = (extChartAt I x0) ((extChartAt I x0).symm z) := by
      rw [hsymm]
    _ = z := by
      exact (extChartAt I x0).right_inv hz'.1

theorem chartTransition_mapsTo_extChartAt_target {x0 x1 : M} {s : Set E}
    (hs : s ⊆ chartOverlap I x0 x1) :
    MapsTo (chartTransition I x0 x1) s (extChartAt I x1).target := by
  intro y hy
  exact (extChartAt I x1).map_source (hs hy)

section ChartSmoothness

variable [IsManifold I ⊤ M]

/--
Smoothness of the concrete coordinate transition, imported directly from
mathlib's extended-chart coordinate-change API.
-/
theorem contDiffOn_chartTransition_source (x0 x1 : M) :
    ContDiffOn Real ⊤ (chartTransition I x0 x1)
      (chartTransitionSource I x0 x1) := by
  simpa [chartTransitionSource, chartTransition] using
    (contDiffOn_ext_coord_change (I := I) (n := (⊤ : WithTop ℕ∞)) x1 x0)

theorem contDiffOn_chartTransition {x0 x1 : M} {s : Set E}
    (hstarget : s ⊆ (extChartAt I x0).target)
    (hsoverlap : s ⊆ chartOverlap I x0 x1) :
    ContDiffOn Real ⊤ (chartTransition I x0 x1) s :=
  (contDiffOn_chartTransition_source (I := I) x0 x1).mono (by
    intro y hy
    rw [chartTransitionSource_eq]
    exact ⟨hstarget hy, hsoverlap hy⟩)

end ChartSmoothness

theorem compContinuousLinearMap_comp
    {F G H : Type*} [AddCommMonoid F] [Module Real F] [TopologicalSpace F]
    [AddCommMonoid G] [Module Real G] [TopologicalSpace G]
    [AddCommMonoid H] [Module Real H] [TopologicalSpace H]
    (η : F [⋀^Fin k]→L[Real] Real) (g : G →L[Real] F) (f : H →L[Real] G) :
    (η.compContinuousLinearMap g).compContinuousLinearMap f =
      η.compContinuousLinearMap (g.comp f) := by
  ext v
  simp [Function.comp_def]

section ChartChange

variable [IsManifold I 1 M]

theorem chartInverseDeriv_comp_chartDeriv {x0 z : M}
    (hz : z ∈ (extChartAt I x0).source) :
    (chartInverseDeriv I x0 ((extChartAt I x0) z)).comp (chartDeriv I x0 z) =
      ContinuousLinearMap.id Real (TangentSpace I z) := by
  have h :=
    mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I) (x := x0) hz
  simpa [chartInverseDeriv, chartDeriv, ContinuousLinearMap.comp_assoc] using h

theorem chartInverseDeriv_comp_chartTransitionDeriv {x0 x1 : M} {y : E}
    (hy : (extChartAt I x0).symm y ∈ (extChartAt I x1).source) :
    (chartInverseDeriv I x1
        ((extChartAt I x1) ((extChartAt I x0).symm y))).comp
      (chartTransitionDeriv I x0 x1 y) =
        chartInverseDeriv I x0 y := by
  rw [chartTransitionDeriv, ← ContinuousLinearMap.comp_assoc,
    chartInverseDeriv_comp_chartDeriv (I := I) (x0 := x1) hy]
  exact ContinuousLinearMap.id_comp (chartInverseDeriv I x0 y)

/--
On the concrete source of a chart transition, the project-level derivative
`chartTransitionDeriv` is exactly mathlib's Frechet derivative of the extended
coordinate change within `range I`.
-/
theorem chartTransitionDeriv_eq_fderivWithin {x0 x1 : M} {y : E}
    (hytarget : y ∈ (extChartAt I x0).target)
    (hyoverlap : y ∈ chartOverlap I x0 x1) :
    chartTransitionDeriv I x0 x1 y =
      fderivWithin Real (chartTransition I x0 x1) (range I) y := by
  have hcomp :
      mfderivWithin (𝓘(Real, E)) (𝓘(Real, E))
          ((extChartAt I x1) ∘ (extChartAt I x0).symm) (range I) y =
        (mfderiv I (𝓘(Real, E)) (extChartAt I x1)
            ((extChartAt I x0).symm y)).comp
          (mfderivWithin (𝓘(Real, E)) I (extChartAt I x0).symm (range I) y) := by
    exact mfderiv_comp_mfderivWithin (x := y)
      (g := (extChartAt I x1)) (f := (extChartAt I x0).symm)
      (mdifferentiableAt_extChartAt (I := I) (x := x1)
        (y := (extChartAt I x0).symm y)
        (by rwa [← extChartAt_source (I := I)]))
      (mdifferentiableWithinAt_extChartAt_symm (I := I) (x := x0) hytarget)
      (I.uniqueMDiffOn y (extChartAt_target_subset_range x0 hytarget))
  rw [← mfderivWithin_eq_fderivWithin (𝕜 := Real)
    (f := (chartTransition I x0 x1)) (s := range I) (x := y)]
  rw [show chartTransition I x0 x1 = (extChartAt I x1) ∘ (extChartAt I x0).symm by rfl]
  rw [hcomp]
  ext v
  rfl

end ChartChange

section ChartSmoothness

variable [IsManifold I ⊤ M]

/--
Smoothness of the concrete coordinate-transition derivative, imported from
mathlib's tangent-bundle coordinate-change API and transported to the
project-level `chartTransitionDeriv`.
-/
theorem contDiffOn_chartTransitionDeriv_source (x0 x1 : M) :
    ContDiffOn Real ⊤ (chartTransitionDeriv I x0 x1)
      (chartTransitionSource I x0 x1) := by
  have hfderiv :
      ContDiffOn Real ⊤
        (fderivWithin Real (chartTransition I x0 x1) (range I))
        (chartTransitionSource I x0 x1) := by
    simpa [chartTransitionSource, chartTransition] using
      (contDiffOn_fderiv_coord_change (𝕜 := Real) (I := I) (n := ⊤)
        (achart H x0) (achart H x1))
  exact hfderiv.congr fun y hy => by
    have hy' : y ∈ (extChartAt I x0).target ∩ chartOverlap I x0 x1 := by
      rwa [← chartTransitionSource_eq (I := I) x0 x1]
    exact chartTransitionDeriv_eq_fderivWithin (I := I) hy'.1 hy'.2

theorem contDiffOn_chartTransitionDeriv {x0 x1 : M} {s : Set E}
    (hstarget : s ⊆ (extChartAt I x0).target)
    (hsoverlap : s ⊆ chartOverlap I x0 x1) :
    ContDiffOn Real ⊤ (chartTransitionDeriv I x0 x1) s :=
  (contDiffOn_chartTransitionDeriv_source (I := I) x0 x1).mono (by
    intro y hy
    rw [chartTransitionSource_eq]
    exact ⟨hstarget hy, hsoverlap hy⟩)

end ChartSmoothness

/--
Pull a manifold form back to the model vector space through the inverse of the
extended chart at `x0`.

Outside the chart target this is still a total function, because
`PartialEquiv.symm` and `mfderivWithin` are total in mathlib.  Local integration
statements should restrict this form to `(extChartAt I x0).target`.
-/
def inChart (x0 : M) (ω : ManifoldForm I M k) : ModelForm E k :=
  fun y => (ω ((extChartAt I x0).symm y)).compContinuousLinearMap
    (chartInverseDeriv I x0 y)

/--
The `x1` chart expression of a form pulled back along the coordinate transition
from `x0` to `x1`.
-/
def transitionPullbackInChart (x0 x1 : M) (ω : ManifoldForm I M k) : ModelForm E k :=
  fun y => (inChart I x1 ω (chartTransition I x0 x1 y)).compContinuousLinearMap
    (chartTransitionDeriv I x0 x1 y)

@[simp]
theorem inChart_apply (x0 : M) (ω : ManifoldForm I M k) (y : E) :
    inChart I x0 ω y =
      (ω ((extChartAt I x0).symm y)).compContinuousLinearMap
        (chartInverseDeriv I x0 y) :=
  rfl

/--
Direct smoothness criterion for the transition-pullback expression.

If the `x1` chart representative is smooth on a target set, the coordinate
transition maps the working set into that target, and both the transition and
its derivative are smooth, then the pulled-back chart representative is smooth.
-/
theorem contDiffOn_transitionPullbackInChart_of_contDiffOn {x0 x1 : M}
    {ω : ManifoldForm I M k} {s t : Set E}
    (hform : ContDiffOn Real ⊤ (inChart I x1 ω) t)
    (htransition : ContDiffOn Real ⊤ (chartTransition I x0 x1) s)
    (hmaps : MapsTo (chartTransition I x0 x1) s t)
    (hderiv : ContDiffOn Real ⊤ (chartTransitionDeriv I x0 x1) s) :
    ContDiffOn Real ⊤ (transitionPullbackInChart I x0 x1 ω) s := by
  have hform_comp :
      ContDiffOn Real ⊤
        (fun y => inChart I x1 ω (chartTransition I x0 x1 y)) s :=
    hform.comp htransition hmaps
  simpa [transitionPullbackInChart] using
    ContinuousAlternatingMap.contDiffOn_compContinuousLinearMap
      (k := k) hform_comp hderiv

section ChartChange

variable [IsManifold I 1 M]

/--
Compatibility of chart expressions for a manifold form.

On the overlap of the `x0` and `x1` charts, the form written in `x0`
coordinates is the pullback of the form written in `x1` coordinates along the
coordinate transition map.
-/
theorem inChart_chartTransition (x0 x1 : M) (ω : ManifoldForm I M k) {y : E}
    (hy : (extChartAt I x0).symm y ∈ (extChartAt I x1).source) :
    (inChart I x1 ω
        ((extChartAt I x1) ((extChartAt I x0).symm y))).compContinuousLinearMap
      (chartTransitionDeriv I x0 x1 y) =
        inChart I x0 ω y := by
  have hleft :
      (extChartAt I x1).symm ((extChartAt I x1) ((extChartAt I x0).symm y)) =
        (extChartAt I x0).symm y :=
    (extChartAt I x1).left_inv hy
  rw [inChart_apply, compContinuousLinearMap_comp,
    chartInverseDeriv_comp_chartTransitionDeriv (I := I) (x0 := x0) (x1 := x1) (y := y) hy,
    hleft, inChart_apply]

/-- Pointwise form of `inChart_chartTransition` using the named transition pullback. -/
theorem transitionPullbackInChart_eq_inChart (x0 x1 : M) (ω : ManifoldForm I M k)
    {y : E} (hy : y ∈ chartOverlap I x0 x1) :
    transitionPullbackInChart I x0 x1 ω y = inChart I x0 ω y := by
  exact inChart_chartTransition (I := I) x0 x1 ω hy

/--
Smoothness transport across a chart change.

If the transition-pullback expression from the `x1` chart is smooth on a set
inside the chart overlap, then the `x0` chart expression is smooth on that set.
The analytic task left for later local Stokes work is to prove the premise from
smoothness of the coordinate transition and the `x1` chart representative.
-/
theorem contDiffOn_inChart_of_transitionPullback {x0 x1 : M}
    {ω : ManifoldForm I M k} {s : Set E}
    (hs : s ⊆ chartOverlap I x0 x1)
    (h : ContDiffOn Real ⊤ (transitionPullbackInChart I x0 x1 ω) s) :
    ContDiffOn Real ⊤ (inChart I x0 ω) s :=
  h.congr fun _ hy => (transitionPullbackInChart_eq_inChart (I := I) x0 x1 ω (hs hy)).symm

/--
Smoothness of the transition-pullback expression on a chart overlap.

This is the reverse direction of `contDiffOn_inChart_of_transitionPullback`:
on the overlap, the named transition-pullback expression is pointwise equal to
the `x0` chart representative, hence it inherits `ContDiffOn` from that
representative.
-/
theorem contDiffOn_transitionPullbackInChart_of_contDiffOn_inChart {x0 x1 : M}
    {ω : ManifoldForm I M k} {s : Set E}
    (hs : s ⊆ chartOverlap I x0 x1)
    (h : ContDiffOn Real ⊤ (inChart I x0 ω) s) :
    ContDiffOn Real ⊤ (transitionPullbackInChart I x0 x1 ω) s :=
  h.congr fun _ hy => transitionPullbackInChart_eq_inChart (I := I) x0 x1 ω (hs hy)

/--
On a chart overlap, smoothness of a chart representative is equivalent to
smoothness of the same representative written as a transition pullback from the
other chart.
-/
theorem contDiffOn_transitionPullbackInChart_iff {x0 x1 : M}
    {ω : ManifoldForm I M k} {s : Set E}
    (hs : s ⊆ chartOverlap I x0 x1) :
    ContDiffOn Real ⊤ (transitionPullbackInChart I x0 x1 ω) s ↔
      ContDiffOn Real ⊤ (inChart I x0 ω) s :=
  ⟨contDiffOn_inChart_of_transitionPullback (I := I) hs,
    contDiffOn_transitionPullbackInChart_of_contDiffOn_inChart (I := I) hs⟩

end ChartChange

/--
Chartwise smoothness for the bare manifold-form representation.

This is deliberately local to extended chart targets.  It is the first bridge
from manifold forms to mathlib's normed-space `ContDiffOn` API.
-/
def ChartwiseSmooth (ω : ManifoldForm I M k) : Prop :=
  ∀ x0 : M, ContDiffOn Real ⊤ (inChart I x0 ω) (extChartAt I x0).target

theorem ChartwiseSmooth.contDiffOn_inChart {ω : ManifoldForm I M k}
    (hω : ChartwiseSmooth I ω) (x0 : M) {s : Set E}
    (hs : s ⊆ (extChartAt I x0).target) :
    ContDiffOn Real ⊤ (inChart I x0 ω) s :=
  (hω x0).mono hs

/--
Direct chartwise-smooth version of
`contDiffOn_transitionPullbackInChart_of_contDiffOn`.
-/
theorem ChartwiseSmooth.contDiffOn_transitionPullbackInChart_of_contDiffOn
    {ω : ManifoldForm I M k} (hω : ChartwiseSmooth I ω) (x0 x1 : M) {s : Set E}
    (htransition : ContDiffOn Real ⊤ (chartTransition I x0 x1) s)
    (hmaps : MapsTo (chartTransition I x0 x1) s (extChartAt I x1).target)
    (hderiv : ContDiffOn Real ⊤ (chartTransitionDeriv I x0 x1) s) :
    ContDiffOn Real ⊤ (transitionPullbackInChart I x0 x1 ω) s :=
  Stokes.ManifoldForm.contDiffOn_transitionPullbackInChart_of_contDiffOn (I := I)
    (hω.contDiffOn_inChart (I := I) x1 (Subset.rfl))
    htransition hmaps hderiv

section ChartSmoothness

variable [IsManifold I ⊤ M]

/--
Chartwise smoothness transported across a chart change using the concrete
mathlib smoothness lemmas for the transition map and its derivative.
-/
theorem ChartwiseSmooth.contDiffOn_transitionPullbackInChart_of_chartAPI
    {ω : ManifoldForm I M k} (hω : ChartwiseSmooth I ω) (x0 x1 : M) {s : Set E}
    (hstarget : s ⊆ (extChartAt I x0).target)
    (hsoverlap : s ⊆ chartOverlap I x0 x1) :
    ContDiffOn Real ⊤ (transitionPullbackInChart I x0 x1 ω) s :=
  hω.contDiffOn_transitionPullbackInChart_of_contDiffOn (I := I) x0 x1
    (contDiffOn_chartTransition (I := I) hstarget hsoverlap)
    (chartTransition_mapsTo_extChartAt_target (I := I) hsoverlap)
    (contDiffOn_chartTransitionDeriv (I := I) hstarget hsoverlap)

end ChartSmoothness

section ChartChange

variable [IsManifold I 1 M]

/--
A chartwise smooth form has a smooth transition-pullback representative on any
set contained in the `x0` chart target and in the overlap with the `x1` chart.
-/
theorem ChartwiseSmooth.contDiffOn_transitionPullbackInChart {ω : ManifoldForm I M k}
    (hω : ChartwiseSmooth I ω) (x0 x1 : M) {s : Set E}
    (hstarget : s ⊆ (extChartAt I x0).target)
    (hsoverlap : s ⊆ chartOverlap I x0 x1) :
    ContDiffOn Real ⊤ (transitionPullbackInChart I x0 x1 ω) s :=
  contDiffOn_transitionPullbackInChart_of_contDiffOn_inChart (I := I) hsoverlap
    (hω.contDiffOn_inChart (I := I) x0 hstarget)

end ChartChange

variable {E' : Type u'} [NormedAddCommGroup E'] [NormedSpace Real E']
variable {H' : Type v'} [TopologicalSpace H']
variable {M' : Type w'} [TopologicalSpace M'] [ChartedSpace H' M']
variable (I' : ModelWithCorners Real E' H')

/--
Pullback of a manifold form along a map, using mathlib's manifold derivative.

Analytic hypotheses are intentionally not baked into this definition.  The
actual Stokes theorem will assume smoothness of the map/form at theorem level.
-/
def pullback (f : M → M') (ω : ManifoldForm I' M' k) : ManifoldForm I M k :=
  fun x => (ω (f x)).compContinuousLinearMap (mfderiv I I' f x)

@[simp]
theorem pullback_apply (f : M → M') (ω : ManifoldForm I' M' k) (x : M) :
    pullback I I' f ω x =
      (ω (f x)).compContinuousLinearMap (mfderiv I I' f x) :=
  rfl

end ManifoldForm

end Stokes

end
