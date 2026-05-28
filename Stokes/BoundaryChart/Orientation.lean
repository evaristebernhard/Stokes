import Stokes.BoundaryChart.SelectedBox

/-!
# Boundary chart orientation data

This file was split out of Stokes.HalfSpace as part of the M6.0
module-structure pass.  The theorem statements and proofs are intended to
remain identical to the monolithic version.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Pointwise boundary-chart compatibility on a boundary-coordinate set.

It records exactly the two hypotheses needed by
`boundaryChartTransition_pointwise_pullback_det`: the chart transition preserves
the boundary face and its derivative preserves boundary tangent vectors.
-/
def boundaryChartTransitionCompatibleOn {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (s : Set (Fin n → Real)) : Prop :=
  ∀ u ∈ s,
    boundaryChartTransitionPreservesBoundaryAt I x0 x1 u ∧
      boundaryChartTransitionDerivPreservesTangentAt I x0 x1 u

/--
The boundary chart transition is injective on any boundary-coordinate set that
lies in the ambient chart-transition source and whose points are preserved as
boundary points by the transition.
-/
theorem boundaryChartTransition_injOn_of_compatibleOn {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) {s : Set (Fin n → Real)}
    (hsource : ∀ u ∈ s, boundaryInclusion n u ∈ boundaryChartDomain I x0 x1)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1 s) :
    InjOn (boundaryChartTransition I x0 x1) s := by
  intro u hu v hv huv
  have huSource :
      boundaryInclusion n u ∈ ManifoldForm.chartTransitionSource I x0 x1 := by
    rw [← boundaryChartDomain_eq_chartTransitionSource]
    exact hsource u hu
  have hvSource :
      boundaryInclusion n v ∈ ManifoldForm.chartTransitionSource I x0 x1 := by
    rw [← boundaryChartDomain_eq_chartTransitionSource]
    exact hsource v hv
  have hamb :
      ManifoldForm.chartTransition I x0 x1 (boundaryInclusion n u) =
        ManifoldForm.chartTransition I x0 x1 (boundaryInclusion n v) := by
    rw [(hcompat u hu).1, (hcompat v hv).1, huv]
  exact boundaryInclusion_injective n
    ((ManifoldForm.chartTransition_injOn_source (I := I) x0 x1)
      huSource hvSource hamb)

theorem boundaryChartTransition_injOn_of_selectedBox_compatibleOn {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b)) :
    InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b) :=
  boundaryChartTransition_injOn_of_compatibleOn I x0 x1
    hbox.boundaryFace_subset_domain hcompat

/--
If the target boundary box is covered by the source box under the boundary
chart transition, and the transition maps the source box into the target box,
then the image of the source box is exactly the target box.

This is the correct box-image API for nonlinear chart changes: the target box
has to be part of the local chart-box choice, not inferred from an arbitrary
source rectangle.
-/
theorem boundaryChartTransition_image_eq_lowerZeroFaceDomain_of_mapsTo_surjOn {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b c d : Fin (n + 1) → Real)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hsurj : SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
      lowerZeroFaceDomain c d :=
  hsurj.image_eq_of_mapsTo hmaps

theorem boundaryChartTransition_image_eq_lowerZeroFaceDomain_of_bijOn {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b c d : Fin (n + 1) → Real)
    (hbij : BijOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
      lowerZeroFaceDomain c d :=
  hbij.surjOn.image_eq_of_mapsTo hbij.mapsTo

theorem boundaryChartTransition_bijOn_of_selectedBox_compatibleOn_mapsTo_surjOn {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hsurj : SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    BijOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d) :=
  BijOn.mk hmaps
    (boundaryChartTransition_injOn_of_selectedBox_compatibleOn hbox hcompat)
    hsurj

/--
Orientation compatibility for a boundary chart transition on a
boundary-coordinate set: the tangential Jacobian is positive.
-/
def boundaryChartOrientationCompatibleOn {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (s : Set (Fin n → Real)) : Prop :=
  ∀ u ∈ s, 0 < boundaryChartTransitionJacobian I x0 x1 u

/--
The target boundary-coordinate frame obtained by pushing the standard boundary
frame through the tangential derivative of a boundary chart transition.
-/
def boundaryChartTransitionFrame {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (u : Fin n → Real) : Fin n → (Fin n → Real) :=
  boundaryChartTransitionTangentMap I x0 x1 u ∘ Pi.basisFun Real (Fin n)

theorem coordinateOrientationSign_boundaryChartTransitionFrame_eq_jacobian {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (u : Fin n → Real) :
    coordinateOrientationSign (boundaryChartTransitionFrame I x0 x1 u) =
      boundaryChartTransitionJacobian I x0 x1 u := by
  rw [coordinateOrientationSign, boundaryChartTransitionFrame,
    coordinateFrameMatrix_linearMap_basisFun]
  simp [boundaryChartTransitionJacobian, boundaryChartTransitionMatrix]

/--
Orientation-facing compatibility of a boundary chart transition: the image of
the standard boundary frame has positive coordinate-orientation sign.
-/
def boundaryChartPreservesOrientationOn {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (s : Set (Fin n → Real)) : Prop :=
  ∀ u ∈ s, 0 < coordinateOrientationSign (boundaryChartTransitionFrame I x0 x1 u)

theorem boundaryChartOrientationCompatibleOn_of_preservesOrientationOn {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) {s : Set (Fin n → Real)}
    (horient : boundaryChartPreservesOrientationOn I x0 x1 s) :
    boundaryChartOrientationCompatibleOn I x0 x1 s := by
  intro u hu
  simpa [coordinateOrientationSign_boundaryChartTransitionFrame_eq_jacobian]
    using horient u hu

/--
Project-local data for an oriented boundary chart atlas.

Mathlib currently supplies the point-set charted-manifold API and linear
orientation API separately, but not a ready-made oriented-manifold-with-boundary
structure.  This structure is the thin bridge needed by the local Stokes layer:
it records a covering family of chart centers and says that chart changes
between centers in the family preserve the boundary face, preserve tangent
vectors to the boundary, and preserve the chosen boundary orientation on the
natural boundary overlap.
-/
structure BoundaryChartOrientedAtlas {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (M : Type w) [TopologicalSpace M] [ChartedSpace H M] where
  /-- Chart centers whose `extChartAt` charts are treated as oriented charts. -/
  charts : Set M
  /-- The chart centers cover the manifold by their extended-chart sources. -/
  covers : ∀ p : M, ∃ x ∈ charts, p ∈ (extChartAt I x).source
  /--
  Boundary chart changes between atlas charts preserve the boundary face and
  boundary tangent directions on their natural boundary overlap.
  -/
  compatibleOn : ∀ {x0 x1 : M}, x0 ∈ charts → x1 ∈ charts →
    boundaryChartTransitionCompatibleOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1)
  /--
  Boundary chart changes between atlas charts preserve the selected orientation
  on their natural boundary overlap.
  -/
  preservesOrientationOn : ∀ {x0 x1 : M}, x0 ∈ charts → x1 ∈ charts →
    boundaryChartPreservesOrientationOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1)

namespace BoundaryChartOrientedAtlas

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

theorem transitionCompatibleOn_subset
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {s : Set (Fin n → Real)}
    (hs : s ⊆ boundaryChartTransitionBoundarySource I x0 x1) :
    boundaryChartTransitionCompatibleOn I x0 x1 s := by
  intro u hu
  exact A.compatibleOn hx0 hx1 u (hs hu)

theorem preservesOrientationOn_subset
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {s : Set (Fin n → Real)}
    (hs : s ⊆ boundaryChartTransitionBoundarySource I x0 x1) :
    boundaryChartPreservesOrientationOn I x0 x1 s := by
  intro u hu
  exact A.preservesOrientationOn hx0 hx1 u (hs hu)

theorem orientationCompatibleOn_subset
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {s : Set (Fin n → Real)}
    (hs : s ⊆ boundaryChartTransitionBoundarySource I x0 x1) :
    boundaryChartOrientationCompatibleOn I x0 x1 s :=
  boundaryChartOrientationCompatibleOn_of_preservesOrientationOn I x0 x1
    (A.preservesOrientationOn_subset hx0 hx1 hs)

theorem transitionCompatibleOn_selectedBox
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  A.transitionCompatibleOn_subset hx0 hx1
    (lowerZeroFaceDomain_subset_boundaryChartTransitionBoundarySource_of_selectedBox hbox)

theorem preservesOrientationOn_selectedBox
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartPreservesOrientationOn I x0 x1 (lowerZeroFaceDomain a b) :=
  A.preservesOrientationOn_subset hx0 hx1
    (lowerZeroFaceDomain_subset_boundaryChartTransitionBoundarySource_of_selectedBox hbox)

theorem orientationCompatibleOn_selectedBox
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  boundaryChartOrientationCompatibleOn_of_preservesOrientationOn I x0 x1
    (A.preservesOrientationOn_selectedBox hx0 hx1 hbox)

end BoundaryChartOrientedAtlas

theorem boundaryChartPreservesOrientationOn_of_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {s : Set (Fin n → Real)}
    (hs : s ⊆ boundaryChartTransitionBoundarySource I x0 x1) :
    boundaryChartPreservesOrientationOn I x0 x1 s :=
  A.preservesOrientationOn_subset hx0 hx1 hs

theorem boundaryChartOrientationCompatibleOn_of_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {s : Set (Fin n → Real)}
    (hs : s ⊆ boundaryChartTransitionBoundarySource I x0 x1) :
    boundaryChartOrientationCompatibleOn I x0 x1 s :=
  A.orientationCompatibleOn_subset hx0 hx1 hs

/--
Global oriented-manifold data for the boundary charts already present in the
current `ChartedSpace`.

This is the typeclass-shaped variant of `BoundaryChartOrientedAtlas`: it says
that all point-centered boundary charts from the chosen charted-space atlas are
mutually boundary-compatible and orientation-preserving on their natural
boundary overlaps.
-/
class BoundaryChartOrientedManifold {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (M : Type w) [TopologicalSpace M] [ChartedSpace H M] : Prop where
  /-- All boundary chart transitions preserve boundary faces and tangent directions. -/
  compatibleOn : ∀ x0 x1 : M,
    boundaryChartTransitionCompatibleOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1)
  /-- All boundary chart transitions preserve the chosen boundary orientation. -/
  preservesOrientationOn : ∀ x0 x1 : M,
    boundaryChartPreservesOrientationOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1)

namespace BoundaryChartOrientedManifold

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/--
The typeclass-style global orientation data as the special atlas containing all
point-centered charts.
-/
def toOrientedAtlas [BoundaryChartOrientedManifold I M] :
    BoundaryChartOrientedAtlas I M where
  charts := univ
  covers := fun p => ⟨p, mem_univ p, mem_extChartAt_source (I := I) p⟩
  compatibleOn := fun {x0 x1} _ _ =>
    BoundaryChartOrientedManifold.compatibleOn (I := I) (M := M) x0 x1
  preservesOrientationOn := fun {x0 x1} _ _ =>
    BoundaryChartOrientedManifold.preservesOrientationOn (I := I) (M := M) x0 x1

@[simp]
theorem charts_toOrientedAtlas [BoundaryChartOrientedManifold I M] :
    (toOrientedAtlas (I := I) (M := M)).charts = univ :=
  rfl

end BoundaryChartOrientedManifold

theorem boundaryChartTransitionCompatibleOn_of_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] (x0 x1 : M)
    {s : Set (Fin n → Real)}
    (hs : s ⊆ boundaryChartTransitionBoundarySource I x0 x1) :
    boundaryChartTransitionCompatibleOn I x0 x1 s := by
  intro u hu
  exact BoundaryChartOrientedManifold.compatibleOn (I := I) (M := M) x0 x1 u (hs hu)

theorem boundaryChartPreservesOrientationOn_of_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] (x0 x1 : M)
    {s : Set (Fin n → Real)}
    (hs : s ⊆ boundaryChartTransitionBoundarySource I x0 x1) :
    boundaryChartPreservesOrientationOn I x0 x1 s := by
  intro u hu
  exact BoundaryChartOrientedManifold.preservesOrientationOn (I := I) (M := M) x0 x1 u (hs hu)

theorem boundaryChartOrientationCompatibleOn_of_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] (x0 x1 : M)
    {s : Set (Fin n → Real)}
    (hs : s ⊆ boundaryChartTransitionBoundarySource I x0 x1) :
    boundaryChartOrientationCompatibleOn I x0 x1 s :=
  boundaryChartOrientationCompatibleOn_of_preservesOrientationOn I x0 x1
    (boundaryChartPreservesOrientationOn_of_orientedManifold x0 x1 hs)

theorem boundaryChartTransitionCompatibleOn_selectedBox_of_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  boundaryChartTransitionCompatibleOn_of_orientedManifold x0 x1
    (lowerZeroFaceDomain_subset_boundaryChartTransitionBoundarySource_of_selectedBox hbox)

theorem boundaryChartPreservesOrientationOn_selectedBox_of_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartPreservesOrientationOn I x0 x1 (lowerZeroFaceDomain a b) :=
  boundaryChartPreservesOrientationOn_of_orientedManifold x0 x1
    (lowerZeroFaceDomain_subset_boundaryChartTransitionBoundarySource_of_selectedBox hbox)

theorem boundaryChartOrientationCompatibleOn_selectedBox_of_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  boundaryChartOrientationCompatibleOn_of_orientedManifold x0 x1
    (lowerZeroFaceDomain_subset_boundaryChartTransitionBoundarySource_of_selectedBox hbox)

end ManifoldBoundary

end Stokes

end
