import Stokes.BoundaryChart.OrientationBridge

/-!
# Oriented boundary atlases as orientation-map bridge data

This file packages the project-local oriented-atlas hypotheses as the
`BoundaryChartOrientationMapDataOn` data used by the mathlib-orientation-facing
bridge layer.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace BoundaryChartOrientedAtlas

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/--
An oriented boundary atlas supplies orientation-map bridge data on any subset
of the natural boundary chart-transition source.
-/
def orientationMapDataOn_subset
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {s : Set (Fin n → Real)}
    (hs : s ⊆ boundaryChartTransitionBoundarySource I x0 x1) :
    BoundaryChartOrientationMapDataOn I x0 x1 s :=
  boundaryChartOrientationMapDataOn_of_preservesOrientationOn I x0 x1
    (A.preservesOrientationOn_subset hx0 hx1 hs)

/-- The natural boundary-overlap specialization of `orientationMapDataOn_subset`. -/
def orientationMapDataOn_boundarySource
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts) :
    BoundaryChartOrientationMapDataOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  boundaryChartOrientationMapDataOn_of_preservesOrientationOn I x0 x1
    (A.preservesOrientationOn hx0 hx1)

/-- Pointwise bridge data from oriented-atlas data on the natural boundary overlap. -/
def orientationMapDataAt_boundarySource
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {u : Fin n → Real}
    (hu : u ∈ boundaryChartTransitionBoundarySource I x0 x1) :
    BoundaryChartOrientationMapData I x0 x1 u :=
  (A.orientationMapDataOn_boundarySource hx0 hx1) u hu

/-- Lower-zero-face specialization from an explicit source-subset hypothesis. -/
def orientationMapDataOn_lowerZeroFaceDomain
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {a b : Fin (n + 1) → Real}
    (hsource : lowerZeroFaceDomain a b ⊆
      boundaryChartTransitionBoundarySource I x0 x1) :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  A.orientationMapDataOn_subset hx0 hx1 hsource

/-- Selected boundary boxes provide bridge data on their lower-zero face. -/
def orientationMapDataOn_selectedBox
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  boundaryChartOrientationMapDataOn_of_preservesOrientationOn I x0 x1
    (A.preservesOrientationOn_selectedBox hx0 hx1 hbox)

/-- Pointwise selected-box bridge data. -/
def orientationMapDataAt_selectedBox
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    {u : Fin n → Real} (hu : u ∈ lowerZeroFaceDomain a b) :
    BoundaryChartOrientationMapData I x0 x1 u :=
  (A.orientationMapDataOn_selectedBox hx0 hx1 hbox) u hu

end BoundaryChartOrientedAtlas

/-- Oriented-atlas bridge data on a subset of the natural boundary overlap. -/
def boundaryChartOrientationMapDataOn_of_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {s : Set (Fin n → Real)}
    (hs : s ⊆ boundaryChartTransitionBoundarySource I x0 x1) :
    BoundaryChartOrientationMapDataOn I x0 x1 s :=
  A.orientationMapDataOn_subset hx0 hx1 hs

/-- Oriented-atlas bridge data on the full natural boundary overlap. -/
def boundaryChartOrientationMapDataOn_boundarySource_of_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts) :
    BoundaryChartOrientationMapDataOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  A.orientationMapDataOn_boundarySource hx0 hx1

/-- Oriented-atlas bridge data on an explicitly sourced lower-zero face. -/
def boundaryChartOrientationMapDataOn_lowerZeroFaceDomain_of_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {a b : Fin (n + 1) → Real}
    (hsource : lowerZeroFaceDomain a b ⊆
      boundaryChartTransitionBoundarySource I x0 x1) :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  A.orientationMapDataOn_lowerZeroFaceDomain hx0 hx1 hsource

/-- Oriented-atlas bridge data on a selected boundary box. -/
def boundaryChartOrientationMapDataOn_selectedBox_of_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  A.orientationMapDataOn_selectedBox hx0 hx1 hbox

namespace BoundaryChartOrientedManifold

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/--
Global oriented-boundary-charted-manifold data supplies orientation-map bridge
data on any subset of the natural boundary chart-transition source.
-/
def orientationMapDataOn_subset
    [BoundaryChartOrientedManifold I M] (x0 x1 : M)
    {s : Set (Fin n → Real)}
    (hs : s ⊆ boundaryChartTransitionBoundarySource I x0 x1) :
    BoundaryChartOrientationMapDataOn I x0 x1 s :=
  boundaryChartOrientationMapDataOn_of_preservesOrientationOn I x0 x1
    (boundaryChartPreservesOrientationOn_of_orientedManifold x0 x1 hs)

/-- The natural boundary-overlap specialization for global oriented-manifold data. -/
def orientationMapDataOn_boundarySource
    [BoundaryChartOrientedManifold I M] (x0 x1 : M) :
    BoundaryChartOrientationMapDataOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  boundaryChartOrientationMapDataOn_of_preservesOrientationOn I x0 x1
    (BoundaryChartOrientedManifold.preservesOrientationOn (I := I) (M := M) x0 x1)

/-- Pointwise bridge data from global oriented-manifold data on the natural overlap. -/
def orientationMapDataAt_boundarySource
    [BoundaryChartOrientedManifold I M] (x0 x1 : M)
    {u : Fin n → Real}
    (hu : u ∈ boundaryChartTransitionBoundarySource I x0 x1) :
    BoundaryChartOrientationMapData I x0 x1 u :=
  (orientationMapDataOn_boundarySource (I := I) (M := M) x0 x1) u hu

/-- Lower-zero-face specialization from an explicit source-subset hypothesis. -/
def orientationMapDataOn_lowerZeroFaceDomain
    [BoundaryChartOrientedManifold I M] (x0 x1 : M)
    {a b : Fin (n + 1) → Real}
    (hsource : lowerZeroFaceDomain a b ⊆
      boundaryChartTransitionBoundarySource I x0 x1) :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  orientationMapDataOn_subset x0 x1 hsource

/--
Selected boundary boxes provide global oriented-manifold bridge data on their
lower-zero face.
-/
def orientationMapDataOn_selectedBox
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  boundaryChartOrientationMapDataOn_of_preservesOrientationOn I x0 x1
    (boundaryChartPreservesOrientationOn_selectedBox_of_orientedManifold hbox)

/-- Pointwise selected-box bridge data from global oriented-manifold data. -/
def orientationMapDataAt_selectedBox
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    {u : Fin n → Real} (hu : u ∈ lowerZeroFaceDomain a b) :
    BoundaryChartOrientationMapData I x0 x1 u :=
  (orientationMapDataOn_selectedBox (I := I) (M := M) hbox) u hu

end BoundaryChartOrientedManifold

/-- Global oriented-manifold bridge data on a subset of the natural boundary overlap. -/
def boundaryChartOrientationMapDataOn_of_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] (x0 x1 : M)
    {s : Set (Fin n → Real)}
    (hs : s ⊆ boundaryChartTransitionBoundarySource I x0 x1) :
    BoundaryChartOrientationMapDataOn I x0 x1 s :=
  BoundaryChartOrientedManifold.orientationMapDataOn_subset x0 x1 hs

/-- Global oriented-manifold bridge data on the full natural boundary overlap. -/
def boundaryChartOrientationMapDataOn_boundarySource_of_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] (x0 x1 : M) :
    BoundaryChartOrientationMapDataOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  BoundaryChartOrientedManifold.orientationMapDataOn_boundarySource x0 x1

/-- Global oriented-manifold bridge data on an explicitly sourced lower-zero face. -/
def boundaryChartOrientationMapDataOn_lowerZeroFaceDomain_of_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] (x0 x1 : M)
    {a b : Fin (n + 1) → Real}
    (hsource : lowerZeroFaceDomain a b ⊆
      boundaryChartTransitionBoundarySource I x0 x1) :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  BoundaryChartOrientedManifold.orientationMapDataOn_lowerZeroFaceDomain x0 x1 hsource

/-- Global oriented-manifold bridge data on a selected boundary box. -/
def boundaryChartOrientationMapDataOn_selectedBox_of_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  BoundaryChartOrientedManifold.orientationMapDataOn_selectedBox hbox

end ManifoldBoundary

end Stokes

end
