import Stokes.BoundaryChart.OrientationNatural

/-!
# Boundary-chart bridge for future mathlib oriented-manifold data

Mathlib currently has a mature linear `Orientation` API, while this project
uses `BoundaryChartOrientedAtlas` and `BoundaryChartOrientedManifold` as the
boundary-chart data consumed by local Stokes and chart-change theorems.

This file records the intended interface to a future mathlib
oriented-manifold-with-boundary API.  The external orientation object is kept as
an arbitrary type parameter `𝓞`; the fields below are exactly the facts that
must be supplied from that object before it can be used by the boundary-chart
layer.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u v w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Fieldized bridge from a future mathlib oriented-atlas object to the
project-local boundary-chart oriented atlas.

The parameter `𝓞` is deliberately abstract: once mathlib exposes a concrete
oriented atlas/manifold-with-boundary structure, an instance of this record
should be built with `orientationData` equal to that object and with the four
remaining fields proved from its chart/orientation compatibility theorems.
-/
structure BoundaryChartMathlibOrientedAtlasBridge {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (M : Type w) [TopologicalSpace M] [ChartedSpace H M]
    (𝓞 : Type v) where
  /-- The external orientation object, eventually a mathlib oriented atlas. -/
  orientationData : 𝓞
  /-- Chart centers selected by the external oriented atlas. -/
  charts : Set M
  /-- The selected chart centers cover the manifold by extended-chart sources. -/
  covers : ∀ p : M, ∃ x ∈ charts, p ∈ (extChartAt I x).source
  /--
  Boundary chart changes supplied by the external data preserve the boundary
  face and boundary tangent directions on the natural boundary overlap.
  -/
  compatibleOn : ∀ {x0 x1 : M}, x0 ∈ charts → x1 ∈ charts →
    boundaryChartTransitionCompatibleOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1)
  /--
  Boundary chart changes supplied by the external data preserve the selected
  boundary orientation on the natural boundary overlap.
  -/
  preservesOrientationOn : ∀ {x0 x1 : M}, x0 ∈ charts → x1 ∈ charts →
    boundaryChartPreservesOrientationOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1)

namespace BoundaryChartMathlibOrientedAtlasBridge

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {𝓞 : Type v}

/-- Forget the external orientation object to the project-local oriented atlas. -/
def toBoundaryChartOrientedAtlas
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) :
    BoundaryChartOrientedAtlas I M where
  charts := B.charts
  covers := B.covers
  compatibleOn := B.compatibleOn
  preservesOrientationOn := B.preservesOrientationOn

@[simp]
theorem charts_toBoundaryChartOrientedAtlas
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) :
    B.toBoundaryChartOrientedAtlas.charts = B.charts :=
  rfl

theorem covers_toBoundaryChartOrientedAtlas
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) (p : M) :
    ∃ x ∈ B.toBoundaryChartOrientedAtlas.charts, p ∈ (extChartAt I x).source :=
  B.covers p

theorem compatibleOn_toBoundaryChartOrientedAtlas
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ B.toBoundaryChartOrientedAtlas.charts)
    (hx1 : x1 ∈ B.toBoundaryChartOrientedAtlas.charts) :
    boundaryChartTransitionCompatibleOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  B.compatibleOn hx0 hx1

theorem preservesOrientationOn_toBoundaryChartOrientedAtlas
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ B.toBoundaryChartOrientedAtlas.charts)
    (hx1 : x1 ∈ B.toBoundaryChartOrientedAtlas.charts) :
    boundaryChartPreservesOrientationOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  B.preservesOrientationOn hx0 hx1

/--
Any future mathlib-oriented-atlas bridge supplies orientation-map data on every
subset of the natural boundary overlap.
-/
def orientationMapDataOn_subset
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ B.toBoundaryChartOrientedAtlas.charts)
    (hx1 : x1 ∈ B.toBoundaryChartOrientedAtlas.charts)
    {s : Set (Fin n → Real)}
    (hs : s ⊆ boundaryChartTransitionBoundarySource I x0 x1) :
    BoundaryChartOrientationMapDataOn I x0 x1 s :=
  B.toBoundaryChartOrientedAtlas.orientationMapDataOn_subset hx0 hx1 hs

/-- Natural-boundary-overlap specialization of `orientationMapDataOn_subset`. -/
def orientationMapDataOn_boundarySource
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ B.toBoundaryChartOrientedAtlas.charts)
    (hx1 : x1 ∈ B.toBoundaryChartOrientedAtlas.charts) :
    BoundaryChartOrientationMapDataOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  B.toBoundaryChartOrientedAtlas.orientationMapDataOn_boundarySource hx0 hx1

/-- Selected-box specialization of the bridge orientation-map data. -/
def orientationMapDataOn_selectedBox
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ B.toBoundaryChartOrientedAtlas.charts)
    (hx1 : x1 ∈ B.toBoundaryChartOrientedAtlas.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  B.toBoundaryChartOrientedAtlas.orientationMapDataOn_selectedBox hx0 hx1 hbox

theorem selectedBox_preservesOrientationOn
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ B.toBoundaryChartOrientedAtlas.charts)
    (hx1 : x1 ∈ B.toBoundaryChartOrientedAtlas.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartPreservesOrientationOn I x0 x1 (lowerZeroFaceDomain a b) :=
  B.toBoundaryChartOrientedAtlas.selectedBoxPreservesOrientation hx0 hx1 hbox

theorem selectedBox_orientationCompatibleOn
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ B.toBoundaryChartOrientedAtlas.charts)
    (hx1 : x1 ∈ B.toBoundaryChartOrientedAtlas.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  B.toBoundaryChartOrientedAtlas.selectedBoxOrientationCompatible hx0 hx1 hbox

end BoundaryChartMathlibOrientedAtlasBridge

/--
Fieldized bridge from a future mathlib oriented-manifold-with-boundary object
to the project-local global boundary-chart orientation class.

Compared with `BoundaryChartMathlibOrientedAtlasBridge`, this is the all-chart
variant: every point-centered chart in the ambient `ChartedSpace` is treated as
an oriented boundary chart.
-/
structure BoundaryChartMathlibOrientedManifoldBridge {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (M : Type w) [TopologicalSpace M] [ChartedSpace H M]
    (𝓞 : Type v) where
  /-- The external orientation object, eventually a mathlib oriented manifold. -/
  orientationData : 𝓞
  /--
  Boundary chart changes supplied by the external oriented-manifold data
  preserve the boundary face and boundary tangent directions.
  -/
  compatibleOn : ∀ x0 x1 : M,
    boundaryChartTransitionCompatibleOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1)
  /--
  Boundary chart changes supplied by the external oriented-manifold data
  preserve the induced boundary orientation.
  -/
  preservesOrientationOn : ∀ x0 x1 : M,
    boundaryChartPreservesOrientationOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1)

namespace BoundaryChartMathlibOrientedManifoldBridge

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {𝓞 : Type v}

/-- Forget the external orientation object to project-local global orientation data. -/
@[reducible]
def toBoundaryChartOrientedManifold
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) :
    BoundaryChartOrientedManifold I M where
  compatibleOn := B.compatibleOn
  preservesOrientationOn := B.preservesOrientationOn

/-- The all-chart atlas associated to a future mathlib-oriented-manifold bridge. -/
def toMathlibOrientedAtlasBridge
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) :
    BoundaryChartMathlibOrientedAtlasBridge I M 𝓞 where
  orientationData := B.orientationData
  charts := univ
  covers := fun p => ⟨p, mem_univ p, mem_extChartAt_source (I := I) p⟩
  compatibleOn := fun {x0 x1} _ _ => B.compatibleOn x0 x1
  preservesOrientationOn := fun {x0 x1} _ _ => B.preservesOrientationOn x0 x1

@[simp]
theorem charts_toMathlibOrientedAtlasBridge
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) :
    B.toMathlibOrientedAtlasBridge.charts = univ :=
  rfl

theorem compatibleOn_toBoundaryChartOrientedManifold
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) (x0 x1 : M) :
    boundaryChartTransitionCompatibleOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  B.compatibleOn x0 x1

theorem preservesOrientationOn_toBoundaryChartOrientedManifold
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) (x0 x1 : M) :
    boundaryChartPreservesOrientationOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  B.preservesOrientationOn x0 x1

/--
Use a future mathlib-oriented-manifold bridge as an explicit local instance of
the project-local global orientation class.
-/
def withBoundaryChartOrientedManifold
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞)
    {α : Sort*} (k : BoundaryChartOrientedManifold I M → α) : α :=
  k B.toBoundaryChartOrientedManifold

/-- Orientation-map data on a subset of a natural boundary overlap. -/
def orientationMapDataOn_subset
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) (x0 x1 : M)
    {s : Set (Fin n → Real)}
    (hs : s ⊆ boundaryChartTransitionBoundarySource I x0 x1) :
    BoundaryChartOrientationMapDataOn I x0 x1 s :=
  (B.toMathlibOrientedAtlasBridge).orientationMapDataOn_subset
    (mem_univ x0) (mem_univ x1) hs

/-- Selected-box specialization of the bridge orientation-map data. -/
def orientationMapDataOn_selectedBox
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (B.toMathlibOrientedAtlasBridge).orientationMapDataOn_selectedBox
    (mem_univ x0) (mem_univ x1) hbox

theorem selectedBox_preservesOrientationOn
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartPreservesOrientationOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (B.toMathlibOrientedAtlasBridge).selectedBox_preservesOrientationOn
    (mem_univ x0) (mem_univ x1) hbox

theorem selectedBox_orientationCompatibleOn
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (B.toMathlibOrientedAtlasBridge).selectedBox_orientationCompatibleOn
    (mem_univ x0) (mem_univ x1) hbox

end BoundaryChartMathlibOrientedManifoldBridge

namespace BoundaryChartOrientedAtlas

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/--
View the current project-local oriented atlas as a bridge with no external
orientation payload.  This is mainly useful for API migration: declarations
written against `BoundaryChartMathlibOrientedAtlasBridge` can already consume
the current project-local data.
-/
def toMathlibBridge (A : BoundaryChartOrientedAtlas I M) :
    BoundaryChartMathlibOrientedAtlasBridge I M Unit where
  orientationData := ()
  charts := A.charts
  covers := A.covers
  compatibleOn := A.compatibleOn
  preservesOrientationOn := A.preservesOrientationOn

@[simp]
theorem charts_toMathlibBridge (A : BoundaryChartOrientedAtlas I M) :
    A.toMathlibBridge.charts = A.charts :=
  rfl

theorem toBoundaryChartOrientedAtlas_toMathlibBridge_charts
    (A : BoundaryChartOrientedAtlas I M) :
    A.toMathlibBridge.toBoundaryChartOrientedAtlas.charts = A.charts :=
  rfl

end BoundaryChartOrientedAtlas

namespace BoundaryChartOrientedManifold

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/--
View the current project-local oriented-manifold class as a bridge with no
external orientation payload.
-/
def toMathlibBridge [BoundaryChartOrientedManifold I M] :
    BoundaryChartMathlibOrientedManifoldBridge I M Unit where
  orientationData := ()
  compatibleOn := BoundaryChartOrientedManifold.compatibleOn (I := I) (M := M)
  preservesOrientationOn :=
    BoundaryChartOrientedManifold.preservesOrientationOn (I := I) (M := M)

theorem toMathlibBridge_compatibleOn [BoundaryChartOrientedManifold I M]
    (x0 x1 : M) :
    boundaryChartTransitionCompatibleOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  (toMathlibBridge (I := I) (M := M)).compatibleOn x0 x1

theorem toMathlibBridge_preservesOrientationOn [BoundaryChartOrientedManifold I M]
    (x0 x1 : M) :
    boundaryChartPreservesOrientationOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  (toMathlibBridge (I := I) (M := M)).preservesOrientationOn x0 x1

end BoundaryChartOrientedManifold

end ManifoldBoundary

end Stokes

end
