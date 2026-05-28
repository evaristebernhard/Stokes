import Stokes.BoundaryChart.OrientationAtlasSelectedBoxBuilder

/-!
# Boundary oriented atlases from mathlib-style orientation data

Mathlib currently provides the linear `Orientation` API used in
`BoundaryChartOrientationMapData`, but it does not yet provide a manifold-with-
boundary oriented atlas whose chart-change theorems directly imply the project
local fields in `BoundaryChartOrientedAtlas`.

This file therefore records the narrow bridge we can honestly prove now:
if an external orientation object supplies pointwise mathlib
`Orientation.map` data for boundary chart transitions, then it supplies the
existing project-local oriented-atlas and mathlib-facing bridge records.  The
remaining future task is to construct these fields from a genuine upstream
oriented-manifold API when such an API is available.
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
Atlas-level bridge input whose orientation field is already expressed in
mathlib's linear `Orientation.map` language.

The payload type `𝓞` is intentionally abstract.  In a future mathlib oriented
manifold API it should be instantiated by the upstream orientation/atlas object,
while the `orientationMapDataOn` field should be proved from its chart-change
orientation compatibility theorem.
-/
structure BoundaryChartMathlibOrientationAtlasData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (M : Type w) [TopologicalSpace M] [ChartedSpace H M]
    (𝓞 : Type v) where
  /-- External orientation payload, eventually a concrete mathlib object. -/
  orientationData : 𝓞
  /-- Chart centers selected by the external oriented atlas. -/
  charts : Set M
  /-- The selected chart centers cover the manifold by extended-chart sources. -/
  covers : ∀ p : M, ∃ x ∈ charts, p ∈ (extChartAt I x).source
  /-- Boundary-face and tangential compatibility on natural boundary overlaps. -/
  compatibleOn : ∀ {x0 x1 : M}, x0 ∈ charts → x1 ∈ charts →
    boundaryChartTransitionCompatibleOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1)
  /--
  Pointwise mathlib orientation-map data for the tangential boundary chart
  transition on natural boundary overlaps.
  -/
  orientationMapDataOn : ∀ {x0 x1 : M}, x0 ∈ charts → x1 ∈ charts →
    BoundaryChartOrientationMapDataOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1)

namespace BoundaryChartMathlibOrientationAtlasData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {𝓞 : Type v}

/-- Forget pointwise mathlib orientation-map data to the project-local predicate. -/
theorem preservesOrientationOn
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts) :
    boundaryChartPreservesOrientationOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  boundaryChartPreservesOrientationOn_of_orientationMapDataOn I x0 x1
    (D.orientationMapDataOn hx0 hx1)

/-- Positive-Jacobian compatibility derived from the mathlib orientation-map field. -/
theorem orientationCompatibleOn
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts) :
    boundaryChartOrientationCompatibleOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  boundaryChartOrientationCompatibleOn_of_orientationMapDataOn I x0 x1
    (D.orientationMapDataOn hx0 hx1)

/--
Convert mathlib-orientation-map atlas data to the existing abstract
mathlib-facing atlas bridge.
-/
def toMathlibOrientedAtlasBridge
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞) :
    BoundaryChartMathlibOrientedAtlasBridge I M 𝓞 where
  orientationData := D.orientationData
  charts := D.charts
  covers := D.covers
  compatibleOn := D.compatibleOn
  preservesOrientationOn := fun hx0 hx1 => D.preservesOrientationOn hx0 hx1

/-- Forget mathlib-orientation-map atlas data to the project-local oriented atlas. -/
def toBoundaryChartOrientedAtlas
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞) :
    BoundaryChartOrientedAtlas I M :=
  D.toMathlibOrientedAtlasBridge.toBoundaryChartOrientedAtlas

@[simp]
theorem charts_toMathlibOrientedAtlasBridge
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞) :
    D.toMathlibOrientedAtlasBridge.charts = D.charts :=
  rfl

@[simp]
theorem charts_toBoundaryChartOrientedAtlas
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞) :
    D.toBoundaryChartOrientedAtlas.charts = D.charts :=
  rfl

theorem compatibleOn_toBoundaryChartOrientedAtlas
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ D.toBoundaryChartOrientedAtlas.charts)
    (hx1 : x1 ∈ D.toBoundaryChartOrientedAtlas.charts) :
    boundaryChartTransitionCompatibleOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  D.compatibleOn hx0 hx1

def orientationMapDataOn_toBoundaryChartOrientedAtlas
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ D.toBoundaryChartOrientedAtlas.charts)
    (hx1 : x1 ∈ D.toBoundaryChartOrientedAtlas.charts) :
    BoundaryChartOrientationMapDataOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  D.orientationMapDataOn hx0 hx1

theorem preservesOrientationOn_toBoundaryChartOrientedAtlas
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ D.toBoundaryChartOrientedAtlas.charts)
    (hx1 : x1 ∈ D.toBoundaryChartOrientedAtlas.charts) :
    boundaryChartPreservesOrientationOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  D.preservesOrientationOn hx0 hx1

end BoundaryChartMathlibOrientationAtlasData

/--
All-chart bridge input whose orientation field is already expressed in
mathlib's linear `Orientation.map` language.

This is not a bare mathlib oriented-manifold typeclass.  It is the smallest
fieldized target that a future mathlib oriented-manifold API should construct
for this project.
-/
structure BoundaryChartMathlibOrientationManifoldData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (M : Type w) [TopologicalSpace M] [ChartedSpace H M]
    (𝓞 : Type v) where
  /-- External orientation payload, eventually a concrete mathlib object. -/
  orientationData : 𝓞
  /-- Boundary-face and tangential compatibility for all point-centered charts. -/
  compatibleOn : ∀ x0 x1 : M,
    boundaryChartTransitionCompatibleOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1)
  /--
  Pointwise mathlib orientation-map data for all point-centered boundary chart
  transitions.
  -/
  orientationMapDataOn : ∀ x0 x1 : M,
    BoundaryChartOrientationMapDataOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1)

namespace BoundaryChartMathlibOrientationManifoldData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {𝓞 : Type v}

/-- Forget pointwise mathlib orientation-map data to the project-local predicate. -/
theorem preservesOrientationOn
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞) (x0 x1 : M) :
    boundaryChartPreservesOrientationOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  boundaryChartPreservesOrientationOn_of_orientationMapDataOn I x0 x1
    (D.orientationMapDataOn x0 x1)

/-- Positive-Jacobian compatibility derived from the mathlib orientation-map field. -/
theorem orientationCompatibleOn
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞) (x0 x1 : M) :
    boundaryChartOrientationCompatibleOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  boundaryChartOrientationCompatibleOn_of_orientationMapDataOn I x0 x1
    (D.orientationMapDataOn x0 x1)

/-- Convert all-chart mathlib-orientation-map data to atlas-level data. -/
def toAtlasData
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞) :
    BoundaryChartMathlibOrientationAtlasData I M 𝓞 where
  orientationData := D.orientationData
  charts := univ
  covers := fun p => ⟨p, mem_univ p, mem_extChartAt_source (I := I) p⟩
  compatibleOn := fun {x0 x1} _ _ => D.compatibleOn x0 x1
  orientationMapDataOn := fun {x0 x1} _ _ => D.orientationMapDataOn x0 x1

/-- Convert all-chart mathlib-orientation-map data to the existing bridge. -/
def toMathlibOrientedManifoldBridge
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞) :
    BoundaryChartMathlibOrientedManifoldBridge I M 𝓞 where
  orientationData := D.orientationData
  compatibleOn := D.compatibleOn
  preservesOrientationOn := D.preservesOrientationOn

/-- Forget all-chart mathlib-orientation-map data to the project-local class data. -/
@[reducible]
def toBoundaryChartOrientedManifold
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞) :
    BoundaryChartOrientedManifold I M where
  compatibleOn := D.compatibleOn
  preservesOrientationOn := D.preservesOrientationOn

/-- Forget all-chart mathlib-orientation-map data to a project-local oriented atlas. -/
def toBoundaryChartOrientedAtlas
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞) :
    BoundaryChartOrientedAtlas I M :=
  D.toAtlasData.toBoundaryChartOrientedAtlas

@[simp]
theorem charts_toAtlasData
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞) :
    D.toAtlasData.charts = univ :=
  rfl

@[simp]
theorem charts_toBoundaryChartOrientedAtlas
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞) :
    D.toBoundaryChartOrientedAtlas.charts = univ :=
  rfl

theorem toMathlibOrientedAtlasBridge_eq
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞) :
    D.toAtlasData.toMathlibOrientedAtlasBridge =
      D.toMathlibOrientedManifoldBridge.toMathlibOrientedAtlasBridge :=
  rfl

end BoundaryChartMathlibOrientationManifoldData

namespace BoundaryChartMathlibOrientedAtlasBridge

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {𝓞 : Type v}

/-- Stable conservative name for forgetting an abstract mathlib-facing bridge. -/
def toProjectLocalOrientedAtlas
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) :
    BoundaryChartOrientedAtlas I M :=
  B.toBoundaryChartOrientedAtlas

@[simp]
theorem charts_toProjectLocalOrientedAtlas
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) :
    B.toProjectLocalOrientedAtlas.charts = B.charts :=
  rfl

theorem toProjectLocalOrientedAtlas_eq
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) :
    B.toProjectLocalOrientedAtlas = B.toBoundaryChartOrientedAtlas :=
  rfl

/-- Build the existing bridge from pointwise mathlib-orientation-map atlas data. -/
def ofOrientationMapAtlasData
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞) :
    BoundaryChartMathlibOrientedAtlasBridge I M 𝓞 :=
  D.toMathlibOrientedAtlasBridge

end BoundaryChartMathlibOrientedAtlasBridge

namespace BoundaryChartOrientedAtlas

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {𝓞 : Type v}

/-- Constructor from atlas-level mathlib-orientation-map data. -/
def ofMathlibOrientationAtlasData
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞) :
    BoundaryChartOrientedAtlas I M :=
  D.toBoundaryChartOrientedAtlas

/--
Constructor from all-chart mathlib-orientation-map data.

The name is intentionally close to the desired eventual API, but the argument
is still a fieldized bridge record rather than a bare upstream oriented
manifold.
-/
def ofMathlibOrientedManifold
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞) :
    BoundaryChartOrientedAtlas I M :=
  D.toBoundaryChartOrientedAtlas

@[simp]
theorem charts_ofMathlibOrientationAtlasData
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞) :
    (ofMathlibOrientationAtlasData D).charts = D.charts :=
  rfl

@[simp]
theorem charts_ofMathlibOrientedManifold
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞) :
    (ofMathlibOrientedManifold D).charts = univ :=
  rfl

theorem compatibleOn_ofMathlibOrientationAtlasData
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ (ofMathlibOrientationAtlasData D).charts)
    (hx1 : x1 ∈ (ofMathlibOrientationAtlasData D).charts) :
    boundaryChartTransitionCompatibleOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  D.compatibleOn hx0 hx1

def orientationMapDataOn_ofMathlibOrientationAtlasData
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ (ofMathlibOrientationAtlasData D).charts)
    (hx1 : x1 ∈ (ofMathlibOrientationAtlasData D).charts) :
    BoundaryChartOrientationMapDataOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  D.orientationMapDataOn hx0 hx1

theorem preservesOrientationOn_ofMathlibOrientationAtlasData
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ (ofMathlibOrientationAtlasData D).charts)
    (hx1 : x1 ∈ (ofMathlibOrientationAtlasData D).charts) :
    boundaryChartPreservesOrientationOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  D.preservesOrientationOn hx0 hx1

def orientationMapDataOn_ofMathlibOrientedManifold
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞) (x0 x1 : M) :
    BoundaryChartOrientationMapDataOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  D.orientationMapDataOn x0 x1

theorem preservesOrientationOn_ofMathlibOrientedManifold
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞) (x0 x1 : M) :
    boundaryChartPreservesOrientationOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  D.preservesOrientationOn x0 x1

end BoundaryChartOrientedAtlas

end ManifoldBoundary

end Stokes

end
