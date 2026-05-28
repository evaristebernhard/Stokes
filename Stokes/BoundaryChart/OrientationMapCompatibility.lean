import Stokes.BoundaryChart.OrientedAtlasFromMathlib

/-!
# Orientation-map compatibility sources

This file records the current honest source of the orientation fields used by
the boundary-chart Stokes layer.

Mathlib currently provides the linear `Orientation.map` API and determinant
criteria in `Mathlib.LinearAlgebra.Orientation`; this project has not found a
manifold-with-boundary oriented-atlas API that directly supplies the boundary
chart fields.  The declarations below therefore keep the missing global layer
fieldized, while making the linear implications precise:

* a concrete `Orientation.map` equality for the tangential chart derivative is
  equivalent to positive tangential Jacobian for the same linear equivalence;
* such linear data builds `BoundaryChartOrientationMapDataOn`;
* atlas/manifold-level fieldized sources build the existing
  `BoundaryChartMathlibOrientationAtlasData` records;
* selected boundary boxes can be packaged as
  `BoundaryChartAtlasBoundarySignData` without losing the original
  orientation-map source.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u v w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

section Pointwise

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {x0 x1 : M} {u : Fin n -> Real}

/--
For a fixed linear equivalence whose underlying linear map is the tangential
boundary chart derivative, preserving the standard mathlib boundary
orientation is equivalent to positive project-local tangential Jacobian.
-/
theorem orientation_map_eq_iff_boundaryChartTransitionJacobian_pos
    (tangentEquiv : (Fin n -> Real) ≃ₗ[Real] (Fin n -> Real))
    (hlinear :
      (tangentEquiv : (Fin n -> Real) →ₗ[Real] (Fin n -> Real)) =
        (boundaryChartTransitionTangentMap I x0 x1 u :
          (Fin n -> Real) →ₗ[Real] (Fin n -> Real))) :
    Orientation.map (Fin n) tangentEquiv (standardBoundaryOrientation n) =
        standardBoundaryOrientation n ↔
      0 < boundaryChartTransitionJacobian I x0 x1 u := by
  constructor
  · intro hmap
    have hdet :
        0 < LinearMap.det
          (tangentEquiv : (Fin n -> Real) →ₗ[Real] (Fin n -> Real)) :=
      det_pos_of_standardBoundaryOrientation_map_eq tangentEquiv hmap
    rw [boundaryChartTransitionJacobian,
      boundaryChartTransitionMatrix_det_eq_linearMap_det]
    simpa [← hlinear] using hdet
  · intro hjac
    have hdet :
        0 < LinearMap.det
          (tangentEquiv : (Fin n -> Real) →ₗ[Real] (Fin n -> Real)) := by
      rw [hlinear]
      simpa [boundaryChartTransitionJacobian,
        boundaryChartTransitionMatrix_det_eq_linearMap_det] using hjac
    exact standardBoundaryOrientation_map_eq_of_det_pos tangentEquiv hdet

/--
The same equivalence expressed using the project-local transported boundary
frame orientation sign.
-/
theorem orientation_map_eq_iff_coordinateOrientationSign_pos
    (tangentEquiv : (Fin n -> Real) ≃ₗ[Real] (Fin n -> Real))
    (hlinear :
      (tangentEquiv : (Fin n -> Real) →ₗ[Real] (Fin n -> Real)) =
        (boundaryChartTransitionTangentMap I x0 x1 u :
          (Fin n -> Real) →ₗ[Real] (Fin n -> Real))) :
    Orientation.map (Fin n) tangentEquiv (standardBoundaryOrientation n) =
        standardBoundaryOrientation n ↔
      0 < coordinateOrientationSign
        (boundaryChartTransitionFrame I x0 x1 u) := by
  rw [coordinateOrientationSign_boundaryChartTransitionFrame_eq_jacobian]
  exact orientation_map_eq_iff_boundaryChartTransitionJacobian_pos
    (I := I) (x0 := x0) (x1 := x1) (u := u) tangentEquiv hlinear

/--
Minimal pointwise source data for a boundary chart `Orientation.map`
compatibility theorem.

This is deliberately smaller than `BoundaryChartOrientationMapData`: it stores
the linear equivalence, its identification with the tangential derivative, and
the mathlib orientation-map equality.  Determinant/Jacobian positivity is then
derived by the bridge theorems above.
-/
structure BoundaryChartLinearOrientationMapSource {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (x0 x1 : M) (u : Fin n -> Real) where
  /-- The tangential boundary derivative as a linear equivalence. -/
  tangentEquiv : (Fin n -> Real) ≃ₗ[Real] (Fin n -> Real)
  /-- The supplied equivalence has the correct underlying linear map. -/
  tangentEquiv_toLinearMap :
    (tangentEquiv : (Fin n -> Real) →ₗ[Real] (Fin n -> Real)) =
      (boundaryChartTransitionTangentMap I x0 x1 u :
        (Fin n -> Real) →ₗ[Real] (Fin n -> Real))
  /-- The tangential equivalence preserves the standard mathlib orientation. -/
  orientation_map_eq :
    Orientation.map (Fin n) tangentEquiv (standardBoundaryOrientation n) =
      standardBoundaryOrientation n

namespace BoundaryChartLinearOrientationMapSource

/-- Promote the minimal source to the existing pointwise orientation-map data. -/
def toOrientationMapData
    (D : BoundaryChartLinearOrientationMapSource I x0 x1 u) :
    BoundaryChartOrientationMapData I x0 x1 u :=
  BoundaryChartOrientationMapData.ofOrientationMapEq
    D.tangentEquiv D.tangentEquiv_toLinearMap D.orientation_map_eq

/-- Build the minimal source from an existing pointwise data package. -/
def ofOrientationMapData
    (D : BoundaryChartOrientationMapData I x0 x1 u) :
    BoundaryChartLinearOrientationMapSource I x0 x1 u where
  tangentEquiv := D.tangentEquiv
  tangentEquiv_toLinearMap := D.tangentEquiv_toLinearMap
  orientation_map_eq := D.orientation_map_eq

/-- Build the minimal source from a chosen tangent equivalence and positive Jacobian. -/
def ofJacobianPos
    (tangentEquiv : (Fin n -> Real) ≃ₗ[Real] (Fin n -> Real))
    (hlinear :
      (tangentEquiv : (Fin n -> Real) →ₗ[Real] (Fin n -> Real)) =
        (boundaryChartTransitionTangentMap I x0 x1 u :
          (Fin n -> Real) →ₗ[Real] (Fin n -> Real)))
    (hjac : 0 < boundaryChartTransitionJacobian I x0 x1 u) :
    BoundaryChartLinearOrientationMapSource I x0 x1 u where
  tangentEquiv := tangentEquiv
  tangentEquiv_toLinearMap := hlinear
  orientation_map_eq :=
    (orientation_map_eq_iff_boundaryChartTransitionJacobian_pos
      (I := I) (x0 := x0) (x1 := x1) (u := u)
      tangentEquiv hlinear).2 hjac

@[simp]
theorem toOrientationMapData_tangentEquiv
    (D : BoundaryChartLinearOrientationMapSource I x0 x1 u) :
    D.toOrientationMapData.tangentEquiv = D.tangentEquiv :=
  rfl

theorem jacobian_pos
    (D : BoundaryChartLinearOrientationMapSource I x0 x1 u) :
    0 < boundaryChartTransitionJacobian I x0 x1 u :=
  (orientation_map_eq_iff_boundaryChartTransitionJacobian_pos
    (I := I) (x0 := x0) (x1 := x1) (u := u)
    D.tangentEquiv D.tangentEquiv_toLinearMap).1 D.orientation_map_eq

theorem coordinateOrientationSign_pos
    (D : BoundaryChartLinearOrientationMapSource I x0 x1 u) :
    0 < coordinateOrientationSign (boundaryChartTransitionFrame I x0 x1 u) :=
  (orientation_map_eq_iff_coordinateOrientationSign_pos
    (I := I) (x0 := x0) (x1 := x1) (u := u)
    D.tangentEquiv D.tangentEquiv_toLinearMap).1 D.orientation_map_eq

end BoundaryChartLinearOrientationMapSource

/-- Set-level source data for pointwise linear orientation-map compatibility. -/
def BoundaryChartLinearOrientationMapSourceOn {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (x0 x1 : M) (s : Set (Fin n -> Real)) : Type _ :=
  ∀ u, u ∈ s -> BoundaryChartLinearOrientationMapSource I x0 x1 u

namespace BoundaryChartLinearOrientationMapSourceOn

variable {s : Set (Fin n -> Real)}

/-- Promote set-level linear sources to the existing orientation-map data. -/
def toOrientationMapDataOn
    (D : BoundaryChartLinearOrientationMapSourceOn I x0 x1 s) :
    BoundaryChartOrientationMapDataOn I x0 x1 s :=
  fun u hu => (D u hu).toOrientationMapData

/-- Positive tangential Jacobian on the set, derived from the map equality. -/
theorem orientationCompatibleOn
    (D : BoundaryChartLinearOrientationMapSourceOn I x0 x1 s) :
    boundaryChartOrientationCompatibleOn I x0 x1 s := by
  intro u hu
  exact (D u hu).jacobian_pos

/-- Project-local orientation preservation on the set, derived from the map equality. -/
theorem preservesOrientationOn
    (D : BoundaryChartLinearOrientationMapSourceOn I x0 x1 s) :
    boundaryChartPreservesOrientationOn I x0 x1 s := by
  intro u hu
  exact (D u hu).coordinateOrientationSign_pos

end BoundaryChartLinearOrientationMapSourceOn

end Pointwise

section AtlasSources

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {𝓞 : Type v}

/--
Atlas-level source whose orientation field is supplied as linear
`Orientation.map` compatibility on boundary chart overlaps.

This is the smallest shape a future upstream oriented-atlas theorem would need
to produce in order to feed `OrientedAtlasFromMathlib`.
-/
structure BoundaryChartMathlibLinearOrientationAtlasSource
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (M : Type w) [TopologicalSpace M] [ChartedSpace H M]
    (𝓞 : Type v) where
  orientationData : 𝓞
  charts : Set M
  covers : ∀ p : M, ∃ x ∈ charts, p ∈ (extChartAt I x).source
  compatibleOn : ∀ {x0 x1 : M}, x0 ∈ charts -> x1 ∈ charts ->
    boundaryChartTransitionCompatibleOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1)
  orientationMapSourceOn : ∀ {x0 x1 : M}, x0 ∈ charts -> x1 ∈ charts ->
    BoundaryChartLinearOrientationMapSourceOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1)

namespace BoundaryChartMathlibLinearOrientationAtlasSource

/-- Convert linear map-equality sources to the existing mathlib-orientation data record. -/
def toOrientationAtlasData
    (D : BoundaryChartMathlibLinearOrientationAtlasSource I M 𝓞) :
    BoundaryChartMathlibOrientationAtlasData I M 𝓞 where
  orientationData := D.orientationData
  charts := D.charts
  covers := D.covers
  compatibleOn := D.compatibleOn
  orientationMapDataOn := fun hx0 hx1 =>
    (D.orientationMapSourceOn hx0 hx1).toOrientationMapDataOn

/-- Forget linear map-equality sources to the project-local oriented atlas. -/
def toBoundaryChartOrientedAtlas
    (D : BoundaryChartMathlibLinearOrientationAtlasSource I M 𝓞) :
    BoundaryChartOrientedAtlas I M :=
  D.toOrientationAtlasData.toBoundaryChartOrientedAtlas

@[simp]
theorem charts_toOrientationAtlasData
    (D : BoundaryChartMathlibLinearOrientationAtlasSource I M 𝓞) :
    D.toOrientationAtlasData.charts = D.charts :=
  rfl

@[simp]
theorem charts_toBoundaryChartOrientedAtlas
    (D : BoundaryChartMathlibLinearOrientationAtlasSource I M 𝓞) :
    D.toBoundaryChartOrientedAtlas.charts = D.charts :=
  rfl

end BoundaryChartMathlibLinearOrientationAtlasSource

/--
Atlas-level source where the available theorem is positive tangential
Jacobian, not a concrete `Orientation.map` equality.

The constructor below uses `BoundaryChartOrientationMapData.ofJacobianPos` to
recover the linear orientation-map package.
-/
structure BoundaryChartPositiveJacobianAtlasSource
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (M : Type w) [TopologicalSpace M] [ChartedSpace H M]
    (𝓞 : Type v) where
  orientationData : 𝓞
  charts : Set M
  covers : ∀ p : M, ∃ x ∈ charts, p ∈ (extChartAt I x).source
  compatibleOn : ∀ {x0 x1 : M}, x0 ∈ charts -> x1 ∈ charts ->
    boundaryChartTransitionCompatibleOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1)
  jacobianPositiveOn : ∀ {x0 x1 : M}, x0 ∈ charts -> x1 ∈ charts ->
    boundaryChartOrientationCompatibleOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1)

namespace BoundaryChartPositiveJacobianAtlasSource

/-- Convert positive-Jacobian atlas data to the fieldized orientation-map record. -/
def toOrientationAtlasData
    (D : BoundaryChartPositiveJacobianAtlasSource I M 𝓞) :
    BoundaryChartMathlibOrientationAtlasData I M 𝓞 where
  orientationData := D.orientationData
  charts := D.charts
  covers := D.covers
  compatibleOn := D.compatibleOn
  orientationMapDataOn := fun {x0 x1} hx0 hx1 u hu =>
    BoundaryChartOrientationMapData.ofJacobianPos
      (I := I) (x0 := x0) (x1 := x1) (u := u)
      (D.jacobianPositiveOn hx0 hx1 u hu)

/-- Forget positive-Jacobian atlas data to the project-local oriented atlas. -/
def toBoundaryChartOrientedAtlas
    (D : BoundaryChartPositiveJacobianAtlasSource I M 𝓞) :
    BoundaryChartOrientedAtlas I M :=
  D.toOrientationAtlasData.toBoundaryChartOrientedAtlas

@[simp]
theorem charts_toOrientationAtlasData
    (D : BoundaryChartPositiveJacobianAtlasSource I M 𝓞) :
    D.toOrientationAtlasData.charts = D.charts :=
  rfl

@[simp]
theorem charts_toBoundaryChartOrientedAtlas
    (D : BoundaryChartPositiveJacobianAtlasSource I M 𝓞) :
    D.toBoundaryChartOrientedAtlas.charts = D.charts :=
  rfl

end BoundaryChartPositiveJacobianAtlasSource

namespace BoundaryChartMathlibOrientedAtlasBridge

/--
Recover the stronger `Orientation.map` atlas-data shape from the older bridge
that only stored project-local orientation preservation.

This does not add global mathlib content; it uses the existing determinant
bridge to manufacture `BoundaryChartOrientationMapDataOn`.
-/
def toOrientationMapAtlasData
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) :
    BoundaryChartMathlibOrientationAtlasData I M 𝓞 where
  orientationData := B.orientationData
  charts := B.charts
  covers := B.covers
  compatibleOn := B.compatibleOn
  orientationMapDataOn := fun hx0 hx1 =>
    B.orientationMapDataOn_boundarySource hx0 hx1

@[simp]
theorem charts_toOrientationMapAtlasData
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) :
    B.toOrientationMapAtlasData.charts = B.charts :=
  rfl

end BoundaryChartMathlibOrientedAtlasBridge

namespace BoundaryChartMathlibOrientationAtlasData

variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) -> Real}

/--
Selected-box boundary-sign data built directly from the stored
`Orientation.map` field.

This avoids passing through `BoundaryChartOrientedAtlas`, which would rebuild
orientation-map data from the weaker positive-frame predicate.
-/
def selectedBoxBoundarySignDataFromOrientationMapData
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b where
  selectedBox := hbox
  compatibleOn := by
    intro u hu
    exact D.compatibleOn hx0 hx1 u
      (lowerZeroFaceDomain_subset_boundaryChartTransitionBoundarySource_of_selectedBox
        hbox hu)
  orientationMapDataOn := by
    intro u hu
    exact D.orientationMapDataOn hx0 hx1 u
      (lowerZeroFaceDomain_subset_boundaryChartTransitionBoundarySource_of_selectedBox
        hbox hu)
  preservesOrientationOn :=
    boundaryChartPreservesOrientationOn_of_orientationMapDataOn I x0 x1 <| by
      intro u hu
      exact D.orientationMapDataOn hx0 hx1 u
        (lowerZeroFaceDomain_subset_boundaryChartTransitionBoundarySource_of_selectedBox
          hbox hu)

theorem selectedBoxBoundarySignDataFromOrientationMapData_jacobian_pos
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    {u : Fin n -> Real} (hu : u ∈ lowerZeroFaceDomain a b) :
    0 < boundaryChartTransitionJacobian I x0 x1 u :=
  (D.selectedBoxBoundarySignDataFromOrientationMapData hx0 hx1 hbox).jacobian_pos hu

theorem selectedBoxBoundarySignDataFromOrientationMapData_boundarySign_eq
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    halfSpaceBoundarySign n = outwardFirstBoundaryOrientationSign n :=
  (D.selectedBoxBoundarySignDataFromOrientationMapData hx0 hx1 hbox).boundarySign_eq_outwardFirst

end BoundaryChartMathlibOrientationAtlasData

namespace BoundaryChartMathlibOrientationManifoldData

variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) -> Real}

/-- All-chart version of the direct selected-box boundary-sign constructor. -/
def selectedBoxBoundarySignDataFromOrientationMapData
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b :=
  D.toAtlasData.selectedBoxBoundarySignDataFromOrientationMapData
    (mem_univ x0) (mem_univ x1) hbox

theorem selectedBoxBoundarySignDataFromOrientationMapData_jacobian_pos
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    {u : Fin n -> Real} (hu : u ∈ lowerZeroFaceDomain a b) :
    0 < boundaryChartTransitionJacobian I x0 x1 u :=
  (D.selectedBoxBoundarySignDataFromOrientationMapData hbox).jacobian_pos hu

theorem selectedBoxBoundarySignDataFromOrientationMapData_boundarySign_eq
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    halfSpaceBoundarySign n = outwardFirstBoundaryOrientationSign n :=
  (D.selectedBoxBoundarySignDataFromOrientationMapData hbox).boundarySign_eq_outwardFirst

end BoundaryChartMathlibOrientationManifoldData

end AtlasSources

end ManifoldBoundary

end Stokes

end
