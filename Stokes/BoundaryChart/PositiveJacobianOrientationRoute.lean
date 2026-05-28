import Stokes.BoundaryChart.OrientationMapCompatibility
import Stokes.BoundaryChart.ChangeOfVariablesFamily

/-!
# Positive-Jacobian orientation route

This file exposes the currently usable route from positive tangential
Jacobian data to the `Orientation.map` and boundary-sign packages used by the
boundary chart Stokes layer.

It does not claim any global oriented-manifold API from mathlib.  Instead it
keeps the global source fieldized and proves the local conversion:

`boundaryChartOrientationCompatibleOn`
  -> `BoundaryChartOrientationMapDataOn`
  -> selected-box `BoundaryChartAtlasBoundarySignData`
  -> selected-box oriented COV data.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u v w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- Positive tangential Jacobian on a set produces pointwise mathlib
`Orientation.map` data for the boundary chart transition. -/
def boundaryChartOrientationMapDataOn_of_orientationCompatibleOn {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) {s : Set (Fin n → Real)}
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 s) :
    BoundaryChartOrientationMapDataOn I x0 x1 s := by
  intro u hu
  exact BoundaryChartOrientationMapData.ofJacobianPos
    (I := I) (x0 := x0) (x1 := x1) (u := u) (horient u hu)

/-- Positive tangential Jacobian can also be viewed as project-local
orientation preservation of the transported boundary frame. -/
theorem boundaryChartPreservesOrientationOn_of_orientationCompatibleOn {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) {s : Set (Fin n → Real)}
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 s) :
    boundaryChartPreservesOrientationOn I x0 x1 s := by
  intro u hu
  simpa [coordinateOrientationSign_boundaryChartTransitionFrame_eq_jacobian]
    using horient u hu

namespace BoundaryChartAtlasBoundarySignData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real}

/-- Build selected-box boundary-sign data directly from the positive-Jacobian
orientation predicate on the selected source face. -/
def ofOrientationCompatibleOn
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1
      (lowerZeroFaceDomain a b))
    (horient : boundaryChartOrientationCompatibleOn I x0 x1
      (lowerZeroFaceDomain a b)) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b where
  selectedBox := hbox
  compatibleOn := hcompat
  orientationMapDataOn :=
    boundaryChartOrientationMapDataOn_of_orientationCompatibleOn I x0 x1 horient
  preservesOrientationOn :=
    boundaryChartPreservesOrientationOn_of_orientationCompatibleOn I x0 x1 horient

/-- Variant using the older project-local orientation-preservation predicate. -/
def ofPreservesOrientationOn
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1
      (lowerZeroFaceDomain a b))
    (hpres : boundaryChartPreservesOrientationOn I x0 x1
      (lowerZeroFaceDomain a b)) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b :=
  ofOrientationCompatibleOn (I := I) (x0 := x0) (x1 := x1) hbox hcompat
    (boundaryChartOrientationCompatibleOn_of_preservesOrientationOn I x0 x1 hpres)

@[simp]
theorem ofOrientationCompatibleOn_selectedBox
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1
      (lowerZeroFaceDomain a b))
    (horient : boundaryChartOrientationCompatibleOn I x0 x1
      (lowerZeroFaceDomain a b)) :
    (ofOrientationCompatibleOn (I := I) (x0 := x0) (x1 := x1)
      hbox hcompat horient).selectedBox = hbox :=
  rfl

@[simp]
theorem ofOrientationCompatibleOn_compatibleOn
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1
      (lowerZeroFaceDomain a b))
    (horient : boundaryChartOrientationCompatibleOn I x0 x1
      (lowerZeroFaceDomain a b)) :
    (ofOrientationCompatibleOn (I := I) (x0 := x0) (x1 := x1)
      hbox hcompat horient).compatibleOn = hcompat :=
  rfl

theorem ofOrientationCompatibleOn_jacobian_pos
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1
      (lowerZeroFaceDomain a b))
    (horient : boundaryChartOrientationCompatibleOn I x0 x1
      (lowerZeroFaceDomain a b))
    {u : Fin n → Real} (hu : u ∈ lowerZeroFaceDomain a b) :
    0 < boundaryChartTransitionJacobian I x0 x1 u :=
  (ofOrientationCompatibleOn (I := I) (x0 := x0) (x1 := x1)
    hbox hcompat horient).jacobian_pos hu

/-- Direct selected-box orientation/COV data from positive-Jacobian data. -/
def orientationCovDataOfOrientationCompatibleOn
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1
      (lowerZeroFaceDomain a b))
    (horient : boundaryChartOrientationCompatibleOn I x0 x1
      (lowerZeroFaceDomain a b))
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  (ofOrientationCompatibleOn (I := I) (x0 := x0) (x1 := x1)
    hbox hcompat horient).toSelectedBoxOrientationCovData himage

/-- Direct selected-box oriented COV from positive-Jacobian data and image data. -/
theorem orientedChangeOfVariablesOfOrientationCompatibleOn
    [IsManifold I 1 M]
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1
      (lowerZeroFaceDomain a b))
    (horient : boundaryChartOrientationCompatibleOn I x0 x1
      (lowerZeroFaceDomain a b))
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (ofOrientationCompatibleOn (I := I) (x0 := x0) (x1 := x1)
    hbox hcompat horient).orientedChangeOfVariables himage

end BoundaryChartAtlasBoundarySignData

namespace BoundaryChartPositiveJacobianAtlasSource

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {𝓞 : Type v}

/-- Constructor whose orientation field is exactly positive tangential
Jacobian on natural boundary overlaps. -/
def ofOrientationCompatibleOn
    (orientationData : 𝓞)
    (charts : Set M)
    (covers : ∀ p : M, ∃ x ∈ charts, p ∈ (extChartAt I x).source)
    (hcompat : ∀ {x0 x1 : M}, x0 ∈ charts → x1 ∈ charts →
      boundaryChartTransitionCompatibleOn I x0 x1
        (boundaryChartTransitionBoundarySource I x0 x1))
    (horient : ∀ {x0 x1 : M}, x0 ∈ charts → x1 ∈ charts →
      boundaryChartOrientationCompatibleOn I x0 x1
        (boundaryChartTransitionBoundarySource I x0 x1)) :
    BoundaryChartPositiveJacobianAtlasSource I M 𝓞 where
  orientationData := orientationData
  charts := charts
  covers := covers
  compatibleOn := hcompat
  jacobianPositiveOn := horient

/-- Constructor from the older project-local orientation-preservation
predicate; the positive-Jacobian predicate is derived pointwise. -/
def ofPreservesOrientationOn
    (orientationData : 𝓞)
    (charts : Set M)
    (covers : ∀ p : M, ∃ x ∈ charts, p ∈ (extChartAt I x).source)
    (hcompat : ∀ {x0 x1 : M}, x0 ∈ charts → x1 ∈ charts →
      boundaryChartTransitionCompatibleOn I x0 x1
        (boundaryChartTransitionBoundarySource I x0 x1))
    (hpres : ∀ {x0 x1 : M}, x0 ∈ charts → x1 ∈ charts →
      boundaryChartPreservesOrientationOn I x0 x1
        (boundaryChartTransitionBoundarySource I x0 x1)) :
    BoundaryChartPositiveJacobianAtlasSource I M 𝓞 :=
  ofOrientationCompatibleOn (I := I) (M := M)
    orientationData charts covers hcompat <| fun {x0 x1} hx0 hx1 =>
      boundaryChartOrientationCompatibleOn_of_preservesOrientationOn I x0 x1
        (hpres hx0 hx1)

@[simp]
theorem charts_ofOrientationCompatibleOn
    (orientationData : 𝓞)
    (charts : Set M)
    (covers : ∀ p : M, ∃ x ∈ charts, p ∈ (extChartAt I x).source)
    (hcompat : ∀ {x0 x1 : M}, x0 ∈ charts → x1 ∈ charts →
      boundaryChartTransitionCompatibleOn I x0 x1
        (boundaryChartTransitionBoundarySource I x0 x1))
    (horient : ∀ {x0 x1 : M}, x0 ∈ charts → x1 ∈ charts →
      boundaryChartOrientationCompatibleOn I x0 x1
        (boundaryChartTransitionBoundarySource I x0 x1)) :
    (ofOrientationCompatibleOn (I := I) (M := M)
      orientationData charts covers hcompat horient).charts = charts :=
  rfl

/-- Selected-box boundary-sign data produced directly from the positive
Jacobian atlas source. -/
def selectedBoxBoundarySignData
    (D : BoundaryChartPositiveJacobianAtlasSource I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b :=
  D.toOrientationAtlasData.selectedBoxBoundarySignDataFromOrientationMapData
    hx0 hx1 hbox

/-- Selected-box orientation-map data produced by the positive-Jacobian route. -/
def selectedBoxOrientationMapDataOn
    (D : BoundaryChartPositiveJacobianAtlasSource I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (D.selectedBoxBoundarySignData hx0 hx1 hbox).orientationMapDataOn

theorem selectedBoxBoundarySignData_orientationCompatibleOn
    (D : BoundaryChartPositiveJacobianAtlasSource I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (D.selectedBoxBoundarySignData hx0 hx1 hbox).orientationCompatibleOn

theorem selectedBoxBoundarySignData_jacobian_pos
    (D : BoundaryChartPositiveJacobianAtlasSource I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    {u : Fin n → Real} (hu : u ∈ lowerZeroFaceDomain a b) :
    0 < boundaryChartTransitionJacobian I x0 x1 u :=
  (D.selectedBoxBoundarySignData hx0 hx1 hbox).jacobian_pos hu

theorem selectedBoxBoundarySignData_boundarySign_eq
    (D : BoundaryChartPositiveJacobianAtlasSource I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    halfSpaceBoundarySign n = outwardFirstBoundaryOrientationSign n :=
  (D.selectedBoxBoundarySignData hx0 hx1 hbox).boundarySign_eq_outwardFirst

/-- Selected-box orientation/COV data produced by the positive-Jacobian route. -/
def selectedBoxOrientationCovData
    (D : BoundaryChartPositiveJacobianAtlasSource I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  (D.selectedBoxBoundarySignData hx0 hx1 hbox).toSelectedBoxOrientationCovData
    himage

/-- Selected-box oriented COV produced by the positive-Jacobian route. -/
theorem selectedBoxOrientedChangeOfVariables
    [IsManifold I 1 M]
    (D : BoundaryChartPositiveJacobianAtlasSource I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (D.selectedBoxBoundarySignData hx0 hx1 hbox).orientedChangeOfVariables
    himage

end BoundaryChartPositiveJacobianAtlasSource

namespace BoundaryChartOrientedAtlas

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/-- View an existing project-local oriented atlas through the positive
Jacobian route. -/
def toPositiveJacobianAtlasSource
    (A : BoundaryChartOrientedAtlas I M) :
    BoundaryChartPositiveJacobianAtlasSource I M Unit :=
  BoundaryChartPositiveJacobianAtlasSource.ofPreservesOrientationOn
    (I := I) (M := M) () A.charts A.covers A.compatibleOn A.preservesOrientationOn

@[simp]
theorem charts_toPositiveJacobianAtlasSource
    (A : BoundaryChartOrientedAtlas I M) :
    A.toPositiveJacobianAtlasSource.charts = A.charts :=
  rfl

/-- Selected-box boundary-sign data rebuilt through the positive-Jacobian
route. -/
def selectedBoxBoundarySignDataFromPositiveJacobian
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b :=
  A.toPositiveJacobianAtlasSource.selectedBoxBoundarySignData hx0 hx1 hbox

end BoundaryChartOrientedAtlas

namespace BoundaryChartMathlibOrientedAtlasBridge

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {𝓞 : Type v}

/-- View the older mathlib-facing bridge through the positive-Jacobian route. -/
def toPositiveJacobianAtlasSource
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) :
    BoundaryChartPositiveJacobianAtlasSource I M 𝓞 :=
  BoundaryChartPositiveJacobianAtlasSource.ofPreservesOrientationOn
    (I := I) (M := M)
    B.orientationData B.charts B.covers B.compatibleOn B.preservesOrientationOn

@[simp]
theorem charts_toPositiveJacobianAtlasSource
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) :
    B.toPositiveJacobianAtlasSource.charts = B.charts :=
  rfl

/-- Selected-box boundary-sign data rebuilt through positive Jacobian rather
than a preexisting project-local orientation-map package. -/
def selectedBoxBoundarySignDataFromPositiveJacobian
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ B.charts) (hx1 : x1 ∈ B.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b :=
  B.toPositiveJacobianAtlasSource.selectedBoxBoundarySignData hx0 hx1 hbox

end BoundaryChartMathlibOrientedAtlasBridge

namespace BoundaryChartMathlibOrientedManifoldBridge

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {𝓞 : Type v}

/-- All-chart positive-Jacobian route for the older mathlib-facing bridge. -/
def toPositiveJacobianAtlasSource
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) :
    BoundaryChartPositiveJacobianAtlasSource I M 𝓞 :=
  B.toMathlibOrientedAtlasBridge.toPositiveJacobianAtlasSource

@[simp]
theorem charts_toPositiveJacobianAtlasSource
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) :
    B.toPositiveJacobianAtlasSource.charts = univ :=
  rfl

/-- All-chart selected-box boundary-sign data via positive Jacobian. -/
def selectedBoxBoundarySignDataFromPositiveJacobian
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b :=
  B.toPositiveJacobianAtlasSource.selectedBoxBoundarySignData
    (mem_univ x0) (mem_univ x1) hbox

end BoundaryChartMathlibOrientedManifoldBridge

namespace BoundaryChartMathlibOrientationAtlasData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {𝓞 : Type v}

/-- Forget a stronger orientation-map atlas source to the positive-Jacobian
route. -/
def toPositiveJacobianAtlasSource
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞) :
    BoundaryChartPositiveJacobianAtlasSource I M 𝓞 where
  orientationData := D.orientationData
  charts := D.charts
  covers := D.covers
  compatibleOn := D.compatibleOn
  jacobianPositiveOn := fun hx0 hx1 => D.orientationCompatibleOn hx0 hx1

@[simp]
theorem charts_toPositiveJacobianAtlasSource
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞) :
    D.toPositiveJacobianAtlasSource.charts = D.charts :=
  rfl

end BoundaryChartMathlibOrientationAtlasData

namespace BoundaryChartMathlibOrientationManifoldData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {𝓞 : Type v}

/-- All-chart positive-Jacobian route from a stronger orientation-map source. -/
def toPositiveJacobianAtlasSource
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞) :
    BoundaryChartPositiveJacobianAtlasSource I M 𝓞 :=
  D.toAtlasData.toPositiveJacobianAtlasSource

@[simp]
theorem charts_toPositiveJacobianAtlasSource
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞) :
    D.toPositiveJacobianAtlasSource.charts = univ :=
  rfl

end BoundaryChartMathlibOrientationManifoldData

end ManifoldBoundary

end Stokes

end
