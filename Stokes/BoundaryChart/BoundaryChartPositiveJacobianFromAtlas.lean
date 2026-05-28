import Stokes.BoundaryChart.PositiveJacobianOrientationRoute

/-!
# Positive-Jacobian selected-box routes from atlas sources

This file is a thin convenience layer over the existing orientation bridge
files.  It records the shortest currently available routes from the project
local oriented-atlas records, the fieldized mathlib-facing records, and the
positive-Jacobian atlas source to the selected-box data consumed by boundary
chart Stokes:

* `boundaryChartOrientationCompatibleOn` on the selected lower face;
* `BoundaryChartAtlasBoundarySignData`;
* `BoundaryChartSelectedBoxOrientationCovData`;
* selected-box oriented change of variables.

No global mathlib oriented-manifold API is assumed here.  The global inputs
remain the precise bridge records already defined in
`OrientationMathlibBridge.lean`, `OrientedAtlasFromMathlib.lean`, and
`OrientationMapCompatibility.lean`.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u v w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace BoundaryChartAtlasBoundarySignData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real}

/-- Alias emphasizing that boundary-sign data already contains the selected
positive-Jacobian compatibility predicate. -/
theorem selectedBoxOrientationCompatible
    (D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  D.orientationCompatibleOn

/-- Alias emphasizing the route from selected-box boundary-sign data to
selected-box orientation/COV data. -/
def selectedBoxOrientationCovDataFromPositiveJacobian
    (D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  D.toSelectedBoxOrientationCovData himage

end BoundaryChartAtlasBoundarySignData

namespace BoundaryChartPositiveJacobianAtlasSource

variable {𝓞 : Type v}
variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real}

/-- The positive-Jacobian atlas source gives selected-box orientation
compatibility directly. -/
theorem selectedBoxOrientationCompatible
    (D : BoundaryChartPositiveJacobianAtlasSource I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  D.selectedBoxBoundarySignData_orientationCompatibleOn hx0 hx1 hbox

/-- Stable alias for selected-box boundary-sign data from a positive-Jacobian
atlas source. -/
def selectedBoxBoundarySignDataFromAtlasSource
    (D : BoundaryChartPositiveJacobianAtlasSource I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b :=
  D.selectedBoxBoundarySignData hx0 hx1 hbox

@[simp]
theorem selectedBoxBoundarySignDataFromAtlasSource_eq
    (D : BoundaryChartPositiveJacobianAtlasSource I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    D.selectedBoxBoundarySignDataFromAtlasSource hx0 hx1 hbox =
      D.selectedBoxBoundarySignData hx0 hx1 hbox :=
  rfl

/-- Positive-Jacobian atlas source to selected-box orientation/COV data. -/
def selectedBoxOrientationCovDataFromAtlasSource
    (D : BoundaryChartPositiveJacobianAtlasSource I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  D.selectedBoxOrientationCovData hx0 hx1 hbox himage

/-- Positive-Jacobian atlas source to selected-box oriented COV. -/
theorem selectedBoxOrientedChangeOfVariablesFromAtlasSource
    [IsManifold I 1 M]
    (D : BoundaryChartPositiveJacobianAtlasSource I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  D.selectedBoxOrientedChangeOfVariables hx0 hx1 hbox himage

end BoundaryChartPositiveJacobianAtlasSource

namespace BoundaryChartOrientedAtlas

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real}

/-- Short direct route from a project-local oriented atlas to selected-box
orientation compatibility. -/
theorem selectedBoxOrientationCompatibleFromAtlas
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  A.selectedBoxBoundarySignData_orientationCompatibleOn hx0 hx1 hbox

/-- Stable alias for the direct selected-box boundary-sign package from an
oriented atlas. -/
def selectedBoxBoundarySignDataFromAtlas
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b :=
  A.selectedBoxBoundarySignData hx0 hx1 hbox

@[simp]
theorem selectedBoxBoundarySignDataFromAtlas_eq
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    A.selectedBoxBoundarySignDataFromAtlas hx0 hx1 hbox =
      A.selectedBoxBoundarySignData hx0 hx1 hbox :=
  rfl

/-- Direct selected-box orientation/COV package from an oriented atlas. -/
def selectedBoxOrientationCovDataFromAtlas
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  (A.selectedBoxBoundarySignDataFromAtlas hx0 hx1 hbox).toSelectedBoxOrientationCovData
    himage

/-- Direct selected-box oriented COV from an oriented atlas. -/
theorem selectedBoxOrientedChangeOfVariablesFromAtlas
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (A.selectedBoxBoundarySignDataFromAtlas hx0 hx1 hbox).orientedChangeOfVariables
    himage

/-- The same selected-box orientation compatibility, routed through the
positive-Jacobian atlas source view. -/
theorem selectedBoxOrientationCompatibleFromPositiveJacobian
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (A.selectedBoxBoundarySignDataFromPositiveJacobian hx0 hx1 hbox).orientationCompatibleOn

/-- Oriented-atlas data viewed through the positive-Jacobian route, packaged
as selected-box orientation/COV data. -/
def selectedBoxOrientationCovDataFromPositiveJacobian
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  (A.selectedBoxBoundarySignDataFromPositiveJacobian hx0 hx1 hbox).toSelectedBoxOrientationCovData
    himage

/-- Oriented-atlas data viewed through the positive-Jacobian route, then
projected to selected-box oriented COV. -/
theorem selectedBoxOrientedChangeOfVariablesFromPositiveJacobian
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (A.selectedBoxBoundarySignDataFromPositiveJacobian hx0 hx1 hbox).orientedChangeOfVariables
    himage

end BoundaryChartOrientedAtlas

namespace BoundaryChartMathlibOrientedAtlasBridge

variable {𝓞 : Type v}
variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real}

/-- Mathlib-facing oriented-atlas bridge to selected-box orientation
compatibility, using its project-local atlas projection. -/
theorem selectedBoxOrientationCompatibleFromBridge
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (hx0 : x0 ∈ B.charts) (hx1 : x1 ∈ B.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (B.selectedBoxBoundarySignData hx0 hx1 hbox).orientationCompatibleOn

/-- Stable selected-box boundary-sign package from a mathlib-facing
oriented-atlas bridge. -/
def selectedBoxBoundarySignDataFromBridge
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (hx0 : x0 ∈ B.charts) (hx1 : x1 ∈ B.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b :=
  B.selectedBoxBoundarySignData hx0 hx1 hbox

/-- Mathlib-facing oriented-atlas bridge to selected-box orientation/COV data. -/
def selectedBoxOrientationCovDataFromBridge
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (hx0 : x0 ∈ B.charts) (hx1 : x1 ∈ B.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  (B.selectedBoxBoundarySignDataFromBridge hx0 hx1 hbox).toSelectedBoxOrientationCovData
    himage

/-- Mathlib-facing oriented-atlas bridge to selected-box oriented COV. -/
theorem selectedBoxOrientedChangeOfVariablesFromBridge
    [IsManifold I 1 M]
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (hx0 : x0 ∈ B.charts) (hx1 : x1 ∈ B.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (B.selectedBoxBoundarySignDataFromBridge hx0 hx1 hbox).orientedChangeOfVariables
    himage

/-- Mathlib-facing oriented-atlas bridge to selected-box orientation
compatibility, routed through the positive-Jacobian source view. -/
theorem selectedBoxOrientationCompatibleFromPositiveJacobian
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (hx0 : x0 ∈ B.charts) (hx1 : x1 ∈ B.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (B.selectedBoxBoundarySignDataFromPositiveJacobian hx0 hx1 hbox).orientationCompatibleOn

/-- Mathlib-facing oriented-atlas bridge through the positive-Jacobian route,
packaged as selected-box orientation/COV data. -/
def selectedBoxOrientationCovDataFromPositiveJacobian
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (hx0 : x0 ∈ B.charts) (hx1 : x1 ∈ B.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  (B.selectedBoxBoundarySignDataFromPositiveJacobian hx0 hx1 hbox).toSelectedBoxOrientationCovData
    himage

/-- Mathlib-facing oriented-atlas bridge through the positive-Jacobian route,
then projected to selected-box oriented COV. -/
theorem selectedBoxOrientedChangeOfVariablesFromPositiveJacobian
    [IsManifold I 1 M]
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (hx0 : x0 ∈ B.charts) (hx1 : x1 ∈ B.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (B.selectedBoxBoundarySignDataFromPositiveJacobian hx0 hx1 hbox).orientedChangeOfVariables
    himage

end BoundaryChartMathlibOrientedAtlasBridge

namespace BoundaryChartMathlibOrientedManifoldBridge

variable {𝓞 : Type v}
variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real}

/-- Mathlib-facing oriented-manifold bridge to selected-box orientation
compatibility. -/
theorem selectedBoxOrientationCompatibleFromBridge
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (B.selectedBoxBoundarySignData hbox).orientationCompatibleOn

/-- Stable selected-box boundary-sign package from a mathlib-facing
oriented-manifold bridge. -/
def selectedBoxBoundarySignDataFromBridge
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b :=
  B.selectedBoxBoundarySignData hbox

/-- Mathlib-facing oriented-manifold bridge to selected-box orientation/COV
data. -/
def selectedBoxOrientationCovDataFromBridge
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  (B.selectedBoxBoundarySignDataFromBridge hbox).toSelectedBoxOrientationCovData
    himage

/-- Mathlib-facing oriented-manifold bridge to selected-box oriented COV. -/
theorem selectedBoxOrientedChangeOfVariablesFromBridge
    [IsManifold I 1 M]
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (B.selectedBoxBoundarySignDataFromBridge hbox).orientedChangeOfVariables
    himage

/-- Mathlib-facing oriented-manifold bridge to selected-box orientation
compatibility, routed through the positive-Jacobian source view. -/
theorem selectedBoxOrientationCompatibleFromPositiveJacobian
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (B.selectedBoxBoundarySignDataFromPositiveJacobian hbox).orientationCompatibleOn

/-- Mathlib-facing oriented-manifold bridge through the positive-Jacobian
route, packaged as selected-box orientation/COV data. -/
def selectedBoxOrientationCovDataFromPositiveJacobian
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  (B.selectedBoxBoundarySignDataFromPositiveJacobian hbox).toSelectedBoxOrientationCovData
    himage

/-- Mathlib-facing oriented-manifold bridge through the positive-Jacobian
route, then projected to selected-box oriented COV. -/
theorem selectedBoxOrientedChangeOfVariablesFromPositiveJacobian
    [IsManifold I 1 M]
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (B.selectedBoxBoundarySignDataFromPositiveJacobian hbox).orientedChangeOfVariables
    himage

end BoundaryChartMathlibOrientedManifoldBridge

namespace BoundaryChartMathlibOrientationAtlasData

variable {𝓞 : Type v}
variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real}

/-- The shortest route from mathlib orientation-map atlas data to selected-box
orientation compatibility. -/
theorem selectedBoxOrientationCompatibleFromOrientationMapData
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (D.selectedBoxBoundarySignDataFromOrientationMapData hx0 hx1 hbox).orientationCompatibleOn

/-- Mathlib orientation-map atlas data to selected-box orientation/COV data. -/
def selectedBoxOrientationCovDataFromOrientationMapData
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  (D.selectedBoxBoundarySignDataFromOrientationMapData hx0 hx1 hbox).toSelectedBoxOrientationCovData
    himage

/-- Mathlib orientation-map atlas data to selected-box oriented COV. -/
theorem selectedBoxOrientedChangeOfVariablesFromOrientationMapData
    [IsManifold I 1 M]
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (D.selectedBoxBoundarySignDataFromOrientationMapData hx0 hx1 hbox).orientedChangeOfVariables
    himage

/-- Mathlib orientation-map atlas data forgotten to the positive-Jacobian
route, then packaged as selected-box boundary-sign data. -/
def selectedBoxBoundarySignDataFromPositiveJacobian
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b :=
  D.toPositiveJacobianAtlasSource.selectedBoxBoundarySignData hx0 hx1 hbox

/-- Mathlib orientation-map atlas data to selected-box orientation
compatibility through the positive-Jacobian route. -/
theorem selectedBoxOrientationCompatibleFromPositiveJacobian
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (D.selectedBoxBoundarySignDataFromPositiveJacobian hx0 hx1 hbox).orientationCompatibleOn

/-- Mathlib orientation-map atlas data through the positive-Jacobian route,
packaged as selected-box orientation/COV data. -/
def selectedBoxOrientationCovDataFromPositiveJacobian
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  (D.selectedBoxBoundarySignDataFromPositiveJacobian hx0 hx1 hbox).toSelectedBoxOrientationCovData
    himage

/-- Mathlib orientation-map atlas data through the positive-Jacobian route,
then projected to selected-box oriented COV. -/
theorem selectedBoxOrientedChangeOfVariablesFromPositiveJacobian
    [IsManifold I 1 M]
    (D : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (D.selectedBoxBoundarySignDataFromPositiveJacobian hx0 hx1 hbox).orientedChangeOfVariables
    himage

end BoundaryChartMathlibOrientationAtlasData

namespace BoundaryChartMathlibOrientationManifoldData

variable {𝓞 : Type v}
variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real}

/-- The shortest route from all-chart mathlib orientation-map data to
selected-box orientation compatibility. -/
theorem selectedBoxOrientationCompatibleFromOrientationMapData
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (D.selectedBoxBoundarySignDataFromOrientationMapData hbox).orientationCompatibleOn

/-- All-chart mathlib orientation-map data to selected-box orientation/COV
data. -/
def selectedBoxOrientationCovDataFromOrientationMapData
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  (D.selectedBoxBoundarySignDataFromOrientationMapData hbox).toSelectedBoxOrientationCovData
    himage

/-- All-chart mathlib orientation-map data to selected-box oriented COV. -/
theorem selectedBoxOrientedChangeOfVariablesFromOrientationMapData
    [IsManifold I 1 M]
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (D.selectedBoxBoundarySignDataFromOrientationMapData hbox).orientedChangeOfVariables
    himage

/-- All-chart mathlib orientation-map data forgotten to the positive-Jacobian
route, then packaged as selected-box boundary-sign data. -/
def selectedBoxBoundarySignDataFromPositiveJacobian
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b :=
  D.toPositiveJacobianAtlasSource.selectedBoxBoundarySignData
    (mem_univ x0) (mem_univ x1) hbox

/-- All-chart mathlib orientation-map data to selected-box orientation
compatibility through the positive-Jacobian route. -/
theorem selectedBoxOrientationCompatibleFromPositiveJacobian
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (D.selectedBoxBoundarySignDataFromPositiveJacobian hbox).orientationCompatibleOn

/-- All-chart mathlib orientation-map data through the positive-Jacobian route,
packaged as selected-box orientation/COV data. -/
def selectedBoxOrientationCovDataFromPositiveJacobian
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  (D.selectedBoxBoundarySignDataFromPositiveJacobian hbox).toSelectedBoxOrientationCovData
    himage

/-- All-chart mathlib orientation-map data through the positive-Jacobian route,
then projected to selected-box oriented COV. -/
theorem selectedBoxOrientedChangeOfVariablesFromPositiveJacobian
    [IsManifold I 1 M]
    (D : BoundaryChartMathlibOrientationManifoldData I M 𝓞)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (D.selectedBoxBoundarySignDataFromPositiveJacobian hbox).orientedChangeOfVariables
    himage

end BoundaryChartMathlibOrientationManifoldData

namespace BoundaryChartMathlibLinearOrientationAtlasSource

variable {𝓞 : Type v}
variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real}

/-- Linear `Orientation.map` atlas source to selected-box boundary-sign data,
via the exact orientation-map atlas-data bridge. -/
def selectedBoxBoundarySignData
    (D : BoundaryChartMathlibLinearOrientationAtlasSource I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b :=
  D.toOrientationAtlasData.selectedBoxBoundarySignDataFromOrientationMapData
    hx0 hx1 hbox

/-- Linear `Orientation.map` atlas source to selected-box orientation
compatibility. -/
theorem selectedBoxOrientationCompatible
    (D : BoundaryChartMathlibLinearOrientationAtlasSource I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (D.selectedBoxBoundarySignData hx0 hx1 hbox).orientationCompatibleOn

/-- Linear `Orientation.map` atlas source to selected-box orientation/COV data. -/
def selectedBoxOrientationCovData
    (D : BoundaryChartMathlibLinearOrientationAtlasSource I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  (D.selectedBoxBoundarySignData hx0 hx1 hbox).toSelectedBoxOrientationCovData
    himage

/-- Linear `Orientation.map` atlas source to selected-box oriented COV. -/
theorem selectedBoxOrientedChangeOfVariables
    [IsManifold I 1 M]
    (D : BoundaryChartMathlibLinearOrientationAtlasSource I M 𝓞)
    (hx0 : x0 ∈ D.charts) (hx1 : x1 ∈ D.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (D.selectedBoxBoundarySignData hx0 hx1 hbox).orientedChangeOfVariables
    himage

end BoundaryChartMathlibLinearOrientationAtlasSource

end ManifoldBoundary

end Stokes

end
