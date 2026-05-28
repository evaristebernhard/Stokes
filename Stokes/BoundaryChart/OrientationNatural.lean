import Stokes.BoundaryChart.OrientationConvenience
import Stokes.BoundaryChart.SelectedBoxImageConstructor

/-!
# Natural selected-box orientation API

Short method-style names for the selected-box orientation wrappers attached to
`BoundaryChartOrientedAtlas` and `BoundaryChartOrientedManifold`.

This is a pure boundary-chart layer: it re-exports existing bridge and
constructor data with compact names and does not import the global Stokes
assembly.
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

/-- Selected-box orientation-map data from an oriented boundary atlas. -/
def selectedBoxOrientationData
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  A.selectedBox_orientationMapDataOn hx0 hx1 hbox

/-- Selected boxes preserve orientation for an oriented boundary atlas. -/
theorem selectedBoxPreservesOrientation
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartPreservesOrientationOn I x0 x1 (lowerZeroFaceDomain a b) :=
  A.selectedBox_preservesOrientationOn hx0 hx1 hbox

/-- Selected boxes are orientation-compatible for an oriented boundary atlas. -/
theorem selectedBoxOrientationCompatible
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  A.selectedBox_orientationCompatibleOn hx0 hx1 hbox

/-- Short alias for selected-box orientation compatibility. -/
theorem selectedBoxCompatible
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  A.selectedBoxOrientationCompatible hx0 hx1 hbox

/-- Selected-box orientation-COV data from an oriented boundary atlas. -/
def selectedBoxOrientationCovData
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  BoundaryChartSelectedBoxOrientationCovData.ofOrientedAtlas
    A hx0 hx1 hbox himage

/-- Selected-box oriented change of variables from packaged image data. -/
theorem selectedBoxChangeOfVariables
    (A : BoundaryChartOrientedAtlas I M) [IsManifold I 1 M] {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (A.selectedBoxOrientationCovData hx0 hx1 hbox himage).orientedChangeOfVariables

/-- Selected-box image-constructor data from an oriented boundary atlas. -/
def selectedBoxImageConstructor
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b :=
  BoundaryChartSelectedBoxImageConstructorData.ofOrientedAtlas
    A hx0 hx1 hbox target

/-- Selected-box orientation-COV data from a selected target image box. -/
def selectedBoxTargetOrientationCovData
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b
      target.lowerCorner target.upperCorner :=
  (A.selectedBoxImageConstructor hx0 hx1 hbox target).BoundaryChartSelectedBoxOrientationCovData

/-- Selected-box oriented change of variables from a selected target image box. -/
theorem selectedBoxTargetChangeOfVariables
    (A : BoundaryChartOrientedAtlas I M) [IsManifold I 1 M] {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (ω : ManifoldForm I M n) {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
      target.lowerCorner target.upperCorner :=
  (A.selectedBoxTargetOrientationCovData hx0 hx1 hbox target).orientedChangeOfVariables

end BoundaryChartOrientedAtlas

namespace BoundaryChartOrientedManifold

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/-- Selected-box orientation-map data from oriented boundary-manifold data. -/
def selectedBoxOrientationData
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  selectedBox_orientationMapDataOn (I := I) (M := M) hbox

/-- Selected boxes preserve orientation for oriented boundary-manifold data. -/
theorem selectedBoxPreservesOrientation
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartPreservesOrientationOn I x0 x1 (lowerZeroFaceDomain a b) :=
  selectedBox_preservesOrientationOn (I := I) (M := M) hbox

/-- Selected boxes are orientation-compatible for oriented boundary-manifold data. -/
theorem selectedBoxOrientationCompatible
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  selectedBox_orientationCompatibleOn (I := I) (M := M) hbox

/-- Short alias for selected-box orientation compatibility. -/
theorem selectedBoxCompatible
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  selectedBoxOrientationCompatible (I := I) (M := M) hbox

/-- Selected-box orientation-COV data from oriented boundary-manifold data. -/
def selectedBoxOrientationCovData
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  BoundaryChartSelectedBoxOrientationCovData.ofOrientedManifold hbox himage

/-- Selected-box oriented change of variables from packaged image data. -/
theorem selectedBoxChangeOfVariables
    [BoundaryChartOrientedManifold I M] [IsManifold I 1 M]
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (selectedBoxOrientationCovData (I := I) (M := M) hbox himage).orientedChangeOfVariables

/-- Selected-box image-constructor data from oriented boundary-manifold data. -/
def selectedBoxImageConstructor
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b :=
  BoundaryChartSelectedBoxImageConstructorData.ofOrientedManifold hbox target

/-- Selected-box orientation-COV data from a selected target image box. -/
def selectedBoxTargetOrientationCovData
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b
      target.lowerCorner target.upperCorner :=
  (selectedBoxImageConstructor
    (I := I) (M := M) hbox target).BoundaryChartSelectedBoxOrientationCovData

/-- Selected-box oriented change of variables from a selected target image box. -/
theorem selectedBoxTargetChangeOfVariables
    [BoundaryChartOrientedManifold I M] [IsManifold I 1 M]
    (x0 x1 : M) (ω : ManifoldForm I M n)
    {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
      target.lowerCorner target.upperCorner :=
  (selectedBoxTargetOrientationCovData (I := I) (M := M) hbox target).orientedChangeOfVariables

end BoundaryChartOrientedManifold

end ManifoldBoundary

end Stokes

end
