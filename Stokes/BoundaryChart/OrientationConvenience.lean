import Stokes.BoundaryChart.OrientedAtlasBridge

/-!
# Boundary-chart orientation convenience wrappers

Short selected-box wrappers for the orientation API.  These declarations keep
the user-facing names small while delegating all content to the bridge layer in
`OrientedAtlasBridge.lean` and `OrientationBridge.lean`.
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

/-- Selected-box orientation-map data from oriented-atlas data. -/
def selectedBox_orientationMapDataOn
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  A.orientationMapDataOn_selectedBox hx0 hx1 hbox

/-- Selected boxes preserve the boundary orientation under oriented-atlas data. -/
theorem selectedBox_preservesOrientationOn
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartPreservesOrientationOn I x0 x1 (lowerZeroFaceDomain a b) :=
  boundaryChartPreservesOrientationOn_of_orientationMapDataOn I x0 x1
    (A.selectedBox_orientationMapDataOn hx0 hx1 hbox)

/-- Selected boxes are orientation-compatible under oriented-atlas data. -/
theorem selectedBox_orientationCompatibleOn
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  boundaryChartOrientationCompatibleOn_of_orientationMapDataOn I x0 x1
    (A.selectedBox_orientationMapDataOn hx0 hx1 hbox)

/-- Short alias for selected-box orientation compatibility under oriented-atlas data. -/
theorem selectedBox_compatibleOn
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  A.selectedBox_orientationCompatibleOn hx0 hx1 hbox

end BoundaryChartOrientedAtlas

namespace BoundaryChartOrientedManifold

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/-- Selected-box orientation-map data from global oriented-manifold data. -/
def selectedBox_orientationMapDataOn
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  orientationMapDataOn_selectedBox (I := I) (M := M) hbox

/-- Selected boxes preserve the boundary orientation under global oriented-manifold data. -/
theorem selectedBox_preservesOrientationOn
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartPreservesOrientationOn I x0 x1 (lowerZeroFaceDomain a b) :=
  boundaryChartPreservesOrientationOn_of_orientationMapDataOn I x0 x1
    (selectedBox_orientationMapDataOn (I := I) (M := M) hbox)

/-- Selected boxes are orientation-compatible under global oriented-manifold data. -/
theorem selectedBox_orientationCompatibleOn
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  boundaryChartOrientationCompatibleOn_of_orientationMapDataOn I x0 x1
    (selectedBox_orientationMapDataOn (I := I) (M := M) hbox)

/-- Short alias for selected-box orientation compatibility under global oriented-manifold data. -/
theorem selectedBox_compatibleOn
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  selectedBox_orientationCompatibleOn (I := I) (M := M) hbox

end BoundaryChartOrientedManifold

/-- Selected-box orientation-map data from oriented-atlas data. -/
def orientedAtlas_selectedBox_orientationMapDataOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  A.selectedBox_orientationMapDataOn hx0 hx1 hbox

/-- Selected boxes preserve the boundary orientation under oriented-atlas data. -/
theorem orientedAtlas_selectedBox_preservesOrientationOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartPreservesOrientationOn I x0 x1 (lowerZeroFaceDomain a b) :=
  A.selectedBox_preservesOrientationOn hx0 hx1 hbox

/-- Selected boxes are orientation-compatible under oriented-atlas data. -/
theorem orientedAtlas_selectedBox_compatibleOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  A.selectedBox_compatibleOn hx0 hx1 hbox

/-- Selected-box orientation-map data from global oriented-manifold data. -/
def orientedManifold_selectedBox_orientationMapDataOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  BoundaryChartOrientedManifold.selectedBox_orientationMapDataOn
    (I := I) (M := M) hbox

/-- Selected boxes preserve the boundary orientation under global oriented-manifold data. -/
theorem orientedManifold_selectedBox_preservesOrientationOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartPreservesOrientationOn I x0 x1 (lowerZeroFaceDomain a b) :=
  BoundaryChartOrientedManifold.selectedBox_preservesOrientationOn
    (I := I) (M := M) hbox

/-- Selected boxes are orientation-compatible under global oriented-manifold data. -/
theorem orientedManifold_selectedBox_compatibleOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  BoundaryChartOrientedManifold.selectedBox_compatibleOn
    (I := I) (M := M) hbox

end ManifoldBoundary

end Stokes

end
