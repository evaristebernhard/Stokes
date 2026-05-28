import Stokes.BoundaryChart.BoundaryBoxSelection
import Stokes.BoundaryChart.TargetBoxSelection
import Stokes.BoundaryChart.OrientationCovBridge

/-!
# Selected boundary-box image constructors

This file is a pure boundary-chart glue layer.  It combines a selected source
boundary box, a selected target image box (compact image plus local inverse),
and the orientation-map hypotheses into the packages consumed by the boundary
change-of-variables wrappers.
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
Unified input package for the selected-box image-data constructor.

The source field is the selected boundary box used for chart derivatives.  The
target-selection field stores the target box together with the two image halves:
compact image control and local right-inverse data.  The final two fields are
exactly the orientation-facing hypotheses needed to package oriented
change-of-variables data.
-/
structure BoundaryChartSelectedBoxImageConstructorData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) where
  /-- The selected source boundary box. -/
  selectedBox :
    boundaryChartSelectedBox I x0 x1 ω a b
  /-- The selected target image box, including compact image and local inverse data. -/
  targetSelection :
    BoundaryChartTargetBoxSelection I x0 x1 a b
  /-- Boundary-face and tangential compatibility on the source boundary box. -/
  compatibleOn :
    boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b)
  /-- Mathlib-orientation-facing pointwise data on the source boundary box. -/
  orientationMapDataOn :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b)

namespace BoundaryChartSelectedBoxImageConstructorData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/-- Lower corner of the selected target boundary-coordinate box. -/
def targetLowerCorner
    (data : BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b) :
    Fin (n + 1) → Real :=
  data.targetSelection.lowerCorner

/-- Upper corner of the selected target boundary-coordinate box. -/
def targetUpperCorner
    (data : BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b) :
    Fin (n + 1) → Real :=
  data.targetSelection.upperCorner

theorem targetLowerCorner_zero
    (data : BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b) :
    data.targetLowerCorner 0 = 0 :=
  data.targetSelection.lowerCorner_zero

theorem targetLower_le_targetUpper
    (data : BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b) :
    data.targetLowerCorner ≤ data.targetUpperCorner :=
  data.targetSelection.lower_le_upper

/-- Compact image control stored in the selected target box. -/
theorem compactImage
    (data : BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b) :
    boundaryChartCompactImageBoxSelection I x0 x1 a b
      data.targetLowerCorner data.targetUpperCorner :=
  data.targetSelection.compactImage

/-- Local right-inverse data stored in the selected target box. -/
theorem localInverseData
    (data : BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b) :
    boundaryChartLocalInverseData I x0 x1 a b
      data.targetLowerCorner data.targetUpperCorner :=
  data.targetSelection.localInverse

/-- Map-to projection of the packaged image data. -/
theorem mapsTo
    (data : BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b) :
    MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b)
      (lowerZeroFaceDomain data.targetLowerCorner data.targetUpperCorner) :=
  data.compactImage.mapsTo

/-- Surjectivity projection supplied by the packaged local inverse. -/
theorem surjOn
    (data : BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b) :
    SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b)
      (lowerZeroFaceDomain data.targetLowerCorner data.targetUpperCorner) :=
  data.localInverseData.surjOn

/-- The image-data package consumed by boundary chart-change wrappers. -/
theorem boundaryChartSelectedBoxImageData
    (data : BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b) :
    _root_.Stokes.boundaryChartSelectedBoxImageData I x0 x1 a b
      data.targetLowerCorner data.targetUpperCorner :=
  data.targetSelection.imageData

/-- Short alias for the selected-box image-data package. -/
theorem imageData
    (data : BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b) :
    _root_.Stokes.boundaryChartSelectedBoxImageData I x0 x1 a b
      data.targetLowerCorner data.targetUpperCorner :=
  data.boundaryChartSelectedBoxImageData

/-- The selected-box orientation-COV package produced from the unified input. -/
def BoundaryChartSelectedBoxOrientationCovData
    (data : BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b) :
    _root_.Stokes.BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b
      data.targetLowerCorner data.targetUpperCorner where
  selectedBox := data.selectedBox
  compatibleOn := data.compatibleOn
  orientationMapDataOn := data.orientationMapDataOn
  imageData := data.imageData

/-- Projection to the orientation-COV bridge data. -/
def orientationCovData [IsManifold I 1 M]
    (data : BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b) :
    BoundaryChartOrientationCovData I x0 x1 a b
      data.targetLowerCorner data.targetUpperCorner :=
  data.BoundaryChartSelectedBoxOrientationCovData.toOrientationCovData

/-- The oriented boundary chart change-of-variables package. -/
theorem boundaryChartOrientedChangeOfVariables [IsManifold I 1 M]
    (data : BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b) :
    _root_.Stokes.boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
      data.targetLowerCorner data.targetUpperCorner :=
  data.BoundaryChartSelectedBoxOrientationCovData.orientedChangeOfVariables

/-- Constructor from an already packaged compact boundary box and target selection. -/
def ofBoundaryCompactBoxSelectionData
    (source : BoundaryCompactBoxSelectionData I x0 x1 ω)
    (target : BoundaryChartTargetBoxSelection I x0 x1 source.a source.b)
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1
        (lowerZeroFaceDomain source.a source.b))
    (hdata :
      BoundaryChartOrientationMapDataOn I x0 x1
        (lowerZeroFaceDomain source.a source.b)) :
    BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω source.a source.b where
  selectedBox := source.selectedBox
  targetSelection := target
  compatibleOn := hcompat
  orientationMapDataOn := hdata

/--
Constructor from the selected source box, the two target-image halves, and
explicit orientation-map COV hypotheses.
-/
def ofCompactImageLocalInverseData
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (c d : Fin (n + 1) → Real) (hc0 : c 0 = 0) (hle : c ≤ d)
    (hcompact : boundaryChartCompactImageBoxSelection I x0 x1 a b c d)
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d)
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hdata :
      BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b)) :
    BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b where
  selectedBox := hbox
  targetSelection :=
    BoundaryChartTargetBoxSelection.mkOfCompactImageLocalInverseData
      c d hc0 hle hcompact hlocal
  compatibleOn := hcompat
  orientationMapDataOn := hdata

/-- Constructor from oriented-atlas data and a packaged target-box selection. -/
def ofOrientedAtlas
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b where
  selectedBox := hbox
  targetSelection := target
  compatibleOn := A.transitionCompatibleOn_selectedBox hx0 hx1 hbox
  orientationMapDataOn := A.orientationMapDataOn_selectedBox hx0 hx1 hbox

/-- Constructor from an oriented boundary-charted manifold and target-box selection. -/
def ofOrientedManifold [BoundaryChartOrientedManifold I M]
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b where
  selectedBox := hbox
  targetSelection := target
  compatibleOn := boundaryChartTransitionCompatibleOn_selectedBox_of_orientedManifold hbox
  orientationMapDataOn :=
    boundaryChartOrientationMapDataOn_selectedBox_of_orientedManifold hbox

end BoundaryChartSelectedBoxImageConstructorData

/-- Top-level image-data projection from the unified constructor package. -/
theorem boundaryChartSelectedBoxImageData_of_selectedBoxImageConstructorData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real}
    (data : BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b) :
    boundaryChartSelectedBoxImageData I x0 x1 a b
      data.targetLowerCorner data.targetUpperCorner :=
  data.imageData

namespace BoundaryChartSelectedBoxOrientationCovData

/-- Build selected-box orientation-COV data from the unified constructor package. -/
def ofSelectedBoxImageConstructorData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real}
    (data : BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b
      data.targetLowerCorner data.targetUpperCorner :=
  data.BoundaryChartSelectedBoxOrientationCovData

end BoundaryChartSelectedBoxOrientationCovData

/-- Top-level oriented-COV projection from the unified constructor package. -/
theorem boundaryChartOrientedChangeOfVariables_of_selectedBoxImageConstructorData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real}
    (data : BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
      data.targetLowerCorner data.targetUpperCorner :=
  data.boundaryChartOrientedChangeOfVariables

/--
Direct oriented-atlas wrapper from a selected source box and target-box
selection to the oriented change-of-variables package.
-/
theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_targetSelection_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (ω : ManifoldForm I M n) {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
      target.lowerCorner target.upperCorner :=
  (BoundaryChartSelectedBoxImageConstructorData.ofOrientedAtlas
    A hx0 hx1 hbox target).boundaryChartOrientedChangeOfVariables

/--
Direct oriented-manifold wrapper from a selected source box and target-box
selection to the oriented change-of-variables package.
-/
theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_targetSelection_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 : M) (ω : ManifoldForm I M n)
    {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
      target.lowerCorner target.upperCorner :=
  (BoundaryChartSelectedBoxImageConstructorData.ofOrientedManifold
    hbox target).boundaryChartOrientedChangeOfVariables

end ManifoldBoundary

end Stokes

end
