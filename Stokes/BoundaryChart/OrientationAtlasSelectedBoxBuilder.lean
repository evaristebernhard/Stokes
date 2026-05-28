import Stokes.BoundaryChart.OrientationAtlasBoundarySign

/-!
# Oriented-atlas selected-box builders

This file is a thin API layer over `OrientationAtlasBoundarySign.lean`.
It gives stable names for the common route

`oriented atlas chart membership + selected source box + selected target image`

to the boundary-sign package, the selected-box orientation/COV package, and the
oriented boundary chart change-of-variables statement.

No global mathlib orientation theorem is proved here: all orientation content
comes from the project-local `BoundaryChartOrientedAtlas` fields already
available in `OrientationAtlasBoundarySign.lean`.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace BoundaryChartAtlasBoundarySignData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real}

@[simp]
theorem toSelectedBoxOrientationCovData_selectedBox
    (D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    (D.toSelectedBoxOrientationCovData himage).selectedBox = D.selectedBox :=
  rfl

@[simp]
theorem toSelectedBoxOrientationCovData_compatibleOn
    (D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    (D.toSelectedBoxOrientationCovData himage).compatibleOn = D.compatibleOn :=
  rfl

@[simp]
theorem toSelectedBoxOrientationCovData_orientationMapDataOn
    (D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    (D.toSelectedBoxOrientationCovData himage).orientationMapDataOn =
      D.orientationMapDataOn :=
  rfl

@[simp]
theorem toSelectedBoxOrientationCovData_imageData
    (D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    (D.toSelectedBoxOrientationCovData himage).imageData = himage :=
  rfl

/-- Stable alias for the selected-box orientation/COV package built from
boundary-sign data and selected target-image data. -/
def selectedBoxOrientationCovData
    (D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  D.toSelectedBoxOrientationCovData himage

@[simp]
theorem selectedBoxOrientationCovData_eq_toSelectedBoxOrientationCovData
    (D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    D.selectedBoxOrientationCovData himage =
      D.toSelectedBoxOrientationCovData himage :=
  rfl

/-- Stable alias for oriented COV produced by selected-box boundary-sign data. -/
theorem orientedChangeOfVariables
    [IsManifold I 1 M]
    (D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (D.toSelectedBoxOrientationCovData himage).orientedChangeOfVariables

/-- Stable alias for the raw COV hypotheses produced by selected-box
boundary-sign data. -/
theorem selectedBoxChangeOfVariablesHypotheses
    [IsManifold I 1 M]
    (D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) ∧
      boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) ∧
        (∀ u ∈ lowerZeroFaceDomain a b,
          HasFDerivWithinAt (boundaryChartTransition I x0 x1)
            (boundaryChartTransitionTangentMap I x0 x1 u)
            (lowerZeroFaceDomain a b) u) ∧
          InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b) ∧
            (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
              lowerZeroFaceDomain c d :=
  D.changeOfVariablesHypotheses himage

end BoundaryChartAtlasBoundarySignData

namespace BoundaryChartOrientedAtlas

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real}

@[simp]
theorem selectedBoxBoundarySignData_selectedBox
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    (A.selectedBoxBoundarySignData hx0 hx1 hbox).selectedBox = hbox :=
  rfl

@[simp]
theorem selectedBoxBoundarySignData_compatibleOn
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    (A.selectedBoxBoundarySignData hx0 hx1 hbox).compatibleOn =
      A.transitionCompatibleOn_selectedBox hx0 hx1 hbox :=
  rfl

@[simp]
theorem selectedBoxBoundarySignData_orientationMapDataOn
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    (A.selectedBoxBoundarySignData hx0 hx1 hbox).orientationMapDataOn =
      A.orientationMapDataOn_selectedBox hx0 hx1 hbox :=
  rfl

@[simp]
theorem selectedBoxBoundarySignData_preservesOrientationOn
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    (A.selectedBoxBoundarySignData hx0 hx1 hbox).preservesOrientationOn =
      A.preservesOrientationOn_selectedBox hx0 hx1 hbox :=
  rfl

/-- Build selected-box orientation/COV data from oriented-atlas chart
membership, a selected source box, and selected target-image data. -/
def selectedBoxOrientationCovDataFromBoundarySign
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  (A.selectedBoxBoundarySignData hx0 hx1 hbox).toSelectedBoxOrientationCovData
    himage

@[simp]
theorem selectedBoxOrientationCovDataFromBoundarySign_eq_ofOrientedAtlas
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    A.selectedBoxOrientationCovDataFromBoundarySign hx0 hx1 hbox himage =
      BoundaryChartSelectedBoxOrientationCovData.ofOrientedAtlas
        A hx0 hx1 hbox himage :=
  rfl

/-- Direct oriented-atlas builder for selected-box oriented COV. -/
theorem selectedBoxOrientedChangeOfVariablesFromBoundarySign
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (A.selectedBoxBoundarySignData hx0 hx1 hbox).orientedChangeOfVariables
    himage

/-- Raw COV hypotheses obtained from oriented-atlas chart membership and
selected-box/image data. -/
theorem selectedBoxChangeOfVariablesHypothesesFromBoundarySign
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) ∧
      boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) ∧
        (∀ u ∈ lowerZeroFaceDomain a b,
          HasFDerivWithinAt (boundaryChartTransition I x0 x1)
            (boundaryChartTransitionTangentMap I x0 x1 u)
            (lowerZeroFaceDomain a b) u) ∧
          InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b) ∧
            (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
              lowerZeroFaceDomain c d :=
  (A.selectedBoxBoundarySignData hx0 hx1 hbox).selectedBoxChangeOfVariablesHypotheses
    himage

end BoundaryChartOrientedAtlas

namespace BoundaryChartMathlibOrientedAtlasBridge

universe v

variable {𝓞 : Type v}
variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real}

/-- Mathlib-facing bridge variant of the oriented-atlas selected-box COV
builder.  This only forgets the bridge to the project-local oriented atlas. -/
def selectedBoxOrientationCovDataFromBoundarySign
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (hx0 : x0 ∈ B.toBoundaryChartOrientedAtlas.charts)
    (hx1 : x1 ∈ B.toBoundaryChartOrientedAtlas.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  (B.selectedBoxBoundarySignData hx0 hx1 hbox).toSelectedBoxOrientationCovData
    himage

/-- Mathlib-facing bridge variant of selected-box oriented COV. -/
theorem selectedBoxOrientedChangeOfVariablesFromBoundarySign
    [IsManifold I 1 M]
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (hx0 : x0 ∈ B.toBoundaryChartOrientedAtlas.charts)
    (hx1 : x1 ∈ B.toBoundaryChartOrientedAtlas.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (B.selectedBoxBoundarySignData hx0 hx1 hbox).orientedChangeOfVariables
    himage

end BoundaryChartMathlibOrientedAtlasBridge

end ManifoldBoundary

end Stokes

end
