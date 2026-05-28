import Stokes.BoundaryChart.SelectedBoxImageConstructor
import Stokes.BoundaryChart.TransitionDerivative

/-!
# Cover-indexed boundary-chart orientation bridge

This file is the finite/indexed-family layer over the single-chart
orientation/change-of-variables bridge.  It intentionally stays inside the
project-local orientation API: a downstream cover-indexed boundary constructor
can provide one selected boundary box and one target-image package per index,
then obtain the `BoundaryChartOrientationCovData` or oriented COV package for
each index from either a `BoundaryChartOrientedAtlas` or a
`BoundaryChartOrientedManifold`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u v w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
An indexed family of selected boundary chart boxes together with explicit
target image boxes.

This is the shape expected by a cover-indexed boundary reconstruction: each
index carries its source/target charts, localized form, selected source
half-space box, and target lower-zero-face image data.
-/
structure CoverIndexedBoundaryChartOrientationInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ι : Type v) where
  /-- Source boundary chart for this boundary piece. -/
  sourceChart : ι → M
  /-- Target boundary chart used to represent the same boundary piece. -/
  targetChart : ι → M
  /-- The localized form attached to the boundary piece. -/
  form : ι → ManifoldForm I M n
  /-- Lower corner of the selected source half-space box. -/
  lower : ι → Fin (n + 1) → Real
  /-- Upper corner of the selected source half-space box. -/
  upper : ι → Fin (n + 1) → Real
  /-- Lower corner of the selected target boundary box. -/
  targetLower : ι → Fin (n + 1) → Real
  /-- Upper corner of the selected target boundary box. -/
  targetUpper : ι → Fin (n + 1) → Real
  /-- Selected source boxes discharge the chart-domain/support and derivative inputs. -/
  selectedBox : ∀ j : ι,
    boundaryChartSelectedBox I (sourceChart j) (targetChart j) (form j)
      (lower j) (upper j)
  /-- Target image data for the boundary chart transition on each selected box. -/
  imageData : ∀ j : ι,
    boundaryChartSelectedBoxImageData I (sourceChart j) (targetChart j)
      (lower j) (upper j) (targetLower j) (targetUpper j)

namespace CoverIndexedBoundaryChartOrientationInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ι : Type v}

/-- Boundary-face and tangential compatibility on one indexed selected box,
obtained from a project-local oriented atlas. -/
theorem compatibleOnOfOrientedAtlas
    (D : CoverIndexedBoundaryChartOrientationInput (M := M) I ι)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ j : ι, D.sourceChart j ∈ A.charts)
    (htarget : ∀ j : ι, D.targetChart j ∈ A.charts)
    (j : ι) :
    boundaryChartTransitionCompatibleOn I (D.sourceChart j) (D.targetChart j)
      (lowerZeroFaceDomain (D.lower j) (D.upper j)) :=
  A.transitionCompatibleOn_selectedBox (hsource j) (htarget j) (D.selectedBox j)

/-- Mathlib-orientation-facing pointwise data on one indexed selected box,
obtained from a project-local oriented atlas. -/
def orientationMapDataOnOfOrientedAtlas
    (D : CoverIndexedBoundaryChartOrientationInput (M := M) I ι)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ j : ι, D.sourceChart j ∈ A.charts)
    (htarget : ∀ j : ι, D.targetChart j ∈ A.charts)
    (j : ι) :
    BoundaryChartOrientationMapDataOn I (D.sourceChart j) (D.targetChart j)
      (lowerZeroFaceDomain (D.lower j) (D.upper j)) :=
  A.orientationMapDataOn_selectedBox (hsource j) (htarget j) (D.selectedBox j)

/-- Positive-Jacobian orientation compatibility on one indexed selected box,
obtained from a project-local oriented atlas. -/
theorem orientationCompatibleOnOfOrientedAtlas
    (D : CoverIndexedBoundaryChartOrientationInput (M := M) I ι)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ j : ι, D.sourceChart j ∈ A.charts)
    (htarget : ∀ j : ι, D.targetChart j ∈ A.charts)
    (j : ι) :
    boundaryChartOrientationCompatibleOn I (D.sourceChart j) (D.targetChart j)
      (lowerZeroFaceDomain (D.lower j) (D.upper j)) :=
  boundaryChartOrientationCompatibleOn_of_orientationMapDataOn I
    (D.sourceChart j) (D.targetChart j)
    (D.orientationMapDataOnOfOrientedAtlas A hsource htarget j)

/-- Selected-box orientation/COV data on one indexed boundary piece, obtained
from a project-local oriented atlas and the indexed image data. -/
def selectedBoxOrientationCovDataOfOrientedAtlas
    (D : CoverIndexedBoundaryChartOrientationInput (M := M) I ι)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ j : ι, D.sourceChart j ∈ A.charts)
    (htarget : ∀ j : ι, D.targetChart j ∈ A.charts)
    (j : ι) :
    BoundaryChartSelectedBoxOrientationCovData I
      (D.sourceChart j) (D.targetChart j) (D.form j)
      (D.lower j) (D.upper j) (D.targetLower j) (D.targetUpper j) :=
  BoundaryChartSelectedBoxOrientationCovData.ofOrientedAtlas
    A (hsource j) (htarget j) (D.selectedBox j) (D.imageData j)

/-- Full orientation COV data on one indexed boundary piece, obtained from a
project-local oriented atlas.  This is the main projection consumed by
change-of-variables based boundary constructors. -/
def orientationCovDataOfOrientedAtlas [IsManifold I 1 M]
    (D : CoverIndexedBoundaryChartOrientationInput (M := M) I ι)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ j : ι, D.sourceChart j ∈ A.charts)
    (htarget : ∀ j : ι, D.targetChart j ∈ A.charts)
    (j : ι) :
    BoundaryChartOrientationCovData I
      (D.sourceChart j) (D.targetChart j)
      (D.lower j) (D.upper j) (D.targetLower j) (D.targetUpper j) :=
  (D.selectedBoxOrientationCovDataOfOrientedAtlas A hsource htarget j).toOrientationCovData

/-- Indexed family form of `orientationCovDataOfOrientedAtlas`. -/
def orientationCovDataFamilyOfOrientedAtlas [IsManifold I 1 M]
    (D : CoverIndexedBoundaryChartOrientationInput (M := M) I ι)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ j : ι, D.sourceChart j ∈ A.charts)
    (htarget : ∀ j : ι, D.targetChart j ∈ A.charts) :
    ∀ j : ι,
      BoundaryChartOrientationCovData I
        (D.sourceChart j) (D.targetChart j)
        (D.lower j) (D.upper j) (D.targetLower j) (D.targetUpper j) :=
  fun j => D.orientationCovDataOfOrientedAtlas A hsource htarget j

/-- Projection of the indexed oriented-atlas data to the exact hypotheses used
by the boundary chart COV theorem. -/
theorem changeOfVariablesHypothesesOfOrientedAtlas [IsManifold I 1 M]
    (D : CoverIndexedBoundaryChartOrientationInput (M := M) I ι)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ j : ι, D.sourceChart j ∈ A.charts)
    (htarget : ∀ j : ι, D.targetChart j ∈ A.charts)
    (j : ι) :
    boundaryChartTransitionCompatibleOn I (D.sourceChart j) (D.targetChart j)
        (lowerZeroFaceDomain (D.lower j) (D.upper j)) ∧
      boundaryChartOrientationCompatibleOn I (D.sourceChart j) (D.targetChart j)
        (lowerZeroFaceDomain (D.lower j) (D.upper j)) ∧
        (∀ u ∈ lowerZeroFaceDomain (D.lower j) (D.upper j),
          HasFDerivWithinAt
            (boundaryChartTransition I (D.sourceChart j) (D.targetChart j))
            (boundaryChartTransitionTangentMap I
              (D.sourceChart j) (D.targetChart j) u)
            (lowerZeroFaceDomain (D.lower j) (D.upper j)) u) ∧
          InjOn (boundaryChartTransition I (D.sourceChart j) (D.targetChart j))
            (lowerZeroFaceDomain (D.lower j) (D.upper j)) ∧
            (boundaryChartTransition I (D.sourceChart j) (D.targetChart j)) ''
                lowerZeroFaceDomain (D.lower j) (D.upper j) =
              lowerZeroFaceDomain (D.targetLower j) (D.targetUpper j) :=
  (D.orientationCovDataOfOrientedAtlas A hsource htarget j).changeOfVariablesHypotheses

/-- Oriented boundary chart change-of-variables on one indexed boundary piece,
using a project-local oriented atlas. -/
theorem orientedChangeOfVariablesOfOrientedAtlas [IsManifold I 1 M]
    (D : CoverIndexedBoundaryChartOrientationInput (M := M) I ι)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ j : ι, D.sourceChart j ∈ A.charts)
    (htarget : ∀ j : ι, D.targetChart j ∈ A.charts)
    (j : ι) :
    boundaryChartOrientedChangeOfVariables I
      (D.sourceChart j) (D.targetChart j) (D.form j)
      (D.lower j) (D.upper j) (D.targetLower j) (D.targetUpper j) :=
  (D.selectedBoxOrientationCovDataOfOrientedAtlas A hsource htarget j).orientedChangeOfVariables

/-- Boundary-face and tangential compatibility on one indexed selected box,
obtained from global project-local oriented-manifold data. -/
theorem compatibleOnOfOrientedManifold [BoundaryChartOrientedManifold I M]
    (D : CoverIndexedBoundaryChartOrientationInput (M := M) I ι) (j : ι) :
    boundaryChartTransitionCompatibleOn I (D.sourceChart j) (D.targetChart j)
      (lowerZeroFaceDomain (D.lower j) (D.upper j)) :=
  boundaryChartTransitionCompatibleOn_selectedBox_of_orientedManifold
    (I := I) (M := M) (x0 := D.sourceChart j) (x1 := D.targetChart j)
    (ω := D.form j) (a := D.lower j) (b := D.upper j) (D.selectedBox j)

/-- Mathlib-orientation-facing pointwise data on one indexed selected box,
obtained from global project-local oriented-manifold data. -/
def orientationMapDataOnOfOrientedManifold [BoundaryChartOrientedManifold I M]
    (D : CoverIndexedBoundaryChartOrientationInput (M := M) I ι) (j : ι) :
    BoundaryChartOrientationMapDataOn I (D.sourceChart j) (D.targetChart j)
      (lowerZeroFaceDomain (D.lower j) (D.upper j)) :=
  boundaryChartOrientationMapDataOn_selectedBox_of_orientedManifold
    (I := I) (M := M) (x0 := D.sourceChart j) (x1 := D.targetChart j)
    (ω := D.form j) (a := D.lower j) (b := D.upper j) (D.selectedBox j)

/-- Positive-Jacobian orientation compatibility on one indexed selected box,
obtained from global project-local oriented-manifold data. -/
theorem orientationCompatibleOnOfOrientedManifold
    [BoundaryChartOrientedManifold I M]
    (D : CoverIndexedBoundaryChartOrientationInput (M := M) I ι) (j : ι) :
  boundaryChartOrientationCompatibleOn I (D.sourceChart j) (D.targetChart j)
      (lowerZeroFaceDomain (D.lower j) (D.upper j)) :=
  boundaryChartOrientationCompatibleOn_of_orientationMapDataOn
    (M := M) I (D.sourceChart j) (D.targetChart j)
    (D.orientationMapDataOnOfOrientedManifold j)

/-- Selected-box orientation/COV data on one indexed boundary piece, obtained
from global project-local oriented-manifold data. -/
def selectedBoxOrientationCovDataOfOrientedManifold
    [BoundaryChartOrientedManifold I M]
    (D : CoverIndexedBoundaryChartOrientationInput (M := M) I ι) (j : ι) :
  BoundaryChartSelectedBoxOrientationCovData I
      (D.sourceChart j) (D.targetChart j) (D.form j)
      (D.lower j) (D.upper j) (D.targetLower j) (D.targetUpper j) :=
  BoundaryChartSelectedBoxOrientationCovData.ofOrientedManifold
    (I := I) (M := M) (x0 := D.sourceChart j) (x1 := D.targetChart j)
    (ω := D.form j) (a := D.lower j) (b := D.upper j)
    (c := D.targetLower j) (d := D.targetUpper j)
    (D.selectedBox j) (D.imageData j)

/-- Full orientation COV data on one indexed boundary piece, obtained from
global project-local oriented-manifold data. -/
def orientationCovDataOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : CoverIndexedBoundaryChartOrientationInput (M := M) I ι) (j : ι) :
    BoundaryChartOrientationCovData I
      (D.sourceChart j) (D.targetChart j)
      (D.lower j) (D.upper j) (D.targetLower j) (D.targetUpper j) :=
  (D.selectedBoxOrientationCovDataOfOrientedManifold j).toOrientationCovData

/-- Indexed family form of `orientationCovDataOfOrientedManifold`. -/
def orientationCovDataFamilyOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : CoverIndexedBoundaryChartOrientationInput (M := M) I ι) :
    ∀ j : ι,
      BoundaryChartOrientationCovData I
        (D.sourceChart j) (D.targetChart j)
        (D.lower j) (D.upper j) (D.targetLower j) (D.targetUpper j) :=
  fun j => D.orientationCovDataOfOrientedManifold j

/-- Projection of the indexed oriented-manifold data to the exact hypotheses
used by the boundary chart COV theorem. -/
theorem changeOfVariablesHypothesesOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : CoverIndexedBoundaryChartOrientationInput (M := M) I ι) (j : ι) :
    boundaryChartTransitionCompatibleOn I (D.sourceChart j) (D.targetChart j)
        (lowerZeroFaceDomain (D.lower j) (D.upper j)) ∧
      boundaryChartOrientationCompatibleOn I (D.sourceChart j) (D.targetChart j)
        (lowerZeroFaceDomain (D.lower j) (D.upper j)) ∧
        (∀ u ∈ lowerZeroFaceDomain (D.lower j) (D.upper j),
          HasFDerivWithinAt
            (boundaryChartTransition I (D.sourceChart j) (D.targetChart j))
            (boundaryChartTransitionTangentMap I
              (D.sourceChart j) (D.targetChart j) u)
            (lowerZeroFaceDomain (D.lower j) (D.upper j)) u) ∧
          InjOn (boundaryChartTransition I (D.sourceChart j) (D.targetChart j))
            (lowerZeroFaceDomain (D.lower j) (D.upper j)) ∧
            (boundaryChartTransition I (D.sourceChart j) (D.targetChart j)) ''
                lowerZeroFaceDomain (D.lower j) (D.upper j) =
              lowerZeroFaceDomain (D.targetLower j) (D.targetUpper j) :=
  (D.orientationCovDataOfOrientedManifold j).changeOfVariablesHypotheses

/-- Oriented boundary chart change-of-variables on one indexed boundary piece,
using global project-local oriented-manifold data. -/
theorem orientedChangeOfVariablesOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : CoverIndexedBoundaryChartOrientationInput (M := M) I ι) (j : ι) :
    boundaryChartOrientedChangeOfVariables I
      (D.sourceChart j) (D.targetChart j) (D.form j)
      (D.lower j) (D.upper j) (D.targetLower j) (D.targetUpper j) :=
  (D.selectedBoxOrientationCovDataOfOrientedManifold j).orientedChangeOfVariables

end CoverIndexedBoundaryChartOrientationInput

/--
Indexed selected boundary boxes with a packaged target-box selection per
index.  This is a slightly higher-level input than explicit `imageData`:
target image data is projected from compact-image plus local-inverse fields.
-/
structure CoverIndexedBoundaryChartTargetSelectionInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ι : Type v) where
  sourceChart : ι → M
  targetChart : ι → M
  form : ι → ManifoldForm I M n
  lower : ι → Fin (n + 1) → Real
  upper : ι → Fin (n + 1) → Real
  selectedBox : ∀ j : ι,
    boundaryChartSelectedBox I (sourceChart j) (targetChart j) (form j)
      (lower j) (upper j)
  targetSelection : ∀ j : ι,
    BoundaryChartTargetBoxSelection I (sourceChart j) (targetChart j)
      (lower j) (upper j)

namespace CoverIndexedBoundaryChartTargetSelectionInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ι : Type v}

/-- Forget packaged target selections to the explicit image-data input. -/
def toOrientationInput
    (D : CoverIndexedBoundaryChartTargetSelectionInput (M := M) I ι) :
    CoverIndexedBoundaryChartOrientationInput (M := M) I ι where
  sourceChart := D.sourceChart
  targetChart := D.targetChart
  form := D.form
  lower := D.lower
  upper := D.upper
  targetLower := fun j => (D.targetSelection j).lowerCorner
  targetUpper := fun j => (D.targetSelection j).upperCorner
  selectedBox := D.selectedBox
  imageData := fun j => (D.targetSelection j).imageData

@[simp]
theorem toOrientationInput_sourceChart
    (D : CoverIndexedBoundaryChartTargetSelectionInput (M := M) I ι) :
    D.toOrientationInput.sourceChart = D.sourceChart :=
  rfl

@[simp]
theorem toOrientationInput_targetChart
    (D : CoverIndexedBoundaryChartTargetSelectionInput (M := M) I ι) :
    D.toOrientationInput.targetChart = D.targetChart :=
  rfl

@[simp]
theorem toOrientationInput_targetLower
    (D : CoverIndexedBoundaryChartTargetSelectionInput (M := M) I ι) (j : ι) :
    D.toOrientationInput.targetLower j = (D.targetSelection j).lowerCorner :=
  rfl

@[simp]
theorem toOrientationInput_targetUpper
    (D : CoverIndexedBoundaryChartTargetSelectionInput (M := M) I ι) (j : ι) :
    D.toOrientationInput.targetUpper j = (D.targetSelection j).upperCorner :=
  rfl

/-- Full orientation COV data from a project-local oriented atlas and packaged
target selections. -/
def orientationCovDataOfOrientedAtlas [IsManifold I 1 M]
    (D : CoverIndexedBoundaryChartTargetSelectionInput (M := M) I ι)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ j : ι, D.sourceChart j ∈ A.charts)
    (htarget : ∀ j : ι, D.targetChart j ∈ A.charts)
    (j : ι) :
    BoundaryChartOrientationCovData I
      (D.sourceChart j) (D.targetChart j)
      (D.lower j) (D.upper j)
      (D.targetSelection j).lowerCorner (D.targetSelection j).upperCorner :=
  D.toOrientationInput.orientationCovDataOfOrientedAtlas A hsource htarget j

/-- Indexed family form of the oriented-atlas target-selection bridge. -/
def orientationCovDataFamilyOfOrientedAtlas [IsManifold I 1 M]
    (D : CoverIndexedBoundaryChartTargetSelectionInput (M := M) I ι)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ j : ι, D.sourceChart j ∈ A.charts)
    (htarget : ∀ j : ι, D.targetChart j ∈ A.charts) :
    ∀ j : ι,
      BoundaryChartOrientationCovData I
        (D.sourceChart j) (D.targetChart j)
        (D.lower j) (D.upper j)
        (D.targetSelection j).lowerCorner (D.targetSelection j).upperCorner :=
  fun j => D.orientationCovDataOfOrientedAtlas A hsource htarget j

/-- Oriented COV from a project-local oriented atlas and packaged target
selection on one indexed boundary piece. -/
theorem orientedChangeOfVariablesOfOrientedAtlas [IsManifold I 1 M]
    (D : CoverIndexedBoundaryChartTargetSelectionInput (M := M) I ι)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ j : ι, D.sourceChart j ∈ A.charts)
    (htarget : ∀ j : ι, D.targetChart j ∈ A.charts)
    (j : ι) :
    boundaryChartOrientedChangeOfVariables I
      (D.sourceChart j) (D.targetChart j) (D.form j)
      (D.lower j) (D.upper j)
      (D.targetSelection j).lowerCorner (D.targetSelection j).upperCorner :=
  D.toOrientationInput.orientedChangeOfVariablesOfOrientedAtlas A hsource htarget j

/-- Full orientation COV data from global project-local oriented-manifold data
and packaged target selections. -/
def orientationCovDataOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : CoverIndexedBoundaryChartTargetSelectionInput (M := M) I ι) (j : ι) :
    BoundaryChartOrientationCovData I
      (D.sourceChart j) (D.targetChart j)
      (D.lower j) (D.upper j)
      (D.targetSelection j).lowerCorner (D.targetSelection j).upperCorner :=
  D.toOrientationInput.orientationCovDataOfOrientedManifold j

/-- Indexed family form of the oriented-manifold target-selection bridge. -/
def orientationCovDataFamilyOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : CoverIndexedBoundaryChartTargetSelectionInput (M := M) I ι) :
    ∀ j : ι,
      BoundaryChartOrientationCovData I
        (D.sourceChart j) (D.targetChart j)
        (D.lower j) (D.upper j)
        (D.targetSelection j).lowerCorner (D.targetSelection j).upperCorner :=
  fun j => D.orientationCovDataOfOrientedManifold j

/-- Oriented COV from global project-local oriented-manifold data and packaged
target selection on one indexed boundary piece. -/
theorem orientedChangeOfVariablesOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : CoverIndexedBoundaryChartTargetSelectionInput (M := M) I ι) (j : ι) :
    boundaryChartOrientedChangeOfVariables I
      (D.sourceChart j) (D.targetChart j) (D.form j)
      (D.lower j) (D.upper j)
      (D.targetSelection j).lowerCorner (D.targetSelection j).upperCorner :=
  D.toOrientationInput.orientedChangeOfVariablesOfOrientedManifold j

end CoverIndexedBoundaryChartTargetSelectionInput

end ManifoldBoundary

end Stokes

end
