import Stokes.Global.CoverIndexedZeroCompactTargetBoxSelection
import Stokes.BoundaryChart.ConstrainedTargetBoxSelectionAuto

/-!
# Geometry projections for lower-zero compact target boxes

The lower-zero compact target-box constructor expects three geometric inputs:

* compact-image containment for the selected target box,
* local right-inverse data on that target box, and
* containment of the selected ambient target `Icc` in the target chart domain.

This file exposes the first two directly from existing target-box selection
packages, and packages the cover-indexed constructor with target-box
neighborhoods to provide the third.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryChartLowerZeroGeometrySelection

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {a b : Fin (n + 1) → Real}

namespace BoundaryChartTargetBoxSelection

/-- Compact-image projection from a selected target box whose corners have
been identified with a lower-zero compact coordinate box. -/
theorem compactImage_of_lowerZeroBox
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (box : CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (hlower : target.lowerCorner = box.lowerZeroLower)
    (hupper : target.upperCorner = box.lowerZeroUpper) :
    boundaryChartCompactImageBoxSelection I x0 x1 a b
      box.lowerZeroLower box.lowerZeroUpper := by
  simpa [hlower, hupper] using target.compactImage

/-- Local-inverse projection from a selected target box whose corners have
been identified with a lower-zero compact coordinate box. -/
theorem localInverse_of_lowerZeroBox
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (box : CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (hlower : target.lowerCorner = box.lowerZeroLower)
    (hupper : target.upperCorner = box.lowerZeroUpper) :
    boundaryChartLocalInverseData I x0 x1 a b
      box.lowerZeroLower box.lowerZeroUpper := by
  simpa [hlower, hupper] using target.localInverse

end BoundaryChartTargetBoxSelection

namespace BoundaryChartControlledTargetBoxSelectionData

variable {selectedLower selectedUpper : Fin (n + 1) → Real}
variable {y : Fin n → Real}
variable {U : Set (Fin n → Real)}

/-- Compact-image projection from a controlled target-box selection after
identifying its controlled later target corners with a lower-zero compact
coordinate box. -/
theorem compactImage_of_lowerZeroBox
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U)
    (box : CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (hlower : D.laterLowerCorner = box.lowerZeroLower)
    (hupper : D.laterUpperCorner = box.lowerZeroUpper) :
    boundaryChartCompactImageBoxSelection I x0 x1 a b
      box.lowerZeroLower box.lowerZeroUpper := by
  simpa [hlower, hupper] using D.compactImage

/-- Local-inverse projection from a controlled target-box selection after
identifying its controlled later target corners with a lower-zero compact
coordinate box. -/
theorem localInverse_of_lowerZeroBox
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U)
    (box : CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (hlower : D.laterLowerCorner = box.lowerZeroLower)
    (hupper : D.laterUpperCorner = box.lowerZeroUpper) :
    boundaryChartLocalInverseData I x0 x1 a b
      box.lowerZeroLower box.lowerZeroUpper := by
  simpa [hlower, hupper] using D.localInverse

end BoundaryChartControlledTargetBoxSelectionData

end BoundaryChartLowerZeroGeometrySelection

section CoverIndexedZeroCompactTargetGeometrySelection

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryTargetBoxData

/-- Construct target-box data from already selected boundary target boxes whose
corners are the lower-zero normalization of compact coordinate boxes.  This
removes the need to pass the compact-image and local-inverse fields separately:
they are projections of `targetSelection`. -/
def ofLowerZeroTargetSelections
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (box :
      {x : M // x ∈ C.boundaryCenters} →
        CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (targetSelection :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartTargetBoxSelection I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (targetLower_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (targetSelection i).lowerCorner = (box i).lowerZeroLower)
    (targetUpper_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (targetSelection i).upperCorner = (box i).lowerZeroUpper) :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega :=
  CoverIndexedBoundaryTargetBoxData.ofLowerZeroCompactCoordinateBoxSelections
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    targetChart sourceTargetSelectedBox box
    (fun i =>
      (targetSelection i).compactImage_of_lowerZeroBox
        (box i) (targetLower_eq i) (targetUpper_eq i))
    (fun i =>
      (targetSelection i).localInverse_of_lowerZeroBox
        (box i) (targetLower_eq i) (targetUpper_eq i))

@[simp]
theorem ofLowerZeroTargetSelections_targetChart
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (box :
      {x : M // x ∈ C.boundaryCenters} →
        CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (targetSelection :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartTargetBoxSelection I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (targetLower_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (targetSelection i).lowerCorner = (box i).lowerZeroLower)
    (targetUpper_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (targetSelection i).upperCorner = (box i).lowerZeroUpper) :
    (ofLowerZeroTargetSelections
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      targetChart sourceTargetSelectedBox box targetSelection
      targetLower_eq targetUpper_eq).targetChart = targetChart :=
  rfl

end CoverIndexedBoundaryTargetBoxData

namespace CoverIndexedZeroCompactRelativeTargetBoxData

variable
    {transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega}

/-- Relative target-box package from lower-zero compact boxes and already
selected target-box geometry.  Compared with
`ofLowerZeroCompactCoordinateBoxSelections`, the compact-image and local-inverse
inputs are projected from `targetSelection`, while `targetBox_subset_target` is
projected from target-box neighborhoods. -/
def ofLowerZeroTargetSelectionsAndNeighborhoods
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetChart_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        transitionSupportData.targetChart i = targetChart i)
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (box :
      {x : M // x ∈ C.boundaryCenters} →
        CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (box_K_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (box i).K = chartCoordinateImage I (targetChart i) K)
    (box_subset_halfSpace :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (box i).K ⊆ upperHalfSpace n)
    (targetSelection :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartTargetBoxSelection I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (targetLower_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (targetSelection i).lowerCorner = (box i).lowerZeroLower)
    (targetUpper_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (targetSelection i).upperCorner = (box i).lowerZeroUpper)
    (targetNeighborhoods :
      CoverIndexedBoundaryTargetBoxNeighborhoods
        (CoverIndexedBoundaryTargetBoxData.ofLowerZeroTargetSelections
          (I := I) (K := K) (C := C) (P := P) (omega := omega)
          targetChart sourceTargetSelectedBox box targetSelection
          targetLower_eq targetUpper_eq)) :
    CoverIndexedZeroCompactRelativeTargetBoxData
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData := by
  let targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega :=
    CoverIndexedBoundaryTargetBoxData.ofLowerZeroTargetSelections
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      targetChart sourceTargetSelectedBox box targetSelection
      targetLower_eq targetUpper_eq
  refine
    CoverIndexedZeroCompactRelativeTargetBoxData.ofLowerZeroCompactCoordinateBoxSelections
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (transitionSupportData := transitionSupportData)
      targetChart targetChart_eq sourceTargetSelectedBox
      box box_K_eq box_subset_halfSpace
      ?_ ?_ ?_
  · intro i
    exact
      (targetSelection i).compactImage_of_lowerZeroBox
        (box i) (targetLower_eq i) (targetUpper_eq i)
  · intro i
    exact
      (targetSelection i).localInverse_of_lowerZeroBox
        (box i) (targetLower_eq i) (targetUpper_eq i)
  · intro i y hy
    have htarget :
        y ∈ Icc (targetBox.targetLower i) (targetBox.targetUpper i) := by
      simpa [targetBox, targetLower_eq i, targetUpper_eq i] using hy
    have hsubset :=
      (CoverIndexedBoundaryTargetBoxNeighborhoods.targetBox_subset_target
        targetNeighborhoods i htarget)
    simpa [targetBox] using hsubset

end CoverIndexedZeroCompactRelativeTargetBoxData

end CoverIndexedZeroCompactTargetGeometrySelection

end Stokes

end
