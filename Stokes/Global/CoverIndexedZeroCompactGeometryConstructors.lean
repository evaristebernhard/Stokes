import Stokes.Global.CoverIndexedZeroCompactGeometryAudit
import Stokes.Global.CoverIndexedZeroCompactTargetGeometrySelection

/-!
# Geometry constructors for compact zero target boxes

This file turns the audit/projection lemmas around the compact zero target-box
route into normal constructors.  The point is to keep the genuinely geometric
choices grouped:

* `BoundaryChartTargetBoxSelection` stores compact-image and local-inverse data;
* `CoverIndexedBoundaryTargetBoxNeighborhoods` stores target-chart-domain
  containment for the selected ambient box;
* lower-zero compact coordinate boxes store the coordinate-image containment
  after the usual lower-zero normalization.

The declarations below deliberately do not prove new chart-transition
`MapsTo` facts.  They only package already selected geometry so endpoint
constructors do not have to expose `compactImage`, `localInverse`, and
`targetBox_subset_target` as unrelated arguments.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section SingleChartTargetGeometryConstructors

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {a b selectedLower selectedUpper : Fin (n + 1) → Real}
variable {y : Fin n → Real}
variable {U : Set (Fin n → Real)}

namespace BoundaryChartTargetBoxSelection

/-- The compact-image field of a selected target box, with the selected corners
spelled out as the target corners consumed by downstream constructors. -/
theorem compactImageField
    (D : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    boundaryChartCompactImageBoxSelection I x0 x1 a b
      D.lowerCorner D.upperCorner :=
  D.compactImage

/-- The local-inverse field of a selected target box, with the selected corners
spelled out as the target corners consumed by downstream constructors. -/
theorem localInverseField
    (D : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    boundaryChartLocalInverseData I x0 x1 a b
      D.lowerCorner D.upperCorner :=
  D.localInverse

/-- Package the two image-geometry fields carried by a selected target box. -/
theorem compactImage_and_localInverse
    (D : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    boundaryChartCompactImageBoxSelection I x0 x1 a b
        D.lowerCorner D.upperCorner ∧
      boundaryChartLocalInverseData I x0 x1 a b
        D.lowerCorner D.upperCorner :=
  ⟨D.compactImage, D.localInverse⟩

end BoundaryChartTargetBoxSelection

namespace BoundaryChartControlledTargetBoxSelectionData

/-- A controlled target-box selection is already a standard target-box
selection; this exposes the compact-image field at the standard corners. -/
theorem compactImageField
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U) :
    boundaryChartCompactImageBoxSelection I x0 x1 a b
      D.targetBoxSelection.lowerCorner D.targetBoxSelection.upperCorner :=
  D.compactImage

/-- A controlled target-box selection is already a standard target-box
selection; this exposes the local-inverse field at the standard corners. -/
theorem localInverseField
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U) :
    boundaryChartLocalInverseData I x0 x1 a b
      D.targetBoxSelection.lowerCorner D.targetBoxSelection.upperCorner :=
  D.localInverse

/-- Package the two image-geometry fields carried by a controlled target-box
selection after converting it to the standard target-box package. -/
theorem compactImage_and_localInverse
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U) :
    boundaryChartCompactImageBoxSelection I x0 x1 a b
        D.targetBoxSelection.lowerCorner D.targetBoxSelection.upperCorner ∧
      boundaryChartLocalInverseData I x0 x1 a b
        D.targetBoxSelection.lowerCorner D.targetBoxSelection.upperCorner :=
  ⟨D.compactImageField, D.localInverseField⟩

end BoundaryChartControlledTargetBoxSelectionData

end SingleChartTargetGeometryConstructors

section CoverIndexedGeometryConstructors

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

/-- Cover-indexed compact-image field projected from the packaged selected
target boxes. -/
theorem compactImageField
    (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryChartCompactImageBoxSelection I
        (C.boundaryChart i.1) (D.targetChart i)
        (C.boundaryLower i.1) (C.boundaryUpper i.1)
        (D.targetLower i) (D.targetUpper i) := by
  intro i
  exact (D.targetSelection i).compactImage

/-- Cover-indexed local-inverse field projected from the packaged selected
target boxes. -/
theorem localInverseField
    (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryChartLocalInverseData I
        (C.boundaryChart i.1) (D.targetChart i)
        (C.boundaryLower i.1) (C.boundaryUpper i.1)
        (D.targetLower i) (D.targetUpper i) := by
  intro i
  exact (D.targetSelection i).localInverse

/-- Build cover-indexed target-box data from controlled target-box selections.
The compact-image and local-inverse halves are consumed through
`controlled i`, rather than being passed separately. -/
def ofControlledTargetSelections
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (selectedLower selectedUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (targetPoint :
      {x : M // x ∈ C.boundaryCenters} → Fin n → Real)
    (targetNeighborhood :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin n → Real))
    (controlled :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartControlledTargetBoxSelectionData I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (selectedLower i) (selectedUpper i)
          (targetPoint i) (targetNeighborhood i)) :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega :=
  CoverIndexedBoundaryTargetBoxData.ofTargetSelection
    (C := C) (P := P) (ω := omega)
    targetChart sourceTargetSelectedBox
    (fun i => (controlled i).targetBoxSelection)

@[simp]
theorem ofControlledTargetSelections_targetChart
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (selectedLower selectedUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (targetPoint :
      {x : M // x ∈ C.boundaryCenters} → Fin n → Real)
    (targetNeighborhood :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin n → Real))
    (controlled :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartControlledTargetBoxSelectionData I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (selectedLower i) (selectedUpper i)
          (targetPoint i) (targetNeighborhood i)) :
    (ofControlledTargetSelections
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      targetChart sourceTargetSelectedBox selectedLower selectedUpper
      targetPoint targetNeighborhood controlled).targetChart = targetChart :=
  rfl

/-- Controlled target selections whose later boxes are identified with
lower-zero compact coordinate boxes give the standard lower-zero cover-indexed
target-box package. -/
def ofControlledLowerZeroTargetSelections
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
    (selectedLower selectedUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (targetPoint :
      {x : M // x ∈ C.boundaryCenters} → Fin n → Real)
    (targetNeighborhood :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin n → Real))
    (controlled :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartControlledTargetBoxSelectionData I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (selectedLower i) (selectedUpper i)
          (targetPoint i) (targetNeighborhood i))
    (targetLower_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (controlled i).targetBoxSelection.lowerCorner = (box i).lowerZeroLower)
    (targetUpper_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (controlled i).targetBoxSelection.upperCorner = (box i).lowerZeroUpper) :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega :=
  CoverIndexedBoundaryTargetBoxData.ofLowerZeroTargetSelections
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    targetChart sourceTargetSelectedBox box
    (fun i => (controlled i).targetBoxSelection)
    targetLower_eq targetUpper_eq

end CoverIndexedBoundaryTargetBoxData

namespace CoverIndexedZeroCompactRelativeTargetBoxData

variable
    {transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega}

/-- Construct relative compact target-box data from an already packaged
cover-indexed target box.  The target-chart-domain field is projected from
`targetNeighborhoods`; only the coordinate-image containment remains as a
separate compact-support field. -/
def ofTargetBoxDataAndNeighborhoods
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (targetChart_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        transitionSupportData.targetChart i = targetBox.targetChart i)
    (targetNeighborhoods : CoverIndexedBoundaryTargetBoxNeighborhoods targetBox)
    (coordinateImage_subset_targetBox :
      targetBox.TargetChartCoordinateImageSubsetIccField) :
    CoverIndexedZeroCompactRelativeTargetBoxData
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData where
  targetBox := targetBox
  targetChart_eq := targetChart_eq
  targetBox_subset_target :=
    targetBox.targetBox_subset_target_of_targetBoxNeighborhoods
      targetNeighborhoods
  coordinateImage_subset_targetBox := coordinateImage_subset_targetBox

/-- Target selections plus target-box neighborhoods give the relative target
package once the compact coordinate-image containment field is available.
Compact-image and local-inverse data are projections of `targetSelection`; the
ambient chart-domain containment is projected from `targetNeighborhoods`. -/
def ofTargetSelectionsAndNeighborhoods
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
    (targetSelection :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartTargetBoxSelection I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (targetNeighborhoods :
      CoverIndexedBoundaryTargetBoxNeighborhoods
        (CoverIndexedBoundaryTargetBoxData.ofTargetSelection
          (C := C) (P := P) (ω := omega)
          targetChart sourceTargetSelectedBox targetSelection))
    (coordinateImage_subset_targetBox :
      (CoverIndexedBoundaryTargetBoxData.ofTargetSelection
        (C := C) (P := P) (ω := omega)
        targetChart sourceTargetSelectedBox targetSelection
        ).TargetChartCoordinateImageSubsetIccField) :
    CoverIndexedZeroCompactRelativeTargetBoxData
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData := by
  let targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega :=
    CoverIndexedBoundaryTargetBoxData.ofTargetSelection
      (C := C) (P := P) (ω := omega)
      targetChart sourceTargetSelectedBox targetSelection
  refine
    ofTargetBoxDataAndNeighborhoods
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (transitionSupportData := transitionSupportData)
      targetBox ?_ ?_ ?_
  · intro i
    simpa [targetBox] using targetChart_eq i
  · simpa [targetBox] using targetNeighborhoods
  · simpa [targetBox] using coordinateImage_subset_targetBox

/-- Controlled target selections plus target-box neighborhoods give the
relative target package once coordinate-image containment is available. -/
def ofControlledTargetSelectionsAndNeighborhoods
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
    (selectedLower selectedUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (targetPoint :
      {x : M // x ∈ C.boundaryCenters} → Fin n → Real)
    (targetNeighborhood :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin n → Real))
    (controlled :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartControlledTargetBoxSelectionData I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (selectedLower i) (selectedUpper i)
          (targetPoint i) (targetNeighborhood i))
    (targetNeighborhoods :
      CoverIndexedBoundaryTargetBoxNeighborhoods
        (CoverIndexedBoundaryTargetBoxData.ofControlledTargetSelections
          (I := I) (K := K) (C := C) (P := P) (omega := omega)
          targetChart sourceTargetSelectedBox selectedLower selectedUpper
          targetPoint targetNeighborhood controlled))
    (coordinateImage_subset_targetBox :
      (CoverIndexedBoundaryTargetBoxData.ofControlledTargetSelections
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        targetChart sourceTargetSelectedBox selectedLower selectedUpper
        targetPoint targetNeighborhood controlled
        ).TargetChartCoordinateImageSubsetIccField) :
    CoverIndexedZeroCompactRelativeTargetBoxData
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData := by
  refine
    ofTargetSelectionsAndNeighborhoods
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (transitionSupportData := transitionSupportData)
      targetChart targetChart_eq sourceTargetSelectedBox
      (fun i => (controlled i).targetBoxSelection) ?_ ?_
  · simpa [CoverIndexedBoundaryTargetBoxData.ofControlledTargetSelections]
      using targetNeighborhoods
  · simpa [CoverIndexedBoundaryTargetBoxData.ofControlledTargetSelections]
      using coordinateImage_subset_targetBox

/-- Controlled target selections whose target corners are the lower-zero
normalization of compact coordinate boxes give the relative target package
without exposing compact-image, local-inverse, or target-chart-domain fields. -/
def ofControlledLowerZeroTargetSelectionsAndNeighborhoods
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
    (selectedLower selectedUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (targetPoint :
      {x : M // x ∈ C.boundaryCenters} → Fin n → Real)
    (targetNeighborhood :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin n → Real))
    (controlled :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartControlledTargetBoxSelectionData I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (selectedLower i) (selectedUpper i)
          (targetPoint i) (targetNeighborhood i))
    (targetLower_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (controlled i).targetBoxSelection.lowerCorner = (box i).lowerZeroLower)
    (targetUpper_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (controlled i).targetBoxSelection.upperCorner = (box i).lowerZeroUpper)
    (targetNeighborhoods :
      CoverIndexedBoundaryTargetBoxNeighborhoods
        (CoverIndexedBoundaryTargetBoxData.ofControlledLowerZeroTargetSelections
          (I := I) (K := K) (C := C) (P := P) (omega := omega)
          targetChart sourceTargetSelectedBox box
          selectedLower selectedUpper targetPoint targetNeighborhood
          controlled targetLower_eq targetUpper_eq)) :
    CoverIndexedZeroCompactRelativeTargetBoxData
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData := by
  refine
    CoverIndexedZeroCompactRelativeTargetBoxData.ofLowerZeroTargetSelectionsAndNeighborhoods
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (transitionSupportData := transitionSupportData)
      targetChart targetChart_eq sourceTargetSelectedBox
      box box_K_eq box_subset_halfSpace
      (fun i => (controlled i).targetBoxSelection)
      targetLower_eq targetUpper_eq ?_
  simpa [CoverIndexedBoundaryTargetBoxData.ofControlledLowerZeroTargetSelections]
    using targetNeighborhoods

end CoverIndexedZeroCompactRelativeTargetBoxData

end CoverIndexedGeometryConstructors

end Stokes

end
