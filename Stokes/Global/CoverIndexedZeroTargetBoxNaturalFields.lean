import Stokes.Global.CoverIndexedBoxNeighborhoodSelection
import Stokes.Global.CoverIndexedZeroTargetBoxFromCompact

/-!
# Natural target-box fields for zero compact-support endpoints

This file contains only thin field/projector lemmas.  The selected boundary
target-image data controls the lower-zero boundary face, while the zero compact
endpoint also needs two ambient target-box facts:

* the whole selected ambient target box lies in the selected target chart;
* the target chart coordinate image of the global compact support lies in that
  selected box.

These facts are not consequences of `boundaryChartSelectedBoxImageData` alone,
so the lemmas below expose them from the packages that genuinely contain them:
target-box neighborhoods and compact coordinate box selections.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroTargetBoxNaturalFields

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryTargetBoxNeighborhoods

variable {D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega}

/-- Build target-box neighborhoods from the generic one-chart open-neighborhood
package, index by index. -/
def ofChartBoxOpenNeighborhoods
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          (extChartAt I (D.targetChart i)).target
          (D.targetLower i) (D.targetUpper i)) :
    CoverIndexedBoundaryTargetBoxNeighborhoods D where
  targetNeighborhood := fun i => (nbr i).neighborhood
  targetNeighborhood_open := fun i => (nbr i).isOpen_neighborhood
  targetIcc_subset_neighborhood := fun i => (nbr i).Icc_subset_neighborhood
  targetNeighborhood_subset_target := fun i => (nbr i).neighborhood_subset_target

@[simp]
theorem ofChartBoxOpenNeighborhoods_targetNeighborhood
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          (extChartAt I (D.targetChart i)).target
          (D.targetLower i) (D.targetUpper i))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    (ofChartBoxOpenNeighborhoods (D := D) nbr).targetNeighborhood i =
      (nbr i).neighborhood :=
  rfl

/-- Generic chart-box neighborhoods give the ambient target-domain field
expected by the zero compact-support endpoint. -/
theorem targetBox_subset_target_of_chartBoxOpenNeighborhoods
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          (extChartAt I (D.targetChart i)).target
          (D.targetLower i) (D.targetUpper i)) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (D.targetLower i) (D.targetUpper i) ⊆
        (extChartAt I (D.targetChart i)).target :=
  targetBox_subset_target (ofChartBoxOpenNeighborhoods (D := D) nbr)

end CoverIndexedBoundaryTargetBoxNeighborhoods

namespace CoverIndexedBoundaryTargetBoxData

variable (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)

/-- Target-box neighborhoods expose the ambient chart-target containment field
needed by zero compact-support endpoint wrappers. -/
theorem targetBox_subset_target_of_targetBoxNeighborhoods
    (nbrs : CoverIndexedBoundaryTargetBoxNeighborhoods D) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (D.targetLower i) (D.targetUpper i) ⊆
        (extChartAt I (D.targetChart i)).target :=
  CoverIndexedBoundaryTargetBoxNeighborhoods.targetBox_subset_target nbrs

/-- Generic one-chart open neighborhoods expose the same target-domain field,
without first naming the cover-indexed neighborhood package. -/
theorem targetBox_subset_target_of_chartBoxOpenNeighborhoods
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          (extChartAt I (D.targetChart i)).target
          (D.targetLower i) (D.targetUpper i)) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (D.targetLower i) (D.targetUpper i) ⊆
        (extChartAt I (D.targetChart i)).target :=
  CoverIndexedBoundaryTargetBoxNeighborhoods.targetBox_subset_target_of_chartBoxOpenNeighborhoods
    (D := D) nbr

/-- If the selected target corners are known to be the corners of compact
coordinate boxes for the target chart images of `K`, then the coordinate-image
containment field is just the stored `subset_Icc` projection. -/
theorem targetChartCoordinateImageSubsetIccField_of_compactCoordinateBoxSelections
    (box :
      {x : M // x ∈ C.boundaryCenters} →
        CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (box_K_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (box i).K = chartCoordinateImage I (D.targetChart i) K)
    (box_lower_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (box i).a = D.targetLower i)
    (box_upper_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (box i).b = D.targetUpper i) :
    D.TargetChartCoordinateImageSubsetIccField := by
  intro i y hy
  have hybox : y ∈ (box i).K := by
    simpa [box_K_eq i] using hy
  have hyIcc : y ∈ Icc (box i).a (box i).b :=
    (box i).subset_Icc hybox
  simpa [box_lower_eq i, box_upper_eq i] using hyIcc

/-- `ChartCompactImage.box` spelling of
`targetChartCoordinateImageSubsetIccField_of_compactCoordinateBoxSelections`.
This is the shape produced directly by compact chart-image selection. -/
theorem targetChartCoordinateImageSubsetIccField_of_chartCompactImages
    (image :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartCompactImage I (D.targetChart i))
    (image_K_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (image i).K = K)
    (box_lower_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (image i).box.a = D.targetLower i)
    (box_upper_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (image i).box.b = D.targetUpper i) :
    D.TargetChartCoordinateImageSubsetIccField := by
  intro i y hy
  have hycoord : y ∈ (image i).coordSupport := by
    simpa [ChartCompactImage.coordSupport, image_K_eq i] using hy
  have hyIcc : y ∈ Icc (image i).box.a (image i).box.b :=
    (image i).coordSupport_subset_box hycoord
  simpa [box_lower_eq i, box_upper_eq i] using hyIcc

/-- A compact-coordinate-box package and target-box neighborhoods together
provide the two endpoint-facing target-box fields. -/
theorem naturalFields_of_targetBoxNeighborhoods_and_compactCoordinateBoxSelections
    (nbrs : CoverIndexedBoundaryTargetBoxNeighborhoods D)
    (box :
      {x : M // x ∈ C.boundaryCenters} →
        CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (box_K_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (box i).K = chartCoordinateImage I (D.targetChart i) K)
    (box_lower_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (box i).a = D.targetLower i)
    (box_upper_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (box i).b = D.targetUpper i) :
    (∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (D.targetLower i) (D.targetUpper i) ⊆
        (extChartAt I (D.targetChart i)).target) ∧
      D.TargetChartCoordinateImageSubsetIccField :=
  ⟨D.targetBox_subset_target_of_targetBoxNeighborhoods nbrs,
    D.targetChartCoordinateImageSubsetIccField_of_compactCoordinateBoxSelections
      box box_K_eq box_lower_eq box_upper_eq⟩

/-- `ChartCompactImage.box` version of
`naturalFields_of_targetBoxNeighborhoods_and_compactCoordinateBoxSelections`. -/
theorem naturalFields_of_targetBoxNeighborhoods_and_chartCompactImages
    (nbrs : CoverIndexedBoundaryTargetBoxNeighborhoods D)
    (image :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartCompactImage I (D.targetChart i))
    (image_K_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (image i).K = K)
    (box_lower_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (image i).box.a = D.targetLower i)
    (box_upper_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (image i).box.b = D.targetUpper i) :
    (∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (D.targetLower i) (D.targetUpper i) ⊆
        (extChartAt I (D.targetChart i)).target) ∧
      D.TargetChartCoordinateImageSubsetIccField :=
  ⟨D.targetBox_subset_target_of_targetBoxNeighborhoods nbrs,
    D.targetChartCoordinateImageSubsetIccField_of_chartCompactImages
      image image_K_eq box_lower_eq box_upper_eq⟩

end CoverIndexedBoundaryTargetBoxData

end CoverIndexedZeroTargetBoxNaturalFields

end Stokes

end
