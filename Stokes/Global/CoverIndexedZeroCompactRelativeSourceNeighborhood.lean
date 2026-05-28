import Stokes.Global.CoverIndexedZeroCompactRelativeIntegralStatement
import Stokes.Global.CoverIndexedZeroNeighborhoodShrink

/-!
# Source-neighborhood wrappers for the relative compact endpoint

This file removes the hand-written `sourceNeighborhood` field from the
relative compact-support zero endpoint in the three source-selection situations
already used elsewhere in the cover-indexed development.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactRelativeSourceNeighborhood

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {muBulk : Measure (Fin (n + 1) → Real)}

/-- Relative compact-support represented Stokes with the source-neighborhood
field generated from a whole-neighborhood source-box shrink. -/
theorem compactSupportRepresentedStokesZeroCompact_relative_eq_integral_of_boundaryNeighborhood_subset_sourceBox
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P omega)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (measure_eq_volume :
      muBulk = (volume : Measure (Fin (n + 1) → Real)))
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (boundaryNeighborhood_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (targetChart_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        transitionSupportData.targetChart i = targetBox.targetChart i)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target)
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (targetBox.targetChart i)).source)
    (homegaSupport : ManifoldForm.support I omega ⊆ K)
    (coordinateImage_subset_targetBox :
      targetBox.TargetChartCoordinateImageSubsetIccField) :
    (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) neighborhoodData measure_eq_volume).globalIntegral =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real)) ∧
      transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real)) := by
  exact
    compactSupportRepresentedStokesZeroCompact_relative_eq_integral_of_globalSupport
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)
      carrierData neighborhoodData measure_eq_volume transitionSupportData
      (neighborhoodData.boundaryNeighborhoodSubsetTransitionSource_of_neighborhood_subset_sourceBox
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData boundaryNeighborhood_subset_sourceBox)
      targetBox targetChart_eq targetBox_subset_target
      hK hsource homegaSupport coordinateImage_subset_targetBox

/-- Boundary-box neighborhood version of the relative compact-support endpoint.
The packaged neighborhood selection supplies the source-neighborhood field once
its neighborhoods agree with `neighborhoodData` and lie in the selected source
boxes. -/
theorem compactSupportRepresentedStokesZeroCompact_relative_eq_integral_of_boundaryBoxNeighborhoods
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P omega)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (measure_eq_volume :
      muBulk = (volume : Measure (Fin (n + 1) → Real)))
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (nbrs : CoverIndexedBoundaryBoxNeighborhoods (I := I) C)
    (hneighborhood :
      neighborhoodData.boundaryNeighborhood = nbrs.neighborhood)
    (hnbrs_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        nbrs.neighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (targetChart_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        transitionSupportData.targetChart i = targetBox.targetChart i)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target)
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (targetBox.targetChart i)).source)
    (homegaSupport : ManifoldForm.support I omega ⊆ K)
    (coordinateImage_subset_targetBox :
      targetBox.TargetChartCoordinateImageSubsetIccField) :
    (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) neighborhoodData measure_eq_volume).globalIntegral =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real)) ∧
      transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real)) := by
  exact
    compactSupportRepresentedStokesZeroCompact_relative_eq_integral_of_globalSupport
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)
      carrierData neighborhoodData measure_eq_volume transitionSupportData
      (neighborhoodData.boundaryNeighborhoodSubsetTransitionSource_of_boundaryBoxNeighborhoods
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData nbrs hneighborhood hnbrs_subset_sourceBox)
      targetBox targetChart_eq targetBox_subset_target
      hK hsource homegaSupport coordinateImage_subset_targetBox

/-- Transition-neighborhood version of the relative compact-support endpoint.
This is the cleanest source-side input when the chart-box selection has already
chosen open neighborhoods contained in the source-to-target overlap. -/
theorem compactSupportRepresentedStokesZeroCompact_relative_eq_integral_of_transitionBoxNeighborhoods
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P omega)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (measure_eq_volume :
      muBulk = (volume : Measure (Fin (n + 1) → Real)))
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (nbrs : CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C transitionSupportData.targetChart)
    (hneighborhood :
      neighborhoodData.boundaryNeighborhood = nbrs.boundaryNeighborhood)
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (targetChart_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        transitionSupportData.targetChart i = targetBox.targetChart i)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target)
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (targetBox.targetChart i)).source)
    (homegaSupport : ManifoldForm.support I omega ⊆ K)
    (coordinateImage_subset_targetBox :
      targetBox.TargetChartCoordinateImageSubsetIccField) :
    (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) neighborhoodData measure_eq_volume).globalIntegral =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real)) ∧
      transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real)) := by
  exact
    compactSupportRepresentedStokesZeroCompact_relative_eq_integral_of_globalSupport
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)
      carrierData neighborhoodData measure_eq_volume transitionSupportData
      (neighborhoodData.boundaryNeighborhoodSubsetTransitionSource_of_transitionBoxNeighborhoods
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData nbrs hneighborhood)
      targetBox targetChart_eq targetBox_subset_target
      hK hsource homegaSupport coordinateImage_subset_targetBox

end CoverIndexedZeroCompactRelativeSourceNeighborhood

end Stokes

end
