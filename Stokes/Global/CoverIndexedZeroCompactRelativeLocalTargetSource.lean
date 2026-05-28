import Stokes.Global.CoverIndexedZeroCompactLocalizedTargetSupport
import Stokes.Global.CoverIndexedZeroNeighborhoodShrink

/-!
# Relative compact endpoints from source selection and local target support

This file combines two refinements of the compact zero route:

* source-neighborhood fields are generated from chart-box shrink data;
* target support is supplied in the genuinely local form
  `TargetInChartZeroTSupportSubsetIccField`.

The resulting wrappers no longer expose `sourceNeighborhood`, no longer use the
strong global target-chart-source condition, and state the boundary side as the
actual zero target-boundary integral.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactRelativeLocalTargetSource

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

/-- Relative compact-support represented Stokes from a source-box shrink and a
local target-support field.

This wrapper simultaneously removes the hand-written source-neighborhood field,
the artificial boundary scalar, and the older global target-chart-source
hypothesis. -/
theorem compactSupportRepresentedStokesZeroCompact_relative_eq_integral_of_boundaryNeighborhood_subset_sourceBox_localTargetSupport
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
    (targetInChartZero_tsupport_subset :
      targetBox.TargetInChartZeroTSupportSubsetIccField) :
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
    compactSupportRepresentedStokesZeroCompact_of_localTargetSupport_relative
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)
      carrierData neighborhoodData measure_eq_volume transitionSupportData
      (neighborhoodData.boundaryNeighborhoodSubsetTransitionSource_of_neighborhood_subset_sourceBox
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData boundaryNeighborhood_subset_sourceBox)
      targetBox targetChart_eq targetBox_subset_target
      targetInChartZero_tsupport_subset
      (∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
        ∂(volume : Measure (Fin n → Real)))
      rfl

/-- Boundary-box-neighborhood version of
`compactSupportRepresentedStokesZeroCompact_relative_eq_integral_of_boundaryNeighborhood_subset_sourceBox_localTargetSupport`. -/
theorem compactSupportRepresentedStokesZeroCompact_relative_eq_integral_of_boundaryBoxNeighborhoods_localTargetSupport
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
    (targetInChartZero_tsupport_subset :
      targetBox.TargetInChartZeroTSupportSubsetIccField) :
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
    compactSupportRepresentedStokesZeroCompact_of_localTargetSupport_relative
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)
      carrierData neighborhoodData measure_eq_volume transitionSupportData
      (neighborhoodData.boundaryNeighborhoodSubsetTransitionSource_of_boundaryBoxNeighborhoods
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData nbrs hneighborhood hnbrs_subset_sourceBox)
      targetBox targetChart_eq targetBox_subset_target
      targetInChartZero_tsupport_subset
      (∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
        ∂(volume : Measure (Fin n → Real)))
      rfl

/-- Transition-neighborhood version.  This is the source-side form closest to
the chart-box selection data used near boundary chart transitions. -/
theorem compactSupportRepresentedStokesZeroCompact_relative_eq_integral_of_transitionBoxNeighborhoods_localTargetSupport
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
    (targetInChartZero_tsupport_subset :
      targetBox.TargetInChartZeroTSupportSubsetIccField) :
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
    compactSupportRepresentedStokesZeroCompact_of_localTargetSupport_relative
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)
      carrierData neighborhoodData measure_eq_volume transitionSupportData
      (neighborhoodData.boundaryNeighborhoodSubsetTransitionSource_of_transitionBoxNeighborhoods
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData nbrs hneighborhood)
      targetBox targetChart_eq targetBox_subset_target
      targetInChartZero_tsupport_subset
      (∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
        ∂(volume : Measure (Fin n → Real)))
      rfl

end CoverIndexedZeroCompactRelativeLocalTargetSource

end Stokes

end
