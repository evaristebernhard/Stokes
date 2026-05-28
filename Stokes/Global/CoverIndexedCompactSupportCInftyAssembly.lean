import Stokes.Global.CoverIndexedCompactSupportNaturalTheorem
import Stokes.Global.CoverIndexedInteriorCInftyLocalData
import Stokes.Global.CoverIndexedBoundaryScalarImageSupport

/-!
# C-infinity compact-support assembly

This file removes the artificial interior
`ContDiffOn Real ⊤` requirement from the compact-support represented route.

The old natural endpoint goes through `CoverIndexedAssignedBoxLocalData`, whose
interior field still stores `interiorChartExtendedBox`, hence the legacy
project-local top smoothness.  The route below keeps the same compact-support
carrier data, but proves the local Stokes equality directly from the
`C^\infty` interior local-data package.  It then assembles the global equality
from:

* assigned-self bulk reconstruction;
* pointwise cover-index local Stokes;
* target-boundary reconstruction.

Thus the new theorem consumes the natural `C^\infty` smoothness level supplied
by the smooth partition and chartwise-smooth form APIs.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportCInftyAssembly

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {μBulk : Measure (Fin (n + 1) → Real)}

/--
Smooth-neighborhood data at the natural `C^\infty` level.

Compared with `CoverIndexedCompactSupportNeighborhoodData`, this record has no
`interior_localized_contDiffOn_top` field.  Interior localized smoothness is
derived by `CoverIndexedInteriorLocalDataFromCompactSupportInfty` from
`chartwiseSmooth` and the chart-target containment of the chosen neighborhood.
-/
structure CoverIndexedCompactSupportNeighborhoodDataInfty
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) where
  chartwiseSmooth : ManifoldForm.ChartwiseSmooth I ω
  localizedChartwiseSmooth :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      ManifoldForm.ChartwiseSmooth I
        (P.coverIndexLocalizedForm ω (Sum.inr i))
  interiorNeighborhood :
    {x : M // x ∈ C.interiorCenters} →
      Set (Fin (n + 1) → Real)
  interior_neighborhood_open :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      IsOpen (interiorNeighborhood i)
  interior_Icc_subset_neighborhood :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      Icc (C.interiorLower i.1) (C.interiorUpper i.1) ⊆
        interiorNeighborhood i
  interior_neighborhood_subset_target :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      interiorNeighborhood i ⊆
        (extChartAt I (C.interiorChart i.1)).target
  boundaryNeighborhood :
    {x : M // x ∈ C.boundaryCenters} →
      Set (Fin (n + 1) → Real)
  boundary_neighborhood_open :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      IsOpen (boundaryNeighborhood i)
  boundary_Icc_subset_neighborhood :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
        boundaryNeighborhood i
  boundary_neighborhood_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryNeighborhood i ⊆
        (extChartAt I (C.boundaryChart i.1)).target

namespace CoverIndexedCompactSupportNeighborhoodDataInfty

variable
    (D :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P ω)

/-- Boundary neighborhoods lie in the self-overlap domain. -/
theorem boundary_neighborhood_subset_overlap
    (i : {x : M // x ∈ C.boundaryCenters}) :
    D.boundaryNeighborhood i ⊆
      ManifoldForm.chartOverlap I (C.boundaryChart i.1) (C.boundaryChart i.1) :=
  ManifoldForm.subset_chartOverlap_self_of_subset_target
    (I := I) (x := C.boundaryChart i.1)
    (D.boundary_neighborhood_subset_target i)

/--
Residual adapter to the legacy neighborhood record.

This is intentionally the only place in this file that mentions the old
interior top-smoothness hypothesis.  It documents the current old endpoint
blocker precisely: converting `C^\infty` neighborhood data to the legacy
record requires exactly this extra field.
-/
def toLegacy
    (interior_top :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        ContDiffOn Real ⊤
          (ManifoldForm.transitionPullbackInChart I
            (C.interiorChart i.1) (C.interiorChart i.1)
            (P.coverIndexLocalizedForm ω (Sum.inl i)))
          (D.interiorNeighborhood i)) :
    CoverIndexedCompactSupportNeighborhoodData
      (I := I) (K := K) C P ω where
  chartwiseSmooth := D.chartwiseSmooth
  localizedChartwiseSmooth := D.localizedChartwiseSmooth
  interiorNeighborhood := D.interiorNeighborhood
  interior_neighborhood_open := D.interior_neighborhood_open
  interior_Icc_subset_neighborhood := D.interior_Icc_subset_neighborhood
  interior_neighborhood_subset_target := D.interior_neighborhood_subset_target
  interior_localized_contDiffOn_top := interior_top
  boundaryNeighborhood := D.boundaryNeighborhood
  boundary_neighborhood_open := D.boundary_neighborhood_open
  boundary_Icc_subset_neighborhood := D.boundary_Icc_subset_neighborhood
  boundary_neighborhood_subset_target := D.boundary_neighborhood_subset_target

end CoverIndexedCompactSupportNeighborhoodDataInfty

namespace CoverIndexedCompactSupportCarrierData

variable
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P ω)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P ω)

/-- Interior compact-support local data at the natural `C^\infty` level. -/
def interiorLocalDataInfty :
    CoverIndexedInteriorLocalDataFromCompactSupportInfty
      (I := I) (K := K) C P ω where
  coordSupport := carrierData.interiorCoordSupport
  neighborhood := neighborhoodData.interiorNeighborhood
  base_tsupport_subset := carrierData.interior_base_tsupport_subset
  coord_mapsTo_support := carrierData.interior_coord_mapsTo_support
  coord_subset_target := carrierData.interior_coord_subset_target
  neighborhood_open := neighborhoodData.interior_neighborhood_open
  Icc_subset_neighborhood :=
    neighborhoodData.interior_Icc_subset_neighborhood
  neighborhood_subset_target :=
    neighborhoodData.interior_neighborhood_subset_target

/-- Boundary compact-support local data; it already consumes `C^\infty`
smoothness through `CoverIndexedBoundarySmoothnessFields`. -/
def boundaryLocalDataInfty :
    CoverIndexedBoundaryLocalDataFromCompactSupport
      (I := I) (K := K) C P ω where
  coordSupport := carrierData.boundaryCoordSupport
  neighborhood := neighborhoodData.boundaryNeighborhood
  coord_compact := carrierData.boundary_coord_compact
  coord_subset_halfSpace := carrierData.boundary_coord_subset_halfSpace
  base_tsupport_subset := carrierData.boundary_base_tsupport_subset
  coord_mapsTo_support := carrierData.boundary_coord_mapsTo_support
  coord_subset_target := carrierData.boundary_coord_subset_target
  neighborhood_open := neighborhoodData.boundary_neighborhood_open
  Icc_subset_neighborhood :=
    neighborhoodData.boundary_Icc_subset_neighborhood
  neighborhood_subset_target :=
    neighborhoodData.boundary_neighborhood_subset_target

/-- Boundary smoothness fields generated from chartwise smoothness and the
chosen boundary neighborhoods. -/
def boundarySmoothnessFieldsInfty
    [IsManifold I ⊤ M] :
    CoverIndexedBoundarySmoothnessFields
      P ω neighborhoodData.boundaryNeighborhood :=
  CoverIndexedBoundarySmoothnessFields.ofChartwiseSmooth
    (P := P) (omega := ω)
    neighborhoodData.chartwiseSmooth
    neighborhoodData.boundary_neighborhood_subset_target
    neighborhoodData.boundary_neighborhood_subset_overlap

/-- Boundary self-selected boxes generated without passing through
`CoverIndexedAssignedBoxLocalData`. -/
theorem sourceSelfSelectedBoxInfty
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P ω)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P ω)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    boundaryChartSelectedBox I
      (C.boundaryChart i.1) (C.boundaryChart i.1)
      (P.coverIndexLocalizedForm ω (Sum.inr i))
      (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  let boundaryData :=
    CoverIndexedCompactSupportCarrierData.boundaryLocalDataInfty
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      carrierData neighborhoodData
  rcases boundaryData.assignedFields i with
    ⟨_hcompact, _hhalf, hbase, ha0, hle, hcoeff, hdomain,
      _hopen, _hbox⟩
  refine ⟨ha0, hle, hdomain, ?_⟩
  simpa [SupportControlledSelectedPartition.coverIndexLocalizedForm] using
    (ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_halfSpaceSupportBox_of_coordSupport
        (I := I)
        (x0 := C.boundaryChart i.1) (x1 := C.boundaryChart i.1)
        (ρ := P.partition (Sum.inr i)) (ω := ω)
        (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
        (C := boundaryData.coordSupport i) hbase hcoeff)

/-- Pointwise cover-index local Stokes from compact-support carrier data and
natural `C^\infty` neighborhood data. -/
theorem localBulk_eq_localBoundaryInfty
    [IsManifold I ⊤ M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P ω)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P ω) :
    ∀ j : C.CoverIndex,
      P.coverIndexLocalBulkTerm ω j =
        P.coverIndexLocalBoundaryTerm ω j := by
  intro j
  rcases j with i | i
  · exact
      (CoverIndexedCompactSupportCarrierData.interiorLocalDataInfty
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        carrierData neighborhoodData)
        |>.coverIndexInteriorLocalBulk_eq_localBoundary
          (omega := ω) neighborhoodData.chartwiseSmooth i
  · exact
      SupportControlledCoverIndexedLocalStokesFields.boundaryLocalBulk_eq_localBoundary_of_assignedBoxFieldsAndBoundarySmoothness
        (P := P) (omega := ω)
        (CoverIndexedCompactSupportCarrierData.boundaryLocalDataInfty
          (I := I) (K := K) (C := C) (P := P) (ω := ω)
          carrierData neighborhoodData).coordSupport
        (CoverIndexedCompactSupportCarrierData.boundaryLocalDataInfty
          (I := I) (K := K) (C := C) (P := P) (ω := ω)
          carrierData neighborhoodData).neighborhood
        (CoverIndexedCompactSupportCarrierData.boundaryLocalDataInfty
          (I := I) (K := K) (C := C) (P := P) (ω := ω)
          carrierData neighborhoodData).assignedFields
        (CoverIndexedCompactSupportCarrierData.boundarySmoothnessFieldsInfty
          (I := I) (K := K) (C := C) (P := P) (ω := ω)
          neighborhoodData) i

/-- Localized assigned-chart representatives are supported in their assigned
coordinate boxes, using only `C^\infty` local data. -/
theorem localized_tsupport_subset_assignedCoordinateBoxInfty
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P ω)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P ω)
    (j : C.CoverIndex) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (C.assignedChart j) (C.assignedChart j)
          (P.coverIndexLocalizedForm ω j)) ⊆
      C.assignedCoordinateBox j := by
  rcases j with i | i
  · simpa [CompactSupportChartCoverSelection.assignedChart,
      CompactSupportChartCoverSelection.assignedCoordinateBox] using
      (CoverIndexedCompactSupportCarrierData.interiorLocalDataInfty
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        carrierData neighborhoodData)
        |>.localized_tsupport_subset_interiorBox i
  · let boundaryData :=
      CoverIndexedCompactSupportCarrierData.boundaryLocalDataInfty
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        carrierData neighborhoodData
    rcases boundaryData.assignedFields i with
      ⟨_hcompact, _hhalf, hbase, _ha0, _hle, hcoeff, _hdomain,
        _hopen, _hbox⟩
    have hsupp :
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
      simpa [SupportControlledSelectedPartition.coverIndexLocalizedForm] using
        ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_halfSpaceSupportBox_of_coordSupport
          (I := I)
          (x0 := C.boundaryChart i.1) (x1 := C.boundaryChart i.1)
          (ρ := P.partition (Sum.inr i)) (ω := ω)
          (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
          (C := boundaryData.coordSupport i) hbase hcoeff
    simpa [CompactSupportChartCoverSelection.assignedChart,
      CompactSupportChartCoverSelection.assignedCoordinateBox] using hsupp

/-- Assigned-self scalar bulk pieces are supported in their assigned boxes,
using only `C^\infty` local data. -/
theorem bulkIntegrand_tsupport_subset_assignedCoordinateBox_selfInfty
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P ω)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P ω)
    (j : C.CoverIndex) :
    tsupport (P.assignedSelfBulkPieceIntegrand (I := I) ω j) ⊆
      C.assignedCoordinateBox j := by
  simpa [SupportControlledSelectedPartition.assignedSelfBulkPieceIntegrand] using
    bulkIntegrand_tsupport_subset_of_transitionPullbackInChart_tsupport_subset
      (I := I)
      (x0 := C.assignedChart j) (x1 := C.assignedChart j)
      (η := P.coverIndexLocalizedForm ω j)
      (CoverIndexedCompactSupportCarrierData.localized_tsupport_subset_assignedCoordinateBoxInfty
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        carrierData neighborhoodData j)

/-- Natural `C^\infty` assigned-self bulk smoothness generated from the compact
support chart-box data. -/
def assignedSelfBulkSmoothnessInfty
    [IsManifold I ⊤ M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P ω)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P ω) :
    SupportControlledSelectedPartition.CoverIndexedAssignedSelfBulkSmoothnessFieldsInfty
      (I := I) (C := C) P ω where
  smoothSet := fun
    | Sum.inl i => neighborhoodData.interiorNeighborhood i
    | Sum.inr i => neighborhoodData.boundaryNeighborhood i
  isOpen_smoothSet := by
    intro j
    rcases j with i | i
    · exact neighborhoodData.interior_neighborhood_open i
    · exact neighborhoodData.boundary_neighborhood_open i
  closedCarrier_subset_smoothSet := by
    intro j
    rcases j with i | i
    · simpa [CompactSupportChartCoverSelection.coverIndexClosedCarrier,
        CompactSupportChartCoverSelection.assignedLower,
        CompactSupportChartCoverSelection.assignedUpper] using
        neighborhoodData.interior_Icc_subset_neighborhood i
    · simpa [CompactSupportChartCoverSelection.coverIndexClosedCarrier,
        CompactSupportChartCoverSelection.assignedLower,
        CompactSupportChartCoverSelection.assignedUpper] using
        neighborhoodData.boundary_Icc_subset_neighborhood i
  localized_contDiffOn := by
    intro j
    rcases j with i | i
    · simpa [CompactSupportChartCoverSelection.assignedChart] using
        (CoverIndexedCompactSupportCarrierData.interiorLocalDataInfty
          (I := I) (K := K) (C := C) (P := P) (ω := ω)
          carrierData neighborhoodData)
          |>.localized_contDiffOn_infty
            (omega := ω) neighborhoodData.chartwiseSmooth i
    · simpa [CompactSupportChartCoverSelection.assignedChart,
        SupportControlledSelectedPartition.coverIndexLocalizedForm] using
        (CoverIndexedCompactSupportCarrierData.boundarySmoothnessFieldsInfty
          (I := I) (K := K) (C := C) (P := P) (ω := ω)
          neighborhoodData)
          |>.localized_contDiffOn i

/-- Assigned-self bulk input generated directly from the `C^\infty` compact
support data. -/
noncomputable def assignedSelfBulkInputInfty
    [IsFiniteMeasureOnCompacts μBulk] [IsManifold I ⊤ M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P ω)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P ω)
    (measure_eq_volume :
      μBulk = (volume : Measure (Fin (n + 1) → Real))) :
    CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk where
  integrand := P.assignedSelfBulkIntegrand (I := I) ω
  globalIntegral :=
    ∫ y, P.assignedSelfBulkIntegrand (I := I) ω y ∂μBulk
  globalIntegral_eq_integral := rfl
  measure_eq_volume := measure_eq_volume
  piece_continuousOn_closedCarrier :=
    (CoverIndexedCompactSupportCarrierData.assignedSelfBulkSmoothnessInfty
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      carrierData neighborhoodData)
      |>.piece_continuousOn_closedCarrier
  piece_tsupport_subset_assigned :=
    CoverIndexedCompactSupportCarrierData.bulkIntegrand_tsupport_subset_assignedCoordinateBox_selfInfty
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      carrierData neighborhoodData
  integrand_ae_eq_pieceSum :=
    P.assignedSelfBulkIntegrand_ae_eq_pieceSum (I := I) ω μBulk

end CoverIndexedCompactSupportCarrierData

namespace CoverIndexedBoundaryTargetBoxData

variable
    (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω)

/-- Target-boundary measure data from scalar image support and an oriented
atlas, with the source-self selected box supplied directly rather than through
legacy assigned-box local data. -/
def toTargetBoundaryMeasureDataOfOrientedAtlasScalarImageSupportInfty
    [IsManifold I 1 M]
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      D.targetChart i ∈ A.charts)
    (localizedChartwiseSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ManifoldForm.ChartwiseSmooth I
          (P.coverIndexLocalizedForm ω (Sum.inr i)))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.targetLower i) (D.targetUpper i) ⊆
          (extChartAt I (D.targetChart i)).target)
    (scalarSupport : D.BoundaryScalarSupportSubsetImageField)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum D.targetChart ω y
          ∂(volume : Measure (Fin n → Real))) :
    CoverIndexedTargetBoundaryMeasureData
      (I := I) (K := K) C P ω where
  targetChart := D.targetChart
  targetLower := D.targetLower
  targetUpper := D.targetUpper
  boundaryIntegrand := P.coverIndexBoundaryTargetPieceSum D.targetChart ω
  globalIntegral := globalIntegral
  globalIntegral_eq_integral := globalIntegral_eq_integral
  boundaryPiece_isCompact := fun i =>
    P.coverIndexBoundaryTargetPieceSet_isCompact
      D.targetLower D.targetUpper (Sum.inr i)
  boundaryPiece_continuousOn :=
    D.boundaryPiece_continuousOn_of_localizedChartwiseSmooth
      localizedChartwiseSmooth targetBox_subset_target
  boundaryPiece_tsupport_subset :=
    D.boundaryPiece_tsupport_subset_of_scalarSupport_subset scalarSupport
  sourceSelfSelectedBox := sourceSelfSelectedBox
  sourceTargetSelectedBox := fun i => D.sourceTargetSelectedBox i
  orientedCOV := by
    let O :=
      P.coverIndexBoundaryChartOrientationInput
        (ω := ω) D.targetChart D.targetLower D.targetUpper
        (fun i => D.sourceTargetSelectedBox i)
        (fun i => (D.targetSelection i).imageData)
    exact fun i =>
      O.orientedChangeOfVariablesOfOrientedAtlas A hsource htarget i
  boundaryIntegrand_ae_eq_pieceSum :=
    P.coverIndexBoundaryTargetPieceSum_ae_eq_pieceSum D.targetChart ω

/-- Target-boundary measure data from scalar image support and oriented
manifold data, with no legacy local-data record. -/
def toTargetBoundaryMeasureDataOfOrientedManifoldScalarImageSupportInfty
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (localizedChartwiseSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ManifoldForm.ChartwiseSmooth I
          (P.coverIndexLocalizedForm ω (Sum.inr i)))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.targetLower i) (D.targetUpper i) ⊆
          (extChartAt I (D.targetChart i)).target)
    (scalarSupport : D.BoundaryScalarSupportSubsetImageField)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum D.targetChart ω y
          ∂(volume : Measure (Fin n → Real))) :
    CoverIndexedTargetBoundaryMeasureData
      (I := I) (K := K) C P ω where
  targetChart := D.targetChart
  targetLower := D.targetLower
  targetUpper := D.targetUpper
  boundaryIntegrand := P.coverIndexBoundaryTargetPieceSum D.targetChart ω
  globalIntegral := globalIntegral
  globalIntegral_eq_integral := globalIntegral_eq_integral
  boundaryPiece_isCompact := fun i =>
    P.coverIndexBoundaryTargetPieceSet_isCompact
      D.targetLower D.targetUpper (Sum.inr i)
  boundaryPiece_continuousOn :=
    D.boundaryPiece_continuousOn_of_localizedChartwiseSmooth
      localizedChartwiseSmooth targetBox_subset_target
  boundaryPiece_tsupport_subset :=
    D.boundaryPiece_tsupport_subset_of_scalarSupport_subset scalarSupport
  sourceSelfSelectedBox := sourceSelfSelectedBox
  sourceTargetSelectedBox := fun i => D.sourceTargetSelectedBox i
  orientedCOV := by
    let O :=
      P.coverIndexBoundaryChartOrientationInput
        (ω := ω) D.targetChart D.targetLower D.targetUpper
        (fun i => D.sourceTargetSelectedBox i)
        (fun i => (D.targetSelection i).imageData)
    exact fun i => O.orientedChangeOfVariablesOfOrientedManifold i
  boundaryIntegrand_ae_eq_pieceSum :=
    P.coverIndexBoundaryTargetPieceSum_ae_eq_pieceSum D.targetChart ω

end CoverIndexedBoundaryTargetBoxData

/-- Assembly theorem from assigned-self bulk and target-boundary data, using a
direct pointwise local-Stokes equality rather than the legacy local-fields
record. -/
theorem representedStokes_ofAssignedSelfBulkTargetBoundaryInfty
    [IsFiniteMeasureOnCompacts μBulk] [IsManifold I 1 M]
    (localBulk_eq_localBoundary :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          P.coverIndexLocalBoundaryTerm ω j)
    (bulk : CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk)
    (boundary : CoverIndexedTargetBoundaryMeasureData
      (I := I) (K := K) C P ω) :
    bulk.globalIntegral = boundary.globalIntegral := by
  classical
  calc
    bulk.globalIntegral =
        ∑ j : C.CoverIndex, P.coverIndexLocalBulkTerm ω j := by
      simpa using bulk.toClosedCarrierBulkData.globalIntegral_eq_localBulkSum
    _ = ∑ j : C.CoverIndex, P.coverIndexLocalBoundaryTerm ω j := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      exact localBulk_eq_localBoundary j
    _ = boundary.globalIntegral := by
      simpa using boundary.toNaturalBoundaryData.localBoundarySum_eq_globalIntegral

/-- Compact-support represented Stokes with natural `C^\infty` neighborhood
data and boundary scalar image support, for an oriented boundary atlas. -/
theorem compactSupportRepresentedStokesScalarInfty_of_orientedAtlas
    [IsFiniteMeasureOnCompacts μBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P ω)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P ω)
    (measure_eq_volume :
      μBulk = (volume : Measure (Fin (n + 1) → Real)))
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      targetBox.targetChart i ∈ A.charts)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target)
    (scalarSupport : targetBox.BoundaryScalarSupportSubsetImageField)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum targetBox.targetChart ω y
          ∂(volume : Measure (Fin n → Real))) :
    (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        (μBulk := μBulk) neighborhoodData measure_eq_volume).globalIntegral =
      globalBoundaryIntegral := by
  let boundary :=
    targetBox.toTargetBoundaryMeasureDataOfOrientedAtlasScalarImageSupportInfty
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      (CoverIndexedCompactSupportCarrierData.sourceSelfSelectedBoxInfty
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        carrierData neighborhoodData)
      A hsource htarget neighborhoodData.localizedChartwiseSmooth
      targetBox_subset_target scalarSupport
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral
  exact
    representedStokes_ofAssignedSelfBulkTargetBoundaryInfty
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      (μBulk := μBulk)
      (CoverIndexedCompactSupportCarrierData.localBulk_eq_localBoundaryInfty
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        carrierData neighborhoodData)
      (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        (μBulk := μBulk) neighborhoodData measure_eq_volume)
      boundary

/-- Compact-support represented Stokes with natural `C^\infty` neighborhood
data and boundary scalar image support, for the oriented-manifold class. -/
theorem compactSupportRepresentedStokesScalarInfty_of_orientedManifold
    [IsFiniteMeasureOnCompacts μBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P ω)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P ω)
    (measure_eq_volume :
      μBulk = (volume : Measure (Fin (n + 1) → Real)))
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target)
    (scalarSupport : targetBox.BoundaryScalarSupportSubsetImageField)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum targetBox.targetChart ω y
          ∂(volume : Measure (Fin n → Real))) :
    (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        (μBulk := μBulk) neighborhoodData measure_eq_volume).globalIntegral =
      globalBoundaryIntegral := by
  let boundary :=
    targetBox.toTargetBoundaryMeasureDataOfOrientedManifoldScalarImageSupportInfty
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      (CoverIndexedCompactSupportCarrierData.sourceSelfSelectedBoxInfty
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        carrierData neighborhoodData)
      neighborhoodData.localizedChartwiseSmooth
      targetBox_subset_target scalarSupport
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral
  exact
    representedStokes_ofAssignedSelfBulkTargetBoundaryInfty
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      (μBulk := μBulk)
      (CoverIndexedCompactSupportCarrierData.localBulk_eq_localBoundaryInfty
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        carrierData neighborhoodData)
      (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        (μBulk := μBulk) neighborhoodData measure_eq_volume)
      boundary

end CompactSupportCInftyAssembly

end Stokes

end
