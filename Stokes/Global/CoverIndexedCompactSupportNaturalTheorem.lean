import Stokes.Global.CoverIndexedCompactSupportRepresentedStokes
import Stokes.Global.CoverIndexedLocalDataFromCompactSupport
import Stokes.Global.CoverIndexedBoundaryTargetImageSupport
import Stokes.Global.CoverIndexedBoundaryTargetSmoothnessConstructor
import Stokes.Global.CoverIndexedSourceTargetSelectedBoxConstructor

/-!
# Compact-support represented Stokes, natural chart-box assembly

This file is only an integration layer.  It groups the remaining inputs for
the compact-support represented route by their mathematical role and then
calls the current represented-Stokes endpoint.

No chart-box existence, local inverse, or image-support theorem is proved here:
those are kept as explicit fields in the grouped inputs.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportNaturalTheorem

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

/-- Coordinate-carrier data selected from compact support.

This is the part of chart-box selection that says the base representatives are
carried by compact coordinate sets lying in the appropriate chart targets. -/
structure CoverIndexedCompactSupportCarrierData
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) where
  interiorCoordSupport :
    {x : M // x ∈ C.interiorCenters} →
      Set (Fin (n + 1) → Real)
  interior_base_tsupport_subset :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.interiorChart i.1) (C.interiorChart i.1) ω) ⊆
        interiorCoordSupport i
  interior_coord_mapsTo_support :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      ∀ y ∈ interiorCoordSupport i,
        (extChartAt I (C.interiorChart i.1)).symm y ∈ K
  interior_coord_subset_target :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      interiorCoordSupport i ⊆
        (extChartAt I (C.interiorChart i.1)).target
  boundaryCoordSupport :
    {x : M // x ∈ C.boundaryCenters} →
      Set (Fin (n + 1) → Real)
  boundary_coord_compact :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      IsCompact (boundaryCoordSupport i)
  boundary_coord_subset_halfSpace :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryCoordSupport i ⊆ upperHalfSpace n
  boundary_base_tsupport_subset :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1) ω) ⊆
        boundaryCoordSupport i
  boundary_coord_mapsTo_support :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      ∀ y ∈ boundaryCoordSupport i,
        (extChartAt I (C.boundaryChart i.1)).symm y ∈ K
  boundary_coord_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryCoordSupport i ⊆
        (extChartAt I (C.boundaryChart i.1)).target

/-- Smooth-neighborhood data around the selected chart boxes.

The chartwise smoothness fields live here because they are the smooth input
used by the local and target-box continuity constructors. -/
structure CoverIndexedCompactSupportNeighborhoodData
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
  interior_localized_contDiffOn_top :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I
          (C.interiorChart i.1) (C.interiorChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inl i)))
        (interiorNeighborhood i)
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

namespace CoverIndexedCompactSupportCarrierData

variable
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P ω)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodData
        (I := I) (K := K) C P ω)

/-- Interior compact-support local data assembled from the carrier and
neighborhood blocks. -/
def interiorLocalData :
    CoverIndexedInteriorLocalDataFromCompactSupport
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
  localized_contDiffOn_top :=
    neighborhoodData.interior_localized_contDiffOn_top

/-- Boundary compact-support local data assembled from the carrier and
neighborhood blocks. -/
def boundaryLocalData :
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

/-- Grouped compact-support local data assembled from carrier and neighborhood
blocks. -/
def localDataFromCompactSupport :
    CoverIndexedLocalDataFromCompactSupport
      (I := I) (K := K) C P ω where
  interior := carrierData.interiorLocalData neighborhoodData
  boundary := carrierData.boundaryLocalData neighborhoodData
  chartwiseSmooth := neighborhoodData.chartwiseSmooth

/-- Endpoint local-data record generated from compact-support chart-box data. -/
def assignedBoxLocalData
    [IsManifold I ⊤ M] :
    CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω :=
  (carrierData.localDataFromCompactSupport neighborhoodData).toAssignedBoxLocalData

end CoverIndexedCompactSupportCarrierData

/-- Source-to-target transition support data.

These are precisely the remaining support and overlap facts used by
`CoverIndexedBoundaryTargetBoxData.ofTargetSelectionAndCoordSupport`. -/
structure CoverIndexedCompactSupportTransitionSupportData
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) where
  targetChart : {x : M // x ∈ C.boundaryCenters} → M
  transitionCoordSupport :
    {x : M // x ∈ C.boundaryCenters} →
      Set (Fin (n + 1) → Real)
  sourceBox_subset_overlap :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
        ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)
  base_tsupport_subset_transitionCoordSupport :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.boundaryChart i.1) (targetChart i) ω) ⊆
        transitionCoordSupport i
  coeff_tsupport_inter_subset_halfSpaceBox :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      tsupport
          (ManifoldForm.transitionCoefficientInChart I
            (C.boundaryChart i.1) (targetChart i)
            (P.partition (Sum.inr i))) ∩
          transitionCoordSupport i ⊆
        halfSpaceSupportBox
          (C.boundaryLower i.1) (C.boundaryUpper i.1)

/-- Target-box data selected after transition support has produced the
source-to-target selected boxes. -/
structure CoverIndexedCompactSupportTargetBoxData
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P ω) where
  targetBox : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω
  targetChart_eq :
    targetBox.targetChart = transitionSupportData.targetChart
  targetBox_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
        (extChartAt I (targetBox.targetChart i)).target

namespace CoverIndexedCompactSupportTargetBoxData

variable
    (localData :
      CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P ω)

/-- Constructor for target-box data from target selections and transition
support control. -/
def ofTargetSelectionAndTransitionSupport
    (targetSelection :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartTargetBoxSelection I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc
            ((CoverIndexedBoundaryTargetBoxData.ofTargetSelectionAndCoordSupport
              (I := I) (K := K) (C := C) (P := P) (ω := ω)
              localData
              transitionSupportData.targetChart
              targetSelection
              transitionSupportData.transitionCoordSupport
              transitionSupportData.sourceBox_subset_overlap
              transitionSupportData.base_tsupport_subset_transitionCoordSupport
              transitionSupportData.coeff_tsupport_inter_subset_halfSpaceBox).targetLower i)
            ((CoverIndexedBoundaryTargetBoxData.ofTargetSelectionAndCoordSupport
              (I := I) (K := K) (C := C) (P := P) (ω := ω)
              localData
              transitionSupportData.targetChart
              targetSelection
              transitionSupportData.transitionCoordSupport
              transitionSupportData.sourceBox_subset_overlap
              transitionSupportData.base_tsupport_subset_transitionCoordSupport
              transitionSupportData.coeff_tsupport_inter_subset_halfSpaceBox).targetUpper i) ⊆
          (extChartAt I
            ((CoverIndexedBoundaryTargetBoxData.ofTargetSelectionAndCoordSupport
              (I := I) (K := K) (C := C) (P := P) (ω := ω)
              localData
              transitionSupportData.targetChart
              targetSelection
              transitionSupportData.transitionCoordSupport
              transitionSupportData.sourceBox_subset_overlap
              transitionSupportData.base_tsupport_subset_transitionCoordSupport
              transitionSupportData.coeff_tsupport_inter_subset_halfSpaceBox).targetChart i)).target) :
    CoverIndexedCompactSupportTargetBoxData
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      transitionSupportData where
  targetBox :=
    CoverIndexedBoundaryTargetBoxData.ofTargetSelectionAndCoordSupport
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      localData
      transitionSupportData.targetChart
      targetSelection
      transitionSupportData.transitionCoordSupport
      transitionSupportData.sourceBox_subset_overlap
      transitionSupportData.base_tsupport_subset_transitionCoordSupport
      transitionSupportData.coeff_tsupport_inter_subset_halfSpaceBox
  targetChart_eq := rfl
  targetBox_subset_target := targetBox_subset_target

end CoverIndexedCompactSupportTargetBoxData

/-- Boundary image-support data.

The field is stated at the ordinary `Function.support` level; the constructor
in `CoverIndexedBoundaryTargetImageSupport` upgrades it to `tsupport` using
closedness of the selected target image. -/
structure CoverIndexedCompactSupportBoundaryImageSupportData
    {transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P ω}
    (targetBoxData :
      CoverIndexedCompactSupportTargetBoxData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        transitionSupportData) where
  targetInChart_support_subset_image :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Function.support
          (ManifoldForm.inChart I (targetBoxData.targetBox.targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
        boundaryChartTransitionAmbientBoundaryImage I
          (C.boundaryChart i.1) (targetBoxData.targetBox.targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)

namespace CoverIndexedCompactSupportBoundaryImageSupportData

variable
    {transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P ω}
    {targetBoxData :
      CoverIndexedCompactSupportTargetBoxData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        transitionSupportData}
    (boundaryImageSupportData :
      CoverIndexedCompactSupportBoundaryImageSupportData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        targetBoxData)

/-- Upgrade ordinary boundary-image support to the target `tsupport` field
required by the represented endpoint. -/
def targetInChart_tsupport_subset_image :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      tsupport
          (ManifoldForm.inChart I (targetBoxData.targetBox.targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
        boundaryChartTransitionAmbientBoundaryImage I
          (C.boundaryChart i.1) (targetBoxData.targetBox.targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  targetBoxData.targetBox.targetInChart_tsupport_subset_image_of_support_subset
    boundaryImageSupportData.targetInChart_support_subset_image

end CoverIndexedCompactSupportBoundaryImageSupportData

/-- Global represented integral data.

The bulk measure normalization is stored here because this is the final
represented-integral block consumed by the endpoint. -/
structure CoverIndexedCompactSupportGlobalBoundaryIntegralData
    (μBulk : Measure (Fin (n + 1) → Real))
    {transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P ω}
    (targetBoxData :
      CoverIndexedCompactSupportTargetBoxData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        transitionSupportData) where
  measure_eq_volume :
    μBulk = (volume : Measure (Fin (n + 1) → Real))
  globalBoundaryIntegral : Real
  globalBoundaryIntegral_eq_integral :
    globalBoundaryIntegral =
      ∫ y,
        P.coverIndexBoundaryTargetPieceSum
            targetBoxData.targetBox.targetChart ω y
        ∂(volume : Measure (Fin n → Real))

/-- Natural represented endpoint input assembled from the grouped chart-box
data above. -/
def compactSupportRepresentedStokesNaturalInput
    [IsManifold I ⊤ M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P ω)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodData
        (I := I) (K := K) C P ω)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P ω)
    (targetBoxData :
      CoverIndexedCompactSupportTargetBoxData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        transitionSupportData)
    (boundaryImageSupportData :
      CoverIndexedCompactSupportBoundaryImageSupportData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        targetBoxData)
    (globalBoundaryIntegral :
      CoverIndexedCompactSupportGlobalBoundaryIntegralData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        μBulk targetBoxData) :
    CoverIndexedCompactSupportRepresentedStokesNaturalInput
      (I := I) (K := K) (ω := ω) (C := C) (P := P)
      (μBulk := μBulk) where
  localData :=
    carrierData.assignedBoxLocalData neighborhoodData
  measure_eq_volume :=
    globalBoundaryIntegral.measure_eq_volume
  targetBox :=
    targetBoxData.targetBox
  localizedChartwiseSmooth :=
    neighborhoodData.localizedChartwiseSmooth
  targetBox_subset_target :=
    targetBoxData.targetBox_subset_target
  targetInChart_tsupport_subset_image :=
    boundaryImageSupportData.targetInChart_tsupport_subset_image
  globalBoundaryIntegral :=
    globalBoundaryIntegral.globalBoundaryIntegral
  globalBoundaryIntegral_eq_integral :=
    globalBoundaryIntegral.globalBoundaryIntegral_eq_integral

/-- Compact-support represented Stokes from grouped compact chart-box data.

This theorem intentionally leaves the true remaining mathematical work as
grouped inputs: carrier selection, smooth neighborhoods, transition support,
target-box selection, boundary image support, and the represented global
boundary integral. -/
theorem compactSupportRepresentedStokes_of_compactChartBoxData
    [IsFiniteMeasureOnCompacts μBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P ω)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodData
        (I := I) (K := K) C P ω)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P ω)
    (targetBoxData :
      CoverIndexedCompactSupportTargetBoxData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        transitionSupportData)
    (boundaryImageSupportData :
      CoverIndexedCompactSupportBoundaryImageSupportData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        targetBoxData)
    (globalBoundaryIntegral :
      CoverIndexedCompactSupportGlobalBoundaryIntegralData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        μBulk targetBoxData) :
    ((compactSupportRepresentedStokesNaturalInput
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        (μBulk := μBulk)
        carrierData neighborhoodData transitionSupportData targetBoxData
        boundaryImageSupportData globalBoundaryIntegral).assignedSelfBulkInput).globalIntegral =
      globalBoundaryIntegral.globalBoundaryIntegral :=
by
  let D :=
    compactSupportRepresentedStokesNaturalInput
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      (μBulk := μBulk)
      carrierData neighborhoodData transitionSupportData targetBoxData
      boundaryImageSupportData globalBoundaryIntegral
  exact D.representedStokes_globalBoundaryIntegral_of_orientedManifold

end CompactSupportNaturalTheorem

end Stokes

end
