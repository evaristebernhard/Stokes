import Stokes.Global.CoverIndexedZeroCompactSelectedNaturalEndpoint
import Stokes.Global.CoverIndexedZeroCompactTargetImageContainment

/-!
# Selected natural compact endpoint from chart-transition containment

This file is the next glue layer above
`CoverIndexedZeroCompactSelectedNaturalEndpoint`.  It replaces the explicit
manifold-side containment

`boundaryChartBoxNeighborhood ... ⊆ target-chart preimage of the target box`

by the more coordinate-native hypothesis that the ambient chart transition maps
the selected half-space source box into the selected target coordinate box.

No chart-transition `MapsTo` theorem is proved here; this file only routes that
honest geometric input into the compact-support represented endpoint.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactSelectedNaturalFromTransition

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

/--
Selected compact-support endpoint input whose target support is controlled by
ambient chart-transition containment on the selected half-space source boxes.

Compared with `CoverIndexedZeroCompactSelectedNaturalEndpointInput`, this
record no longer asks for the already-pushed-forward manifold-side boundary box
containment.  It asks for the coordinate `MapsTo` statement that later
selection lemmas should construct from continuity/local compactness.
-/
structure CoverIndexedZeroCompactSelectedNaturalFromTransitionInput
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n)
    (muBulk : Measure (Fin (n + 1) → Real)) where
  carrierData :
    CoverIndexedCompactSupportCarrierData
      (I := I) (K := K) C P omega
  neighborhoodData :
    CoverIndexedCompactSupportNeighborhoodDataInfty
      (I := I) (K := K) C P omega
  measure_eq_volume :
    muBulk = (volume : Measure (Fin (n + 1) → Real))
  transitionSupportData :
    CoverIndexedCompactSupportTransitionSupportData
      (I := I) (K := K) C P omega
  transitionNeighborhoods :
    CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C transitionSupportData.targetChart
  boundaryNeighborhood_eq :
    neighborhoodData.boundaryNeighborhood =
      transitionNeighborhoods.boundaryNeighborhood
  targetData :
    CoverIndexedZeroCompactRelativeTargetBoxData
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData
  omega_support_subset :
    ManifoldForm.support I omega ⊆ K
  chartTransition_mapsTo :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      MapsTo
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (targetData.targetBox.targetChart i))
        (halfSpaceSupportBox (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (Icc (targetData.targetBox.targetLower i)
          (targetData.targetBox.targetUpper i))

namespace CoverIndexedZeroCompactSelectedNaturalFromTransitionInput

variable
    (D :
      CoverIndexedZeroCompactSelectedNaturalFromTransitionInput
        (I := I) (K := K) C P omega muBulk)

/-- Manifold-side boundary-box containment generated from the coordinate
chart-transition `MapsTo` hypothesis. -/
def boundaryBox_subset_targetPreimage :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryChartBoxNeighborhood I (C.boundaryChart i.1)
          (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
        {p : M | (extChartAt I (D.targetData.targetBox.targetChart i)) p ∈
          Icc (D.targetData.targetBox.targetLower i)
            (D.targetData.targetBox.targetUpper i)} :=
  D.targetData.targetBox.boundaryChartBox_subset_targetPreimage_of_chartTransition_mapsTo
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    D.chartTransition_mapsTo

/-- The target-zero support field generated directly from global support and
ambient chart-transition containment. -/
def targetInChartZero_tsupport_subset :
    D.targetData.targetBox.TargetInChartZeroTSupportSubsetIccField :=
  D.targetData.targetBox.targetInChartZero_tsupport_subset_Icc_of_chartTransition_mapsTo
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    D.omega_support_subset D.chartTransition_mapsTo

/-- Forget the coordinate `MapsTo` input after generating the selected natural
boundary-box containment required by the previous endpoint layer. -/
def toSelectedNaturalEndpointInput :
    CoverIndexedZeroCompactSelectedNaturalEndpointInput
      (I := I) (K := K) C P omega muBulk where
  carrierData := D.carrierData
  neighborhoodData := D.neighborhoodData
  measure_eq_volume := D.measure_eq_volume
  transitionSupportData := D.transitionSupportData
  transitionNeighborhoods := D.transitionNeighborhoods
  boundaryNeighborhood_eq := D.boundaryNeighborhood_eq
  targetData := D.targetData
  omega_support_subset := D.omega_support_subset
  boundaryBox_subset_targetPreimage :=
    D.boundaryBox_subset_targetPreimage
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)

/-- Direct projection to the relative endpoint input, using the support field
generated from chart-transition containment. -/
def toRelativeNaturalEndpointInput :
    CoverIndexedZeroCompactRelativeNaturalEndpointInput
      (I := I) (K := K) C P omega muBulk where
  carrierData := D.carrierData
  neighborhoodData := D.neighborhoodData
  measure_eq_volume := D.measure_eq_volume
  transitionSupportData := D.transitionSupportData
  transitionNeighborhoods := D.transitionNeighborhoods
  boundaryNeighborhood_eq := D.boundaryNeighborhood_eq
  targetData := D.targetData
  targetInChartZero_tsupport_subset :=
    D.targetInChartZero_tsupport_subset
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)

/-- The boundary scalar selected by this transition-controlled endpoint. -/
def boundaryIntegral : Real :=
  (D.toRelativeNaturalEndpointInput
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)).boundaryIntegral

/-- Represented compact-support Stokes, with target-zero support generated
from global support and ambient chart-transition containment. -/
theorem representedStokes_and_zeroSourceTargetBulkAssembly_eq_integral
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    (D.carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) D.neighborhoodData D.measure_eq_volume).globalIntegral =
        D.boundaryIntegral
          (I := I) (K := K) (C := C) (P := P) (omega := omega)
          (muBulk := muBulk) ∧
      D.transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        D.boundaryIntegral
          (I := I) (K := K) (C := C) (P := P) (omega := omega)
          (muBulk := muBulk) := by
  simpa [boundaryIntegral, toRelativeNaturalEndpointInput] using
    (D.toRelativeNaturalEndpointInput
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)).representedStokes_and_zeroSourceTargetBulkAssembly_eq_integral

/-- Integral-facing spelling of the transition-controlled selected endpoint. -/
theorem representedStokes_and_zeroSourceTargetBulkAssembly
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    (D.carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) D.neighborhoodData D.measure_eq_volume).globalIntegral =
        ∫ y,
          P.coverIndexBoundaryTargetZeroPieceSum
            D.targetData.targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real)) ∧
      D.transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        ∫ y,
          P.coverIndexBoundaryTargetZeroPieceSum
            D.targetData.targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real)) := by
  simpa [boundaryIntegral,
    CoverIndexedZeroCompactRelativeNaturalEndpointInput.boundaryIntegral,
    toRelativeNaturalEndpointInput] using
    D.representedStokes_and_zeroSourceTargetBulkAssembly_eq_integral
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)

end CoverIndexedZeroCompactSelectedNaturalFromTransitionInput

end CoverIndexedZeroCompactSelectedNaturalFromTransition

end Stokes

end
