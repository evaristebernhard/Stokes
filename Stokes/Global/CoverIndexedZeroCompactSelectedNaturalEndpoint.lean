import Stokes.Global.CoverIndexedZeroCompactRelativeNaturalEndpoint
import Stokes.Global.CoverIndexedZeroCompactLocalizedPartitionSupport
import Stokes.Global.CoverIndexedZeroCompactSourceTransitionSelection
import Stokes.Global.CoverIndexedZeroCompactTargetBoxSelection

/-!
# Selected natural compact-support endpoint

This file is a glue layer around the current relative compact-support endpoint.
It does not prove new chart geometry.  Instead it records the honest geometric
containment that a selected boundary chart box is mapped into the selected
target coordinate box, then uses the partition support control to build the
target-zero topological-support field consumed by the endpoint.

The resulting input package no longer asks callers to provide

`targetInChartZero_tsupport_subset`

directly.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactSelectedNaturalEndpoint

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
Natural selected-chart input for the compact-support relative endpoint.

Compared with `CoverIndexedZeroCompactRelativeNaturalEndpointInput`, this
record replaces the explicit target-zero `tsupport` field by the more geometric
data that the selected boundary box lies in the preimage of the selected target
box, together with the global support control of `omega`.
-/
structure CoverIndexedZeroCompactSelectedNaturalEndpointInput
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
  boundaryBox_subset_targetPreimage :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryChartBoxNeighborhood I (C.boundaryChart i.1)
          (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
        {p : M | (extChartAt I (targetData.targetBox.targetChart i)) p ∈
          Icc (targetData.targetBox.targetLower i)
            (targetData.targetBox.targetUpper i)}

namespace CoverIndexedZeroCompactSelectedNaturalEndpointInput

variable
    (D :
      CoverIndexedZeroCompactSelectedNaturalEndpointInput
        (I := I) (K := K) C P omega muBulk)

/-- The target-zero support field generated from global support control and
the selected boundary-box image containment. -/
def targetInChartZero_tsupport_subset :
    D.targetData.targetBox.TargetInChartZeroTSupportSubsetIccField :=
  D.targetData.targetBox.targetInChartZero_tsupport_subset_Icc_of_boundaryBox_subset_preimage
    (I := I) (K := K) (C := C) (P := P) (ω := omega)
    D.omega_support_subset
    D.boundaryBox_subset_targetPreimage

/-- Forget the selected-box containment input after generating the target
support field required by the previous natural endpoint. -/
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

/-- The boundary scalar selected by this endpoint: the actual target-boundary
integral attached to the selected target charts. -/
def boundaryIntegral : Real :=
  (D.toRelativeNaturalEndpointInput
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)).boundaryIntegral

/-- Represented compact-support Stokes, with target-zero `tsupport` generated
from selected boundary-box containment and global support. -/
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

/-- Integral-facing spelling of the selected natural endpoint. -/
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

end CoverIndexedZeroCompactSelectedNaturalEndpointInput

end CoverIndexedZeroCompactSelectedNaturalEndpoint

end Stokes

end
