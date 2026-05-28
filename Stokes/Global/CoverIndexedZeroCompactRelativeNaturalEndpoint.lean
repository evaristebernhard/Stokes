import Stokes.Global.CoverIndexedZeroCompactRelativeLocalTargetSource
import Stokes.Global.CoverIndexedZeroCompactRelativeTargetBox
import Stokes.Global.CoverIndexedZeroCompactRelativeNaturalConstructor

/-!
# Natural endpoint for the relative compact-support zero route

This file packages the last glue layer around the current relative compact
endpoint.  It does not choose boxes or prove new support estimates.  Instead it
collects the already selected source transition neighborhoods, target-box data,
and local target support field, then exposes the represented Stokes conclusion
with the boundary side written as the actual target-boundary integral.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactRelativeNaturalEndpoint

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
Final natural input package for the current relative compact-support endpoint.

The record deliberately stores the source side in the transition-neighborhood
form and the target side in the compact relative target-box package.  Thus the
endpoint below no longer exposes:

* a raw `sourceNeighborhood`;
* a raw `globalBoundaryIntegral`;
* the older global target-chart-source hypothesis;
* the naked target-box fields.
-/
structure CoverIndexedZeroCompactRelativeNaturalEndpointInput
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
  targetInChartZero_tsupport_subset :
    targetData.targetBox.TargetInChartZeroTSupportSubsetIccField

namespace CoverIndexedZeroCompactRelativeNaturalEndpointInput

variable
    (D :
      CoverIndexedZeroCompactRelativeNaturalEndpointInput
        (I := I) (K := K) C P omega muBulk)

/-- The boundary scalar selected by the natural endpoint: the actual target
zero-boundary integral for the packaged target charts. -/
def boundaryIntegral : Real :=
  ∫ y,
    P.coverIndexBoundaryTargetZeroPieceSum
      D.targetData.targetBox.targetChart omega y
    ∂(volume : Measure (Fin n → Real))

/-- The represented Stokes equality and the relative zero source-target
assembly equality, with all source-neighborhood, global-boundary-integral,
global target-source, and naked target-field inputs hidden in `D`. -/
theorem representedStokes_and_zeroSourceTargetBulkAssembly_eq_integral
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    (D.carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) D.neighborhoodData D.measure_eq_volume).globalIntegral =
        D.boundaryIntegral ∧
      D.transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        D.boundaryIntegral := by
  simpa [boundaryIntegral] using
    compactSupportRepresentedStokesZeroCompact_relative_eq_integral_of_transitionBoxNeighborhoods_localTargetSupport
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)
      D.carrierData D.neighborhoodData D.measure_eq_volume
      D.transitionSupportData D.transitionNeighborhoods
      D.boundaryNeighborhood_eq
      D.targetData.targetBox D.targetData.targetChart_eq
      D.targetData.targetBox_subset_target
      D.targetInChartZero_tsupport_subset

/-- Integral-facing spelling without unfolding `D.boundaryIntegral` at the
call site. -/
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
  simpa [boundaryIntegral] using
    D.representedStokes_and_zeroSourceTargetBulkAssembly_eq_integral
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)

end CoverIndexedZeroCompactRelativeNaturalEndpointInput

end CoverIndexedZeroCompactRelativeNaturalEndpoint

end Stokes

end
