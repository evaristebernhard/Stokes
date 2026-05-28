import Stokes.Global.CoverIndexedZeroAssemblyBridge
import Stokes.Global.CoverIndexedZeroBoundaryScalarIntegral

/-!
# Zero-boundary-scalar assembly bridge

This file is the endpoint-facing bridge for the zero-extension route when the
boundary side is represented directly by the zero-extended target scalar sum.
Unlike `CoverIndexedZeroAssemblyBridgeEndpointInput`, it does not carry the old
target scalar face-support hypothesis.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroBoundaryScalarAssemblyBridge

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

/-- Endpoint-facing bridge record for the zero-boundary-scalar route.

The represented compact-support Stokes endpoint uses the zero target scalar sum
as its boundary representative, while `sourceTargetAssembly` supplies the local
source-target zero bulk assembly.  The only global reconstruction field here is
the equality between the chosen global boundary integral and that zero scalar
sum. -/
structure CoverIndexedZeroBoundaryScalarAssemblyBridgeEndpointInput
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
  targetBox :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega
  targetBox_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
        (extChartAt I (targetBox.targetChart i)).target
  zeroScalarSupport :
    targetBox.BoundaryZeroScalarSupportSubsetImageField
  sourceTargetAssembly :
    CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput
      (I := I) (K := K) C P omega
  globalBoundaryIntegral_eq_integral :
    sourceTargetAssembly.globalBoundaryIntegral =
      ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
        ∂(volume : Measure (Fin n → Real))

namespace CoverIndexedZeroBoundaryScalarAssemblyBridgeEndpointInput

variable
    (D :
      CoverIndexedZeroBoundaryScalarAssemblyBridgeEndpointInput
        (I := I) (K := K) C P omega muBulk)

/-- Represented compact-support Stokes plus the source-target zero bulk
assembly, using the zero target scalar sum as the boundary representative.

This is the zero-boundary-scalar counterpart of
`CoverIndexedZeroAssemblyBridgeEndpointInput.representedStokes_and_zeroSourceTargetBulkAssembly`;
in particular, it has no `oldScalarSupport_subset_targetFace` input. -/
theorem representedStokes_and_zeroSourceTargetBulkAssembly
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    (D.carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk)
        D.neighborhoodData D.measure_eq_volume).globalIntegral =
        D.sourceTargetAssembly.globalBoundaryIntegral ∧
      D.sourceTargetAssembly.transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        D.sourceTargetAssembly.globalBoundaryIntegral := by
  refine ⟨?_, ?_⟩
  · exact
      compactSupportRepresentedStokesZeroBoundaryScalarInfty_of_orientedManifold
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk)
        D.carrierData D.neighborhoodData D.measure_eq_volume
        D.targetBox D.targetBox_subset_target D.zeroScalarSupport
        D.sourceTargetAssembly.globalBoundaryIntegral
        D.globalBoundaryIntegral_eq_integral
  · exact
      D.sourceTargetAssembly.zeroBulkSetIntegralSum_eq_globalBoundaryIntegral
        (I := I) (K := K) (C := C) (P := P) (omega := omega)

end CoverIndexedZeroBoundaryScalarAssemblyBridgeEndpointInput

end CoverIndexedZeroBoundaryScalarAssemblyBridge

end Stokes

end
