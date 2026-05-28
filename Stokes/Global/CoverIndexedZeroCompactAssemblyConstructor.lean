import Stokes.Global.CoverIndexedZeroAssemblyBridge
import Stokes.Global.CoverIndexedZeroBoundaryScalarIntegral
import Stokes.Global.CoverIndexedZeroTargetBoxFromCompact

/-!
# Compact-support constructors for zero-scalar assembly

This file is the compact-support constructor layer for the zero-boundary-scalar
route.  It keeps the remaining global boundary reconstruction in the
source-target assembly package, but derives the endpoint zero scalar support
from global compact support and target coordinate-image containment.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactAssemblyConstructor

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

/-- Compact-support input for the zero-boundary-scalar source-target assembly.

The analytic/local part is carried by `sourceTargetAssembly`.  The support part
is kept in its natural compact-support form:

* `hK`, `hsource`, and `homegaSupport` say that the localized manifold form is
  supported in a compact set lying in each selected target chart;
* `coordinateImage_subset_targetBox` says the chosen target boxes contain those
  compact coordinate images;
* `targetBox_subset_target` is the chart-domain side condition needed to replace
  old target boundary scalars by zero-extended target scalars. -/
structure CoverIndexedZeroCompactAssemblyConstructorInput
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n)
    (muBulk : Measure (Fin (n + 1) → Real)) where
  carrierData :
    CoverIndexedCompactSupportCarrierData
      (I := I) (K := K) C P omega
  measure_eq_volume :
    muBulk = (volume : Measure (Fin (n + 1) → Real))
  targetBox :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega
  hK : IsCompact K
  hsource :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      K ⊆ (extChartAt I (targetBox.targetChart i)).source
  homegaSupport : ManifoldForm.support I omega ⊆ K
  coordinateImage_subset_targetBox :
    targetBox.TargetChartCoordinateImageSubsetIccField
  targetBox_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
        (extChartAt I (targetBox.targetChart i)).target
  sourceTargetAssembly :
    CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput
      (I := I) (K := K) C P omega
  globalBoundaryIntegral_eq_integral :
    sourceTargetAssembly.globalBoundaryIntegral =
      ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
        ∂(volume : Measure (Fin n → Real))

namespace CoverIndexedZeroCompactAssemblyConstructorInput

variable
    (D :
      CoverIndexedZeroCompactAssemblyConstructorInput
        (I := I) (K := K) C P omega muBulk)

/-- The zero scalar support field required by the zero-boundary-scalar endpoint,
generated from global compact support and coordinate-image containment. -/
theorem boundaryZeroScalarSupportSubsetImageField :
    D.targetBox.BoundaryZeroScalarSupportSubsetImageField :=
  D.targetBox.boundaryZeroScalarSupportSubsetImageField_of_globalManifoldSupport
    (I := I) (K := K) (C := C) (P := P) (ω := omega)
    D.hK D.hsource D.homegaSupport D.coordinateImage_subset_targetBox

/-- Apply the zero-boundary-scalar represented Stokes endpoint with the compact
support-generated scalar support field. -/
theorem representedStokesZeroBoundaryScalar
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    (D.carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk)
        D.sourceTargetAssembly.neighborhoodData D.measure_eq_volume).globalIntegral =
      D.sourceTargetAssembly.globalBoundaryIntegral := by
  exact
    compactSupportRepresentedStokesZeroBoundaryScalarInfty_of_orientedManifold
      (I := I) (K := K) (C := C) (P := P) (ω := omega)
      (μBulk := muBulk)
      D.carrierData D.sourceTargetAssembly.neighborhoodData D.measure_eq_volume
      D.targetBox D.targetBox_subset_target
      D.boundaryZeroScalarSupportSubsetImageField
      D.sourceTargetAssembly.globalBoundaryIntegral
      D.globalBoundaryIntegral_eq_integral

/-- The compact-support constructor gives both the represented Stokes endpoint
and the source-target zero bulk assembly equality. -/
theorem representedStokes_and_zeroSourceTargetBulkAssembly
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    (D.carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk)
        D.sourceTargetAssembly.neighborhoodData D.measure_eq_volume).globalIntegral =
        D.sourceTargetAssembly.globalBoundaryIntegral ∧
      D.sourceTargetAssembly.transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        D.sourceTargetAssembly.globalBoundaryIntegral := by
  refine ⟨?_, ?_⟩
  · exact
      D.representedStokesZeroBoundaryScalar
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        (muBulk := muBulk)
  · exact
      D.sourceTargetAssembly.zeroBulkSetIntegralSum_eq_globalBoundaryIntegral
        (I := I) (K := K) (C := C) (P := P) (omega := omega)

end CoverIndexedZeroCompactAssemblyConstructorInput

end CoverIndexedZeroCompactAssemblyConstructor

end Stokes

end
