import Stokes.Global.CoverIndexedZeroBoundaryScalarIntegral
import Stokes.Global.CoverIndexedZeroRelativeSource
import Stokes.Global.CoverIndexedZeroTargetBoxFromCompact

/-!
# Compact-support constructors for relative-source zero assembly

This file is the compact-support constructor layer for the zero-boundary-scalar
route using the boundary-compatible relative-source assembly input.

Compared with `CoverIndexedZeroCompactAssemblyConstructorInput`, the local
source-target assembly package is
`CoverIndexedZeroBoundaryRelativeSourceAssemblyInput`, so the endpoint does not
carry the false-in-boundary ambient openness hypothesis
`IsOpen (ManifoldForm.chartTransitionSource ...)`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactRelativeAssemblyConstructor

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

/-- Compact-support input for the zero-boundary-scalar endpoint using the
relative-source source-target assembly route.

The scalar support side is generated from compact support and target coordinate
image containment, while the zero bulk boundary reconstruction is supplied by
`sourceTargetAssembly` without requiring ambient openness of the chart
transition source. -/
structure CoverIndexedZeroCompactRelativeAssemblyConstructorInput
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
    CoverIndexedZeroBoundaryRelativeSourceAssemblyInput
      (I := I) (K := K) C P omega
  globalBoundaryIntegral_eq_integral :
    sourceTargetAssembly.globalBoundaryIntegral =
      ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
        ∂(volume : Measure (Fin n → Real))

namespace CoverIndexedZeroCompactRelativeAssemblyConstructorInput

variable
    (D :
      CoverIndexedZeroCompactRelativeAssemblyConstructorInput
        (I := I) (K := K) C P omega muBulk)

/-- The zero scalar support field required by the zero-boundary-scalar endpoint,
generated from global compact support and coordinate-image containment. -/
theorem boundaryZeroScalarSupportSubsetImageField :
    D.targetBox.BoundaryZeroScalarSupportSubsetImageField :=
  D.targetBox.boundaryZeroScalarSupportSubsetImageField_of_globalManifoldSupport
    (I := I) (K := K) (C := C) (P := P) (ω := omega)
    D.hK D.hsource D.homegaSupport D.coordinateImage_subset_targetBox

/-- Apply the zero-boundary-scalar represented Stokes endpoint with the compact
support-generated scalar support field.  This theorem uses only the
`neighborhoodData` inside the relative-source assembly package; no ambient
openness of chart-transition sources is required. -/
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

/-- The compact-support relative-source constructor gives both the represented
Stokes endpoint and the source-target zero bulk assembly equality. -/
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

end CoverIndexedZeroCompactRelativeAssemblyConstructorInput

end CoverIndexedZeroCompactRelativeAssemblyConstructor

end Stokes

end
