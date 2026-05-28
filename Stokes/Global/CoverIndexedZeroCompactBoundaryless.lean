import Stokes.ManifoldFormChartTransitionOpen
import Stokes.Global.CoverIndexedZeroSourceSupport
import Stokes.Global.CoverIndexedZeroCompactNaturalTheorem

/-!
# Boundaryless compact-support zero endpoint

This file gives the boundaryless specialization of the zero-compact endpoint.
In a boundaryless model, chart-transition sources are ambient-open, and the
source-side zero support field is generated from transition support data.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactBoundaryless

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

/-- Boundaryless natural wrapper for the zero-compact represented Stokes
endpoint.

Compared with `compactSupportRepresentedStokesZeroCompact_of_globalSupport`,
this theorem no longer asks callers to provide the ambient-open
chart-transition source field or the source-side zero support field.  They are
generated respectively by
`CoverIndexedCompactSupportTransitionSupportData.sourceOpenField` and
`CoverIndexedCompactSupportTransitionSupportData.zero_tsupport_subset_source`.
-/
theorem compactSupportRepresentedStokesZeroCompact_of_globalSupport_boundaryless
    [I.Boundaryless]
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
    (sourceNeighborhood :
      CoverIndexedCompactSupportNeighborhoodDataInfty.BoundaryNeighborhoodSubsetTransitionSource
        (I := I) (K := K) neighborhoodData transitionSupportData)
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
      targetBox.TargetChartCoordinateImageSubsetIccField)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real))) :
    (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) neighborhoodData measure_eq_volume).globalIntegral =
        globalBoundaryIntegral ∧
      transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        globalBoundaryIntegral := by
  exact
    compactSupportRepresentedStokesZeroCompact_of_globalSupport
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)
      carrierData neighborhoodData measure_eq_volume transitionSupportData
      sourceNeighborhood
      (transitionSupportData.sourceOpenField
        (I := I) (K := K) (C := C) (P := P) (omega := omega))
      (transitionSupportData.zero_tsupport_subset_source
        (I := I) (K := K) (C := C) (P := P) (omega := omega))
      targetBox targetChart_eq targetBox_subset_target
      hK hsource homegaSupport coordinateImage_subset_targetBox
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral

end CoverIndexedZeroCompactBoundaryless

end Stokes

end
