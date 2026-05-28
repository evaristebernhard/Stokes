import Stokes.Global.CoverIndexedZeroCompactNaturalTheorem
import Stokes.Global.CoverIndexedZeroSourceSupport

/-!
# Compact-support zero endpoint from transition neighborhoods

This file is a theorem-facing wrapper for the zero-compact endpoint.  It
replaces the two source-side inputs

* `sourceNeighborhood`, and
* `zero_tsupport_subset_source`,

by the natural transition-neighborhood package produced by chart-box
selection.  The ambient `sourceOpen` hypothesis is intentionally still
explicit: for manifolds with boundary the concrete transition source is only a
relative neighborhood in general.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactTransitionNeighborhood

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

/-- Compact-support represented Stokes for the zero-extension route, with the
source-side transition-neighborhood and zero-support fields generated from
transition box neighborhoods.

This is the natural endpoint once chart-box selection has produced open
neighborhoods inside the relevant source-to-target chart-transition sources.
The explicit `sourceOpen` hypothesis is kept, since for manifolds with
boundary it should eventually be replaced by a relative-neighborhood version
rather than silently assumed. -/
theorem compactSupportRepresentedStokesZeroCompact_of_transitionBoxNeighborhoods
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
    (sourceOpen :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen
          (ManifoldForm.chartTransitionSource I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)))
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
      (CoverIndexedCompactSupportNeighborhoodDataInfty.boundaryNeighborhoodSubsetTransitionSource_of_transitionBoxNeighborhoods
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        neighborhoodData transitionSupportData nbrs hneighborhood)
      sourceOpen
      (transitionSupportData.zero_tsupport_subset_source
        (I := I) (K := K) (C := C) (P := P) (omega := omega))
      targetBox targetChart_eq targetBox_subset_target hK hsource
      homegaSupport coordinateImage_subset_targetBox
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral

end CoverIndexedZeroCompactTransitionNeighborhood

end Stokes

end
