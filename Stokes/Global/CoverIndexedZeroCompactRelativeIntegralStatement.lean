import Stokes.Global.CoverIndexedZeroCompactRelativeNaturalTheorem

/-!
# Integral-valued relative compact-support zero endpoint

This file gives the theorem-facing relative-source compact-support zero
endpoint whose boundary scalar is the actual target boundary integral.

It is a thin wrapper around
`compactSupportRepresentedStokesZeroCompact_of_globalSupport_relative`: the
auxiliary name `globalBoundaryIntegral` is instantiated by the integral itself,
so callers no longer provide that scalar or the reflexive equality identifying
it.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactRelativeIntegralStatement

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

/-- Compact-support represented Stokes for the relative-source zero route,
stated directly against the target boundary integral.

Compared with
`compactSupportRepresentedStokesZeroCompact_of_globalSupport_relative`, this
version removes the artificial scalar `globalBoundaryIntegral : Real` and its
equality with the boundary integral.  The remaining hypotheses are the current
relative-source compact-support data: carrier data, selected neighborhoods,
transition support, target box, and compact support containment. -/
theorem compactSupportRepresentedStokesZeroCompact_relative_eq_integral_of_globalSupport
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
      targetBox.TargetChartCoordinateImageSubsetIccField) :
    (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) neighborhoodData measure_eq_volume).globalIntegral =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real)) ∧
      transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real)) := by
  exact
    compactSupportRepresentedStokesZeroCompact_of_globalSupport_relative
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)
      carrierData neighborhoodData measure_eq_volume transitionSupportData
      sourceNeighborhood targetBox targetChart_eq targetBox_subset_target
      hK hsource homegaSupport coordinateImage_subset_targetBox
      (∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
        ∂(volume : Measure (Fin n → Real)))
      rfl

end CoverIndexedZeroCompactRelativeIntegralStatement

end Stokes

end
