import Stokes.ManifoldFormZeroTransitionSupport
import Stokes.Global.CoverIndexedZeroTransitionSourceConstructors

/-!
# Cover-indexed source-side support for zero transitions

This file fills the source-side support field used by the zero source-target
assembly bridge.  The point is small but important: zero extension cannot
enlarge topological support, so the already available source-to-target
localized support bound for the ordinary transition representative immediately
gives the corresponding bound for the zero-extended representative.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroSourceSupport

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedCompactSupportTransitionSupportData

variable
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)

/-- The ordinary localized source-to-target transition representative is
supported in the selected source half-space box. -/
theorem localized_tsupport_subset_source_halfSpaceSupportBox
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
      halfSpaceSupportBox
        (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  P.boundary_sourceTarget_tsupport_subset_halfSpaceSupportBox_of_coordSupport
    (ω := omega)
    transitionSupportData.targetChart
    transitionSupportData.transitionCoordSupport
    transitionSupportData.base_tsupport_subset_transitionCoordSupport
    transitionSupportData.coeff_tsupport_inter_subset_halfSpaceBox
    i

/-- Zero-extension version of
`localized_tsupport_subset_source_halfSpaceSupportBox`.  This is exactly the
`zero_tsupport_subset_source` field required by
`CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput`. -/
theorem zero_tsupport_subset_source_halfSpaceSupportBox
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (ManifoldForm.transitionPullbackInChartZero I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
      halfSpaceSupportBox
        (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  ManifoldForm.transitionPullbackInChartZero_tsupport_subset_of_transition_tsupport_subset
    (I := I)
    (x0 := C.boundaryChart i.1)
    (x1 := transitionSupportData.targetChart i)
    (ω := P.coverIndexLocalizedForm omega (Sum.inr i))
    (transitionSupportData.localized_tsupport_subset_source_halfSpaceSupportBox
      (I := I) (K := K) (C := C) (P := P) (omega := omega) i)

/-- Field-level spelling of
`zero_tsupport_subset_source_halfSpaceSupportBox`, ready to pass into the zero
source-target assembly constructors. -/
theorem zero_tsupport_subset_source :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      tsupport
          (ManifoldForm.transitionPullbackInChartZero I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
        halfSpaceSupportBox
          (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  fun i =>
    transitionSupportData.zero_tsupport_subset_source_halfSpaceSupportBox
      (I := I) (K := K) (C := C) (P := P) (omega := omega) i

end CoverIndexedCompactSupportTransitionSupportData

namespace CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput

/-- Source-neighborhood constructor with the zero support field derived
directly from `CoverIndexedCompactSupportTransitionSupportData`. -/
def ofSourceNeighborhoodAndTransitionSupport
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (sourceNeighborhood :
      CoverIndexedCompactSupportNeighborhoodDataInfty.BoundaryNeighborhoodSubsetTransitionSource
        (I := I) (K := K) neighborhoodData transitionSupportData)
    (sourceOpen :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen
          (ManifoldForm.chartTransitionSource I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)))
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_sourceTargetBoundarySum :
      globalBoundaryIntegral =
        Finset.sum C.boundaryCoverIndexFinset fun i =>
          projectLocalBoundaryIntegral I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput
      (I := I) (K := K) C P omega :=
  ofSourceNeighborhood
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    neighborhoodData transitionSupportData
    sourceNeighborhood sourceOpen
    (transitionSupportData.zero_tsupport_subset_source
      (I := I) (K := K) (C := C) (P := P) (omega := omega))
    globalBoundaryIntegral globalBoundaryIntegral_eq_sourceTargetBoundarySum

/-- Transition-neighborhood constructor with source-side zero support derived
from transition support data. -/
def ofTransitionBoxNeighborhoodsAndTransitionSupport
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
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
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_sourceTargetBoundarySum :
      globalBoundaryIntegral =
        Finset.sum C.boundaryCoverIndexFinset fun i =>
          projectLocalBoundaryIntegral I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput
      (I := I) (K := K) C P omega :=
  ofTransitionBoxNeighborhoods
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    neighborhoodData transitionSupportData nbrs hneighborhood sourceOpen
    (transitionSupportData.zero_tsupport_subset_source
      (I := I) (K := K) (C := C) (P := P) (omega := omega))
    globalBoundaryIntegral globalBoundaryIntegral_eq_sourceTargetBoundarySum

/-- Raw boundary-neighborhood overlap constructor with source-side zero support
derived from transition support data. -/
def ofBoundaryNeighborhoodOverlapAndTransitionSupport
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (hUoverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          ManifoldForm.chartOverlap I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i))
    (sourceOpen :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen
          (ManifoldForm.chartTransitionSource I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)))
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_sourceTargetBoundarySum :
      globalBoundaryIntegral =
        Finset.sum C.boundaryCoverIndexFinset fun i =>
          projectLocalBoundaryIntegral I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput
      (I := I) (K := K) C P omega :=
  ofBoundaryNeighborhoodOverlap
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    neighborhoodData transitionSupportData hUoverlap sourceOpen
    (transitionSupportData.zero_tsupport_subset_source
      (I := I) (K := K) (C := C) (P := P) (omega := omega))
    globalBoundaryIntegral globalBoundaryIntegral_eq_sourceTargetBoundarySum

end CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput

end CoverIndexedZeroSourceSupport

end Stokes

end
