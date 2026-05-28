import Stokes.Global.CoverIndexedZeroNeighborhoodShrink
import Stokes.Global.CoverIndexedZeroRelativeSource

/-!
# Relative-source assembly inputs from natural source neighborhoods

This file is the relative-source analogue of the source-neighborhood wrappers
used by the older zero compact endpoint.  Its constructors build
`CoverIndexedZeroBoundaryRelativeSourceAssemblyInput` from natural neighborhood
selection data, deriving the source-neighborhood field and the zero source
support field without asking for ambient openness of the chart-transition
source.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroRelativeSourceNeighborhoodWrappers

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedZeroBoundaryRelativeSourceAssemblyInput

/-- Build the relative zero source-target assembly input from a packaged
transition-neighborhood selection.

This is the direct replacement for the old transition-neighborhood constructor
that required an ambient `sourceOpen` field.  The source-neighborhood
containment is generated from `nbrs`, while zero source support and the
relative source-neighborhood field are generated from `transitionSupportData`.
-/
def ofTransitionBoxNeighborhoodsAndBoundarySum
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
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_sourceTargetBoundarySum :
      globalBoundaryIntegral =
        Finset.sum C.boundaryCoverIndexFinset fun i =>
          projectLocalBoundaryIntegral I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedZeroBoundaryRelativeSourceAssemblyInput
      (I := I) (K := K) C P omega :=
  ofSourceNeighborhoodAndTransitionSupport
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    neighborhoodData transitionSupportData
    (CoverIndexedCompactSupportNeighborhoodDataInfty.boundaryNeighborhoodSubsetTransitionSource_of_transitionBoxNeighborhoods
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      neighborhoodData transitionSupportData nbrs hneighborhood)
    globalBoundaryIntegral globalBoundaryIntegral_eq_sourceTargetBoundarySum

/-- Build the relative zero source-target assembly input from the geometric
source-box shrink condition on the selected boundary neighborhoods.

The hypothesis says exactly that each open smoothness neighborhood has been
shrunk into the source half-space box already controlled by
`transitionSupportData`.  This produces the transition-source containment
needed by the relative assembly input, and no ambient openness assumption is
needed.
-/
def ofBoundaryNeighborhood_subset_sourceBox_andBoundarySum
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (boundaryNeighborhood_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_sourceTargetBoundarySum :
      globalBoundaryIntegral =
        Finset.sum C.boundaryCoverIndexFinset fun i =>
          projectLocalBoundaryIntegral I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedZeroBoundaryRelativeSourceAssemblyInput
      (I := I) (K := K) C P omega :=
  ofSourceNeighborhoodAndTransitionSupport
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    neighborhoodData transitionSupportData
    (CoverIndexedCompactSupportNeighborhoodDataInfty.boundaryNeighborhoodSubsetTransitionSource_of_neighborhood_subset_sourceBox
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      neighborhoodData transitionSupportData boundaryNeighborhood_subset_sourceBox)
    globalBoundaryIntegral globalBoundaryIntegral_eq_sourceTargetBoundarySum

/-- Boundary-box neighborhood version of
`ofBoundaryNeighborhood_subset_sourceBox_andBoundarySum`.

This is useful immediately after chart-box selection has produced an auxiliary
`CoverIndexedBoundaryBoxNeighborhoods` package whose neighborhoods agree with
the smoothness neighborhoods stored in `neighborhoodData`.
-/
def ofBoundaryBoxNeighborhoodsAndBoundarySum
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (nbrs : CoverIndexedBoundaryBoxNeighborhoods (I := I) C)
    (hneighborhood :
      neighborhoodData.boundaryNeighborhood = nbrs.neighborhood)
    (hnbrs_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        nbrs.neighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_sourceTargetBoundarySum :
      globalBoundaryIntegral =
        Finset.sum C.boundaryCoverIndexFinset fun i =>
          projectLocalBoundaryIntegral I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedZeroBoundaryRelativeSourceAssemblyInput
      (I := I) (K := K) C P omega :=
  ofSourceNeighborhoodAndTransitionSupport
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    neighborhoodData transitionSupportData
    (CoverIndexedCompactSupportNeighborhoodDataInfty.boundaryNeighborhoodSubsetTransitionSource_of_boundaryBoxNeighborhoods
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      neighborhoodData transitionSupportData nbrs hneighborhood hnbrs_subset_sourceBox)
    globalBoundaryIntegral globalBoundaryIntegral_eq_sourceTargetBoundarySum

end CoverIndexedZeroBoundaryRelativeSourceAssemblyInput

end CoverIndexedZeroRelativeSourceNeighborhoodWrappers

end Stokes

end
