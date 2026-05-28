import Stokes.Global.CoverIndexedZeroTransitionSourceConstructors
import Stokes.Global.CoverIndexedBoxNeighborhoodSelection

/-!
# Neighborhood shrink constructors for zero boundary assembly

This file records the direct shrink lemmas used by the zero-extension boundary
assembly.  The key point is deliberately modest: existing transition-support
data controls the selected closed source box, so a later chart-box shrink only
has to prove that the chosen open smoothness neighborhood lies inside that
closed source box.  Then the whole neighborhood lies in the source-to-target
overlap, hence in the concrete chart-transition source.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroNeighborhoodShrink

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedCompactSupportNeighborhoodDataInfty

variable
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)

/-- If every selected boundary smoothness neighborhood has been shrunk inside
the selected source box, then the whole neighborhood lies in the source-to-target
chart overlap. -/
theorem boundaryNeighborhoodOverlap_of_neighborhood_subset_sourceBox
    (hUbox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      neighborhoodData.boundaryNeighborhood i ⊆
        ManifoldForm.chartOverlap I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i) := by
  intro i
  exact (hUbox i).trans (transitionSupportData.sourceBox_subset_overlap i)

/-- Source-box shrink version with a name matching the natural shrink
hypothesis. -/
theorem boundaryNeighborhoodSubsetTransitionSource_of_neighborhood_subset_sourceBox
    (hUbox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (K := K) neighborhoodData transitionSupportData :=
  boundaryNeighborhoodSubsetTransitionSource_of_overlap
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    neighborhoodData transitionSupportData
    (boundaryNeighborhoodOverlap_of_neighborhood_subset_sourceBox
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      neighborhoodData transitionSupportData hUbox)

/-- A packaged boundary-box neighborhood whose underlying neighborhoods are
also contained in the selected source boxes gives the needed overlap field for
the natural `C^\infty` neighborhood record. -/
theorem boundaryNeighborhoodOverlap_of_boundaryBoxNeighborhoods
    (nbrs : CoverIndexedBoundaryBoxNeighborhoods (I := I) C)
    (hneighborhood :
      neighborhoodData.boundaryNeighborhood = nbrs.neighborhood)
    (hnbrs_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        nbrs.neighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      neighborhoodData.boundaryNeighborhood i ⊆
        ManifoldForm.chartOverlap I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i) := by
  refine boundaryNeighborhoodOverlap_of_neighborhood_subset_sourceBox
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    neighborhoodData transitionSupportData ?_
  intro i y hy
  exact hnbrs_subset_sourceBox i (by simpa [hneighborhood] using hy)

/-- Boundary-box neighborhood shrink constructor for the exact transition-source
field consumed by the zero assembly bridge. -/
theorem boundaryNeighborhoodSubsetTransitionSource_of_boundaryBoxNeighborhoods
    (nbrs : CoverIndexedBoundaryBoxNeighborhoods (I := I) C)
    (hneighborhood :
      neighborhoodData.boundaryNeighborhood = nbrs.neighborhood)
    (hnbrs_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        nbrs.neighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (K := K) neighborhoodData transitionSupportData :=
  boundaryNeighborhoodSubsetTransitionSource_of_overlap
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    neighborhoodData transitionSupportData
    (boundaryNeighborhoodOverlap_of_boundaryBoxNeighborhoods
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      neighborhoodData transitionSupportData
      nbrs hneighborhood hnbrs_subset_sourceBox)

/-- Transition-neighborhood packages directly contain the needed overlap field;
this lemma exposes it without immediately constructing the stronger
transition-source field. -/
theorem boundaryNeighborhoodOverlap_of_transitionBoxNeighborhoods
    (nbrs : CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C transitionSupportData.targetChart)
    (hneighborhood :
      neighborhoodData.boundaryNeighborhood = nbrs.boundaryNeighborhood) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      neighborhoodData.boundaryNeighborhood i ⊆
        ManifoldForm.chartOverlap I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i) := by
  intro i y hy
  have hy' : y ∈ nbrs.boundaryNeighborhood i := by
    simpa [hneighborhood] using hy
  exact nbrs.boundary_neighborhood_subset_overlap i hy'

end CoverIndexedCompactSupportNeighborhoodDataInfty

end CoverIndexedZeroNeighborhoodShrink

end Stokes

end
