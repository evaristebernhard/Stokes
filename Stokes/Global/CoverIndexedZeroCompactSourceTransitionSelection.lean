import Stokes.Global.CoverIndexedCompactSupportBoxDataAssembly
import Stokes.Global.CoverIndexedZeroCompactRelativeSourceNeighborhood

/-!
# Source-side transition-neighborhood selection

This file is the chart-box selection bridge for the source side of the
relative zero compact-support route.

The geometric input one really wants from chart-box selection is an open
boundary neighborhood contained in the source-to-target chart overlap.  Existing
compact-support transition data only knows that the selected closed source box
lies in the overlap.  Therefore the useful shrink hypothesis is that the chosen
open boundary neighborhood has already been selected inside that source box.
Under that honest shrink, the transition-neighborhood package is automatic.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactSourceTransitionSelection

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryTransitionBoxNeighborhoods

/-- Upgrade ordinary boundary box-neighborhood data to transition-neighborhood
data once the whole selected neighborhood is known to lie in the
source-to-target chart overlap. -/
def ofBoundaryBoxNeighborhoodsAndOverlap
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (nbrs : CoverIndexedBoundaryBoxNeighborhoods (I := I) C)
    (boundary_neighborhood_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        nbrs.neighborhood i ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C targetChart where
  boundaryNeighborhood := nbrs.neighborhood
  boundary_neighborhood_open := nbrs.neighborhood_open
  boundary_Icc_subset_neighborhood := nbrs.Icc_subset_neighborhood
  boundary_neighborhood_subset_target := nbrs.neighborhood_subset_target
  boundary_neighborhood_subset_overlap :=
    boundary_neighborhood_subset_overlap

@[simp]
theorem ofBoundaryBoxNeighborhoodsAndOverlap_boundaryNeighborhood
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (nbrs : CoverIndexedBoundaryBoxNeighborhoods (I := I) C)
    (boundary_neighborhood_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        nbrs.neighborhood i ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    (ofBoundaryBoxNeighborhoodsAndOverlap
      (I := I) (K := K) (C := C)
      targetChart nbrs boundary_neighborhood_subset_overlap).boundaryNeighborhood =
        nbrs.neighborhood :=
  rfl

/-- If the chosen boundary neighborhoods have been shrunk inside the selected
source boxes, existing transition-support data upgrades them to
source-to-target transition neighborhoods. -/
def ofBoundaryBoxNeighborhoodsAndSourceBox
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (nbrs : CoverIndexedBoundaryBoxNeighborhoods (I := I) C)
    (boundary_neighborhood_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        nbrs.neighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C transitionSupportData.targetChart :=
  ofBoundaryBoxNeighborhoodsAndOverlap
    (I := I) (K := K) (C := C)
    transitionSupportData.targetChart nbrs
    (by
      intro i
      exact
        (boundary_neighborhood_subset_sourceBox i).trans
          (transitionSupportData.sourceBox_subset_overlap i))

@[simp]
theorem ofBoundaryBoxNeighborhoodsAndSourceBox_boundaryNeighborhood
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (nbrs : CoverIndexedBoundaryBoxNeighborhoods (I := I) C)
    (boundary_neighborhood_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        nbrs.neighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    (ofBoundaryBoxNeighborhoodsAndSourceBox
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData nbrs boundary_neighborhood_subset_sourceBox).boundaryNeighborhood =
        nbrs.neighborhood :=
  rfl

end CoverIndexedBoundaryTransitionBoxNeighborhoods

namespace CoverIndexedCompactSupportNeighborhoodDataInfty

variable
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)

/-- Turn the natural `C^\infty` neighborhood record itself into transition-box
neighborhoods, assuming the selected boundary neighborhoods have been shrunk
inside the selected source boxes.  This constructor gives downstream wrappers
`hneighborhood = rfl`. -/
def toBoundaryTransitionBoxNeighborhoodsOfSourceBox
    (boundaryNeighborhood_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C transitionSupportData.targetChart where
  boundaryNeighborhood := neighborhoodData.boundaryNeighborhood
  boundary_neighborhood_open := neighborhoodData.boundary_neighborhood_open
  boundary_Icc_subset_neighborhood :=
    neighborhoodData.boundary_Icc_subset_neighborhood
  boundary_neighborhood_subset_target :=
    neighborhoodData.boundary_neighborhood_subset_target
  boundary_neighborhood_subset_overlap := by
    intro i
    exact
      (boundaryNeighborhood_subset_sourceBox i).trans
        (transitionSupportData.sourceBox_subset_overlap i)

@[simp]
theorem toBoundaryTransitionBoxNeighborhoodsOfSourceBox_boundaryNeighborhood
    (boundaryNeighborhood_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    (neighborhoodData.toBoundaryTransitionBoxNeighborhoodsOfSourceBox
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData boundaryNeighborhood_subset_sourceBox).boundaryNeighborhood =
        neighborhoodData.boundaryNeighborhood :=
  rfl

/-- The transition-neighborhood constructor above immediately supplies the
source-neighborhood field used by the relative zero assembly. -/
theorem boundaryNeighborhoodSubsetTransitionSource_of_sourceBoxTransitionSelection
    (boundaryNeighborhood_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (K := K) neighborhoodData transitionSupportData := by
  exact
    neighborhoodData.boundaryNeighborhoodSubsetTransitionSource_of_transitionBoxNeighborhoods
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData
      (neighborhoodData.toBoundaryTransitionBoxNeighborhoodsOfSourceBox
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData boundaryNeighborhood_subset_sourceBox)
      rfl

end CoverIndexedCompactSupportNeighborhoodDataInfty

namespace CoverIndexedCompactSupportBoxDataAssembly

variable
    (D :
      CoverIndexedCompactSupportBoxDataAssembly
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)

/-- Source-side transition neighborhoods generated from a compact chart-box
assembly whose boundary neighborhoods have been shrunk into the selected source
boxes. -/
def boundaryTransitionBoxNeighborhoodsOfSourceBox
    (boundaryNeighborhood_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        D.boundaryNeighborhoods.neighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C transitionSupportData.targetChart :=
  CoverIndexedBoundaryTransitionBoxNeighborhoods.ofBoundaryBoxNeighborhoodsAndSourceBox
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    transitionSupportData D.boundaryNeighborhoods
    boundaryNeighborhood_subset_sourceBox

@[simp]
theorem boundaryTransitionBoxNeighborhoodsOfSourceBox_boundaryNeighborhood
    (boundaryNeighborhood_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        D.boundaryNeighborhoods.neighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    (D.boundaryTransitionBoxNeighborhoodsOfSourceBox
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData boundaryNeighborhood_subset_sourceBox).boundaryNeighborhood =
        D.boundaryNeighborhoods.neighborhood :=
  rfl

/-- Compatibility field for feeding
`boundaryTransitionBoxNeighborhoodsOfSourceBox` into theorem wrappers built from
`D.neighborhoodData`. -/
theorem neighborhoodData_boundaryNeighborhood_eq_boundaryTransitionBoxNeighborhoodsOfSourceBox
    (boundaryNeighborhood_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        D.boundaryNeighborhoods.neighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    D.neighborhoodData.boundaryNeighborhood =
      (D.boundaryTransitionBoxNeighborhoodsOfSourceBox
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData boundaryNeighborhood_subset_sourceBox).boundaryNeighborhood :=
  rfl

end CoverIndexedCompactSupportBoxDataAssembly

end CoverIndexedZeroCompactSourceTransitionSelection

end Stokes

end
