import Stokes.Global.CoverIndexedZeroCompactSourceTransitionSelection

/-!
# Source-shrink selection for compact zero Stokes

This file records the honest source-side shrink geometry needed by the
relative compact-support route.

The key point is that the already selected source box cannot also serve as an
open neighborhood contained in itself: downstream local data stores
`Icc lower upper ⊆ U`, so asking for `U ⊆ Icc lower upper` is generally too
strong.  The useful geometric datum is instead an outer source box:

`selected closed box ⊆ U ⊆ outer source box ⊆ chart overlap`.

From that datum we can construct the transition-neighborhood package consumed
by the current compact zero endpoint.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactSourceShrinkSelection

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryBoxNeighborhoods

/-- Build ordinary boundary-box neighborhoods from a per-index
`ChartBoxOpenNeighborhood` whose target is the intersection of an outer source
box and the source chart target.

Mathematically this is the strict-shrink shape:
`Icc C.boundaryLower C.boundaryUpper ⊆ U ⊆ Icc sourceLower sourceUpper`,
with chart-target containment carried at the same time. -/
def ofSourceBoxChartBoxOpenNeighborhoods
    (sourceLower sourceUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          (Icc (sourceLower i) (sourceUpper i) ∩
            (extChartAt I (C.boundaryChart i.1)).target)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedBoundaryBoxNeighborhoods (I := I) C where
  neighborhood := fun i => (nbr i).neighborhood
  neighborhood_open := fun i => (nbr i).isOpen_neighborhood
  Icc_subset_neighborhood := fun i => (nbr i).Icc_subset_neighborhood
  neighborhood_subset_target := by
    intro i y hy
    exact ((nbr i).neighborhood_subset_target hy).2

@[simp]
theorem ofSourceBoxChartBoxOpenNeighborhoods_neighborhood
    (sourceLower sourceUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          (Icc (sourceLower i) (sourceUpper i) ∩
            (extChartAt I (C.boundaryChart i.1)).target)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    (ofSourceBoxChartBoxOpenNeighborhoods
      (I := I) (K := K) (C := C)
      sourceLower sourceUpper nbr).neighborhood =
        fun i => (nbr i).neighborhood :=
  rfl

/-- The neighborhoods produced from source-box `ChartBoxOpenNeighborhood`s are
contained in the corresponding outer source boxes. -/
theorem ofSourceBoxChartBoxOpenNeighborhoods_subset_sourceBox
    (sourceLower sourceUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          (Icc (sourceLower i) (sourceUpper i) ∩
            (extChartAt I (C.boundaryChart i.1)).target)
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    (ofSourceBoxChartBoxOpenNeighborhoods
      (I := I) (K := K) (C := C)
      sourceLower sourceUpper nbr).neighborhood i ⊆
        Icc (sourceLower i) (sourceUpper i) := by
  intro y hy
  exact ((nbr i).neighborhood_subset_target hy).1

end CoverIndexedBoundaryBoxNeighborhoods

namespace CoverIndexedBoundaryTransitionBoxNeighborhoods

/-- Upgrade boundary-box neighborhoods to transition neighborhoods using an
outer source box.  This is the correct shrink form:
`neighborhood ⊆ outer source box`, not `neighborhood ⊆ selected box`. -/
def ofBoundaryBoxNeighborhoodsAndOuterSourceBox
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceLower sourceUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (nbrs : CoverIndexedBoundaryBoxNeighborhoods (I := I) C)
    (boundary_neighborhood_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        nbrs.neighborhood i ⊆ Icc (sourceLower i) (sourceUpper i))
    (sourceBox_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (sourceLower i) (sourceUpper i) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C targetChart where
  boundaryNeighborhood := nbrs.neighborhood
  boundary_neighborhood_open := nbrs.neighborhood_open
  boundary_Icc_subset_neighborhood := nbrs.Icc_subset_neighborhood
  boundary_neighborhood_subset_target := nbrs.neighborhood_subset_target
  boundary_neighborhood_subset_overlap := by
    intro i
    exact
      (boundary_neighborhood_subset_sourceBox i).trans
        (sourceBox_subset_overlap i)

@[simp]
theorem ofBoundaryBoxNeighborhoodsAndOuterSourceBox_boundaryNeighborhood
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceLower sourceUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (nbrs : CoverIndexedBoundaryBoxNeighborhoods (I := I) C)
    (boundary_neighborhood_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        nbrs.neighborhood i ⊆ Icc (sourceLower i) (sourceUpper i))
    (sourceBox_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (sourceLower i) (sourceUpper i) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    (ofBoundaryBoxNeighborhoodsAndOuterSourceBox
      (I := I) (K := K) (C := C)
      targetChart sourceLower sourceUpper nbrs
      boundary_neighborhood_subset_sourceBox
      sourceBox_subset_overlap).boundaryNeighborhood =
        nbrs.neighborhood :=
  rfl

/-- Direct transition-neighborhood constructor from per-index
`ChartBoxOpenNeighborhood`s inside outer source boxes. -/
def ofSourceBoxChartBoxOpenNeighborhoods
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceLower sourceUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          (Icc (sourceLower i) (sourceUpper i) ∩
            (extChartAt I (C.boundaryChart i.1)).target)
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (sourceBox_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (sourceLower i) (sourceUpper i) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C targetChart :=
  ofBoundaryBoxNeighborhoodsAndOuterSourceBox
    (I := I) (K := K) (C := C)
    targetChart sourceLower sourceUpper
    (CoverIndexedBoundaryBoxNeighborhoods.ofSourceBoxChartBoxOpenNeighborhoods
      (I := I) (K := K) (C := C) sourceLower sourceUpper nbr)
    (CoverIndexedBoundaryBoxNeighborhoods.ofSourceBoxChartBoxOpenNeighborhoods_subset_sourceBox
      (I := I) (K := K) (C := C) sourceLower sourceUpper nbr)
    sourceBox_subset_overlap

@[simp]
theorem ofSourceBoxChartBoxOpenNeighborhoods_boundaryNeighborhood
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceLower sourceUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          (Icc (sourceLower i) (sourceUpper i) ∩
            (extChartAt I (C.boundaryChart i.1)).target)
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (sourceBox_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (sourceLower i) (sourceUpper i) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    (ofSourceBoxChartBoxOpenNeighborhoods
      (I := I) (K := K) (C := C)
      targetChart sourceLower sourceUpper nbr
      sourceBox_subset_overlap).boundaryNeighborhood =
        fun i => (nbr i).neighborhood :=
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

/-- Turn the natural `C^\infty` neighborhood record into transition
neighborhoods using an outer source box that contains the chosen neighborhoods
and is contained in the chart overlap. -/
def toBoundaryTransitionBoxNeighborhoodsOfOuterSourceBox
    (sourceLower sourceUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (boundaryNeighborhood_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          Icc (sourceLower i) (sourceUpper i))
    (sourceBox_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (sourceLower i) (sourceUpper i) ⊆
          ManifoldForm.chartOverlap I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)) :
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
        (sourceBox_subset_overlap i)

@[simp]
theorem toBoundaryTransitionBoxNeighborhoodsOfOuterSourceBox_boundaryNeighborhood
    (sourceLower sourceUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (boundaryNeighborhood_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          Icc (sourceLower i) (sourceUpper i))
    (sourceBox_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (sourceLower i) (sourceUpper i) ⊆
          ManifoldForm.chartOverlap I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)) :
    (neighborhoodData.toBoundaryTransitionBoxNeighborhoodsOfOuterSourceBox
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData sourceLower sourceUpper
      boundaryNeighborhood_subset_sourceBox
      sourceBox_subset_overlap).boundaryNeighborhood =
        neighborhoodData.boundaryNeighborhood :=
  rfl

/-- Outer-source-box shrink version of the transition-source field used by the
relative compact zero assembly. -/
theorem boundaryNeighborhoodSubsetTransitionSource_of_outerSourceBox
    (sourceLower sourceUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (boundaryNeighborhood_subset_sourceBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          Icc (sourceLower i) (sourceUpper i))
    (sourceBox_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (sourceLower i) (sourceUpper i) ⊆
          ManifoldForm.chartOverlap I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)) :
    BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (K := K) neighborhoodData transitionSupportData :=
  neighborhoodData.boundaryNeighborhoodSubsetTransitionSource_of_transitionBoxNeighborhoods
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    transitionSupportData
    (neighborhoodData.toBoundaryTransitionBoxNeighborhoodsOfOuterSourceBox
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData sourceLower sourceUpper
      boundaryNeighborhood_subset_sourceBox
      sourceBox_subset_overlap)
    rfl

end CoverIndexedCompactSupportNeighborhoodDataInfty

end CoverIndexedZeroCompactSourceShrinkSelection

end Stokes

end
