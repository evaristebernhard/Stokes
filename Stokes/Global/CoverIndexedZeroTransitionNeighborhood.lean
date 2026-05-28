import Stokes.Global.CoverIndexedZeroBulkMeasureConstructor
import Stokes.Global.CoverIndexedBoxNeighborhoodSelection
import Stokes.Global.CoverIndexedCompactSupportCInftyAssembly

/-!
# Boundary transition-source neighborhoods

The zero-extension bulk comparison needs more than the selected boundary source
box lying in a source-to-target chart overlap.  Since Frechet-derivative
equalities are local statements, the whole open smoothness neighborhood around
the selected box must lie in the concrete chart-transition source.

This file isolates the exact missing geometric input.  Existing
`CoverIndexedCompactSupportTransitionSupportData` records only
`sourceBox_subset_overlap`, so we prove what follows from that data and package
the honest extra `boundaryNeighborhood ⊆ overlap` field needed for later
chart-box shrinking.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryTransitionNeighborhood

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {omega : ManifoldForm I M n}

namespace ManifoldForm

/-- A set contained in the source chart target and the source-to-target overlap
is contained in the concrete chart-transition source. -/
theorem subset_chartTransitionSource_of_subset_target_subset_overlap
    {x0 x1 : M} {s : Set (Fin (n + 1) → Real)}
    (htarget : s ⊆ (extChartAt I x0).target)
    (hoverlap : s ⊆ chartOverlap I x0 x1) :
    s ⊆ chartTransitionSource I x0 x1 := by
  intro y hy
  rw [chartTransitionSource_eq]
  exact ⟨htarget hy, hoverlap hy⟩

end ManifoldForm

/-- Open neighborhoods around boundary source boxes which are already shrunk
inside the source chart target and the source-to-target chart overlap.  This is
the geometric package later chart-box selection should produce. -/
structure CoverIndexedBoundaryTransitionBoxNeighborhoods
    (C : CompactSupportChartCoverSelection I K)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M) where
  /-- Per-index open source-side transition neighborhood. -/
  boundaryNeighborhood :
    {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real)
  /-- The chosen neighborhoods are open. -/
  boundary_neighborhood_open :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      IsOpen (boundaryNeighborhood i)
  /-- Each selected closed boundary source box lies in its transition
  neighborhood. -/
  boundary_Icc_subset_neighborhood :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
        boundaryNeighborhood i
  /-- The transition neighborhoods lie in the source boundary chart target. -/
  boundary_neighborhood_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryNeighborhood i ⊆
        (extChartAt I (C.boundaryChart i.1)).target
  /-- The transition neighborhoods lie in the source-to-target chart overlap. -/
  boundary_neighborhood_subset_overlap :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryNeighborhood i ⊆
        ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)

namespace CoverIndexedBoundaryTransitionBoxNeighborhoods

variable {targetChart : {x : M // x ∈ C.boundaryCenters} → M}

/-- Forget the source-to-target overlap field and keep the ordinary boundary
box-neighborhood data used by the self-chart smoothness layer. -/
def toBoundaryBoxNeighborhoods
    (nbrs : CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C targetChart) :
    CoverIndexedBoundaryBoxNeighborhoods (I := I) C where
  neighborhood := nbrs.boundaryNeighborhood
  neighborhood_open := nbrs.boundary_neighborhood_open
  Icc_subset_neighborhood := nbrs.boundary_Icc_subset_neighborhood
  neighborhood_subset_target := nbrs.boundary_neighborhood_subset_target

/-- The packaged transition neighborhoods lie in the concrete chart-transition
source. -/
theorem boundaryNeighborhood_subset_chartTransitionSource
    (nbrs : CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C targetChart)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    nbrs.boundaryNeighborhood i ⊆
      ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (targetChart i) :=
  ManifoldForm.subset_chartTransitionSource_of_subset_target_subset_overlap
    (I := I)
    (x0 := C.boundaryChart i.1) (x1 := targetChart i)
    (nbrs.boundary_neighborhood_subset_target i)
    (nbrs.boundary_neighborhood_subset_overlap i)

end CoverIndexedBoundaryTransitionBoxNeighborhoods

namespace CoverIndexedCompactSupportTransitionSupportData

variable
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodData
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)

/-- The exact missing field for source-to-target boundary derivative
comparisons: the already selected boundary smoothness neighborhoods must be
contained in the source-to-target chart overlap. -/
structure BoundaryNeighborhoodOverlapData where
  boundary_neighborhood_subset_overlap :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      neighborhoodData.boundaryNeighborhood i ⊆
        ManifoldForm.chartOverlap I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)

/-- Whole-neighborhood target and overlap containment give the transition-source
hypothesis consumed by the zero bulk comparison. -/
theorem boundaryNeighborhoodSubsetTransitionSource_of_target_overlap
    (hUtarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (hUoverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          ManifoldForm.chartOverlap I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)) :
    BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (C := C) (neighborhoodData := neighborhoodData)
      transitionSupportData := by
  intro i
  exact
    ManifoldForm.subset_chartTransitionSource_of_subset_target_subset_overlap
      (I := I)
      (x0 := C.boundaryChart i.1)
      (x1 := transitionSupportData.targetChart i)
      (hUtarget i) (hUoverlap i)

/-- Version using the chart-target containment already stored in
`CoverIndexedCompactSupportNeighborhoodData`. -/
theorem boundaryNeighborhoodSubsetTransitionSource_of_overlap
    (hUoverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          ManifoldForm.chartOverlap I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)) :
    BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (C := C) (neighborhoodData := neighborhoodData)
      transitionSupportData :=
  boundaryNeighborhoodSubsetTransitionSource_of_target_overlap
    (I := I) (C := C)
    (neighborhoodData := neighborhoodData)
    (transitionSupportData := transitionSupportData)
    neighborhoodData.boundary_neighborhood_subset_target hUoverlap

/-- The packaged overlap field is exactly enough to construct the
transition-source hypothesis. -/
def BoundaryNeighborhoodOverlapData.toBoundaryNeighborhoodSubsetTransitionSource
    (D : BoundaryNeighborhoodOverlapData
      (I := I) (C := C)
      neighborhoodData transitionSupportData) :
    BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (C := C) (neighborhoodData := neighborhoodData)
      transitionSupportData :=
  boundaryNeighborhoodSubsetTransitionSource_of_overlap
    (I := I) (C := C)
    (neighborhoodData := neighborhoodData)
    (transitionSupportData := transitionSupportData)
    D.boundary_neighborhood_subset_overlap

/-- Existing transition-support data gives overlap on the selected source box.
If a future shrink chooses the whole boundary neighborhood inside that source
box, then the missing overlap field follows automatically. -/
def BoundaryNeighborhoodOverlapData.of_subset_sourceBox
    (hUbox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    BoundaryNeighborhoodOverlapData
      (I := I) (C := C)
      neighborhoodData transitionSupportData where
  boundary_neighborhood_subset_overlap := by
    intro i
    exact (hUbox i).trans (transitionSupportData.sourceBox_subset_overlap i)

/-- Source-box shrink version of
`boundaryNeighborhoodSubsetTransitionSource_of_overlap`. -/
theorem boundaryNeighborhoodSubsetTransitionSource_of_subset_sourceBox
    (hUbox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (C := C) (neighborhoodData := neighborhoodData)
      transitionSupportData :=
  (BoundaryNeighborhoodOverlapData.of_subset_sourceBox
    (I := I) (C := C)
    (neighborhoodData := neighborhoodData)
    (transitionSupportData := transitionSupportData)
    hUbox).toBoundaryNeighborhoodSubsetTransitionSource
      (I := I) (C := C)
      (neighborhoodData := neighborhoodData)
      (transitionSupportData := transitionSupportData)

/-- The strongest conclusion available from the existing records without an
extra shrink hypothesis: the selected closed source box, not the whole open
neighborhood, lies in the concrete transition source. -/
theorem sourceBox_subset_chartTransitionSource_of_existing_fields
    (i : {x : M // x ∈ C.boundaryCenters}) :
    Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
      ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i) :=
  ManifoldForm.subset_chartTransitionSource_of_subset_target_subset_overlap
    (I := I)
    (x0 := C.boundaryChart i.1)
    (x1 := transitionSupportData.targetChart i)
    (by
      intro y hy
      exact (C.boundary_Icc_subset_domain i.1 i.2 hy).1)
    (transitionSupportData.sourceBox_subset_overlap i)

/-- Constructor from an explicitly chosen transition-neighborhood package whose
neighborhoods agree with the already selected smoothness neighborhoods. -/
theorem boundaryNeighborhoodSubsetTransitionSource_of_transitionBoxNeighborhoods
    (nbrs : CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C transitionSupportData.targetChart)
    (hneighborhood :
      neighborhoodData.boundaryNeighborhood = nbrs.boundaryNeighborhood) :
    BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (C := C) (neighborhoodData := neighborhoodData)
      transitionSupportData := by
  intro i y hy
  have hy' : y ∈ nbrs.boundaryNeighborhood i := by
    simpa [hneighborhood] using hy
  exact
    nbrs.boundaryNeighborhood_subset_chartTransitionSource
      (I := I) (K := K) (C := C) i hy'

end CoverIndexedCompactSupportTransitionSupportData

namespace CoverIndexedCompactSupportTransitionSupportData

variable
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)

/-- `C^\infty` analogue of
`BoundaryNeighborhoodSubsetTransitionSource`.  The current bulk-measure theorem
uses the legacy record, but the natural endpoint works with this record. -/
abbrev BoundaryNeighborhoodSubsetTransitionSourceInfty
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega) : Prop :=
  ∀ i : {x : M // x ∈ C.boundaryCenters},
    neighborhoodData.boundaryNeighborhood i ⊆
      ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)

/-- Whole-neighborhood target and overlap containment give the `C^\infty`
transition-source hypothesis. -/
theorem boundaryNeighborhoodSubsetTransitionSourceInfty_of_target_overlap
    (hUtarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (hUoverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          ManifoldForm.chartOverlap I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)) :
    BoundaryNeighborhoodSubsetTransitionSourceInfty
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      neighborhoodData transitionSupportData := by
  intro i
  exact
    ManifoldForm.subset_chartTransitionSource_of_subset_target_subset_overlap
      (I := I)
      (x0 := C.boundaryChart i.1)
      (x1 := transitionSupportData.targetChart i)
      (hUtarget i) (hUoverlap i)

/-- `C^\infty` version using the chart-target containment already stored in the
natural neighborhood record. -/
theorem boundaryNeighborhoodSubsetTransitionSourceInfty_of_overlap
    (hUoverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          ManifoldForm.chartOverlap I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)) :
    BoundaryNeighborhoodSubsetTransitionSourceInfty
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      neighborhoodData transitionSupportData :=
  boundaryNeighborhoodSubsetTransitionSourceInfty_of_target_overlap
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    (transitionSupportData := transitionSupportData)
    neighborhoodData
    neighborhoodData.boundary_neighborhood_subset_target hUoverlap

/-- Source-box shrink version for the natural `C^\infty` record. -/
theorem boundaryNeighborhoodSubsetTransitionSourceInfty_of_subset_sourceBox
    (hUbox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    BoundaryNeighborhoodSubsetTransitionSourceInfty
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      neighborhoodData transitionSupportData :=
  boundaryNeighborhoodSubsetTransitionSourceInfty_of_overlap
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    (transitionSupportData := transitionSupportData)
    neighborhoodData
    (by
      intro i
      exact (hUbox i).trans (transitionSupportData.sourceBox_subset_overlap i))

/-- Constructor from an explicitly chosen transition-neighborhood package for
the natural `C^\infty` neighborhood record. -/
theorem boundaryNeighborhoodSubsetTransitionSourceInfty_of_transitionBoxNeighborhoods
    (nbrs : CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C transitionSupportData.targetChart)
    (hneighborhood :
      neighborhoodData.boundaryNeighborhood = nbrs.boundaryNeighborhood) :
    BoundaryNeighborhoodSubsetTransitionSourceInfty
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      neighborhoodData transitionSupportData := by
  intro i y hy
  have hy' : y ∈ nbrs.boundaryNeighborhood i := by
    simpa [hneighborhood] using hy
  exact
    nbrs.boundaryNeighborhood_subset_chartTransitionSource
      (I := I) (K := K) (C := C) i hy'

end CoverIndexedCompactSupportTransitionSupportData

end BoundaryTransitionNeighborhood

end Stokes

end
