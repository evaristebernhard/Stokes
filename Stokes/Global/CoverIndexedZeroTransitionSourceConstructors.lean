import Stokes.Global.CoverIndexedZeroAssemblyBridge
import Stokes.Global.CoverIndexedZeroTransitionNeighborhood

/-!
# Transition-source constructors for the zero assembly bridge

This file is a thin constructor layer.  The geometric work is already in
`CoverIndexedZeroTransitionNeighborhood`: a boundary source box has to be
shrunk with an open neighborhood contained in the concrete source-to-target
chart-transition source.  Here we turn that package into the exact field used
by `CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroTransitionSourceConstructors

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

/-- Whole-neighborhood chart-target and overlap containment give the exact
transition-source field consumed by the zero assembly bridge. -/
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
      (I := I) (K := K) neighborhoodData transitionSupportData := by
  intro i
  exact
    ManifoldForm.subset_chartTransitionSource_of_subset_target_subset_overlap
      (I := I)
      (x0 := C.boundaryChart i.1)
      (x1 := transitionSupportData.targetChart i)
      (hUtarget i) (hUoverlap i)

/-- Version using the chart-target containment already stored in the natural
`C^\infty` neighborhood record. -/
theorem boundaryNeighborhoodSubsetTransitionSource_of_overlap
    (hUoverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          ManifoldForm.chartOverlap I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)) :
    BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (K := K) neighborhoodData transitionSupportData :=
  boundaryNeighborhoodSubsetTransitionSource_of_target_overlap
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    neighborhoodData transitionSupportData
    neighborhoodData.boundary_neighborhood_subset_target hUoverlap

/-- Constructor from an explicitly chosen transition-neighborhood package whose
neighborhoods agree with the boundary neighborhoods in `neighborhoodData`. -/
theorem boundaryNeighborhoodSubsetTransitionSource_of_transitionBoxNeighborhoods
    (nbrs : CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C transitionSupportData.targetChart)
    (hneighborhood :
      neighborhoodData.boundaryNeighborhood = nbrs.boundaryNeighborhood) :
    BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (K := K) neighborhoodData transitionSupportData := by
  intro i y hy
  have hy' : y ∈ nbrs.boundaryNeighborhood i := by
    simpa [hneighborhood] using hy
  exact
    nbrs.boundaryNeighborhood_subset_chartTransitionSource
      (I := I) (K := K) (C := C) i hy'

/-- Source-box shrink version.  This is useful when the chart-box selection has
already made the smoothness neighborhood sit inside the selected source box. -/
theorem boundaryNeighborhoodSubsetTransitionSource_of_subset_sourceBox
    (hUbox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (K := K) neighborhoodData transitionSupportData :=
  boundaryNeighborhoodSubsetTransitionSource_of_overlap
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    neighborhoodData transitionSupportData
    (by
      intro i
      exact (hUbox i).trans (transitionSupportData.sourceBox_subset_overlap i))

end CoverIndexedCompactSupportNeighborhoodDataInfty

namespace CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput

/-- Direct constructor when the exact transition-source neighborhood field has
already been generated.  This gives a named, stable constructor for downstream
code instead of relying on raw structure syntax. -/
def ofSourceNeighborhood
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
    (zero_tsupport_subset_source :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChartZero I
              (C.boundaryChart i.1) (transitionSupportData.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_sourceTargetBoundarySum :
      globalBoundaryIntegral =
        Finset.sum C.boundaryCoverIndexFinset fun i =>
          projectLocalBoundaryIntegral I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput
      (I := I) (K := K) C P omega where
  neighborhoodData := neighborhoodData
  transitionSupportData := transitionSupportData
  sourceNeighborhood := sourceNeighborhood
  sourceOpen := sourceOpen
  zero_tsupport_subset_source := zero_tsupport_subset_source
  globalBoundaryIntegral := globalBoundaryIntegral
  globalBoundaryIntegral_eq_sourceTargetBoundarySum :=
    globalBoundaryIntegral_eq_sourceTargetBoundarySum

/-- Practical constructor from transition-neighborhood data.  The only
compatibility requirement is that the packaged transition neighborhoods are
the boundary neighborhoods already stored in `neighborhoodData`. -/
def ofTransitionBoxNeighborhoods
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
    (zero_tsupport_subset_source :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChartZero I
              (C.boundaryChart i.1) (transitionSupportData.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1))
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
    (CoverIndexedCompactSupportNeighborhoodDataInfty.boundaryNeighborhoodSubsetTransitionSource_of_transitionBoxNeighborhoods
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        neighborhoodData transitionSupportData nbrs hneighborhood)
    sourceOpen zero_tsupport_subset_source
    globalBoundaryIntegral globalBoundaryIntegral_eq_sourceTargetBoundarySum

/-- Constructor from a raw whole-neighborhood overlap field.  This is often the
output of a local chart-box shrink before it has been packaged as
`CoverIndexedBoundaryTransitionBoxNeighborhoods`. -/
def ofBoundaryNeighborhoodOverlap
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
    (zero_tsupport_subset_source :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChartZero I
              (C.boundaryChart i.1) (transitionSupportData.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1))
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
    (CoverIndexedCompactSupportNeighborhoodDataInfty.boundaryNeighborhoodSubsetTransitionSource_of_overlap
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        neighborhoodData transitionSupportData hUoverlap)
    sourceOpen zero_tsupport_subset_source
    globalBoundaryIntegral globalBoundaryIntegral_eq_sourceTargetBoundarySum

end CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput

end CoverIndexedZeroTransitionSourceConstructors

end Stokes

end
