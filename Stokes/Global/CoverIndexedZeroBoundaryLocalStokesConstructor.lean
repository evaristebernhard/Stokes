import Stokes.BoundaryChart.ZeroExtensionLocalStokes
import Stokes.Global.CoverIndexedZeroConstructors
import Stokes.Global.CoverIndexedCompactSupportCInftyAssembly

/-!
# Cover-indexed boundary local Stokes from zero-extension support

The zero-extension route separates the two roles of a chart representative:

* the ordinary transition representative is the smooth object used by local
  Stokes;
* the zero-extended transition representative is the support-controlled object
  used to kill the artificial half-space faces.

This file connects that local half-space theorem to the cover-indexed boundary
box data.  It deliberately does not change the endpoint structures: callers can
use the per-index project-local equality below before later target-boundary
change-of-variables steps.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroBoundaryLocalStokesConstructor

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace ManifoldForm

/-- The concrete transition source is contained in the source chart target. -/
theorem chartTransitionSource_subset_target
    (x0 x1 : M) :
    chartTransitionSource I x0 x1 ⊆ (extChartAt I x0).target := by
  intro y hy
  have hy' :
      y ∈ (extChartAt I x0).target ∩ chartOverlap I x0 x1 := by
    simpa [chartTransitionSource_eq] using hy
  exact hy'.1

/-- The concrete transition source is contained in the source-to-target
chart overlap. -/
theorem chartTransitionSource_subset_overlap
    (x0 x1 : M) :
    chartTransitionSource I x0 x1 ⊆ chartOverlap I x0 x1 := by
  intro y hy
  have hy' :
      y ∈ (extChartAt I x0).target ∩ chartOverlap I x0 x1 := by
    simpa [chartTransitionSource_eq] using hy
  exact hy'.2

end ManifoldForm

namespace CoverIndexedCompactSupportNeighborhoodData

/-- Smoothness of the old localized source-to-target transition
representative on the concrete transition source.

This is the smooth half of the zero-extension handoff: the old representative
is used for local Stokes, while support will come from its zero extension. -/
theorem boundary_sourceTransition_localized_contDiffOn
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodData
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    [IsManifold I ⊤ M]
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContDiffOn Real ⊤
      (ManifoldForm.transitionPullbackInChart I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)
        (P.coverIndexLocalizedForm omega (Sum.inr i)))
      (ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)) :=
  (neighborhoodData.localizedChartwiseSmooth i).contDiffOn_transitionPullbackInChart_of_chartAPI
    (I := I)
    (C.boundaryChart i.1) (transitionSupportData.targetChart i)
    (ManifoldForm.chartTransitionSource_subset_target
      (I := I) (C.boundaryChart i.1) (transitionSupportData.targetChart i))
    (ManifoldForm.chartTransitionSource_subset_overlap
      (I := I) (C.boundaryChart i.1) (transitionSupportData.targetChart i))

/-- Per-index boundary local Stokes with artificial faces removed by the
zero-extended localized representative.

The open-set input is exactly the remaining ambient-analysis fact for the
current half-space theorem.  The selected source box containment is supplied by
`boundary_sourceBox_subset_chartTransitionSource`, while smoothness is derived
from chartwise smoothness of the localized boundary piece. -/
theorem boundary_projectLocalStokes_of_zero_tsupport_subset_source
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodData
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    [IsManifold I ⊤ M]
    (i : {x : M // x ∈ C.boundaryCenters})
    (hsourceOpen :
      IsOpen
        (ManifoldForm.chartTransitionSource I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)))
    (hzero :
      tsupport
          (ManifoldForm.transitionPullbackInChartZero I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
        halfSpaceSupportBox
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    projectLocalBulkIntegral I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)
        (P.coverIndexLocalizedForm omega (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1) =
      projectLocalBoundaryIntegral I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)
        (P.coverIndexLocalizedForm omega (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  have hlocal :
      halfSpaceLocalTransitionBulkIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) =
        halfSpaceBoundarySign n *
          halfSpaceBoundaryTransitionFormIntegral I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
    halfSpaceLocalStokes_transitionPullback_of_zero_tsupport_subset_contDiffOn_isOpen
      (I := I)
      (x0 := C.boundaryChart i.1)
      (x1 := transitionSupportData.targetChart i)
      (ω := P.coverIndexLocalizedForm omega (Sum.inr i))
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (C.boundary_le i.1 i.2)
      (C.boundary_lower_zero i.1 i.2)
      hsourceOpen
      (CoverIndexedCompactSupportNeighborhoodData.boundary_sourceBox_subset_chartTransitionSource
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        neighborhoodData transitionSupportData i)
      (fun y hy => hy)
      (neighborhoodData.boundary_sourceTransition_localized_contDiffOn
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData i)
      hzero
  rw [projectLocalBulkIntegral, projectLocalBoundaryIntegral,
    outwardFirstBoundaryChartIntegral_eq_halfSpaceBoundarySign_mul]
  exact hlocal

/-- Per-index boundary local Stokes using the selected open boundary
neighborhood as the smoothness domain.

This is the boundary-compatible replacement for
`boundary_projectLocalStokes_of_zero_tsupport_subset_source`: the theorem no
longer asks the whole chart-transition source to be ambient-open.  Instead, the
already selected boundary neighborhood is open, contains the source box, and is
assumed to lie in the concrete transition source. -/
theorem boundary_projectLocalStokes_of_zero_tsupport_subset_sourceNeighborhood
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodData
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    [IsManifold I ⊤ M]
    (i : {x : M // x ∈ C.boundaryCenters})
    (hsourceNeighborhood :
      neighborhoodData.boundaryNeighborhood i ⊆
        ManifoldForm.chartTransitionSource I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i))
    (hzero :
      tsupport
          (ManifoldForm.transitionPullbackInChartZero I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
        halfSpaceSupportBox
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    projectLocalBulkIntegral I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)
        (P.coverIndexLocalizedForm omega (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1) =
      projectLocalBoundaryIntegral I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)
        (P.coverIndexLocalizedForm omega (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  have hω :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i)))
        (neighborhoodData.boundaryNeighborhood i) :=
    (neighborhoodData.localizedChartwiseSmooth i).contDiffOn_transitionPullbackInChart_of_chartAPI
      (I := I)
      (C.boundaryChart i.1) (transitionSupportData.targetChart i)
      (neighborhoodData.boundary_neighborhood_subset_target i)
      (by
        intro y hy
        exact
          ManifoldForm.chartTransitionSource_subset_overlap
            (I := I) (C.boundaryChart i.1)
            (transitionSupportData.targetChart i)
            (hsourceNeighborhood hy))
  have hlocal :
      halfSpaceLocalTransitionBulkIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) =
        halfSpaceBoundarySign n *
          halfSpaceBoundaryTransitionFormIntegral I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
    exact
      halfSpaceLocalStokes_transitionPullback_of_zero_tsupport_subset_contDiffOn_isOpen
        (I := I)
        (x0 := C.boundaryChart i.1)
        (x1 := transitionSupportData.targetChart i)
        (ω := P.coverIndexLocalizedForm omega (Sum.inr i))
        (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
        (C.boundary_le i.1 i.2)
        (C.boundary_lower_zero i.1 i.2)
        (neighborhoodData.boundary_neighborhood_open i)
        (neighborhoodData.boundary_Icc_subset_neighborhood i)
        hsourceNeighborhood
        hω
        hzero
  rw [projectLocalBulkIntegral, projectLocalBoundaryIntegral,
    outwardFirstBoundaryChartIntegral_eq_halfSpaceBoundarySign_mul]
  exact hlocal

/-- Finite boundary-cover sum form of
`boundary_projectLocalStokes_of_zero_tsupport_subset_source`. -/
theorem boundary_projectLocalBulkSum_eq_boundarySum_of_zero_tsupport_subset_source
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodData
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    [IsManifold I ⊤ M]
    (hsourceOpen :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen
          (ManifoldForm.chartTransitionSource I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)))
    (hzero :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChartZero I
              (C.boundaryChart i.1) (transitionSupportData.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    (Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBulkIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) =
      Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBoundaryIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact
    neighborhoodData.boundary_projectLocalStokes_of_zero_tsupport_subset_source
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData i (hsourceOpen i) (hzero i)

/-- Finite boundary-cover sum form using the selected open boundary
neighborhoods as smoothness domains. -/
theorem boundary_projectLocalBulkSum_eq_boundarySum_of_zero_tsupport_subset_sourceNeighborhood
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodData
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    [IsManifold I ⊤ M]
    (hsourceNeighborhood :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          ManifoldForm.chartTransitionSource I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i))
    (hzero :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChartZero I
              (C.boundaryChart i.1) (transitionSupportData.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    (Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBulkIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) =
      Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBoundaryIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact
    neighborhoodData.boundary_projectLocalStokes_of_zero_tsupport_subset_sourceNeighborhood
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData i (hsourceNeighborhood i) (hzero i)

end CoverIndexedCompactSupportNeighborhoodData

namespace CoverIndexedCompactSupportNeighborhoodDataInfty

/-- Source boundary boxes lie in the concrete chart-transition source for the
`C^\infty` neighborhood package. -/
theorem boundary_sourceBox_subset_chartTransitionSource
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
      ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i) := by
  intro y hy
  rw [ManifoldForm.chartTransitionSource_eq]
  exact
    ⟨neighborhoodData.boundary_neighborhood_subset_target i
        (neighborhoodData.boundary_Icc_subset_neighborhood i hy),
      transitionSupportData.sourceBox_subset_overlap i hy⟩

/-- `C^\infty` version of
`CoverIndexedCompactSupportNeighborhoodData.boundary_sourceTransition_localized_contDiffOn`. -/
theorem boundary_sourceTransition_localized_contDiffOn
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    [IsManifold I ⊤ M]
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContDiffOn Real ⊤
      (ManifoldForm.transitionPullbackInChart I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)
        (P.coverIndexLocalizedForm omega (Sum.inr i)))
      (ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)) :=
  (neighborhoodData.localizedChartwiseSmooth i).contDiffOn_transitionPullbackInChart_of_chartAPI
    (I := I)
    (C.boundaryChart i.1) (transitionSupportData.targetChart i)
    (ManifoldForm.chartTransitionSource_subset_target
      (I := I) (C.boundaryChart i.1) (transitionSupportData.targetChart i))
    (ManifoldForm.chartTransitionSource_subset_overlap
      (I := I) (C.boundaryChart i.1) (transitionSupportData.targetChart i))

/-- Natural `C^\infty` boundary local Stokes with artificial faces removed by
zero-extension support. -/
theorem boundary_projectLocalStokes_of_zero_tsupport_subset_source
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    [IsManifold I ⊤ M]
    (i : {x : M // x ∈ C.boundaryCenters})
    (hsourceOpen :
      IsOpen
        (ManifoldForm.chartTransitionSource I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)))
    (hzero :
      tsupport
          (ManifoldForm.transitionPullbackInChartZero I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
        halfSpaceSupportBox
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    projectLocalBulkIntegral I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)
        (P.coverIndexLocalizedForm omega (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1) =
      projectLocalBoundaryIntegral I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)
        (P.coverIndexLocalizedForm omega (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  have hlocal :
      halfSpaceLocalTransitionBulkIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) =
        halfSpaceBoundarySign n *
          halfSpaceBoundaryTransitionFormIntegral I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
    halfSpaceLocalStokes_transitionPullback_of_zero_tsupport_subset_contDiffOn_isOpen
      (I := I)
      (x0 := C.boundaryChart i.1)
      (x1 := transitionSupportData.targetChart i)
      (ω := P.coverIndexLocalizedForm omega (Sum.inr i))
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (C.boundary_le i.1 i.2)
      (C.boundary_lower_zero i.1 i.2)
      hsourceOpen
      (neighborhoodData.boundary_sourceBox_subset_chartTransitionSource
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData i)
      (fun y hy => hy)
      (neighborhoodData.boundary_sourceTransition_localized_contDiffOn
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData i)
      hzero
  rw [projectLocalBulkIntegral, projectLocalBoundaryIntegral,
    outwardFirstBoundaryChartIntegral_eq_halfSpaceBoundarySign_mul]
  exact hlocal

/-- Natural `C^\infty` boundary local Stokes using the selected open boundary
neighborhood as the smoothness domain.

This is the boundary-compatible local Stokes constructor: it replaces the
ambient-open chart-transition-source hypothesis by the genuine local field
`boundaryNeighborhood i ⊆ chartTransitionSource ...`. -/
theorem boundary_projectLocalStokes_of_zero_tsupport_subset_sourceNeighborhood
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    [IsManifold I ⊤ M]
    (i : {x : M // x ∈ C.boundaryCenters})
    (hsourceNeighborhood :
      neighborhoodData.boundaryNeighborhood i ⊆
        ManifoldForm.chartTransitionSource I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i))
    (hzero :
      tsupport
          (ManifoldForm.transitionPullbackInChartZero I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
        halfSpaceSupportBox
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    projectLocalBulkIntegral I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)
        (P.coverIndexLocalizedForm omega (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1) =
      projectLocalBoundaryIntegral I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)
        (P.coverIndexLocalizedForm omega (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  have hω :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i)))
        (neighborhoodData.boundaryNeighborhood i) :=
    (neighborhoodData.localizedChartwiseSmooth i).contDiffOn_transitionPullbackInChart_of_chartAPI
      (I := I)
      (C.boundaryChart i.1) (transitionSupportData.targetChart i)
      (neighborhoodData.boundary_neighborhood_subset_target i)
      (by
        intro y hy
        exact
          ManifoldForm.chartTransitionSource_subset_overlap
            (I := I) (C.boundaryChart i.1)
            (transitionSupportData.targetChart i)
            (hsourceNeighborhood hy))
  have hlocal :
      halfSpaceLocalTransitionBulkIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) =
        halfSpaceBoundarySign n *
          halfSpaceBoundaryTransitionFormIntegral I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
    exact
      halfSpaceLocalStokes_transitionPullback_of_zero_tsupport_subset_contDiffOn_isOpen
        (I := I)
        (x0 := C.boundaryChart i.1)
        (x1 := transitionSupportData.targetChart i)
        (ω := P.coverIndexLocalizedForm omega (Sum.inr i))
        (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
        (C.boundary_le i.1 i.2)
        (C.boundary_lower_zero i.1 i.2)
        (neighborhoodData.boundary_neighborhood_open i)
        (neighborhoodData.boundary_Icc_subset_neighborhood i)
        hsourceNeighborhood
        hω
        hzero
  rw [projectLocalBulkIntegral, projectLocalBoundaryIntegral,
    outwardFirstBoundaryChartIntegral_eq_halfSpaceBoundarySign_mul]
  exact hlocal

/-- Finite boundary-cover sum form for the natural `C^\infty` package. -/
theorem boundary_projectLocalBulkSum_eq_boundarySum_of_zero_tsupport_subset_source
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    [IsManifold I ⊤ M]
    (hsourceOpen :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen
          (ManifoldForm.chartTransitionSource I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)))
    (hzero :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChartZero I
              (C.boundaryChart i.1) (transitionSupportData.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    (Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBulkIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) =
      Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBoundaryIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact
    neighborhoodData.boundary_projectLocalStokes_of_zero_tsupport_subset_source
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData i (hsourceOpen i) (hzero i)

/-- Finite boundary-cover sum form for the natural `C^\infty` package, using
selected boundary neighborhoods rather than ambient-open transition sources. -/
theorem boundary_projectLocalBulkSum_eq_boundarySum_of_zero_tsupport_subset_sourceNeighborhood
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    [IsManifold I ⊤ M]
    (hsourceNeighborhood :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhoodData.boundaryNeighborhood i ⊆
          ManifoldForm.chartTransitionSource I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i))
    (hzero :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChartZero I
              (C.boundaryChart i.1) (transitionSupportData.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    (Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBulkIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) =
      Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBoundaryIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact
    neighborhoodData.boundary_projectLocalStokes_of_zero_tsupport_subset_sourceNeighborhood
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData i (hsourceNeighborhood i) (hzero i)

end CoverIndexedCompactSupportNeighborhoodDataInfty

end CoverIndexedZeroBoundaryLocalStokesConstructor

end Stokes

end
