import Stokes.Global.ChartCompactImage
import Stokes.ManifoldFormChartTransitionOpenCore

/-!
# Core self chart-transition source neighborhoods

This file contains only low-level self-chart facts in the `ManifoldForm`
namespace.  It deliberately avoids the cover-indexed constructor layer.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

universe uE uH uM

section ManifoldFormSelfSource

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H}
variable {K : Set M}
variable {x : M}
variable {k : Nat}
variable {omega : ManifoldForm I M k}

namespace ManifoldForm

/-- In a self chart change, the concrete transition source is just the chart
target.  The ambient `chartOverlap I x x` may be larger because
`PartialEquiv.symm` is a total function, but the partial-equivalence source
intersects it with the source chart target. -/
theorem chartTransitionSource_self_eq_target :
    chartTransitionSource I x x = (extChartAt I x).target := by
  rw [chartTransitionSource_eq]
  ext y
  constructor
  · intro hy
    exact hy.1
  · intro hy
    exact ⟨hy, (extChartAt I x).map_target hy⟩

/-- The target of a chart is contained in the self chart-transition source. -/
theorem target_subset_chartTransitionSource_self :
    (extChartAt I x).target ⊆ chartTransitionSource I x x := by
  rw [chartTransitionSource_self_eq_target]

/-- The self chart-transition source is contained in the chart target. -/
theorem chartTransitionSource_self_subset_target :
    chartTransitionSource I x x ⊆ (extChartAt I x).target := by
  rw [chartTransitionSource_self_eq_target]

/-- The self chart-transition source is open in a boundaryless model.  For
manifolds with boundary, the corresponding statement is generally only
relative to `range I`, so callers should use the explicit open-neighborhood
wrappers below. -/
theorem isOpen_chartTransitionSource_self [I.Boundaryless] :
    IsOpen (chartTransitionSource I x x) := by
  rw [chartTransitionSource_self_eq_target]
  exact isOpen_extChartAt_target x

/-- Coordinate images of manifold-side sets inside the chart source lie in the
self chart-transition source. -/
theorem chartCoordinateImage_subset_chartTransitionSource_self
    (hsource : K ⊆ (extChartAt I x).source) :
    chartCoordinateImage I x K ⊆ chartTransitionSource I x x := by
  rw [chartTransitionSource_self_eq_target]
  exact chartCoordinateImage_subset_target hsource

/-- A point of the chart target has the self chart-transition source as an
ordinary neighborhood in a boundaryless model. -/
theorem chartTransitionSource_self_mem_nhds_of_mem_target {y : E}
    [I.Boundaryless]
    (hy : y ∈ (extChartAt I x).target) :
    chartTransitionSource I x x ∈ 𝓝 y := by
  rw [chartTransitionSource_self_eq_target]
  exact extChartAt_target_mem_nhds' hy

/-- A point in the interior of the chart target has the self chart-transition
source as an ordinary neighborhood, without any boundaryless assumption. -/
theorem chartTransitionSource_self_mem_nhds_of_mem_interior_target {y : E}
    (hy : y ∈ interior (extChartAt I x).target) :
    chartTransitionSource I x x ∈ 𝓝 y := by
  exact
    mem_of_superset
      (isOpen_interior.mem_nhds hy)
      (by
        intro z hz
        exact target_subset_chartTransitionSource_self (I := I) (x := x) (interior_subset hz))

/-- A point in a coordinate image of a source-contained manifold set has the
self chart-transition source as a neighborhood in a boundaryless model. -/
theorem chartTransitionSource_self_mem_nhds_of_mem_chartCoordinateImage
    [I.Boundaryless]
    (hsource : K ⊆ (extChartAt I x).source) {y : E}
    (hy : y ∈ chartCoordinateImage I x K) :
    chartTransitionSource I x x ∈ 𝓝 y :=
  chartTransitionSource_self_mem_nhds_of_mem_target
    (I := I) (x := x)
    (chartCoordinateImage_subset_target hsource hy)

/-- If the old self-chart representative is topologically supported in a
source-contained coordinate image, the zero-extension bridge's source
neighborhood condition is automatic in a boundaryless model. -/
theorem transitionPullbackInChart_self_source_mem_nhds_of_tsupport_subset_chartCoordinateImage
    [I.Boundaryless]
    (hsource : K ⊆ (extChartAt I x).source)
    (hsupp :
      tsupport (transitionPullbackInChart I x x omega) ⊆
        chartCoordinateImage I x K) :
    ∀ y,
      y ∈ tsupport (transitionPullbackInChart I x x omega) →
        chartTransitionSource I x x ∈ 𝓝 y := by
  intro y hy
  exact
    chartTransitionSource_self_mem_nhds_of_mem_chartCoordinateImage
      (I := I) (K := K) (x := x) hsource (hsupp hy)

/-- Interior-target variant of the self source-neighborhood condition.  This is
the boundary-compatible form: it asks for the old support to lie in the ordinary
interior of the chart target. -/
theorem transitionPullbackInChart_self_source_mem_nhds_of_tsupport_subset_interior_target
    (hsupp :
      tsupport (transitionPullbackInChart I x x omega) ⊆
        interior (extChartAt I x).target) :
    ∀ y,
      y ∈ tsupport (transitionPullbackInChart I x x omega) →
        chartTransitionSource I x x ∈ 𝓝 y := by
  intro y hy
  exact
    chartTransitionSource_self_mem_nhds_of_mem_interior_target
      (I := I) (x := x) (hsupp hy)

/-- Open-neighborhood variant: any open neighborhood inside the chart target is
enough to produce the self transition-source neighborhood condition. -/
theorem transitionPullbackInChart_self_source_mem_nhds_of_tsupport_subset_open
    {U : Set E} (hUopen : IsOpen U)
    (hsupp : tsupport (transitionPullbackInChart I x x omega) ⊆ U)
    (hUtarget : U ⊆ (extChartAt I x).target) :
    ∀ y,
      y ∈ tsupport (transitionPullbackInChart I x x omega) →
        chartTransitionSource I x x ∈ 𝓝 y := by
  intro y hy
  exact
    mem_of_superset
      (hUopen.mem_nhds (hsupp hy))
      (by
        intro z hz
        exact target_subset_chartTransitionSource_self (I := I) (x := x) (hUtarget hz))

/-- Direct subset-source version of the open-neighborhood wrapper. -/
theorem transitionPullbackInChart_self_source_mem_nhds_of_tsupport_subset_open_source
    {U : Set E} (hUopen : IsOpen U)
    (hsupp : tsupport (transitionPullbackInChart I x x omega) ⊆ U)
    (hUsource : U ⊆ chartTransitionSource I x x) :
    ∀ y,
      y ∈ tsupport (transitionPullbackInChart I x x omega) →
        chartTransitionSource I x x ∈ 𝓝 y := by
  intro y hy
  exact mem_of_superset (hUopen.mem_nhds (hsupp hy)) hUsource

end ManifoldForm

end ManifoldFormSelfSource

end Stokes

end
