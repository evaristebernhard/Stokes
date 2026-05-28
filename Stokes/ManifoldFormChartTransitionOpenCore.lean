import Stokes.ManifoldForm

/-!
# Core openness facts for chart-transition sources

This file contains only the low-level `ManifoldForm` facts about chart
transition sources.  It intentionally avoids importing the cover-indexed
global Stokes layers.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set Filter
open scoped Manifold Topology

namespace Stokes

universe uE uH uM

section ManifoldFormChartTransitionOpen

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H}

namespace ManifoldForm

/-- The project-level transition source is the image under the model map of the
usual chart-at transition source. -/
theorem chartTransitionSource_eq_image_chartAt_source (x0 x1 : M) :
    chartTransitionSource I x0 x1 =
      I '' (((chartAt H x0).symm ≫ₕ chartAt H x1).source) := by
  simpa [chartTransitionSource] using
    (ext_coord_change_source (I := I) (x := x1) (x' := x0))

/-- In a model with corners, the transition source is a neighborhood within the
model range at every point of the source.  This is the boundary-compatible
replacement for ambient openness. -/
theorem chartTransitionSource_mem_nhdsWithin_range_of_mem
    {x0 x1 : M} {y : E}
    (hy : y ∈ chartTransitionSource I x0 x1) :
    chartTransitionSource I x0 x1 ∈ 𝓝[range I] y := by
  rw [chartTransitionSource_eq_image_chartAt_source (I := I) x0 x1] at hy ⊢
  rcases hy with ⟨z, hz, rfl⟩
  exact
    I.image_mem_nhdsWithin
      (((chartAt H x0).symm ≫ₕ chartAt H x1).open_source.mem_nhds hz)

/-- Boundaryless specialization: the chart-transition source is genuinely open
in the ambient model vector space.  Without `[I.Boundaryless]` this statement is
false in general; the self-transition source can be a half-space. -/
theorem isOpen_chartTransitionSource [I.Boundaryless] (x0 x1 : M) :
    IsOpen (chartTransitionSource I x0 x1) := by
  rw [chartTransitionSource_eq_image_chartAt_source (I := I) x0 x1]
  simpa [ModelWithCorners.toHomeomorph]
    using
      (ModelWithCorners.toHomeomorph I).isOpenMap
        (((chartAt H x0).symm ≫ₕ chartAt H x1).source)
        (((chartAt H x0).symm ≫ₕ chartAt H x1).open_source)

/-- Boundaryless point-neighborhood form of `isOpen_chartTransitionSource`. -/
theorem chartTransitionSource_mem_nhds_of_mem [I.Boundaryless]
    {x0 x1 : M} {y : E}
    (hy : y ∈ chartTransitionSource I x0 x1) :
    chartTransitionSource I x0 x1 ∈ 𝓝 y :=
  (isOpen_chartTransitionSource (I := I) x0 x1).mem_nhds hy

end ManifoldForm

end ManifoldFormChartTransitionOpen

end Stokes

end
