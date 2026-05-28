import Stokes.ManifoldFormChartTransitionOpenCore
import Stokes.Global.CoverIndexedCompactSupportNaturalTheorem

/-!
# Cover-indexed wrappers for chart-transition source topology

The core `ManifoldForm` facts live in
`Stokes.ManifoldFormChartTransitionOpenCore`.  This module preserves the older
cover-indexed wrapper fields without making the core chart API depend on the
global Stokes route.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set Filter
open scoped Manifold Topology

namespace Stokes

universe uH uM

section CoverIndexedChartTransitionOpen

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {omega : ManifoldForm I M n}

namespace CoverIndexedCompactSupportTransitionSupportData

/-- Boundaryless cover-index constructor for the ambient-open source field
currently consumed by some local half-space wrappers. -/
theorem sourceOpenField [I.Boundaryless]
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      IsOpen
        (ManifoldForm.chartTransitionSource I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)) := by
  intro i
  exact
    ManifoldForm.isOpen_chartTransitionSource
      (I := I) (C.boundaryChart i.1) (transitionSupportData.targetChart i)

/-- Cover-index relative-neighborhood source field, valid for manifolds with
boundary.  This is the honest chart API available without assuming the model
range is all of the ambient vector space. -/
theorem sourceMemNhdsWithinRangeField
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      ∀ y,
        y ∈ ManifoldForm.chartTransitionSource I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i) →
        ManifoldForm.chartTransitionSource I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i) ∈
            𝓝[range I] y := by
  intro i y hy
  exact
    ManifoldForm.chartTransitionSource_mem_nhdsWithin_range_of_mem
      (I := I) hy

end CoverIndexedCompactSupportTransitionSupportData

end CoverIndexedChartTransitionOpen

end Stokes

end
