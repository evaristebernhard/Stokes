import Stokes.ManifoldForm

/-!
# Zero-extended chart representatives

This file adds a thin zero-extension layer for chart representatives.

The existing `ManifoldForm.inChart` and `ManifoldForm.transitionPullbackInChart`
remain the smooth representatives used on chart domains.  The definitions here
only add the mathematical convention that a coordinate representative is zero
outside the chart domain where it is meant to be used.
-/

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace Stokes

universe u v w

/-- Extend a function by zero outside a set. -/
def zeroOutside {X A : Type*} [Zero A] (s : Set X) (f : X → A) : X → A :=
  by
    classical
    exact fun x => if x ∈ s then f x else 0

@[simp]
theorem zeroOutside_eq_of_mem {X A : Type*} [Zero A] {s : Set X}
    {f : X → A} {x : X} (hx : x ∈ s) :
    zeroOutside s f x = f x := by
  classical
  simp [zeroOutside, hx]

@[simp]
theorem zeroOutside_eq_zero_of_notMem {X A : Type*} [Zero A] {s : Set X}
    {f : X → A} {x : X} (hx : x ∉ s) :
    zeroOutside s f x = 0 := by
  classical
  simp [zeroOutside, hx]

/-- The ordinary support of a zero extension is contained in the extension set. -/
theorem support_zeroOutside_subset {X A : Type*} [Zero A] {s : Set X}
    {f : X → A} :
    Function.support (zeroOutside s f) ⊆ s := by
  intro x hx
  by_contra hxs
  have hxne : zeroOutside s f x ≠ 0 := by
    simpa [Function.mem_support] using hx
  exact hxne (zeroOutside_eq_zero_of_notMem hxs)

/-- The zero extension agrees with the original function on the extension set. -/
theorem zeroOutside_eqOn {X A : Type*} [Zero A] {s : Set X} {f : X → A} :
    EqOn (zeroOutside s f) f s := by
  intro x hx
  exact zeroOutside_eq_of_mem hx

/-- The zero extension is eventually equal to the original function at points
whose neighborhood filter contains the extension set. -/
theorem zeroOutside_eventuallyEq_of_mem_nhds {X A : Type*}
    [TopologicalSpace X] [Zero A] {s : Set X} {f : X → A} {x : X}
    (hs : s ∈ 𝓝 x) :
    zeroOutside s f =ᶠ[𝓝 x] f := by
  filter_upwards [hs] with y hy
  exact zeroOutside_eq_of_mem hy

namespace ManifoldForm

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners Real E H)
variable {k : Nat}

/-- The chart representative extended by zero outside the chart target. -/
def inChartZero (x0 : M) (ω : ManifoldForm I M k) : ModelForm E k :=
  zeroOutside (extChartAt I x0).target (inChart I x0 ω)

/-- The transition representative extended by zero outside the concrete
source of the coordinate transition. -/
def transitionPullbackInChartZero (x0 x1 : M)
    (ω : ManifoldForm I M k) : ModelForm E k :=
  zeroOutside (chartTransitionSource I x0 x1)
    (transitionPullbackInChart I x0 x1 ω)

@[simp]
theorem inChartZero_eq_inChart_of_mem {x0 : M} {ω : ManifoldForm I M k}
    {y : E} (hy : y ∈ (extChartAt I x0).target) :
    inChartZero I x0 ω y = inChart I x0 ω y := by
  exact zeroOutside_eq_of_mem hy

@[simp]
theorem inChartZero_eq_zero_of_notMem {x0 : M} {ω : ManifoldForm I M k}
    {y : E} (hy : y ∉ (extChartAt I x0).target) :
    inChartZero I x0 ω y = 0 := by
  exact zeroOutside_eq_zero_of_notMem hy

theorem inChartZero_support_subset_target (x0 : M)
    (ω : ManifoldForm I M k) :
    Function.support (inChartZero I x0 ω) ⊆ (extChartAt I x0).target :=
  support_zeroOutside_subset

theorem inChartZero_eqOn_inChart (x0 : M) (ω : ManifoldForm I M k) :
    EqOn (inChartZero I x0 ω) (inChart I x0 ω)
      (extChartAt I x0).target :=
  zeroOutside_eqOn

theorem inChartZero_eventuallyEq_inChart_of_mem_nhds {x0 : M}
    {ω : ManifoldForm I M k} {y : E}
    (hy : (extChartAt I x0).target ∈ 𝓝 y) :
    inChartZero I x0 ω =ᶠ[𝓝 y] inChart I x0 ω :=
  zeroOutside_eventuallyEq_of_mem_nhds hy

@[simp]
theorem transitionPullbackInChartZero_eq_transitionPullbackInChart_of_mem_source
    {x0 x1 : M} {ω : ManifoldForm I M k} {y : E}
    (hy : y ∈ chartTransitionSource I x0 x1) :
    transitionPullbackInChartZero I x0 x1 ω y =
      transitionPullbackInChart I x0 x1 ω y := by
  exact zeroOutside_eq_of_mem hy

@[simp]
theorem transitionPullbackInChartZero_eq_zero_of_notMem_source
    {x0 x1 : M} {ω : ManifoldForm I M k} {y : E}
    (hy : y ∉ chartTransitionSource I x0 x1) :
    transitionPullbackInChartZero I x0 x1 ω y = 0 := by
  exact zeroOutside_eq_zero_of_notMem hy

theorem transitionPullbackInChartZero_support_subset_source
    (x0 x1 : M) (ω : ManifoldForm I M k) :
    Function.support (transitionPullbackInChartZero I x0 x1 ω) ⊆
      chartTransitionSource I x0 x1 :=
  support_zeroOutside_subset

theorem transitionPullbackInChartZero_support_subset_target
    (x0 x1 : M) (ω : ManifoldForm I M k) :
    Function.support (transitionPullbackInChartZero I x0 x1 ω) ⊆
      (extChartAt I x0).target := by
  intro y hy
  have hsource :
      y ∈ chartTransitionSource I x0 x1 :=
    transitionPullbackInChartZero_support_subset_source (I := I) x0 x1 ω hy
  have hsource' :
      y ∈ (extChartAt I x0).target ∩ chartOverlap I x0 x1 := by
    simpa [chartTransitionSource_eq] using hsource
  exact hsource'.1

theorem transitionPullbackInChartZero_support_subset_overlap
    (x0 x1 : M) (ω : ManifoldForm I M k) :
    Function.support (transitionPullbackInChartZero I x0 x1 ω) ⊆
      chartOverlap I x0 x1 := by
  intro y hy
  have hsource :
      y ∈ chartTransitionSource I x0 x1 :=
    transitionPullbackInChartZero_support_subset_source (I := I) x0 x1 ω hy
  have hsource' :
      y ∈ (extChartAt I x0).target ∩ chartOverlap I x0 x1 := by
    simpa [chartTransitionSource_eq] using hsource
  exact hsource'.2

theorem transitionPullbackInChartZero_eqOn_transitionPullbackInChart
    (x0 x1 : M) (ω : ManifoldForm I M k) :
    EqOn (transitionPullbackInChartZero I x0 x1 ω)
      (transitionPullbackInChart I x0 x1 ω)
      (chartTransitionSource I x0 x1) :=
  zeroOutside_eqOn

theorem transitionPullbackInChartZero_eventuallyEq_transitionPullbackInChart_of_mem_nhds
    {x0 x1 : M} {ω : ManifoldForm I M k} {y : E}
    (hy : chartTransitionSource I x0 x1 ∈ 𝓝 y) :
    transitionPullbackInChartZero I x0 x1 ω =ᶠ[𝓝 y]
      transitionPullbackInChart I x0 x1 ω :=
  zeroOutside_eventuallyEq_of_mem_nhds hy

theorem transitionPullbackInChartZero_eq_transitionPullbackInChart_of_mem_target_overlap
    {x0 x1 : M} {ω : ManifoldForm I M k} {y : E}
    (hytarget : y ∈ (extChartAt I x0).target)
    (hyoverlap : y ∈ chartOverlap I x0 x1) :
    transitionPullbackInChartZero I x0 x1 ω y =
      transitionPullbackInChart I x0 x1 ω y := by
  exact transitionPullbackInChartZero_eq_transitionPullbackInChart_of_mem_source
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    (by
      rw [chartTransitionSource_eq]
      exact ⟨hytarget, hyoverlap⟩)

end ManifoldForm

end Stokes

end
