import Stokes.ManifoldFormZero
import Stokes.Global.BulkIntegrandAE

/-!
# Bulk equality for zero-extended transition representatives

The zero-extension layer controls supports by replacing a chart representative
with the same representative extended by zero outside its chart-transition
source.  Local Stokes arguments, however, should still reuse the old smooth
representatives on chart boxes contained in that source.

This file packages the precise locality bridge: on any neighborhood contained
in the chart-transition source, the exterior derivatives of the zero-extended
and old transition representatives agree.  In top degree this gives equality of
the scalar bulk integrand used by the existing local/global Stokes assembly.
-/

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace Stokes

namespace ManifoldForm

section TransitionZeroExtDeriv

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}
variable {x0 x1 : M} {ω : ManifoldForm I M k} {y : E}

/--
If the concrete chart-transition source is a neighborhood of `y`, then the
zero-extended transition representative and the old transition representative
have the same exterior derivative at `y`.
-/
theorem transitionPullbackInChartZero_extDeriv_eq_transitionPullbackInChart_of_mem_nhds
    (hy : chartTransitionSource I x0 x1 ∈ 𝓝 y) :
    extDeriv (transitionPullbackInChartZero I x0 x1 ω) y =
      extDeriv (transitionPullbackInChart I x0 x1 ω) y :=
  extDeriv_eq_of_eventuallyEq
    (transitionPullbackInChartZero_eventuallyEq_transitionPullbackInChart_of_mem_nhds
      (I := I) (x0 := x0) (x1 := x1) (ω := ω) (y := y) hy)

/--
A neighborhood `s` contained in the chart-transition source is enough to compare
the zero-extended and old exterior derivatives at `y`.
-/
theorem transitionPullbackInChartZero_extDeriv_eq_transitionPullbackInChart_of_set_mem_nhds
    {s : Set E} (hs : s ∈ 𝓝 y)
    (hssource : s ⊆ chartTransitionSource I x0 x1) :
    extDeriv (transitionPullbackInChartZero I x0 x1 ω) y =
      extDeriv (transitionPullbackInChart I x0 x1 ω) y := by
  apply extDeriv_eq_of_eventuallyEq
  filter_upwards [hs] with z hz
  exact
    transitionPullbackInChartZero_eq_transitionPullbackInChart_of_mem_source
      (I := I) (x0 := x0) (x1 := x1) (ω := ω) (y := z) (hssource hz)

/--
Point membership in an open set contained in the chart-transition source gives
the same exterior-derivative comparison.
-/
theorem transitionPullbackInChartZero_extDeriv_eq_transitionPullbackInChart_of_isOpen_mem
    {s : Set E} (hsopen : IsOpen s) (hy : y ∈ s)
    (hssource : s ⊆ chartTransitionSource I x0 x1) :
    extDeriv (transitionPullbackInChartZero I x0 x1 ω) y =
      extDeriv (transitionPullbackInChart I x0 x1 ω) y :=
  transitionPullbackInChartZero_extDeriv_eq_transitionPullbackInChart_of_set_mem_nhds
    (I := I) (x0 := x0) (x1 := x1) (ω := ω) (y := y)
    (hsopen.mem_nhds hy) hssource

end TransitionZeroExtDeriv

end ManifoldForm

section ZeroBulkIntegrand

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
The scalar top-degree bulk integrand built from the zero-extended transition
representative.  This is only a local bridge; the project-facing `bulkIntegrand`
still uses the original manifold form.
-/
def zeroTransitionBulkIntegrand {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) :
    (Fin (n + 1) → Real) → Real :=
  fun y =>
    extDeriv (ManifoldForm.transitionPullbackInChartZero I x0 x1 ω) y
      (standardTopFrame n)

/--
On a neighborhood contained in the chart-transition source, the zero-extended
scalar bulk integrand agrees with the existing chartwise `bulkIntegrand`.
-/
theorem zeroTransitionBulkIntegrand_eq_bulkIntegrand_of_mem_nhds {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {y : Fin (n + 1) → Real}
    (hy : ManifoldForm.chartTransitionSource I x0 x1 ∈ 𝓝 y) :
    zeroTransitionBulkIntegrand I x0 x1 ω y =
      bulkIntegrand I x0 x1 ω y := by
  have hext :
      extDeriv (ManifoldForm.transitionPullbackInChartZero I x0 x1 ω) y =
        extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y :=
    ManifoldForm.transitionPullbackInChartZero_extDeriv_eq_transitionPullbackInChart_of_mem_nhds
      (I := I) (x0 := x0) (x1 := x1) (ω := ω) (y := y) hy
  simpa [zeroTransitionBulkIntegrand, bulkIntegrand] using
    congrArg (fun η => η (standardTopFrame n)) hext

/--
Version of `zeroTransitionBulkIntegrand_eq_bulkIntegrand_of_mem_nhds` using an
explicit neighborhood `s` contained in the transition source.
-/
theorem zeroTransitionBulkIntegrand_eq_bulkIntegrand_of_set_mem_nhds {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {y : Fin (n + 1) → Real}
    {s : Set (Fin (n + 1) → Real)} (hs : s ∈ 𝓝 y)
    (hssource : s ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    zeroTransitionBulkIntegrand I x0 x1 ω y =
      bulkIntegrand I x0 x1 ω y := by
  have hext :
      extDeriv (ManifoldForm.transitionPullbackInChartZero I x0 x1 ω) y =
        extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y :=
    ManifoldForm.transitionPullbackInChartZero_extDeriv_eq_transitionPullbackInChart_of_set_mem_nhds
      (I := I) (x0 := x0) (x1 := x1) (ω := ω) (y := y) hs hssource
  simpa [zeroTransitionBulkIntegrand, bulkIntegrand] using
    congrArg (fun η => η (standardTopFrame n)) hext

/--
Open-neighborhood form used by local chart boxes: if the box lies in an open
set contained in the transition source, the zero-extended and old bulk scalar
terms agree at points of that open set.
-/
theorem zeroTransitionBulkIntegrand_eq_bulkIntegrand_of_isOpen_mem {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {y : Fin (n + 1) → Real}
    {s : Set (Fin (n + 1) → Real)} (hsopen : IsOpen s) (hy : y ∈ s)
    (hssource : s ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    zeroTransitionBulkIntegrand I x0 x1 ω y =
      bulkIntegrand I x0 x1 ω y :=
  zeroTransitionBulkIntegrand_eq_bulkIntegrand_of_set_mem_nhds
    (I := I) (x0 := x0) (x1 := x1) (ω := ω) (y := y)
    (hsopen.mem_nhds hy) hssource

end ZeroBulkIntegrand

end Stokes

end
