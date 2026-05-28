import Stokes.SingularCube.ManifoldBridge

/-!
# Smooth singular bridge facade

This file exposes a small public entry point for using the smooth singular
cube Stokes theorem with a manifold form written in one chart.

The theorem remains intentionally honest about the current analytic gap:
`ChartwiseSmooth` gives the chart representative only `ContDiffOn` on a chart
neighborhood, while the imported singular-cube theorem currently asks for a
globally `ContDiff` Euclidean form.  The facade packages the chart-local data
and keeps the global smoothness extension hypothesis explicit.
-/

noncomputable section

open Set
open scoped Manifold Topology

namespace Stokes

section SmoothSingularBridgeFacade

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Build the local chart data used by the smooth-singular-cube bridge from a
chartwise smooth manifold form.
-/
abbrev chartSingularCubeLocalDataOfChartwiseSmooth {d m k : Nat}
    {I : ModelWithCorners Real (Fin m -> Real) H}
    {omega : ManifoldForm I M k}
    (chart : M) (cube : SmoothSingularCube d m)
    {U : Set (Fin m -> Real)}
    (hU : IsOpen U)
    (himage : MapsTo cube.toFun (singularParameterCube d) U)
    (hUtarget : U <= (extChartAt I chart).target)
    (homega : ManifoldForm.ChartwiseSmooth I omega) :
    ChartSingularCubeLocalData (d := d) I omega :=
  ChartSingularCubeLocalData.ofChartwiseSmooth
    (I := I) (omega := omega) chart cube hU himage hUtarget homega

/--
Boundary-integral smooth singular Stokes for a manifold form in one chart.

The final hypothesis is the current bridge gap: it asks for a global smooth
extension of the selected chart representative.
-/
theorem chartwise_singular_boundary_stokes_of_globalSmooth {n m : Nat}
    {I : ModelWithCorners Real (Fin m -> Real) H}
    {omega : ManifoldForm I M n}
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    {U : Set (Fin m -> Real)}
    (hU : IsOpen U)
    (himage : MapsTo cube.toFun (singularParameterCube (n + 1)) U)
    (hUtarget : U <= (extChartAt I chart).target)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (homega_global : ContDiff Real ⊤ (chartLocalForm I chart omega)) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  let D :=
    chartSingularCubeLocalDataOfChartwiseSmooth
      (I := I) (omega := omega) chart cube hU himage hUtarget homega
  exact D.singular_boundary_stokes_local (by
    simpa [D, chartSingularCubeLocalDataOfChartwiseSmooth] using homega_global)

/--
Chain-level smooth singular Stokes for a manifold form in one chart.

This is the same facade as
`chartwise_singular_boundary_stokes_of_globalSmooth`, but in the finite-chain
orientation used by `Stokes.SingularCube`.
-/
theorem chartwise_singular_chain_stokes_of_globalSmooth {n m : Nat}
    {I : ModelWithCorners Real (Fin m -> Real) H}
    {omega : ManifoldForm I M n}
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    {U : Set (Fin m -> Real)}
    (hU : IsOpen U)
    (himage : MapsTo cube.toFun (singularParameterCube (n + 1)) U)
    (hUtarget : U <= (extChartAt I chart).target)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (homega_global : ContDiff Real ⊤ (chartLocalForm I chart omega)) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  let D :=
    chartSingularCubeLocalDataOfChartwiseSmooth
      (I := I) (omega := omega) chart cube hU himage hUtarget homega
  exact D.singular_chain_stokes_local (by
    simpa [D, chartSingularCubeLocalDataOfChartwiseSmooth] using homega_global)

end SmoothSingularBridgeFacade

end Stokes

end
