import Stokes.SingularCube.SmoothBridgeFacade
import Stokes.SingularCube.IntegralCongruence
import Stokes.SingularCube.ExtDerivLocality

/-!
# Smooth singular bridge with local extension hypotheses

This facade is the public version of the smooth-singular bridge that uses a
global smooth Euclidean extension only where the current singular-cube theorem
needs one.  The user-facing hypotheses are local agreement hypotheses on the
cube and boundary-face images; the pointwise exterior-derivative congruence is
hidden behind `Stokes.SingularCube.ExtDerivLocality`.
-/

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace Stokes

section SmoothSingularBridgeLocalityFacade

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Boundary-integral smooth singular Stokes for a chartwise smooth manifold form,
using a globally smooth extension that agrees with the chart representative in
neighborhoods of the high faces, low faces, and cube image.
-/
theorem chartwise_singular_boundary_stokes_of_extension_eventuallyEq {n m : Nat}
    {I : ModelWithCorners Real (Fin m → Real) H}
    {omega : ManifoldForm I M n}
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    {U : Set (Fin m → Real)}
    (hU : IsOpen U)
    (himage : MapsTo cube.toFun (singularParameterCube (n + 1)) U)
    (hUtarget : U ⊆ (extChartAt I chart).target)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (omegaExt : EuclideanForm m n)
    (homegaExt : ContDiff Real ⊤ omegaExt)
    (hone :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        omegaExt =ᶠ[𝓝 ((singularFace cube i 1).toFun x)]
          chartLocalForm I chart omega)
    (hzero :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        omegaExt =ᶠ[𝓝 ((singularFace cube i 0).toFun x)]
          chartLocalForm I chart omega)
    (hcube :
      ∀ x ∈ singularParameterCube (n + 1),
        omegaExt =ᶠ[𝓝 (cube.toFun x)] chartLocalForm I chart omega) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  let D :=
    chartSingularCubeLocalDataOfChartwiseSmooth
      (I := I) (omega := omega) chart cube hU himage hUtarget homega
  simpa [D, chartSingularCubeLocalDataOfChartwiseSmooth] using
    (D.singular_boundary_stokes_local_of_extension_eventuallyEq
      omegaExt homegaExt hone hzero hcube)

/--
Chain-level version of
`chartwise_singular_boundary_stokes_of_extension_eventuallyEq`.
-/
theorem chartwise_singular_chain_stokes_of_extension_eventuallyEq {n m : Nat}
    {I : ModelWithCorners Real (Fin m → Real) H}
    {omega : ManifoldForm I M n}
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    {U : Set (Fin m → Real)}
    (hU : IsOpen U)
    (himage : MapsTo cube.toFun (singularParameterCube (n + 1)) U)
    (hUtarget : U ⊆ (extChartAt I chart).target)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (omegaExt : EuclideanForm m n)
    (homegaExt : ContDiff Real ⊤ omegaExt)
    (hone :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        omegaExt =ᶠ[𝓝 ((singularFace cube i 1).toFun x)]
          chartLocalForm I chart omega)
    (hzero :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        omegaExt =ᶠ[𝓝 ((singularFace cube i 0).toFun x)]
          chartLocalForm I chart omega)
    (hcube :
      ∀ x ∈ singularParameterCube (n + 1),
        omegaExt =ᶠ[𝓝 (cube.toFun x)] chartLocalForm I chart omega) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  let D :=
    chartSingularCubeLocalDataOfChartwiseSmooth
      (I := I) (omega := omega) chart cube hU himage hUtarget homega
  simpa [D, chartSingularCubeLocalDataOfChartwiseSmooth] using
    (D.singular_chain_stokes_local_of_extension_eventuallyEq
      omegaExt homegaExt hone hzero hcube)

/--
Boundary-integral smooth singular Stokes from equality on neighborhoods of each
cube and boundary-face image point.
-/
theorem chartwise_singular_boundary_stokes_of_extension_eqOn_mem_nhds {n m : Nat}
    {I : ModelWithCorners Real (Fin m → Real) H}
    {omega : ManifoldForm I M n}
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    {U : Set (Fin m → Real)}
    (hU : IsOpen U)
    (himage : MapsTo cube.toFun (singularParameterCube (n + 1)) U)
    (hUtarget : U ⊆ (extChartAt I chart).target)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (omegaExt : EuclideanForm m n)
    (homegaExt : ContDiff Real ⊤ omegaExt)
    (hone :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        ∃ s : Set (Fin m → Real),
          s ∈ 𝓝 ((singularFace cube i 1).toFun x) ∧
            EqOn omegaExt (chartLocalForm I chart omega) s)
    (hzero :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        ∃ s : Set (Fin m → Real),
          s ∈ 𝓝 ((singularFace cube i 0).toFun x) ∧
            EqOn omegaExt (chartLocalForm I chart omega) s)
    (hcube :
      ∀ x ∈ singularParameterCube (n + 1),
        ∃ s : Set (Fin m → Real),
          s ∈ 𝓝 (cube.toFun x) ∧ EqOn omegaExt (chartLocalForm I chart omega) s) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  let D :=
    chartSingularCubeLocalDataOfChartwiseSmooth
      (I := I) (omega := omega) chart cube hU himage hUtarget homega
  simpa [D, chartSingularCubeLocalDataOfChartwiseSmooth] using
    (D.singular_boundary_stokes_local_of_extension_eqOn_mem_nhds
      omegaExt homegaExt hone hzero hcube)

/--
Chain-level version of
`chartwise_singular_boundary_stokes_of_extension_eqOn_mem_nhds`.
-/
theorem chartwise_singular_chain_stokes_of_extension_eqOn_mem_nhds {n m : Nat}
    {I : ModelWithCorners Real (Fin m → Real) H}
    {omega : ManifoldForm I M n}
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    {U : Set (Fin m → Real)}
    (hU : IsOpen U)
    (himage : MapsTo cube.toFun (singularParameterCube (n + 1)) U)
    (hUtarget : U ⊆ (extChartAt I chart).target)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (omegaExt : EuclideanForm m n)
    (homegaExt : ContDiff Real ⊤ omegaExt)
    (hone :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        ∃ s : Set (Fin m → Real),
          s ∈ 𝓝 ((singularFace cube i 1).toFun x) ∧
            EqOn omegaExt (chartLocalForm I chart omega) s)
    (hzero :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        ∃ s : Set (Fin m → Real),
          s ∈ 𝓝 ((singularFace cube i 0).toFun x) ∧
            EqOn omegaExt (chartLocalForm I chart omega) s)
    (hcube :
      ∀ x ∈ singularParameterCube (n + 1),
        ∃ s : Set (Fin m → Real),
          s ∈ 𝓝 (cube.toFun x) ∧ EqOn omegaExt (chartLocalForm I chart omega) s) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  let D :=
    chartSingularCubeLocalDataOfChartwiseSmooth
      (I := I) (omega := omega) chart cube hU himage hUtarget homega
  simpa [D, chartSingularCubeLocalDataOfChartwiseSmooth] using
    (D.singular_chain_stokes_local_of_extension_eqOn_mem_nhds
      omegaExt homegaExt hone hzero hcube)

/--
Boundary-integral smooth singular Stokes from one open extension neighborhood
on which the global extension agrees with the selected chart representative.
-/
theorem chartwise_singular_boundary_stokes_of_extension_eqOn_isOpen {n m : Nat}
    {I : ModelWithCorners Real (Fin m → Real) H}
    {omega : ManifoldForm I M n}
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    {U V : Set (Fin m → Real)}
    (hU : IsOpen U)
    (himage : MapsTo cube.toFun (singularParameterCube (n + 1)) U)
    (hUtarget : U ⊆ (extChartAt I chart).target)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (omegaExt : EuclideanForm m n)
    (homegaExt : ContDiff Real ⊤ omegaExt)
    (hV : IsOpen V)
    (hone :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        (singularFace cube i 1).toFun x ∈ V)
    (hzero :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        (singularFace cube i 0).toFun x ∈ V)
    (hcube : ∀ x ∈ singularParameterCube (n + 1), cube.toFun x ∈ V)
    (heq : EqOn omegaExt (chartLocalForm I chart omega) V) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  let D :=
    chartSingularCubeLocalDataOfChartwiseSmooth
      (I := I) (omega := omega) chart cube hU himage hUtarget homega
  simpa [D, chartSingularCubeLocalDataOfChartwiseSmooth] using
    (D.singular_boundary_stokes_local_of_extension_eqOn_isOpen
      omegaExt homegaExt hV hone hzero hcube heq)

/--
Chain-level version of
`chartwise_singular_boundary_stokes_of_extension_eqOn_isOpen`.
-/
theorem chartwise_singular_chain_stokes_of_extension_eqOn_isOpen {n m : Nat}
    {I : ModelWithCorners Real (Fin m → Real) H}
    {omega : ManifoldForm I M n}
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    {U V : Set (Fin m → Real)}
    (hU : IsOpen U)
    (himage : MapsTo cube.toFun (singularParameterCube (n + 1)) U)
    (hUtarget : U ⊆ (extChartAt I chart).target)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (omegaExt : EuclideanForm m n)
    (homegaExt : ContDiff Real ⊤ omegaExt)
    (hV : IsOpen V)
    (hone :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        (singularFace cube i 1).toFun x ∈ V)
    (hzero :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        (singularFace cube i 0).toFun x ∈ V)
    (hcube : ∀ x ∈ singularParameterCube (n + 1), cube.toFun x ∈ V)
    (heq : EqOn omegaExt (chartLocalForm I chart omega) V) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  let D :=
    chartSingularCubeLocalDataOfChartwiseSmooth
      (I := I) (omega := omega) chart cube hU himage hUtarget homega
  simpa [D, chartSingularCubeLocalDataOfChartwiseSmooth] using
    (D.singular_chain_stokes_local_of_extension_eqOn_isOpen
      omegaExt homegaExt hV hone hzero hcube heq)

end SmoothSingularBridgeLocalityFacade

end Stokes

end
