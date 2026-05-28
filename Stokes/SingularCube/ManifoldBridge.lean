import Stokes.SingularCube
import Stokes.ManifoldForm

/-!
# Smooth singular cubes in manifold charts

This module is a clean-room bridge between the smooth singular cube API and the
current manifold-chart route.

The prior-art singular-cube layer integrates Euclidean forms
`EuclideanForm m k` along smooth maps `Fin d -> Real -> Fin m -> Real`.  The
manifold route represents a form in a chart by
`ManifoldForm.inChart I x0 omega`.  The definitions below name that
identification and package the local hypotheses that later let a smooth
singular cube be treated as a chart-local parameterization.

The key intentional gap is explicit: the imported singular Stokes theorem asks
for a globally `ContDiff` Euclidean form, while the manifold route usually
supplies `ContDiffOn` on a chart neighborhood.  The local data record therefore
stores the `ContDiffOn` statement, and the theorem wrappers below take the
stronger global smoothness hypothesis only at the point where the existing
singular-cube theorem is invoked.
-/

noncomputable section

open Set
open scoped Manifold Topology

namespace Stokes

section SingularCubeManifoldBridge

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- The parameter cube used by the smooth singular-cube integration layer. -/
def singularParameterCube (d : Nat) : Set (Fin d → Real) :=
  Icc (fun _ : Fin d => (0 : Real)) (fun _ => 1)

/--
The chart expression of a manifold form, viewed as the Euclidean form expected
by the smooth singular-cube API.
-/
abbrev chartLocalForm {m k : Nat}
    (I : ModelWithCorners Real (Fin m → Real) H) (x0 : M)
    (omega : ManifoldForm I M k) : EuclideanForm m k :=
  ManifoldForm.inChart I x0 omega

/--
A smooth singular cube in model coordinates, interpreted as a map into the
manifold through the inverse of the extended chart at `x0`.
-/
def chartCubeMap {d m : Nat}
    (I : ModelWithCorners Real (Fin m → Real) H) (x0 : M)
    (sigma : SmoothSingularCube d m) : (Fin d → Real) → M :=
  fun x => (extChartAt I x0).symm (sigma.toFun x)

/--
The chart-coordinate pullback of a manifold form along a smooth singular cube.

This is definitionally the prior-art `pullbackForm` applied to the chart
representative `ManifoldForm.inChart`.
-/
abbrev chartCubePullback {d m k : Nat}
    (I : ModelWithCorners Real (Fin m → Real) H) (x0 : M)
    (sigma : SmoothSingularCube d m) (omega : ManifoldForm I M k) :
    (Fin d → Real) → (Fin d → Real) [⋀^Fin k]→L[Real] Real :=
  pullbackForm sigma (chartLocalForm I x0 omega)

@[simp]
theorem chartCubePullback_apply {d m k : Nat}
    (I : ModelWithCorners Real (Fin m → Real) H) (x0 : M)
    (sigma : SmoothSingularCube d m) (omega : ManifoldForm I M k)
    (x : Fin d → Real) :
    chartCubePullback I x0 sigma omega x =
      (ManifoldForm.inChart I x0 omega (sigma.toFun x)).compContinuousLinearMap
        (fderiv Real sigma.toFun x) :=
  rfl

/--
On points whose local coordinates lie in the chart target, interpreting a
coordinate cube as a manifold map and then reading it back in the same chart
recovers the original coordinate cube.
-/
theorem extChartAt_chartCubeMap_eq {d m : Nat}
    (I : ModelWithCorners Real (Fin m → Real) H) (x0 : M)
    (sigma : SmoothSingularCube d m) {x : Fin d → Real}
    (hx : sigma.toFun x ∈ (extChartAt I x0).target) :
    (extChartAt I x0) (chartCubeMap I x0 sigma x) = sigma.toFun x :=
  (extChartAt I x0).right_inv hx

/--
Local bridge data for a smooth singular cube that lives in one manifold chart.

The record exposes exactly the interface mismatch:
* `cube` is the globally smooth coordinate cube required by the singular-cube
  API;
* `localForm_contDiffOn` is the chart-local smoothness statement naturally
  produced by the manifold route;
* `unitCube_image_subset_smoothSet` and `smoothSet_subset_chartTarget` say the
  cube is used only where that chart representative is meaningful.
-/
structure ChartSingularCubeLocalData {d m k : Nat}
    (I : ModelWithCorners Real (Fin m → Real) H)
    (omega : ManifoldForm I M k) where
  /-- The chart in which the singular cube is written. -/
  chart : M
  /-- The smooth singular cube in chart coordinates. -/
  cube : SmoothSingularCube d m
  /-- An open model-space neighborhood on which the chart representative is smooth. -/
  smoothSet : Set (Fin m → Real)
  /-- The recorded smoothness neighborhood is open. -/
  isOpen_smoothSet : IsOpen smoothSet
  /-- The parameter unit cube maps into the smoothness neighborhood. -/
  unitCube_image_subset_smoothSet :
    MapsTo cube.toFun (singularParameterCube d) smoothSet
  /-- The smoothness neighborhood lies in the chart target. -/
  smoothSet_subset_chartTarget : smoothSet ⊆ (extChartAt I chart).target
  /-- The manifold form's chart representative is smooth on the recorded neighborhood. -/
  localForm_contDiffOn :
    ContDiffOn Real ⊤ (chartLocalForm I chart omega) smoothSet

namespace ChartSingularCubeLocalData

variable {d m k : Nat}
variable {I : ModelWithCorners Real (Fin m → Real) H}
variable {omega : ManifoldForm I M k}

/-- The local Euclidean form attached to the bridge data. -/
abbrev localForm (D : ChartSingularCubeLocalData (d := d) I omega) : EuclideanForm m k :=
  chartLocalForm I D.chart omega

/-- The prior-art pullback form attached to the bridge data. -/
abbrev localPullback
    (D : ChartSingularCubeLocalData (d := d) I omega) :
    (Fin d → Real) → (Fin d → Real) [⋀^Fin k]→L[Real] Real :=
  pullbackForm D.cube D.localForm

/-- The manifold-valued map obtained by sending the coordinate cube through the chart. -/
abbrev manifoldMap (D : ChartSingularCubeLocalData (d := d) I omega) :
    (Fin d → Real) → M :=
  chartCubeMap I D.chart D.cube

@[simp]
theorem localPullback_apply
    (D : ChartSingularCubeLocalData (d := d) I omega) (x : Fin d → Real) :
    D.localPullback x =
      (D.localForm (D.cube.toFun x)).compContinuousLinearMap
        (fderiv Real D.cube.toFun x) :=
  rfl

/-- The cube lands in the recorded smoothness neighborhood on the parameter cube. -/
theorem cube_mem_smoothSet
    (D : ChartSingularCubeLocalData (d := d) I omega)
    {x : Fin d → Real} (hx : x ∈ singularParameterCube d) :
    D.cube.toFun x ∈ D.smoothSet :=
  D.unitCube_image_subset_smoothSet hx

/-- The cube lands in the chart target on the parameter cube. -/
theorem cube_mem_chartTarget
    (D : ChartSingularCubeLocalData (d := d) I omega)
    {x : Fin d → Real} (hx : x ∈ singularParameterCube d) :
    D.cube.toFun x ∈ (extChartAt I D.chart).target :=
  D.smoothSet_subset_chartTarget (D.cube_mem_smoothSet hx)

/--
On the parameter cube, the manifold map represented by the local coordinate
cube reads back to the original coordinate cube in the selected chart.
-/
theorem extChartAt_manifoldMap_eq
    (D : ChartSingularCubeLocalData (d := d) I omega)
    {x : Fin d → Real} (hx : x ∈ singularParameterCube d) :
    (extChartAt I D.chart) (D.manifoldMap x) = D.cube.toFun x :=
  extChartAt_chartCubeMap_eq I D.chart D.cube (D.cube_mem_chartTarget hx)

/-- Restrict the recorded local smoothness statement to a smaller set. -/
theorem localForm_contDiffOn_of_subset
    (D : ChartSingularCubeLocalData (d := d) I omega)
    {s : Set (Fin m → Real)} (hs : s ⊆ D.smoothSet) :
    ContDiffOn Real ⊤ D.localForm s :=
  D.localForm_contDiffOn.mono hs

/--
Constructor from the current chartwise-smooth manifold-form API.

This is the common case for the manifold route: once a chartwise-smooth form is
available and a cube image is known to lie in a chart-target neighborhood, the
recorded local smoothness follows from `ManifoldForm.ChartwiseSmooth`.
-/
def ofChartwiseSmooth
    (chart : M) (cube : SmoothSingularCube d m)
    {U : Set (Fin m → Real)}
    (hU : IsOpen U)
    (himage : MapsTo cube.toFun (singularParameterCube d) U)
    (hUtarget : U ⊆ (extChartAt I chart).target)
    (homega : ManifoldForm.ChartwiseSmooth I omega) :
    ChartSingularCubeLocalData (d := d) I omega where
  chart := chart
  cube := cube
  smoothSet := U
  isOpen_smoothSet := hU
  unitCube_image_subset_smoothSet := himage
  smoothSet_subset_chartTarget := hUtarget
  localForm_contDiffOn := homega.contDiffOn_inChart (I := I) chart hUtarget

/--
Existing singular-cube naturality specialized to a manifold form written in a
chart.

The global smoothness hypothesis is deliberately explicit; the local data
itself only records the weaker `ContDiffOn` statement supplied by the manifold
route.
-/
theorem singular_pullback_extDeriv_local
    {n m : Nat} {I : ModelWithCorners Real (Fin m → Real) H}
    {omega : ManifoldForm I M n}
    (D : ChartSingularCubeLocalData (d := n + 1) I omega)
    (homega_global : ContDiff Real ⊤ D.localForm)
    (x : Fin (n + 1) → Real) :
    extDeriv D.localPullback x =
      (extDeriv D.localForm (D.cube.toFun x)).compContinuousLinearMap
        (fderiv Real D.cube.toFun x) :=
  singular_pullback_extDeriv D.cube D.localForm homega_global x

/--
Existing chain-level singular Stokes specialized to a manifold form written in
one chart.
-/
theorem singular_chain_stokes_local
    {n m : Nat} {I : ModelWithCorners Real (Fin m → Real) H}
    {omega : ManifoldForm I M n}
    (D : ChartSingularCubeLocalData (d := n + 1) I omega)
    (homega_global : ContDiff Real ⊤ D.localForm) :
    integrateChain (singularBoundarySingle D.cube) D.localForm =
      integrateForm D.cube (fun y => extDeriv D.localForm y) :=
  singular_cube_chain_stokes D.cube D.localForm homega_global

/--
The same specialization in the boundary-integral orientation used by the
singular-cube API.
-/
theorem singular_boundary_stokes_local
    {n m : Nat} {I : ModelWithCorners Real (Fin m → Real) H}
    {omega : ManifoldForm I M n}
    (D : ChartSingularCubeLocalData (d := n + 1) I omega)
    (homega_global : ContDiff Real ⊤ D.localForm) :
    SingularCubeStokes.bdryIntegral_singular D.cube D.localForm =
      integrateForm D.cube (fun y => extDeriv D.localForm y) :=
  singular_cube_boundary_stokes D.cube D.localForm homega_global

end ChartSingularCubeLocalData

end SingularCubeManifoldBridge

end Stokes

end
