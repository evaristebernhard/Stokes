import Stokes.SingularCube.SmoothBridgeLocalityFacade

/-!
# Smooth singular bridge extension inputs

This module packages the open-neighborhood extension hypotheses used by
`SmoothBridgeLocalityFacade`.

The point is deliberately modest: it does not prove an extension theorem.
Instead it names the exact data that such a theorem should produce for a
smooth singular cube in one chart, and provides theorem-facing wrappers for the
boundary-integral and chain-level singular Stokes statements.
-/

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace Stokes

section SmoothBridgeExtensionInput

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Open-neighborhood extension data for an already constructed
`ChartSingularCubeLocalData`.

The record is the local singular-cube version of the extension problem: give a
globally smooth Euclidean form that agrees with the chart-local form on one
open coordinate neighborhood containing the cube image and both boundary-face
images.
-/
structure ChartSingularCubeLocalExtensionInput {n m : Nat}
    {I : ModelWithCorners Real (Fin m -> Real) H}
    {omega : ManifoldForm I M n}
    (D : ChartSingularCubeLocalData (d := n + 1) I omega) where
  /-- The globally smooth Euclidean extension form. -/
  omegaExt : EuclideanForm m n
  /-- The extension is globally smooth, matching the current singular-cube API. -/
  contDiff_omegaExt : ContDiff Real ⊤ omegaExt
  /-- The open coordinate neighborhood on which the extension agrees locally. -/
  extensionSet : Set (Fin m -> Real)
  /-- The extension neighborhood is open. -/
  isOpen_extensionSet : IsOpen extensionSet
  /-- The high boundary faces lie in the extension neighborhood. -/
  highFace_mem_extensionSet :
    ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
      (singularFace D.cube i 1).toFun x ∈ extensionSet
  /-- The low boundary faces lie in the extension neighborhood. -/
  lowFace_mem_extensionSet :
    ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
      (singularFace D.cube i 0).toFun x ∈ extensionSet
  /-- The full cube image lies in the extension neighborhood. -/
  cube_mem_extensionSet :
    ∀ x ∈ singularParameterCube (n + 1), D.cube.toFun x ∈ extensionSet
  /-- On the extension neighborhood, the extension agrees with the local chart form. -/
  agreesOn_extensionSet : EqOn omegaExt D.localForm extensionSet

namespace ChartSingularCubeLocalExtensionInput

variable {n m : Nat}
variable {I : ModelWithCorners Real (Fin m -> Real) H}
variable {omega : ManifoldForm I M n}
variable {D : ChartSingularCubeLocalData (d := n + 1) I omega}

/-- The high-face neighborhood equality extracted from open extension data. -/
theorem highFace_eventuallyEq
    (E : ChartSingularCubeLocalExtensionInput D) :
    ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
      E.omegaExt =ᶠ[𝓝 ((singularFace D.cube i 1).toFun x)] D.localForm := by
  intro i x hx
  exact eventually_of_mem
    (E.isOpen_extensionSet.mem_nhds (E.highFace_mem_extensionSet i x hx))
    E.agreesOn_extensionSet

/-- The low-face neighborhood equality extracted from open extension data. -/
theorem lowFace_eventuallyEq
    (E : ChartSingularCubeLocalExtensionInput D) :
    ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
      E.omegaExt =ᶠ[𝓝 ((singularFace D.cube i 0).toFun x)] D.localForm := by
  intro i x hx
  exact eventually_of_mem
    (E.isOpen_extensionSet.mem_nhds (E.lowFace_mem_extensionSet i x hx))
    E.agreesOn_extensionSet

/-- The cube-image neighborhood equality extracted from open extension data. -/
theorem cube_eventuallyEq
    (E : ChartSingularCubeLocalExtensionInput D) :
    ∀ x ∈ singularParameterCube (n + 1),
      E.omegaExt =ᶠ[𝓝 (D.cube.toFun x)] D.localForm := by
  intro x hx
  exact eventually_of_mem
    (E.isOpen_extensionSet.mem_nhds (E.cube_mem_extensionSet x hx))
    E.agreesOn_extensionSet

/-- Boundary-integral local singular Stokes from packaged extension data. -/
theorem singular_boundary_stokes_local
    (E : ChartSingularCubeLocalExtensionInput D) :
    SingularCubeStokes.bdryIntegral_singular D.cube D.localForm =
      integrateForm D.cube (fun y => extDeriv D.localForm y) :=
  D.singular_boundary_stokes_local_of_extension_eqOn_isOpen
    E.omegaExt E.contDiff_omegaExt E.isOpen_extensionSet
    E.highFace_mem_extensionSet E.lowFace_mem_extensionSet
    E.cube_mem_extensionSet E.agreesOn_extensionSet

/-- Chain-level local singular Stokes from packaged extension data. -/
theorem singular_chain_stokes_local
    (E : ChartSingularCubeLocalExtensionInput D) :
    integrateChain (singularBoundarySingle D.cube) D.localForm =
      integrateForm D.cube (fun y => extDeriv D.localForm y) :=
  D.singular_chain_stokes_local_of_extension_eqOn_isOpen
    E.omegaExt E.contDiff_omegaExt E.isOpen_extensionSet
    E.highFace_mem_extensionSet E.lowFace_mem_extensionSet
    E.cube_mem_extensionSet E.agreesOn_extensionSet

end ChartSingularCubeLocalExtensionInput

/--
Chartwise extension data for a smooth singular cube written in a manifold
chart.

This is the theorem-facing input intended for the next extension theorem:
besides the usual chartwise-smooth local data, it asks for a globally smooth
Euclidean extension agreeing with the chart representative on one open
coordinate neighborhood containing the cube and face images.
-/
structure ChartwiseSingularCubeOpenExtensionInput {n m : Nat}
    {I : ModelWithCorners Real (Fin m -> Real) H}
    (omega : ManifoldForm I M n)
    (chart : M) (cube : SmoothSingularCube (n + 1) m) where
  /-- The chart-local smoothness neighborhood used to construct local cube data. -/
  smoothSet : Set (Fin m -> Real)
  /-- The chart-local smoothness neighborhood is open. -/
  isOpen_smoothSet : IsOpen smoothSet
  /-- The cube image lies in the chart-local smoothness neighborhood. -/
  cube_mem_smoothSet : MapsTo cube.toFun (singularParameterCube (n + 1)) smoothSet
  /-- The smoothness neighborhood lies in the chart target. -/
  smoothSet_subset_chartTarget : smoothSet ⊆ (extChartAt I chart).target
  /-- The manifold form is chartwise smooth. -/
  chartwiseSmooth : ManifoldForm.ChartwiseSmooth I omega
  /-- The globally smooth Euclidean extension form. -/
  omegaExt : EuclideanForm m n
  /-- The extension is globally smooth, matching the current singular-cube API. -/
  contDiff_omegaExt : ContDiff Real ⊤ omegaExt
  /-- The open coordinate neighborhood on which the extension agrees locally. -/
  extensionSet : Set (Fin m -> Real)
  /-- The extension neighborhood is open. -/
  isOpen_extensionSet : IsOpen extensionSet
  /-- The high boundary faces lie in the extension neighborhood. -/
  highFace_mem_extensionSet :
    ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
      (singularFace cube i 1).toFun x ∈ extensionSet
  /-- The low boundary faces lie in the extension neighborhood. -/
  lowFace_mem_extensionSet :
    ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
      (singularFace cube i 0).toFun x ∈ extensionSet
  /-- The full cube image lies in the extension neighborhood. -/
  cube_mem_extensionSet :
    ∀ x ∈ singularParameterCube (n + 1), cube.toFun x ∈ extensionSet
  /-- On the extension neighborhood, the extension agrees with the local chart form. -/
  agreesOn_extensionSet : EqOn omegaExt (chartLocalForm I chart omega) extensionSet

namespace ChartwiseSingularCubeOpenExtensionInput

variable {n m : Nat}
variable {I : ModelWithCorners Real (Fin m -> Real) H}
variable {omega : ManifoldForm I M n}
variable {chart : M} {cube : SmoothSingularCube (n + 1) m}

/-- The `ChartSingularCubeLocalData` generated by chartwise extension input. -/
abbrev localData
    (E : ChartwiseSingularCubeOpenExtensionInput omega chart cube) :
    ChartSingularCubeLocalData (d := n + 1) I omega :=
  chartSingularCubeLocalDataOfChartwiseSmooth
    (I := I) (omega := omega) chart cube
    E.isOpen_smoothSet E.cube_mem_smoothSet
    E.smoothSet_subset_chartTarget E.chartwiseSmooth

/-- Convert chartwise extension input to local-data extension input. -/
def toLocalExtensionInput
    (E : ChartwiseSingularCubeOpenExtensionInput omega chart cube) :
    ChartSingularCubeLocalExtensionInput E.localData where
  omegaExt := E.omegaExt
  contDiff_omegaExt := E.contDiff_omegaExt
  extensionSet := E.extensionSet
  isOpen_extensionSet := E.isOpen_extensionSet
  highFace_mem_extensionSet := E.highFace_mem_extensionSet
  lowFace_mem_extensionSet := E.lowFace_mem_extensionSet
  cube_mem_extensionSet := E.cube_mem_extensionSet
  agreesOn_extensionSet := E.agreesOn_extensionSet

/-- Boundary-integral smooth singular Stokes from packaged chartwise extension input. -/
theorem boundary_stokes
    (E : ChartwiseSingularCubeOpenExtensionInput omega chart cube) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  simpa [localData, toLocalExtensionInput, chartSingularCubeLocalDataOfChartwiseSmooth]
    using E.toLocalExtensionInput.singular_boundary_stokes_local

/-- Chain-level smooth singular Stokes from packaged chartwise extension input. -/
theorem chain_stokes
    (E : ChartwiseSingularCubeOpenExtensionInput omega chart cube) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  simpa [localData, toLocalExtensionInput, chartSingularCubeLocalDataOfChartwiseSmooth]
    using E.toLocalExtensionInput.singular_chain_stokes_local

end ChartwiseSingularCubeOpenExtensionInput

/--
Boundary-integral facade using the packaged chartwise extension input record.
-/
theorem chartwise_singular_boundary_stokes_of_openExtensionInput {n m : Nat}
    {I : ModelWithCorners Real (Fin m -> Real) H}
    {omega : ManifoldForm I M n}
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    (E : ChartwiseSingularCubeOpenExtensionInput omega chart cube) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  E.boundary_stokes

/--
Chain-level facade using the packaged chartwise extension input record.
-/
theorem chartwise_singular_chain_stokes_of_openExtensionInput {n m : Nat}
    {I : ModelWithCorners Real (Fin m -> Real) H}
    {omega : ManifoldForm I M n}
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    (E : ChartwiseSingularCubeOpenExtensionInput omega chart cube) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  E.chain_stokes

/--
The proposition shape that a future chart-local extension theorem should
produce.  Keeping it as a proposition, rather than a theorem here, makes the
remaining analytic dependency explicit without adding a placeholder.
-/
def ExistsChartwiseSingularCubeOpenExtensionInput {n m : Nat}
    {I : ModelWithCorners Real (Fin m -> Real) H}
    (omega : ManifoldForm I M n)
    (chart : M) (cube : SmoothSingularCube (n + 1) m) : Prop :=
  ∃ _E : ChartwiseSingularCubeOpenExtensionInput omega chart cube, True

/--
Boundary-integral facade from the existential extension-theorem output shape.
-/
theorem chartwise_singular_boundary_stokes_of_exists_openExtensionInput {n m : Nat}
    {I : ModelWithCorners Real (Fin m -> Real) H}
    {omega : ManifoldForm I M n}
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    (hE : ExistsChartwiseSingularCubeOpenExtensionInput omega chart cube) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  rcases hE with ⟨E, _⟩
  exact chartwise_singular_boundary_stokes_of_openExtensionInput chart cube E

/--
Chain-level facade from the existential extension-theorem output shape.
-/
theorem chartwise_singular_chain_stokes_of_exists_openExtensionInput {n m : Nat}
    {I : ModelWithCorners Real (Fin m -> Real) H}
    {omega : ManifoldForm I M n}
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    (hE : ExistsChartwiseSingularCubeOpenExtensionInput omega chart cube) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  rcases hE with ⟨E, _⟩
  exact chartwise_singular_chain_stokes_of_openExtensionInput chart cube E

end SmoothBridgeExtensionInput

end Stokes

end
