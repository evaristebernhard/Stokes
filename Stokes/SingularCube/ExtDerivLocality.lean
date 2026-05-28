import Stokes.SingularCube.IntegralCongruence

/-!
# Locality wrappers for `extDeriv` in the singular-cube bridge

This file packages the mathlib theorem
`Filter.EventuallyEq.extDeriv_eq` in the shapes needed by the smooth singular
bridge.  The analytic content is deliberately small: if two Euclidean forms
agree near a point, then their exterior derivatives agree at that point.

The later extension step can therefore provide local neighborhood equality on
the cube and face images, and this module turns it into the pointwise
`hderiv`, `hone`, and `hzero` hypotheses used by
`Stokes.SingularCube.IntegralCongruence`.
-/

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace Stokes

section EuclideanFormLocality

variable {m n : Nat}
variable {omega eta : EuclideanForm m n}
variable {y : Fin m → Real}

/-- Eventually equal Euclidean forms have equal exterior derivatives at the point. -/
theorem euclideanForm_extDeriv_eq_of_eventuallyEq
    (h : omega =ᶠ[𝓝 y] eta) :
    extDeriv omega y = extDeriv eta y :=
  h.extDeriv_eq

/-- Equality on a neighborhood is enough to identify exterior derivatives. -/
theorem euclideanForm_extDeriv_eq_of_eqOn_mem_nhds
    {s : Set (Fin m → Real)}
    (hs : s ∈ 𝓝 y) (h : EqOn omega eta s) :
    extDeriv omega y = extDeriv eta y :=
  euclideanForm_extDeriv_eq_of_eventuallyEq (eventually_of_mem hs h)

/-- Eventually equal Euclidean forms are equal at the base point. -/
theorem euclideanForm_eq_of_eventuallyEq
    (h : omega =ᶠ[𝓝 y] eta) :
    omega y = eta y :=
  h.self_of_nhds

/-- Equality on a neighborhood gives equality at the base point. -/
theorem euclideanForm_eq_of_eqOn_mem_nhds
    {s : Set (Fin m → Real)}
    (hs : s ∈ 𝓝 y) (h : EqOn omega eta s) :
    omega y = eta y :=
  euclideanForm_eq_of_eventuallyEq (eventually_of_mem hs h)

end EuclideanFormLocality

section CubeImageLocality

variable {m n : Nat}

/--
The `hderiv` hypothesis expected by
`integrateForm_extDeriv_congr_on_image`, derived from pointwise neighborhood
equality along the cube image.
-/
theorem extDeriv_eq_on_cube_image_of_eventuallyEq
    (sigma : SmoothSingularCube (n + 1) m)
    {omega eta : EuclideanForm m n}
    (h :
      ∀ x ∈ singularParameterCube (n + 1),
        omega =ᶠ[𝓝 (sigma.toFun x)] eta) :
    ∀ x ∈ singularParameterCube (n + 1),
      extDeriv omega (sigma.toFun x) =
        extDeriv eta (sigma.toFun x) := by
  intro x hx
  exact euclideanForm_extDeriv_eq_of_eventuallyEq (h x hx)

/--
The same cube-image derivative congruence from equality on a neighborhood of
each image point.
-/
theorem extDeriv_eq_on_cube_image_of_eqOn_mem_nhds
    (sigma : SmoothSingularCube (n + 1) m)
    {omega eta : EuclideanForm m n}
    (h :
      ∀ x ∈ singularParameterCube (n + 1),
        ∃ s : Set (Fin m → Real),
          s ∈ 𝓝 (sigma.toFun x) ∧ EqOn omega eta s) :
    ∀ x ∈ singularParameterCube (n + 1),
      extDeriv omega (sigma.toFun x) =
        extDeriv eta (sigma.toFun x) := by
  intro x hx
  rcases h x hx with ⟨s, hs, heq⟩
  exact euclideanForm_extDeriv_eq_of_eqOn_mem_nhds hs heq

/--
Open-neighborhood version for the common extension case: one open set contains
the cube image and carries equality of the two forms.
-/
theorem extDeriv_eq_on_cube_image_of_eqOn_isOpen
    (sigma : SmoothSingularCube (n + 1) m)
    {omega eta : EuclideanForm m n}
    {U : Set (Fin m → Real)}
    (hU : IsOpen U)
    (himage :
      ∀ x ∈ singularParameterCube (n + 1), sigma.toFun x ∈ U)
    (heq : EqOn omega eta U) :
    ∀ x ∈ singularParameterCube (n + 1),
      extDeriv omega (sigma.toFun x) =
        extDeriv eta (sigma.toFun x) := by
  intro x hx
  exact euclideanForm_extDeriv_eq_of_eqOn_mem_nhds
    (hU.mem_nhds (himage x hx)) heq

/--
Face-image pointwise equality from neighborhood equality.  This is the `hone`
or `hzero` shape required by the boundary congruence lemmas.
-/
theorem form_eq_on_face_image_of_eventuallyEq
    (sigma : SmoothSingularCube (n + 1) m)
    {omega eta : EuclideanForm m n}
    (epsilon : Real)
    (h :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        omega =ᶠ[𝓝 ((singularFace sigma i epsilon).toFun x)] eta) :
    ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
      omega ((singularFace sigma i epsilon).toFun x) =
        eta ((singularFace sigma i epsilon).toFun x) := by
  intro i x hx
  exact euclideanForm_eq_of_eventuallyEq (h i x hx)

/--
Face-image pointwise equality from equality on a neighborhood of each face
image point.
-/
theorem form_eq_on_face_image_of_eqOn_mem_nhds
    (sigma : SmoothSingularCube (n + 1) m)
    {omega eta : EuclideanForm m n}
    (epsilon : Real)
    (h :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        ∃ s : Set (Fin m → Real),
          s ∈ 𝓝 ((singularFace sigma i epsilon).toFun x) ∧ EqOn omega eta s) :
    ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
      omega ((singularFace sigma i epsilon).toFun x) =
        eta ((singularFace sigma i epsilon).toFun x) := by
  intro i x hx
  rcases h i x hx with ⟨s, hs, heq⟩
  exact euclideanForm_eq_of_eqOn_mem_nhds hs heq

/--
Face-image pointwise equality from equality on one open set containing the face
image.
-/
theorem form_eq_on_face_image_of_eqOn_isOpen
    (sigma : SmoothSingularCube (n + 1) m)
    {omega eta : EuclideanForm m n}
    (epsilon : Real)
    {U : Set (Fin m → Real)}
    (hU : IsOpen U)
    (himage :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        (singularFace sigma i epsilon).toFun x ∈ U)
    (heq : EqOn omega eta U) :
    ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
      omega ((singularFace sigma i epsilon).toFun x) =
        eta ((singularFace sigma i epsilon).toFun x) := by
  intro i x hx
  exact euclideanForm_eq_of_eqOn_mem_nhds
    (hU.mem_nhds (himage i x hx)) heq

end CubeImageLocality

namespace ChartSingularCubeLocalData

section LocalExtensionLocality

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n m : Nat}
variable {I : ModelWithCorners Real (Fin m → Real) H}
variable {omega : ManifoldForm I M n}

/--
Local singular Stokes from a globally smooth extension and neighborhood
equality on the cube and face images.
-/
theorem singular_boundary_stokes_local_of_extension_eventuallyEq
    (D : ChartSingularCubeLocalData (d := n + 1) I omega)
    (omegaExt : EuclideanForm m n)
    (homegaExt : ContDiff Real ⊤ omegaExt)
    (hone :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        omegaExt =ᶠ[𝓝 ((singularFace D.cube i 1).toFun x)] D.localForm)
    (hzero :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        omegaExt =ᶠ[𝓝 ((singularFace D.cube i 0).toFun x)] D.localForm)
    (hderiv :
      ∀ x ∈ singularParameterCube (n + 1),
        omegaExt =ᶠ[𝓝 (D.cube.toFun x)] D.localForm) :
    SingularCubeStokes.bdryIntegral_singular D.cube D.localForm =
      integrateForm D.cube (fun y => extDeriv D.localForm y) :=
  D.singular_boundary_stokes_local_of_extension_congruence
    omegaExt homegaExt
    (form_eq_on_face_image_of_eventuallyEq D.cube 1 hone)
    (form_eq_on_face_image_of_eventuallyEq D.cube 0 hzero)
    (extDeriv_eq_on_cube_image_of_eventuallyEq D.cube hderiv)

/--
Chain-level local singular Stokes from a globally smooth extension and
neighborhood equality on the cube and face images.
-/
theorem singular_chain_stokes_local_of_extension_eventuallyEq
    (D : ChartSingularCubeLocalData (d := n + 1) I omega)
    (omegaExt : EuclideanForm m n)
    (homegaExt : ContDiff Real ⊤ omegaExt)
    (hone :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        omegaExt =ᶠ[𝓝 ((singularFace D.cube i 1).toFun x)] D.localForm)
    (hzero :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        omegaExt =ᶠ[𝓝 ((singularFace D.cube i 0).toFun x)] D.localForm)
    (hderiv :
      ∀ x ∈ singularParameterCube (n + 1),
        omegaExt =ᶠ[𝓝 (D.cube.toFun x)] D.localForm) :
    integrateChain (singularBoundarySingle D.cube) D.localForm =
      integrateForm D.cube (fun y => extDeriv D.localForm y) :=
  D.singular_chain_stokes_local_of_extension_congruence
    omegaExt homegaExt
    (form_eq_on_face_image_of_eventuallyEq D.cube 1 hone)
    (form_eq_on_face_image_of_eventuallyEq D.cube 0 hzero)
    (extDeriv_eq_on_cube_image_of_eventuallyEq D.cube hderiv)

/--
Local singular Stokes from equality on neighborhoods of every cube and face
image point.
-/
theorem singular_boundary_stokes_local_of_extension_eqOn_mem_nhds
    (D : ChartSingularCubeLocalData (d := n + 1) I omega)
    (omegaExt : EuclideanForm m n)
    (homegaExt : ContDiff Real ⊤ omegaExt)
    (hone :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        ∃ s : Set (Fin m → Real),
          s ∈ 𝓝 ((singularFace D.cube i 1).toFun x) ∧ EqOn omegaExt D.localForm s)
    (hzero :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        ∃ s : Set (Fin m → Real),
          s ∈ 𝓝 ((singularFace D.cube i 0).toFun x) ∧ EqOn omegaExt D.localForm s)
    (hderiv :
      ∀ x ∈ singularParameterCube (n + 1),
        ∃ s : Set (Fin m → Real),
          s ∈ 𝓝 (D.cube.toFun x) ∧ EqOn omegaExt D.localForm s) :
    SingularCubeStokes.bdryIntegral_singular D.cube D.localForm =
      integrateForm D.cube (fun y => extDeriv D.localForm y) :=
  D.singular_boundary_stokes_local_of_extension_congruence
    omegaExt homegaExt
    (form_eq_on_face_image_of_eqOn_mem_nhds D.cube 1 hone)
    (form_eq_on_face_image_of_eqOn_mem_nhds D.cube 0 hzero)
    (extDeriv_eq_on_cube_image_of_eqOn_mem_nhds D.cube hderiv)

/--
Chain-level local singular Stokes from equality on neighborhoods of every cube
and face image point.
-/
theorem singular_chain_stokes_local_of_extension_eqOn_mem_nhds
    (D : ChartSingularCubeLocalData (d := n + 1) I omega)
    (omegaExt : EuclideanForm m n)
    (homegaExt : ContDiff Real ⊤ omegaExt)
    (hone :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        ∃ s : Set (Fin m → Real),
          s ∈ 𝓝 ((singularFace D.cube i 1).toFun x) ∧ EqOn omegaExt D.localForm s)
    (hzero :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        ∃ s : Set (Fin m → Real),
          s ∈ 𝓝 ((singularFace D.cube i 0).toFun x) ∧ EqOn omegaExt D.localForm s)
    (hderiv :
      ∀ x ∈ singularParameterCube (n + 1),
        ∃ s : Set (Fin m → Real),
          s ∈ 𝓝 (D.cube.toFun x) ∧ EqOn omegaExt D.localForm s) :
    integrateChain (singularBoundarySingle D.cube) D.localForm =
      integrateForm D.cube (fun y => extDeriv D.localForm y) :=
  D.singular_chain_stokes_local_of_extension_congruence
    omegaExt homegaExt
    (form_eq_on_face_image_of_eqOn_mem_nhds D.cube 1 hone)
    (form_eq_on_face_image_of_eqOn_mem_nhds D.cube 0 hzero)
    (extDeriv_eq_on_cube_image_of_eqOn_mem_nhds D.cube hderiv)

/--
Open-set version: one open coordinate neighborhood contains the cube and face
images, and the extension agrees with the local chart form on that open set.
-/
theorem singular_boundary_stokes_local_of_extension_eqOn_isOpen
    (D : ChartSingularCubeLocalData (d := n + 1) I omega)
    (omegaExt : EuclideanForm m n)
    (homegaExt : ContDiff Real ⊤ omegaExt)
    {U : Set (Fin m → Real)}
    (hU : IsOpen U)
    (hone :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        (singularFace D.cube i 1).toFun x ∈ U)
    (hzero :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        (singularFace D.cube i 0).toFun x ∈ U)
    (hcube :
      ∀ x ∈ singularParameterCube (n + 1), D.cube.toFun x ∈ U)
    (heq : EqOn omegaExt D.localForm U) :
    SingularCubeStokes.bdryIntegral_singular D.cube D.localForm =
      integrateForm D.cube (fun y => extDeriv D.localForm y) :=
  D.singular_boundary_stokes_local_of_extension_congruence
    omegaExt homegaExt
    (form_eq_on_face_image_of_eqOn_isOpen D.cube 1 hU hone heq)
    (form_eq_on_face_image_of_eqOn_isOpen D.cube 0 hU hzero heq)
    (extDeriv_eq_on_cube_image_of_eqOn_isOpen D.cube hU hcube heq)

/--
Chain-level open-set version of
`singular_boundary_stokes_local_of_extension_eqOn_isOpen`.
-/
theorem singular_chain_stokes_local_of_extension_eqOn_isOpen
    (D : ChartSingularCubeLocalData (d := n + 1) I omega)
    (omegaExt : EuclideanForm m n)
    (homegaExt : ContDiff Real ⊤ omegaExt)
    {U : Set (Fin m → Real)}
    (hU : IsOpen U)
    (hone :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        (singularFace D.cube i 1).toFun x ∈ U)
    (hzero :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        (singularFace D.cube i 0).toFun x ∈ U)
    (hcube :
      ∀ x ∈ singularParameterCube (n + 1), D.cube.toFun x ∈ U)
    (heq : EqOn omegaExt D.localForm U) :
    integrateChain (singularBoundarySingle D.cube) D.localForm =
      integrateForm D.cube (fun y => extDeriv D.localForm y) :=
  D.singular_chain_stokes_local_of_extension_congruence
    omegaExt homegaExt
    (form_eq_on_face_image_of_eqOn_isOpen D.cube 1 hU hone heq)
    (form_eq_on_face_image_of_eqOn_isOpen D.cube 0 hU hzero heq)
    (extDeriv_eq_on_cube_image_of_eqOn_isOpen D.cube hU hcube heq)

end LocalExtensionLocality

end ChartSingularCubeLocalData

end Stokes

end
