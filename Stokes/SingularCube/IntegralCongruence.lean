import Stokes.SingularCube.ManifoldBridge

/-!
# Congruence lemmas for smooth singular-cube integrals

This file isolates the clean-room congruence facts needed by the next local
extension step in the smooth singular-cube bridge.

The key point is modest but useful: the imported singular-cube integrals only
sample a Euclidean form on the image of the parameter cube, and the boundary
integral only samples it on the images of the boundary faces.  Thus an
extension theorem can invoke global smooth Stokes for a globally smooth
extension, then replace the extension by the local chart representative via
these congruence lemmas.
-/

noncomputable section

open Set Finset MeasureTheory
open scoped Manifold Topology

namespace Stokes

section IntegralCongruence

variable {d n m : Nat}

/--
If two top-degree Euclidean forms agree on the image of a smooth singular cube,
then their integrals over that cube agree.
-/
theorem integrateForm_congr_on_image
    (sigma : SmoothSingularCube d m)
    {omega eta : EuclideanForm m d}
    (h :
      ∀ x ∈ singularParameterCube d,
        omega (sigma.toFun x) = eta (sigma.toFun x)) :
    integrateForm sigma omega = integrateForm sigma eta := by
  unfold integrateForm SingularCubeStokes.integrateForm
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro x hx
  unfold SingularCubeStokes.pullbackForm
  have hx' : x ∈ singularParameterCube d := by
    simpa [singularParameterCube] using hx
  change
    ((omega (sigma.toFun x)).compContinuousLinearMap (fderiv Real sigma.toFun x))
        (fun j => Pi.single j 1) =
      ((eta (sigma.toFun x)).compContinuousLinearMap (fderiv Real sigma.toFun x))
        (fun j => Pi.single j 1)
  rw [h x hx']

/--
Global pointwise equality is a common special case of
`integrateForm_congr_on_image`.
-/
theorem integrateForm_congr
    (sigma : SmoothSingularCube d m)
    {omega eta : EuclideanForm m d}
    (h : ∀ y, omega y = eta y) :
    integrateForm sigma omega = integrateForm sigma eta :=
  integrateForm_congr_on_image sigma (by
    intro x _
    exact h (sigma.toFun x))

/--
If exterior derivatives of two `n`-forms agree on the image of an
`(n+1)`-cube, then their interior singular-cube integrals agree.
-/
theorem integrateForm_extDeriv_congr_on_image
    (sigma : SmoothSingularCube (n + 1) m)
    {omega eta : EuclideanForm m n}
    (h :
      ∀ x ∈ singularParameterCube (n + 1),
        extDeriv omega (sigma.toFun x) = extDeriv eta (sigma.toFun x)) :
    integrateForm sigma (fun y => extDeriv omega y) =
      integrateForm sigma (fun y => extDeriv eta y) :=
  integrateForm_congr_on_image sigma h

/--
If two `n`-forms agree on every high and low face image of an `(n+1)`-cube,
then their oriented boundary integrals agree.
-/
theorem bdryIntegral_singular_congr_on_faces
    (sigma : SmoothSingularCube (n + 1) m)
    {omega eta : EuclideanForm m n}
    (hone :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        omega ((singularFace sigma i 1).toFun x) =
          eta ((singularFace sigma i 1).toFun x))
    (hzero :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        omega ((singularFace sigma i 0).toFun x) =
          eta ((singularFace sigma i 0).toFun x)) :
    SingularCubeStokes.bdryIntegral_singular sigma omega =
      SingularCubeStokes.bdryIntegral_singular sigma eta := by
  unfold SingularCubeStokes.bdryIntegral_singular
  apply Finset.sum_congr rfl
  intro i _
  have hone_i :
      SingularCubeStokes.integrateForm (SingularCubeStokes.singularFace sigma i 1) omega =
        SingularCubeStokes.integrateForm (SingularCubeStokes.singularFace sigma i 1) eta :=
    integrateForm_congr_on_image (singularFace sigma i 1) (hone i)
  have hzero_i :
      SingularCubeStokes.integrateForm (SingularCubeStokes.singularFace sigma i 0) omega =
        SingularCubeStokes.integrateForm (SingularCubeStokes.singularFace sigma i 0) eta :=
    integrateForm_congr_on_image (singularFace sigma i 0) (hzero i)
  rw [hone_i, hzero_i]

/--
The same boundary-face congruence in the finite-chain formulation of the
boundary of one singular cube.
-/
theorem integrateChain_singularBoundarySingle_congr_on_faces
    (sigma : SmoothSingularCube (n + 1) m)
    {omega eta : EuclideanForm m n}
    (hone :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        omega ((singularFace sigma i 1).toFun x) =
          eta ((singularFace sigma i 1).toFun x))
    (hzero :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        omega ((singularFace sigma i 0).toFun x) =
          eta ((singularFace sigma i 0).toFun x)) :
    integrateChain (singularBoundarySingle sigma) omega =
      integrateChain (singularBoundarySingle sigma) eta := by
  change
    SingularCubeStokes.integrateChain
        (SingularCubeStokes.singularBoundarySingle sigma) omega =
      SingularCubeStokes.integrateChain
        (SingularCubeStokes.singularBoundarySingle sigma) eta
  rw [SingularCubeStokes.integrateChain_singularBoundarySingle,
    SingularCubeStokes.integrateChain_singularBoundarySingle]
  exact bdryIntegral_singular_congr_on_faces sigma hone hzero

end IntegralCongruence

namespace ChartSingularCubeLocalData

section LocalExtensionCongruence

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n m : Nat}
variable {I : ModelWithCorners Real (Fin m -> Real) H}
variable {omega : ManifoldForm I M n}

/--
Boundary-integral local Stokes from a globally smooth extension, assuming the
extension agrees with the local chart representative on all boundary face
images and its exterior derivative agrees on the cube image.

The remaining analytic blocker for the planned stronger theorem is exactly the
last hypothesis: it should eventually be derived from equality on a
neighborhood of the cube image.
-/
theorem singular_boundary_stokes_local_of_extension_congruence
    (D : ChartSingularCubeLocalData (d := n + 1) I omega)
    (omegaExt : EuclideanForm m n)
    (homegaExt : ContDiff Real ⊤ omegaExt)
    (hone :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        omegaExt ((singularFace D.cube i 1).toFun x) =
          D.localForm ((singularFace D.cube i 1).toFun x))
    (hzero :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        omegaExt ((singularFace D.cube i 0).toFun x) =
          D.localForm ((singularFace D.cube i 0).toFun x))
    (hderiv :
      ∀ x ∈ singularParameterCube (n + 1),
        extDeriv omegaExt (D.cube.toFun x) =
          extDeriv D.localForm (D.cube.toFun x)) :
    SingularCubeStokes.bdryIntegral_singular D.cube D.localForm =
      integrateForm D.cube (fun y => extDeriv D.localForm y) := by
  calc
    SingularCubeStokes.bdryIntegral_singular D.cube D.localForm =
        SingularCubeStokes.bdryIntegral_singular D.cube omegaExt := by
      exact (bdryIntegral_singular_congr_on_faces D.cube hone hzero).symm
    _ = integrateForm D.cube (fun y => extDeriv omegaExt y) :=
      singular_cube_boundary_stokes D.cube omegaExt homegaExt
    _ = integrateForm D.cube (fun y => extDeriv D.localForm y) :=
      integrateForm_extDeriv_congr_on_image D.cube hderiv

/--
Chain-level version of
`singular_boundary_stokes_local_of_extension_congruence`.
-/
theorem singular_chain_stokes_local_of_extension_congruence
    (D : ChartSingularCubeLocalData (d := n + 1) I omega)
    (omegaExt : EuclideanForm m n)
    (homegaExt : ContDiff Real ⊤ omegaExt)
    (hone :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        omegaExt ((singularFace D.cube i 1).toFun x) =
          D.localForm ((singularFace D.cube i 1).toFun x))
    (hzero :
      ∀ i : Fin (n + 1), ∀ x ∈ singularParameterCube n,
        omegaExt ((singularFace D.cube i 0).toFun x) =
          D.localForm ((singularFace D.cube i 0).toFun x))
    (hderiv :
      ∀ x ∈ singularParameterCube (n + 1),
        extDeriv omegaExt (D.cube.toFun x) =
          extDeriv D.localForm (D.cube.toFun x)) :
    integrateChain (singularBoundarySingle D.cube) D.localForm =
      integrateForm D.cube (fun y => extDeriv D.localForm y) := by
  calc
    integrateChain (singularBoundarySingle D.cube) D.localForm =
        integrateChain (singularBoundarySingle D.cube) omegaExt := by
      exact (integrateChain_singularBoundarySingle_congr_on_faces D.cube hone hzero).symm
    _ = integrateForm D.cube (fun y => extDeriv omegaExt y) :=
      singular_cube_chain_stokes D.cube omegaExt homegaExt
    _ = integrateForm D.cube (fun y => extDeriv D.localForm y) :=
      integrateForm_extDeriv_congr_on_image D.cube hderiv

end LocalExtensionCongruence

end ChartSingularCubeLocalData

end Stokes

end
