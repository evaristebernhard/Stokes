import Stokes.SingularCube.SmoothBridgeExtensionInputAuto
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smooth singular extension mathlib audit

This private audit module records the mathlib and project APIs that can carry
the next smooth singular-cube extension step.  It intentionally contains only
definitions and wrappers proved from existing declarations.
-/

noncomputable section

open Set Filter Function
open scoped Manifold Topology

namespace Stokes
namespace SingularCubeSmoothExtensionAudit

section CubeAndFacesImage

variable {n m : Nat}

/-- The finite list of coordinate images sampled by singular Stokes: the full
cube image and all high/low face images. -/
def cubeAndFacesImage (cube : SmoothSingularCube (n + 1) m) : Set (Fin m → Real) :=
  cube.toFun '' singularParameterCube (n + 1) ∪
    ((⋃ i : Fin (n + 1), (singularFace cube i 1).toFun '' singularParameterCube n) ∪
      (⋃ i : Fin (n + 1), (singularFace cube i 0).toFun '' singularParameterCube n))

theorem cube_image_subset_cubeAndFacesImage
    (cube : SmoothSingularCube (n + 1) m) :
    cube.toFun '' singularParameterCube (n + 1) ⊆ cubeAndFacesImage cube := by
  intro y hy
  exact Or.inl hy

theorem highFace_image_subset_cubeAndFacesImage
    (cube : SmoothSingularCube (n + 1) m) (i : Fin (n + 1)) :
    (singularFace cube i 1).toFun '' singularParameterCube n ⊆
      cubeAndFacesImage cube := by
  intro y hy
  exact Or.inr (Or.inl (mem_iUnion.2 ⟨i, hy⟩))

theorem lowFace_image_subset_cubeAndFacesImage
    (cube : SmoothSingularCube (n + 1) m) (i : Fin (n + 1)) :
    (singularFace cube i 0).toFun '' singularParameterCube n ⊆
      cubeAndFacesImage cube := by
  intro y hy
  exact Or.inr (Or.inr (mem_iUnion.2 ⟨i, hy⟩))

theorem cube_mem_of_cubeAndFacesImage_subset
    (cube : SmoothSingularCube (n + 1) m) {U : Set (Fin m → Real)}
    (hU : cubeAndFacesImage cube ⊆ U) {x : Fin (n + 1) → Real}
    (hx : x ∈ singularParameterCube (n + 1)) :
    cube.toFun x ∈ U :=
  hU (Or.inl ⟨x, hx, rfl⟩)

theorem highFace_mem_of_cubeAndFacesImage_subset
    (cube : SmoothSingularCube (n + 1) m) {U : Set (Fin m → Real)}
    (hU : cubeAndFacesImage cube ⊆ U) (i : Fin (n + 1))
    {x : Fin n → Real} (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 1).toFun x ∈ U :=
  hU (Or.inr (Or.inl (mem_iUnion.2 ⟨i, ⟨x, hx, rfl⟩⟩)))

theorem lowFace_mem_of_cubeAndFacesImage_subset
    (cube : SmoothSingularCube (n + 1) m) {U : Set (Fin m → Real)}
    (hU : cubeAndFacesImage cube ⊆ U) (i : Fin (n + 1))
    {x : Fin n → Real} (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 0).toFun x ∈ U :=
  hU (Or.inr (Or.inr (mem_iUnion.2 ⟨i, ⟨x, hx, rfl⟩⟩)))

end CubeAndFacesImage

section OpenExtensionCoreInput

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- A thinner extension input: one set contains every image point sampled by
the singular Stokes statement. -/
structure ChartwiseSingularCubeCoreExtensionInput {n m : Nat}
    {I : ModelWithCorners Real (Fin m → Real) H}
    (omega : ManifoldForm I M n)
    (chart : M) (cube : SmoothSingularCube (n + 1) m) where
  smoothSet : Set (Fin m → Real)
  isOpen_smoothSet : IsOpen smoothSet
  cube_mem_smoothSet : MapsTo cube.toFun (singularParameterCube (n + 1)) smoothSet
  smoothSet_subset_chartTarget : smoothSet ⊆ (extChartAt I chart).target
  chartwiseSmooth : ManifoldForm.ChartwiseSmooth I omega
  omegaExt : EuclideanForm m n
  contDiff_omegaExt : ContDiff Real ⊤ omegaExt
  extensionSet : Set (Fin m → Real)
  isOpen_extensionSet : IsOpen extensionSet
  image_subset_extensionSet : cubeAndFacesImage cube ⊆ extensionSet
  agreesOn_extensionSet : EqOn omegaExt (chartLocalForm I chart omega) extensionSet

namespace ChartwiseSingularCubeCoreExtensionInput

variable {n m : Nat}
variable {I : ModelWithCorners Real (Fin m → Real) H}
variable {omega : ManifoldForm I M n}
variable {chart : M} {cube : SmoothSingularCube (n + 1) m}

/-- Expand the compact audit input into the theorem-facing open extension
input already used by the smooth singular bridge. -/
def toOpenExtensionInput
    (E : ChartwiseSingularCubeCoreExtensionInput omega chart cube) :
    ChartwiseSingularCubeOpenExtensionInput omega chart cube where
  smoothSet := E.smoothSet
  isOpen_smoothSet := E.isOpen_smoothSet
  cube_mem_smoothSet := E.cube_mem_smoothSet
  smoothSet_subset_chartTarget := E.smoothSet_subset_chartTarget
  chartwiseSmooth := E.chartwiseSmooth
  omegaExt := E.omegaExt
  contDiff_omegaExt := E.contDiff_omegaExt
  extensionSet := E.extensionSet
  isOpen_extensionSet := E.isOpen_extensionSet
  highFace_mem_extensionSet := fun i _ hx =>
    highFace_mem_of_cubeAndFacesImage_subset cube E.image_subset_extensionSet i hx
  lowFace_mem_extensionSet := fun i _ hx =>
    lowFace_mem_of_cubeAndFacesImage_subset cube E.image_subset_extensionSet i hx
  cube_mem_extensionSet := fun _ hx =>
    cube_mem_of_cubeAndFacesImage_subset cube E.image_subset_extensionSet hx
  agreesOn_extensionSet := E.agreesOn_extensionSet

theorem boundary_stokes
    (E : ChartwiseSingularCubeCoreExtensionInput omega chart cube) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  E.toOpenExtensionInput.boundary_stokes

theorem chain_stokes
    (E : ChartwiseSingularCubeCoreExtensionInput omega chart cube) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  E.toOpenExtensionInput.chain_stokes

end ChartwiseSingularCubeCoreExtensionInput

end OpenExtensionCoreInput

section MathlibWrappers

variable {m n d : Nat}

/-- Mathlib locality of `extDeriv`, in the Euclidean form shape used here. -/
theorem eventuallyEq_extDeriv_eq_available
    {omega eta : EuclideanForm m n} {y : Fin m → Real}
    (h : omega =ᶠ[𝓝 y] eta) :
    extDeriv omega y = extDeriv eta y :=
  h.extDeriv_eq

/-- Mathlib pullback naturality for `extDeriv`, specialized to Euclidean
coordinate forms. -/
theorem extDeriv_pullback_available
    {r : WithTop ℕ∞} {f : (Fin d → Real) → (Fin m → Real)}
    {omega : EuclideanForm m n} {x : Fin d → Real}
    (homega : DifferentiableAt Real omega (f x))
    (hf : ContDiffAt Real r f x)
    (hr : minSmoothness Real 2 ≤ r) :
    extDeriv
        (fun x => (omega (f x)).compContinuousLinearMap (fderiv Real f x)) x =
      (extDeriv omega (f x)).compContinuousLinearMap (fderiv Real f x) :=
  extDeriv_pullback homega hf hr

/-- The within-set version of mathlib pullback naturality for `extDeriv`. -/
theorem extDerivWithin_pullback_available
    {r : WithTop ℕ∞} {f : (Fin d → Real) → (Fin m → Real)}
    {omega : EuclideanForm m n} {s : Set (Fin d → Real)}
    {t : Set (Fin m → Real)} {x : Fin d → Real}
    (homega : DifferentiableWithinAt Real omega t (f x))
    (hf : ContDiffWithinAt Real r f s x)
    (hr : minSmoothness Real 2 ≤ r)
    (hs : UniqueDiffOn Real s)
    (hxc : x ∈ closure (interior s))
    (hxs : x ∈ s)
    (hst : MapsTo f s t) :
    extDerivWithin
        (fun x => (omega (f x)).compContinuousLinearMap (fderivWithin Real f s x)) s x =
      (extDerivWithin omega t (f x)).compContinuousLinearMap
        (fderivWithin Real f s x) :=
  extDerivWithin_pullback homega hf hr hs hxc hxs hst

/-- Pointwise finite-dimensional bump functions with compact topological
support, directly from mathlib. -/
theorem exists_contDiff_tsupport_subset_available
    {s : Set (Fin m → Real)} {x : Fin m → Real} {r : ℕ∞}
    (hs : s ∈ 𝓝 x) :
    ∃ phi : (Fin m → Real) → Real,
      tsupport phi ⊆ s ∧ HasCompactSupport phi ∧ ContDiff Real r phi ∧
        range phi ⊆ Icc 0 1 ∧ phi x = 1 :=
  exists_contDiff_tsupport_subset hs

/-- Smooth functions with prescribed open support in finite-dimensional
Euclidean coordinates, directly from mathlib. -/
theorem isOpen_exists_contDiff_support_eq_available
    {s : Set (Fin m → Real)} {r : ℕ∞}
    (hs : IsOpen s) :
    ∃ phi : (Fin m → Real) → Real,
      support phi = s ∧ ContDiff Real r phi ∧ range phi ⊆ Icc 0 1 :=
  hs.exists_contDiff_support_eq

end MathlibWrappers

section ChartTransitionWrappers

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H}
variable [IsManifold I ⊤ M]

/-- Concrete coordinate changes are smooth on chart-overlap subsets. -/
theorem chartTransition_contDiffOn_available {x0 x1 : M} {s : Set E}
    (hstarget : s ⊆ (extChartAt I x0).target)
    (hsoverlap : s ⊆ ManifoldForm.chartOverlap I x0 x1) :
    ContDiffOn Real ⊤ (ManifoldForm.chartTransition I x0 x1) s :=
  ManifoldForm.contDiffOn_chartTransition (I := I) hstarget hsoverlap

/-- The project-level derivative of the coordinate change is smooth on the
same overlap subsets. -/
theorem chartTransitionDeriv_contDiffOn_available {x0 x1 : M} {s : Set E}
    (hstarget : s ⊆ (extChartAt I x0).target)
    (hsoverlap : s ⊆ ManifoldForm.chartOverlap I x0 x1) :
    ContDiffOn Real ⊤ (ManifoldForm.chartTransitionDeriv I x0 x1) s :=
  ManifoldForm.contDiffOn_chartTransitionDeriv (I := I) hstarget hsoverlap

/-- Smoothness of transition pullback from `ChartwiseSmooth` and the chart API. -/
theorem chartwise_transitionPullback_contDiffOn_available {k : Nat}
    {omega : ManifoldForm I M k} (homega : ManifoldForm.ChartwiseSmooth I omega)
    (x0 x1 : M) {s : Set E}
    (hstarget : s ⊆ (extChartAt I x0).target)
    (hsoverlap : s ⊆ ManifoldForm.chartOverlap I x0 x1) :
    ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 omega) s :=
  homega.contDiffOn_transitionPullbackInChart_of_chartAPI (I := I) x0 x1 hstarget hsoverlap

/-- Smoothness of alternating-form pullback by a smooth family of Frechet
derivatives, as used in `transitionPullbackInChart`. -/
theorem alternating_compContinuousLinearMap_contDiffOn_available
    {X F : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup F] [NormedSpace Real F]
    {k : Nat} {s : Set X}
    {eta : X → F [⋀^Fin k]→L[Real] Real}
    {g : X → E →L[Real] F}
    (heta : ContDiffOn Real ⊤ eta s)
    (hg : ContDiffOn Real ⊤ g s) :
    ContDiffOn Real ⊤ (fun x => (eta x).compContinuousLinearMap (g x)) s :=
  ContinuousAlternatingMap.contDiffOn_compContinuousLinearMap heta hg

end ChartTransitionWrappers

end SingularCubeSmoothExtensionAudit
end Stokes

end
