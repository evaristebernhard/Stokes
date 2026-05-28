import Stokes.SingularCube.CutoffExtensionTopologyAuto
import Stokes.SingularCube.CoreExtensionFromCompactCarrierAuto
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smooth singular cube cutoff-extension mega layer

This module pushes the smooth singular-cube extension route one step closer to
the analytic theorem used in ordinary geometry texts.  The previous modules
produce a compact carrier and an open shrink around the cube-and-faces image.
Here we add the next theorem-facing layer:

* a nested cutoff shrink `K ⊆ inner`, `closure inner ⊆ supportSet`,
  `closure supportSet ⊆ outer`;
* a genuine smooth scalar cutoff with topological support in `outer` and value
  `1` on `inner`;
* a global smooth Euclidean form `x ↦ φ x • ω x` from a form smooth on `outer`;
* chartwise compact-extension inputs and singular Stokes wrappers.

The key point is that no extension theorem is postulated: the scalar cutoff is
constructed from mathlib's smooth partition-of-unity API, and the form
smoothness is proved from the topological-support route.
-/

noncomputable section

open Set Function Filter
open scoped Manifold Topology ContDiff

namespace Stokes
namespace SingularCubeSmoothExtensionAudit

section EuclideanCutoff

variable {m n : Nat}

/-- The fiber of a Euclidean differential form at a coordinate point. -/
abbrev EuclideanFormFiber (m n : Nat) :=
  (Fin m → Real) [⋀^Fin n]→L[Real] Real

/--
A nested cutoff shrink around a compact carrier.

`inner` is the open set on which the later extension agrees with the original
form.  `supportSet` is an open buffer whose closure lies in `outer`, the set on
which the original Euclidean form is known to be smooth.
-/
structure CompactCarrierCutoffShrink
    (K outer : Set (Fin m → Real)) where
  inner : Set (Fin m → Real)
  supportSet : Set (Fin m → Real)
  isOpen_inner : IsOpen inner
  carrier_subset_inner : K ⊆ inner
  closure_inner_subset_supportSet : closure inner ⊆ supportSet
  isOpen_supportSet : IsOpen supportSet
  closure_supportSet_subset_outer : closure supportSet ⊆ outer

namespace CompactCarrierCutoffShrink

variable {K outer : Set (Fin m → Real)}

/-- The inner open set is contained in the support buffer. -/
theorem inner_subset_supportSet
    (S : CompactCarrierCutoffShrink (m := m) K outer) :
    S.inner ⊆ S.supportSet :=
  subset_closure.trans S.closure_inner_subset_supportSet

/-- The support buffer is contained in the outer smoothness set. -/
theorem supportSet_subset_outer
    (S : CompactCarrierCutoffShrink (m := m) K outer) :
    S.supportSet ⊆ outer :=
  subset_closure.trans S.closure_supportSet_subset_outer

/-- The inner set is contained in the outer smoothness set. -/
theorem inner_subset_outer
    (S : CompactCarrierCutoffShrink (m := m) K outer) :
    S.inner ⊆ outer :=
  S.inner_subset_supportSet.trans S.supportSet_subset_outer

/-- The compact carrier is contained in the support buffer. -/
theorem carrier_subset_supportSet
    (S : CompactCarrierCutoffShrink (m := m) K outer) :
    K ⊆ S.supportSet :=
  S.carrier_subset_inner.trans S.inner_subset_supportSet

/-- The compact carrier is contained in the outer smoothness set. -/
theorem carrier_subset_outer
    (S : CompactCarrierCutoffShrink (m := m) K outer) :
    K ⊆ outer :=
  S.carrier_subset_inner.trans S.inner_subset_outer

/-- The inner open set is a set-neighborhood of the carrier. -/
theorem inner_mem_nhdsSet
    (S : CompactCarrierCutoffShrink (m := m) K outer) :
    S.inner ∈ 𝓝ˢ K :=
  S.isOpen_inner.mem_nhdsSet.2 S.carrier_subset_inner

/-- The support buffer is a set-neighborhood of the carrier. -/
theorem supportSet_mem_nhdsSet
    (S : CompactCarrierCutoffShrink (m := m) K outer) :
    S.supportSet ∈ 𝓝ˢ K :=
  S.isOpen_supportSet.mem_nhdsSet.2 S.carrier_subset_supportSet

/-- Pointwise membership in the inner set for carrier points. -/
theorem mem_inner_of_mem_carrier
    (S : CompactCarrierCutoffShrink (m := m) K outer)
    {x : Fin m → Real} (hx : x ∈ K) :
    x ∈ S.inner :=
  S.carrier_subset_inner hx

/-- Pointwise membership in the outer set for carrier points. -/
theorem mem_outer_of_mem_carrier
    (S : CompactCarrierCutoffShrink (m := m) K outer)
    {x : Fin m → Real} (hx : x ∈ K) :
    x ∈ outer :=
  S.carrier_subset_outer hx

/-- Convert to the earlier compact-carrier open-neighborhood package. -/
def innerOpenNeighborhood
    (S : CompactCarrierCutoffShrink (m := m) K outer) :
    CompactCarrierOpenNeighborhood K where
  openSet := S.inner
  isOpen_openSet := S.isOpen_inner
  carrier_subset_openSet := S.carrier_subset_inner

/-- Convert the inner/outer part to the earlier open-shrink package. -/
def toOpenShrink
    (S : CompactCarrierCutoffShrink (m := m) K outer) :
    CompactCarrierOpenShrink K outer where
  shrink := S.inner
  isOpen_shrink := S.isOpen_inner
  carrier_subset_shrink := S.carrier_subset_inner
  closure_shrink_subset_outer :=
    S.closure_inner_subset_supportSet.trans S.supportSet_subset_outer

@[simp]
theorem innerOpenNeighborhood_openSet
    (S : CompactCarrierCutoffShrink (m := m) K outer) :
    S.innerOpenNeighborhood.openSet = S.inner :=
  rfl

@[simp]
theorem toOpenShrink_shrink
    (S : CompactCarrierCutoffShrink (m := m) K outer) :
    S.toOpenShrink.shrink = S.inner :=
  rfl

@[simp]
theorem toOpenShrink_carrier_subset
    (S : CompactCarrierCutoffShrink (m := m) K outer) :
    S.toOpenShrink.carrier_subset_shrink = S.carrier_subset_inner :=
  rfl

end CompactCarrierCutoffShrink

/--
The scalar cutoff data produced from a nested cutoff shrink.

The support equality is intentionally about `support`, while the theorem-facing
route also exposes `tsupport_subset_outer`, which is the fact needed to prove
global smoothness of `φ • ω` from smoothness of `ω` on `outer`.
-/
structure EuclideanCutoffFunctionData
    {K outer : Set (Fin m → Real)}
    (S : CompactCarrierCutoffShrink (m := m) K outer) where
  cutoff : (Fin m → Real) → Real
  contDiff_cutoff : ContDiff Real ∞ cutoff
  range_subset_Icc : range cutoff ⊆ Icc (0 : Real) 1
  support_eq_supportSet : support cutoff = S.supportSet
  eq_one_iff_mem_closure_inner :
    ∀ x : Fin m → Real, x ∈ closure S.inner ↔ cutoff x = 1
  tsupport_subset_outer : tsupport cutoff ⊆ outer

namespace EuclideanCutoffFunctionData

variable {K outer : Set (Fin m → Real)}
variable {S : CompactCarrierCutoffShrink (m := m) K outer}

/-- The cutoff is equal to one on `closure inner`. -/
theorem eq_one_on_closure_inner
    (C : EuclideanCutoffFunctionData S) :
    EqOn C.cutoff 1 (closure S.inner) := by
  intro x hx
  exact (C.eq_one_iff_mem_closure_inner x).1 hx

/-- The cutoff is equal to one on the inner open set. -/
theorem eq_one_on_inner
    (C : EuclideanCutoffFunctionData S) :
    EqOn C.cutoff 1 S.inner := by
  intro x hx
  exact C.eq_one_on_closure_inner (subset_closure hx)

/-- The cutoff is equal to one on the carrier. -/
theorem eq_one_on_carrier
    (C : EuclideanCutoffFunctionData S) :
    EqOn C.cutoff 1 K := by
  intro x hx
  exact C.eq_one_on_inner (S.carrier_subset_inner hx)

/-- Pointwise cutoff value on the inner open set. -/
theorem cutoff_eq_one_of_mem_inner
    (C : EuclideanCutoffFunctionData S)
    {x : Fin m → Real} (hx : x ∈ S.inner) :
    C.cutoff x = 1 :=
  C.eq_one_on_inner hx

/-- Pointwise cutoff value on the carrier. -/
theorem cutoff_eq_one_of_mem_carrier
    (C : EuclideanCutoffFunctionData S)
    {x : Fin m → Real} (hx : x ∈ K) :
    C.cutoff x = 1 :=
  C.eq_one_on_carrier hx

/-- The support of the cutoff lies in the outer smoothness set. -/
theorem support_subset_outer
    (C : EuclideanCutoffFunctionData S) :
    support C.cutoff ⊆ outer := by
  rw [C.support_eq_supportSet]
  exact S.supportSet_subset_outer

/-- The cutoff has values between zero and one. -/
theorem cutoff_mem_Icc
    (C : EuclideanCutoffFunctionData S)
    (x : Fin m → Real) :
    C.cutoff x ∈ Icc (0 : Real) 1 :=
  C.range_subset_Icc (mem_range_self x)

/-- The cutoff is nonnegative. -/
theorem cutoff_nonneg
    (C : EuclideanCutoffFunctionData S)
    (x : Fin m → Real) :
    0 ≤ C.cutoff x :=
  (C.cutoff_mem_Icc x).1

/-- The cutoff is bounded above by one. -/
theorem cutoff_le_one
    (C : EuclideanCutoffFunctionData S)
    (x : Fin m → Real) :
    C.cutoff x ≤ 1 :=
  (C.cutoff_mem_Icc x).2

/-- Outside the support buffer, the cutoff vanishes. -/
theorem cutoff_eq_zero_of_not_mem_supportSet
    (C : EuclideanCutoffFunctionData S)
    {x : Fin m → Real} (hx : x ∉ S.supportSet) :
    C.cutoff x = 0 := by
  rw [← notMem_support]
  rwa [C.support_eq_supportSet]

/-- Outside the outer smoothness set, the cutoff vanishes. -/
theorem cutoff_eq_zero_of_not_mem_outer
    (C : EuclideanCutoffFunctionData S)
    {x : Fin m → Real} (hx : x ∉ outer) :
    C.cutoff x = 0 :=
  C.cutoff_eq_zero_of_not_mem_supportSet
    (fun hs => hx (S.supportSet_subset_outer hs))

/-- The cutoff has compact support whenever the support-buffer closure is compact. -/
theorem hasCompactSupport_of_isCompact_closure_supportSet
    (C : EuclideanCutoffFunctionData S)
    (hcompact : IsCompact (closure S.supportSet)) :
    HasCompactSupport C.cutoff := by
  simpa [hasCompactSupport_def, C.support_eq_supportSet] using hcompact

@[simp]
theorem cutoff_eq_one_on_inner_apply
    (C : EuclideanCutoffFunctionData S)
    {x : Fin m → Real} (hx : x ∈ S.inner) :
    C.cutoff x = 1 :=
  C.cutoff_eq_one_of_mem_inner hx

end EuclideanCutoffFunctionData

/--
Mathlib's smooth partition-of-unity API gives the scalar cutoff required by a
nested shrink.
-/
theorem exists_euclideanCutoffFunctionData
    {K outer : Set (Fin m → Real)}
    (S : CompactCarrierCutoffShrink (m := m) K outer) :
    ∃ _C : EuclideanCutoffFunctionData S, True := by
  classical
  rcases exists_contMDiff_support_eq_eq_one_iff
      (I := 𝓘(ℝ, Fin m → Real)) (M := Fin m → Real)
      (n := (⊤ : ℕ∞))
      S.isOpen_supportSet isClosed_closure
      S.closure_inner_subset_supportSet with
    ⟨φ, hφsmooth, hφrange, hφsupport, hφone⟩
  refine ⟨?_, trivial⟩
  refine
    { cutoff := φ
      contDiff_cutoff := hφsmooth.contDiff
      range_subset_Icc := hφrange
      support_eq_supportSet := hφsupport
      eq_one_iff_mem_closure_inner := hφone
      tsupport_subset_outer := ?_ }
  simpa [tsupport, hφsupport] using S.closure_supportSet_subset_outer

/-- A chosen scalar cutoff for a nested shrink. -/
def euclideanCutoffFunctionData
    {K outer : Set (Fin m → Real)}
    (S : CompactCarrierCutoffShrink (m := m) K outer) :
    EuclideanCutoffFunctionData S :=
  Classical.choose (exists_euclideanCutoffFunctionData S)

@[simp]
theorem euclideanCutoffFunctionData_support_eq
    {K outer : Set (Fin m → Real)}
    (S : CompactCarrierCutoffShrink (m := m) K outer) :
    (euclideanCutoffFunctionData S).support_eq_supportSet =
      (euclideanCutoffFunctionData S).support_eq_supportSet :=
  rfl

/-- The cutoff-smul Euclidean form associated to a scalar cutoff. -/
def cutoffSmulForm
    {K outer : Set (Fin m → Real)}
    {S : CompactCarrierCutoffShrink (m := m) K outer}
    (C : EuclideanCutoffFunctionData S)
    (omega : EuclideanForm m n) : EuclideanForm m n :=
  fun x => C.cutoff x • omega x

@[simp]
theorem cutoffSmulForm_apply
    {K outer : Set (Fin m → Real)}
    {S : CompactCarrierCutoffShrink (m := m) K outer}
    (C : EuclideanCutoffFunctionData S)
    (omega : EuclideanForm m n) (x : Fin m → Real) :
    cutoffSmulForm C omega x = C.cutoff x • omega x :=
  rfl

/--
If the original form is smooth on the outer set and the scalar cutoff has
topological support inside that set, then `φ • ω` is globally smooth.
-/
theorem contDiff_cutoffSmulForm_of_contDiffOn
    {K outer : Set (Fin m → Real)}
    {S : CompactCarrierCutoffShrink (m := m) K outer}
    (C : EuclideanCutoffFunctionData S)
    {omega : EuclideanForm m n}
    (houter : IsOpen outer)
    (homega : ContDiffOn Real ∞ omega outer) :
    ContDiff Real ∞ (cutoffSmulForm C omega) := by
  have hmd :
      ContMDiff 𝓘(ℝ, Fin m → Real) 𝓘(ℝ, EuclideanFormFiber m n)
        ((⊤ : ℕ∞) : WithTop ℕ∞) (cutoffSmulForm C omega) := by
    refine contMDiff_of_tsupport (I := 𝓘(ℝ, Fin m → Real))
      (I' := 𝓘(ℝ, EuclideanFormFiber m n))
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) ?_
    intro x hx
    have hxCutoff : x ∈ tsupport C.cutoff :=
      tsupport_smul_subset_left C.cutoff omega hx
    have hxOuter : x ∈ outer := C.tsupport_subset_outer hxCutoff
    have hωx : ContDiffAt Real ∞ omega x :=
      (homega x hxOuter).contDiffAt (houter.mem_nhds hxOuter)
    exact (C.contDiff_cutoff.contDiffAt.smul hωx).contMDiffAt
  exact hmd.contDiff

/-- Agreement of the cutoff-smul form with the original form on `inner`. -/
theorem cutoffSmulForm_eqOn_inner
    {K outer : Set (Fin m → Real)}
    {S : CompactCarrierCutoffShrink (m := m) K outer}
    (C : EuclideanCutoffFunctionData S)
    (omega : EuclideanForm m n) :
    EqOn (cutoffSmulForm C omega) omega S.inner := by
  intro x hx
  simp [cutoffSmulForm, C.cutoff_eq_one_of_mem_inner hx]

/-- Agreement of the cutoff-smul form with the original form on the carrier. -/
theorem cutoffSmulForm_eqOn_carrier
    {K outer : Set (Fin m → Real)}
    {S : CompactCarrierCutoffShrink (m := m) K outer}
    (C : EuclideanCutoffFunctionData S)
    (omega : EuclideanForm m n) :
    EqOn (cutoffSmulForm C omega) omega K := by
  intro x hx
  simp [cutoffSmulForm, C.cutoff_eq_one_of_mem_carrier hx]

/-- Outside the outer smoothness set, the cutoff-smul form is zero. -/
theorem cutoffSmulForm_eq_zero_of_not_mem_outer
    {K outer : Set (Fin m → Real)}
    {S : CompactCarrierCutoffShrink (m := m) K outer}
    (C : EuclideanCutoffFunctionData S)
    (omega : EuclideanForm m n)
    {x : Fin m → Real} (hx : x ∉ outer) :
    cutoffSmulForm C omega x = 0 := by
  simp [cutoffSmulForm, C.cutoff_eq_zero_of_not_mem_outer hx]

/--
The theorem-facing Euclidean cutoff-extension package: it contains the
original local smoothness, the generated scalar cutoff, the global smooth form,
and the agreement neighborhood.
-/
structure EuclideanFormCutoffSmoothPackage
    (omega : EuclideanForm m n)
    {K outer : Set (Fin m → Real)}
    (S : CompactCarrierCutoffShrink (m := m) K outer) where
  isOpen_outer : IsOpen outer
  contDiffOn_omega_outer : ContDiffOn Real ∞ omega outer
  cutoffData : EuclideanCutoffFunctionData S
  omegaExt : EuclideanForm m n := cutoffSmulForm cutoffData omega
  omegaExt_eq_cutoffSmul : omegaExt = cutoffSmulForm cutoffData omega := by rfl
  contDiff_omegaExt : ContDiff Real ∞ omegaExt
  agreesOn_inner : EqOn omegaExt omega S.inner

namespace EuclideanFormCutoffSmoothPackage

variable {K outer : Set (Fin m → Real)}
variable {S : CompactCarrierCutoffShrink (m := m) K outer}
variable {omega : EuclideanForm m n}

/-- Constructor from the generated cutoff and local smoothness on the outer set. -/
def ofCutoffData
    (houter : IsOpen outer)
    (homega : ContDiffOn Real ∞ omega outer)
    (C : EuclideanCutoffFunctionData S) :
    EuclideanFormCutoffSmoothPackage omega S where
  isOpen_outer := houter
  contDiffOn_omega_outer := homega
  cutoffData := C
  omegaExt := cutoffSmulForm C omega
  omegaExt_eq_cutoffSmul := rfl
  contDiff_omegaExt :=
    contDiff_cutoffSmulForm_of_contDiffOn C houter homega
  agreesOn_inner := cutoffSmulForm_eqOn_inner C omega

/-- Noncomputable constructor using the mathlib-produced cutoff. -/
def ofContDiffOn
    (houter : IsOpen outer)
    (homega : ContDiffOn Real ∞ omega outer) :
    EuclideanFormCutoffSmoothPackage omega S :=
  ofCutoffData houter homega (euclideanCutoffFunctionData S)

/-- The extension agrees with the original form on the carrier. -/
theorem agreesOn_carrier
    (P : EuclideanFormCutoffSmoothPackage omega S) :
    EqOn P.omegaExt omega K := by
  intro x hx
  exact P.agreesOn_inner (S.carrier_subset_inner hx)

/-- The extension is explicitly the cutoff-smul form. -/
theorem omegaExt_apply
    (P : EuclideanFormCutoffSmoothPackage omega S)
    (x : Fin m → Real) :
    P.omegaExt x = P.cutoffData.cutoff x • omega x := by
  rw [P.omegaExt_eq_cutoffSmul]
  rfl

/-- Pointwise agreement on the inner open set. -/
theorem omegaExt_eq_of_mem_inner
    (P : EuclideanFormCutoffSmoothPackage omega S)
    {x : Fin m → Real} (hx : x ∈ S.inner) :
    P.omegaExt x = omega x :=
  P.agreesOn_inner hx

/-- Pointwise agreement on the carrier. -/
theorem omegaExt_eq_of_mem_carrier
    (P : EuclideanFormCutoffSmoothPackage omega S)
    {x : Fin m → Real} (hx : x ∈ K) :
    P.omegaExt x = omega x :=
  P.agreesOn_carrier hx

@[simp]
theorem ofCutoffData_omegaExt
    (houter : IsOpen outer)
    (homega : ContDiffOn Real ∞ omega outer)
    (C : EuclideanCutoffFunctionData S) :
    (ofCutoffData (omega := omega) houter homega C).omegaExt =
      cutoffSmulForm C omega :=
  rfl

@[simp]
theorem ofContDiffOn_cutoffData
    (houter : IsOpen outer)
    (homega : ContDiffOn Real ∞ omega outer) :
    (ofContDiffOn (S := S) (omega := omega) houter homega).cutoffData =
      euclideanCutoffFunctionData S :=
  rfl

end EuclideanFormCutoffSmoothPackage

end EuclideanCutoff

section CubeCarrierCutoff

variable {n m : Nat}
variable {cube : SmoothSingularCube (n + 1) m}
variable {outer : Set (Fin m → Real)}

/-- A cutoff shrink for the canonical cube-and-faces compact carrier. -/
abbrev CubeAndFacesCutoffShrink
    (cube : SmoothSingularCube (n + 1) m)
    (outer : Set (Fin m → Real)) : Type :=
  CompactCarrierCutoffShrink (m := m)
    (cubeAndFacesCompactData cube).carrier outer

namespace CubeAndFacesCompactData

variable (D : CubeAndFacesCompactData cube)

/-- Build a cutoff shrink for a packaged cube-and-faces compact carrier. -/
def cutoffShrinkOfNestedOpenSets
    {inner supportSet outer : Set (Fin m → Real)}
    (hinner : IsOpen inner)
    (hcarrier : D.carrier ⊆ inner)
    (hinner_support : closure inner ⊆ supportSet)
    (hsupport : IsOpen supportSet)
    (hsupport_outer : closure supportSet ⊆ outer) :
    CompactCarrierCutoffShrink (m := m) D.carrier outer where
  inner := inner
  supportSet := supportSet
  isOpen_inner := hinner
  carrier_subset_inner := hcarrier
  closure_inner_subset_supportSet := hinner_support
  isOpen_supportSet := hsupport
  closure_supportSet_subset_outer := hsupport_outer

/-- Build a cutoff shrink using the canonical cube-and-faces carrier. -/
def canonicalCutoffShrinkOfNestedOpenSets
    {inner supportSet outer : Set (Fin m → Real)}
    (hinner : IsOpen inner)
    (hcarrier : cubeAndFacesImage cube ⊆ inner)
    (hinner_support : closure inner ⊆ supportSet)
    (hsupport : IsOpen supportSet)
    (hsupport_outer : closure supportSet ⊆ outer) :
    CompactCarrierCutoffShrink (m := m) D.carrier outer :=
  D.cutoffShrinkOfNestedOpenSets hinner
    (D.carrier_subset_of_cubeAndFacesImage_subset hcarrier)
    hinner_support hsupport hsupport_outer

/-- The full cube image lies in the inner set of a cutoff shrink. -/
theorem cube_mem_cutoff_inner
    {S : CompactCarrierCutoffShrink (m := m) D.carrier outer}
    {x : Fin (n + 1) → Real}
    (hx : x ∈ singularParameterCube (n + 1)) :
    cube.toFun x ∈ S.inner :=
  S.carrier_subset_inner (D.cube_image_subset_carrier ⟨x, hx, rfl⟩)

/-- High-face images lie in the inner set of a cutoff shrink. -/
theorem highFace_mem_cutoff_inner
    {S : CompactCarrierCutoffShrink (m := m) D.carrier outer}
    (i : Fin (n + 1)) {x : Fin n → Real}
    (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 1).toFun x ∈ S.inner :=
  S.carrier_subset_inner (D.highFace_image_subset_carrier i ⟨x, hx, rfl⟩)

/-- Low-face images lie in the inner set of a cutoff shrink. -/
theorem lowFace_mem_cutoff_inner
    {S : CompactCarrierCutoffShrink (m := m) D.carrier outer}
    (i : Fin (n + 1)) {x : Fin n → Real}
    (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 0).toFun x ∈ S.inner :=
  S.carrier_subset_inner (D.lowFace_image_subset_carrier i ⟨x, hx, rfl⟩)

end CubeAndFacesCompactData

end CubeCarrierCutoff

section ChartwiseCutoffExtension

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n m : Nat}
variable {I : ModelWithCorners Real (Fin m → Real) H}
variable {omega : ManifoldForm I M n}
variable {chart : M} {cube : SmoothSingularCube (n + 1) m}

/--
Chartwise cutoff-extension input: the original form is chartwise smooth on an
outer coordinate neighborhood, and a nested cutoff shrink chooses the agreement
neighborhood and cutoff support.
-/
structure ChartwiseSingularCubeCutoffExtensionInput
    (omega : ManifoldForm I M n)
    (chart : M) (cube : SmoothSingularCube (n + 1) m) where
  smoothSet : Set (Fin m → Real)
  isOpen_smoothSet : IsOpen smoothSet
  cube_mem_smoothSet : MapsTo cube.toFun (singularParameterCube (n + 1)) smoothSet
  smoothSet_subset_chartTarget : smoothSet ⊆ (extChartAt I chart).target
  chartwiseSmooth : ManifoldForm.ChartwiseSmooth I omega
  compactCarrier : CubeAndFacesCompactData cube
  cutoffShrink :
    CompactCarrierCutoffShrink (m := m) compactCarrier.carrier smoothSet

namespace ChartwiseSingularCubeCutoffExtensionInput

/-- Local smoothness of the chart representative on the outer smoothness set. -/
theorem contDiffOn_localForm_smoothSet
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube) :
    ContDiffOn Real ⊤ (chartLocalForm I chart omega) E.smoothSet :=
  E.chartwiseSmooth.contDiffOn_inChart (I := I) chart
    E.smoothSet_subset_chartTarget

/-- The `C∞` version of local smoothness used by the smooth cutoff API. -/
theorem contDiffOn_localForm_smoothSet_infty
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube) :
    ContDiffOn Real ∞ (chartLocalForm I chart omega) E.smoothSet :=
  E.contDiffOn_localForm_smoothSet.of_le le_top

/-- The Euclidean smooth cutoff package generated by a chartwise input. -/
def euclideanPackage
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube) :
    EuclideanFormCutoffSmoothPackage
      (chartLocalForm I chart omega) E.cutoffShrink :=
  EuclideanFormCutoffSmoothPackage.ofContDiffOn
    E.isOpen_smoothSet E.contDiffOn_localForm_smoothSet_infty

/-- The generated extension agrees with the chart representative on `inner`. -/
theorem omegaExt_agreesOn_inner
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube) :
    EqOn E.euclideanPackage.omegaExt
      (chartLocalForm I chart omega) E.cutoffShrink.inner :=
  E.euclideanPackage.agreesOn_inner

/-- The generated extension agrees with the chart representative on the carrier. -/
theorem omegaExt_agreesOn_carrier
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube) :
    EqOn E.euclideanPackage.omegaExt
      (chartLocalForm I chart omega) E.compactCarrier.carrier :=
  E.euclideanPackage.agreesOn_carrier

/-- The full cube image lies in the extension set. -/
theorem cube_mem_extensionSet
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    {x : Fin (n + 1) → Real}
    (hx : x ∈ singularParameterCube (n + 1)) :
    cube.toFun x ∈ E.cutoffShrink.inner :=
  E.compactCarrier.cube_mem_cutoff_inner hx

/-- High-face images lie in the extension set. -/
theorem highFace_mem_extensionSet
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (i : Fin (n + 1)) {x : Fin n → Real}
    (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 1).toFun x ∈ E.cutoffShrink.inner :=
  E.compactCarrier.highFace_mem_cutoff_inner i hx

/-- Low-face images lie in the extension set. -/
theorem lowFace_mem_extensionSet
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (i : Fin (n + 1)) {x : Fin n → Real}
    (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 0).toFun x ∈ E.cutoffShrink.inner :=
  E.compactCarrier.lowFace_mem_cutoff_inner i hx

end ChartwiseSingularCubeCutoffExtensionInput

/--
The compatibility input needed to feed the current singular Stokes engine.

The cutoff construction above proves `C∞` smoothness of the generated global
form.  The existing singular-cube theorem currently asks for the stronger
`ContDiff Real ⊤` hypothesis, so this wrapper records exactly that remaining
upgrade without hiding it.
-/
structure ChartwiseSingularCubeCutoffTopExtensionInput
    (omega : ManifoldForm I M n)
    (chart : M) (cube : SmoothSingularCube (n + 1) m) where
  base : ChartwiseSingularCubeCutoffExtensionInput omega chart cube
  contDiff_top_omegaExt :
    ContDiff Real ⊤ base.euclideanPackage.omegaExt

namespace ChartwiseSingularCubeCutoffTopExtensionInput

/-- Convert top-upgraded cutoff data to compact-carrier extension input. -/
def toCompactExtensionInput
    (E : ChartwiseSingularCubeCutoffTopExtensionInput omega chart cube) :
    ChartwiseSingularCubeCompactExtensionInput omega chart cube where
  smoothSet := E.base.smoothSet
  isOpen_smoothSet := E.base.isOpen_smoothSet
  cube_mem_smoothSet := E.base.cube_mem_smoothSet
  smoothSet_subset_chartTarget := E.base.smoothSet_subset_chartTarget
  chartwiseSmooth := E.base.chartwiseSmooth
  omegaExt := E.base.euclideanPackage.omegaExt
  contDiff_omegaExt := E.contDiff_top_omegaExt
  extensionSet := E.base.cutoffShrink.inner
  isOpen_extensionSet := E.base.cutoffShrink.isOpen_inner
  compactCarrier := E.base.compactCarrier
  carrier_subset_extensionSet := E.base.cutoffShrink.carrier_subset_inner
  agreesOn_extensionSet := E.base.euclideanPackage.agreesOn_inner

/-- Convert top-upgraded cutoff data to the core extension input. -/
def toCoreExtensionInput
    (E : ChartwiseSingularCubeCutoffTopExtensionInput omega chart cube) :
    ChartwiseSingularCubeCoreExtensionInput omega chart cube :=
  E.toCompactExtensionInput.toCoreExtensionInput

/-- Convert top-upgraded cutoff data to the open extension input. -/
def toOpenExtensionInput
    (E : ChartwiseSingularCubeCutoffTopExtensionInput omega chart cube) :
    ChartwiseSingularCubeOpenExtensionInput omega chart cube :=
  E.toCompactExtensionInput.toOpenExtensionInput

/-- Boundary-integral smooth singular Stokes from top-upgraded cutoff data. -/
theorem boundary_stokes
    (E : ChartwiseSingularCubeCutoffTopExtensionInput omega chart cube) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  E.toCompactExtensionInput.boundary_stokes

/-- Chain-level smooth singular Stokes from top-upgraded cutoff data. -/
theorem chain_stokes
    (E : ChartwiseSingularCubeCutoffTopExtensionInput omega chart cube) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  E.toCompactExtensionInput.chain_stokes

@[simp]
theorem toCompactExtensionInput_extensionSet
    (E : ChartwiseSingularCubeCutoffTopExtensionInput omega chart cube) :
    E.toCompactExtensionInput.extensionSet = E.base.cutoffShrink.inner :=
  rfl

@[simp]
theorem toCompactExtensionInput_omegaExt
    (E : ChartwiseSingularCubeCutoffTopExtensionInput omega chart cube) :
    E.toCompactExtensionInput.omegaExt = E.base.euclideanPackage.omegaExt :=
  rfl

@[simp]
theorem toCompactExtensionInput_compactCarrier
    (E : ChartwiseSingularCubeCutoffTopExtensionInput omega chart cube) :
    E.toCompactExtensionInput.compactCarrier = E.base.compactCarrier :=
  rfl

@[simp]
theorem toOpenExtensionInput_extensionSet
    (E : ChartwiseSingularCubeCutoffTopExtensionInput omega chart cube) :
    E.toOpenExtensionInput.extensionSet = E.base.cutoffShrink.inner :=
  rfl

end ChartwiseSingularCubeCutoffTopExtensionInput

/-- The proposition shape produced by the cutoff-extension construction. -/
def ExistsChartwiseSingularCubeCutoffExtensionInput
    (omega : ManifoldForm I M n)
    (chart : M) (cube : SmoothSingularCube (n + 1) m) : Prop :=
  ∃ _E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube, True

/-- The proposition shape that can feed the current singular Stokes theorem. -/
def ExistsChartwiseSingularCubeCutoffTopExtensionInput
    (omega : ManifoldForm I M n)
    (chart : M) (cube : SmoothSingularCube (n + 1) m) : Prop :=
  ∃ _E : ChartwiseSingularCubeCutoffTopExtensionInput omega chart cube, True

/-- Boundary-integral facade from top-upgraded cutoff-extension input. -/
theorem chartwise_singular_boundary_stokes_of_cutoffTopExtensionInput
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    (E : ChartwiseSingularCubeCutoffTopExtensionInput omega chart cube) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  E.boundary_stokes

/-- Chain-level facade from top-upgraded cutoff-extension input. -/
theorem chartwise_singular_chain_stokes_of_cutoffTopExtensionInput
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    (E : ChartwiseSingularCubeCutoffTopExtensionInput omega chart cube) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  E.chain_stokes

/-- Boundary-integral facade from the existential top-upgraded cutoff output. -/
theorem chartwise_singular_boundary_stokes_of_exists_cutoffTopExtensionInput
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    (hE : ExistsChartwiseSingularCubeCutoffTopExtensionInput omega chart cube) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  rcases hE with ⟨E, _⟩
  exact chartwise_singular_boundary_stokes_of_cutoffTopExtensionInput chart cube E

/-- Chain-level facade from the existential top-upgraded cutoff output. -/
theorem chartwise_singular_chain_stokes_of_exists_cutoffTopExtensionInput
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    (hE : ExistsChartwiseSingularCubeCutoffTopExtensionInput omega chart cube) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  rcases hE with ⟨E, _⟩
  exact chartwise_singular_chain_stokes_of_cutoffTopExtensionInput chart cube E

end ChartwiseCutoffExtension

end SingularCubeSmoothExtensionAudit
end Stokes

end
