import Stokes.Global.BulkMeasureIntegralIdentities
import Stokes.Global.BulkLocalTermCompactSupportConstructor

/-!
# Boundary bulk `Icc` to half-space-box transfer

The project-local half-space bulk term is definitionally an integral over the
closed source box `Icc a b`, while the canonical selected bulk box used by the
global measure layer is `halfSpaceSupportBox a b`.  This file proves the
measure-theoretic transfer between those two domains from support containment.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section SetIntegralSupportTransfer

universe u

variable {α : Type u} [MeasurableSpace α]
variable {μ : Measure α}

/--
If `s ⊆ t` and `f` is supported in `s`, integrating over `t` is the same as
integrating over `s`.
-/
theorem setIntegral_eq_setIntegral_of_subset_of_support_subset
    {s t : Set α} {f : α → Real}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) (hsupp : Function.support f ⊆ s) :
    (∫ x in t, f x ∂μ) = ∫ x in s, f x ∂μ := by
  rw [← integral_indicator ht, ← integral_indicator hs]
  refine integral_congr_ae (ae_of_all μ ?_)
  intro x
  by_cases hxs : x ∈ s
  · simp [Set.indicator_of_mem hxs, Set.indicator_of_mem (hst hxs)]
  · have hzero : f x = 0 := by
      exact Function.notMem_support.mp fun hx_support => hxs (hsupp hx_support)
    by_cases hxt : x ∈ t
    · simp [Set.indicator_of_notMem hxs, Set.indicator_of_mem hxt, hzero]
    · simp [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxt]

/--
Specialized transfer from an ambient closed box to a contained half-space
support box.
-/
theorem Icc_integral_eq_halfSpaceSupportBox_integral_of_support_subset {n : Nat}
    {μ : Measure (Fin (n + 1) → Real)}
    {a b : Fin (n + 1) → Real} {f : (Fin (n + 1) → Real) → Real}
    (hsupp : Function.support f ⊆ halfSpaceSupportBox a b) :
    (∫ y in Set.Icc a b, f y ∂μ) =
      ∫ y in halfSpaceSupportBox a b, f y ∂μ := by
  exact setIntegral_eq_setIntegral_of_subset_of_support_subset
    (μ := μ)
    (s := halfSpaceSupportBox a b) (t := Set.Icc a b) (f := f)
    (measurableSet_halfSpaceSupportBox a b)
    measurableSet_Icc
    (halfSpaceSupportBox_subset_Icc a b)
    hsupp

end SetIntegralSupportTransfer

section BoundaryTransferConstructor

universe u w b ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {P : SelectedBoxPartitionOfUnity I omega}
variable {boundary : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {localized : LocalizedInteriorM8Fields I omega P}
variable {μ : Measure (Fin (n + 1) → Real)}
variable [IsFiniteMeasureOnCompacts μ]
variable
    {localFacts :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized}

namespace SelectedBoundaryIccToHalfSpaceIntegralTransfer

/--
The canonical boundary transfer follows from support containment in the
half-space support box.  For the canonical local facts this support containment
is already one of the boxed local facts.
-/
def of_support_subset_halfSpaceSupportBox :
    SelectedBoundaryIccToHalfSpaceIntegralTransfer
      (P := P) (boundary := boundary) (localized := localized)
      localFacts μ where
  boundary_Icc_integral_eq_canonicalBox_integral := by
    intro x hx q hq
    have hsupp :
        Function.support (selectedPartitionBoundaryBulkScalarTerm boundary x q) ⊆
          halfSpaceSupportBox (boundary.sourceLowerCorner x q)
            (boundary.sourceUpperCorner x q) := by
      intro y hy
      by_contra hnot
      exact hy (localFacts.boundary_eq_zero_off_box x hx q hq (by simpa using hnot))
    simpa [SelectedPartitionBulkCanonicalLocalFacts.boundaryBox,
      selectedPartitionBoundaryCanonicalBox] using
      Icc_integral_eq_halfSpaceSupportBox_integral_of_support_subset
        (μ := μ)
        (a := boundary.sourceLowerCorner x q)
        (b := boundary.sourceUpperCorner x q)
        (f := selectedPartitionBoundaryBulkScalarTerm boundary x q)
        hsupp

/--
Volume-facing local set-integral identities with the boundary transfer now
constructed from canonical support containment.
-/
def toLocalSetIntegralIdentitiesOfMeasureEqVolumeFromSupport
    (hμ : μ = volume) :
    SelectedPartitionBulkLocalSetIntegralIdentities
      (P := P) (boundary := boundary) localized μ :=
  (of_support_subset_halfSpaceSupportBox
    (localFacts := localFacts) (μ := μ)).toLocalSetIntegralIdentitiesOfMeasureEqVolume
      localFacts hμ

end SelectedBoundaryIccToHalfSpaceIntegralTransfer

end BoundaryTransferConstructor

end Stokes

end
