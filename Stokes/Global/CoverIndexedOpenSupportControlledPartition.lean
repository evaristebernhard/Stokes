import Stokes.Global.CoverIndexedPointwiseOpenSelection

/-!
# Support-controlled partitions remembering the open shrink

`SupportControlledSelectedPartition` deliberately stores support control into the
selected chart boxes.  For the intrinsic compact-support route we also need to
remember the auxiliary open shrink used to build the partition, because those
open sets replace the old, false `assignedCoverSet_isOpen` input.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section OpenSupportControlledPartition

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {D : PointwiseCompactSupportChartBoxData I K}

namespace PointwiseCompactSupportChartBoxData

/-- A selected partition built from `OpenSelectedCover.openCoverSet`, retaining
both the old closed-box support control and the sharper open-shrink support
control. -/
structure OpenSupportControlledSelectedPartition
    (S : OpenSelectedCover (I := I) (K := K) D)
    extends SupportControlledSelectedPartition S.C where
  /-- The coefficient support on `K` lands in the auxiliary open shrink. -/
  tsupport_inter_subset_openCoverSet :
    ∀ j : S.C.CoverIndex, tsupport (partition j) ∩ K ⊆ S.openCoverSet j

namespace OpenSelectedCover

variable (S : OpenSelectedCover (I := I) (K := K) D)

/-- Construct the support-controlled partition while retaining the open-shrink
support statement used by the intrinsic route. -/
theorem exists_openSupportControlledSelectedPartition
    [FiniteDimensional Real (Fin (n + 1) → Real)]
    [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact K) :
    ∃ P : OpenSupportControlledSelectedPartition (I := I) (K := K) S,
      (∀ x ∈ K, ∑ j : S.C.CoverIndex, P.partition j x = 1) ∧
        (∀ j : S.C.CoverIndex,
          tsupport (P.partition j) ∩ K ⊆ S.openCoverSet j) ∧
          (∀ j : S.C.CoverIndex,
            tsupport (P.partition j) ∩ K ⊆ S.C.assignedCoverSet j) := by
  classical
  rcases SmoothPartitionOfUnity.exists_isSubordinate
      (I := I) (s := K) hK.isClosed S.openCoverSet
      S.openCoverSet_isOpen S.support_subset_iUnion_openCoverSet with
    ⟨ρ, hρopen⟩
  let P0 : SupportControlledSelectedPartition S.C :=
    { partition := ρ
      subordinate := by
        intro j x hx
        exact S.openCoverSet_subset_assigned j (hρopen j hx)
      sum_eq_one := sum_eq_one_on_supportSet ρ
      tsupport_inter_subset_assigned := by
        intro j x hx
        exact S.openCoverSet_subset_assigned j
          ((tsupport_partition_inter_supportSet_subset_cover hρopen j) hx) }
  let P : OpenSupportControlledSelectedPartition (I := I) (K := K) S :=
    { P0 with
      tsupport_inter_subset_openCoverSet := by
        intro j x hx
        exact (tsupport_partition_inter_supportSet_subset_cover hρopen j) hx }
  exact ⟨P, P0.finite_sum_eq_one,
    (by intro j; exact P.tsupport_inter_subset_openCoverSet j),
    (by intro j; exact P.tsupport_inter_subset_assigned j)⟩

/-- Canonically choose the open-shrink-aware selected partition. -/
def openSupportControlledSelectedPartition
    [FiniteDimensional Real (Fin (n + 1) → Real)]
    [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact K) :
    OpenSupportControlledSelectedPartition (I := I) (K := K) S :=
  Classical.choose
    (S.exists_openSupportControlledSelectedPartition (I := I) hK)

/-- The canonical open-shrink-aware partition is a usual
`SupportControlledSelectedPartition`. -/
def supportControlledSelectedPartition
    [FiniteDimensional Real (Fin (n + 1) → Real)]
    [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact K) :
    SupportControlledSelectedPartition S.C :=
  (S.openSupportControlledSelectedPartition (I := I) hK).toSupportControlledSelectedPartition

/-- The canonical open-shrink-aware partition sums to one on the compact
carrier. -/
theorem openSupportControlledSelectedPartition_sum_eq_one
    [FiniteDimensional Real (Fin (n + 1) → Real)]
    [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact K) :
    ∀ x ∈ K,
      ∑ j : S.C.CoverIndex,
        (S.openSupportControlledSelectedPartition (I := I) hK).partition j x = 1 := by
  have hspec :=
    Classical.choose_spec
      (S.exists_openSupportControlledSelectedPartition (I := I) hK)
  exact hspec.1

/-- The canonical open-shrink-aware partition has support, on `K`, in the
auxiliary open cover. -/
theorem openSupportControlledSelectedPartition_tsupport_inter_subset_openCoverSet
    [FiniteDimensional Real (Fin (n + 1) → Real)]
    [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact K) :
    ∀ j : S.C.CoverIndex,
      tsupport
          ((S.openSupportControlledSelectedPartition
            (I := I) hK).partition j) ∩ K ⊆
        S.openCoverSet j := by
  have hspec :=
    Classical.choose_spec
      (S.exists_openSupportControlledSelectedPartition (I := I) hK)
  exact hspec.2.1

/-- The canonical open-shrink-aware partition also has the usual selected-box
support control. -/
theorem openSupportControlledSelectedPartition_tsupport_inter_subset_assigned
    [FiniteDimensional Real (Fin (n + 1) → Real)]
    [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact K) :
    ∀ j : S.C.CoverIndex,
      tsupport
          ((S.openSupportControlledSelectedPartition
            (I := I) hK).partition j) ∩ K ⊆
        S.C.assignedCoverSet j := by
  have hspec :=
    Classical.choose_spec
      (S.exists_openSupportControlledSelectedPartition (I := I) hK)
  exact hspec.2.2

end OpenSelectedCover

end PointwiseCompactSupportChartBoxData

end OpenSupportControlledPartition

end Stokes

end
