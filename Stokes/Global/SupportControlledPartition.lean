import Stokes.Global.Partition

/-!
# Support-controlled smooth partitions on compact supports

Mathlib already contains the main existence theorem needed here:
`SmoothPartitionOfUnity.exists_isSubordinate`.  This file specializes it to the
finite-cover shape used in the compact-support Stokes globalization.

The theorem obtained here is intentionally modest and honest: it gives a smooth
partition of unity on the compact support set `K`, subordinate to a finite open
cover.  Thus the sum is `1` on `K`, and every coefficient has topological
support contained in its assigned open set.  A stronger statement with
`sum = 1` on a whole neighborhood of `K` is not a field of mathlib's current
`SmoothPartitionOfUnity` existence theorem.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section SupportControlledPartition

universe uι uE uH uM

variable {ι : Type uι}
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H}

/--
The support projection supplied by a subordinate smooth partition of unity.

This is the exact support condition needed by the localized Stokes step:
on the compact support set, the `i`-th coefficient can only contribute inside
its assigned open set.
-/
theorem tsupport_partition_inter_supportSet_subset_cover
    {K : Set M} {U : ι → Set M}
    {ρ : SmoothPartitionOfUnity ι I M K}
    (hρU : ρ.IsSubordinate U) (i : ι) :
    tsupport (ρ i) ∩ K ⊆ U i := by
  intro x hx
  exact hρU i hx.1

/--
The pointwise partition identity on the compact support set.

For compact-support Stokes this is the honest theorem directly provided by
mathlib's partition-of-unity structure.  Upgrading it to a neighborhood of `K`
would require an additional bump/shrinking construction.
-/
theorem sum_eq_one_on_supportSet
    {K : Set M} (ρ : SmoothPartitionOfUnity ι I M K) :
    ∀ x ∈ K, ∑ᶠ i, ρ i x = 1 := by
  intro x hx
  exact ρ.sum_eq_one hx

/--
A support-controlled smooth partition of unity subordinate to a finite open
cover of a compact set.

The index type of the resulting partition is the subtype of indices in the
finite cover.  This keeps the partition genuinely finite-indexed for later
finite sums, while preserving mathlib's `SmoothPartitionOfUnity` API.
-/
theorem exists_supportControlledSmoothPartition_finset
    [FiniteDimensional Real E] [IsManifold I ⊤ M] [T2Space M]
    [SigmaCompactSpace M]
    (s : Finset ι) (K : Set M) (hK : IsCompact K)
    (U : ι → Set M)
    (hUopen : ∀ i ∈ s, IsOpen (U i))
    (hcover : K ⊆ ⋃ i ∈ s, U i) :
    ∃ ρ : SmoothPartitionOfUnity {i // i ∈ s} I M K,
      ρ.IsSubordinate (fun i : {i // i ∈ s} => U i.1) ∧
        (∀ x ∈ K, ∑ᶠ i : {i // i ∈ s}, ρ i x = 1) ∧
          (∀ i : {i // i ∈ s}, tsupport (ρ i) ∩ K ⊆ U i.1) := by
  have hcover' : K ⊆ ⋃ i : {i // i ∈ s}, U i.1 := by
    intro x hx
    rcases mem_iUnion.1 (hcover hx) with ⟨i, hxi⟩
    rcases mem_iUnion.1 hxi with ⟨his, hxU⟩
    exact mem_iUnion_of_mem ⟨i, his⟩ hxU
  rcases SmoothPartitionOfUnity.exists_isSubordinate
      (I := I) (s := K) hK.isClosed
      (fun i : {i // i ∈ s} => U i.1)
      (fun i => hUopen i.1 i.2) hcover' with
    ⟨ρ, hρU⟩
  exact
    ⟨ρ, hρU, sum_eq_one_on_supportSet ρ,
      fun i => tsupport_partition_inter_supportSet_subset_cover hρU i⟩

/--
Finite-sum version of `exists_supportControlledSmoothPartition_finset`.

Since the partition is indexed by the finite subtype `{i // i ∈ s}`, the
`finsum` partition identity can be rewritten as an ordinary finite sum.
-/
theorem exists_supportControlledSmoothPartition_finset_sum
    [FiniteDimensional Real E] [IsManifold I ⊤ M] [T2Space M]
    [SigmaCompactSpace M]
    (s : Finset ι) (K : Set M) (hK : IsCompact K)
    (U : ι → Set M)
    (hUopen : ∀ i ∈ s, IsOpen (U i))
    (hcover : K ⊆ ⋃ i ∈ s, U i) :
    ∃ ρ : SmoothPartitionOfUnity {i // i ∈ s} I M K,
      ρ.IsSubordinate (fun i : {i // i ∈ s} => U i.1) ∧
        (∀ x ∈ K, ∑ i : {i // i ∈ s}, ρ i x = 1) ∧
          (∀ i : {i // i ∈ s}, tsupport (ρ i) ∩ K ⊆ U i.1) := by
  classical
  rcases exists_supportControlledSmoothPartition_finset
      (I := I) s K hK U hUopen hcover with
    ⟨ρ, hρU, hsum, hsupp⟩
  refine ⟨ρ, hρU, ?_, hsupp⟩
  intro x hx
  simpa [finsum_eq_sum_of_fintype] using hsum x hx

/--
Subtype-indexed version when the cover has already been reindexed by the
finite subtype.
-/
theorem exists_supportControlledSmoothPartition_subtype
    [FiniteDimensional Real E] [IsManifold I ⊤ M] [T2Space M]
    [SigmaCompactSpace M]
    (s : Finset ι) (K : Set M) (hK : IsCompact K)
    (U : {i // i ∈ s} → Set M)
    (hUopen : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i : {i // i ∈ s}, U i) :
    ∃ ρ : SmoothPartitionOfUnity {i // i ∈ s} I M K,
      ρ.IsSubordinate U ∧
        (∀ x ∈ K, ∑ᶠ i : {i // i ∈ s}, ρ i x = 1) ∧
          (∀ i : {i // i ∈ s}, tsupport (ρ i) ∩ K ⊆ U i) := by
  rcases SmoothPartitionOfUnity.exists_isSubordinate
      (I := I) (s := K) hK.isClosed U hUopen hcover with
    ⟨ρ, hρU⟩
  exact
    ⟨ρ, hρU, sum_eq_one_on_supportSet ρ,
      fun i => tsupport_partition_inter_supportSet_subset_cover hρU i⟩

end SupportControlledPartition

end Stokes

end
