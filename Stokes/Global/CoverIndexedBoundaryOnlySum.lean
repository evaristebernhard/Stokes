import Stokes.Global.CoverIndexedFromSupportControlledCover

/-!
# Boundary-only finite sums for cover-indexed selected covers

The mixed selected cover index is a sum type:

`C.CoverIndex = interior selected centers ⊕ boundary selected centers`.

This file records the small algebraic rewrites used when a cover-indexed
boundary family is identically zero on the interior summand.  No analysis or
measure theory is involved here.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedBoundaryOnlySum

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}

namespace CompactSupportChartCoverSelection

/-- If a real-valued cover-index family vanishes on interior selected indices,
then its total cover-index sum is the boundary-index sum. -/
theorem coverIndex_sum_eq_boundary_sum_of_inl_eq_zero
    (C : CompactSupportChartCoverSelection I K) (f : C.CoverIndex → Real)
    (hzero :
      ∀ i : {x : M // x ∈ C.interiorCenters}, f (Sum.inl i) = 0) :
    (∑ j : C.CoverIndex, f j) =
      ∑ i : {x : M // x ∈ C.boundaryCenters}, f (Sum.inr i) := by
  classical
  change
    (∑ j :
        ({x : M // x ∈ C.interiorCenters} ⊕
          {x : M // x ∈ C.boundaryCenters}), f j) =
      ∑ i : {x : M // x ∈ C.boundaryCenters}, f (Sum.inr i)
  calc
    (∑ j :
        ({x : M // x ∈ C.interiorCenters} ⊕
          {x : M // x ∈ C.boundaryCenters}), f j) =
        (∑ i : {x : M // x ∈ C.interiorCenters}, f (Sum.inl i)) +
          ∑ i : {x : M // x ∈ C.boundaryCenters}, f (Sum.inr i) := by
      simp only [Fintype.sum_sum_type]
    _ = 0 + ∑ i : {x : M // x ∈ C.boundaryCenters}, f (Sum.inr i) := by
      have hleft :
          (∑ i : {x : M // x ∈ C.interiorCenters}, f (Sum.inl i)) = 0 := by
        exact Finset.sum_eq_zero (fun i _hi => hzero i)
      rw [hleft]
    _ = ∑ i : {x : M // x ∈ C.boundaryCenters}, f (Sum.inr i) := by
      rw [zero_add]

/-- Reverse-oriented version of
`coverIndex_sum_eq_boundary_sum_of_inl_eq_zero`, convenient for `rw` in the
opposite direction. -/
theorem boundary_sum_eq_coverIndex_sum_of_inl_eq_zero
    (C : CompactSupportChartCoverSelection I K) (f : C.CoverIndex → Real)
    (hzero :
      ∀ i : {x : M // x ∈ C.interiorCenters}, f (Sum.inl i) = 0) :
    (∑ i : {x : M // x ∈ C.boundaryCenters}, f (Sum.inr i)) =
      ∑ j : C.CoverIndex, f j :=
  (C.coverIndex_sum_eq_boundary_sum_of_inl_eq_zero f hzero).symm

/-- The canonical boundary cover-index finset is just `Finset.univ` on the
selected boundary subtype. -/
theorem sum_boundaryCoverIndexFinset_eq_univ
    (C : CompactSupportChartCoverSelection I K)
    (f : {x : M // x ∈ C.boundaryCenters} → Real) :
    (∑ i ∈ C.boundaryCoverIndexFinset, f i) =
      ∑ i : {x : M // x ∈ C.boundaryCenters}, f i := by
  classical
  simp [boundaryCoverIndexFinset]

/-- Boundary-only rewrite with the repository's canonical boundary finset on
the right-hand side. -/
theorem coverIndex_sum_eq_boundaryCoverIndexFinset_sum_of_inl_eq_zero
    (C : CompactSupportChartCoverSelection I K) (f : C.CoverIndex → Real)
    (hzero :
      ∀ i : {x : M // x ∈ C.interiorCenters}, f (Sum.inl i) = 0) :
    (∑ j : C.CoverIndex, f j) =
      ∑ i ∈ C.boundaryCoverIndexFinset, f (Sum.inr i) := by
  classical
  calc
    (∑ j : C.CoverIndex, f j) =
        ∑ i : {x : M // x ∈ C.boundaryCenters}, f (Sum.inr i) :=
      C.coverIndex_sum_eq_boundary_sum_of_inl_eq_zero f hzero
    _ = ∑ i ∈ C.boundaryCoverIndexFinset, f (Sum.inr i) :=
      (C.sum_boundaryCoverIndexFinset_eq_univ
        (fun i : {x : M // x ∈ C.boundaryCenters} => f (Sum.inr i))).symm

end CompactSupportChartCoverSelection

namespace SupportControlledSelectedPartition

/-- The local true-boundary cover-index sum only sees selected boundary
indices, because `coverIndexLocalBoundaryTerm` is definitionally zero on
interior selected indices. -/
theorem coverIndexLocalBoundaryTerm_sum_eq_boundary_sum
    (P : SupportControlledSelectedPartition C) :
    (∑ j : C.CoverIndex, P.coverIndexLocalBoundaryTerm omega j) =
      ∑ i : {x : M // x ∈ C.boundaryCenters},
        P.coverIndexLocalBoundaryTerm omega (Sum.inr i) := by
  classical
  exact
    C.coverIndex_sum_eq_boundary_sum_of_inl_eq_zero
      (fun j => P.coverIndexLocalBoundaryTerm omega j)
      (by
        intro i
        simp)

/-- Boundary-finite-set version of
`coverIndexLocalBoundaryTerm_sum_eq_boundary_sum`. -/
theorem coverIndexLocalBoundaryTerm_sum_eq_boundaryCoverIndexFinset_sum
    (P : SupportControlledSelectedPartition C) :
    (∑ j : C.CoverIndex, P.coverIndexLocalBoundaryTerm omega j) =
      ∑ i ∈ C.boundaryCoverIndexFinset,
        P.coverIndexLocalBoundaryTerm omega (Sum.inr i) := by
  classical
  rw [P.coverIndexLocalBoundaryTerm_sum_eq_boundary_sum,
    C.sum_boundaryCoverIndexFinset_eq_univ]

/-- Same boundary-only rewrite, expanded to the project-local boundary
integral carried by selected boundary boxes. -/
theorem coverIndexLocalBoundaryTerm_sum_eq_projectLocalBoundaryIntegral_sum
    (P : SupportControlledSelectedPartition C) :
    (∑ j : C.CoverIndex, P.coverIndexLocalBoundaryTerm omega j) =
      ∑ i ∈ C.boundaryCoverIndexFinset,
        projectLocalBoundaryIntegral I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  classical
  rw [P.coverIndexLocalBoundaryTerm_sum_eq_boundaryCoverIndexFinset_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simp

end SupportControlledSelectedPartition

end CoverIndexedBoundaryOnlySum

end Stokes
