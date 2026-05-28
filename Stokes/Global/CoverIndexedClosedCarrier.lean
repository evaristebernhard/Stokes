import Stokes.Global.SupportControlledSelectedPartition

/-!
# Cover-indexed closed compact carriers

`CompactSupportChartCoverSelection.assignedCoordinateBox` is the strict/open
support region used to kill artificial faces.  It is not compact, so it should
not be used directly as the measure carrier in the global reconstruction layer.

This file records the closed carrier attached to the same cover index:

* interior indices use the closed box `Set.Icc interiorLower interiorUpper`;
* boundary indices use the closed box `Set.Icc boundaryLower boundaryUpper`.

The main API transfers support already known to lie in the strict assigned
coordinate box into the closed compact carrier.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedClosedCarrier

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}

namespace CompactSupportChartCoverSelection

/-- The closed coordinate carrier attached to a selected mixed cover index. -/
def coverIndexClosedCarrier (C : CompactSupportChartCoverSelection I K) :
    C.CoverIndex → Set (Fin (n + 1) → Real) :=
  fun j => Set.Icc (C.assignedLower j) (C.assignedUpper j)

/-- Strict interior support boxes are contained in the corresponding closed box. -/
theorem boxInteriorSupportBox_subset_Icc {a b : Fin (n + 1) → Real} :
    boxInteriorSupportBox a b ⊆ Set.Icc a b := by
  intro y hy
  constructor
  · intro i
    exact le_of_lt (hy i).1
  · intro i
    exact le_of_lt (hy i).2

/-- Half-space support boxes are contained in the corresponding closed box. -/
theorem halfSpaceSupportBox_subset_Icc {a b : Fin (n + 1) → Real} :
    halfSpaceSupportBox a b ⊆ Set.Icc a b := by
  intro y hy
  constructor
  · intro i
    by_cases hi : i = 0
    · subst hi
      exact hy.1
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, hk⟩
      · contradiction
      · subst hk
        exact le_of_lt (hy.2.2 k).1
  · intro i
    by_cases hi : i = 0
    · subst hi
      exact le_of_lt hy.2.1
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, hk⟩
      · contradiction
      · subst hk
        exact le_of_lt (hy.2.2 k).2

/-- The assigned strict/open support box lies in the closed compact carrier. -/
theorem assignedCoordinateBox_subset_closedCarrier
    (C : CompactSupportChartCoverSelection I K) (j : C.CoverIndex) :
    C.assignedCoordinateBox j ⊆ C.coverIndexClosedCarrier j := by
  rcases j with i | i
  · simpa [coverIndexClosedCarrier, assignedCoordinateBox, assignedLower, assignedUpper] using
      (boxInteriorSupportBox_subset_Icc
        (a := C.interiorLower i.1) (b := C.interiorUpper i.1))
  · simpa [coverIndexClosedCarrier, assignedCoordinateBox, assignedLower, assignedUpper] using
      (halfSpaceSupportBox_subset_Icc
        (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1))

/-- Alias with the name used by downstream cover-indexed measure constructors. -/
theorem coverIndex_openSupportBox_subset_closedCarrier
    (C : CompactSupportChartCoverSelection I K) (j : C.CoverIndex) :
    C.assignedCoordinateBox j ⊆ C.coverIndexClosedCarrier j :=
  C.assignedCoordinateBox_subset_closedCarrier j

/-- Each cover-indexed closed carrier is compact. -/
theorem coverIndex_closedCarrier_isCompact
    (C : CompactSupportChartCoverSelection I K) (j : C.CoverIndex) :
    IsCompact (C.coverIndexClosedCarrier j) := by
  simpa [coverIndexClosedCarrier] using
    (isCompact_Icc : IsCompact (Set.Icc (C.assignedLower j) (C.assignedUpper j)))

/-- Transfer topological support from the assigned strict/open box to the closed carrier. -/
theorem coverIndex_tsupport_subset_closedCarrier_of_tsupport_subset_assignedCoordinateBox
    (C : CompactSupportChartCoverSelection I K) (j : C.CoverIndex)
    {α : (Fin (n + 1) → Real) → E} [Zero E]
    (hsupp : tsupport α ⊆ C.assignedCoordinateBox j) :
    tsupport α ⊆ C.coverIndexClosedCarrier j :=
  hsupp.trans (C.coverIndex_openSupportBox_subset_closedCarrier j)

/-- Function-support version useful before passing to `tsupport`-based measure wrappers. -/
theorem coverIndex_support_subset_closedCarrier_of_support_subset_assignedCoordinateBox
    (C : CompactSupportChartCoverSelection I K) (j : C.CoverIndex)
    {α : (Fin (n + 1) → Real) → E} [Zero E]
    (hsupp : Function.support α ⊆ C.assignedCoordinateBox j) :
    Function.support α ⊆ C.coverIndexClosedCarrier j :=
  hsupp.trans (C.coverIndex_openSupportBox_subset_closedCarrier j)

end CompactSupportChartCoverSelection

end CoverIndexedClosedCarrier

end Stokes
