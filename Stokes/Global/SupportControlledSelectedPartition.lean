import Stokes.Global.SupportControlledPartition
import Stokes.Global.CompactSupportChartCoverSelection
import Stokes.Global.FiniteBoxCoverPartition
import Stokes.BoundaryChart.BoundaryAssignedBoxSupport

/-!
# Support-controlled partitions for selected compact chart-box covers

This file connects the compact chart-box cover selection with the
support-controlled smooth partition wrapper.

The selected cover is mixed: an index is either an interior chart-box center or
a boundary chart-box center.  The resulting partition is indexed by the finite
sum of those two selected subtypes.  The core output is intentionally honest:
the partition sums to `1` on the compact support set, and each coefficient has
topological support, after intersection with that compact set, inside its
assigned manifold-side chart-box neighborhood.

The final coordinate-support lemmas are conditional bridges.  They package the
extra chart-coordinate hypotheses needed to turn manifold-side support control
into the exact coefficient-support shapes consumed by
`InteriorAssignedBoxSupport` and `BoundaryAssignedBoxSupport`.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section SupportControlledSelectedPartition

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}

namespace CompactSupportChartCoverSelection

/-- The finite mixed index type of a compact-support chart-box selection. -/
def CoverIndex (C : CompactSupportChartCoverSelection I K) : Type w :=
  ({x : M // x ∈ C.interiorCenters} ⊕ {x : M // x ∈ C.boundaryCenters})

instance instFintypeCoverIndex (C : CompactSupportChartCoverSelection I K) :
    Fintype C.CoverIndex := by
  classical
  dsimp [CoverIndex]
  infer_instance

/-- The center carried by a selected mixed cover index. -/
def coverCenter (C : CompactSupportChartCoverSelection I K) :
    C.CoverIndex → M
  | Sum.inl x => x.1
  | Sum.inr x => x.1

/-- The chart assigned to a selected mixed cover index. -/
def assignedChart (C : CompactSupportChartCoverSelection I K) :
    C.CoverIndex → M
  | Sum.inl x => C.interiorChart x.1
  | Sum.inr x => C.boundaryChart x.1

/-- The lower coordinate corner assigned to a selected mixed cover index. -/
def assignedLower (C : CompactSupportChartCoverSelection I K) :
    C.CoverIndex → Fin (n + 1) → Real
  | Sum.inl x => C.interiorLower x.1
  | Sum.inr x => C.boundaryLower x.1

/-- The upper coordinate corner assigned to a selected mixed cover index. -/
def assignedUpper (C : CompactSupportChartCoverSelection I K) :
    C.CoverIndex → Fin (n + 1) → Real
  | Sum.inl x => C.interiorUpper x.1
  | Sum.inr x => C.boundaryUpper x.1

/-- The coordinate-side box assigned to a selected mixed cover index. -/
def assignedCoordinateBox (C : CompactSupportChartCoverSelection I K) :
    C.CoverIndex → Set (Fin (n + 1) → Real)
  | Sum.inl x => boxInteriorSupportBox (C.interiorLower x.1) (C.interiorUpper x.1)
  | Sum.inr x => halfSpaceSupportBox (C.boundaryLower x.1) (C.boundaryUpper x.1)

/-- The manifold-side cover set assigned to a selected mixed cover index. -/
def assignedCoverSet (C : CompactSupportChartCoverSelection I K) :
    C.CoverIndex → Set M
  | Sum.inl x =>
      interiorChartBoxNeighborhood I (C.interiorChart x.1)
        (C.interiorLower x.1) (C.interiorUpper x.1)
  | Sum.inr x =>
      boundaryChartBoxNeighborhood I (C.boundaryChart x.1)
        (C.boundaryLower x.1) (C.boundaryUpper x.1)

/-- The selected mixed index cover still covers the compact support set. -/
theorem support_subset_iUnion_assignedCoverSet
    (C : CompactSupportChartCoverSelection I K) :
    K ⊆ ⋃ j : C.CoverIndex, C.assignedCoverSet j := by
  intro y hy
  rcases C.support_subset_interior_union_boundary hy with hyint | hybdry
  · simp only [interiorCoverSet, mem_iUnion, exists_prop] at hyint
    rcases hyint with ⟨x, hxmem, hyx⟩
    exact mem_iUnion_of_mem (Sum.inl ⟨x, hxmem⟩) hyx
  · simp only [boundaryCoverSet, mem_iUnion, exists_prop] at hybdry
    rcases hybdry with ⟨x, hxmem, hyx⟩
    exact mem_iUnion_of_mem (Sum.inr ⟨x, hxmem⟩) hyx

end CompactSupportChartCoverSelection

/--
A smooth partition subordinate to the mixed chart-box cover selected from a
compact support set.
-/
structure SupportControlledSelectedPartition
    (C : CompactSupportChartCoverSelection I K) where
  /-- The smooth partition, indexed by the selected interior/boundary cover indices. -/
  partition : SmoothPartitionOfUnity C.CoverIndex I M K
  /-- Subordination to the assigned manifold-side cover sets. -/
  subordinate : partition.IsSubordinate C.assignedCoverSet
  /-- The partition sums to one on the controlled compact support set. -/
  sum_eq_one : ∀ x ∈ K, ∑ᶠ j : C.CoverIndex, partition j x = 1
  /-- Every coefficient is supported, on `K`, in its assigned cover set. -/
  tsupport_inter_subset_assigned :
    ∀ j : C.CoverIndex, tsupport (partition j) ∩ K ⊆ C.assignedCoverSet j

namespace SupportControlledSelectedPartition

variable {C : CompactSupportChartCoverSelection I K}

/-- Ordinary finite-sum form of the partition identity. -/
theorem finite_sum_eq_one (P : SupportControlledSelectedPartition C) :
    ∀ x ∈ K, ∑ j : C.CoverIndex, P.partition j x = 1 := by
  classical
  intro x hx
  simpa [finsum_eq_sum_of_fintype] using P.sum_eq_one x hx

/-- The interior selected coefficient is supported, on `K`, in its assigned box neighborhood. -/
theorem interior_tsupport_inter_subset_assigned
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.interiorCenters}) :
    tsupport (P.partition (Sum.inl i)) ∩ K ⊆
      interiorChartBoxNeighborhood I (C.interiorChart i.1)
        (C.interiorLower i.1) (C.interiorUpper i.1) := by
  simpa [CompactSupportChartCoverSelection.assignedCoverSet] using
    P.tsupport_inter_subset_assigned (Sum.inl i)

/-- The boundary selected coefficient is supported, on `K`, in its assigned box neighborhood. -/
theorem boundary_tsupport_inter_subset_assigned
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport (P.partition (Sum.inr i)) ∩ K ⊆
      boundaryChartBoxNeighborhood I (C.boundaryChart i.1)
        (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  simpa [CompactSupportChartCoverSelection.assignedCoverSet] using
    P.tsupport_inter_subset_assigned (Sum.inr i)

/--
Generic coordinate-support bridge for the selected coefficient attached to a
mixed cover index.

The extra hypotheses say that the chosen coordinate support maps back into
`K`, lies in the chart target, and that coordinate `tsupport` of the
transition coefficient maps back into manifold-side `tsupport` of the
partition coefficient.  Under those standard chart-coordinate inputs, the
manifold-side subordination field becomes the exact assigned coordinate-box
support statement.
-/
theorem transitionCoefficient_inter_coordSupport_subset_assignedCoordinateBox
    (P : SupportControlledSelectedPartition C)
    (j : C.CoverIndex) {coordSupport : Set (Fin (n + 1) → Real)}
    (hcoordK :
      ∀ y ∈ coordSupport,
        (extChartAt I (C.assignedChart j)).symm y ∈ K)
    (hcoordTarget :
      coordSupport ⊆ (extChartAt I (C.assignedChart j)).target)
    (hcoeff_tsupport :
      ∀ y,
        y ∈ tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (C.assignedChart j) (C.assignedChart j) (P.partition j)) →
          (extChartAt I (C.assignedChart j)).symm y ∈
            tsupport (P.partition j)) :
    tsupport
          (ManifoldForm.transitionCoefficientInChart I
            (C.assignedChart j) (C.assignedChart j) (P.partition j)) ∩
        coordSupport ⊆
      C.assignedCoordinateBox j := by
  rintro y ⟨hycoeff, hycoord⟩
  have hmanifold :
      (extChartAt I (C.assignedChart j)).symm y ∈
        C.assignedCoverSet j :=
    P.tsupport_inter_subset_assigned j
      ⟨hcoeff_tsupport y hycoeff, hcoordK y hycoord⟩
  rcases j with i | i
  · have hright :
        (extChartAt I (C.interiorChart i.1))
            ((extChartAt I (C.interiorChart i.1)).symm y) = y :=
      (extChartAt I (C.interiorChart i.1)).right_inv
        (hcoordTarget hycoord)
    have hbox :
        (extChartAt I (C.interiorChart i.1))
            ((extChartAt I (C.interiorChart i.1)).symm y) ∈
          boxInteriorSupportBox (C.interiorLower i.1) (C.interiorUpper i.1) := by
      simpa [CompactSupportChartCoverSelection.assignedChart,
        CompactSupportChartCoverSelection.assignedCoverSet] using hmanifold.2
    rw [hright] at hbox
    simpa [CompactSupportChartCoverSelection.assignedCoordinateBox] using hbox
  · have hright :
        (extChartAt I (C.boundaryChart i.1))
            ((extChartAt I (C.boundaryChart i.1)).symm y) = y :=
      (extChartAt I (C.boundaryChart i.1)).right_inv
        (hcoordTarget hycoord)
    have hbox :
        (extChartAt I (C.boundaryChart i.1))
            ((extChartAt I (C.boundaryChart i.1)).symm y) ∈
          halfSpaceSupportBox (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
      simpa [CompactSupportChartCoverSelection.assignedChart,
        CompactSupportChartCoverSelection.assignedCoverSet] using hmanifold.2
    rw [hright] at hbox
    simpa [CompactSupportChartCoverSelection.assignedCoordinateBox] using hbox

/--
Interior specialization in the exact coefficient-support shape consumed by the
assigned interior-box support API.
-/
theorem interior_transitionCoefficient_inter_coordSupport_subset_box
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.interiorCenters})
    {coordSupport : Set (Fin (n + 1) → Real)}
    (hcoordK :
      ∀ y ∈ coordSupport,
        (extChartAt I (C.interiorChart i.1)).symm y ∈ K)
    (hcoordTarget :
      coordSupport ⊆ (extChartAt I (C.interiorChart i.1)).target)
    (hcoeff_tsupport :
      ∀ y,
        y ∈ tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (C.interiorChart i.1) (C.interiorChart i.1)
              (P.partition (Sum.inl i))) →
          (extChartAt I (C.interiorChart i.1)).symm y ∈
            tsupport (P.partition (Sum.inl i))) :
    tsupport
          (ManifoldForm.transitionCoefficientInChart I
            (C.interiorChart i.1) (C.interiorChart i.1)
            (P.partition (Sum.inl i))) ∩
        coordSupport ⊆
      boxInteriorSupportBox (C.interiorLower i.1) (C.interiorUpper i.1) := by
  simpa [CompactSupportChartCoverSelection.assignedChart,
    CompactSupportChartCoverSelection.assignedCoordinateBox] using
    P.transitionCoefficient_inter_coordSupport_subset_assignedCoordinateBox
      (j := Sum.inl i) hcoordK hcoordTarget hcoeff_tsupport

/--
Boundary specialization in the exact coefficient-support shape consumed by the
assigned boundary half-space support API.
-/
theorem boundary_transitionCoefficient_inter_coordSupport_subset_box
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters})
    {coordSupport : Set (Fin (n + 1) → Real)}
    (hcoordK :
      ∀ y ∈ coordSupport,
        (extChartAt I (C.boundaryChart i.1)).symm y ∈ K)
    (hcoordTarget :
      coordSupport ⊆ (extChartAt I (C.boundaryChart i.1)).target)
    (hcoeff_tsupport :
      ∀ y,
        y ∈ tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1)
              (P.partition (Sum.inr i))) →
          (extChartAt I (C.boundaryChart i.1)).symm y ∈
            tsupport (P.partition (Sum.inr i))) :
    tsupport
          (ManifoldForm.transitionCoefficientInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1)
            (P.partition (Sum.inr i))) ∩
        coordSupport ⊆
      halfSpaceSupportBox (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  simpa [CompactSupportChartCoverSelection.assignedChart,
    CompactSupportChartCoverSelection.assignedCoordinateBox] using
    P.transitionCoefficient_inter_coordSupport_subset_assignedCoordinateBox
      (j := Sum.inr i) hcoordK hcoordTarget hcoeff_tsupport

end SupportControlledSelectedPartition

/--
Existence of a support-controlled smooth partition subordinate to a selected
compact chart-box cover, assuming the selected cover sets are open.
-/
theorem exists_supportControlledSelectedPartition
    [FiniteDimensional Real (Fin (n + 1) → Real)] [IsManifold I ⊤ M]
    [T2Space M] [SigmaCompactSpace M]
    (C : CompactSupportChartCoverSelection I K) (hK : IsCompact K)
    (hopen : ∀ j : C.CoverIndex, IsOpen (C.assignedCoverSet j)) :
    ∃ P : SupportControlledSelectedPartition C,
      (∀ x ∈ K, ∑ j : C.CoverIndex, P.partition j x = 1) ∧
        (∀ j : C.CoverIndex,
          tsupport (P.partition j) ∩ K ⊆ C.assignedCoverSet j) := by
  rcases SmoothPartitionOfUnity.exists_isSubordinate
      (I := I) (s := K) hK.isClosed C.assignedCoverSet hopen
      C.support_subset_iUnion_assignedCoverSet with
    ⟨ρ, hρsub⟩
  let P : SupportControlledSelectedPartition C :=
    { partition := ρ
      subordinate := hρsub
      sum_eq_one := sum_eq_one_on_supportSet ρ
      tsupport_inter_subset_assigned :=
        fun j => tsupport_partition_inter_supportSet_subset_cover hρsub j }
  exact ⟨P, P.finite_sum_eq_one, P.tsupport_inter_subset_assigned⟩

/-- Nonempty form of `exists_supportControlledSelectedPartition`, convenient for projection. -/
theorem nonempty_supportControlledSelectedPartition
    [FiniteDimensional Real (Fin (n + 1) → Real)] [IsManifold I ⊤ M]
    [T2Space M] [SigmaCompactSpace M]
    (C : CompactSupportChartCoverSelection I K) (hK : IsCompact K)
    (hopen : ∀ j : C.CoverIndex, IsOpen (C.assignedCoverSet j)) :
    Nonempty (SupportControlledSelectedPartition C) := by
  rcases exists_supportControlledSelectedPartition C hK hopen with ⟨P, _⟩
  exact ⟨P⟩

end SupportControlledSelectedPartition

end Stokes

end
