import Stokes.Global.SupportControlledSelectedPartition

/-!
# Open-shrink selected covers from pointwise chart boxes

`CompactSupportChartCoverSelection.assignedCoverSet` is intentionally a
closed/relative chart box on boundary pieces, so it is not an honest ambient
open set in general.  This file extracts an auxiliary open shrink from the
pointwise `nhds` data, builds the finite selected cover from those open
shrinks, and then constructs the usual `SupportControlledSelectedPartition`
by subordinating to the open shrink and pushing support containment back to
the original assigned chart box.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section PointwiseOpenSelection

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}

namespace PointwiseCompactSupportChartBoxData

/-- The chart box selected by pointwise compact-support data at a point. -/
def chartBox (D : PointwiseCompactSupportChartBoxData I K) (x : M) : Set M :=
  if D.isBoundary x then
    boundaryChartBoxNeighborhood I (D.boundaryChart x)
      (D.boundaryLower x) (D.boundaryUpper x)
  else
    interiorChartBoxNeighborhood I (D.interiorChart x)
      (D.interiorLower x) (D.interiorUpper x)

/-- An ambient-open shrink of the selected chart box at points of `K`.

Away from `K` this is defined as `univ`; only the `x ∈ K` branch is used by
finite-subcover extraction.
-/
def openShrink (D : PointwiseCompactSupportChartBoxData I K) (x : M) : Set M :=
  by
    classical
    exact
      if hx : x ∈ K then
        Classical.choose (mem_nhds_iff.mp (by
          simpa [chartBox] using D.chartBox_mem_nhds x hx))
      else
        univ

theorem openShrink_subset_chartBox
    (D : PointwiseCompactSupportChartBoxData I K) {x : M} (hx : x ∈ K) :
    D.openShrink x ⊆ D.chartBox (I := I) x := by
  classical
  have hspec :=
    Classical.choose_spec (mem_nhds_iff.mp (by
      simpa [chartBox] using D.chartBox_mem_nhds x hx))
  simpa [openShrink, hx] using hspec.1

theorem isOpen_openShrink
    (D : PointwiseCompactSupportChartBoxData I K) (x : M) :
    IsOpen (D.openShrink (I := I) x) := by
  classical
  by_cases hx : x ∈ K
  · have hspec :=
      Classical.choose_spec (mem_nhds_iff.mp (by
        simpa [chartBox] using D.chartBox_mem_nhds x hx))
    simpa [openShrink, hx] using hspec.2.1
  · simp [openShrink, hx]

theorem mem_openShrink_self
    (D : PointwiseCompactSupportChartBoxData I K) {x : M} (hx : x ∈ K) :
    x ∈ D.openShrink (I := I) x := by
  classical
  have hspec :=
    Classical.choose_spec (mem_nhds_iff.mp (by
      simpa [chartBox] using D.chartBox_mem_nhds x hx))
  simpa [openShrink, hx] using hspec.2.2

/-- A finite selected chart-box cover together with the auxiliary open shrink
used to build the smooth partition of unity. -/
structure OpenSelectedCover (D : PointwiseCompactSupportChartBoxData I K) where
  C : CompactSupportChartCoverSelection I K
  interiorChart_eq : C.interiorChart = D.interiorChart
  boundaryChart_eq : C.boundaryChart = D.boundaryChart
  interiorLower_eq : C.interiorLower = D.interiorLower
  interiorUpper_eq : C.interiorUpper = D.interiorUpper
  boundaryLower_eq : C.boundaryLower = D.boundaryLower
  boundaryUpper_eq : C.boundaryUpper = D.boundaryUpper
  openCoverSet : C.CoverIndex → Set M
  openCoverSet_isOpen : ∀ j : C.CoverIndex, IsOpen (openCoverSet j)
  openCoverSet_subset_assigned :
    ∀ j : C.CoverIndex, openCoverSet j ⊆ C.assignedCoverSet j
  support_subset_iUnion_openCoverSet :
    K ⊆ ⋃ j : C.CoverIndex, openCoverSet j

namespace OpenSelectedCover

variable {D : PointwiseCompactSupportChartBoxData I K}

variable
    (S : OpenSelectedCover (I := I) (K := K) D)

/-- Build the usual support-controlled selected partition from the auxiliary
open shrink.  This is the replacement for the old
`assignedCoverSet_isOpen` assumption. -/
theorem exists_supportControlledSelectedPartition
    [FiniteDimensional Real (Fin (n + 1) → Real)]
    [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact K) :
    ∃ P : SupportControlledSelectedPartition S.C,
      (∀ x ∈ K, ∑ j : S.C.CoverIndex, P.partition j x = 1) ∧
        (∀ j : S.C.CoverIndex,
          tsupport (P.partition j) ∩ K ⊆ S.C.assignedCoverSet j) := by
  classical
  rcases SmoothPartitionOfUnity.exists_isSubordinate
      (I := I) (s := K) hK.isClosed S.openCoverSet
      S.openCoverSet_isOpen S.support_subset_iUnion_openCoverSet with
    ⟨ρ, hρopen⟩
  let P : SupportControlledSelectedPartition S.C :=
    { partition := ρ
      subordinate := by
        intro j x hx
        exact S.openCoverSet_subset_assigned j (hρopen j hx)
      sum_eq_one := sum_eq_one_on_supportSet ρ
      tsupport_inter_subset_assigned := by
        intro j x hx
        exact S.openCoverSet_subset_assigned j
          ((tsupport_partition_inter_supportSet_subset_cover hρopen j) hx) }
  exact ⟨P, P.finite_sum_eq_one, P.tsupport_inter_subset_assigned⟩

/-- Nonempty spelling of `exists_supportControlledSelectedPartition`. -/
theorem nonempty_supportControlledSelectedPartition
    [FiniteDimensional Real (Fin (n + 1) → Real)]
    [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact K) :
    Nonempty (SupportControlledSelectedPartition S.C) := by
  rcases S.exists_supportControlledSelectedPartition (I := I) hK with ⟨P, _⟩
  exact ⟨P⟩

end OpenSelectedCover

/-- Extract a finite selected chart-box cover from pointwise chart-box data,
using auxiliary open shrinks for the compactness argument.

The selected cover has the same chart and box functions as the pointwise data,
but its partition-of-unity construction should use `openCoverSet`, not the
possibly non-open assigned chart boxes.
-/
theorem exists_openSelectedCover
    (D : PointwiseCompactSupportChartBoxData I K) (hK : IsCompact K) :
    ∃ S : OpenSelectedCover (I := I) (K := K) D,
      S.C.interiorChart = D.interiorChart ∧
        S.C.boundaryChart = D.boundaryChart ∧
          S.C.interiorLower = D.interiorLower ∧
            S.C.interiorUpper = D.interiorUpper ∧
              S.C.boundaryLower = D.boundaryLower ∧
                S.C.boundaryUpper = D.boundaryUpper := by
  classical
  have hnhds : ∀ x ∈ K, D.openShrink (I := I) x ∈ 𝓝 x := by
    intro x hx
    exact (D.isOpen_openShrink (I := I) x).mem_nhds
      (D.mem_openShrink_self (I := I) hx)
  obtain ⟨centers, hcentersK, hcover⟩ :=
    hK.elim_nhds_subcover (fun x => D.openShrink (I := I) x) hnhds
  let interiorCenters : Finset M :=
    centers.filter (fun x => D.isBoundary x = false)
  let boundaryCenters : Finset M :=
    centers.filter (fun x => D.isBoundary x = true)
  let C : CompactSupportChartCoverSelection I K :=
    { interiorCenters := interiorCenters
      boundaryCenters := boundaryCenters
      interior_center_mem := by
        intro x hx
        exact hcentersK x ((Finset.mem_filter.mp hx).1)
      boundary_center_mem := by
        intro x hx
        exact hcentersK x ((Finset.mem_filter.mp hx).1)
      interiorChart := D.interiorChart
      boundaryChart := D.boundaryChart
      interiorLower := D.interiorLower
      interiorUpper := D.interiorUpper
      boundaryLower := D.boundaryLower
      boundaryUpper := D.boundaryUpper
      interior_le := by
        intro x hx
        exact D.interior_le x
          (hcentersK x ((Finset.mem_filter.mp hx).1))
          (Finset.mem_filter.mp hx).2
      interior_Icc_subset_domain := by
        intro x hx
        exact D.interior_Icc_subset_domain x
          (hcentersK x ((Finset.mem_filter.mp hx).1))
          (Finset.mem_filter.mp hx).2
      boundary_lower_zero := by
        intro x hx
        exact D.boundary_lower_zero x
          (hcentersK x ((Finset.mem_filter.mp hx).1))
          (Finset.mem_filter.mp hx).2
      boundary_le := by
        intro x hx
        exact D.boundary_le x
          (hcentersK x ((Finset.mem_filter.mp hx).1))
          (Finset.mem_filter.mp hx).2
      boundary_Icc_subset_domain := by
        intro x hx
        exact D.boundary_Icc_subset_domain x
          (hcentersK x ((Finset.mem_filter.mp hx).1))
          (Finset.mem_filter.mp hx).2
      support_subset_cover := by
        intro y hy
        have hycover : y ∈ ⋃ x ∈ centers, D.openShrink (I := I) x := hcover hy
        simp only [mem_iUnion, exists_prop] at hycover
        rcases hycover with ⟨x, hxcenters, hyopen⟩
        have hxK : x ∈ K := hcentersK x hxcenters
        have hybox : y ∈ D.chartBox (I := I) x :=
          D.openShrink_subset_chartBox (I := I) hxK hyopen
        by_cases hxkind : D.isBoundary x = true
        · right
          refine mem_iUnion.mpr ⟨x, ?_⟩
          refine mem_iUnion.mpr ⟨?_, ?_⟩
          · exact Finset.mem_filter.mpr ⟨hxcenters, hxkind⟩
          · simpa [chartBox, hxkind] using hybox
        · left
          have hxfalse : D.isBoundary x = false := by
            cases h : D.isBoundary x
            · rfl
            · exact (hxkind h).elim
          refine mem_iUnion.mpr ⟨x, ?_⟩
          refine mem_iUnion.mpr ⟨?_, ?_⟩
          · exact Finset.mem_filter.mpr ⟨hxcenters, hxfalse⟩
          · simpa [chartBox, hxfalse] using hybox }
  let openCoverSet : C.CoverIndex → Set M
    | Sum.inl x => D.openShrink (I := I) x.1
    | Sum.inr x => D.openShrink (I := I) x.1
  refine ⟨{
    C := C
    interiorChart_eq := rfl
    boundaryChart_eq := rfl
    interiorLower_eq := rfl
    interiorUpper_eq := rfl
    boundaryLower_eq := rfl
    boundaryUpper_eq := rfl
    openCoverSet := openCoverSet
    openCoverSet_isOpen := ?_
    openCoverSet_subset_assigned := ?_
    support_subset_iUnion_openCoverSet := ?_ },
    rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro j
    rcases j with i | i <;>
      simpa [openCoverSet] using D.isOpen_openShrink (I := I) i.1
  · intro j y hy
    rcases j with i | i
    · have hiK : i.1 ∈ K := hcentersK i.1 ((Finset.mem_filter.mp i.2).1)
      have hifalse : D.isBoundary i.1 = false := (Finset.mem_filter.mp i.2).2
      have hybox : y ∈ D.chartBox (I := I) i.1 :=
        D.openShrink_subset_chartBox (I := I) hiK hy
      simpa [C, openCoverSet, CompactSupportChartCoverSelection.assignedCoverSet,
        chartBox, hifalse] using hybox
    · have hiK : i.1 ∈ K := hcentersK i.1 ((Finset.mem_filter.mp i.2).1)
      have hitrue : D.isBoundary i.1 = true := (Finset.mem_filter.mp i.2).2
      have hybox : y ∈ D.chartBox (I := I) i.1 :=
        D.openShrink_subset_chartBox (I := I) hiK hy
      simpa [C, openCoverSet, CompactSupportChartCoverSelection.assignedCoverSet,
        chartBox, hitrue] using hybox
  · intro y hy
    have hycover : y ∈ ⋃ x ∈ centers, D.openShrink (I := I) x := hcover hy
    simp only [mem_iUnion, exists_prop] at hycover
    rcases hycover with ⟨x, hxcenters, hyopen⟩
    by_cases hxkind : D.isBoundary x = true
    · refine mem_iUnion.mpr ⟨Sum.inr ⟨x, ?_⟩, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hxcenters, hxkind⟩
      · simpa [openCoverSet]
    · have hxfalse : D.isBoundary x = false := by
        cases h : D.isBoundary x
        · rfl
        · exact (hxkind h).elim
      refine mem_iUnion.mpr ⟨Sum.inl ⟨x, ?_⟩, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hxcenters, hxfalse⟩
      · simpa [openCoverSet]

/-- Canonically choose the open-shrink selected cover extracted from pointwise
chart-box data.  This is the replacement for choosing a finite cover whose
assigned closed/relative boxes are themselves assumed open. -/
def selectedOpenCoverOfPointwise
    (D : PointwiseCompactSupportChartBoxData I K) (hK : IsCompact K) :
    OpenSelectedCover (I := I) (K := K) D :=
  Classical.choose (D.exists_openSelectedCover (I := I) hK)

/-- Specification of `selectedOpenCoverOfPointwise`: it preserves the
pointwise chart and box functions while carrying an auxiliary open cover for
partition-of-unity construction. -/
theorem selectedOpenCoverOfPointwise_spec
    (D : PointwiseCompactSupportChartBoxData I K) (hK : IsCompact K) :
    (D.selectedOpenCoverOfPointwise (I := I) hK).C.interiorChart =
        D.interiorChart ∧
      (D.selectedOpenCoverOfPointwise (I := I) hK).C.boundaryChart =
        D.boundaryChart ∧
        (D.selectedOpenCoverOfPointwise (I := I) hK).C.interiorLower =
          D.interiorLower ∧
          (D.selectedOpenCoverOfPointwise (I := I) hK).C.interiorUpper =
            D.interiorUpper ∧
            (D.selectedOpenCoverOfPointwise (I := I) hK).C.boundaryLower =
              D.boundaryLower ∧
              (D.selectedOpenCoverOfPointwise (I := I) hK).C.boundaryUpper =
                D.boundaryUpper := by
  simpa [selectedOpenCoverOfPointwise] using
    Classical.choose_spec (D.exists_openSelectedCover (I := I) hK)

/-- The canonical finite chart-cover selected through open shrinks. -/
def selectedCoverOfOpenPointwise
    (D : PointwiseCompactSupportChartBoxData I K) (hK : IsCompact K) :
    CompactSupportChartCoverSelection I K :=
  (D.selectedOpenCoverOfPointwise (I := I) hK).C

/-- The canonical support-controlled partition built from the open-shrink
selected cover.  Its support-control field still lands in the original
assigned chart boxes, not merely in the auxiliary open shrink. -/
def selectedOpenSupportControlledPartition
    [FiniteDimensional Real (Fin (n + 1) → Real)]
    [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]
    (D : PointwiseCompactSupportChartBoxData I K) (hK : IsCompact K) :
    SupportControlledSelectedPartition
      (D.selectedCoverOfOpenPointwise (I := I) hK) :=
  Classical.choice
    ((D.selectedOpenCoverOfPointwise (I := I) hK)
      |>.nonempty_supportControlledSelectedPartition (I := I) hK)

/-- The canonical open-shrink partition sums to one on the compact carrier. -/
theorem selectedOpenSupportControlledPartition_sum_eq_one
    [FiniteDimensional Real (Fin (n + 1) → Real)]
    [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]
    (D : PointwiseCompactSupportChartBoxData I K) (hK : IsCompact K) :
    ∀ x ∈ K,
      ∑ j : (D.selectedCoverOfOpenPointwise (I := I) hK).CoverIndex,
        (D.selectedOpenSupportControlledPartition (I := I) hK).partition j x = 1 :=
  (D.selectedOpenSupportControlledPartition (I := I) hK).finite_sum_eq_one

/-- The canonical open-shrink partition is supported, on `K`, inside the
original assigned chart boxes. -/
theorem selectedOpenSupportControlledPartition_tsupport_inter_subset_assigned
    [FiniteDimensional Real (Fin (n + 1) → Real)]
    [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]
    (D : PointwiseCompactSupportChartBoxData I K) (hK : IsCompact K) :
    ∀ j : (D.selectedCoverOfOpenPointwise (I := I) hK).CoverIndex,
      tsupport
          ((D.selectedOpenSupportControlledPartition
            (I := I) hK).partition j) ∩ K ⊆
        (D.selectedCoverOfOpenPointwise (I := I) hK).assignedCoverSet j :=
  (D.selectedOpenSupportControlledPartition (I := I) hK).tsupport_inter_subset_assigned

end PointwiseCompactSupportChartBoxData

end PointwiseOpenSelection

end Stokes

end
