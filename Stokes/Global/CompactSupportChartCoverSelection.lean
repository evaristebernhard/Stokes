import Stokes.Global.CompactOpenBoxSelection
import Stokes.BoundaryChart.BoundaryOpenBoxSelection
import Stokes.Global.NaturalInputData

/-!
# Compact-support chart-cover selection

This file records the compactness step needed before constructing a
support-controlled partition subordinate to local Stokes boxes.

The key point is deliberately modest: compactness extracts a finite subcover
from pointwise chart-box neighborhoods.  The hard geometric assertions that a
given boundary half-space box is a genuine manifold neighborhood, or that a
chart is the correct interior/boundary chart for a point, remain explicit
inputs.  This avoids pretending that an arbitrary compact support can be put
inside one global box, or that boundary half-space boxes are ambient Euclidean
neighborhoods.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section ChartBoxNeighborhoods

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/--
The manifold-side neighborhood cut out by a strict coordinate box in a chosen
interior chart.  The explicit source condition keeps the set aligned with the
partial equivalence behind `extChartAt`.
-/
def interiorChartBoxNeighborhood (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (chart : M) (a b : Fin (n + 1) → Real) : Set M :=
  {p | p ∈ (extChartAt I chart).source ∧
    (extChartAt I chart) p ∈ boxInteriorSupportBox a b}

/--
The manifold-side set cut out by a half-space support box in a chosen boundary
chart.  Whether this is a genuine neighborhood of a boundary point is a
relative-topology fact and is supplied explicitly in the finite-subcover
constructor below.
-/
def boundaryChartBoxNeighborhood (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (chart : M) (a b : Fin (n + 1) → Real) : Set M :=
  {p | p ∈ (extChartAt I chart).source ∧
    (extChartAt I chart) p ∈ halfSpaceSupportBox a b}

theorem interiorChartBoxNeighborhood_mem_nhds
    {x chart : M} {a b : Fin (n + 1) → Real}
    (hxsource : x ∈ (extChartAt I chart).source)
    (hboxnhds :
      boxInteriorSupportBox a b ∈ 𝓝 ((extChartAt I chart) x)) :
    interiorChartBoxNeighborhood I chart a b ∈ 𝓝 x := by
  have hsource : (extChartAt I chart).source ∈ 𝓝 x :=
    extChartAt_source_mem_nhds' (I := I) hxsource
  have hpre :
      (extChartAt I chart) ⁻¹' boxInteriorSupportBox a b ∈ 𝓝 x :=
    (continuousAt_extChartAt' (I := I) hxsource).preimage_mem_nhds hboxnhds
  change
    ((extChartAt I chart).source ∩
      (extChartAt I chart) ⁻¹' boxInteriorSupportBox a b) ∈ 𝓝 x
  exact inter_mem hsource hpre

/--
Coordinate compact-open box selection, transported back to a manifold chart as
a genuine local manifold neighborhood.
-/
theorem exists_interiorChartBoxNeighborhood_subset_coord_nhds
    {x chart : M} {U : Set (Fin (n + 1) → Real)}
    (hxsource : x ∈ (extChartAt I chart).source)
    (hU : U ∈ 𝓝 ((extChartAt I chart) x)) :
    ∃ a b : Fin (n + 1) → Real,
      a ≤ b ∧
        (extChartAt I chart) x ∈ boxInteriorSupportBox a b ∧
          interiorChartBoxNeighborhood I chart a b ∈ 𝓝 x ∧
            Set.Icc a b ⊆ U := by
  obtain ⟨a, b, hle, hxbox, hboxnhds, hIcc⟩ :=
    exists_boxInteriorSupportBox_mem_nhds_subset_of_mem_nhds
      (n := n) (x := (extChartAt I chart) x) hU
  exact ⟨a, b, hle, hxbox,
    interiorChartBoxNeighborhood_mem_nhds
      (I := I) (x := x) (chart := chart) hxsource hboxnhds,
    hIcc⟩

theorem boundaryChartBoxNeighborhood_mem_nhds_of_coord
    {x chart : M} {a b : Fin (n + 1) → Real}
    (hxsource : x ∈ (extChartAt I chart).source)
    (hboxnhds :
      halfSpaceSupportBox a b ∈ 𝓝 ((extChartAt I chart) x)) :
    boundaryChartBoxNeighborhood I chart a b ∈ 𝓝 x := by
  have hsource : (extChartAt I chart).source ∈ 𝓝 x :=
    extChartAt_source_mem_nhds' (I := I) hxsource
  have hpre :
      (extChartAt I chart) ⁻¹' halfSpaceSupportBox a b ∈ 𝓝 x :=
    (continuousAt_extChartAt' (I := I) hxsource).preimage_mem_nhds hboxnhds
  change
    ((extChartAt I chart).source ∩
      (extChartAt I chart) ⁻¹' halfSpaceSupportBox a b) ∈ 𝓝 x
  exact inter_mem hsource hpre

end ChartBoxNeighborhoods

section FiniteChartSourceCover

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/--
Every compact set in a charted space is covered by finitely many extended chart
sources, with centers chosen from the compact set.
-/
theorem exists_finite_extChartAt_source_cover_of_isCompact
    {K : Set M} (hK : IsCompact K) :
    ∃ centers : Finset M,
      (∀ x ∈ centers, x ∈ K) ∧
        K ⊆ ⋃ x ∈ centers, (extChartAt I x).source := by
  exact hK.elim_nhds_subcover
    (fun x => (extChartAt I x).source)
    (fun x _ => extChartAt_source_mem_nhds (I := I) x)

namespace CompactlySupportedSmoothFormData

variable {ω : ManifoldForm I M n}

/--
Finite chart-source cover of the compact support set recorded in natural
compact-support input data.
-/
theorem exists_finite_extChartAt_source_cover
    (formData : CompactlySupportedSmoothFormData I ω) :
    ∃ centers : Finset M,
      (∀ x ∈ centers, x ∈ formData.supportSet) ∧
        formData.supportSet ⊆ ⋃ x ∈ centers, (extChartAt I x).source :=
  exists_finite_extChartAt_source_cover_of_isCompact
    (I := I) formData.isCompact_supportSet

end CompactlySupportedSmoothFormData

end FiniteChartSourceCover

section MixedChartBoxCover

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/--
A finite family of interior and boundary chart boxes covering a compact
manifold-side set `K`.

The finite indices are the compactness-selected centers, not necessarily the
same as the chart labels used by `extChartAt`.  This makes the package suitable
for a later subordinate partition refinement, where several local boxes may
live in the same chart.
-/
structure CompactSupportChartCoverSelection
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H) (K : Set M) where
  interiorCenters : Finset M
  boundaryCenters : Finset M
  interior_center_mem :
    ∀ x ∈ interiorCenters, x ∈ K
  boundary_center_mem :
    ∀ x ∈ boundaryCenters, x ∈ K
  interiorChart : M → M
  boundaryChart : M → M
  interiorLower : M → Fin (n + 1) → Real
  interiorUpper : M → Fin (n + 1) → Real
  boundaryLower : M → Fin (n + 1) → Real
  boundaryUpper : M → Fin (n + 1) → Real
  interior_le :
    ∀ x ∈ interiorCenters, interiorLower x ≤ interiorUpper x
  interior_Icc_subset_domain :
    ∀ x ∈ interiorCenters,
      Set.Icc (interiorLower x) (interiorUpper x) ⊆
        interiorChartDomain I (interiorChart x) (interiorChart x)
  boundary_lower_zero :
    ∀ x ∈ boundaryCenters, boundaryLower x 0 = 0
  boundary_le :
    ∀ x ∈ boundaryCenters, boundaryLower x ≤ boundaryUpper x
  boundary_Icc_subset_domain :
    ∀ x ∈ boundaryCenters,
      Set.Icc (boundaryLower x) (boundaryUpper x) ⊆
        boundaryChartDomain I (boundaryChart x) (boundaryChart x)
  support_subset_cover :
    K ⊆
      (⋃ x ∈ interiorCenters,
        interiorChartBoxNeighborhood I (interiorChart x)
          (interiorLower x) (interiorUpper x)) ∪
      (⋃ x ∈ boundaryCenters,
        boundaryChartBoxNeighborhood I (boundaryChart x)
          (boundaryLower x) (boundaryUpper x))

namespace CompactSupportChartCoverSelection

variable {K : Set M}

def interiorCoverSet (C : CompactSupportChartCoverSelection I K) : Set M :=
  ⋃ x ∈ C.interiorCenters,
    interiorChartBoxNeighborhood I (C.interiorChart x)
      (C.interiorLower x) (C.interiorUpper x)

def boundaryCoverSet (C : CompactSupportChartCoverSelection I K) : Set M :=
  ⋃ x ∈ C.boundaryCenters,
    boundaryChartBoxNeighborhood I (C.boundaryChart x)
      (C.boundaryLower x) (C.boundaryUpper x)

theorem support_subset_interior_union_boundary
    (C : CompactSupportChartCoverSelection I K) :
    K ⊆ C.interiorCoverSet ∪ C.boundaryCoverSet := by
  simpa [interiorCoverSet, boundaryCoverSet] using C.support_subset_cover

end CompactSupportChartCoverSelection

/--
Pointwise local chart-box data over a compact set.  The boolean `isBoundary`
chooses whether the local box at a point is interpreted as an interior box or
as a half-space boundary box.

The field `chartBox_mem_nhds` is the mathematically important local input:
compactness can only extract a finite subcover from sets that are actual
neighborhoods of the points they are meant to cover.
-/
structure PointwiseCompactSupportChartBoxData
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H) (K : Set M) where
  isBoundary : M → Bool
  interiorChart : M → M
  boundaryChart : M → M
  interiorLower : M → Fin (n + 1) → Real
  interiorUpper : M → Fin (n + 1) → Real
  boundaryLower : M → Fin (n + 1) → Real
  boundaryUpper : M → Fin (n + 1) → Real
  interior_le :
    ∀ x ∈ K, isBoundary x = false →
      interiorLower x ≤ interiorUpper x
  interior_Icc_subset_domain :
    ∀ x ∈ K, isBoundary x = false →
      Set.Icc (interiorLower x) (interiorUpper x) ⊆
        interiorChartDomain I (interiorChart x) (interiorChart x)
  boundary_lower_zero :
    ∀ x ∈ K, isBoundary x = true →
      boundaryLower x 0 = 0
  boundary_le :
    ∀ x ∈ K, isBoundary x = true →
      boundaryLower x ≤ boundaryUpper x
  boundary_Icc_subset_domain :
    ∀ x ∈ K, isBoundary x = true →
      Set.Icc (boundaryLower x) (boundaryUpper x) ⊆
        boundaryChartDomain I (boundaryChart x) (boundaryChart x)
  chartBox_mem_nhds :
    ∀ x ∈ K,
      (if isBoundary x then
        boundaryChartBoxNeighborhood I (boundaryChart x)
          (boundaryLower x) (boundaryUpper x)
      else
        interiorChartBoxNeighborhood I (interiorChart x)
          (interiorLower x) (interiorUpper x)) ∈ 𝓝 x

namespace PointwiseCompactSupportChartBoxData

variable {K : Set M}

/--
Compactness turns pointwise chart-box neighborhoods into a finite mixed
interior/boundary chart-box cover.
-/
theorem exists_finite_selection
    (D : PointwiseCompactSupportChartBoxData I K) (hK : IsCompact K) :
    ∃ C : CompactSupportChartCoverSelection I K,
      C.interiorChart = D.interiorChart ∧
        C.boundaryChart = D.boundaryChart ∧
          C.interiorLower = D.interiorLower ∧
            C.interiorUpper = D.interiorUpper ∧
              C.boundaryLower = D.boundaryLower ∧
                C.boundaryUpper = D.boundaryUpper := by
  classical
  let chartBox : M → Set M := fun x =>
    if D.isBoundary x then
      boundaryChartBoxNeighborhood I (D.boundaryChart x)
        (D.boundaryLower x) (D.boundaryUpper x)
    else
      interiorChartBoxNeighborhood I (D.interiorChart x)
        (D.interiorLower x) (D.interiorUpper x)
  have hnhds : ∀ x ∈ K, chartBox x ∈ 𝓝 x := by
    intro x hx
    simpa [chartBox] using D.chartBox_mem_nhds x hx
  obtain ⟨centers, hcentersK, hcover⟩ := hK.elim_nhds_subcover chartBox hnhds
  let interiorCenters : Finset M := centers.filter (fun x => D.isBoundary x = false)
  let boundaryCenters : Finset M := centers.filter (fun x => D.isBoundary x = true)
  refine ⟨{
    interiorCenters := interiorCenters
    boundaryCenters := boundaryCenters
    interior_center_mem := ?_
    boundary_center_mem := ?_
    interiorChart := D.interiorChart
    boundaryChart := D.boundaryChart
    interiorLower := D.interiorLower
    interiorUpper := D.interiorUpper
    boundaryLower := D.boundaryLower
    boundaryUpper := D.boundaryUpper
    interior_le := ?_
    interior_Icc_subset_domain := ?_
    boundary_lower_zero := ?_
    boundary_le := ?_
    boundary_Icc_subset_domain := ?_
    support_subset_cover := ?_ }, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro x hx
    exact hcentersK x ((Finset.mem_filter.mp hx).1)
  · intro x hx
    exact hcentersK x ((Finset.mem_filter.mp hx).1)
  · intro x hx
    exact D.interior_le x
      (hcentersK x ((Finset.mem_filter.mp hx).1))
      (Finset.mem_filter.mp hx).2
  · intro x hx
    exact D.interior_Icc_subset_domain x
      (hcentersK x ((Finset.mem_filter.mp hx).1))
      (Finset.mem_filter.mp hx).2
  · intro x hx
    exact D.boundary_lower_zero x
      (hcentersK x ((Finset.mem_filter.mp hx).1))
      (Finset.mem_filter.mp hx).2
  · intro x hx
    exact D.boundary_le x
      (hcentersK x ((Finset.mem_filter.mp hx).1))
      (Finset.mem_filter.mp hx).2
  · intro x hx
    exact D.boundary_Icc_subset_domain x
      (hcentersK x ((Finset.mem_filter.mp hx).1))
      (Finset.mem_filter.mp hx).2
  · intro y hy
    have hycover : y ∈ ⋃ x ∈ centers, chartBox x := hcover hy
    simp only [mem_iUnion, exists_prop] at hycover
    rcases hycover with ⟨x, hxmem, hyx⟩
    by_cases hxkind : D.isBoundary x = true
    · right
      refine mem_iUnion.mpr ⟨x, ?_⟩
      refine mem_iUnion.mpr ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hxmem, hxkind⟩
      · simpa [chartBox, hxkind] using hyx
    · left
      have hxfalse : D.isBoundary x = false := by
        cases h : D.isBoundary x
        · rfl
        · exact (hxkind h).elim
      refine mem_iUnion.mpr ⟨x, ?_⟩
      refine mem_iUnion.mpr ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hxmem, hxfalse⟩
      · simpa [chartBox, hxfalse] using hyx

end PointwiseCompactSupportChartBoxData

namespace CompactlySupportedSmoothFormData

variable {ω : ManifoldForm I M n}

/--
Compact-support wrapper for the finite mixed chart-box cover selection.
-/
theorem exists_chartBoxCoverSelection_of_pointwise
    (formData : CompactlySupportedSmoothFormData I ω)
    (D : PointwiseCompactSupportChartBoxData I formData.supportSet) :
    ∃ C : CompactSupportChartCoverSelection I formData.supportSet,
      C.interiorChart = D.interiorChart ∧
        C.boundaryChart = D.boundaryChart ∧
          C.interiorLower = D.interiorLower ∧
            C.interiorUpper = D.interiorUpper ∧
              C.boundaryLower = D.boundaryLower ∧
                C.boundaryUpper = D.boundaryUpper :=
  D.exists_finite_selection formData.isCompact_supportSet

end CompactlySupportedSmoothFormData

end MixedChartBoxCover

end Stokes

end
