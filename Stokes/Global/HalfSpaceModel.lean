import Stokes.Global.CompactSupportChartCoverSelection
import Stokes.ManifoldFormChartTransitionSourceSelfCore
import Stokes.ManifoldFormChartTransitionOpenCore

/-!
# Half-space model helper API

This file records the minimal project-level assumption that the concrete model
with corners has coordinate range equal to the closed upper half-space used by
the local Stokes layer.

The class is a background geometric assumption on the model, not a field of the
Stokes input form.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set Filter
open scoped Manifold Topology

namespace Stokes

universe uH uM

section HalfSpaceModel

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable (I : ModelWithCorners Real (Fin (n + 1) → Real) H)

/-- The model-coordinate range is the project half-space `{x | 0 ≤ x 0}`. -/
class HalfSpaceModel : Prop where
  range_eq_upperHalfSpace : Set.range I = upperHalfSpace n

namespace HalfSpaceModel

variable [HalfSpaceModel I]

theorem range_eq : Set.range I = upperHalfSpace n :=
  HalfSpaceModel.range_eq_upperHalfSpace (I := I)

theorem upperHalfSpace_eq_range : upperHalfSpace n = Set.range I :=
  (range_eq (I := I)).symm

theorem extChartAt_target_subset_upperHalfSpace (x : M) :
    (extChartAt I x).target ⊆ upperHalfSpace n := by
  intro y hy
  have hyrange : y ∈ Set.range I := extChartAt_target_subset_range x hy
  simpa [range_eq (I := I)] using hyrange

theorem self_coord_mem_upperHalfSpace (x : M) :
    (extChartAt I x) x ∈ upperHalfSpace n := by
  exact extChartAt_target_subset_upperHalfSpace (I := I) x
    ((extChartAt I x).map_source (mem_extChartAt_source (I := I) x))

/-- Interior points of the model half-space see the half-space as an ordinary
ambient neighborhood. -/
theorem upperHalfSpace_mem_nhds_of_pos
    {y : Fin (n + 1) → Real} (hypos : 0 < y 0) :
    upperHalfSpace n ∈ 𝓝 y := by
  have hpre :
      {z : Fin (n + 1) → Real | 0 < z 0} ∈ 𝓝 y := by
    simpa using
      ((continuous_apply (0 : Fin (n + 1))).continuousAt.preimage_mem_nhds
        (isOpen_Ioi.mem_nhds hypos))
  exact mem_of_superset hpre (by
    intro z hz
    simpa [upperHalfSpace] using (le_of_lt (show 0 < z 0 from hz)))

theorem mem_nhds_of_mem_nhdsWithin_of_mem_nhds
    {α : Type*} [TopologicalSpace α] {s t : Set α} {x : α}
    (hs : s ∈ 𝓝[t] x) (ht : t ∈ 𝓝 x) :
    s ∈ 𝓝 x := by
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hs with ⟨u, hu, hus⟩
  exact mem_of_superset (inter_mem hu ht) (by
    intro y hy
    exact hus ⟨hy.1, hy.2⟩)

/-- A self extended-chart target is an ordinary neighborhood of an interior
model point. -/
theorem self_target_mem_nhds_of_pos
    {x : M} (hypos : 0 < ((extChartAt I x) x) 0) :
    (extChartAt I x).target ∈ 𝓝 ((extChartAt I x) x) := by
  have htarget :
      (extChartAt I x).target ∈ 𝓝[Set.range I] ((extChartAt I x) x) := by
    have hmem :
        (extChartAt I x) x ∈ ManifoldForm.chartTransitionSource I x x := by
      rw [ManifoldForm.chartTransitionSource_self_eq_target]
      exact (extChartAt I x).map_source (mem_extChartAt_source (I := I) x)
    simpa [ManifoldForm.chartTransitionSource_self_eq_target] using
      (ManifoldForm.chartTransitionSource_mem_nhdsWithin_range_of_mem
        (I := I) hmem)
  have hrange : Set.range I ∈ 𝓝 ((extChartAt I x) x) := by
    simpa [range_eq (I := I)] using
      upperHalfSpace_mem_nhds_of_pos (n := n) hypos
  exact mem_nhds_of_mem_nhdsWithin_of_mem_nhds htarget hrange

/-- A relative coordinate neighborhood pulls back to a genuine manifold
neighborhood through an extended chart source. -/
theorem chart_preimage_mem_nhds_of_mem_nhdsWithin_range
    {chart x : M} {s : Set (Fin (n + 1) → Real)}
    (hxsource : x ∈ (extChartAt I chart).source)
    (hs :
      s ∈ 𝓝[Set.range I] ((extChartAt I chart) x)) :
    {p : M | p ∈ (extChartAt I chart).source ∧ (extChartAt I chart) p ∈ s}
      ∈ 𝓝 x := by
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hs with ⟨u, hu, hus⟩
  have hsource : (extChartAt I chart).source ∈ 𝓝 x :=
    extChartAt_source_mem_nhds' (I := I) hxsource
  have hpre :
      (extChartAt I chart) ⁻¹' u ∈ 𝓝 x :=
    (continuousAt_extChartAt' (I := I) hxsource).preimage_mem_nhds hu
  exact mem_of_superset (inter_mem hsource hpre) (by
    intro p hp
    have htarget : (extChartAt I chart) p ∈ (extChartAt I chart).target :=
      (extChartAt I chart).map_source hp.1
    have hrange : (extChartAt I chart) p ∈ Set.range I :=
      extChartAt_target_subset_range chart htarget
    exact ⟨hp.1, hus ⟨hp.2, hrange⟩⟩)

theorem boundaryChartBoxNeighborhood_mem_nhds_of_coordWithin
    {chart x : M} {a b : Fin (n + 1) → Real}
    (hxsource : x ∈ (extChartAt I chart).source)
    (hbox :
      halfSpaceSupportBox a b ∈
        𝓝[Set.range I] ((extChartAt I chart) x)) :
    boundaryChartBoxNeighborhood I chart a b ∈ 𝓝 x := by
  simpa [boundaryChartBoxNeighborhood] using
    chart_preimage_mem_nhds_of_mem_nhdsWithin_range
      (I := I) (chart := chart) (x := x)
      (s := halfSpaceSupportBox a b) hxsource hbox

theorem halfSpaceSupportBox_mem_nhdsWithin_upperHalfSpace_of_mem
    {a b y : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hy : y ∈ halfSpaceSupportBox a b) :
    halfSpaceSupportBox a b ∈ 𝓝[upperHalfSpace n] y := by
  have hnormal :
      {z : Fin (n + 1) → Real | z 0 < b 0} ∈ 𝓝 y := by
    simpa using
      ((continuous_apply (0 : Fin (n + 1))).continuousAt.preimage_mem_nhds
        (isOpen_Iio.mem_nhds hy.2.1))
  have htangent :
      (⋂ i : Fin n,
        {z : Fin (n + 1) → Real |
          a i.succ < z i.succ ∧ z i.succ < b i.succ}) ∈ 𝓝 y := by
    refine Filter.iInter_mem.mpr ?_
    intro i
    have hleft :
        {z : Fin (n + 1) → Real | a i.succ < z i.succ} ∈ 𝓝 y := by
      simpa using
        ((continuous_apply i.succ).continuousAt.preimage_mem_nhds
          (isOpen_Ioi.mem_nhds (hy.2.2 i).1))
    have hright :
        {z : Fin (n + 1) → Real | z i.succ < b i.succ} ∈ 𝓝 y := by
      simpa using
        ((continuous_apply i.succ).continuousAt.preimage_mem_nhds
          (isOpen_Iio.mem_nhds (hy.2.2 i).2))
    exact inter_mem hleft hright
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine ⟨{z : Fin (n + 1) → Real | z 0 < b 0} ∩
      (⋂ i : Fin n,
        {z : Fin (n + 1) → Real |
          a i.succ < z i.succ ∧ z i.succ < b i.succ}),
    inter_mem hnormal htangent, ?_⟩
  intro z hz
  rcases hz with ⟨⟨hz0lt, hztan⟩, hzhalf⟩
  refine ⟨?_, hz0lt, ?_⟩
  · simpa [ha0, upperHalfSpace] using hzhalf
  · intro i
    exact mem_iInter.mp hztan i

theorem halfSpaceSupportBox_mem_nhdsWithin_range_of_mem
    {a b y : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hy : y ∈ halfSpaceSupportBox a b) :
    halfSpaceSupportBox a b ∈ 𝓝[Set.range I] y := by
  simpa [range_eq (I := I)] using
    halfSpaceSupportBox_mem_nhdsWithin_upperHalfSpace_of_mem
      (n := n) (a := a) (b := b) (y := y) ha0 hy

theorem Icc_subset_upperHalfSpace_of_lower_zero
    {a b : Fin (n + 1) → Real} (ha0 : a 0 = 0) :
    Set.Icc a b ⊆ upperHalfSpace n := by
  intro z hz
  simpa [upperHalfSpace, ha0] using hz.1 0

end HalfSpaceModel

end HalfSpaceModel

end Stokes

end
