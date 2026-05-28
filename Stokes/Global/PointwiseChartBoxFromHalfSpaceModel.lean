import Stokes.Global.HalfSpaceModel

/-!
# Pointwise chart boxes from the half-space model

This file hides the former public `PointwiseCompactSupportChartBoxData` input
when the model range is the project half-space.  The selected charts are self
charts; the first coordinate decides whether the point is treated as an
interior point or a boundary point.
-/

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace Stokes

section PointwiseFromHalfSpaceModel

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable [HalfSpaceModel I]

namespace PointwiseCompactSupportChartBoxData

private theorem self_coord_nonneg (x : M) :
    0 ≤ ((extChartAt I x) x) 0 := by
  simpa [upperHalfSpace] using
    HalfSpaceModel.self_coord_mem_upperHalfSpace (I := I) x

private theorem self_coord_pos_of_ne_zero {x : M}
    (hzero : ¬ ((extChartAt I x) x) 0 = 0) :
    0 < ((extChartAt I x) x) 0 :=
  lt_of_le_of_ne (self_coord_nonneg (I := I) x) (Ne.symm hzero)

/-- Interior self-chart box selection at a point whose normal coordinate is
strictly positive. -/
theorem exists_interiorSelfChartBox
    {x : M} (hpos : 0 < ((extChartAt I x) x) 0) :
    ∃ a b : Fin (n + 1) → Real,
      a ≤ b ∧
        (extChartAt I x) x ∈ boxInteriorSupportBox a b ∧
          interiorChartBoxNeighborhood I x a b ∈ 𝓝 x ∧
            Set.Icc a b ⊆ interiorChartDomain I x x := by
  have hxsource : x ∈ (extChartAt I x).source :=
    mem_extChartAt_source (I := I) x
  have htarget :
      (extChartAt I x).target ∈ 𝓝 ((extChartAt I x) x) :=
    HalfSpaceModel.self_target_mem_nhds_of_pos (I := I) hpos
  rcases exists_interiorChartBoxNeighborhood_subset_coord_nhds
      (I := I) (x := x) (chart := x)
      (U := (extChartAt I x).target) hxsource htarget with
    ⟨a, b, hle, hybox, hboxnhds, hIccTarget⟩
  refine ⟨a, b, hle, hybox, hboxnhds, ?_⟩
  intro z hz
  exact ⟨hIccTarget hz, (extChartAt I x).map_target (hIccTarget hz)⟩

/-- Boundary self-chart box selection at a point whose normal coordinate is
zero. -/
theorem exists_boundarySelfChartBox
    {x : M} (hzero : ((extChartAt I x) x) 0 = 0) :
    ∃ a b : Fin (n + 1) → Real,
      a 0 = 0 ∧
        a ≤ b ∧
          (extChartAt I x) x ∈ halfSpaceSupportBox a b ∧
            boundaryChartBoxNeighborhood I x a b ∈ 𝓝 x ∧
              Set.Icc a b ⊆ boundaryChartDomain I x x := by
  let y : Fin (n + 1) → Real := (extChartAt I x) x
  have hxsource : x ∈ (extChartAt I x).source :=
    mem_extChartAt_source (I := I) x
  have hytarget : y ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsource
  have hrel :
      (extChartAt I x).target ∈ 𝓝[Set.range I] y := by
    have hmem : y ∈ ManifoldForm.chartTransitionSource I x x := by
      rw [ManifoldForm.chartTransitionSource_self_eq_target]
      exact hytarget
    simpa [ManifoldForm.chartTransitionSource_self_eq_target] using
      (ManifoldForm.chartTransitionSource_mem_nhdsWithin_range_of_mem
        (I := I) hmem)
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hrel with
    ⟨U, hU, hUtarget⟩
  rcases exists_halfSpaceSupportBox_subset_of_boundary_mem_nhds
      (n := n) (U := U) (x := y) hzero hU with
    ⟨a, b, ha0, hle, hybox, hIccU⟩
  have hboxRel :
      halfSpaceSupportBox a b ∈ 𝓝[Set.range I] y :=
    HalfSpaceModel.halfSpaceSupportBox_mem_nhdsWithin_range_of_mem
      (I := I) ha0 hybox
  refine ⟨a, b, ha0, hle, hybox,
    HalfSpaceModel.boundaryChartBoxNeighborhood_mem_nhds_of_coordWithin
      (I := I) (chart := x) (x := x) hxsource hboxRel,
    ?_⟩
  intro z hz
  have hzrange : z ∈ Set.range I := by
    have hzhalf : z ∈ upperHalfSpace n :=
      HalfSpaceModel.Icc_subset_upperHalfSpace_of_lower_zero
        (n := n) ha0 hz
    simpa [HalfSpaceModel.upperHalfSpace_eq_range (I := I)] using hzhalf
  have hztarget : z ∈ (extChartAt I x).target :=
    hUtarget ⟨hIccU hz, hzrange⟩
  exact ⟨hztarget, (extChartAt I x).map_target hztarget⟩

private def selfIsBoundary (x : M) : Bool :=
  if ((extChartAt I x) x) 0 = 0 then true else false

private noncomputable def selfInteriorLower (x : M) : Fin (n + 1) → Real :=
  if hzero : ((extChartAt I x) x) 0 = 0 then
    0
  else
    Classical.choose (exists_interiorSelfChartBox (I := I)
      (self_coord_pos_of_ne_zero (I := I) hzero))

private noncomputable def selfInteriorUpper (x : M) : Fin (n + 1) → Real :=
  if hzero : ((extChartAt I x) x) 0 = 0 then
    0
  else
    Classical.choose (Classical.choose_spec
      (exists_interiorSelfChartBox (I := I)
        (self_coord_pos_of_ne_zero (I := I) hzero)))

private noncomputable def selfBoundaryLower (x : M) : Fin (n + 1) → Real :=
  if hzero : ((extChartAt I x) x) 0 = 0 then
    Classical.choose (exists_boundarySelfChartBox (I := I) hzero)
  else
    0

private noncomputable def selfBoundaryUpper (x : M) : Fin (n + 1) → Real :=
  if hzero : ((extChartAt I x) x) 0 = 0 then
    Classical.choose (Classical.choose_spec
      (exists_boundarySelfChartBox (I := I) hzero))
  else
    0

/-- Automatic pointwise chart-box data from self charts in the project
half-space model. -/
def ofHalfSpaceModelSelfCharts (K : Set M) :
    PointwiseCompactSupportChartBoxData I K where
  isBoundary := selfIsBoundary (I := I)
  interiorChart := fun x => x
  boundaryChart := fun x => x
  interiorLower := selfInteriorLower (I := I)
  interiorUpper := selfInteriorUpper (I := I)
  boundaryLower := selfBoundaryLower (I := I)
  boundaryUpper := selfBoundaryUpper (I := I)
  interior_le := by
    intro x _hx hboundary
    unfold selfIsBoundary at hboundary
    change (if ((extChartAt I x) x) 0 = 0 then true else false) = false at hboundary
    by_cases hzero : ((extChartAt I x) x) 0 = 0
    · rw [if_pos hzero] at hboundary
      cases hboundary
    · have hspec :=
        Classical.choose_spec
          (Classical.choose_spec
            (exists_interiorSelfChartBox (I := I)
              (self_coord_pos_of_ne_zero (I := I) hzero)))
      unfold selfInteriorLower selfInteriorUpper
      rw [dif_neg hzero, dif_neg hzero]
      exact hspec.1
  interior_Icc_subset_domain := by
    intro x _hx hboundary
    unfold selfIsBoundary at hboundary
    change (if ((extChartAt I x) x) 0 = 0 then true else false) = false at hboundary
    by_cases hzero : ((extChartAt I x) x) 0 = 0
    · rw [if_pos hzero] at hboundary
      cases hboundary
    · have hspec :=
        Classical.choose_spec
          (Classical.choose_spec
            (exists_interiorSelfChartBox (I := I)
              (self_coord_pos_of_ne_zero (I := I) hzero)))
      unfold selfInteriorLower selfInteriorUpper
      rw [dif_neg hzero, dif_neg hzero]
      exact hspec.2.2.2
  boundary_lower_zero := by
    intro x _hx hboundary
    unfold selfIsBoundary at hboundary
    change (if ((extChartAt I x) x) 0 = 0 then true else false) = true at hboundary
    by_cases hzero : ((extChartAt I x) x) 0 = 0
    · have hspec :=
        Classical.choose_spec
          (Classical.choose_spec
            (exists_boundarySelfChartBox (I := I) hzero))
      unfold selfBoundaryLower
      rw [dif_pos hzero]
      exact hspec.1
    · rw [if_neg hzero] at hboundary
      cases hboundary
  boundary_le := by
    intro x _hx hboundary
    unfold selfIsBoundary at hboundary
    change (if ((extChartAt I x) x) 0 = 0 then true else false) = true at hboundary
    by_cases hzero : ((extChartAt I x) x) 0 = 0
    · have hspec :=
        Classical.choose_spec
          (Classical.choose_spec
            (exists_boundarySelfChartBox (I := I) hzero))
      unfold selfBoundaryLower selfBoundaryUpper
      rw [dif_pos hzero, dif_pos hzero]
      exact hspec.2.1
    · rw [if_neg hzero] at hboundary
      cases hboundary
  boundary_Icc_subset_domain := by
    intro x _hx hboundary
    unfold selfIsBoundary at hboundary
    change (if ((extChartAt I x) x) 0 = 0 then true else false) = true at hboundary
    by_cases hzero : ((extChartAt I x) x) 0 = 0
    · have hspec :=
        Classical.choose_spec
          (Classical.choose_spec
            (exists_boundarySelfChartBox (I := I) hzero))
      unfold selfBoundaryLower selfBoundaryUpper
      rw [dif_pos hzero, dif_pos hzero]
      exact hspec.2.2.2.2
    · rw [if_neg hzero] at hboundary
      cases hboundary
  chartBox_mem_nhds := by
    intro x _hx
    unfold selfIsBoundary
    by_cases hzero : ((extChartAt I x) x) 0 = 0
    · have hspec :=
        Classical.choose_spec
          (Classical.choose_spec
            (exists_boundarySelfChartBox (I := I) hzero))
      unfold selfBoundaryLower selfBoundaryUpper
      rw [if_pos hzero, dif_pos hzero, dif_pos hzero]
      exact hspec.2.2.2.1
    · have hspec :=
        Classical.choose_spec
          (Classical.choose_spec
            (exists_interiorSelfChartBox (I := I)
              (self_coord_pos_of_ne_zero (I := I) hzero)))
      unfold selfInteriorLower selfInteriorUpper
      rw [if_neg hzero, dif_neg hzero, dif_neg hzero]
      exact hspec.2.2.1

end PointwiseCompactSupportChartBoxData

end PointwiseFromHalfSpaceModel

end Stokes

end
