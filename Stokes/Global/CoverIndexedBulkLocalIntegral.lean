import Stokes.Global.CoverIndexedBulkMeasureFacts
import Stokes.Global.CoverIndexedClosedCarrier

/-!
# Cover-indexed local bulk integrals over assigned boxes

This file proves the honest local set-integral identity available directly from
the definitions of the project-local bulk terms.

The important point is that `SupportControlledSelectedPartition.coverIndexLocalBulkTerm`
uses the chart attached to the selected cover index itself.  Thus the immediate
identity is the self-chart version

`bulkIntegrand I (C.assignedChart j) (C.assignedChart j) ...`,

not a fixed global chart pair.  A fixed chart-pair version needs an additional
bulk chart-change/change-of-variables theorem.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedBulkLocalIntegral

universe uH uM

section SetIntegralTransfer

universe uA

variable {α : Type uA} [TopologicalSpace α] [MeasurableSpace α]
variable {μ : Measure α}

private theorem setIntegral_eq_setIntegral_of_subset_of_tsupport_subset_local
    {s t : Set α} {f : α → Real}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) (htsupport : tsupport f ⊆ s) :
    (∫ x in t, f x ∂μ) = ∫ x in s, f x ∂μ := by
  rw [← integral_indicator ht, ← integral_indicator hs]
  refine integral_congr_ae (ae_of_all μ ?_)
  intro x
  by_cases hxs : x ∈ s
  · simp [Set.indicator_of_mem hxs, Set.indicator_of_mem (hst hxs)]
  · have hzero : f x = 0 := by
      exact Function.notMem_support.mp fun hx_support =>
        hxs (htsupport ((subset_tsupport f) hx_support))
    by_cases hxt : x ∈ t
    · simp [Set.indicator_of_notMem hxs, Set.indicator_of_mem hxt, hzero]
    · simp [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxt]

end SetIntegralTransfer

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace SupportControlledSelectedPartition

variable (P)

/--
Interior selected cover pieces: the local project-bulk term is the set integral
of the canonical self-chart bulk scalar over the assigned strict interior box,
provided that scalar has topological support in that assigned box.
-/
theorem coverIndexLocalBulkTerm_inl_eq_setIntegral_assigned_self_of_tsupport_subset
    (i : {x : M // x ∈ C.interiorCenters})
    (hsupp :
      tsupport
          (fun y =>
            bulkIntegrand I (C.interiorChart i.1) (C.interiorChart i.1)
              (P.coverIndexLocalizedForm ω (Sum.inl i)) y) ⊆
        C.assignedCoordinateBox (Sum.inl i)) :
    P.coverIndexLocalBulkTerm ω (Sum.inl i) =
      ∫ y in C.assignedCoordinateBox (Sum.inl i),
        bulkIntegrand I (C.interiorChart i.1) (C.interiorChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inl i)) y := by
  have hclosed :
      (∫ y in C.coverIndexClosedCarrier (Sum.inl i),
          bulkIntegrand I (C.interiorChart i.1) (C.interiorChart i.1)
            (P.coverIndexLocalizedForm ω (Sum.inl i)) y) =
        ∫ y in C.assignedCoordinateBox (Sum.inl i),
          bulkIntegrand I (C.interiorChart i.1) (C.interiorChart i.1)
            (P.coverIndexLocalizedForm ω (Sum.inl i)) y :=
    setIntegral_eq_setIntegral_of_subset_of_tsupport_subset_local
      (μ := volume)
      (s := C.assignedCoordinateBox (Sum.inl i))
      (t := C.coverIndexClosedCarrier (Sum.inl i))
      (f := fun y =>
        bulkIntegrand I (C.interiorChart i.1) (C.interiorChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inl i)) y)
      (C.measurableSet_assignedCoordinateBox (Sum.inl i))
      ((C.coverIndex_closedCarrier_isCompact (Sum.inl i)).measurableSet)
      (C.coverIndex_openSupportBox_subset_closedCarrier (Sum.inl i))
      hsupp
  have hlocal :
      P.coverIndexLocalBulkTerm ω (Sum.inl i) =
        ∫ y in C.coverIndexClosedCarrier (Sum.inl i),
          bulkIntegrand I (C.interiorChart i.1) (C.interiorChart i.1)
            (P.coverIndexLocalizedForm ω (Sum.inl i)) y := by
    simp [SupportControlledSelectedPartition.coverIndexLocalBulkTerm,
      CompactSupportChartCoverSelection.coverIndexClosedCarrier,
      CompactSupportChartCoverSelection.assignedLower,
      CompactSupportChartCoverSelection.assignedUpper,
      projectInteriorBulkIntegral, bulkIntegrand]
  exact hlocal.trans hclosed

/--
Boundary selected cover pieces: the half-space project-bulk term is the set
integral of the canonical self-chart bulk scalar over the assigned strict
half-space support box, provided that scalar has topological support in that
assigned box.
-/
theorem coverIndexLocalBulkTerm_inr_eq_setIntegral_assigned_self_of_tsupport_subset
    (i : {x : M // x ∈ C.boundaryCenters})
    (hsupp :
      tsupport
          (fun y =>
            bulkIntegrand I (C.boundaryChart i.1) (C.boundaryChart i.1)
              (P.coverIndexLocalizedForm ω (Sum.inr i)) y) ⊆
        C.assignedCoordinateBox (Sum.inr i)) :
    P.coverIndexLocalBulkTerm ω (Sum.inr i) =
      ∫ y in C.assignedCoordinateBox (Sum.inr i),
        bulkIntegrand I (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i)) y := by
  have hclosed :
      (∫ y in C.coverIndexClosedCarrier (Sum.inr i),
          bulkIntegrand I (C.boundaryChart i.1) (C.boundaryChart i.1)
            (P.coverIndexLocalizedForm ω (Sum.inr i)) y) =
        ∫ y in C.assignedCoordinateBox (Sum.inr i),
          bulkIntegrand I (C.boundaryChart i.1) (C.boundaryChart i.1)
            (P.coverIndexLocalizedForm ω (Sum.inr i)) y :=
    setIntegral_eq_setIntegral_of_subset_of_tsupport_subset_local
      (μ := volume)
      (s := C.assignedCoordinateBox (Sum.inr i))
      (t := C.coverIndexClosedCarrier (Sum.inr i))
      (f := fun y =>
        bulkIntegrand I (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i)) y)
      (C.measurableSet_assignedCoordinateBox (Sum.inr i))
      ((C.coverIndex_closedCarrier_isCompact (Sum.inr i)).measurableSet)
      (C.coverIndex_openSupportBox_subset_closedCarrier (Sum.inr i))
      hsupp
  have hlocal :
      P.coverIndexLocalBulkTerm ω (Sum.inr i) =
        ∫ y in C.coverIndexClosedCarrier (Sum.inr i),
          bulkIntegrand I (C.boundaryChart i.1) (C.boundaryChart i.1)
            (P.coverIndexLocalizedForm ω (Sum.inr i)) y := by
    simp [SupportControlledSelectedPartition.coverIndexLocalBulkTerm,
      CompactSupportChartCoverSelection.coverIndexClosedCarrier,
      CompactSupportChartCoverSelection.assignedLower,
      CompactSupportChartCoverSelection.assignedUpper,
      projectLocalBulkIntegral, halfSpaceLocalTransitionBulkIntegral,
      halfSpaceLocalBulkIntegral, bulkIntegrand]
  exact hlocal.trans hclosed

/--
Cover-indexed self-chart local bulk identity over the assigned strict support
box.  This is the direct local integral lemma available without any bulk chart
change theorem.
-/
theorem coverIndexLocalBulkTerm_eq_setIntegral_assigned_self_of_tsupport_subset
    (hsupp :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I (C.assignedChart j) (C.assignedChart j)
                (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j) :
    ∀ j : C.CoverIndex,
      P.coverIndexLocalBulkTerm ω j =
        ∫ y in C.assignedCoordinateBox j,
          bulkIntegrand I (C.assignedChart j) (C.assignedChart j)
            (P.coverIndexLocalizedForm ω j) y := by
  intro j
  rcases j with i | i
  · simpa [CompactSupportChartCoverSelection.assignedChart] using
      P.coverIndexLocalBulkTerm_inl_eq_setIntegral_assigned_self_of_tsupport_subset
        (C := C) (ω := ω) i (by
          simpa [CompactSupportChartCoverSelection.assignedChart] using
            hsupp (Sum.inl i))
  · simpa [CompactSupportChartCoverSelection.assignedChart] using
      P.coverIndexLocalBulkTerm_inr_eq_setIntegral_assigned_self_of_tsupport_subset
        (C := C) (ω := ω) i (by
          simpa [CompactSupportChartCoverSelection.assignedChart] using
            hsupp (Sum.inr i))

/--
Same self-chart identity for a measure definitionally or propositionally equal
to `volume`.
-/
theorem coverIndexLocalBulkTerm_eq_setIntegral_assigned_self_of_tsupport_subset_of_measure_eq_volume
    {μ : Measure (Fin (n + 1) → Real)}
    (hμ : μ = volume)
    (hsupp :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I (C.assignedChart j) (C.assignedChart j)
                (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j) :
    ∀ j : C.CoverIndex,
      P.coverIndexLocalBulkTerm ω j =
        ∫ y in C.assignedCoordinateBox j,
          bulkIntegrand I (C.assignedChart j) (C.assignedChart j)
            (P.coverIndexLocalizedForm ω j) y ∂μ := by
  subst hμ
  exact
    P.coverIndexLocalBulkTerm_eq_setIntegral_assigned_self_of_tsupport_subset
      (C := C) (ω := ω) hsupp

/--
Adapter for a single index whose requested chart pair is known to be the
selected self-chart.  Without hypotheses of this shape, a fixed global
`sourceChart`/`targetChart` statement is not definitionally implied by
`coverIndexLocalBulkTerm`; it needs a separate bulk chart-change theorem.
-/
theorem coverIndexLocalBulkTerm_eq_setIntegral_assigned_of_eq_assignedChart
    {μ : Measure (Fin (n + 1) → Real)}
    (hμ : μ = volume)
    (j : C.CoverIndex) {sourceChart targetChart : M}
    (hsource : sourceChart = C.assignedChart j)
    (htarget : targetChart = C.assignedChart j)
    (hsupp :
      tsupport
          (fun y =>
            bulkIntegrand I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j) y) ⊆
        C.assignedCoordinateBox j) :
    P.coverIndexLocalBulkTerm ω j =
      ∫ y in C.assignedCoordinateBox j,
        bulkIntegrand I sourceChart targetChart
          (P.coverIndexLocalizedForm ω j) y ∂μ := by
  subst hsource
  subst htarget
  subst hμ
  rcases j with i | i
  · simpa [CompactSupportChartCoverSelection.assignedChart] using
      P.coverIndexLocalBulkTerm_inl_eq_setIntegral_assigned_self_of_tsupport_subset
        (C := C) (ω := ω) i (by
          simpa [CompactSupportChartCoverSelection.assignedChart] using hsupp)
  · simpa [CompactSupportChartCoverSelection.assignedChart] using
      P.coverIndexLocalBulkTerm_inr_eq_setIntegral_assigned_self_of_tsupport_subset
        (C := C) (ω := ω) i (by
          simpa [CompactSupportChartCoverSelection.assignedChart] using hsupp)

end SupportControlledSelectedPartition

end CoverIndexedBulkLocalIntegral

end Stokes

end
