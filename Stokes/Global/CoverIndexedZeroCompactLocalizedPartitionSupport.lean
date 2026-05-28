import Stokes.Global.CoverIndexedZeroCompactLocalizedTargetSupport

/-!
# Localized partition support for compact zero endpoints

This file supplies the missing support-propagation bridge from a
support-controlled selected partition to the target zero representative used by
the compact-support zero endpoint.

The useful shape is local: if a localized boundary piece is supported in the
preimage of a selected target box, then its zero-extended target chart
representative has `tsupport` in that box.  The partition support control gives
one natural way to prove that preimage support condition.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section LocalizedPartitionSupport

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace ManifoldForm

/-- Ordinary support version: if a manifold-side form is supported in the
preimage of a target coordinate box, then its zero-extended chart
representative is supported in that coordinate box. -/
theorem inChartZero_support_subset_Icc_of_support_subset_preimage
    {x : M} {η : ManifoldForm I M n} {c d : Fin (n + 1) → Real}
    (hsupport : support I η ⊆ {p : M | (extChartAt I x) p ∈ Icc c d}) :
    Function.support (inChartZero I x η) ⊆ Icc c d := by
  intro y hy
  have hyne : inChartZero I x η y ≠ 0 := by
    simpa [Function.mem_support] using hy
  have htarget : y ∈ (extChartAt I x).target :=
    inChartZero_support_subset_target (I := I) x η hy
  have hpSupport : (extChartAt I x).symm y ∈ support I η :=
    inChartZero_ne_zero_mapsTo_support (I := I) (x := x) (ω := η) hyne
  have hpIcc : (extChartAt I x) ((extChartAt I x).symm y) ∈ Icc c d :=
    hsupport hpSupport
  have hright : (extChartAt I x) ((extChartAt I x).symm y) = y :=
    (extChartAt I x).right_inv htarget
  rwa [hright] at hpIcc

/-- Topological support version of
`inChartZero_support_subset_Icc_of_support_subset_preimage`. -/
theorem inChartZero_tsupport_subset_Icc_of_support_subset_preimage
    {x : M} {η : ManifoldForm I M n} {c d : Fin (n + 1) → Real}
    (hsupport : support I η ⊆ {p : M | (extChartAt I x) p ∈ Icc c d}) :
    tsupport (inChartZero I x η) ⊆ Icc c d := by
  simpa [tsupport] using
    closure_minimal
      (inChartZero_support_subset_Icc_of_support_subset_preimage
        (I := I) (x := x) (η := η) (c := c) (d := d) hsupport)
      (isClosed_Icc : IsClosed (Icc c d))

end ManifoldForm

namespace SupportControlledSelectedPartition

/-- A cover-indexed localized form is supported in its assigned cover set,
provided the original form is supported in the controlled compact set `K`. -/
theorem coverIndexLocalizedForm_support_subset_assignedCoverSet_of_globalSupport
    (P : SupportControlledSelectedPartition C)
    (hωsupport : ManifoldForm.support I ω ⊆ K)
    (j : C.CoverIndex) :
    ManifoldForm.support I (P.coverIndexLocalizedForm ω j) ⊆
      C.assignedCoverSet j := by
  intro p hp
  have hpcoeffSupport : p ∈ Function.support (P.partition j) := by
    exact
      ManifoldForm.localizedForm_support_subset_coefficient_support
        (I := I) (P.partition j) ω
        (by
          simpa [SupportControlledSelectedPartition.coverIndexLocalizedForm]
            using hp)
  have hpcoeffTSupport : p ∈ tsupport (P.partition j) :=
    subset_closure hpcoeffSupport
  have hpForm : p ∈ ManifoldForm.support I ω := by
    exact
      ManifoldForm.localizedForm_support_subset_form_support
        (I := I) (P.partition j) ω
        (by
          simpa [SupportControlledSelectedPartition.coverIndexLocalizedForm]
            using hp)
  exact P.tsupport_inter_subset_assigned j ⟨hpcoeffTSupport, hωsupport hpForm⟩

/-- Boundary-index specialization of
`coverIndexLocalizedForm_support_subset_assignedCoverSet_of_globalSupport`. -/
theorem boundary_coverIndexLocalizedForm_support_subset_assignedCoverSet_of_globalSupport
    (P : SupportControlledSelectedPartition C)
    (hωsupport : ManifoldForm.support I ω ⊆ K)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ManifoldForm.support I (P.coverIndexLocalizedForm ω (Sum.inr i)) ⊆
      boundaryChartBoxNeighborhood I (C.boundaryChart i.1)
        (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  simpa [CompactSupportChartCoverSelection.assignedCoverSet] using
    P.coverIndexLocalizedForm_support_subset_assignedCoverSet_of_globalSupport
      (I := I) (K := K) (ω := ω) hωsupport (Sum.inr i)

end SupportControlledSelectedPartition

namespace CoverIndexedBoundaryTargetBoxData

variable
  (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω)

/-- Direct target-zero support bridge from localized manifold-side support in
the selected target-chart preimage of the target box. -/
theorem targetInChartZero_tsupport_subset_Icc_of_localizedSupport_subset_preimage
    (hsupport :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ManifoldForm.support I (P.coverIndexLocalizedForm ω (Sum.inr i)) ⊆
          {p : M | (extChartAt I (D.targetChart i)) p ∈
            Icc (D.targetLower i) (D.targetUpper i)}) :
    D.TargetInChartZeroTSupportSubsetIccField := by
  intro i
  exact
    ManifoldForm.inChartZero_tsupport_subset_Icc_of_support_subset_preimage
      (I := I) (x := D.targetChart i)
      (η := P.coverIndexLocalizedForm ω (Sum.inr i))
      (c := D.targetLower i) (d := D.targetUpper i)
      (hsupport i)

/-- Use the selected partition support control, plus a target-preimage
containment for the assigned cover set, to build the target zero `tsupport`
field needed by compact zero endpoints. -/
theorem targetInChartZero_tsupport_subset_Icc_of_assignedCoverSet_subset_preimage
    (hωsupport : ManifoldForm.support I ω ⊆ K)
    (hassigned :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        C.assignedCoverSet (Sum.inr i) ⊆
          {p : M | (extChartAt I (D.targetChart i)) p ∈
            Icc (D.targetLower i) (D.targetUpper i)}) :
    D.TargetInChartZeroTSupportSubsetIccField :=
  D.targetInChartZero_tsupport_subset_Icc_of_localizedSupport_subset_preimage
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (fun i =>
      (P.coverIndexLocalizedForm_support_subset_assignedCoverSet_of_globalSupport
        (I := I) (K := K) (ω := ω) hωsupport (Sum.inr i)).trans
        (hassigned i))

/-- Boundary-box version of
`targetInChartZero_tsupport_subset_Icc_of_assignedCoverSet_subset_preimage`.
This is the natural statement after unfolding the boundary branch of the
selected cover. -/
theorem targetInChartZero_tsupport_subset_Icc_of_boundaryBox_subset_preimage
    (hωsupport : ManifoldForm.support I ω ⊆ K)
    (hbox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartBoxNeighborhood I (C.boundaryChart i.1)
            (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          {p : M | (extChartAt I (D.targetChart i)) p ∈
            Icc (D.targetLower i) (D.targetUpper i)}) :
    D.TargetInChartZeroTSupportSubsetIccField :=
  D.targetInChartZero_tsupport_subset_Icc_of_assignedCoverSet_subset_preimage
    (I := I) (K := K) (C := C) (P := P) (ω := ω) hωsupport
    (by
      intro i
      simpa [CompactSupportChartCoverSelection.assignedCoverSet] using hbox i)

end CoverIndexedBoundaryTargetBoxData

end LocalizedPartitionSupport

end Stokes

end
