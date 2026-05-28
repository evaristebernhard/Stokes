import Stokes.Global.CoverIndexedBulkSetIntegralConstructor
import Stokes.Global.CoverIndexedNaturalAssembly

/-!
# Initial bulk set integrals over assigned boxes

The closed-carrier bulk layer integrates each localized scalar over
`C.coverIndexClosedCarrier j`, because this is compact.  The local box theorems
more naturally identify `P.coverIndexLocalBulkTerm` with the set integral over
the strict assigned support box `C.assignedCoordinateBox j`.

This file packages that last transport step:

* prove the local term equality over the closed carrier from the initial
  assigned-box equality and topological support control;
* construct `CoverIndexedClosedCarrierBulkData` from assigned-box data;
* specialize the package to the canonical coordinate bulk integrands.

The remaining real mathematical input is now exactly the local assigned-box
set-integral identity for each cover index.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkInitialIntegralConstructor

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {μ : Measure (Fin (n + 1) → Real)}
variable [IsFiniteMeasureOnCompacts μ]

namespace CoverIndexedClosedCarrierBulkData

/--
Transport the initial local bulk identity from the assigned coordinate support
box to the compact closed carrier.

Mathematically this is just
`∫_{closed carrier} f = ∫_{assigned box} f`, because `f` is topologically
supported in the assigned box and the assigned box is contained in the closed
carrier.
-/
theorem localBulk_eq_setIntegral_closedCarrier_of_assignedCoordinateBox
    (pieceIntegrand : C.CoverIndex → (Fin (n + 1) → Real) → Real)
    (piece_tsupport_subset_assignedCoordinateBox :
      ∀ j : C.CoverIndex,
        tsupport (pieceIntegrand j) ⊆ C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_assignedCoordinateBox :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in C.assignedCoordinateBox j, pieceIntegrand j y ∂μ) :
    ∀ j : C.CoverIndex,
      P.coverIndexLocalBulkTerm ω j =
        ∫ y in C.coverIndexClosedCarrier j, pieceIntegrand j y ∂μ := by
  intro j
  exact
    localTerm_eq_setIntegral_over_superset_of_tsupport_subset
      (μ := μ)
      (s := C.assignedCoordinateBox j)
      (t := C.coverIndexClosedCarrier j)
      (f := pieceIntegrand j)
      (hs := C.measurableSet_assignedCoordinateBox j)
      (ht := (C.coverIndex_closedCarrier_isCompact j).measurableSet)
      (hst := C.coverIndex_openSupportBox_subset_closedCarrier j)
      (htsupport := piece_tsupport_subset_assignedCoordinateBox j)
      (hlocal := localBulk_eq_setIntegral_assignedCoordinateBox j)

/--
Build closed-carrier bulk data from the natural initial local identities over
assigned coordinate boxes.

This is the generic adapter for the natural assembly layer: callers no longer
need to provide local closed-carrier set-integral equalities by hand.
-/
def ofAssignedCoordinateBox
    (integrand : (Fin (n + 1) → Real) → Real)
    (pieceIntegrand : C.CoverIndex → (Fin (n + 1) → Real) → Real)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral = ∫ y, integrand y ∂μ)
    (piece_continuousOn_closedCarrier :
      ∀ j : C.CoverIndex,
        ContinuousOn (pieceIntegrand j) (C.coverIndexClosedCarrier j))
    (piece_tsupport_subset_assignedCoordinateBox :
      ∀ j : C.CoverIndex,
        tsupport (pieceIntegrand j) ⊆ C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_assignedCoordinateBox :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in C.assignedCoordinateBox j, pieceIntegrand j y ∂μ)
    (integrand_ae_eq_pieceSum :
      integrand =ᵐ[μ]
        fun y => ∑ j : C.CoverIndex, pieceIntegrand j y) :
    CoverIndexedClosedCarrierBulkData
      (I := I) (K := K) (μBulk := μ) C P ω where
  integrand := integrand
  pieceIntegrand := pieceIntegrand
  globalIntegral := globalIntegral
  globalIntegral_eq_integral := globalIntegral_eq_integral
  piece_continuousOn_closedCarrier := piece_continuousOn_closedCarrier
  piece_tsupport_subset_assignedCoordinateBox :=
    piece_tsupport_subset_assignedCoordinateBox
  localBulk_eq_setIntegral_closedCarrier :=
    localBulk_eq_setIntegral_closedCarrier_of_assignedCoordinateBox
      (C := C) (P := P) (ω := ω) (μ := μ)
      pieceIntegrand piece_tsupport_subset_assignedCoordinateBox
      localBulk_eq_setIntegral_assignedCoordinateBox
  integrand_ae_eq_pieceSum := integrand_ae_eq_pieceSum

end CoverIndexedClosedCarrierBulkData

namespace CoverIndexedResolvedBulkFields

/--
Resolved bulk fields from initial assigned-box local integral identities, with
the carrier fixed to `C.coverIndexClosedCarrier`.
-/
def ofAssignedCoordinateBox
    (integrand : (Fin (n + 1) → Real) → Real)
    (pieceIntegrand : C.CoverIndex → (Fin (n + 1) → Real) → Real)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral = ∫ y, integrand y ∂μ)
    (piece_continuousOn_closedCarrier :
      ∀ j : C.CoverIndex,
        ContinuousOn (pieceIntegrand j) (C.coverIndexClosedCarrier j))
    (piece_tsupport_subset_assignedCoordinateBox :
      ∀ j : C.CoverIndex,
        tsupport (pieceIntegrand j) ⊆ C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_assignedCoordinateBox :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in C.assignedCoordinateBox j, pieceIntegrand j y ∂μ)
    (integrand_ae_eq_pieceSum :
      integrand =ᵐ[μ]
        fun y => ∑ j : C.CoverIndex, pieceIntegrand j y) :
    CoverIndexedResolvedBulkFields
      (C := C) (ω := ω)
      (αBulk := Fin (n + 1) → Real) (μBulk := μ) P :=
  (CoverIndexedClosedCarrierBulkData.ofAssignedCoordinateBox
    (C := C) (P := P) (ω := ω) (μ := μ)
    integrand pieceIntegrand globalIntegral globalIntegral_eq_integral
    piece_continuousOn_closedCarrier
    piece_tsupport_subset_assignedCoordinateBox
    localBulk_eq_setIntegral_assignedCoordinateBox
    integrand_ae_eq_pieceSum).toResolvedBulkFields

end CoverIndexedResolvedBulkFields

namespace SupportControlledSelectedPartition

/--
The canonical coordinate bulk integrand of `ω` is a.e. the finite sum of the
canonical coordinate bulk integrands of the cover-indexed localized forms.
-/
theorem coordinateBulkIntegrand_ae_eq_pieceSum
    (P : SupportControlledSelectedPartition C)
    (x0 x1 : M)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (hdiff :
      ∀ᶠ y in ae μ,
        ∀ j : C.CoverIndex,
          DifferentiableAt Real
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (P.coverIndexLocalizedForm ω j)) y) :
    bulkIntegrand I x0 x1 ω =ᵐ[μ]
      fun y =>
        ∑ j : C.CoverIndex,
          bulkIntegrand I x0 x1
            (P.coverIndexLocalizedForm ω j) y := by
  classical
  have hraw :
      bulkIntegrand I x0 x1 ω =ᵐ[μ]
        fun y =>
          ∑ j ∈ (Finset.univ : Finset C.CoverIndex),
            bulkIntegrand I x0 x1
              (ManifoldForm.localizedForm I
                (fun z => P.partition j z) ω) y :=
    _root_.Stokes.coverIndexed_bulkIntegrand_ae_eq_sum_localized_of_support_subset
      (I := I) (active := (Finset.univ : Finset C.CoverIndex))
      (ρ := fun j z => P.partition j z) (ω := ω)
      (K := K) P.finite_sum_eq_one hωsupp μ x0 x1
      (by
        filter_upwards [hdiff] with y hy
        intro j _hj
        simpa [SupportControlledSelectedPartition.coverIndexLocalizedForm]
          using hy j)
  refine hraw.trans (Filter.Eventually.of_forall ?_)
  intro y
  simp [SupportControlledSelectedPartition.coverIndexLocalizedForm]

/--
Canonical coordinate closed-carrier bulk data from initial assigned-box local
integral identities.

This is the main worker-A handoff theorem for the natural assembly route.  The
unresolved mathematical lemma is the explicit input
`localBulk_eq_setIntegral_assignedCoordinateBox`.
-/
def coordinateClosedCarrierBulkData_of_assignedCoordinateBox
    (P : SupportControlledSelectedPartition C)
    (x0 x1 : M)
    (globalBulkIntegral : Real)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral =
        ∫ y, bulkIntegrand I x0 x1 ω y ∂μ)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (piece_continuousOn_closedCarrier :
      ∀ j : C.CoverIndex,
        ContinuousOn
          (fun y =>
            bulkIntegrand I x0 x1 (P.coverIndexLocalizedForm ω j) y)
          (C.coverIndexClosedCarrier j))
    (piece_tsupport_subset_assignedCoordinateBox :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I x0 x1
                (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_assignedCoordinateBox :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in C.assignedCoordinateBox j,
            bulkIntegrand I x0 x1
              (P.coverIndexLocalizedForm ω j) y ∂μ)
    (hdiff :
      ∀ᶠ y in ae μ,
        ∀ j : C.CoverIndex,
          DifferentiableAt Real
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (P.coverIndexLocalizedForm ω j)) y) :
    CoverIndexedClosedCarrierBulkData
      (I := I) (K := K) (μBulk := μ) C P ω :=
  CoverIndexedClosedCarrierBulkData.ofAssignedCoordinateBox
    (C := C) (P := P) (ω := ω) (μ := μ)
    (bulkIntegrand I x0 x1 ω)
    (fun j y =>
      bulkIntegrand I x0 x1 (P.coverIndexLocalizedForm ω j) y)
    globalBulkIntegral
    globalBulkIntegral_eq_integral
    piece_continuousOn_closedCarrier
    piece_tsupport_subset_assignedCoordinateBox
    localBulk_eq_setIntegral_assignedCoordinateBox
    (P.coordinateBulkIntegrand_ae_eq_pieceSum
      (ω := ω) (μ := μ) x0 x1 hωsupp hdiff)

/--
Resolved-bulk version of
`coordinateClosedCarrierBulkData_of_assignedCoordinateBox`.
-/
def coordinateResolvedBulkFields_of_assignedCoordinateBox
    (P : SupportControlledSelectedPartition C)
    (x0 x1 : M)
    (globalBulkIntegral : Real)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral =
        ∫ y, bulkIntegrand I x0 x1 ω y ∂μ)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (piece_continuousOn_closedCarrier :
      ∀ j : C.CoverIndex,
        ContinuousOn
          (fun y =>
            bulkIntegrand I x0 x1 (P.coverIndexLocalizedForm ω j) y)
          (C.coverIndexClosedCarrier j))
    (piece_tsupport_subset_assignedCoordinateBox :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I x0 x1
                (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_assignedCoordinateBox :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in C.assignedCoordinateBox j,
            bulkIntegrand I x0 x1
              (P.coverIndexLocalizedForm ω j) y ∂μ)
    (hdiff :
      ∀ᶠ y in ae μ,
        ∀ j : C.CoverIndex,
          DifferentiableAt Real
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (P.coverIndexLocalizedForm ω j)) y) :
    CoverIndexedResolvedBulkFields
      (C := C) (ω := ω)
      (αBulk := Fin (n + 1) → Real) (μBulk := μ) P :=
  (P.coordinateClosedCarrierBulkData_of_assignedCoordinateBox
    (ω := ω) (μ := μ) x0 x1 globalBulkIntegral
    globalBulkIntegral_eq_integral hωsupp
    piece_continuousOn_closedCarrier
    piece_tsupport_subset_assignedCoordinateBox
    localBulk_eq_setIntegral_assignedCoordinateBox hdiff).toResolvedBulkFields

end SupportControlledSelectedPartition

end BulkInitialIntegralConstructor

end Stokes

end
