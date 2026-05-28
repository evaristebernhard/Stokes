import Stokes.Global.CoverIndexedResolvedInput
import Stokes.Global.CoverIndexedClosedCarrier
import Stokes.Global.CoverIndexedBulkMeasureFacts
import Stokes.Global.BulkBoundaryIccHalfSpaceTransfer

/-!
# Cover-indexed bulk set integrals over closed carriers

The support-controlled cover gives an assigned coordinate support box for each
cover index.  Those boxes are the right sets for zero/support arguments, but
they need not be compact.  The measure layer should instead integrate over the
closed carrier `C.coverIndexClosedCarrier j`.

This file packages the honest transfer:

* if a local bulk scalar is supported in a measurable set `s`;
* and `s` is contained in a compact carrier `t`;
* and the recorded local bulk term is the set integral over `s`;

then the same local bulk term is the set integral over `t`.

The final constructors specialize this to the coordinate bulk integrands of a
support-controlled selected chart cover.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section SetIntegralCarrierTransfer

universe u

variable {α : Type u} [TopologicalSpace α] [MeasurableSpace α]
variable {μ : Measure α}

/--
If `s ⊆ t` and the topological support of `f` is contained in `s`, then the
integral over the larger carrier `t` equals the integral over `s`.
-/
theorem setIntegral_eq_setIntegral_of_subset_of_tsupport_subset
    {s t : Set α} {f : α → Real}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) (htsupport : tsupport f ⊆ s) :
    (∫ x in t, f x ∂μ) = ∫ x in s, f x ∂μ :=
  setIntegral_eq_setIntegral_of_subset_of_support_subset
    (μ := μ) (s := s) (t := t) (f := f) hs ht hst
    ((subset_tsupport f).trans htsupport)

/--
Zero-off-set version of the same carrier transfer.  This is useful when the
support control was proved as a pointwise vanishing statement.
-/
theorem setIntegral_eq_setIntegral_of_subset_of_eq_zero_off
    {s t : Set α} {f : α → Real}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) (hzero : ∀ x, x ∉ s → f x = 0) :
    (∫ x in t, f x ∂μ) = ∫ x in s, f x ∂μ := by
  refine setIntegral_eq_setIntegral_of_subset_of_support_subset
    (μ := μ) (s := s) (t := t) (f := f) hs ht hst ?_
  intro x hx
  by_contra hxs
  exact hx (hzero x hxs)

/--
Transport a recorded local term from integration over a support set to
integration over a larger carrier.
-/
theorem localTerm_eq_setIntegral_over_superset_of_tsupport_subset
    {s t : Set α} {f : α → Real} {localTerm : Real}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) (htsupport : tsupport f ⊆ s)
    (hlocal : localTerm = ∫ x in s, f x ∂μ) :
    localTerm = ∫ x in t, f x ∂μ :=
  hlocal.trans
    (setIntegral_eq_setIntegral_of_subset_of_tsupport_subset
      (μ := μ) (s := s) (t := t) (f := f)
      hs ht hst htsupport).symm

/--
Zero-off-set variant of `localTerm_eq_setIntegral_over_superset_of_tsupport_subset`.
-/
theorem localTerm_eq_setIntegral_over_superset_of_eq_zero_off
    {s t : Set α} {f : α → Real} {localTerm : Real}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) (hzero : ∀ x, x ∉ s → f x = 0)
    (hlocal : localTerm = ∫ x in s, f x ∂μ) :
    localTerm = ∫ x in t, f x ∂μ :=
  hlocal.trans
    (setIntegral_eq_setIntegral_of_subset_of_eq_zero_off
      (μ := μ) (s := s) (t := t) (f := f)
      hs ht hst hzero).symm

end SetIntegralCarrierTransfer

section SupportControlledBulkCarrier

universe uH uM uA

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {αBulk : Type uA} [TopologicalSpace αBulk]
variable [MeasurableSpace αBulk] [OpensMeasurableSpace αBulk]
variable [T2Space αBulk]
variable {μBulk : Measure αBulk} [IsFiniteMeasureOnCompacts μBulk]

namespace SupportControlledSelectedPartition

/--
Bulk set-integral fields over compact carrier sets, when the local term is
initially known as an integral over a smaller support set.

This is the generic closed-carrier adapter: callers provide the support sets
`bulkSupportSet`, compact carriers `bulkCarrierSet`, and the inclusion
`bulkSupportSet j ⊆ bulkCarrierSet j`.  The constructor transports
`localBulk_eq_setIntegral` to the carrier before invoking the existing
cover-indexed bulk measure constructor.
-/
def coverIndexedBulkSetIntegralFields_of_pieceSum_over_superset
    (P : SupportControlledSelectedPartition C)
    (bulkIntegrand : αBulk → Real)
    (bulkSupportSet bulkCarrierSet : C.CoverIndex → Set αBulk)
    (bulkPieceIntegrand : C.CoverIndex → αBulk → Real)
    (globalBulkIntegral : Real)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral = ∫ y, bulkIntegrand y ∂μBulk)
    (bulkSupportSet_measurable :
      ∀ j : C.CoverIndex, MeasurableSet (bulkSupportSet j))
    (bulkCarrier_isCompact :
      ∀ j : C.CoverIndex, IsCompact (bulkCarrierSet j))
    (bulkSupport_subset_carrier :
      ∀ j : C.CoverIndex, bulkSupportSet j ⊆ bulkCarrierSet j)
    (bulkPiece_continuousOn_carrier :
      ∀ j : C.CoverIndex,
        ContinuousOn (bulkPieceIntegrand j) (bulkCarrierSet j))
    (bulkPiece_tsupport_subset_support :
      ∀ j : C.CoverIndex,
        tsupport (bulkPieceIntegrand j) ⊆ bulkSupportSet j)
    (localBulk_eq_setIntegral_support :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in bulkSupportSet j, bulkPieceIntegrand j y ∂μBulk)
    (bulkIntegrand_ae_eq_pieceSum :
      bulkIntegrand =ᵐ[μBulk]
        fun y => ∑ j : C.CoverIndex, bulkPieceIntegrand j y) :
    CoverIndexedSetIntegralFields
      (α := αBulk) (Finset.univ : Finset C.CoverIndex) μBulk
      (P.coverIndexLocalBulkTerm ω) :=
  P.coverIndexedBulkSetIntegralFields_of_pieceSum
    (ω := ω) (μBulk := μBulk)
    (bulkIntegrand := bulkIntegrand)
    (bulkPieceSet := bulkCarrierSet)
    (bulkPieceIntegrand := bulkPieceIntegrand)
    (globalBulkIntegral := globalBulkIntegral)
    globalBulkIntegral_eq_integral
    bulkCarrier_isCompact
    bulkPiece_continuousOn_carrier
    (fun j =>
      (bulkPiece_tsupport_subset_support j).trans
        (bulkSupport_subset_carrier j))
    (fun j =>
      localTerm_eq_setIntegral_over_superset_of_tsupport_subset
        (μ := μBulk)
        (s := bulkSupportSet j) (t := bulkCarrierSet j)
        (f := bulkPieceIntegrand j)
        (hs := bulkSupportSet_measurable j)
        (ht := (bulkCarrier_isCompact j).measurableSet)
        (hst := bulkSupport_subset_carrier j)
        (htsupport := bulkPiece_tsupport_subset_support j)
        (hlocal := localBulk_eq_setIntegral_support j))
    bulkIntegrand_ae_eq_pieceSum

end SupportControlledSelectedPartition

namespace CoverIndexedResolvedBulkFields

/--
Resolved bulk fields over compact carriers, with local terms transported from
smaller support sets.
-/
def ofPieceSumOverSuperset
    (P : SupportControlledSelectedPartition C)
    (bulkIntegrand : αBulk → Real)
    (bulkSupportSet bulkCarrierSet : C.CoverIndex → Set αBulk)
    (bulkPieceIntegrand : C.CoverIndex → αBulk → Real)
    (globalBulkIntegral : Real)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral = ∫ y, bulkIntegrand y ∂μBulk)
    (bulkSupportSet_measurable :
      ∀ j : C.CoverIndex, MeasurableSet (bulkSupportSet j))
    (bulkCarrier_isCompact :
      ∀ j : C.CoverIndex, IsCompact (bulkCarrierSet j))
    (bulkSupport_subset_carrier :
      ∀ j : C.CoverIndex, bulkSupportSet j ⊆ bulkCarrierSet j)
    (bulkPiece_continuousOn_carrier :
      ∀ j : C.CoverIndex,
        ContinuousOn (bulkPieceIntegrand j) (bulkCarrierSet j))
    (bulkPiece_tsupport_subset_support :
      ∀ j : C.CoverIndex,
        tsupport (bulkPieceIntegrand j) ⊆ bulkSupportSet j)
    (localBulk_eq_setIntegral_support :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in bulkSupportSet j, bulkPieceIntegrand j y ∂μBulk)
    (bulkIntegrand_ae_eq_pieceSum :
      bulkIntegrand =ᵐ[μBulk]
        fun y => ∑ j : C.CoverIndex, bulkPieceIntegrand j y) :
    CoverIndexedResolvedBulkFields
      (C := C) (ω := ω) (αBulk := αBulk) (μBulk := μBulk) P where
  fields :=
    P.coverIndexedBulkSetIntegralFields_of_pieceSum_over_superset
      (ω := ω) (μBulk := μBulk)
      (bulkIntegrand := bulkIntegrand)
      (bulkSupportSet := bulkSupportSet)
      (bulkCarrierSet := bulkCarrierSet)
      (bulkPieceIntegrand := bulkPieceIntegrand)
      (globalBulkIntegral := globalBulkIntegral)
      globalBulkIntegral_eq_integral
      bulkSupportSet_measurable bulkCarrier_isCompact
      bulkSupport_subset_carrier bulkPiece_continuousOn_carrier
      bulkPiece_tsupport_subset_support localBulk_eq_setIntegral_support
      bulkIntegrand_ae_eq_pieceSum

end CoverIndexedResolvedBulkFields

end SupportControlledBulkCarrier

section CoordinateClosedCarrierBulk

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {μ : Measure (Fin (n + 1) → Real)}
variable [IsFiniteMeasureOnCompacts μ]

namespace SupportControlledSelectedPartition

/--
Coordinate bulk measure fields using the closed carrier attached to each cover
index.

The local term may still be proved over the assigned support box.  This
constructor transfers it to `C.coverIndexClosedCarrier j`, using support
control in `C.assignedCoordinateBox j`.
-/
def coordinateBulkSetIntegralFields_closedCarrier
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
    (piece_tsupport_subset_assigned :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I x0 x1
                (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_assigned :
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
    CoverIndexedSetIntegralFields
      (α := Fin (n + 1) → Real)
      (Finset.univ : Finset C.CoverIndex) μ
      (P.coverIndexLocalBulkTerm ω) := by
  classical
  have hpieceSum :
      bulkIntegrand I x0 x1 ω =ᵐ[μ]
        fun y =>
          Finset.sum (Finset.univ : Finset C.CoverIndex) fun j =>
            bulkIntegrand I x0 x1
              (P.coverIndexLocalizedForm ω j) y := by
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
  exact
    P.coverIndexedBulkSetIntegralFields_of_pieceSum_over_superset
      (ω := ω) (μBulk := μ)
      (bulkIntegrand := bulkIntegrand I x0 x1 ω)
      (bulkSupportSet := C.assignedCoordinateBox)
      (bulkCarrierSet := C.coverIndexClosedCarrier)
      (bulkPieceIntegrand := fun j y =>
        bulkIntegrand I x0 x1 (P.coverIndexLocalizedForm ω j) y)
      (globalBulkIntegral := globalBulkIntegral)
      globalBulkIntegral_eq_integral
      C.measurableSet_assignedCoordinateBox
      C.coverIndex_closedCarrier_isCompact
      C.coverIndex_openSupportBox_subset_closedCarrier
      piece_continuousOn_closedCarrier
      piece_tsupport_subset_assigned
      localBulk_eq_setIntegral_assigned
      hpieceSum

/--
Resolved bulk fields using cover-indexed closed carriers.
-/
def coordinateResolvedBulkFields_closedCarrier
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
    (piece_tsupport_subset_assigned :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I x0 x1
                (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_assigned :
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
      (αBulk := Fin (n + 1) → Real) (μBulk := μ) P where
  fields :=
    P.coordinateBulkSetIntegralFields_closedCarrier
      (ω := ω) (μ := μ) x0 x1 globalBulkIntegral
      globalBulkIntegral_eq_integral hωsupp
      piece_continuousOn_closedCarrier piece_tsupport_subset_assigned
      localBulk_eq_setIntegral_assigned hdiff

end SupportControlledSelectedPartition

end CoordinateClosedCarrierBulk

end Stokes

end
