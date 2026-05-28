import Stokes.Global.CoverIndexedFromSupportControlledCover

/-!
# Cover-indexed bulk measure constructors

This module packages the bulk-side measure input in the direction needed by
the compact-support globalization route.  The main point is to let callers
provide the more natural unlocalized finite-sum reconstruction

`F =ᵐ[μ] fun y => ∑ i in active, f i y`

together with topological support control for the pieces.  The constructor
reuses `CoverIndexedSetIntegralFields.ofTSupportSubsetCompactBoxPieceSum`,
which inserts the indicator functions required by
`CoverIndexedSetIntegralFields`.

The final constructor specializes this to a support-controlled selected chart
cover: the unlocalized finite-sum reconstruction is derived from the
partition identity and the chartwise exterior-derivative/bulk-integrand
reconstruction theorem.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section SupportControlledPieceSum

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
Support-controlled-cover wrapper for the generic bulk constructor.

The active set is the mixed cover index `Finset.univ`, and the local terms are
the concrete cover-indexed bulk terms attached to the selected partition.
-/
def coverIndexedBulkSetIntegralFields_of_pieceSum
    (P : SupportControlledSelectedPartition C)
    (bulkIntegrand : αBulk → Real)
    (bulkPieceSet : C.CoverIndex → Set αBulk)
    (bulkPieceIntegrand : C.CoverIndex → αBulk → Real)
    (globalBulkIntegral : Real)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral = ∫ y, bulkIntegrand y ∂μBulk)
    (bulkPiece_isCompact :
      ∀ j : C.CoverIndex, IsCompact (bulkPieceSet j))
    (bulkPiece_continuousOn :
      ∀ j : C.CoverIndex,
        ContinuousOn (bulkPieceIntegrand j) (bulkPieceSet j))
    (bulkPiece_tsupport_subset :
      ∀ j : C.CoverIndex,
        tsupport (bulkPieceIntegrand j) ⊆ bulkPieceSet j)
    (localBulk_eq_setIntegral :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in bulkPieceSet j, bulkPieceIntegrand j y ∂μBulk)
    (bulkIntegrand_ae_eq_pieceSum :
      bulkIntegrand =ᵐ[μBulk]
        fun y => ∑ j : C.CoverIndex, bulkPieceIntegrand j y) :
    CoverIndexedSetIntegralFields
      (α := αBulk) (Finset.univ : Finset C.CoverIndex) μBulk
      (P.coverIndexLocalBulkTerm ω) :=
  CoverIndexedSetIntegralFields.ofTSupportSubsetCompactBoxPieceSum
    (μ := μBulk) (Finset.univ : Finset C.CoverIndex)
    (P.coverIndexLocalBulkTerm ω) bulkIntegrand bulkPieceSet
    bulkPieceIntegrand globalBulkIntegral globalBulkIntegral_eq_integral
    (fun j _hj => bulkPiece_isCompact j)
    (fun j _hj => bulkPiece_continuousOn j)
    (fun j _hj => bulkPiece_tsupport_subset j)
    (fun j _hj => localBulk_eq_setIntegral j)
    (by
      classical
      simpa using bulkIntegrand_ae_eq_pieceSum)

end SupportControlledSelectedPartition

end SupportControlledPieceSum

section SupportControlledCoordinateBulk

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
Coordinate bulk measure fields for a support-controlled selected partition.

Here the global integrand is the chartwise `bulkIntegrand` of `ω`, the piece
integrands are the chartwise `bulkIntegrand`s of the localized forms
`ρ_j • ω`, and the piece sets are the assigned coordinate boxes of the compact
chart-box cover.  The a.e. unlocalized sum is derived automatically from the
partition identity and the chartwise derivative reconstruction.
-/
def coordinateBulkSetIntegralFields
    (P : SupportControlledSelectedPartition C)
    (x0 x1 : M)
    (globalBulkIntegral : Real)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral =
        ∫ y, bulkIntegrand I x0 x1 ω y ∂μ)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (piece_isCompact :
      ∀ j : C.CoverIndex, IsCompact (C.assignedCoordinateBox j))
    (piece_continuousOn :
      ∀ j : C.CoverIndex,
        ContinuousOn
          (fun y =>
            bulkIntegrand I x0 x1 (P.coverIndexLocalizedForm ω j) y)
          (C.assignedCoordinateBox j))
    (piece_tsupport_subset :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I x0 x1
                (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral :
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
    P.coverIndexedBulkSetIntegralFields_of_pieceSum
      (μBulk := μ)
      (bulkIntegrand := bulkIntegrand I x0 x1 ω)
      (bulkPieceSet := C.assignedCoordinateBox)
      (bulkPieceIntegrand := fun j y =>
        bulkIntegrand I x0 x1 (P.coverIndexLocalizedForm ω j) y)
      (globalBulkIntegral := globalBulkIntegral)
      globalBulkIntegral_eq_integral
      piece_isCompact piece_continuousOn piece_tsupport_subset
      localBulk_eq_setIntegral hpieceSum

end SupportControlledSelectedPartition

end SupportControlledCoordinateBulk

end Stokes

end
