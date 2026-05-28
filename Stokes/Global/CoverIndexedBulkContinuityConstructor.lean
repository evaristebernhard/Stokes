import Stokes.Global.CoverIndexedNaturalAssembly
import Stokes.Global.BulkLocalTermCompactSupportConstructor

/-!
# Cover-indexed bulk continuity constructors

The closed-carrier bulk data used by the natural assembly layer asks for
continuity of each scalar bulk piece on `C.coverIndexClosedCarrier j`.  In the
geometric construction this continuity should not be an independent field: it
comes from `ContDiffOn` smoothness of the localized chart representative on a
coordinate neighborhood containing the closed carrier.

This file packages that reduction without changing the surrounding measure or
boundary APIs.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section GenericContDiff

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace Real F]
variable {m : WithTop ℕ∞}

/--
Restrict a `ContDiffOn` function to a smaller carrier and keep only the
continuity statement.
-/
theorem continuousOn_of_contDiffOn_subset {f : E → F} {U S : Set E}
    (hf : ContDiffOn Real m f U) (hSU : S ⊆ U) :
    ContinuousOn f S :=
  hf.continuousOn.mono hSU

/--
Cover-indexed version of `continuousOn_of_contDiffOn_subset` for arbitrary
scalar piece integrands on coordinate space.
-/
theorem coverIndex_piece_continuousOn_closedCarrier_of_contDiffOn_subset
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {K : Set M}
    (C : CompactSupportChartCoverSelection I K)
    (pieceIntegrand : C.CoverIndex → (Fin (n + 1) → Real) → Real)
    (smoothSet : C.CoverIndex → Set (Fin (n + 1) → Real))
    (hcarrier : ∀ j : C.CoverIndex,
      C.coverIndexClosedCarrier j ⊆ smoothSet j)
    (hsmooth : ∀ j : C.CoverIndex,
      ContDiffOn Real m (pieceIntegrand j) (smoothSet j)) :
    ∀ j : C.CoverIndex,
      ContinuousOn (pieceIntegrand j) (C.coverIndexClosedCarrier j) := by
  intro j
  exact continuousOn_of_contDiffOn_subset (hsmooth j) (hcarrier j)

end GenericContDiff

section CanonicalBulkContinuity

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}

namespace SupportControlledSelectedPartition

/--
The canonical scalar bulk piece is continuous on each closed carrier when the
localized transition-pullback representative is smooth on an open neighborhood
of that carrier.
-/
theorem coverIndexBulkIntegrand_continuousOn_closedCarrier_of_contDiffOn_isOpen
    (P : SupportControlledSelectedPartition C)
    (x0 x1 : M)
    (smoothSet : C.CoverIndex → Set (Fin (n + 1) → Real))
    (hopen : ∀ j : C.CoverIndex, IsOpen (smoothSet j))
    (hcarrier : ∀ j : C.CoverIndex,
      C.coverIndexClosedCarrier j ⊆ smoothSet j)
    (hsmooth : ∀ j : C.CoverIndex,
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (P.coverIndexLocalizedForm ω j)) (smoothSet j)) :
    ∀ j : C.CoverIndex,
      ContinuousOn
        (fun y => bulkIntegrand I x0 x1 (P.coverIndexLocalizedForm ω j) y)
        (C.coverIndexClosedCarrier j) := by
  intro j
  exact
    bulkIntegrand_continuousOn_of_contDiffOn_isOpen
      (I := I) (x0 := x0) (x1 := x1)
      (ω := P.coverIndexLocalizedForm ω j)
      (U := smoothSet j) (s := C.coverIndexClosedCarrier j)
      (hopen j) (hcarrier j) (hsmooth j)

/--
Bulk smoothness fields sufficient to generate closed-carrier continuity for
the canonical cover-indexed scalar bulk pieces.
-/
structure CoverIndexedBulkSmoothnessFields
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) (x0 x1 : M) where
  /-- Smoothness neighborhood for each cover-indexed scalar piece. -/
  smoothSet : C.CoverIndex → Set (Fin (n + 1) → Real)
  /-- Each smoothness neighborhood is open. -/
  isOpen_smoothSet :
    ∀ j : C.CoverIndex, IsOpen (smoothSet j)
  /-- The closed measure carrier lies in the corresponding smoothness set. -/
  closedCarrier_subset_smoothSet :
    ∀ j : C.CoverIndex, C.coverIndexClosedCarrier j ⊆ smoothSet j
  /-- The localized chart representative is smooth on the chosen neighborhood. -/
  localized_contDiffOn :
    ∀ j : C.CoverIndex,
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (P.coverIndexLocalizedForm ω j)) (smoothSet j)

namespace CoverIndexedBulkSmoothnessFields

/-- Extract the closed-carrier continuity field required by bulk measure data. -/
theorem piece_continuousOn_closedCarrier
    {P : SupportControlledSelectedPartition C}
    {x0 x1 : M}
    (D : CoverIndexedBulkSmoothnessFields P ω x0 x1) :
    ∀ j : C.CoverIndex,
      ContinuousOn
        (fun y => bulkIntegrand I x0 x1 (P.coverIndexLocalizedForm ω j) y)
        (C.coverIndexClosedCarrier j) :=
  P.coverIndexBulkIntegrand_continuousOn_closedCarrier_of_contDiffOn_isOpen
    (ω := ω) x0 x1 D.smoothSet D.isOpen_smoothSet
    D.closedCarrier_subset_smoothSet D.localized_contDiffOn

end CoverIndexedBulkSmoothnessFields

end SupportControlledSelectedPartition

end CanonicalBulkContinuity

section ClosedCarrierBulkDataConstructors

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {μBulk : Measure (Fin (n + 1) → Real)}

namespace CoverIndexedClosedCarrierBulkData

/--
Construct closed-carrier bulk data from `ContDiffOn` smoothness of arbitrary
coordinate scalar pieces on supersets of the closed carriers.

This is the generic field-elimination constructor: the caller supplies
smoothness of the scalar piece integrands, and the continuity field of
`CoverIndexedClosedCarrierBulkData` is generated automatically.
-/
def ofContDiffOnSuperset
    (integrand : (Fin (n + 1) → Real) → Real)
    (pieceIntegrand :
      C.CoverIndex → (Fin (n + 1) → Real) → Real)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral = ∫ y, integrand y ∂μBulk)
    (smoothSet : C.CoverIndex → Set (Fin (n + 1) → Real))
    (closedCarrier_subset_smoothSet :
      ∀ j : C.CoverIndex, C.coverIndexClosedCarrier j ⊆ smoothSet j)
    (piece_contDiffOn :
      ∀ j : C.CoverIndex,
        ContDiffOn Real ⊤ (pieceIntegrand j) (smoothSet j))
    (piece_tsupport_subset_assignedCoordinateBox :
      ∀ j : C.CoverIndex,
        tsupport (pieceIntegrand j) ⊆ C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_closedCarrier :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in C.coverIndexClosedCarrier j, pieceIntegrand j y ∂μBulk)
    (integrand_ae_eq_pieceSum :
      integrand =ᵐ[μBulk]
        fun y => ∑ j : C.CoverIndex, pieceIntegrand j y) :
    CoverIndexedClosedCarrierBulkData
      (I := I) (K := K) (μBulk := μBulk) C P ω where
  integrand := integrand
  pieceIntegrand := pieceIntegrand
  globalIntegral := globalIntegral
  globalIntegral_eq_integral := globalIntegral_eq_integral
  piece_continuousOn_closedCarrier :=
    coverIndex_piece_continuousOn_closedCarrier_of_contDiffOn_subset
      C pieceIntegrand smoothSet closedCarrier_subset_smoothSet
      piece_contDiffOn
  piece_tsupport_subset_assignedCoordinateBox :=
    piece_tsupport_subset_assignedCoordinateBox
  localBulk_eq_setIntegral_closedCarrier :=
    localBulk_eq_setIntegral_closedCarrier
  integrand_ae_eq_pieceSum := integrand_ae_eq_pieceSum

/--
Canonical bulk-data constructor specialized to scalar bulk integrands
`bulkIntegrand I x0 x1 (P.coverIndexLocalizedForm ω j)`.

Compared with `CoverIndexedClosedCarrierBulkData`, callers provide the
geometric smoothness package `CoverIndexedBulkSmoothnessFields` instead of the
closed-carrier continuity field.
-/
def ofCanonicalBulkSmoothness
    (x0 x1 : M)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral = ∫ y, bulkIntegrand I x0 x1 ω y ∂μBulk)
    (smooth :
      SupportControlledSelectedPartition.CoverIndexedBulkSmoothnessFields
        (C := C) P ω x0 x1)
    (piece_tsupport_subset_assignedCoordinateBox :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I x0 x1 (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_closedCarrier :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in C.coverIndexClosedCarrier j,
            bulkIntegrand I x0 x1 (P.coverIndexLocalizedForm ω j) y ∂μBulk)
    (integrand_ae_eq_pieceSum :
      bulkIntegrand I x0 x1 ω =ᵐ[μBulk]
        fun y =>
          ∑ j : C.CoverIndex,
            bulkIntegrand I x0 x1 (P.coverIndexLocalizedForm ω j) y) :
    CoverIndexedClosedCarrierBulkData
      (I := I) (K := K) (μBulk := μBulk) C P ω where
  integrand := bulkIntegrand I x0 x1 ω
  pieceIntegrand := fun j y =>
    bulkIntegrand I x0 x1 (P.coverIndexLocalizedForm ω j) y
  globalIntegral := globalIntegral
  globalIntegral_eq_integral := globalIntegral_eq_integral
  piece_continuousOn_closedCarrier := smooth.piece_continuousOn_closedCarrier
  piece_tsupport_subset_assignedCoordinateBox :=
    piece_tsupport_subset_assignedCoordinateBox
  localBulk_eq_setIntegral_closedCarrier :=
    localBulk_eq_setIntegral_closedCarrier
  integrand_ae_eq_pieceSum := integrand_ae_eq_pieceSum

end CoverIndexedClosedCarrierBulkData

end ClosedCarrierBulkDataConstructors

end Stokes

end
