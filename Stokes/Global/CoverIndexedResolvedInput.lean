import Stokes.Global.CoverIndexedBulkMeasureConstructor
import Stokes.Global.CoverIndexedBoundaryMeasureConstructor

/-!
# Cover-indexed resolved compact-support input

This file is the integration layer between the support-controlled chart-cover
route and the cover-indexed compact-support core.

The flat input `SupportControlledCoverIndexedMeasureInput` carries the same
bulk and boundary measure-reconstruction pattern twice.  Here we group those
fields into resolved bulk and boundary records whose payload is the already
proved `CoverIndexedSetIntegralFields` package, specialized to the concrete
support-controlled local terms.  This gives later constructor files a smaller
target: produce one resolved bulk record and one resolved boundary record, then
the compact-support represented Stokes theorem follows.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section ResolvedSupportControlledInput

universe uH uM a b

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}

variable {αBulk : Type a} [TopologicalSpace αBulk]
variable [MeasurableSpace αBulk] [OpensMeasurableSpace αBulk]
variable [T2Space αBulk]
variable {μBulk : Measure αBulk} [IsFiniteMeasureOnCompacts μBulk]

variable {αBoundary : Type b} [TopologicalSpace αBoundary]
variable [MeasurableSpace αBoundary] [OpensMeasurableSpace αBoundary]
variable [T2Space αBoundary]
variable {μBoundary : Measure αBoundary}
variable [IsFiniteMeasureOnCompacts μBoundary]

/--
Resolved bulk measure fields for a support-controlled selected cover.

Instead of repeating all bulk scalar fields from
`SupportControlledCoverIndexedMeasureInput`, this record carries the single
cover-indexed set-integral package specialized to the concrete local bulk
terms of the selected partition.
-/
structure CoverIndexedResolvedBulkFields
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) where
  /-- Compact-support, set-integral, and a.e. reconstruction data for bulk. -/
  fields :
    CoverIndexedSetIntegralFields
      (α := αBulk) (Finset.univ : Finset C.CoverIndex) μBulk
      (P.coverIndexLocalBulkTerm ω)

/--
Resolved boundary measure fields for a support-controlled selected cover.

The hard boundary chart/orientation/target-image work is expected to have
already produced this `CoverIndexedSetIntegralFields` value.
-/
structure CoverIndexedResolvedBoundaryFields
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) where
  /-- Compact-support, set-integral, and a.e. reconstruction data for boundary. -/
  fields :
    CoverIndexedSetIntegralFields
      (α := αBoundary) (Finset.univ : Finset C.CoverIndex) μBoundary
      (P.coverIndexLocalBoundaryTerm ω)

namespace CoverIndexedResolvedBulkFields

variable {P : SupportControlledSelectedPartition C}

/-- The global bulk scalar integrand carried by resolved bulk fields. -/
abbrev integrand
    (D :
      CoverIndexedResolvedBulkFields
        (C := C) (ω := ω) (αBulk := αBulk) (μBulk := μBulk) P) :
    αBulk → Real :=
  D.fields.integrand

/-- The cover-indexed bulk carrier set. -/
abbrev pieceSet
    (D :
      CoverIndexedResolvedBulkFields
        (C := C) (ω := ω) (αBulk := αBulk) (μBulk := μBulk) P) :
    C.CoverIndex → Set αBulk :=
  D.fields.pieceSet

/-- The cover-indexed bulk scalar representative. -/
abbrev pieceIntegrand
    (D :
      CoverIndexedResolvedBulkFields
        (C := C) (ω := ω) (αBulk := αBulk) (μBulk := μBulk) P) :
    C.CoverIndex → αBulk → Real :=
  D.fields.pieceIntegrand

/-- The represented global bulk integral carried by resolved bulk fields. -/
abbrev measureIntegral
    (D :
      CoverIndexedResolvedBulkFields
        (C := C) (ω := ω) (αBulk := αBulk) (μBulk := μBulk) P) :
    Real :=
  D.fields.measureIntegral

/-- Bulk reconstruction as a finite sum of the concrete local bulk terms. -/
theorem measureIntegral_eq_localBulkSum
    (D :
      CoverIndexedResolvedBulkFields
        (C := C) (ω := ω) (αBulk := αBulk) (μBulk := μBulk) P) :
    D.measureIntegral =
      Finset.sum (Finset.univ : Finset C.CoverIndex)
        (P.coverIndexLocalBulkTerm ω) :=
  D.fields.measureIntegral_eq_localTermSum

/--
Build resolved bulk fields from the natural unlocalized finite-sum
reconstruction.  Support control inserts the indicators via the existing bulk
constructor.
-/
def ofPieceSum
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
    CoverIndexedResolvedBulkFields
      (C := C) (ω := ω) (αBulk := αBulk) (μBulk := μBulk) P where
  fields :=
    P.coverIndexedBulkSetIntegralFields_of_pieceSum
      (ω := ω) (μBulk := μBulk)
      (bulkIntegrand := bulkIntegrand)
      (bulkPieceSet := bulkPieceSet)
      (bulkPieceIntegrand := bulkPieceIntegrand)
      (globalBulkIntegral := globalBulkIntegral)
      globalBulkIntegral_eq_integral
      bulkPiece_isCompact bulkPiece_continuousOn bulkPiece_tsupport_subset
      localBulk_eq_setIntegral bulkIntegrand_ae_eq_pieceSum

end CoverIndexedResolvedBulkFields

namespace CoverIndexedResolvedBoundaryFields

variable {P : SupportControlledSelectedPartition C}

/-- The global boundary scalar integrand carried by resolved boundary fields. -/
abbrev integrand
    (D :
      CoverIndexedResolvedBoundaryFields
        (C := C) (ω := ω)
        (αBoundary := αBoundary) (μBoundary := μBoundary) P) :
    αBoundary → Real :=
  D.fields.integrand

/-- The cover-indexed boundary carrier set. -/
abbrev pieceSet
    (D :
      CoverIndexedResolvedBoundaryFields
        (C := C) (ω := ω)
        (αBoundary := αBoundary) (μBoundary := μBoundary) P) :
    C.CoverIndex → Set αBoundary :=
  D.fields.pieceSet

/-- The cover-indexed boundary scalar representative. -/
abbrev pieceIntegrand
    (D :
      CoverIndexedResolvedBoundaryFields
        (C := C) (ω := ω)
        (αBoundary := αBoundary) (μBoundary := μBoundary) P) :
    C.CoverIndex → αBoundary → Real :=
  D.fields.pieceIntegrand

/-- The represented global boundary integral carried by resolved boundary fields. -/
abbrev measureIntegral
    (D :
      CoverIndexedResolvedBoundaryFields
        (C := C) (ω := ω)
        (αBoundary := αBoundary) (μBoundary := μBoundary) P) :
    Real :=
  D.fields.measureIntegral

/-- Boundary reconstruction as a finite sum of concrete local boundary terms. -/
theorem localBoundarySum_eq_measureIntegral
    (D :
      CoverIndexedResolvedBoundaryFields
        (C := C) (ω := ω)
        (αBoundary := αBoundary) (μBoundary := μBoundary) P) :
    Finset.sum (Finset.univ : Finset C.CoverIndex)
        (P.coverIndexLocalBoundaryTerm ω) =
      D.measureIntegral :=
  D.fields.measureIntegral_eq_localTermSum.symm

/--
Build resolved boundary fields from an indicator-sum reconstruction supplied by
the resolved boundary chart/orientation route.
-/
def ofIndicatorReconstruction
    (P : SupportControlledSelectedPartition C)
    (boundaryIntegrand : αBoundary → Real)
    (boundaryPieceSet : C.CoverIndex → Set αBoundary)
    (boundaryPieceIntegrand : C.CoverIndex → αBoundary → Real)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral = ∫ y, boundaryIntegrand y ∂μBoundary)
    (boundaryPiece_isCompact :
      ∀ j : C.CoverIndex, IsCompact (boundaryPieceSet j))
    (boundaryPiece_continuousOn :
      ∀ j : C.CoverIndex,
        ContinuousOn (boundaryPieceIntegrand j) (boundaryPieceSet j))
    (boundaryPiece_tsupport_subset :
      ∀ j : C.CoverIndex,
        tsupport (boundaryPieceIntegrand j) ⊆ boundaryPieceSet j)
    (localBoundary_eq_setIntegral :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBoundaryTerm ω j =
          ∫ y in boundaryPieceSet j, boundaryPieceIntegrand j y ∂μBoundary)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[μBoundary]
        fun y => ∑ j : C.CoverIndex,
          (boundaryPieceSet j).indicator (boundaryPieceIntegrand j) y) :
    CoverIndexedResolvedBoundaryFields
      (C := C) (ω := ω)
      (αBoundary := αBoundary) (μBoundary := μBoundary) P where
  fields :=
    coverIndexed_boundarySetIntegralFields_of_indicator_reconstruction
      (μ := μBoundary)
      (active := (Finset.univ : Finset C.CoverIndex))
      (localBoundary := P.coverIndexLocalBoundaryTerm ω)
      (boundaryIntegrand := boundaryIntegrand)
      (boundaryPieceSet := boundaryPieceSet)
      (boundaryPieceIntegrand := boundaryPieceIntegrand)
      (globalBoundaryIntegral := globalBoundaryIntegral)
      globalBoundaryIntegral_eq_integral
      (fun j _hj => boundaryPiece_isCompact j)
      (fun j _hj => boundaryPiece_continuousOn j)
      (fun j _hj => boundaryPiece_tsupport_subset j)
      (fun j _hj => localBoundary_eq_setIntegral j)
      (by
        classical
        simpa using boundaryIntegrand_ae_eq_indicatorSum)

/--
Build resolved boundary fields from an unlocalized finite-sum reconstruction.
Support control turns the piece sum into the required indicator sum.
-/
def ofPieceSum
    (P : SupportControlledSelectedPartition C)
    (boundaryIntegrand : αBoundary → Real)
    (boundaryPieceSet : C.CoverIndex → Set αBoundary)
    (boundaryPieceIntegrand : C.CoverIndex → αBoundary → Real)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral = ∫ y, boundaryIntegrand y ∂μBoundary)
    (boundaryPiece_isCompact :
      ∀ j : C.CoverIndex, IsCompact (boundaryPieceSet j))
    (boundaryPiece_continuousOn :
      ∀ j : C.CoverIndex,
        ContinuousOn (boundaryPieceIntegrand j) (boundaryPieceSet j))
    (boundaryPiece_tsupport_subset :
      ∀ j : C.CoverIndex,
        tsupport (boundaryPieceIntegrand j) ⊆ boundaryPieceSet j)
    (localBoundary_eq_setIntegral :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBoundaryTerm ω j =
          ∫ y in boundaryPieceSet j, boundaryPieceIntegrand j y ∂μBoundary)
    (boundaryIntegrand_ae_eq_pieceSum :
      boundaryIntegrand =ᵐ[μBoundary]
        fun y => ∑ j : C.CoverIndex, boundaryPieceIntegrand j y) :
    CoverIndexedResolvedBoundaryFields
      (C := C) (ω := ω)
      (αBoundary := αBoundary) (μBoundary := μBoundary) P where
  fields :=
    coverIndexed_boundarySetIntegralFields_of_ae_piece_sum
      (μ := μBoundary)
      (active := (Finset.univ : Finset C.CoverIndex))
      (localBoundary := P.coverIndexLocalBoundaryTerm ω)
      (boundaryIntegrand := boundaryIntegrand)
      (boundaryPieceSet := boundaryPieceSet)
      (boundaryPieceIntegrand := boundaryPieceIntegrand)
      (globalBoundaryIntegral := globalBoundaryIntegral)
      globalBoundaryIntegral_eq_integral
      (fun j _hj => boundaryPiece_isCompact j)
      (fun j _hj => boundaryPiece_continuousOn j)
      (fun j _hj => boundaryPiece_tsupport_subset j)
      (fun j _hj => localBoundary_eq_setIntegral j)
      (by
        classical
        simpa using boundaryIntegrand_ae_eq_pieceSum)

end CoverIndexedResolvedBoundaryFields

/--
Resolved compact-support input for the cover-indexed support-controlled route.

The bulk and boundary sides are grouped as measure-field packages, while the
local Stokes fields remain the geometric proof that the two local term
families agree.  This is the natural assembly point for independently produced
bulk, boundary, and local constructors.
-/
structure CoverIndexedResolvedCompactSupportInput where
  /-- Finite chart-box cover of the compact support set. -/
  chartBoxCover : CompactSupportChartCoverSelection I K
  /-- Support-controlled partition subordinate to the chart-box cover. -/
  controlledPartition :
    SupportControlledSelectedPartition chartBoxCover
  /-- Local support and smoothness fields proving local Stokes on cover pieces. -/
  localFields :
    SupportControlledCoverIndexedLocalStokesFields
      controlledPartition ω
  /-- Resolved bulk measure reconstruction fields. -/
  bulk :
    CoverIndexedResolvedBulkFields
      (C := chartBoxCover) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      controlledPartition
  /-- Resolved boundary measure reconstruction fields. -/
  boundary :
    CoverIndexedResolvedBoundaryFields
      (C := chartBoxCover) (ω := ω)
      (αBoundary := αBoundary) (μBoundary := μBoundary)
      controlledPartition

namespace CoverIndexedResolvedCompactSupportInput

/-- The canonical active cover set. -/
def active
    (D :
      CoverIndexedResolvedCompactSupportInput
        (I := I) (K := K) (ω := ω)
        (αBulk := αBulk) (μBulk := μBulk)
        (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    Finset D.chartBoxCover.CoverIndex :=
  Finset.univ

/-- Project resolved grouped fields to the generic cover-indexed measure core. -/
def toCoverIndexedMeasureFields
    (D :
      CoverIndexedResolvedCompactSupportInput
        (I := I) (K := K) (ω := ω)
        (αBulk := αBulk) (μBulk := μBulk)
        (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    CoverIndexedMeasureFields D.active μBulk μBoundary where
  localBulk := D.controlledPartition.coverIndexLocalBulkTerm ω
  localBoundary := D.controlledPartition.coverIndexLocalBoundaryTerm ω
  bulk := by
    simpa [active] using D.bulk.fields
  boundary := by
    simpa [active] using D.boundary.fields
  localBulk_eq_localBoundary := by
    intro j _hj
    exact D.localFields.localBulk_eq_localBoundary j

/--
Projection to the older flat support-controlled input.  This is the key
compatibility theorem for existing code: the grouped records fill exactly the
bulk and boundary fields expected by `SupportControlledCoverIndexedMeasureInput`.
-/
def toSupportControlledMeasureInput
    (D :
      CoverIndexedResolvedCompactSupportInput
        (I := I) (K := K) (ω := ω)
        (αBulk := αBulk) (μBulk := μBulk)
        (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary) where
  chartBoxCover := D.chartBoxCover
  controlledPartition := D.controlledPartition
  localFields := D.localFields
  bulkIntegrand := D.bulk.fields.integrand
  bulkPieceSet := D.bulk.fields.pieceSet
  bulkPieceIntegrand := D.bulk.fields.pieceIntegrand
  globalBulkIntegral := D.bulk.fields.measureIntegral
  globalBulkIntegral_eq_integral := D.bulk.fields.measureIntegral_eq_integral
  bulkPiece_isCompact := by
    intro j
    exact D.bulk.fields.piece_isCompact j (by simp)
  bulkPiece_continuousOn := by
    intro j
    exact D.bulk.fields.piece_continuousOn j (by simp)
  bulkPiece_tsupport_subset := by
    intro j
    exact D.bulk.fields.piece_tsupport_subset j (by simp)
  localBulk_eq_setIntegral := by
    intro j
    exact D.bulk.fields.localTerm_eq_setIntegral j (by simp)
  bulkIntegrand_ae_eq_indicatorSum := by
    classical
    simpa [active] using D.bulk.fields.integrand_ae_eq_indicatorSum
  boundaryIntegrand := D.boundary.fields.integrand
  boundaryPieceSet := D.boundary.fields.pieceSet
  boundaryPieceIntegrand := D.boundary.fields.pieceIntegrand
  globalBoundaryIntegral := D.boundary.fields.measureIntegral
  globalBoundaryIntegral_eq_integral :=
    D.boundary.fields.measureIntegral_eq_integral
  boundaryPiece_isCompact := by
    intro j
    exact D.boundary.fields.piece_isCompact j (by simp)
  boundaryPiece_continuousOn := by
    intro j
    exact D.boundary.fields.piece_continuousOn j (by simp)
  boundaryPiece_tsupport_subset := by
    intro j
    exact D.boundary.fields.piece_tsupport_subset j (by simp)
  localBoundary_eq_setIntegral := by
    intro j
    exact D.boundary.fields.localTerm_eq_setIntegral j (by simp)
  boundaryIntegrand_ae_eq_indicatorSum := by
    classical
    simpa [active] using D.boundary.fields.integrand_ae_eq_indicatorSum

/-- The represented global bulk value of the resolved input. -/
abbrev globalBulk
    (D :
      CoverIndexedResolvedCompactSupportInput
        (I := I) (K := K) (ω := ω)
        (αBulk := αBulk) (μBulk := μBulk)
        (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    Real :=
  D.bulk.fields.measureIntegral

/-- The represented global boundary value of the resolved input. -/
abbrev globalBoundary
    (D :
      CoverIndexedResolvedCompactSupportInput
        (I := I) (K := K) (ω := ω)
        (αBulk := αBulk) (μBulk := μBulk)
        (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    Real :=
  D.boundary.fields.measureIntegral

/-- The resolved input has the same measure-field projection as the flat input. -/
theorem toSupportControlledMeasureInput_toMeasureFields
    (D :
      CoverIndexedResolvedCompactSupportInput
        (I := I) (K := K) (ω := ω)
        (αBulk := αBulk) (μBulk := μBulk)
        (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    D.toSupportControlledMeasureInput.toCoverIndexedMeasureFields =
      D.toCoverIndexedMeasureFields := by
  rfl

/-- Compact-support represented Stokes from grouped resolved fields. -/
theorem stokes
    (D :
      CoverIndexedResolvedCompactSupportInput
        (I := I) (K := K) (ω := ω)
        (αBulk := αBulk) (μBulk := μBulk)
        (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    D.globalBulk = D.globalBoundary := by
  exact D.toCoverIndexedMeasureFields.stokes

/-- The same result routed through the existing flat input, for compatibility. -/
theorem stokes_via_supportControlledMeasureInput
    (D :
      CoverIndexedResolvedCompactSupportInput
        (I := I) (K := K) (ω := ω)
        (αBulk := αBulk) (μBulk := μBulk)
        (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    D.globalBulk = D.globalBoundary := by
  exact D.toSupportControlledMeasureInput.stokes

end CoverIndexedResolvedCompactSupportInput

end ResolvedSupportControlledInput

end Stokes

end
