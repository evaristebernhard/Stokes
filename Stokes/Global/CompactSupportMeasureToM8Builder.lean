import Stokes.Global.BulkMeasureFromPartition
import Stokes.Global.BulkMeasureToM8
import Stokes.Global.CompactSupportToM8Measure
import Stokes.Global.BoundaryMeasureFromPartition
import Stokes.Global.BoundaryMeasureToM8
import Stokes.Global.M8MeasureConstructors

/-!
# Compact-support measure-side builder for M8

This file combines the selected-partition bulk measure package with boundary
partition measure data and exposes the resulting `M8MeasureLocalizationData`.

The analytic inputs remain visible in the builder record: the bulk side is a
`BulkMeasureFromPartitionData`, while the boundary side records the global
boundary integrand, selected boundary support sets, compact-support
integrability, set-integral identifications, and the a.e. indicator
reconstruction used by `BoundaryMeasurePartitionData`.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportMeasureToM8Builder

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

/--
Measure-side data sufficient to build M8 measure localization.

The bulk package is already aligned with the selected partition.  The boundary
partition package is aligned by `boundary_active` and `boundary_pieces`; its
analytic measure hypotheses are kept as explicit fields.
-/
structure CompactSupportMeasureToM8BuilderData
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (μ : Measure α)
    (globalBulkIntegral globalBoundaryIntegral : Real) where
  /-- Selected-partition compact-support bulk measure localization. -/
  bulk :
    BulkMeasureFromPartitionData (α := α) (μ := μ)
      selectedPartition targetImages globalBulkIntegral
  /-- Boundary finite partition data before rewriting to the selected M8 shape. -/
  boundaryPartition : BoundaryMeasurePartitionData M BoundaryPiece
  /-- Boundary active charts are the selected active charts. -/
  boundary_active :
    boundaryPartition.activeCharts = selectedPartition.active
  /-- Boundary pieces are the selected target-image pieces. -/
  boundary_pieces :
    boundaryPartition.boundaryPieces = targetImages.boundaryPieces
  /-- Boundary-side integrand represented by the measure integral. -/
  boundaryIntegrand : α → Real
  /-- Support set for one selected boundary piece. -/
  boundaryPieceSet : M → BoundaryPiece → Set α
  /-- Scalar integrand for one selected boundary piece. -/
  boundaryPieceIntegrand : M → BoundaryPiece → α → Real
  /-- Genuine boundary measure integral. -/
  boundaryMeasureIntegral : Real
  /-- The represented boundary integral agrees with the boundary measure integral. -/
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :
    globalBoundaryIntegral = boundaryMeasureIntegral
  /-- The boundary measure integral is the integral of the global boundary integrand. -/
  boundaryMeasureIntegral_eq_integral :
    boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ
  /-- Active boundary support sets are measurable. -/
  boundaryPieceSet_measurable :
    ∀ x, x ∈ boundaryPartition.activeCharts →
      ∀ q, q ∈ boundaryPartition.boundaryPieces x →
        MeasurableSet (boundaryPieceSet x q)
  /-- Active boundary-piece integrands have compact-support integrability data. -/
  boundaryPieceCompactSupport :
    ∀ x, x ∈ boundaryPartition.activeCharts →
      ∀ q, q ∈ boundaryPartition.boundaryPieces x →
        CompactSupportIntegrabilityData (boundaryPieceIntegrand x q)
  /-- Active boundary partition terms are the corresponding set integrals. -/
  boundaryPartitionTerm_eq_setIntegral :
    ∀ x, x ∈ boundaryPartition.activeCharts →
      ∀ q, q ∈ boundaryPartition.boundaryPieces x →
        boundaryPartition.boundaryPartitionTerm x q =
          ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ
  /-- A.e. reconstruction of the boundary integrand by selected indicators. -/
  boundaryIntegrand_ae_eq_indicatorSum :
    boundaryIntegrand =ᵐ[μ]
      boundaryMeasureIndicatorSum boundaryPartition.activeCharts
        boundaryPartition.boundaryPieces boundaryPieceSet
        boundaryPieceIntegrand

namespace CompactSupportMeasureToM8BuilderData

variable {globalBulkIntegral globalBoundaryIntegral : Real}

variable
    (D :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImages μ
        globalBulkIntegral globalBoundaryIntegral)

/-- Boundary compact/set-integral fields in the native partition shape. -/
def toBoundaryCompactMeasureFields :
    BoundaryCompactMeasureFields μ D.boundaryPartition.activeCharts
      D.boundaryPartition.boundaryPieces
      D.boundaryPartition.boundaryPartitionTerm :=
  D.boundaryPartition.compactFieldsOfCompactSupport
    (μ := μ) D.boundaryIntegrand D.boundaryPieceSet
    D.boundaryPieceIntegrand D.boundaryMeasureIntegral
    D.boundaryMeasureIntegral_eq_integral D.boundaryPieceSet_measurable
    D.boundaryPieceCompactSupport
    D.boundaryPartitionTerm_eq_setIntegral
    D.boundaryIntegrand_ae_eq_indicatorSum

/-- Boundary compact/set-integral fields rewritten to the selected M8 shape. -/
def toSelectedBoundaryCompactMeasureFields :
    BoundaryCompactMeasureFields μ selectedPartition.active
      targetImages.boundaryPieces
      D.boundaryPartition.boundaryPartitionTerm where
  boundaryIntegrand := D.boundaryIntegrand
  boundaryPieceSet := D.boundaryPieceSet
  boundaryPieceIntegrand := D.boundaryPieceIntegrand
  boundaryMeasureIntegral := D.boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_integral :=
    D.boundaryMeasureIntegral_eq_integral
  boundaryPieceSet_measurable := by
    intro x hx q hq
    exact D.boundaryPieceSet_measurable x
      (by simpa [D.boundary_active] using hx) q
      (by simpa [D.boundary_pieces] using hq)
  boundaryPieceIntegrableOn := by
    intro x hx q hq
    exact (D.boundaryPieceCompactSupport x
      (by simpa [D.boundary_active] using hx) q
      (by simpa [D.boundary_pieces] using hq)).integrableOn
      (D.boundaryPieceSet x q)
  boundaryPartitionTerm_eq_setIntegral := by
    intro x hx q hq
    exact D.boundaryPartitionTerm_eq_setIntegral x
      (by simpa [D.boundary_active] using hx) q
      (by simpa [D.boundary_pieces] using hq)
  boundaryIntegrand_ae_eq_indicatorSum := by
    simpa [D.boundary_active, D.boundary_pieces] using
      D.boundaryIntegrand_ae_eq_indicatorSum

@[simp]
theorem toSelectedBoundaryCompactMeasureFields_boundaryMeasureIntegral :
    D.toSelectedBoundaryCompactMeasureFields.boundaryMeasureIntegral =
      D.boundaryMeasureIntegral := by
  rfl

/-- Analytic boundary localization data rewritten to the selected M8 shape. -/
def toBoundaryMeasureLocalizationData :
    BoundaryMeasureLocalizationData μ selectedPartition.active
      targetImages.boundaryPieces
      D.boundaryPartition.boundaryPartitionTerm :=
  D.toSelectedBoundaryCompactMeasureFields.toBoundaryMeasureLocalizationData

@[simp]
theorem toBoundaryMeasureLocalizationData_boundaryMeasureIntegral :
    D.toBoundaryMeasureLocalizationData.boundaryMeasureIntegral =
      D.boundaryMeasureIntegral := by
  rw [toBoundaryMeasureLocalizationData]
  exact D.toSelectedBoundaryCompactMeasureFields_boundaryMeasureIntegral

/-- Fieldized boundary measure localization used by M8 constructors. -/
def toBoundaryMeasureLocalizationFields :
    BoundaryMeasureLocalizationFields selectedPartition.active
      targetImages.boundaryPieces
      D.boundaryPartition.boundaryPartitionTerm globalBoundaryIntegral :=
  D.toBoundaryMeasureLocalizationData.toBoundaryMeasureLocalizationFields
    globalBoundaryIntegral
    (by
      rw [D.toBoundaryMeasureLocalizationData_boundaryMeasureIntegral]
      exact D.globalBoundaryIntegral_eq_boundaryMeasureIntegral)

/-- M8 boundary-only package induced by the boundary partition measure data. -/
def toM8BoundaryMeasureData :
    M8BoundaryMeasureData I omega selectedPartition targetImages :=
  M8BoundaryMeasureData.ofBoundaryMeasureLocalizationFields
    (I := I) (omega := omega) (selectedPartition := selectedPartition)
    (targetImages := targetImages)
    D.toBoundaryMeasureLocalizationFields

/--
Compact-support-facing measure package assembled from the selected bulk and
boundary partition measure data.
-/
def toCompactSupportToM8MeasureData :
    CompactSupportToM8MeasureData
      (α := α) I omega selectedPartition targetImages μ where
  localized := D.bulk.localized
  targetImages_active := D.bulk.boundary_active
  globalBulkIntegral := globalBulkIntegral
  bulk := D.bulk.toCompactSupportBulkMeasureData
  boundaryPartitionTerm := D.boundaryPartition.boundaryPartitionTerm
  boundary := D.toSelectedBoundaryCompactMeasureFields
  globalBoundaryIntegral := globalBoundaryIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    (by
      rw [D.toSelectedBoundaryCompactMeasureFields_boundaryMeasureIntegral]
      exact D.globalBoundaryIntegral_eq_boundaryMeasureIntegral)

/--
Final M8 measure-localization data.  This route goes through the
compact-support-facing adapter, so the compact-support package remains visible
to downstream users.
-/
def toM8MeasureLocalizationData :
    M8MeasureLocalizationData I omega selectedPartition targetImages :=
  D.toCompactSupportToM8MeasureData.toM8MeasureLocalizationData

/--
The same final M8 data built through the selected-partition bulk-to-M8 adapter
and the fieldized boundary package.
-/
def toM8MeasureLocalizationDataOfBoundaryFields :
    M8MeasureLocalizationData I omega selectedPartition targetImages :=
  (D.bulk.toBulkMeasureLocalizationFields.toM8BulkMeasureFields
      D.bulk.localized.localized_active D.bulk.localized.localized_coefficient
      D.bulk.boundary_active).toM8MeasureLocalizationData
    D.boundaryPartition.boundaryPartitionTerm globalBoundaryIntegral
    D.toBoundaryMeasureLocalizationFields.boundaryMeasureIntegral
    D.toBoundaryMeasureLocalizationFields.globalBoundaryIntegral_eq_boundaryMeasureIntegral
    D.toBoundaryMeasureLocalizationFields.boundaryMeasureIntegral_eq_partitionSum

@[simp]
theorem toBoundaryCompactMeasureFields_boundaryMeasureIntegral :
    D.toBoundaryCompactMeasureFields.boundaryMeasureIntegral =
      D.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem toBoundaryMeasureLocalizationFields_boundaryMeasureIntegral :
    D.toBoundaryMeasureLocalizationFields.boundaryMeasureIntegral =
      D.boundaryMeasureIntegral := by
  rw [toBoundaryMeasureLocalizationFields]
  exact D.toBoundaryMeasureLocalizationData_boundaryMeasureIntegral

@[simp]
theorem toM8BoundaryMeasureData_boundaryPartitionTerm :
    D.toM8BoundaryMeasureData.boundaryPartitionTerm =
      D.boundaryPartition.boundaryPartitionTerm := by
  rw [toM8BoundaryMeasureData, toBoundaryMeasureLocalizationFields]
  rfl

@[simp]
theorem toM8BoundaryMeasureData_globalBoundaryIntegral :
    D.toM8BoundaryMeasureData.globalBoundaryIntegral =
      globalBoundaryIntegral := by
  rw [toM8BoundaryMeasureData, toBoundaryMeasureLocalizationFields]
  rfl

@[simp]
theorem toM8BoundaryMeasureData_boundaryMeasureIntegral :
    D.toM8BoundaryMeasureData.boundaryMeasureIntegral =
      D.boundaryMeasureIntegral := by
  rw [toM8BoundaryMeasureData]
  exact D.toBoundaryMeasureLocalizationFields_boundaryMeasureIntegral

@[simp]
theorem toCompactSupportToM8MeasureData_globalBulkIntegral :
    D.toCompactSupportToM8MeasureData.globalBulkIntegral =
      globalBulkIntegral :=
  rfl

@[simp]
theorem toCompactSupportToM8MeasureData_boundaryPartitionTerm :
    D.toCompactSupportToM8MeasureData.boundaryPartitionTerm =
      D.boundaryPartition.boundaryPartitionTerm :=
  rfl

@[simp]
theorem toCompactSupportToM8MeasureData_globalBoundaryIntegral :
    D.toCompactSupportToM8MeasureData.globalBoundaryIntegral =
      globalBoundaryIntegral :=
  rfl

@[simp]
theorem toCompactSupportToM8MeasureData_boundaryMeasureIntegral :
    D.toCompactSupportToM8MeasureData.boundary.boundaryMeasureIntegral =
      D.boundaryMeasureIntegral := by
  rw [toCompactSupportToM8MeasureData]
  exact D.toSelectedBoundaryCompactMeasureFields_boundaryMeasureIntegral

@[simp]
theorem toM8MeasureLocalizationData_globalBulkIntegral :
    D.toM8MeasureLocalizationData.globalBulkIntegral =
      globalBulkIntegral :=
  rfl

@[simp]
theorem toM8MeasureLocalizationData_bulkMeasureIntegral :
    D.toM8MeasureLocalizationData.bulkMeasureIntegral =
      globalBulkIntegral :=
  rfl

@[simp]
theorem toM8MeasureLocalizationData_boundaryPartitionTerm :
    D.toM8MeasureLocalizationData.boundaryPartitionTerm =
      D.boundaryPartition.boundaryPartitionTerm :=
  rfl

@[simp]
theorem toM8MeasureLocalizationData_globalBoundaryIntegral :
    D.toM8MeasureLocalizationData.globalBoundaryIntegral =
      globalBoundaryIntegral :=
  rfl

@[simp]
theorem toM8MeasureLocalizationData_boundaryMeasureIntegral :
    D.toM8MeasureLocalizationData.boundaryMeasureIntegral =
      D.boundaryMeasureIntegral := by
  rw [toM8MeasureLocalizationData]
  exact D.toCompactSupportToM8MeasureData_boundaryMeasureIntegral

@[simp]
theorem toM8MeasureLocalizationDataOfBoundaryFields_bulkMeasureIntegral :
    D.toM8MeasureLocalizationDataOfBoundaryFields.bulkMeasureIntegral =
      globalBulkIntegral :=
  rfl

@[simp]
theorem toM8MeasureLocalizationDataOfBoundaryFields_boundaryMeasureIntegral :
    D.toM8MeasureLocalizationDataOfBoundaryFields.boundaryMeasureIntegral =
      D.boundaryMeasureIntegral := by
  rw [toM8MeasureLocalizationDataOfBoundaryFields]
  exact D.toBoundaryMeasureLocalizationFields_boundaryMeasureIntegral

/-- Boundary finite-sum projection supplied by the builder. -/
theorem boundaryMeasureIntegral_eq_partitionSum :
    D.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces
        D.boundaryPartition.boundaryPartitionTerm := by
  simpa using
    D.toBoundaryMeasureLocalizationData.boundaryMeasureIntegral_eq_partitionSum

/-- Bulk finite-sum projection supplied by the selected bulk package. -/
theorem bulkMeasureIntegral_eq_localBulkSum :
    globalBulkIntegral =
      (Finset.sum selectedPartition.active fun x =>
        Finset.sum ({()} : Finset Unit) fun _q =>
          D.bulk.localized.localizedInterior.bulkTerm x) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (targetImages.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm targetImages x q := by
  simpa using D.bulk.bulkIntegralLocalizes_selected

/-- M8 boundary finite-sum projection in terms of the produced localization data. -/
theorem toM8MeasureLocalizationData_boundaryMeasureIntegral_eq_partitionSum :
    D.toM8MeasureLocalizationData.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces
        D.boundaryPartition.boundaryPartitionTerm := by
  simpa using D.boundaryMeasureIntegral_eq_partitionSum

/-- M8 bulk finite-sum projection in terms of the produced localization data. -/
theorem toM8MeasureLocalizationData_bulkMeasureIntegral_eq_localBulkSum :
    D.toM8MeasureLocalizationData.bulkMeasureIntegral =
      (Finset.sum selectedPartition.active fun x =>
        Finset.sum ({()} : Finset Unit) fun _q =>
          D.bulk.localized.localizedInterior.bulkTerm x) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (targetImages.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm targetImages x q := by
  simpa using D.bulkMeasureIntegral_eq_localBulkSum

end CompactSupportMeasureToM8BuilderData

end CompactSupportMeasureToM8Builder

end Stokes

end
