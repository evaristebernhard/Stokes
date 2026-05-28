import Stokes.Global.CompactSupportBulkMeasure
import Stokes.Global.BoundaryCompactMeasure
import Stokes.Global.LocalizedInteriorConstructors
import Stokes.Global.M8Statement

/-!
# Compact-support measure localization for M8

This file packages the compact-support-facing bulk and boundary measure
constructors together with the selected-partition localized-interior fields.

The result is a small adapter to `M8MeasureLocalizationData`: downstream code
can now provide compact-support bulk localization, compact boundary measure
localization, and selected-partition interior alignment without hand-writing the
M8 measure record.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportToM8Measure

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
Compact-support-facing measure package for the M8 statement.

The bulk side is supplied by `CompactSupportBulkMeasureData`, the boundary side
by `BoundaryCompactMeasureFields`, and the selected-partition alignment by
`LocalizedInteriorM8Fields`.
-/
structure CompactSupportToM8MeasureData
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (μ : Measure α) where
  /-- Selected-partition localized-interior alignment. -/
  localized : LocalizedInteriorM8Fields I omega selectedPartition
  /-- The target-image boundary family is indexed by the selected active set. -/
  targetImages_active :
    targetImages.activeCharts = selectedPartition.active
  /-- The represented bulk integral. -/
  globalBulkIntegral : Real
  /-- Compact-support bulk measure-localization data. -/
  bulk :
    CompactSupportBulkMeasureData (α := α) (μ := μ)
      localized.localizedInterior targetImages globalBulkIntegral
  /-- Boundary partition term after boundary chart transport. -/
  boundaryPartitionTerm : M → BoundaryPiece → Real
  /-- Compact/set-integral boundary measure-localization data. -/
  boundary :
    BoundaryCompactMeasureFields μ selectedPartition.active
      targetImages.boundaryPieces boundaryPartitionTerm
  /-- The represented global boundary integral. -/
  globalBoundaryIntegral : Real
  /-- The represented boundary integral agrees with the compact measure one. -/
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :
    globalBoundaryIntegral = boundary.boundaryMeasureIntegral

namespace CompactSupportToM8MeasureData

variable
    (D :
      CompactSupportToM8MeasureData
        (α := α) I omega selectedPartition targetImages μ)

/-- The compact-support bulk package gives the M8 bulk finite-sum field. -/
theorem bulkMeasureIntegral_eq_localBulkSum :
    D.globalBulkIntegral =
      (Finset.sum selectedPartition.active fun x =>
        Finset.sum ({()} : Finset Unit) fun _q =>
          D.localized.localizedInterior.bulkTerm x) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (targetImages.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm targetImages x q := by
  simpa [D.localized.localized_active, D.targetImages_active,
    BoundaryPieceFamilyInput.boundaryBulkSum] using
    D.bulk.bulkIntegralLocalizes

/-- Convert the compact-support-facing package to M8 measure-localization data. -/
def toM8MeasureLocalizationData :
    M8MeasureLocalizationData I omega selectedPartition targetImages where
  localizedInterior := D.localized.localizedInterior
  localized_active := D.localized.localized_active
  localized_coefficient := D.localized.localized_coefficient
  globalBulkIntegral := D.globalBulkIntegral
  bulkMeasureIntegral := D.globalBulkIntegral
  globalBulkIntegral_eq_bulkMeasureIntegral := rfl
  bulkMeasureIntegral_eq_localBulkSum :=
    D.bulkMeasureIntegral_eq_localBulkSum
  boundaryPartitionTerm := D.boundaryPartitionTerm
  globalBoundaryIntegral := D.globalBoundaryIntegral
  boundaryMeasureIntegral := D.boundary.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    D.globalBoundaryIntegral_eq_boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_partitionSum :=
    D.boundary.boundaryMeasureIntegral_eq_partitionSum

@[simp]
theorem toM8MeasureLocalizationData_localizedInterior :
    D.toM8MeasureLocalizationData.localizedInterior =
      D.localized.localizedInterior :=
  rfl

@[simp]
theorem toM8MeasureLocalizationData_globalBulkIntegral :
    D.toM8MeasureLocalizationData.globalBulkIntegral =
      D.globalBulkIntegral :=
  rfl

@[simp]
theorem toM8MeasureLocalizationData_bulkMeasureIntegral :
    D.toM8MeasureLocalizationData.bulkMeasureIntegral =
      D.globalBulkIntegral :=
  rfl

@[simp]
theorem toM8MeasureLocalizationData_boundaryPartitionTerm :
    D.toM8MeasureLocalizationData.boundaryPartitionTerm =
      D.boundaryPartitionTerm :=
  rfl

@[simp]
theorem toM8MeasureLocalizationData_globalBoundaryIntegral :
    D.toM8MeasureLocalizationData.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

@[simp]
theorem toM8MeasureLocalizationData_boundaryMeasureIntegral :
    D.toM8MeasureLocalizationData.boundaryMeasureIntegral =
      D.boundary.boundaryMeasureIntegral :=
  rfl

/--
Convenience constructor when the represented global boundary integral is taken
to be the boundary measure integral itself.
-/
def ofBoundaryMeasureIntegral
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (targetImages_active :
      targetImages.activeCharts = selectedPartition.active)
    (globalBulkIntegral : Real)
    (bulk :
      CompactSupportBulkMeasureData (α := α) (μ := μ)
        localized.localizedInterior targetImages globalBulkIntegral)
    (boundaryPartitionTerm : M → BoundaryPiece → Real)
    (boundary :
      BoundaryCompactMeasureFields μ selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm) :
    CompactSupportToM8MeasureData
      (α := α) I omega selectedPartition targetImages μ where
  localized := localized
  targetImages_active := targetImages_active
  globalBulkIntegral := globalBulkIntegral
  bulk := bulk
  boundaryPartitionTerm := boundaryPartitionTerm
  boundary := boundary
  globalBoundaryIntegral := boundary.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := rfl

omit [OpensMeasurableSpace α] [T2Space α] [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem ofBoundaryMeasureIntegral_globalBoundaryIntegral
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (targetImages_active :
      targetImages.activeCharts = selectedPartition.active)
    (globalBulkIntegral : Real)
    (bulk :
      CompactSupportBulkMeasureData (α := α) (μ := μ)
        localized.localizedInterior targetImages globalBulkIntegral)
    (boundaryPartitionTerm : M → BoundaryPiece → Real)
    (boundary :
      BoundaryCompactMeasureFields μ selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm) :
    (ofBoundaryMeasureIntegral (α := α) (μ := μ)
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      localized targetImages_active globalBulkIntegral bulk
      boundaryPartitionTerm boundary).globalBoundaryIntegral =
      boundary.boundaryMeasureIntegral :=
  rfl

end CompactSupportToM8MeasureData

end CompactSupportToM8Measure

end Stokes

end
