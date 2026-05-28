import Stokes.Global.M8Statement
import Stokes.Global.BoundaryCOVMeasureConstructor

/-!
# Boundary measure localization to M8

This file is a boundary-only adapter layer for the M8 statement.  It converts
the existing boundary measure-localization packages into the exact boundary
fields used by `M8MeasureLocalizationData`, without changing any bulk data.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryMeasureToM8

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

/--
Boundary-only measure data in the exact shape needed by the M8 measure package.

The active chart set is fixed to the selected partition, and the boundary-piece
family is fixed to the target-image family.  Bulk localization is intentionally
absent from this record.
-/
structure M8BoundaryMeasureData
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece) where
  /-- Boundary partition term after target-image transport and chart changes. -/
  boundaryPartitionTerm : M → BoundaryPiece → Real
  /-- The represented global boundary integral. -/
  globalBoundaryIntegral : Real
  /-- The genuine boundary measure integral. -/
  boundaryMeasureIntegral : Real
  /-- The represented boundary integral agrees with the boundary measure integral. -/
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :
    globalBoundaryIntegral = boundaryMeasureIntegral
  /-- The boundary measure integral is reconstructed from partition terms. -/
  boundaryMeasureIntegral_eq_partitionSum :
    boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm

namespace M8BoundaryMeasureData

variable
    {D : M8BoundaryMeasureData I omega selectedPartition targetImages}

/-- Forget the M8 wrapper and expose the natural measure-localization fields. -/
def toBoundaryMeasureLocalizationFields
    (D : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    BoundaryMeasureLocalizationFields selectedPartition.active
      targetImages.boundaryPieces D.boundaryPartitionTerm
      D.globalBoundaryIntegral where
  boundaryMeasureIntegral := D.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    D.globalBoundaryIntegral_eq_boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_partitionSum :=
    D.boundaryMeasureIntegral_eq_partitionSum

/-- Forget the intermediate measure integral and keep boundary reconstruction. -/
def toBoundaryIntegralReconstructionData
    (D : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    BoundaryIntegralReconstructionData selectedPartition.active
      targetImages.boundaryPieces D.boundaryPartitionTerm
      D.globalBoundaryIntegral :=
  D.toBoundaryMeasureLocalizationFields.toBoundaryIntegralReconstructionData

@[simp]
theorem toBoundaryMeasureLocalizationFields_boundaryMeasureIntegral
    (D : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    D.toBoundaryMeasureLocalizationFields.boundaryMeasureIntegral =
      D.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem toBoundaryMeasureLocalizationFields_globalBoundaryIntegral_eq_partitionSum
    (D : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    D.toBoundaryMeasureLocalizationFields.globalBoundaryIntegral_eq_partitionSum =
      D.globalBoundaryIntegral_eq_boundaryMeasureIntegral.trans
        D.boundaryMeasureIntegral_eq_partitionSum :=
  rfl

/-- Projection theorem in the exact finite-sum form usually needed by M8. -/
theorem boundaryMeasureIntegral_eq_partitionSum'
    (D : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    D.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces D.boundaryPartitionTerm :=
  D.boundaryMeasureIntegral_eq_partitionSum

/-- Expanded nested finite-sum projection for call sites that avoid the helper. -/
theorem boundaryMeasureIntegral_eq_partitionSum_expanded
    (D : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    D.boundaryMeasureIntegral =
      Finset.sum selectedPartition.active fun x =>
        Finset.sum (targetImages.boundaryPieces x) fun q =>
          D.boundaryPartitionTerm x q := by
  simpa [selectedBoundaryPieceSum] using
    D.boundaryMeasureIntegral_eq_partitionSum

/-- Build M8 boundary data from the natural fieldized boundary package. -/
def ofBoundaryMeasureLocalizationFields
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    {globalBoundaryIntegral : Real}
    (B :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    M8BoundaryMeasureData I omega selectedPartition targetImages where
  boundaryPartitionTerm := boundaryPartitionTerm
  globalBoundaryIntegral := globalBoundaryIntegral
  boundaryMeasureIntegral := B.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    B.globalBoundaryIntegral_eq_boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_partitionSum :=
    B.boundaryMeasureIntegral_eq_partitionSum

@[simp]
theorem ofBoundaryMeasureLocalizationFields_boundaryPartitionTerm
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    {globalBoundaryIntegral : Real}
    (B :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    (ofBoundaryMeasureLocalizationFields
      (I := I) (omega := omega) (selectedPartition := selectedPartition)
      (targetImages := targetImages) B).boundaryPartitionTerm =
      boundaryPartitionTerm :=
  rfl

@[simp]
theorem ofBoundaryMeasureLocalizationFields_globalBoundaryIntegral
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    {globalBoundaryIntegral : Real}
    (B :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    (ofBoundaryMeasureLocalizationFields
      (I := I) (omega := omega) (selectedPartition := selectedPartition)
      (targetImages := targetImages) B).globalBoundaryIntegral =
      globalBoundaryIntegral :=
  rfl

@[simp]
theorem ofBoundaryMeasureLocalizationFields_boundaryMeasureIntegral
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    {globalBoundaryIntegral : Real}
    (B :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    (ofBoundaryMeasureLocalizationFields
      (I := I) (omega := omega) (selectedPartition := selectedPartition)
      (targetImages := targetImages) B).boundaryMeasureIntegral =
      B.boundaryMeasureIntegral :=
  rfl

/-- The fieldized package supplies M8's boundary finite-sum field. -/
theorem ofBoundaryMeasureLocalizationFields_boundaryMeasureIntegral_eq_partitionSum
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    {globalBoundaryIntegral : Real}
    (B :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    (ofBoundaryMeasureLocalizationFields
      (I := I) (omega := omega) (selectedPartition := selectedPartition)
      (targetImages := targetImages) B).boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm :=
  B.boundaryMeasureIntegral_eq_partitionSum

/-- Build M8 boundary data from the analytic boundary-measure localization record. -/
def ofBoundaryMeasureLocalizationData
    {α : Type a} [MeasurableSpace α]
    {μ : Measure α}
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    (B :
      BoundaryMeasureLocalizationData μ selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm)
    (globalBoundaryIntegral : Real)
    (hmeasure : globalBoundaryIntegral = B.boundaryMeasureIntegral) :
    M8BoundaryMeasureData I omega selectedPartition targetImages :=
  ofBoundaryMeasureLocalizationFields
    (I := I) (omega := omega) (selectedPartition := selectedPartition)
    (targetImages := targetImages)
    (B.toBoundaryMeasureLocalizationFields globalBoundaryIntegral hmeasure)

@[simp]
theorem ofBoundaryMeasureLocalizationData_boundaryMeasureIntegral
    {α : Type a} [MeasurableSpace α]
    {μ : Measure α}
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    (B :
      BoundaryMeasureLocalizationData μ selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm)
    (globalBoundaryIntegral : Real)
    (hmeasure : globalBoundaryIntegral = B.boundaryMeasureIntegral) :
    (ofBoundaryMeasureLocalizationData
      (I := I) (omega := omega) (selectedPartition := selectedPartition)
      (targetImages := targetImages) B globalBoundaryIntegral hmeasure).boundaryMeasureIntegral =
      B.boundaryMeasureIntegral :=
  rfl

/-- The analytic localization record supplies M8's boundary finite-sum field. -/
theorem ofBoundaryMeasureLocalizationData_boundaryMeasureIntegral_eq_partitionSum
    {α : Type a} [MeasurableSpace α]
    {μ : Measure α}
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    (B :
      BoundaryMeasureLocalizationData μ selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm)
    (globalBoundaryIntegral : Real)
    (hmeasure : globalBoundaryIntegral = B.boundaryMeasureIntegral) :
    (ofBoundaryMeasureLocalizationData
      (I := I) (omega := omega) (selectedPartition := selectedPartition)
      (targetImages := targetImages) B globalBoundaryIntegral hmeasure).boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm :=
  B.boundaryMeasureIntegral_eq_partitionSum

/--
Build M8 boundary data from the boundary-chart COV measure reconstruction
fields.  The two alignment hypotheses identify the COV family with the M8
selected partition and target-image boundary pieces.
-/
def ofBoundaryCOVMeasureReconstructionFields
    [IsManifold I 1 M]
    {F : BoundaryChartChangeOfVariablesFamily I omega M BoundaryPiece}
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    {globalBoundaryIntegral : Real}
    (B :
      BoundaryChartChangeOfVariablesFamily.BoundaryCOVMeasureReconstructionFields
        F boundaryPartitionTerm globalBoundaryIntegral)
    (hactive : F.activeCharts = selectedPartition.active)
    (hpieces : F.localPieces = targetImages.boundaryPieces) :
    M8BoundaryMeasureData I omega selectedPartition targetImages where
  boundaryPartitionTerm := boundaryPartitionTerm
  globalBoundaryIntegral := globalBoundaryIntegral
  boundaryMeasureIntegral := B.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    B.manifoldBoundaryIntegral_eq_boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_partitionSum := by
    have h := B.boundaryMeasureIntegral_eq_partitionSum
    simpa [hactive, hpieces] using h

@[simp]
theorem ofBoundaryCOVMeasureReconstructionFields_boundaryMeasureIntegral
    [IsManifold I 1 M]
    {F : BoundaryChartChangeOfVariablesFamily I omega M BoundaryPiece}
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    {globalBoundaryIntegral : Real}
    (B :
      BoundaryChartChangeOfVariablesFamily.BoundaryCOVMeasureReconstructionFields
        F boundaryPartitionTerm globalBoundaryIntegral)
    (hactive : F.activeCharts = selectedPartition.active)
    (hpieces : F.localPieces = targetImages.boundaryPieces) :
    (ofBoundaryCOVMeasureReconstructionFields
      (I := I) (omega := omega) (selectedPartition := selectedPartition)
      (targetImages := targetImages) B hactive hpieces).boundaryMeasureIntegral =
      B.boundaryMeasureIntegral :=
  rfl

/-- The COV measure fields supply M8's boundary finite-sum field. -/
theorem ofBoundaryCOVMeasureReconstructionFields_boundaryMeasureIntegral_eq_partitionSum
    [IsManifold I 1 M]
    {F : BoundaryChartChangeOfVariablesFamily I omega M BoundaryPiece}
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    {globalBoundaryIntegral : Real}
    (B :
      BoundaryChartChangeOfVariablesFamily.BoundaryCOVMeasureReconstructionFields
        F boundaryPartitionTerm globalBoundaryIntegral)
    (hactive : F.activeCharts = selectedPartition.active)
    (hpieces : F.localPieces = targetImages.boundaryPieces) :
    (ofBoundaryCOVMeasureReconstructionFields
      (I := I) (omega := omega) (selectedPartition := selectedPartition)
      (targetImages := targetImages) B hactive hpieces).boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm :=
  (ofBoundaryCOVMeasureReconstructionFields
      (I := I) (omega := omega) (selectedPartition := selectedPartition)
      (targetImages := targetImages) B hactive hpieces).boundaryMeasureIntegral_eq_partitionSum

end M8BoundaryMeasureData

namespace M8MeasureLocalizationData

/--
Replace only the boundary component of an M8 measure-localization package,
leaving all bulk and localized-interior fields unchanged.
-/
def withBoundaryMeasureData
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (B : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    M8MeasureLocalizationData I omega selectedPartition targetImages where
  localizedInterior := D.localizedInterior
  localized_active := D.localized_active
  localized_coefficient := D.localized_coefficient
  globalBulkIntegral := D.globalBulkIntegral
  bulkMeasureIntegral := D.bulkMeasureIntegral
  globalBulkIntegral_eq_bulkMeasureIntegral :=
    D.globalBulkIntegral_eq_bulkMeasureIntegral
  bulkMeasureIntegral_eq_localBulkSum :=
    D.bulkMeasureIntegral_eq_localBulkSum
  boundaryPartitionTerm := B.boundaryPartitionTerm
  globalBoundaryIntegral := B.globalBoundaryIntegral
  boundaryMeasureIntegral := B.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    B.globalBoundaryIntegral_eq_boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_partitionSum :=
    B.boundaryMeasureIntegral_eq_partitionSum

@[simp]
theorem withBoundaryMeasureData_boundaryPartitionTerm
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (B : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    (D.withBoundaryMeasureData B).boundaryPartitionTerm =
      B.boundaryPartitionTerm :=
  rfl

@[simp]
theorem withBoundaryMeasureData_globalBoundaryIntegral
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (B : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    (D.withBoundaryMeasureData B).globalBoundaryIntegral =
      B.globalBoundaryIntegral :=
  rfl

@[simp]
theorem withBoundaryMeasureData_boundaryMeasureIntegral
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (B : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    (D.withBoundaryMeasureData B).boundaryMeasureIntegral =
      B.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem withBoundaryMeasureData_globalBulkIntegral
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (B : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    (D.withBoundaryMeasureData B).globalBulkIntegral =
      D.globalBulkIntegral :=
  rfl

@[simp]
theorem withBoundaryMeasureData_bulkMeasureIntegral
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (B : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    (D.withBoundaryMeasureData B).bulkMeasureIntegral =
      D.bulkMeasureIntegral :=
  rfl

/-- Projection theorem for the boundary finite-sum field after replacement. -/
theorem withBoundaryMeasureData_boundaryMeasureIntegral_eq_partitionSum
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (B : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    (D.withBoundaryMeasureData B).boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces B.boundaryPartitionTerm :=
  B.boundaryMeasureIntegral_eq_partitionSum

/-- Replace the M8 boundary component from natural boundary localization fields. -/
def withBoundaryMeasureLocalizationFields
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    {globalBoundaryIntegral : Real}
    (B :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    M8MeasureLocalizationData I omega selectedPartition targetImages :=
  D.withBoundaryMeasureData
    (M8BoundaryMeasureData.ofBoundaryMeasureLocalizationFields
      (I := I) (omega := omega) (selectedPartition := selectedPartition)
      (targetImages := targetImages) B)

@[simp]
theorem withBoundaryMeasureLocalizationFields_boundaryMeasureIntegral
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    {globalBoundaryIntegral : Real}
    (B :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    (D.withBoundaryMeasureLocalizationFields B).boundaryMeasureIntegral =
      B.boundaryMeasureIntegral :=
  rfl

/-- Natural fieldized localization supplies the M8 boundary finite-sum field. -/
theorem withBoundaryMeasureLocalizationFields_boundaryMeasureIntegral_eq_partitionSum
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    {globalBoundaryIntegral : Real}
    (B :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    (D.withBoundaryMeasureLocalizationFields B).boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm :=
  B.boundaryMeasureIntegral_eq_partitionSum

/-- Replace the M8 boundary component from analytic boundary localization data. -/
def withBoundaryMeasureLocalizationData
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    {α : Type a} [MeasurableSpace α]
    {μ : Measure α}
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    (B :
      BoundaryMeasureLocalizationData μ selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm)
    (globalBoundaryIntegral : Real)
    (hmeasure : globalBoundaryIntegral = B.boundaryMeasureIntegral) :
    M8MeasureLocalizationData I omega selectedPartition targetImages :=
  D.withBoundaryMeasureData
    (M8BoundaryMeasureData.ofBoundaryMeasureLocalizationData
      (I := I) (omega := omega) (selectedPartition := selectedPartition)
      (targetImages := targetImages) B globalBoundaryIntegral hmeasure)

@[simp]
theorem withBoundaryMeasureLocalizationData_boundaryMeasureIntegral
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    {α : Type a} [MeasurableSpace α]
    {μ : Measure α}
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    (B :
      BoundaryMeasureLocalizationData μ selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm)
    (globalBoundaryIntegral : Real)
    (hmeasure : globalBoundaryIntegral = B.boundaryMeasureIntegral) :
    (let R := D.withBoundaryMeasureLocalizationData B globalBoundaryIntegral hmeasure
     R.boundaryMeasureIntegral) =
      B.boundaryMeasureIntegral :=
  rfl

/-- Analytic boundary localization supplies the M8 boundary finite-sum field. -/
theorem withBoundaryMeasureLocalizationData_boundaryMeasureIntegral_eq_partitionSum
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    {α : Type a} [MeasurableSpace α]
    {μ : Measure α}
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    (B :
      BoundaryMeasureLocalizationData μ selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm)
    (globalBoundaryIntegral : Real)
    (hmeasure : globalBoundaryIntegral = B.boundaryMeasureIntegral) :
    (let R := D.withBoundaryMeasureLocalizationData B globalBoundaryIntegral hmeasure
     R.boundaryMeasureIntegral) =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm :=
  B.boundaryMeasureIntegral_eq_partitionSum

end M8MeasureLocalizationData

end BoundaryMeasureToM8

end Stokes

end
