import Stokes.Global.BoundaryTargetSelectedBoxAlignment
import Stokes.Global.BulkMeasureSelectedBoxAlignment

/-!
# Boundary target compact-support glue for measure builders

This file connects the canonical boundary target compact-support route to the
compact-support measure builder.  It is a bookkeeping layer only: the genuine
boundary measure hypotheses stay as fields of
`CanonicalBoundaryTargetCompactSupportInput`, and no change-of-variables or
measure equality is inferred here.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryTargetMeasureBuilderGlue

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
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

namespace CanonicalBoundaryTargetCompactSupportInput

variable
    {D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}
    (B : CanonicalBoundaryTargetCompactSupportInput (α := α) D μ)

/-- The selected boundary partition data projected from the target-image input. -/
abbrev selectedBoundaryMeasurePartitionData
    (_B : CanonicalBoundaryTargetCompactSupportInput (α := α) D μ) :
    BoundaryMeasurePartitionData M BoundaryPiece :=
  D.toSelectedBoundaryMeasurePartitionData

/-- The selected compact boundary fields projected from canonical target data. -/
abbrev selectedBoundaryCompactFields
    (B : CanonicalBoundaryTargetCompactSupportInput (α := α) D μ) :
    BoundaryCompactMeasureFields μ selectedPartition.active
      D.targetImages.boundaryPieces D.assembly.boundaryPartitionTerm :=
  B.canonicalBoundaryCompactFields

@[simp]
theorem selectedBoundaryMeasurePartitionData_activeCharts :
    B.selectedBoundaryMeasurePartitionData.activeCharts =
      selectedPartition.active :=
  rfl

@[simp]
theorem selectedBoundaryMeasurePartitionData_boundaryPieces :
    B.selectedBoundaryMeasurePartitionData.boundaryPieces =
      D.targetImages.boundaryPieces :=
  rfl

@[simp]
theorem selectedBoundaryMeasurePartitionData_boundaryPartitionTerm :
    B.selectedBoundaryMeasurePartitionData.boundaryPartitionTerm =
      D.assembly.boundaryPartitionTerm :=
  rfl

@[simp]
theorem selectedBoundaryCompactFields_boundaryMeasureIntegral :
    B.selectedBoundaryCompactFields.boundaryMeasureIntegral =
      B.boundaryMeasureIntegral :=
  rfl

/--
Build the compact-support measure-side builder by using the canonical target
boundary compact-support package for the boundary half.
-/
def toMeasureBuilderData {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition D.targetImages
        globalBulkIntegral) :
    CompactSupportMeasureToM8BuilderData
      (α := α) I omega selectedPartition D.targetImages μ
      globalBulkIntegral B.globalBoundaryIntegral where
  bulk := bulk
  boundaryPartition := D.toSelectedBoundaryMeasurePartitionData
  boundary_active := rfl
  boundary_pieces := rfl
  boundaryIntegrand := B.boundaryIntegrand
  boundaryPieceSet := B.boundaryPieceSet
  boundaryPieceIntegrand := B.boundaryPieceIntegrand
  boundaryMeasureIntegral := B.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    B.globalBoundaryIntegral_eq_boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_integral :=
    B.boundaryMeasureIntegral_eq_integral
  boundaryPieceSet_measurable :=
    B.boundaryPieceSet_measurable
  boundaryPieceCompactSupport :=
    B.boundaryPieceCompact
  boundaryPartitionTerm_eq_setIntegral :=
    B.boundaryPartitionTerm_eq_setIntegral
  boundaryIntegrand_ae_eq_indicatorSum :=
    B.boundaryIntegrand_ae_eq_indicatorSum

@[simp]
theorem toMeasureBuilderData_boundaryPartition {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition D.targetImages
        globalBulkIntegral) :
    (B.toMeasureBuilderData bulk).boundaryPartition =
      D.toSelectedBoundaryMeasurePartitionData :=
  rfl

@[simp]
theorem toMeasureBuilderData_boundaryPartitionTerm {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition D.targetImages
        globalBulkIntegral) :
    (B.toMeasureBuilderData bulk).boundaryPartition.boundaryPartitionTerm =
      D.assembly.boundaryPartitionTerm :=
  rfl

@[simp]
theorem toMeasureBuilderData_boundaryMeasureIntegral {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition D.targetImages
        globalBulkIntegral) :
    (B.toMeasureBuilderData bulk).boundaryMeasureIntegral =
      B.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem toMeasureBuilderData_globalBoundaryIntegral {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition D.targetImages
        globalBulkIntegral) :
    (B.toMeasureBuilderData bulk).toCompactSupportToM8MeasureData.globalBoundaryIntegral =
      B.globalBoundaryIntegral :=
  rfl

@[simp]
theorem toMeasureBuilderData_compactSupport_boundaryPartitionTerm
    {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition D.targetImages
        globalBulkIntegral) :
    (B.toMeasureBuilderData bulk).toCompactSupportToM8MeasureData.boundaryPartitionTerm =
      D.assembly.boundaryPartitionTerm :=
  rfl

/--
Boundary-term equality in the exact shape consumed by the natural compact
support builders.
-/
theorem target_boundaryPartitionTerm_forMeasureBuilder
    {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition D.targetImages
        globalBulkIntegral) :
    D.assembly.boundaryPartitionTerm =
      (B.toMeasureBuilderData bulk).toCompactSupportToM8MeasureData.boundaryPartitionTerm :=
  rfl

@[simp]
theorem toMeasureBuilderData_toM8_boundaryPartitionTerm
    {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition D.targetImages
        globalBulkIntegral) :
    (B.toMeasureBuilderData bulk).toM8MeasureLocalizationData.boundaryPartitionTerm =
      D.assembly.boundaryPartitionTerm :=
  rfl

theorem target_boundaryPartitionTerm_forM8MeasureBuilder
    {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition D.targetImages
        globalBulkIntegral) :
    D.assembly.boundaryPartitionTerm =
      (B.toMeasureBuilderData bulk).toM8MeasureLocalizationData.boundaryPartitionTerm :=
  rfl

/--
The boundary partition term in the measure builder is still the selected
project-local boundary integral recorded by the target-image route.
-/
theorem toMeasureBuilderData_boundaryPartitionTerm_eq_projectLocal
    {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition D.targetImages
        globalBulkIntegral)
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    (B.toMeasureBuilderData bulk).boundaryPartition.boundaryPartitionTerm x q =
      projectLocalBoundaryIntegral I
        (D.assembly.boundaryTargetChart x q)
        (D.assembly.partitionTargetChart x q) omega
        (D.assembly.partitionLowerCorner x q)
        (D.assembly.partitionUpperCorner x q) := by
  simpa using
    D.boundaryPartitionTerm_eq_projectLocal_of_selected hx hq

end CanonicalBoundaryTargetCompactSupportInput

namespace NaturalCompactSupportBuilderData

variable
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
variable {globalBulkIntegral : Real}

/--
Natural builder entry point from canonical boundary target compact-support data,
bulk measure data, and a form strict buffer.  The target/boundary partition term
alignment is supplied by `target_boundaryPartitionTerm_forMeasureBuilder`.
-/
def ofCanonicalBoundaryTargetWithFormInnerBoxBuffer
    (boundaryTarget :
      CanonicalBoundaryTargetCompactSupportInput
        (α := α) targetImageInput μ)
    (bulk :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition targetImageInput.targetImages
        globalBulkIntegral)
    (buffer :
      LocalizedInteriorFormInnerBoxBuffer I omega selectedPartition
        targetImageInput.targetImages
        (boundaryTarget.toMeasureBuilderData bulk).toM8MeasureLocalizationData) :
    NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ :=
  ofMeasureBuilderWithFormInnerBoxBuffer
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    formData orientedBoundaryAtlas selectedPartition selectedPartition_supportSet
    targetImageInput (boundaryTarget.toMeasureBuilderData bulk)
    (boundaryTarget.target_boundaryPartitionTerm_forMeasureBuilder bulk)
    buffer

@[simp]
theorem ofCanonicalBoundaryTargetWithFormInnerBoxBuffer_measure
    (boundaryTarget :
      CanonicalBoundaryTargetCompactSupportInput
        (α := α) targetImageInput μ)
    (bulk :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition targetImageInput.targetImages
        globalBulkIntegral)
    (buffer :
      LocalizedInteriorFormInnerBoxBuffer I omega selectedPartition
        targetImageInput.targetImages
        (boundaryTarget.toMeasureBuilderData bulk).toM8MeasureLocalizationData) :
    (ofCanonicalBoundaryTargetWithFormInnerBoxBuffer
      (α := α) (μ := μ) (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece)
      formData orientedBoundaryAtlas selectedPartition selectedPartition_supportSet
      targetImageInput boundaryTarget bulk buffer).measure =
        (boundaryTarget.toMeasureBuilderData bulk).toCompactSupportToM8MeasureData :=
  rfl

/--
Natural builder entry point from canonical boundary target compact-support data,
bulk measure data, and a coefficient strict buffer.
-/
def ofCanonicalBoundaryTargetWithCoefficientInnerBoxBuffer
    (boundaryTarget :
      CanonicalBoundaryTargetCompactSupportInput
        (α := α) targetImageInput μ)
    (bulk :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition targetImageInput.targetImages
        globalBulkIntegral)
    (buffer :
      LocalizedInteriorCoefficientInnerBoxBuffer I omega selectedPartition
        targetImageInput.targetImages
        (boundaryTarget.toMeasureBuilderData bulk).toM8MeasureLocalizationData) :
    NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ :=
  ofMeasureBuilderWithCoefficientInnerBoxBuffer
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    formData orientedBoundaryAtlas selectedPartition selectedPartition_supportSet
    targetImageInput (boundaryTarget.toMeasureBuilderData bulk)
    (boundaryTarget.target_boundaryPartitionTerm_forMeasureBuilder bulk)
    buffer

@[simp]
theorem ofCanonicalBoundaryTargetWithCoefficientInnerBoxBuffer_measure
    (boundaryTarget :
      CanonicalBoundaryTargetCompactSupportInput
        (α := α) targetImageInput μ)
    (bulk :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition targetImageInput.targetImages
        globalBulkIntegral)
    (buffer :
      LocalizedInteriorCoefficientInnerBoxBuffer I omega selectedPartition
        targetImageInput.targetImages
        (boundaryTarget.toMeasureBuilderData bulk).toM8MeasureLocalizationData) :
    (ofCanonicalBoundaryTargetWithCoefficientInnerBoxBuffer
      (α := α) (μ := μ) (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece)
      formData orientedBoundaryAtlas selectedPartition selectedPartition_supportSet
      targetImageInput boundaryTarget bulk buffer).measure =
        (boundaryTarget.toMeasureBuilderData bulk).toCompactSupportToM8MeasureData :=
  rfl

end NaturalCompactSupportBuilderData

end BoundaryTargetMeasureBuilderGlue

end Stokes

end
