import Stokes.Global.NaturalCompactActiveStrictBuilder
import Stokes.Global.BulkMeasureSelectedBoxAlignment
import Stokes.Global.SelectedPartitionCompactActiveAlignment
import Stokes.Global.LocalizedInteriorPieceAlignment

/-!
# Natural measure/strict-buffer builders

This file composes the measure-side builder with the compact-active
strict-buffer route.

The declarations here do not prove new analytic localization or boundary
change-of-variables facts.  They remove bookkeeping that is already determined
by the existing packages:

* `CompactSupportMeasureToM8BuilderData` supplies the compact-support measure
  package and its localized-interior equality;
* compact-active strict-buffer alignment supplies the artificial-face buffer;
* a small higher-level alignment record reduces the strict-buffer input to
  selected-partition alignment, localized-piece chart alignment, and strict
  outer-box margins.

The remaining genuinely mathematical boundary identification is kept explicit
as `target_boundaryPartitionTerm_eq_measureBuilder`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalMeasureStrictBuilder

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

namespace NaturalCompactSupportBuilderData

variable
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
variable {globalBulkIntegral globalBoundaryIntegral : Real}

/--
Natural builder from the measure-side builder plus compact-active strict-buffer
alignment.

The selected localized-interior equality is projected from
`measureBuilder`; callers only still provide the real boundary-term equality
between the target-image assembly and the measure partition.
-/
def ofMeasureBuilderWithCompactActiveBoxAlignment
    (measureBuilder :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImageInput.targetImages μ
        globalBulkIntegral globalBoundaryIntegral)
    (target_boundaryPartitionTerm_eq_measureBuilder :
      targetImageInput.assembly.boundaryPartitionTerm =
        measureBuilder.toCompactSupportToM8MeasureData.boundaryPartitionTerm)
    {D : CompactActiveBoxData I omega}
    (alignment :
      CompactActiveBoxStrictBufferAlignment D selectedPartition
        targetImageInput.targetImages measureBuilder.toM8MeasureLocalizationData) :
    NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ :=
  ofMeasureBuilderWithFormInnerBoxBuffer
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    formData orientedBoundaryAtlas selectedPartition
    selectedPartition_supportSet targetImageInput measureBuilder
    target_boundaryPartitionTerm_eq_measureBuilder
    alignment.toLocalizedInteriorFormInnerBoxBuffer

@[simp]
theorem ofMeasureBuilderWithCompactActiveBoxAlignment_measure
    (measureBuilder :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImageInput.targetImages μ
        globalBulkIntegral globalBoundaryIntegral)
    (target_boundaryPartitionTerm_eq_measureBuilder :
      targetImageInput.assembly.boundaryPartitionTerm =
        measureBuilder.toCompactSupportToM8MeasureData.boundaryPartitionTerm)
    {D : CompactActiveBoxData I omega}
    (alignment :
      CompactActiveBoxStrictBufferAlignment D selectedPartition
        targetImageInput.targetImages measureBuilder.toM8MeasureLocalizationData) :
    (ofMeasureBuilderWithCompactActiveBoxAlignment
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      formData selectedPartition_supportSet targetImageInput measureBuilder
      target_boundaryPartitionTerm_eq_measureBuilder alignment).measure =
        measureBuilder.toCompactSupportToM8MeasureData := by
  rfl

@[simp]
theorem ofMeasureBuilderWithCompactActiveBoxAlignment_localizedInterior
    (measureBuilder :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImageInput.targetImages μ
        globalBulkIntegral globalBoundaryIntegral)
    (target_boundaryPartitionTerm_eq_measureBuilder :
      targetImageInput.assembly.boundaryPartitionTerm =
        measureBuilder.toCompactSupportToM8MeasureData.boundaryPartitionTerm)
    {D : CompactActiveBoxData I omega}
    (alignment :
      CompactActiveBoxStrictBufferAlignment D selectedPartition
        targetImageInput.targetImages measureBuilder.toM8MeasureLocalizationData) :
    (ofMeasureBuilderWithCompactActiveBoxAlignment
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      formData selectedPartition_supportSet targetImageInput measureBuilder
      target_boundaryPartitionTerm_eq_measureBuilder alignment).localizedInterior =
        measureBuilder.bulk.localized := by
  rfl

@[simp]
theorem ofMeasureBuilderWithCompactActiveBoxAlignment_artificial
    (measureBuilder :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImageInput.targetImages μ
        globalBulkIntegral globalBoundaryIntegral)
    (target_boundaryPartitionTerm_eq_measureBuilder :
      targetImageInput.assembly.boundaryPartitionTerm =
        measureBuilder.toCompactSupportToM8MeasureData.boundaryPartitionTerm)
    {D : CompactActiveBoxData I omega}
    (alignment :
      CompactActiveBoxStrictBufferAlignment D selectedPartition
        targetImageInput.targetImages measureBuilder.toM8MeasureLocalizationData) :
    (ofMeasureBuilderWithCompactActiveBoxAlignment
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      formData selectedPartition_supportSet targetImageInput measureBuilder
      target_boundaryPartitionTerm_eq_measureBuilder alignment).artificial =
        alignment.toLocalizedInteriorFormInnerBoxBuffer.toM8ArtificialFaceFields := by
  rfl

end NaturalCompactSupportBuilderData

namespace NaturalCompactSupportStokesInput

variable
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
variable {globalBulkIntegral globalBoundaryIntegral : Real}

/--
Natural compact-support Stokes input from the measure-side builder plus
compact-active strict-buffer alignment.
-/
def ofMeasureBuilderWithCompactActiveBoxAlignment
    (measureBuilder :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImageInput.targetImages μ
        globalBulkIntegral globalBoundaryIntegral)
    (target_boundaryPartitionTerm_eq_measureBuilder :
      targetImageInput.assembly.boundaryPartitionTerm =
        measureBuilder.toCompactSupportToM8MeasureData.boundaryPartitionTerm)
    {D : CompactActiveBoxData I omega}
    (alignment :
      CompactActiveBoxStrictBufferAlignment D selectedPartition
        targetImageInput.targetImages measureBuilder.toM8MeasureLocalizationData) :
    NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ :=
  ofPackagesWithFormInnerBoxBuffer
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    formData orientedBoundaryAtlas selectedPartition
    selectedPartition_supportSet targetImageInput
    measureBuilder.toCompactSupportToM8MeasureData
    target_boundaryPartitionTerm_eq_measureBuilder
    alignment.toLocalizedInteriorFormInnerBoxBuffer

@[simp]
theorem ofMeasureBuilderWithCompactActiveBoxAlignment_measure
    (measureBuilder :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImageInput.targetImages μ
        globalBulkIntegral globalBoundaryIntegral)
    (target_boundaryPartitionTerm_eq_measureBuilder :
      targetImageInput.assembly.boundaryPartitionTerm =
        measureBuilder.toCompactSupportToM8MeasureData.boundaryPartitionTerm)
    {D : CompactActiveBoxData I omega}
    (alignment :
      CompactActiveBoxStrictBufferAlignment D selectedPartition
        targetImageInput.targetImages measureBuilder.toM8MeasureLocalizationData) :
    (ofMeasureBuilderWithCompactActiveBoxAlignment
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      formData selectedPartition_supportSet targetImageInput measureBuilder
      target_boundaryPartitionTerm_eq_measureBuilder alignment).measure =
        measureBuilder.toCompactSupportToM8MeasureData := by
  rfl

@[simp]
theorem ofMeasureBuilderWithCompactActiveBoxAlignment_artificial
    (measureBuilder :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImageInput.targetImages μ
        globalBulkIntegral globalBoundaryIntegral)
    (target_boundaryPartitionTerm_eq_measureBuilder :
      targetImageInput.assembly.boundaryPartitionTerm =
        measureBuilder.toCompactSupportToM8MeasureData.boundaryPartitionTerm)
    {D : CompactActiveBoxData I omega}
    (alignment :
      CompactActiveBoxStrictBufferAlignment D selectedPartition
        targetImageInput.targetImages measureBuilder.toM8MeasureLocalizationData) :
    (ofMeasureBuilderWithCompactActiveBoxAlignment
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      formData selectedPartition_supportSet targetImageInput measureBuilder
      target_boundaryPartitionTerm_eq_measureBuilder alignment).artificial =
        alignment.toLocalizedInteriorFormInnerBoxBuffer.toM8ArtificialFaceFields := by
  rfl

end NaturalCompactSupportStokesInput

/--
Higher-level alignment package for the measure-builder/strict-buffer route.

This record keeps only the facts not already projected from the measure-side
builder.  It still exposes the real boundary partition-term identification,
because that is a boundary COV/target-image statement rather than bookkeeping.
-/
structure NaturalMeasureStrictBuilderAlignment
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    {globalBulkIntegral globalBoundaryIntegral : Real}
    (measureBuilder :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImageInput.targetImages μ
        globalBulkIntegral globalBoundaryIntegral)
    (D : CompactActiveBoxData I omega) where
  /-- The selected partition is the one controlled by the compact active boxes. -/
  selectedPartitionAlignment :
    CompactActiveSelectedPartitionAlignment D selectedPartition
  /-- The measure-localized pieces use the selected chart label as source/target. -/
  localizedPieceAlignment :
    LocalizedInteriorPieceAlignment selectedPartition
      targetImageInput.targetImages measureBuilder.toM8MeasureLocalizationData
  /-- The measure outer lower corner is strictly below the selected inner lower corner. -/
  outer_lower_lt_selectedLower :
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      (measureBuilder.toM8MeasureLocalizationData.localizedInterior.piece x).lowerCorner j <
        selectedPartition.lower x j
  /-- The selected inner upper corner is strictly below the measure outer upper corner. -/
  selectedUpper_lt_outer_upper :
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      selectedPartition.upper x j <
        (measureBuilder.toM8MeasureLocalizationData.localizedInterior.piece x).upperCorner j
  /--
  Boundary assembly and measure-side boundary partition terms agree.

  This is the remaining non-bookkeeping boundary input.
  -/
  target_boundaryPartitionTerm_eq_measureBuilder :
    targetImageInput.assembly.boundaryPartitionTerm =
      measureBuilder.toCompactSupportToM8MeasureData.boundaryPartitionTerm

namespace NaturalMeasureStrictBuilderAlignment

variable
    {targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}
variable {globalBulkIntegral globalBoundaryIntegral : Real}
variable
    {measureBuilder :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImageInput.targetImages μ
        globalBulkIntegral globalBoundaryIntegral}
variable {D : CompactActiveBoxData I omega}

/--
Convert the higher-level alignment package to the strict-buffer alignment
consumed downstream.
-/
def toCompactActiveBoxStrictBufferAlignment
    (A :
      NaturalMeasureStrictBuilderAlignment targetImageInput measureBuilder D) :
    CompactActiveBoxStrictBufferAlignment D selectedPartition
      targetImageInput.targetImages measureBuilder.toM8MeasureLocalizationData :=
  A.selectedPartitionAlignment.toStrictBufferAlignmentOfSelectedPartitionPiece
    A.localizedPieceAlignment.piece_transitionPullback_eq
    A.outer_lower_lt_selectedLower
    A.selectedUpper_lt_outer_upper

@[simp]
theorem toCompactActiveBoxStrictBufferAlignment_active_subset
    (A :
      NaturalMeasureStrictBuilderAlignment targetImageInput measureBuilder D) :
    A.toCompactActiveBoxStrictBufferAlignment.active_subset =
      A.selectedPartitionAlignment.active_subset := by
  rfl

@[simp]
theorem toCompactActiveBoxStrictBufferAlignment_outer_lower
    (A :
      NaturalMeasureStrictBuilderAlignment targetImageInput measureBuilder D) :
    A.toCompactActiveBoxStrictBufferAlignment.outer_lower_lt_innerLower =
      fun x hx j =>
        show
          (measureBuilder.toM8MeasureLocalizationData.localizedInterior.piece x).lowerCorner j <
            D.lower x j from
        by
          simpa [A.selectedPartitionAlignment.lower_eq] using
            A.outer_lower_lt_selectedLower x hx j := by
  rfl

/-- Build natural builder data from the compact measure builder and high-level strict alignment. -/
def toNaturalCompactSupportBuilderData
    (A :
      NaturalMeasureStrictBuilderAlignment targetImageInput measureBuilder D)
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet) :
    NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ :=
  NaturalCompactSupportBuilderData.ofMeasureBuilderWithCompactActiveBoxAlignment
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    formData selectedPartition_supportSet targetImageInput measureBuilder
    A.target_boundaryPartitionTerm_eq_measureBuilder
    A.toCompactActiveBoxStrictBufferAlignment

/--
Build natural compact-support Stokes input from the compact measure builder and
high-level strict alignment.
-/
def toNaturalCompactSupportStokesInput
    (A :
      NaturalMeasureStrictBuilderAlignment targetImageInput measureBuilder D)
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet) :
    NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ :=
  NaturalCompactSupportStokesInput.ofMeasureBuilderWithCompactActiveBoxAlignment
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    formData selectedPartition_supportSet targetImageInput measureBuilder
    A.target_boundaryPartitionTerm_eq_measureBuilder
    A.toCompactActiveBoxStrictBufferAlignment

@[simp]
theorem toNaturalCompactSupportBuilderData_measure
    (A :
      NaturalMeasureStrictBuilderAlignment targetImageInput measureBuilder D)
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet) :
    (A.toNaturalCompactSupportBuilderData
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      formData selectedPartition_supportSet).measure =
        measureBuilder.toCompactSupportToM8MeasureData := by
  rfl

@[simp]
theorem toNaturalCompactSupportStokesInput_measure
    (A :
      NaturalMeasureStrictBuilderAlignment targetImageInput measureBuilder D)
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet) :
    (A.toNaturalCompactSupportStokesInput
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      formData selectedPartition_supportSet).measure =
        measureBuilder.toCompactSupportToM8MeasureData := by
  rfl

end NaturalMeasureStrictBuilderAlignment

namespace NaturalCompactSupportBuilderData

variable
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
variable {globalBulkIntegral globalBoundaryIntegral : Real}

/--
Natural builder from the measure-side builder and the higher-level strict
alignment package.
-/
def ofNaturalMeasureStrictBuilderAlignment
    (measureBuilder :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImageInput.targetImages μ
        globalBulkIntegral globalBoundaryIntegral)
    {D : CompactActiveBoxData I omega}
    (alignment :
      NaturalMeasureStrictBuilderAlignment targetImageInput measureBuilder D) :
    NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ :=
  alignment.toNaturalCompactSupportBuilderData
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    formData selectedPartition_supportSet

@[simp]
theorem ofNaturalMeasureStrictBuilderAlignment_artificial
    (measureBuilder :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImageInput.targetImages μ
        globalBulkIntegral globalBoundaryIntegral)
    {D : CompactActiveBoxData I omega}
    (alignment :
      NaturalMeasureStrictBuilderAlignment targetImageInput measureBuilder D) :
    (ofNaturalMeasureStrictBuilderAlignment
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      formData selectedPartition_supportSet targetImageInput measureBuilder
      alignment).artificial =
        (alignment.toCompactActiveBoxStrictBufferAlignment
          |>.toLocalizedInteriorFormInnerBoxBuffer
          |>.toM8ArtificialFaceFields) := by
  rfl

end NaturalCompactSupportBuilderData

namespace NaturalCompactSupportStokesInput

variable
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
variable {globalBulkIntegral globalBoundaryIntegral : Real}

/--
Natural compact-support Stokes input from the measure-side builder and the
higher-level strict alignment package.
-/
def ofNaturalMeasureStrictBuilderAlignment
    (measureBuilder :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImageInput.targetImages μ
        globalBulkIntegral globalBoundaryIntegral)
    {D : CompactActiveBoxData I omega}
    (alignment :
      NaturalMeasureStrictBuilderAlignment targetImageInput measureBuilder D) :
    NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ :=
  alignment.toNaturalCompactSupportStokesInput
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    formData selectedPartition_supportSet

@[simp]
theorem ofNaturalMeasureStrictBuilderAlignment_artificial
    (measureBuilder :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImageInput.targetImages μ
        globalBulkIntegral globalBoundaryIntegral)
    {D : CompactActiveBoxData I omega}
    (alignment :
      NaturalMeasureStrictBuilderAlignment targetImageInput measureBuilder D) :
    (ofNaturalMeasureStrictBuilderAlignment
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      formData selectedPartition_supportSet targetImageInput measureBuilder
      alignment).artificial =
        (alignment.toCompactActiveBoxStrictBufferAlignment
          |>.toLocalizedInteriorFormInnerBoxBuffer
          |>.toM8ArtificialFaceFields) := by
  rfl

end NaturalCompactSupportStokesInput

end NaturalMeasureStrictBuilder

end Stokes

end
