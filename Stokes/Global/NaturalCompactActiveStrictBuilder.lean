import Stokes.Global.CompactSupportStrictBufferFromActive
import Stokes.Global.NaturalStrictBufferBuilder

/-!
# Natural builders from compact-active strict-buffer alignment

This file is a higher-level adapter for the selected-box alignment route.

`CompactSupportStrictBufferFromActive` proves that compact active boxes, once
aligned with the M8 localized-interior pieces and given strict margins, produce
the strict form-buffer needed to kill artificial faces.  `NaturalStrictBufferBuilder`
then consumes that buffer.  The declarations below compose those two steps.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactActiveStrictBuilder

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

namespace NaturalCompactSupportBuilderData

/--
Natural compact-support builder from compact active boxes plus the explicit
alignment fields that identify them with the M8 localized-interior pieces.
-/
def ofPackagesWithCompactActiveBoxAlignment
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (localizedInterior :
      LocalizedInteriorM8Fields I omega selectedPartition)
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega selectedPartition
        targetImageInput.targetImages μ)
    (measure_localizedInterior :
      measure.toM8MeasureLocalizationData.localizedInterior =
        localizedInterior.localizedInterior)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measure.boundaryPartitionTerm)
    {D : CompactActiveBoxData I omega}
    (alignment :
      CompactActiveBoxStrictBufferAlignment D selectedPartition
        targetImageInput.targetImages measure.toM8MeasureLocalizationData) :
    NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ :=
  ofPackagesWithFormInnerBoxBuffer
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    formData orientedBoundaryAtlas selectedPartition selectedPartition_supportSet
    targetImageInput localizedInterior measure measure_localizedInterior
    target_boundaryPartitionTerm
    alignment.toLocalizedInteriorFormInnerBoxBuffer

@[simp]
theorem ofPackagesWithCompactActiveBoxAlignment_artificial
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (localizedInterior :
      LocalizedInteriorM8Fields I omega selectedPartition)
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega selectedPartition
        targetImageInput.targetImages μ)
    (measure_localizedInterior :
      measure.toM8MeasureLocalizationData.localizedInterior =
        localizedInterior.localizedInterior)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measure.boundaryPartitionTerm)
    {D : CompactActiveBoxData I omega}
    (alignment :
      CompactActiveBoxStrictBufferAlignment D selectedPartition
        targetImageInput.targetImages measure.toM8MeasureLocalizationData) :
    (ofPackagesWithCompactActiveBoxAlignment
      (α := α) (μ := μ) (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece)
      formData orientedBoundaryAtlas selectedPartition selectedPartition_supportSet
      targetImageInput localizedInterior measure measure_localizedInterior
      target_boundaryPartitionTerm alignment).artificial =
        alignment.toLocalizedInteriorFormInnerBoxBuffer.toM8ArtificialFaceFields :=
  rfl

end NaturalCompactSupportBuilderData

namespace NaturalCompactSupportStokesInput

/--
Natural compact-support Stokes input from compact active boxes plus strict
selected-box alignment.
-/
def ofPackagesWithCompactActiveBoxAlignment
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega selectedPartition
        targetImageInput.targetImages μ)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measure.boundaryPartitionTerm)
    {D : CompactActiveBoxData I omega}
    (alignment :
      CompactActiveBoxStrictBufferAlignment D selectedPartition
        targetImageInput.targetImages measure.toM8MeasureLocalizationData) :
    NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ :=
  ofPackagesWithFormInnerBoxBuffer
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    formData orientedBoundaryAtlas selectedPartition selectedPartition_supportSet
    targetImageInput measure target_boundaryPartitionTerm
    alignment.toLocalizedInteriorFormInnerBoxBuffer

@[simp]
theorem ofPackagesWithCompactActiveBoxAlignment_artificial
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega selectedPartition
        targetImageInput.targetImages μ)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measure.boundaryPartitionTerm)
    {D : CompactActiveBoxData I omega}
    (alignment :
      CompactActiveBoxStrictBufferAlignment D selectedPartition
        targetImageInput.targetImages measure.toM8MeasureLocalizationData) :
    (ofPackagesWithCompactActiveBoxAlignment
      (α := α) (μ := μ) (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece)
      formData orientedBoundaryAtlas selectedPartition selectedPartition_supportSet
      targetImageInput measure target_boundaryPartitionTerm alignment).artificial =
        alignment.toLocalizedInteriorFormInnerBoxBuffer.toM8ArtificialFaceFields :=
  rfl

end NaturalCompactSupportStokesInput

namespace M8CompactSupportStokesInput

variable {formData : CompactlySupportedSmoothFormData I omega}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureResolved :
  M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages}

/--
M8 compact-support input from compact active boxes plus strict selected-box
alignment.
-/
def ofCompactActiveBoxAlignment
    (boundaryTargetResolved :
      M8CompactSupportBoundaryTargetResolvedData I omega formData
        selectedPartition targetImages measureResolved)
    {D : CompactActiveBoxData I omega}
    (alignment :
      CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
        measureResolved.measureLocalization) :
    M8CompactSupportStokesInput I omega BoundaryPiece :=
  ofFormInnerBoxBuffer
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    boundaryTargetResolved alignment.toLocalizedInteriorFormInnerBoxBuffer

theorem ofCompactActiveBoxAlignment_artificialFaces
    (boundaryTargetResolved :
      M8CompactSupportBoundaryTargetResolvedData I omega formData
        selectedPartition targetImages measureResolved)
    {D : CompactActiveBoxData I omega}
    (alignment :
      CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
        measureResolved.measureLocalization) :
    (ofCompactActiveBoxAlignment (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece)
      boundaryTargetResolved alignment).artificialFaceResolved.artificialFaces =
        (alignment.toLocalizedInteriorFormInnerBoxBuffer
          |>.toM8ArtificialFaceFields).artificialFaces :=
  rfl

end M8CompactSupportStokesInput

end NaturalCompactActiveStrictBuilder

end Stokes

end
