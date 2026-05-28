import Stokes.Global.CompactSupportStrictBuffer

/-!
# Natural strict-buffer builders

This file is a thin public-facing adapter from strict inner-box buffer data to
the current natural compact-support and M8 compact-support inputs.

The analytic content stays in `CompactSupportStrictBuffer`: a form-buffer or
coefficient-buffer proves that the localized representatives have topological
support in the strict interior of the selected chart boxes.  The declarations
below only remove the manual intermediate conversion through
`CompactSupportBoxBuffer`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalStrictBufferBuilder

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {A : Type a} [TopologicalSpace A] [MeasurableSpace A]
variable [OpensMeasurableSpace A] [T2Space A]
variable {mu : Measure A} [IsFiniteMeasureOnCompacts mu]

namespace NaturalCompactSupportBuilderData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/--
Natural compact-support builder constructor where artificial-face cancellation
is generated directly from strict inner boxes for localized form
representatives.
-/
def ofPackagesWithFormInnerBoxBuffer
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
      CompactSupportToM8MeasureData I omega selectedPartition
        targetImageInput.targetImages mu)
    (measure_localizedInterior :
      measure.toM8MeasureLocalizationData.localizedInterior =
        localizedInterior.localizedInterior)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measure.boundaryPartitionTerm)
    (buffer :
      LocalizedInteriorFormInnerBoxBuffer I omega selectedPartition
        targetImageInput.targetImages measure.toM8MeasureLocalizationData) :
    NaturalCompactSupportBuilderData I omega BoundaryPiece mu :=
  ofPackagesWithCompactSupportBoxBuffer
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    formData orientedBoundaryAtlas selectedPartition
    selectedPartition_supportSet targetImageInput localizedInterior measure
    measure_localizedInterior target_boundaryPartitionTerm
    buffer.toCompactSupportBoxBuffer

@[simp]
theorem ofPackagesWithFormInnerBoxBuffer_artificial
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
      CompactSupportToM8MeasureData I omega selectedPartition
        targetImageInput.targetImages mu)
    (measure_localizedInterior :
      measure.toM8MeasureLocalizationData.localizedInterior =
        localizedInterior.localizedInterior)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measure.boundaryPartitionTerm)
    (buffer :
      LocalizedInteriorFormInnerBoxBuffer I omega selectedPartition
        targetImageInput.targetImages measure.toM8MeasureLocalizationData) :
    (ofPackagesWithFormInnerBoxBuffer
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      formData orientedBoundaryAtlas selectedPartition
      selectedPartition_supportSet targetImageInput localizedInterior measure
      measure_localizedInterior target_boundaryPartitionTerm buffer).artificial =
        buffer.toM8ArtificialFaceFields :=
  rfl

/--
Natural compact-support builder constructor where artificial-face cancellation
is generated directly from strict inner boxes for localized transition
coefficients.
-/
def ofPackagesWithCoefficientInnerBoxBuffer
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
      CompactSupportToM8MeasureData I omega selectedPartition
        targetImageInput.targetImages mu)
    (measure_localizedInterior :
      measure.toM8MeasureLocalizationData.localizedInterior =
        localizedInterior.localizedInterior)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measure.boundaryPartitionTerm)
    (buffer :
      LocalizedInteriorCoefficientInnerBoxBuffer I omega selectedPartition
        targetImageInput.targetImages measure.toM8MeasureLocalizationData) :
    NaturalCompactSupportBuilderData I omega BoundaryPiece mu :=
  ofPackagesWithCompactSupportBoxBuffer
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    formData orientedBoundaryAtlas selectedPartition
    selectedPartition_supportSet targetImageInput localizedInterior measure
    measure_localizedInterior target_boundaryPartitionTerm
    buffer.toCompactSupportBoxBuffer

@[simp]
theorem ofPackagesWithCoefficientInnerBoxBuffer_artificial
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
      CompactSupportToM8MeasureData I omega selectedPartition
        targetImageInput.targetImages mu)
    (measure_localizedInterior :
      measure.toM8MeasureLocalizationData.localizedInterior =
        localizedInterior.localizedInterior)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measure.boundaryPartitionTerm)
    (buffer :
      LocalizedInteriorCoefficientInnerBoxBuffer I omega selectedPartition
        targetImageInput.targetImages measure.toM8MeasureLocalizationData) :
    (ofPackagesWithCoefficientInnerBoxBuffer
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      formData orientedBoundaryAtlas selectedPartition
      selectedPartition_supportSet targetImageInput localizedInterior measure
      measure_localizedInterior target_boundaryPartitionTerm buffer).artificial =
        buffer.toM8ArtificialFaceFields :=
  rfl

end NaturalCompactSupportBuilderData

namespace NaturalCompactSupportStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/--
Natural compact-support Stokes input with artificial-face cancellation generated
directly from strict inner boxes for localized form representatives.
-/
def ofPackagesWithFormInnerBoxBuffer
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (measure :
      CompactSupportToM8MeasureData I omega selectedPartition
        targetImageInput.targetImages mu)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measure.boundaryPartitionTerm)
    (buffer :
      LocalizedInteriorFormInnerBoxBuffer I omega selectedPartition
        targetImageInput.targetImages measure.toM8MeasureLocalizationData) :
    NaturalCompactSupportStokesInput I omega BoundaryPiece mu where
  formData := formData
  orientedBoundaryAtlas := orientedBoundaryAtlas
  selectedPartition := selectedPartition
  selectedPartition_supportSet := selectedPartition_supportSet
  targetImageInput := targetImageInput
  measure := measure
  target_boundaryPartitionTerm := target_boundaryPartitionTerm
  artificial := buffer.toM8ArtificialFaceFields

@[simp]
theorem ofPackagesWithFormInnerBoxBuffer_artificial
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (measure :
      CompactSupportToM8MeasureData I omega selectedPartition
        targetImageInput.targetImages mu)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measure.boundaryPartitionTerm)
    (buffer :
      LocalizedInteriorFormInnerBoxBuffer I omega selectedPartition
        targetImageInput.targetImages measure.toM8MeasureLocalizationData) :
    (ofPackagesWithFormInnerBoxBuffer
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      formData orientedBoundaryAtlas selectedPartition
      selectedPartition_supportSet targetImageInput measure
      target_boundaryPartitionTerm buffer).artificial =
        buffer.toM8ArtificialFaceFields :=
  rfl

/--
Natural compact-support Stokes input with artificial-face cancellation generated
directly from strict inner boxes for localized transition coefficients.
-/
def ofPackagesWithCoefficientInnerBoxBuffer
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (measure :
      CompactSupportToM8MeasureData I omega selectedPartition
        targetImageInput.targetImages mu)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measure.boundaryPartitionTerm)
    (buffer :
      LocalizedInteriorCoefficientInnerBoxBuffer I omega selectedPartition
        targetImageInput.targetImages measure.toM8MeasureLocalizationData) :
    NaturalCompactSupportStokesInput I omega BoundaryPiece mu where
  formData := formData
  orientedBoundaryAtlas := orientedBoundaryAtlas
  selectedPartition := selectedPartition
  selectedPartition_supportSet := selectedPartition_supportSet
  targetImageInput := targetImageInput
  measure := measure
  target_boundaryPartitionTerm := target_boundaryPartitionTerm
  artificial := buffer.toM8ArtificialFaceFields

@[simp]
theorem ofPackagesWithCoefficientInnerBoxBuffer_artificial
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (measure :
      CompactSupportToM8MeasureData I omega selectedPartition
        targetImageInput.targetImages mu)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measure.boundaryPartitionTerm)
    (buffer :
      LocalizedInteriorCoefficientInnerBoxBuffer I omega selectedPartition
        targetImageInput.targetImages measure.toM8MeasureLocalizationData) :
    (ofPackagesWithCoefficientInnerBoxBuffer
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      formData orientedBoundaryAtlas selectedPartition
      selectedPartition_supportSet targetImageInput measure
      target_boundaryPartitionTerm buffer).artificial =
        buffer.toM8ArtificialFaceFields :=
  rfl

end NaturalCompactSupportStokesInput

namespace M8CompactSupportStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {formData : CompactlySupportedSmoothFormData I omega}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureResolved :
  M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages}

/--
M8 compact-support input with artificial-face data generated directly from
strict inner boxes for localized form representatives.
-/
def ofFormInnerBoxBuffer
    (boundaryTargetResolved :
      M8CompactSupportBoundaryTargetResolvedData I omega formData
        selectedPartition targetImages measureResolved)
    (buffer :
      LocalizedInteriorFormInnerBoxBuffer I omega selectedPartition
        targetImages measureResolved.measureLocalization) :
    M8CompactSupportStokesInput I omega BoundaryPiece where
  formData := formData
  selectedPartition := selectedPartition
  targetImages := targetImages
  measureResolved := measureResolved
  artificialFaceResolved := buffer.toCompactSupportBoxBuffer
    |>.toCompactSupportArtificialFaceResolvedData
  boundaryTargetResolved := boundaryTargetResolved

@[simp]
theorem ofFormInnerBoxBuffer_artificialFaces
    (boundaryTargetResolved :
      M8CompactSupportBoundaryTargetResolvedData I omega formData
        selectedPartition targetImages measureResolved)
    (buffer :
      LocalizedInteriorFormInnerBoxBuffer I omega selectedPartition
        targetImages measureResolved.measureLocalization) :
    (ofFormInnerBoxBuffer (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece)
      boundaryTargetResolved buffer).artificialFaceResolved.artificialFaces =
        buffer.toM8ArtificialFaceFields.artificialFaces :=
  rfl

/--
M8 compact-support input with artificial-face data generated directly from
strict inner boxes for localized transition coefficients.
-/
def ofCoefficientInnerBoxBuffer
    (boundaryTargetResolved :
      M8CompactSupportBoundaryTargetResolvedData I omega formData
        selectedPartition targetImages measureResolved)
    (buffer :
      LocalizedInteriorCoefficientInnerBoxBuffer I omega selectedPartition
        targetImages measureResolved.measureLocalization) :
    M8CompactSupportStokesInput I omega BoundaryPiece where
  formData := formData
  selectedPartition := selectedPartition
  targetImages := targetImages
  measureResolved := measureResolved
  artificialFaceResolved := buffer.toCompactSupportBoxBuffer
    |>.toCompactSupportArtificialFaceResolvedData
  boundaryTargetResolved := boundaryTargetResolved

@[simp]
theorem ofCoefficientInnerBoxBuffer_artificialFaces
    (boundaryTargetResolved :
      M8CompactSupportBoundaryTargetResolvedData I omega formData
        selectedPartition targetImages measureResolved)
    (buffer :
      LocalizedInteriorCoefficientInnerBoxBuffer I omega selectedPartition
        targetImages measureResolved.measureLocalization) :
    (ofCoefficientInnerBoxBuffer (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece)
      boundaryTargetResolved buffer).artificialFaceResolved.artificialFaces =
        buffer.toM8ArtificialFaceFields.artificialFaces :=
  rfl

end M8CompactSupportStokesInput

end NaturalStrictBufferBuilder

end Stokes

end
