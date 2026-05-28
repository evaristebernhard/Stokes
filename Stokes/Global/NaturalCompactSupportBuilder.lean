import Stokes.Global.M8InputBuilder
import Stokes.Global.NaturalCompactSupportStokesStatement
import Stokes.Global.TargetImageResolvedToM8Input

/-!
# Natural compact-support builder

This file is a small adaptor layer for
`NaturalCompactSupportStokesInput`.  It keeps the analytic and geometric work in
the existing resolved packages, then bundles them into the natural
compact-support statement.

The main entry points are:

* `NaturalCompactSupportBuilderData.toNaturalCompactSupportStokesInput`;
* `M8InputBuilderData.toNaturalCompactSupportBuilderData`, for callers that
  already assembled an M8 builder and additionally have the compact-support
  measure package;
* constructors from resolved target-image data and resolved artificial-face
  data.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportBuilder

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]

/--
Builder data for the natural compact-support statement.

The measure field is the compact-support package.  The localized-interior,
target-image, and artificial-face fields are kept visible because many
upstream constructors naturally produce them separately before the final
compact-support statement is assembled.
-/
structure NaturalCompactSupportBuilderData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (μ : Measure α) [IsFiniteMeasureOnCompacts μ] where
  /-- Compactly supported smooth input form. -/
  formData : CompactlySupportedSmoothFormData I omega
  /-- Explicit oriented boundary-chart atlas data. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Selected partition of unity and selected chart boxes. -/
  selectedPartition : SelectedBoxPartitionOfUnity I omega
  /-- The selected partition is controlled by the compact support set. -/
  selectedPartition_supportSet :
    selectedPartition.K = formData.supportSet
  /-- Boundary target-image and assembly data in M8 shape. -/
  targetImageInput :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece
  /-- Localized partition-of-unity interior fields produced upstream. -/
  localizedInterior :
    LocalizedInteriorM8Fields I omega selectedPartition
  /-- Compact-support measure localization resolved to the M8 shape. -/
  measure :
    CompactSupportToM8MeasureData
      (α := α) I omega selectedPartition
      targetImageInput.targetImages μ
  /-- The compact-support measure package uses the recorded localized family. -/
  measure_localizedInterior :
    measure.toM8MeasureLocalizationData.localizedInterior =
      localizedInterior.localizedInterior
  /--
  The target-image assembly boundary term is the boundary partition term used
  by compact-support measure localization.
  -/
  target_boundaryPartitionTerm :
    targetImageInput.assembly.boundaryPartitionTerm =
      measure.boundaryPartitionTerm
  /-- Resolved artificial-face cancellation in the M8 shape. -/
  artificial :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImageInput.targetImages measure.toM8MeasureLocalizationData

namespace NaturalCompactSupportBuilderData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/-- The target-image family determined by the builder. -/
abbrev targetImages
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    BoundaryPieceFamilyInput I omega M BoundaryPiece :=
  D.targetImageInput.targetImages

/-- Forget the builder-only localized-interior handle and expose the natural input. -/
def toNaturalCompactSupportStokesInput
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ where
  formData := D.formData
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  selectedPartition := D.selectedPartition
  selectedPartition_supportSet := D.selectedPartition_supportSet
  targetImageInput := D.targetImageInput
  measure := D.measure
  target_boundaryPartitionTerm := D.target_boundaryPartitionTerm
  artificial := D.artificial

/--
Expose the same data as the existing M8 input builder.

This is useful for downstream code that wants to reuse M8 projections while
building from compact-support measure localization.
-/
def toM8InputBuilderData
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    M8InputBuilderData I omega BoundaryPiece where
  formData := D.formData
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  selectedPartition := D.selectedPartition
  selectedPartition_supportSet := D.selectedPartition_supportSet
  targetImageInput := D.targetImageInput
  localizedInterior := D.localizedInterior
  measureLocalization := D.measure.toM8MeasureLocalizationData
  measure_localizedInterior := D.measure_localizedInterior
  measureLocalization_boundaryTerm := by
    simpa [CompactSupportToM8MeasureData.toM8MeasureLocalizationData] using
      D.target_boundaryPartitionTerm
  artificial := D.artificial

@[simp]
theorem toNaturalCompactSupportStokesInput_formData
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    D.toNaturalCompactSupportStokesInput.formData = D.formData :=
  rfl

@[simp]
theorem toNaturalCompactSupportStokesInput_selectedPartition
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    D.toNaturalCompactSupportStokesInput.selectedPartition =
      D.selectedPartition :=
  rfl

@[simp]
theorem toNaturalCompactSupportStokesInput_measure
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    D.toNaturalCompactSupportStokesInput.measure = D.measure :=
  rfl

@[simp]
theorem toNaturalCompactSupportStokesInput_targetImageInput
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    D.toNaturalCompactSupportStokesInput.targetImageInput =
      D.targetImageInput :=
  rfl

@[simp]
theorem toNaturalCompactSupportStokesInput_artificial
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    D.toNaturalCompactSupportStokesInput.artificial = D.artificial :=
  rfl

@[simp]
theorem toM8InputBuilderData_targetImageInput
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    D.toM8InputBuilderData.targetImageInput = D.targetImageInput :=
  rfl

@[simp]
theorem toM8InputBuilderData_measureLocalization
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    D.toM8InputBuilderData.measureLocalization =
      D.measure.toM8MeasureLocalizationData :=
  rfl

@[simp]
theorem toM8InputBuilderData_localizedInterior
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    D.toM8InputBuilderData.localizedInterior = D.localizedInterior :=
  rfl

@[simp]
theorem toM8InputBuilderData_artificial
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    D.toM8InputBuilderData.artificial = D.artificial :=
  rfl

/-- Direct constructor from the resolved packages already used by the builder. -/
def ofPackages
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
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
        targetImageInput.targetImages measure.toM8MeasureLocalizationData) :
    NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ where
  formData := formData
  orientedBoundaryAtlas := orientedBoundaryAtlas
  selectedPartition := selectedPartition
  selectedPartition_supportSet := selectedPartition_supportSet
  targetImageInput := targetImageInput
  localizedInterior := localizedInterior
  measure := measure
  measure_localizedInterior := measure_localizedInterior
  target_boundaryPartitionTerm := target_boundaryPartitionTerm
  artificial := artificial

@[simp]
theorem ofPackages_measure
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
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
        targetImageInput.targetImages measure.toM8MeasureLocalizationData) :
    (ofPackages (α := α) (μ := μ) (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece)
      formData orientedBoundaryAtlas selectedPartition
      selectedPartition_supportSet targetImageInput localizedInterior measure
      measure_localizedInterior target_boundaryPartitionTerm artificial).measure =
        measure :=
  rfl

/-- Constructor from resolved target-image input plus an M8 artificial package. -/
def ofResolvedTargetImage
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageResolved :
      M8TargetImageResolvedInput I omega selectedPartition
        orientedBoundaryAtlas BoundaryPiece)
    (localizedInterior :
      LocalizedInteriorM8Fields I omega selectedPartition)
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega selectedPartition
        targetImageResolved.toM8TargetImageInput.targetImages μ)
    (measure_localizedInterior :
      measure.toM8MeasureLocalizationData.localizedInterior =
        localizedInterior.localizedInterior)
    (target_boundaryPartitionTerm :
      targetImageResolved.boundaryPartitionTerm =
        measure.boundaryPartitionTerm)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
        targetImageResolved.toM8TargetImageInput.targetImages
        measure.toM8MeasureLocalizationData) :
    NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ :=
  ofPackages (α := α) (μ := μ) (I := I) (omega := omega)
    (BoundaryPiece := BoundaryPiece)
    formData orientedBoundaryAtlas selectedPartition
    selectedPartition_supportSet targetImageResolved.toM8TargetImageInput
    localizedInterior measure measure_localizedInterior
    (by
      simpa [M8TargetImageResolvedInput.toM8TargetImageInput,
        M8TargetImageResolvedInput.toAssemblyInput] using
        target_boundaryPartitionTerm)
    artificial

@[simp]
theorem ofResolvedTargetImage_targetImageInput
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageResolved :
      M8TargetImageResolvedInput I omega selectedPartition
        orientedBoundaryAtlas BoundaryPiece)
    (localizedInterior :
      LocalizedInteriorM8Fields I omega selectedPartition)
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega selectedPartition
        targetImageResolved.toM8TargetImageInput.targetImages μ)
    (measure_localizedInterior :
      measure.toM8MeasureLocalizationData.localizedInterior =
        localizedInterior.localizedInterior)
    (target_boundaryPartitionTerm :
      targetImageResolved.boundaryPartitionTerm =
        measure.boundaryPartitionTerm)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
        targetImageResolved.toM8TargetImageInput.targetImages
        measure.toM8MeasureLocalizationData) :
    (ofResolvedTargetImage (α := α) (μ := μ) (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece)
      formData orientedBoundaryAtlas selectedPartition
      selectedPartition_supportSet targetImageResolved localizedInterior
      measure measure_localizedInterior target_boundaryPartitionTerm
      artificial).targetImageInput =
        targetImageResolved.toM8TargetImageInput :=
  rfl

/--
Constructor from resolved target-image data and raw resolved artificial-face
data.
-/
def ofResolvedTargetImageAndArtificialFaces
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageResolved :
      M8TargetImageResolvedInput I omega selectedPartition
        orientedBoundaryAtlas BoundaryPiece)
    (localizedInterior :
      LocalizedInteriorM8Fields I omega selectedPartition)
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega selectedPartition
        targetImageResolved.toM8TargetImageInput.targetImages μ)
    (measure_localizedInterior :
      measure.toM8MeasureLocalizationData.localizedInterior =
        localizedInterior.localizedInterior)
    (target_boundaryPartitionTerm :
      targetImageResolved.boundaryPartitionTerm =
        measure.boundaryPartitionTerm)
    (artificialFaces : ArtificialFaceResolvedData M Unit)
    (artificialFaces_active :
      artificialFaces.activeCharts = selectedPartition.active)
    (artificialFaces_pieces :
      artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (artificialFaces_term :
      artificialFaces.interiorBoundaryTerm =
        measure.toM8MeasureLocalizationData.interiorBoundaryTerm) :
    NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ :=
  ofResolvedTargetImage (α := α) (μ := μ) (I := I) (omega := omega)
    (BoundaryPiece := BoundaryPiece)
    formData orientedBoundaryAtlas selectedPartition
    selectedPartition_supportSet targetImageResolved localizedInterior
    measure measure_localizedInterior target_boundaryPartitionTerm
    (M8ArtificialFaceFields.ofResolved
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      (selectedPartition := selectedPartition)
      (targetImages := targetImageResolved.toM8TargetImageInput.targetImages)
      (measureLocalization := measure.toM8MeasureLocalizationData)
      artificialFaces artificialFaces_active artificialFaces_pieces
      artificialFaces_term)

/-- Natural compact-support Stokes, exposed from the builder input. -/
theorem stokes
    [IsManifold I 1 M]
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    D.measure.toM8MeasureLocalizationData.bulkMeasureIntegral =
      D.measure.toM8MeasureLocalizationData.boundaryMeasureIntegral :=
  D.toNaturalCompactSupportStokesInput.stokes

/-- Natural compact-support Stokes in compact-support measure field names. -/
theorem stokes_compactSupportFields
    [IsManifold I 1 M]
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    D.measure.globalBulkIntegral =
      D.measure.boundary.boundaryMeasureIntegral :=
  D.toNaturalCompactSupportStokesInput.stokes_compactSupportFields

end NaturalCompactSupportBuilderData

namespace M8InputBuilderData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/--
Adapt an existing M8 builder to the natural compact-support builder, once the
M8 measure-localization record has been identified with a compact-support
measure package.
-/
def toNaturalCompactSupportBuilderData
    (D : M8InputBuilderData I omega BoundaryPiece)
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega D.selectedPartition D.targetImages μ)
    (hmeasure :
      D.measureLocalization = measure.toM8MeasureLocalizationData) :
    NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ where
  formData := D.formData
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  selectedPartition := D.selectedPartition
  selectedPartition_supportSet := D.selectedPartition_supportSet
  targetImageInput := D.targetImageInput
  localizedInterior := D.localizedInterior
  measure := measure
  measure_localizedInterior := by
    simpa [hmeasure] using D.measure_localizedInterior
  target_boundaryPartitionTerm := by
    simpa [hmeasure,
      CompactSupportToM8MeasureData.toM8MeasureLocalizationData] using
      D.measureLocalization_boundaryTerm
  artificial :=
    { artificialFaces := D.artificial.artificialFaces
      artificialFaces_active := D.artificial.artificialFaces_active
      artificialFaces_pieces := D.artificial.artificialFaces_pieces
      artificialFaces_term := by
        simpa [hmeasure] using D.artificial.artificialFaces_term }

/--
Adapt an existing M8 builder directly to the natural compact-support input,
once compact-support measure localization is supplied.
-/
def toNaturalCompactSupportStokesInput
    (D : M8InputBuilderData I omega BoundaryPiece)
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega D.selectedPartition D.targetImages μ)
    (hmeasure :
      D.measureLocalization = measure.toM8MeasureLocalizationData) :
    NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ :=
  (D.toNaturalCompactSupportBuilderData
    (α := α) (μ := μ) measure hmeasure)
    |>.toNaturalCompactSupportStokesInput

@[simp]
theorem toNaturalCompactSupportBuilderData_measure
    (D : M8InputBuilderData I omega BoundaryPiece)
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega D.selectedPartition D.targetImages μ)
    (hmeasure :
      D.measureLocalization = measure.toM8MeasureLocalizationData) :
    (D.toNaturalCompactSupportBuilderData
      (α := α) (μ := μ) measure hmeasure).measure = measure :=
  rfl

@[simp]
theorem toNaturalCompactSupportBuilderData_targetImageInput
    (D : M8InputBuilderData I omega BoundaryPiece)
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega D.selectedPartition D.targetImages μ)
    (hmeasure :
      D.measureLocalization = measure.toM8MeasureLocalizationData) :
    (D.toNaturalCompactSupportBuilderData
      (α := α) (μ := μ) measure hmeasure).targetImageInput =
        D.targetImageInput :=
  rfl

@[simp]
theorem toNaturalCompactSupportBuilderData_localizedInterior
    (D : M8InputBuilderData I omega BoundaryPiece)
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega D.selectedPartition D.targetImages μ)
    (hmeasure :
      D.measureLocalization = measure.toM8MeasureLocalizationData) :
    (D.toNaturalCompactSupportBuilderData
      (α := α) (μ := μ) measure hmeasure).localizedInterior =
        D.localizedInterior :=
  rfl

@[simp]
theorem toNaturalCompactSupportStokesInput_measure
    (D : M8InputBuilderData I omega BoundaryPiece)
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega D.selectedPartition D.targetImages μ)
    (hmeasure :
      D.measureLocalization = measure.toM8MeasureLocalizationData) :
    (D.toNaturalCompactSupportStokesInput
      (α := α) (μ := μ) measure hmeasure).measure = measure :=
  rfl

/-- Compact-support Stokes directly from an M8 builder plus its measure package. -/
theorem naturalCompactSupportStokes
    [IsManifold I 1 M]
    (D : M8InputBuilderData I omega BoundaryPiece)
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega D.selectedPartition D.targetImages μ)
    (hmeasure :
      D.measureLocalization = measure.toM8MeasureLocalizationData) :
    measure.toM8MeasureLocalizationData.bulkMeasureIntegral =
      measure.toM8MeasureLocalizationData.boundaryMeasureIntegral :=
  (D.toNaturalCompactSupportBuilderData
    (α := α) (μ := μ) measure hmeasure).stokes

/--
Compact-support Stokes in compact-support measure field names, directly from
an M8 builder plus its measure package.
-/
theorem naturalCompactSupportStokes_compactSupportFields
    [IsManifold I 1 M]
    (D : M8InputBuilderData I omega BoundaryPiece)
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega D.selectedPartition D.targetImages μ)
    (hmeasure :
      D.measureLocalization = measure.toM8MeasureLocalizationData) :
    measure.globalBulkIntegral =
      measure.boundary.boundaryMeasureIntegral :=
  (D.toNaturalCompactSupportBuilderData
    (α := α) (μ := μ) measure hmeasure).stokes_compactSupportFields

end M8InputBuilderData

end NaturalCompactSupportBuilder

end Stokes

end
