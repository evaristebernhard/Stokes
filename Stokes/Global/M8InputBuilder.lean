import Stokes.Global.ArtificialFaceToM8
import Stokes.Global.BoundaryMeasureToM8
import Stokes.Global.BulkMeasureToM8
import Stokes.Global.LocalizedInteriorConstructors
import Stokes.Global.M8CompactSupportStatement
import Stokes.Global.TargetImageToM8

/-!
# M8 input builder

This file is a bookkeeping layer for the M8 Stokes statement.  It collects the
already-built compact-support form data, selected partition, localized interior
fields, measure fields, artificial-face fields, and target-image fields into a
single input record.

No new analytic theorem is proved here.  Hard facts such as measure
localization, boundary chart change of variables, and artificial-face
cancellation remain explicit inputs in the lower-level records.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section M8InputBuilder

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

/--
Natural builder input for the M8 Stokes wrappers.

The target-image input determines the M8 boundary-piece family.  The
measure-localization and artificial-face packages are then indexed by that same
family, so the downstream `M8GlobalStokesInput` record can be produced without
manually restating the field equalities.
-/
structure M8InputBuilderData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b) where
  /-- Compactly supported smooth input form. -/
  formData : CompactlySupportedSmoothFormData I omega
  /-- Explicit oriented boundary-chart atlas data. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Selected partition of unity and selected interior boxes. -/
  selectedPartition : SelectedBoxPartitionOfUnity I omega
  /-- The selected partition is controlled by the compact form-support set. -/
  selectedPartition_supportSet :
    selectedPartition.K = formData.supportSet
  /-- Boundary target-image and assembly data in M8 shape. -/
  targetImageInput :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece
  /-- Localized partition-of-unity interior fields. -/
  localizedInterior :
    LocalizedInteriorM8Fields I omega selectedPartition
  /-- Measure-localization fields indexed by the target-image family. -/
  measureLocalization :
    M8MeasureLocalizationData I omega selectedPartition
      targetImageInput.targetImages
  /-- The measure package uses the localized interior family recorded above. -/
  measure_localizedInterior :
    measureLocalization.localizedInterior =
      localizedInterior.localizedInterior
  /-- The target-image assembly boundary term is the measure boundary term. -/
  measureLocalization_boundaryTerm :
    targetImageInput.assembly.boundaryPartitionTerm =
      measureLocalization.boundaryPartitionTerm
  /-- Artificial-face cancellation fields indexed by the same M8 data. -/
  artificial :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImageInput.targetImages measureLocalization

namespace M8InputBuilderData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/-- The M8 target-image family determined by the builder. -/
abbrev targetImages
    (D : M8InputBuilderData I omega BoundaryPiece) :
    BoundaryPieceFamilyInput I omega M BoundaryPiece :=
  D.targetImageInput.targetImages

/-- Measure-resolution package for the compact-support-facing M8 wrapper. -/
def toMeasureResolved
    (D : M8InputBuilderData I omega BoundaryPiece) :
    M8CompactSupportMeasureResolvedData I omega D.selectedPartition
      D.targetImages where
  measureLocalization := D.measureLocalization

/-- Artificial-face resolution package for the compact-support-facing wrapper. -/
def toArtificialFaceResolvedData
    (D : M8InputBuilderData I omega BoundaryPiece) :
    M8CompactSupportArtificialFaceResolvedData I omega D.selectedPartition
      D.targetImages D.toMeasureResolved where
  artificialFaces := D.artificial.artificialFaces
  artificialFaces_active := D.artificial.artificialFaces_active
  artificialFaces_pieces := D.artificial.artificialFaces_pieces
  artificialFaces_term := D.artificial.artificialFaces_term

/-- Boundary-target resolution package for the compact-support-facing wrapper. -/
def toBoundaryTargetResolvedData
    [IsManifold I 1 M]
    (D : M8InputBuilderData I omega BoundaryPiece) :
    M8CompactSupportBoundaryTargetResolvedData I omega D.formData
      D.selectedPartition D.targetImages D.toMeasureResolved where
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  selectedPartition_supportSet := D.selectedPartition_supportSet
  targetImages_active := D.targetImageInput.targetImages_active
  targetImages_source_mem := D.targetImageInput.targetImages_source_mem
  targetImages_boundarySource_mem :=
    D.targetImageInput.targetImages_boundarySource_mem
  targetBoundaryTerm_eq_partition :=
    D.targetImageInput.targetBoundaryTerm_eq_measureLocalization
      D.measureLocalization D.measureLocalization_boundaryTerm

/-- Convert the builder directly to the existing global M8 input. -/
def toM8GlobalStokesInput
    [IsManifold I 1 M]
    (D : M8InputBuilderData I omega BoundaryPiece) :
    M8GlobalStokesInput I omega BoundaryPiece where
  formData := D.formData
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  selectedPartition := D.selectedPartition
  selectedPartition_supportSet := D.selectedPartition_supportSet
  targetImages := D.targetImages
  targetImages_active := D.targetImageInput.targetImages_active
  measureLocalization := D.measureLocalization
  artificialFaces := D.artificial.artificialFaces
  artificialFaces_active := D.artificial.artificialFaces_active
  artificialFaces_pieces := D.artificial.artificialFaces_pieces
  artificialFaces_term := D.artificial.artificialFaces_term
  targetImages_source_mem := D.targetImageInput.targetImages_source_mem
  targetImages_boundarySource_mem :=
    D.targetImageInput.targetImages_boundarySource_mem
  targetBoundaryTerm_eq_partition :=
    D.targetImageInput.targetBoundaryTerm_eq_measureLocalization
      D.measureLocalization D.measureLocalization_boundaryTerm

/-- Convert the builder to the compact-support-facing M8 input. -/
def toM8CompactSupportStokesInput
    [IsManifold I 1 M]
    (D : M8InputBuilderData I omega BoundaryPiece) :
    M8CompactSupportStokesInput I omega BoundaryPiece where
  formData := D.formData
  selectedPartition := D.selectedPartition
  targetImages := D.targetImages
  measureResolved := D.toMeasureResolved
  artificialFaceResolved := D.toArtificialFaceResolvedData
  boundaryTargetResolved := D.toBoundaryTargetResolvedData

@[simp]
theorem toMeasureResolved_measureLocalization
    (D : M8InputBuilderData I omega BoundaryPiece) :
    D.toMeasureResolved.measureLocalization = D.measureLocalization :=
  rfl

@[simp]
theorem toArtificialFaceResolvedData_artificialFaces
    (D : M8InputBuilderData I omega BoundaryPiece) :
    D.toArtificialFaceResolvedData.artificialFaces =
      D.artificial.artificialFaces :=
  rfl

@[simp]
theorem toM8GlobalStokesInput_formData
    [IsManifold I 1 M]
    (D : M8InputBuilderData I omega BoundaryPiece) :
    D.toM8GlobalStokesInput.formData = D.formData :=
  rfl

@[simp]
theorem toM8GlobalStokesInput_selectedPartition
    [IsManifold I 1 M]
    (D : M8InputBuilderData I omega BoundaryPiece) :
    D.toM8GlobalStokesInput.selectedPartition = D.selectedPartition :=
  rfl

@[simp]
theorem toM8GlobalStokesInput_targetImages
    [IsManifold I 1 M]
    (D : M8InputBuilderData I omega BoundaryPiece) :
    D.toM8GlobalStokesInput.targetImages = D.targetImages :=
  rfl

@[simp]
theorem toM8GlobalStokesInput_measureLocalization
    [IsManifold I 1 M]
    (D : M8InputBuilderData I omega BoundaryPiece) :
    D.toM8GlobalStokesInput.measureLocalization =
      D.measureLocalization :=
  rfl

@[simp]
theorem toM8CompactSupportStokesInput_measureLocalization
    [IsManifold I 1 M]
    (D : M8InputBuilderData I omega BoundaryPiece) :
    D.toM8CompactSupportStokesInput.measureResolved.measureLocalization =
      D.measureLocalization :=
  rfl

/--
Constructor from separated bulk and boundary measure fields.

This is the main convenience spelling for later workers: bulk localization and
boundary localization can be built independently, then combined here before the
full M8 input is emitted.
-/
def ofBulkBoundaryFields
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
    (bulk :
      M8BulkMeasureFields I omega selectedPartition
        targetImageInput.targetImages)
    (boundary :
      M8BoundaryMeasureData I omega selectedPartition
        targetImageInput.targetImages)
    (hlocalized :
      bulk.localizedInterior = localizedInterior.localizedInterior)
    (hboundaryTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        boundary.boundaryPartitionTerm)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
        targetImageInput.targetImages
        (bulk.toM8MeasureLocalizationData boundary.boundaryPartitionTerm
          boundary.globalBoundaryIntegral boundary.boundaryMeasureIntegral
          boundary.globalBoundaryIntegral_eq_boundaryMeasureIntegral
          boundary.boundaryMeasureIntegral_eq_partitionSum)) :
    M8InputBuilderData I omega BoundaryPiece where
  formData := formData
  orientedBoundaryAtlas := orientedBoundaryAtlas
  selectedPartition := selectedPartition
  selectedPartition_supportSet := selectedPartition_supportSet
  targetImageInput := targetImageInput
  localizedInterior := localizedInterior
  measureLocalization :=
    bulk.toM8MeasureLocalizationData boundary.boundaryPartitionTerm
      boundary.globalBoundaryIntegral boundary.boundaryMeasureIntegral
      boundary.globalBoundaryIntegral_eq_boundaryMeasureIntegral
      boundary.boundaryMeasureIntegral_eq_partitionSum
  measure_localizedInterior := hlocalized
  measureLocalization_boundaryTerm := hboundaryTerm
  artificial := artificial

@[simp]
theorem ofBulkBoundaryFields_measureLocalization
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
    (bulk :
      M8BulkMeasureFields I omega selectedPartition
        targetImageInput.targetImages)
    (boundary :
      M8BoundaryMeasureData I omega selectedPartition
        targetImageInput.targetImages)
    (hlocalized :
      bulk.localizedInterior = localizedInterior.localizedInterior)
    (hboundaryTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        boundary.boundaryPartitionTerm)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
        targetImageInput.targetImages
        (bulk.toM8MeasureLocalizationData boundary.boundaryPartitionTerm
          boundary.globalBoundaryIntegral boundary.boundaryMeasureIntegral
          boundary.globalBoundaryIntegral_eq_boundaryMeasureIntegral
          boundary.boundaryMeasureIntegral_eq_partitionSum)) :
    (ofBulkBoundaryFields (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece)
      formData orientedBoundaryAtlas selectedPartition
      selectedPartition_supportSet targetImageInput localizedInterior
      bulk boundary hlocalized hboundaryTerm artificial).measureLocalization =
        bulk.toM8MeasureLocalizationData boundary.boundaryPartitionTerm
          boundary.globalBoundaryIntegral boundary.boundaryMeasureIntegral
          boundary.globalBoundaryIntegral_eq_boundaryMeasureIntegral
          boundary.boundaryMeasureIntegral_eq_partitionSum :=
  rfl

@[simp]
theorem ofBulkBoundaryFields_targetImages
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
    (bulk :
      M8BulkMeasureFields I omega selectedPartition
        targetImageInput.targetImages)
    (boundary :
      M8BoundaryMeasureData I omega selectedPartition
        targetImageInput.targetImages)
    (hlocalized :
      bulk.localizedInterior = localizedInterior.localizedInterior)
    (hboundaryTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        boundary.boundaryPartitionTerm)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
        targetImageInput.targetImages
        (bulk.toM8MeasureLocalizationData boundary.boundaryPartitionTerm
          boundary.globalBoundaryIntegral boundary.boundaryMeasureIntegral
          boundary.globalBoundaryIntegral_eq_boundaryMeasureIntegral
          boundary.boundaryMeasureIntegral_eq_partitionSum)) :
    (ofBulkBoundaryFields (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece)
      formData orientedBoundaryAtlas selectedPartition
      selectedPartition_supportSet targetImageInput localizedInterior
      bulk boundary hlocalized hboundaryTerm artificial).targetImages =
        targetImageInput.targetImages :=
  rfl

/-- M8 Stokes, exposed from the builder input. -/
theorem stokes
    [IsManifold I 1 M]
    (D : M8InputBuilderData I omega BoundaryPiece) :
    D.measureLocalization.bulkMeasureIntegral =
      D.measureLocalization.boundaryMeasureIntegral := by
  simpa [toM8GlobalStokesInput] using
    m8GlobalStokes (D.toM8GlobalStokesInput)

/-- Represented-integral M8 Stokes, exposed from the builder input. -/
theorem represented_stokes
    [IsManifold I 1 M]
    (D : M8InputBuilderData I omega BoundaryPiece) :
    D.measureLocalization.globalBulkIntegral =
      D.measureLocalization.globalBoundaryIntegral := by
  simpa [toM8GlobalStokesInput] using
    m8GlobalStokes_represented (D.toM8GlobalStokesInput)

end M8InputBuilderData

end M8InputBuilder

end Stokes

end
