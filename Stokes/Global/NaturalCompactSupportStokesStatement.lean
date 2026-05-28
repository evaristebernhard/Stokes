import Stokes.Global.M8CompactSupportStatement
import Stokes.Global.CompactSupportToM8Measure
import Stokes.Global.ArtificialFaceToM8
import Stokes.Global.TargetImageToM8

/-!
# Natural compact-support Stokes statement

This file is a user-facing wrapper around `m8CompactSupportStokes`.

The theorem here still has conditional inputs, but those inputs are the current
resolved packages rather than the raw M8 fields:

* compact-support bulk/boundary measure localization;
* resolved artificial-face cancellation;
* boundary target-image data from the selected boundary chart package.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportStokesStatement

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]

/--
Compact-support Stokes input in the most natural package shape currently
available in the project.

Compared with `M8CompactSupportStokesInput`, this record does not ask callers
to provide raw M8 measure/artificial/target fields.  Instead, it consumes the
resolved constructors produced by the compact-support measure, artificial-face,
and target-image layers.
-/
structure NaturalCompactSupportStokesInput {n : Nat}
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
  /-- Boundary target-image data resolved from selected boundary charts. -/
  targetImageInput :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece
  /-- Compact-support measure localization resolved to the M8 shape. -/
  measure :
    CompactSupportToM8MeasureData
      (α := α) I omega selectedPartition
      targetImageInput.targetImages μ
  /--
  The boundary partition term in the target-image assembly is the boundary
  partition term used by measure localization.
  -/
  target_boundaryPartitionTerm :
    targetImageInput.assembly.boundaryPartitionTerm =
      measure.boundaryPartitionTerm
  /-- Resolved artificial-face cancellation in the M8 shape. -/
  artificial :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImageInput.targetImages measure.toM8MeasureLocalizationData

namespace NaturalCompactSupportStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/-- Expose the M8 measure-resolved package. -/
def toMeasureResolved
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    M8CompactSupportMeasureResolvedData I omega D.selectedPartition
      D.targetImageInput.targetImages where
  measureLocalization := D.measure.toM8MeasureLocalizationData

@[simp]
theorem toMeasureResolved_measureLocalization
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.toMeasureResolved.measureLocalization =
      D.measure.toM8MeasureLocalizationData :=
  rfl

/-- Expose the M8 artificial-face resolved package. -/
def toArtificialFaceResolved
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    M8CompactSupportArtificialFaceResolvedData I omega D.selectedPartition
      D.targetImageInput.targetImages D.toMeasureResolved where
  artificialFaces := D.artificial.artificialFaces
  artificialFaces_active := D.artificial.artificialFaces_active
  artificialFaces_pieces := D.artificial.artificialFaces_pieces
  artificialFaces_term := D.artificial.artificialFaces_term

@[simp]
theorem toArtificialFaceResolved_artificialFaces
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.toArtificialFaceResolved.artificialFaces =
      D.artificial.artificialFaces :=
  rfl

/-- Expose the M8 boundary-target resolved package. -/
def toBoundaryTargetResolved
    [IsManifold I 1 M]
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    M8CompactSupportBoundaryTargetResolvedData I omega D.formData
      D.selectedPartition D.targetImageInput.targetImages D.toMeasureResolved where
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  selectedPartition_supportSet := D.selectedPartition_supportSet
  targetImages_active := D.targetImageInput.targetImages_active
  targetImages_source_mem := D.targetImageInput.targetImages_source_mem
  targetImages_boundarySource_mem :=
    D.targetImageInput.targetImages_boundarySource_mem
  targetBoundaryTerm_eq_partition :=
    D.targetImageInput.targetBoundaryTerm_eq_measureLocalization
      D.measure.toM8MeasureLocalizationData D.target_boundaryPartitionTerm

@[simp]
theorem toBoundaryTargetResolved_orientedBoundaryAtlas
    [IsManifold I 1 M]
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.toBoundaryTargetResolved.orientedBoundaryAtlas =
      D.orientedBoundaryAtlas :=
  rfl

/-- Forget the natural resolved packages and expose the compact-support M8 input. -/
def toM8CompactSupportStokesInput
    [IsManifold I 1 M]
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    M8CompactSupportStokesInput I omega BoundaryPiece where
  formData := D.formData
  selectedPartition := D.selectedPartition
  targetImages := D.targetImageInput.targetImages
  measureResolved := D.toMeasureResolved
  artificialFaceResolved := D.toArtificialFaceResolved
  boundaryTargetResolved := D.toBoundaryTargetResolved

@[simp]
theorem toM8CompactSupportStokesInput_measureResolved
    [IsManifold I 1 M]
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.toM8CompactSupportStokesInput.measureResolved =
      D.toMeasureResolved :=
  rfl

/--
Natural compact-support Stokes wrapper.

The statement is the compact-support measure-level equality exposed by the
resolved measure package.  Its proof is exactly `m8CompactSupportStokes`.
-/
theorem stokes
    [IsManifold I 1 M]
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.measure.toM8MeasureLocalizationData.bulkMeasureIntegral =
      D.measure.toM8MeasureLocalizationData.boundaryMeasureIntegral := by
  simpa [toM8CompactSupportStokesInput, toMeasureResolved] using
    m8CompactSupportStokes D.toM8CompactSupportStokesInput

/--
Natural compact-support Stokes in the compact-support package's own field
names.
-/
theorem stokes_compactSupportFields
    [IsManifold I 1 M]
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.measure.globalBulkIntegral =
      D.measure.boundary.boundaryMeasureIntegral := by
  simpa [CompactSupportToM8MeasureData.toM8MeasureLocalizationData] using
    D.stokes

end NaturalCompactSupportStokesInput

/-- Top-level natural compact-support Stokes theorem. -/
theorem naturalCompactSupportStokes
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
    [IsManifold I 1 M]
    {omega : ManifoldForm I M n}
    {BoundaryPiece : Type b}
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.measure.toM8MeasureLocalizationData.bulkMeasureIntegral =
      D.measure.toM8MeasureLocalizationData.boundaryMeasureIntegral :=
  D.stokes

/-- Top-level natural compact-support Stokes theorem in compact-support fields. -/
theorem naturalCompactSupportStokes_compactSupportFields
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
    [IsManifold I 1 M]
    {omega : ManifoldForm I M n}
    {BoundaryPiece : Type b}
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.measure.globalBulkIntegral =
      D.measure.boundary.boundaryMeasureIntegral :=
  D.stokes_compactSupportFields

end NaturalCompactSupportStokesStatement

end Stokes

end
