import Stokes.Global.BulkMeasureFromPartition
import Stokes.Global.NaturalBoundaryMeasureBuilder
import Stokes.Global.NaturalCompactSupportStokesStatement
import Stokes.Global.BoundaryMeasureFromTargetCOV

/-!
# Natural compact-support Stokes with separated measure spaces

The older compact-support adapter `CompactSupportToM8MeasureData` uses one
measure space for both the bulk and boundary localization data.  This file keeps
the same M8 endpoint, but lets the bulk and boundary analytic packages live on
different measure spaces.

The intended first use is:

* bulk terms over `Fin (n + 1) -> Real`;
* boundary terms over `Fin n -> Real`.

No analytic theorem is hidden here.  The adapter only combines already proved
bulk and boundary localization packages into the real-valued
`M8MeasureLocalizationData` consumed by the compact-support M8 theorem.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportSeparatedMeasures

universe u w b ab adb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {AlphaBulk : Type ab} [TopologicalSpace AlphaBulk]
variable [MeasurableSpace AlphaBulk] [OpensMeasurableSpace AlphaBulk]
variable [T2Space AlphaBulk]
variable {muBulk : Measure AlphaBulk} [IsFiniteMeasureOnCompacts muBulk]
variable {AlphaBoundary : Type adb} [TopologicalSpace AlphaBoundary]
variable [MeasurableSpace AlphaBoundary] [OpensMeasurableSpace AlphaBoundary]
variable [T2Space AlphaBoundary]
variable {muBoundary : Measure AlphaBoundary}
variable [IsFiniteMeasureOnCompacts muBoundary]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

/--
Compact-support measure data with separate bulk and boundary measure spaces.

The bulk package may be built over the ambient chart space, while the boundary
package may be built over the lower-dimensional boundary chart space.  The two
halves meet only in the target `M8MeasureLocalizationData`, whose fields are
real numbers and finite sums indexed by the selected chart data.
-/
structure SeparatedCompactSupportToM8MeasureData
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (muBulk : Measure AlphaBulk)
    [IsFiniteMeasureOnCompacts muBulk]
    (muBoundary : Measure AlphaBoundary) where
  /-- Represented global bulk integral. -/
  globalBulkIntegral : Real
  /-- Bulk localization data over the bulk measure space. -/
  bulk :
    BulkMeasureFromPartitionData
      (α := AlphaBulk) (μ := muBulk)
      selectedPartition targetImages globalBulkIntegral
  /-- Boundary localization data over the boundary measure space. -/
  boundary :
    NaturalBoundaryMeasureBuilderData
      (α := AlphaBoundary) I omega selectedPartition targetImages
      muBoundary

namespace SeparatedCompactSupportToM8MeasureData

variable
    (D :
      SeparatedCompactSupportToM8MeasureData
        (AlphaBulk := AlphaBulk) (AlphaBoundary := AlphaBoundary)
        I omega selectedPartition targetImages muBulk muBoundary)

/-- The bulk half rewritten into the exact M8 bulk field shape. -/
def toM8BulkMeasureFields :
    M8BulkMeasureFields I omega selectedPartition targetImages :=
  D.bulk.toBulkMeasureLocalizationFields.toM8BulkMeasureFields
    D.bulk.localized.localized_active
    D.bulk.localized.localized_coefficient
    D.bulk.boundary_active

/-- The boundary half rewritten into the exact M8 boundary field shape. -/
def toM8BoundaryMeasureData :
    M8BoundaryMeasureData I omega selectedPartition targetImages :=
  D.boundary.toM8BoundaryMeasureData

/--
Final M8 measure-localization data assembled from separated bulk and boundary
measure packages.
-/
def toM8MeasureLocalizationData :
    M8MeasureLocalizationData I omega selectedPartition targetImages :=
  D.toM8BulkMeasureFields.toM8MeasureLocalizationData
    D.boundary.boundaryPartitionTerm
    D.boundary.globalBoundaryIntegral
    D.boundary.toBoundaryMeasureLocalizationFields.boundaryMeasureIntegral
    D.boundary.toBoundaryMeasureLocalizationFields.globalBoundaryIntegral_eq_boundaryMeasureIntegral
    D.boundary.toBoundaryMeasureLocalizationFields.boundaryMeasureIntegral_eq_partitionSum

@[simp]
theorem toM8MeasureLocalizationData_globalBulkIntegral :
    D.toM8MeasureLocalizationData.globalBulkIntegral =
      D.globalBulkIntegral := by
  rfl

@[simp]
theorem toM8MeasureLocalizationData_bulkMeasureIntegral :
    D.toM8MeasureLocalizationData.bulkMeasureIntegral =
      D.globalBulkIntegral := by
  rfl

@[simp]
theorem toM8MeasureLocalizationData_boundaryPartitionTerm :
    D.toM8MeasureLocalizationData.boundaryPartitionTerm =
      D.boundary.boundaryPartitionTerm := by
  rfl

@[simp]
theorem toM8MeasureLocalizationData_globalBoundaryIntegral :
    D.toM8MeasureLocalizationData.globalBoundaryIntegral =
      D.boundary.globalBoundaryIntegral := by
  rfl

@[simp]
theorem toM8MeasureLocalizationData_boundaryMeasureIntegral :
    D.toM8MeasureLocalizationData.boundaryMeasureIntegral =
      D.boundary.compactFields.boundaryMeasureIntegral := by
  rfl

/-- The separated adapter keeps the selected bulk finite-sum reconstruction. -/
theorem toM8MeasureLocalizationData_bulkMeasureIntegral_eq_localBulkSum :
    D.toM8MeasureLocalizationData.bulkMeasureIntegral =
      (Finset.sum selectedPartition.active fun x =>
        Finset.sum ({()} : Finset Unit) fun _q =>
          D.bulk.localized.localizedInterior.bulkTerm x) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (targetImages.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm targetImages x q := by
  simpa using BulkMeasureFromPartitionData.bulkIntegralLocalizes_selected D.bulk

/-- The separated adapter keeps the selected boundary finite-sum reconstruction. -/
theorem toM8MeasureLocalizationData_boundaryMeasureIntegral_eq_partitionSum :
    D.toM8MeasureLocalizationData.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces D.boundary.boundaryPartitionTerm := by
  simpa using
    NaturalBoundaryMeasureBuilderData.boundaryMeasureIntegral_eq_partitionSum
      D.boundary

variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/--
Constructor from the existing COV-backed boundary route.

This is the common case where the bulk package is built on an ambient chart
measure space, while the boundary COV package is built on a boundary chart
measure space.
-/
def ofBoundaryFromTargetCOV
    [IsManifold I 1 M]
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := AlphaBulk) (μ := muBulk)
        selectedPartition targetImageInput.targetImages globalBulkIntegral)
    (boundaryCOV :
      BoundaryMeasureFromTargetCOVInput
        (α := AlphaBoundary) targetImageInput muBoundary) :
    SeparatedCompactSupportToM8MeasureData
      (AlphaBulk := AlphaBulk) (AlphaBoundary := AlphaBoundary)
      I omega selectedPartition targetImageInput.targetImages
      muBulk muBoundary where
  globalBulkIntegral := globalBulkIntegral
  bulk := bulk
  boundary :=
    { boundaryPartitionTerm := targetImageInput.assembly.boundaryPartitionTerm
      compactFields :=
        boundaryCOV.toCanonicalBoundaryTargetCompactSupportInput
          |>.canonicalBoundaryCompactFields
      globalBoundaryIntegral := boundaryCOV.globalBoundaryIntegral
      globalBoundaryIntegral_eq_boundaryMeasureIntegral := by
        simpa using
          boundaryCOV.globalBoundaryIntegral_eq_boundaryMeasureIntegral }

end SeparatedCompactSupportToM8MeasureData

/--
Compact-support Stokes input whose bulk and boundary measure spaces are allowed
to differ.

This mirrors `NaturalCompactSupportStokesInput`, but its measure field is the
separated adapter above instead of the older one-measure-space package.
-/
structure NaturalCompactSupportSeparatedMeasuresInput
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (muBulk : Measure AlphaBulk)
    [IsFiniteMeasureOnCompacts muBulk]
    (muBoundary : Measure AlphaBoundary) where
  /-- Compactly supported smooth input form. -/
  formData : CompactlySupportedSmoothFormData I omega
  /-- Explicit oriented boundary-chart atlas data. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Selected partition of unity and selected chart boxes. -/
  selectedPartition : SelectedBoxPartitionOfUnity I omega
  /-- The selected partition is controlled by the compact support set. -/
  selectedPartition_supportSet :
    selectedPartition.K = formData.supportSet
  /-- Boundary target-image data over the selected partition. -/
  targetImageInput :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece
  /-- Separated bulk and boundary measure data. -/
  measure :
    SeparatedCompactSupportToM8MeasureData
      (AlphaBulk := AlphaBulk) (AlphaBoundary := AlphaBoundary)
      I omega selectedPartition targetImageInput.targetImages
      muBulk muBoundary
  /--
  The boundary partition term in the target-image assembly is the boundary
  partition term used by separated measure localization.
  -/
  target_boundaryPartitionTerm :
    targetImageInput.assembly.boundaryPartitionTerm =
      measure.toM8MeasureLocalizationData.boundaryPartitionTerm
  /-- Resolved artificial-face cancellation in the M8 shape. -/
  artificial :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImageInput.targetImages measure.toM8MeasureLocalizationData

namespace NaturalCompactSupportSeparatedMeasuresInput

variable
    (D :
      NaturalCompactSupportSeparatedMeasuresInput
        (AlphaBulk := AlphaBulk) (AlphaBoundary := AlphaBoundary)
        I omega BoundaryPiece muBulk muBoundary)

/-- Expose the M8 measure-resolved package. -/
def toMeasureResolved :
    M8CompactSupportMeasureResolvedData I omega D.selectedPartition
      D.targetImageInput.targetImages where
  measureLocalization := D.measure.toM8MeasureLocalizationData

@[simp]
theorem toMeasureResolved_measureLocalization :
    D.toMeasureResolved.measureLocalization =
      D.measure.toM8MeasureLocalizationData := by
  rfl

/-- Expose the M8 artificial-face resolved package. -/
def toArtificialFaceResolved :
    M8CompactSupportArtificialFaceResolvedData I omega D.selectedPartition
      D.targetImageInput.targetImages D.toMeasureResolved where
  artificialFaces := D.artificial.artificialFaces
  artificialFaces_active := D.artificial.artificialFaces_active
  artificialFaces_pieces := D.artificial.artificialFaces_pieces
  artificialFaces_term := D.artificial.artificialFaces_term

/-- Expose the M8 boundary-target resolved package. -/
def toBoundaryTargetResolved
    [IsManifold I 1 M] :
    M8CompactSupportBoundaryTargetResolvedData I omega D.formData
      D.selectedPartition D.targetImageInput.targetImages
      D.toMeasureResolved where
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  selectedPartition_supportSet := D.selectedPartition_supportSet
  targetImages_active := D.targetImageInput.targetImages_active
  targetImages_source_mem := D.targetImageInput.targetImages_source_mem
  targetImages_boundarySource_mem :=
    D.targetImageInput.targetImages_boundarySource_mem
  targetBoundaryTerm_eq_partition :=
    D.targetImageInput.targetBoundaryTerm_eq_measureLocalization
      D.measure.toM8MeasureLocalizationData D.target_boundaryPartitionTerm

/-- Forget the separated natural wrapper and expose the compact-support M8 input. -/
def toM8CompactSupportStokesInput
    [IsManifold I 1 M] :
    M8CompactSupportStokesInput I omega BoundaryPiece where
  formData := D.formData
  selectedPartition := D.selectedPartition
  targetImages := D.targetImageInput.targetImages
  measureResolved := D.toMeasureResolved
  artificialFaceResolved := D.toArtificialFaceResolved
  boundaryTargetResolved := D.toBoundaryTargetResolved

@[simp]
theorem toM8CompactSupportStokesInput_measureResolved
    [IsManifold I 1 M] :
    D.toM8CompactSupportStokesInput.measureResolved =
      D.toMeasureResolved := by
  rfl

/--
Separated-measure compact-support Stokes theorem, routed through the existing
M8 compact-support endpoint.
-/
theorem stokes
    [IsManifold I 1 M] :
    D.measure.toM8MeasureLocalizationData.bulkMeasureIntegral =
      D.measure.toM8MeasureLocalizationData.boundaryMeasureIntegral := by
  simpa [toM8CompactSupportStokesInput, toMeasureResolved] using
    m8CompactSupportStokes D.toM8CompactSupportStokesInput

/-- Stokes in the separated adapter's compact-support field names. -/
theorem stokes_compactSupportFields
    [IsManifold I 1 M] :
    D.measure.globalBulkIntegral =
      D.measure.boundary.compactFields.boundaryMeasureIntegral := by
  simpa using D.stokes

end NaturalCompactSupportSeparatedMeasuresInput

/--
Top-level compact-support Stokes wrapper for separated bulk and boundary
measure spaces.
-/
theorem naturalCompactSupportStokes_of_separatedMeasures
    [IsManifold I 1 M]
    (D :
      NaturalCompactSupportSeparatedMeasuresInput
        (AlphaBulk := AlphaBulk) (AlphaBoundary := AlphaBoundary)
        I omega BoundaryPiece muBulk muBoundary) :
    D.measure.toM8MeasureLocalizationData.bulkMeasureIntegral =
      D.measure.toM8MeasureLocalizationData.boundaryMeasureIntegral :=
  D.stokes

/--
Top-level compact-support Stokes wrapper in separated adapter field names.
-/
theorem naturalCompactSupportStokes_separatedCompactSupportFields
    [IsManifold I 1 M]
    (D :
      NaturalCompactSupportSeparatedMeasuresInput
        (AlphaBulk := AlphaBulk) (AlphaBoundary := AlphaBoundary)
        I omega BoundaryPiece muBulk muBoundary) :
    D.measure.globalBulkIntegral =
      D.measure.boundary.compactFields.boundaryMeasureIntegral :=
  D.stokes_compactSupportFields

end NaturalCompactSupportSeparatedMeasures

end Stokes

end
