import Stokes.Global.BoundaryTargetImageToAssembly
import Stokes.Global.M8Statement

/-!
# Target-image data as M8 input fields

This file is the M8-facing adapter for boundary target-image data.  The pure
`BoundaryChart.TargetImageFieldReduction` layer resolves target boxes, while
`BoundaryTargetImageToAssembly` adds the global partition endpoint fields.  The
wrappers here expose exactly the target-image fields consumed by
`M8GlobalStokesInput`.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section TargetImageToM8

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

/--
Boundary target-image data in the shape needed by `M8GlobalStokesInput`.

The chart labels are the manifold points used by the selected partition.  The
underlying assembly input keeps all local target-image and partition endpoint
data; this wrapper records only the active-set alignment and oriented-atlas
membership facts needed by M8.
-/
structure M8TargetImageInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (BoundaryPiece : Type b) where
  /-- Target-image and boundary-partition endpoint data. -/
  assembly : BoundaryTargetImageToAssemblyInput I omega M BoundaryPiece
  /-- The target-image family uses the selected partition active set. -/
  active_eq : assembly.activeCharts = selectedPartition.active
  /-- Source charts lie in the oriented boundary atlas. -/
  source_mem :
    forall x, x ∈ assembly.activeCharts ->
      forall q, q ∈ assembly.boundaryPieces x ->
        assembly.sourceChart x q ∈ orientedBoundaryAtlas.charts
  /-- Boundary-source charts lie in the oriented boundary atlas. -/
  boundarySource_mem :
    forall x, x ∈ assembly.activeCharts ->
      forall q, q ∈ assembly.boundaryPieces x ->
        assembly.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts
  /-- Boundary-target charts lie in the oriented boundary atlas. -/
  boundaryTarget_mem :
    forall x, x ∈ assembly.activeCharts ->
      forall q, q ∈ assembly.boundaryPieces x ->
        assembly.boundaryTargetChart x q ∈ orientedBoundaryAtlas.charts

namespace M8TargetImageInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/-- The boundary-piece family supplied to `M8GlobalStokesInput.targetImages`. -/
abbrev targetImages
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    BoundaryPieceFamilyInput I omega M BoundaryPiece :=
  D.assembly.targetImageData.toBoundaryPieceFamilyInput

@[simp]
theorem targetImages_activeCharts
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    D.targetImages.activeCharts = D.assembly.activeCharts :=
  rfl

@[simp]
theorem targetImages_boundaryPieces
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    D.targetImages.boundaryPieces = D.assembly.boundaryPieces :=
  rfl

@[simp]
theorem targetImages_sourceChart
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    D.targetImages.sourceChart = D.assembly.sourceChart :=
  rfl

@[simp]
theorem targetImages_boundarySourceChart
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    D.targetImages.boundarySourceChart = D.assembly.boundarySourceChart :=
  rfl

@[simp]
theorem targetImages_boundaryTargetChart
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    D.targetImages.boundaryTargetChart = D.assembly.boundaryTargetChart :=
  rfl

/-- The target-image active set is the selected partition active set. -/
theorem targetImages_active
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    D.targetImages.activeCharts = selectedPartition.active := by
  simpa [targetImages] using D.active_eq

/-- Source-chart atlas membership in the exact field shape expected by M8. -/
theorem targetImages_source_mem
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    forall x, x ∈ D.targetImages.activeCharts ->
      forall q, q ∈ D.targetImages.boundaryPieces x ->
        D.targetImages.sourceChart x q ∈ orientedBoundaryAtlas.charts := by
  intro x hx q hq
  simpa [targetImages] using D.source_mem x hx q hq

/-- Boundary-source atlas membership in the exact field shape expected by M8. -/
theorem targetImages_boundarySource_mem
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    forall x, x ∈ D.targetImages.activeCharts ->
      forall q, q ∈ D.targetImages.boundaryPieces x ->
        D.targetImages.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts := by
  intro x hx q hq
  simpa [targetImages] using D.boundarySource_mem x hx q hq

/-- Selected boundary assembly induced by the target-image data and oriented atlas. -/
def selectedBoundaryAssemblyData
    [IsManifold I 1 M]
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    SelectedBoundaryAssemblyData I omega M BoundaryPiece :=
  D.assembly.toSelectedBoundaryAssemblyData_of_orientedAtlas
    orientedBoundaryAtlas D.boundarySource_mem D.boundaryTarget_mem

/--
The transported target-image boundary term agrees pointwise with the boundary
partition term recorded by the assembly input.
-/
theorem targetBoundaryTerm_eq_assemblyPartition
    [IsManifold I 1 M]
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    forall x, x ∈ D.targetImages.activeCharts ->
      forall q, q ∈ D.targetImages.boundaryPieces x ->
        BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages x q =
          D.assembly.boundaryPartitionTerm x q := by
  intro x hx q hq
  have hpoint :
      SelectedBoundaryAssemblyData.boundaryBoundaryTerm
          (D.selectedBoundaryAssemblyData) x q =
        (D.selectedBoundaryAssemblyData).boundaryPartitionTerm x q :=
    (D.selectedBoundaryAssemblyData).pointwise_chartChange x hx q hq
  simpa [selectedBoundaryAssemblyData, targetImages,
    BoundaryTargetImageToAssemblyInput.toSelectedBoundaryAssemblyData_of_orientedAtlas,
    BoundaryTargetImageToAssemblyInput.toBoundaryOrientationSelectedAssemblyInput,
    BoundaryOrientationSelectedAssemblyInput.toSelectedBoundaryAssemblyData_of_orientedAtlas,
    SelectedBoundaryAssemblyData.boundaryBoundaryTerm,
    BoundaryPieceFamilyInput.boundaryBoundaryTerm] using hpoint

/--
Pointwise M8 target-boundary alignment after identifying the assembly
partition term with an external boundary partition term.
-/
theorem targetBoundaryTerm_eq_partition
    [IsManifold I 1 M]
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (boundaryPartitionTerm : M -> BoundaryPiece -> Real)
    (hterm : D.assembly.boundaryPartitionTerm = boundaryPartitionTerm) :
    forall x, x ∈ selectedPartition.active ->
      forall q, q ∈ D.targetImages.boundaryPieces x ->
        BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages x q =
          boundaryPartitionTerm x q := by
  intro x hx q hq
  have hx' : x ∈ D.targetImages.activeCharts := by
    simpa [D.targetImages_active] using hx
  simpa [hterm] using
    D.targetBoundaryTerm_eq_assemblyPartition x hx' q hq

/--
Pointwise M8 target-boundary alignment against an `M8MeasureLocalizationData`
package whose boundary partition term is the assembly partition term.
-/
theorem targetBoundaryTerm_eq_measureLocalization
    [IsManifold I 1 M]
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition D.targetImages)
    (hterm :
      D.assembly.boundaryPartitionTerm =
        measureLocalization.boundaryPartitionTerm) :
    forall x, x ∈ selectedPartition.active ->
      forall q, q ∈ D.targetImages.boundaryPieces x ->
        BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages x q =
          measureLocalization.boundaryPartitionTerm x q :=
  D.targetBoundaryTerm_eq_partition
    measureLocalization.boundaryPartitionTerm hterm

end M8TargetImageInput

namespace M8GlobalStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/--
Constructor for `M8GlobalStokesInput` that fills all target-image fields from
the target-image-to-assembly adapter.
-/
def ofTargetImageInput
    [IsManifold I 1 M]
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition
        targetImageInput.targetImages)
    (measureLocalization_boundaryTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measureLocalization.boundaryPartitionTerm)
    (artificialFaces : ArtificialFaceResolvedData M Unit)
    (artificialFaces_active :
      artificialFaces.activeCharts = selectedPartition.active)
    (artificialFaces_pieces :
      artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (artificialFaces_term :
      artificialFaces.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm) :
    M8GlobalStokesInput I omega BoundaryPiece where
  formData := formData
  orientedBoundaryAtlas := orientedBoundaryAtlas
  selectedPartition := selectedPartition
  selectedPartition_supportSet := selectedPartition_supportSet
  targetImages := targetImageInput.targetImages
  targetImages_active := targetImageInput.targetImages_active
  measureLocalization := measureLocalization
  artificialFaces := artificialFaces
  artificialFaces_active := artificialFaces_active
  artificialFaces_pieces := artificialFaces_pieces
  artificialFaces_term := artificialFaces_term
  targetImages_source_mem := targetImageInput.targetImages_source_mem
  targetImages_boundarySource_mem :=
    targetImageInput.targetImages_boundarySource_mem
  targetBoundaryTerm_eq_partition :=
    targetImageInput.targetBoundaryTerm_eq_measureLocalization
      measureLocalization measureLocalization_boundaryTerm

@[simp]
theorem ofTargetImageInput_targetImages
    [IsManifold I 1 M]
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition
        targetImageInput.targetImages)
    (measureLocalization_boundaryTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measureLocalization.boundaryPartitionTerm)
    (artificialFaces : ArtificialFaceResolvedData M Unit)
    (artificialFaces_active :
      artificialFaces.activeCharts = selectedPartition.active)
    (artificialFaces_pieces :
      artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (artificialFaces_term :
      artificialFaces.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm) :
    (ofTargetImageInput formData orientedBoundaryAtlas selectedPartition
        selectedPartition_supportSet targetImageInput measureLocalization
        measureLocalization_boundaryTerm artificialFaces artificialFaces_active
        artificialFaces_pieces artificialFaces_term).targetImages =
      targetImageInput.targetImages :=
  rfl

@[simp]
theorem ofTargetImageInput_measureLocalization
    [IsManifold I 1 M]
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition
        targetImageInput.targetImages)
    (measureLocalization_boundaryTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measureLocalization.boundaryPartitionTerm)
    (artificialFaces : ArtificialFaceResolvedData M Unit)
    (artificialFaces_active :
      artificialFaces.activeCharts = selectedPartition.active)
    (artificialFaces_pieces :
      artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (artificialFaces_term :
      artificialFaces.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm) :
    (ofTargetImageInput formData orientedBoundaryAtlas selectedPartition
        selectedPartition_supportSet targetImageInput measureLocalization
        measureLocalization_boundaryTerm artificialFaces artificialFaces_active
        artificialFaces_pieces artificialFaces_term).measureLocalization =
      measureLocalization :=
  rfl

end M8GlobalStokesInput

end TargetImageToM8

end Stokes

end
