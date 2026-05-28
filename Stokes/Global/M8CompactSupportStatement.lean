import Stokes.Global.M8Statement

/-!
# Compact-support-facing M8 Stokes statement

This file gives a thinner, compact-support-facing wrapper around
`m8GlobalStokes`.  It does not add analytic content: the remaining work is
packaged into three resolved inputs, then projected to the existing
`M8GlobalStokesInput`.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section M8CompactSupportStatement

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

/--
Resolved measure-localization input for the compact-support-facing M8 wrapper.
-/
structure M8CompactSupportMeasureResolvedData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece) where
  /-- The measure-level bulk and boundary localization package used by M8. -/
  measureLocalization :
    M8MeasureLocalizationData I omega selectedPartition targetImages

/--
Resolved artificial-face input for the compact-support-facing M8 wrapper.
-/
structure M8CompactSupportArtificialFaceResolvedData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureResolved :
      M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages) where
  /-- Artificial faces already reduced to a single cancellation package. -/
  artificialFaces : ArtificialFaceResolvedData M Unit
  /-- The resolved artificial-face data uses the selected active charts. -/
  artificialFaces_active :
    artificialFaces.activeCharts = selectedPartition.active
  /-- The resolved artificial-face data uses singleton localized pieces. -/
  artificialFaces_pieces :
    artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit)
  /-- Its term is the localized artificial-boundary term from the measure package. -/
  artificialFaces_term :
    artificialFaces.interiorBoundaryTerm =
      measureResolved.measureLocalization.interiorBoundaryTerm

/--
Resolved boundary-target data for the compact-support-facing M8 wrapper.

This package keeps the compact-support/selection compatibility, oriented
boundary-chart atlas data, target-image active-set compatibility, and the final
comparison between transported boundary terms and boundary partition terms.
-/
structure M8CompactSupportBoundaryTargetResolvedData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureResolved :
      M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages) where
  /-- Explicit oriented boundary-chart atlas data. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- The selected partition is controlled by the compact support set. -/
  selectedPartition_supportSet :
    selectedPartition.K = formData.supportSet
  /-- Target-image data uses the selected active chart set. -/
  targetImages_active :
    targetImages.activeCharts = selectedPartition.active
  /-- Source charts of target-image pieces belong to the explicit oriented atlas. -/
  targetImages_source_mem :
    forall x, x ∈ targetImages.activeCharts ->
      forall q, q ∈ targetImages.boundaryPieces x ->
        targetImages.sourceChart x q ∈ orientedBoundaryAtlas.charts
  /-- Boundary-source charts of target-image pieces belong to the oriented atlas. -/
  targetImages_boundarySource_mem :
    forall x, x ∈ targetImages.activeCharts ->
      forall q, q ∈ targetImages.boundaryPieces x ->
        targetImages.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts
  /-- Transported target-image terms agree with the boundary partition terms. -/
  targetBoundaryTerm_eq_partition :
    forall x, x ∈ selectedPartition.active ->
      forall q, q ∈ targetImages.boundaryPieces x ->
        BoundaryPieceFamilyInput.boundaryBoundaryTerm targetImages x q =
          measureResolved.measureLocalization.boundaryPartitionTerm x q

/--
Compact-support-facing M8 input.

The visible inputs are the compactly supported form data, the selected
partition, the selected target-image family, and three resolved packages:
measure localization, artificial-face cancellation, and boundary-target
compatibility.
-/
structure M8CompactSupportStokesInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b) where
  /-- Compactly supported smooth input form. -/
  formData : CompactlySupportedSmoothFormData I omega
  /-- Selected partition of unity and selected interior boxes. -/
  selectedPartition : SelectedBoxPartitionOfUnity I omega
  /-- Boundary pieces carrying selected target-image data. -/
  targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece
  /-- Resolved measure-localization package. -/
  measureResolved :
    M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages
  /-- Resolved artificial-face package. -/
  artificialFaceResolved :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved
  /-- Resolved boundary-target and compact-support compatibility package. -/
  boundaryTargetResolved :
    M8CompactSupportBoundaryTargetResolvedData I omega formData
      selectedPartition targetImages measureResolved

namespace M8CompactSupportStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {BoundaryPiece : Type b}

/-- Forget the compact-support-facing packaging and expose the existing M8 input. -/
def toM8GlobalStokesInput
    (D : M8CompactSupportStokesInput I omega BoundaryPiece) :
    M8GlobalStokesInput I omega BoundaryPiece where
  formData := D.formData
  orientedBoundaryAtlas := D.boundaryTargetResolved.orientedBoundaryAtlas
  selectedPartition := D.selectedPartition
  selectedPartition_supportSet :=
    D.boundaryTargetResolved.selectedPartition_supportSet
  targetImages := D.targetImages
  targetImages_active := D.boundaryTargetResolved.targetImages_active
  measureLocalization := D.measureResolved.measureLocalization
  artificialFaces := D.artificialFaceResolved.artificialFaces
  artificialFaces_active := D.artificialFaceResolved.artificialFaces_active
  artificialFaces_pieces := D.artificialFaceResolved.artificialFaces_pieces
  artificialFaces_term := D.artificialFaceResolved.artificialFaces_term
  targetImages_source_mem := D.boundaryTargetResolved.targetImages_source_mem
  targetImages_boundarySource_mem :=
    D.boundaryTargetResolved.targetImages_boundarySource_mem
  targetBoundaryTerm_eq_partition :=
    D.boundaryTargetResolved.targetBoundaryTerm_eq_partition

@[simp]
theorem toM8GlobalStokesInput_measureLocalization
    (D : M8CompactSupportStokesInput I omega BoundaryPiece) :
    D.toM8GlobalStokesInput.measureLocalization =
      D.measureResolved.measureLocalization :=
  rfl

@[simp]
theorem toM8GlobalStokesInput_formData
    (D : M8CompactSupportStokesInput I omega BoundaryPiece) :
    D.toM8GlobalStokesInput.formData = D.formData :=
  rfl

@[simp]
theorem toM8GlobalStokesInput_selectedPartition
    (D : M8CompactSupportStokesInput I omega BoundaryPiece) :
    D.toM8GlobalStokesInput.selectedPartition = D.selectedPartition :=
  rfl

@[simp]
theorem toM8GlobalStokesInput_targetImages
    (D : M8CompactSupportStokesInput I omega BoundaryPiece) :
    D.toM8GlobalStokesInput.targetImages = D.targetImages :=
  rfl

/--
Compact-support-facing M8 theorem.

All remaining analytic and geometric obligations are carried by the three
resolved packages in `D`; the proof is exactly the existing M8 theorem.
-/
theorem stokes
    [IsManifold I 1 M]
    (D : M8CompactSupportStokesInput I omega BoundaryPiece) :
    D.measureResolved.measureLocalization.bulkMeasureIntegral =
      D.measureResolved.measureLocalization.boundaryMeasureIntegral := by
  simpa [toM8GlobalStokesInput] using
    m8GlobalStokes (D.toM8GlobalStokesInput)

end M8CompactSupportStokesInput

/-- Top-level compact-support-facing M8 theorem. -/
theorem m8CompactSupportStokes
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
    [IsManifold I 1 M]
    {omega : ManifoldForm I M n}
    {BoundaryPiece : Type b}
    (D : M8CompactSupportStokesInput I omega BoundaryPiece) :
    D.measureResolved.measureLocalization.bulkMeasureIntegral =
      D.measureResolved.measureLocalization.boundaryMeasureIntegral :=
  D.stokes

end M8CompactSupportStatement

end Stokes

end
