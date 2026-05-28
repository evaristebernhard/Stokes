import Stokes.Global.M8Statement

/-!
# Oriented boundary atlas fields for M8

This file isolates the orientation-membership part of `M8GlobalStokesInput`.
It does not add geometric content: it only packages an oriented boundary-chart
atlas together with the two membership facts that M8 needs for a target-image
boundary family.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section OrientedAtlasToM8

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

/--
The orientation-facing target-image fields consumed by `M8GlobalStokesInput`.

The target-image family is kept separate from the oriented atlas so downstream
constructors can build the boundary family first, then supply exactly the two
atlas-membership facts needed to invoke oriented boundary chart change.
-/
structure M8TargetOrientationFields {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece) where
  /-- Explicit oriented boundary-chart atlas data. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Source charts of target-image pieces belong to the oriented atlas. -/
  source_mem :
    forall x, x ∈ targetImages.activeCharts ->
      forall q, q ∈ targetImages.boundaryPieces x ->
        targetImages.sourceChart x q ∈ orientedBoundaryAtlas.charts
  /-- Boundary-source charts of target-image pieces belong to the oriented atlas. -/
  boundarySource_mem :
    forall x, x ∈ targetImages.activeCharts ->
      forall q, q ∈ targetImages.boundaryPieces x ->
        targetImages.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts

namespace M8TargetOrientationFields

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

/-- Constructor with the field order used by downstream M8 builders. -/
def ofMembership
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (source_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.sourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundarySource_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts) :
    M8TargetOrientationFields I omega BoundaryPiece targetImages where
  orientedBoundaryAtlas := orientedBoundaryAtlas
  source_mem := source_mem
  boundarySource_mem := boundarySource_mem

@[simp]
theorem ofMembership_orientedBoundaryAtlas
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (source_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.sourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundarySource_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts) :
    (ofMembership (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece) (targetImages := targetImages)
      orientedBoundaryAtlas source_mem boundarySource_mem).orientedBoundaryAtlas =
        orientedBoundaryAtlas :=
  rfl

/-- Source-chart membership in the exact field shape expected by M8. -/
theorem targetImages_source_mem
    (D : M8TargetOrientationFields I omega BoundaryPiece targetImages) :
    forall x, x ∈ targetImages.activeCharts ->
      forall q, q ∈ targetImages.boundaryPieces x ->
        targetImages.sourceChart x q ∈ D.orientedBoundaryAtlas.charts :=
  D.source_mem

/-- Boundary-source chart membership in the exact field shape expected by M8. -/
theorem targetImages_boundarySource_mem
    (D : M8TargetOrientationFields I omega BoundaryPiece targetImages) :
    forall x, x ∈ targetImages.activeCharts ->
      forall q, q ∈ targetImages.boundaryPieces x ->
        targetImages.boundarySourceChart x q ∈ D.orientedBoundaryAtlas.charts :=
  D.boundarySource_mem

end M8TargetOrientationFields

namespace M8GlobalStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/-- Project the orientation-membership part of an M8 input. -/
def targetOrientationFields
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    M8TargetOrientationFields I omega BoundaryPiece D.targetImages where
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  source_mem := D.targetImages_source_mem
  boundarySource_mem := D.targetImages_boundarySource_mem

@[simp]
theorem targetOrientationFields_orientedBoundaryAtlas
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    D.targetOrientationFields.orientedBoundaryAtlas =
      D.orientedBoundaryAtlas :=
  rfl

/--
Constructor for `M8GlobalStokesInput` that fills the orientation-membership
fields from a single package.
-/
def ofTargetOrientationFields
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (targetImages_active :
      targetImages.activeCharts = selectedPartition.active)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages)
    (artificialFaces : ArtificialFaceResolvedData M Unit)
    (artificialFaces_active :
      artificialFaces.activeCharts = selectedPartition.active)
    (artificialFaces_pieces :
      artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (artificialFaces_term :
      artificialFaces.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm)
    (targetOrientation :
      M8TargetOrientationFields I omega BoundaryPiece targetImages)
    (targetBoundaryTerm_eq_partition :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBoundaryTerm targetImages x q =
            measureLocalization.boundaryPartitionTerm x q) :
    M8GlobalStokesInput I omega BoundaryPiece where
  formData := formData
  orientedBoundaryAtlas := targetOrientation.orientedBoundaryAtlas
  selectedPartition := selectedPartition
  selectedPartition_supportSet := selectedPartition_supportSet
  targetImages := targetImages
  targetImages_active := targetImages_active
  measureLocalization := measureLocalization
  artificialFaces := artificialFaces
  artificialFaces_active := artificialFaces_active
  artificialFaces_pieces := artificialFaces_pieces
  artificialFaces_term := artificialFaces_term
  targetImages_source_mem := targetOrientation.targetImages_source_mem
  targetImages_boundarySource_mem :=
    targetOrientation.targetImages_boundarySource_mem
  targetBoundaryTerm_eq_partition := targetBoundaryTerm_eq_partition

@[simp]
theorem ofTargetOrientationFields_orientedBoundaryAtlas
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (targetImages_active :
      targetImages.activeCharts = selectedPartition.active)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages)
    (artificialFaces : ArtificialFaceResolvedData M Unit)
    (artificialFaces_active :
      artificialFaces.activeCharts = selectedPartition.active)
    (artificialFaces_pieces :
      artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (artificialFaces_term :
      artificialFaces.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm)
    (targetOrientation :
      M8TargetOrientationFields I omega BoundaryPiece targetImages)
    (targetBoundaryTerm_eq_partition :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBoundaryTerm targetImages x q =
            measureLocalization.boundaryPartitionTerm x q) :
    (ofTargetOrientationFields formData selectedPartition
      selectedPartition_supportSet targetImages targetImages_active
      measureLocalization artificialFaces artificialFaces_active
      artificialFaces_pieces artificialFaces_term targetOrientation
      targetBoundaryTerm_eq_partition).orientedBoundaryAtlas =
        targetOrientation.orientedBoundaryAtlas :=
  rfl

@[simp]
theorem ofTargetOrientationFields_targetImages
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (targetImages_active :
      targetImages.activeCharts = selectedPartition.active)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages)
    (artificialFaces : ArtificialFaceResolvedData M Unit)
    (artificialFaces_active :
      artificialFaces.activeCharts = selectedPartition.active)
    (artificialFaces_pieces :
      artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (artificialFaces_term :
      artificialFaces.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm)
    (targetOrientation :
      M8TargetOrientationFields I omega BoundaryPiece targetImages)
    (targetBoundaryTerm_eq_partition :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBoundaryTerm targetImages x q =
            measureLocalization.boundaryPartitionTerm x q) :
    (ofTargetOrientationFields formData selectedPartition
      selectedPartition_supportSet targetImages targetImages_active
      measureLocalization artificialFaces artificialFaces_active
      artificialFaces_pieces artificialFaces_term targetOrientation
      targetBoundaryTerm_eq_partition).targetImages =
        targetImages :=
  rfl

end M8GlobalStokesInput

end OrientedAtlasToM8

end Stokes

end
