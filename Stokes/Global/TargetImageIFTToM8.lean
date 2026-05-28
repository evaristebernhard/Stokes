import Stokes.BoundaryChart.TargetImageIFTBridge
import Stokes.Global.TargetImageResolvedToM8Input

/-!
# IFT-facing target-image data as M8 input

This file is the global adapter from the pure boundary-chart
`BoundaryChartIFTTargetImageFamily` package to the M8 target-image input shape.

The pure file proves the local-openness neighborhood statement from
strict-derivative/surjectivity data.  This global wrapper adds only the data
that belongs to the M8/global layer: source extended boxes, boundary partition
endpoint boxes, and oriented-atlas membership.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section TargetImageIFTToM8

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

/--
M8-facing target-image input whose pure boundary-chart component is produced
from inverse-function/local-openness data.
-/
structure M8TargetImageIFTInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (BoundaryPiece : Type b) where
  /-- Pure IFT-facing target-image family.  M8 chart labels are manifold points. -/
  family : BoundaryChartIFTTargetImageFamily I omega M BoundaryPiece
  /-- Extended source boxes needed by local boundary Stokes. -/
  sourceExtendedBox :
    forall x, x ∈ family.toTargetImageResolvedFamily.activeCharts ->
      forall q, q ∈ family.toTargetImageResolvedFamily.localPieces x ->
        boundaryChartExtendedBox I (family.toTargetImageResolvedFamily.sourceChart x q)
          (family.toTargetImageResolvedFamily.boundarySourceChart x q) omega
          (family.toTargetImageResolvedFamily.sourceLowerCorner x q)
          (family.toTargetImageResolvedFamily.sourceUpperCorner x q)
  /-- Chart used for the selected boundary-partition representative. -/
  partitionTargetChart : M -> BoundaryPiece -> M
  /-- Target-box selection for the COV from transported boundary term to partition term. -/
  partitionTargetBox :
    (x : M) -> (q : BoundaryPiece) ->
      BoundaryChartTargetBoxSelection I
        (family.toTargetImageResolvedFamily.boundarySourceChart x q)
        (family.toTargetImageResolvedFamily.boundaryTargetChart x q)
        (family.toTargetImageResolvedFamily.targetLowerCorner x q)
        (family.toTargetImageResolvedFamily.targetUpperCorner x q)
  /-- Selected auxiliary target box for the selected partition representative. -/
  partitionSelectedBox :
    forall x, x ∈ family.toTargetImageResolvedFamily.activeCharts ->
      forall q, q ∈ family.toTargetImageResolvedFamily.localPieces x ->
        boundaryChartSelectedBox I
          (family.toTargetImageResolvedFamily.boundaryTargetChart x q)
          (partitionTargetChart x q) omega
          ((partitionTargetBox x q).lowerCorner)
          ((partitionTargetBox x q).upperCorner)
  /-- Boundary partition term used by the global reconstruction package. -/
  boundaryPartitionTerm : M -> BoundaryPiece -> Real
  /-- Endpoint identification for the selected boundary partition term. -/
  boundaryPartitionTerm_eq :
    forall x, x ∈ family.toTargetImageResolvedFamily.activeCharts ->
      forall q, q ∈ family.toTargetImageResolvedFamily.localPieces x ->
        boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I
            (family.toTargetImageResolvedFamily.boundaryTargetChart x q)
            (partitionTargetChart x q) omega
            ((partitionTargetBox x q).lowerCorner)
            ((partitionTargetBox x q).upperCorner)
  /-- The resolved family uses the selected partition active set. -/
  active_eq : family.toTargetImageResolvedFamily.activeCharts = selectedPartition.active
  /-- Source charts lie in the oriented boundary atlas. -/
  source_mem :
    forall x, x ∈ family.toTargetImageResolvedFamily.activeCharts ->
      forall q, q ∈ family.toTargetImageResolvedFamily.localPieces x ->
        family.toTargetImageResolvedFamily.sourceChart x q ∈ orientedBoundaryAtlas.charts
  /-- Boundary-source charts lie in the oriented boundary atlas. -/
  boundarySource_mem :
    forall x, x ∈ family.toTargetImageResolvedFamily.activeCharts ->
      forall q, q ∈ family.toTargetImageResolvedFamily.localPieces x ->
        family.toTargetImageResolvedFamily.boundarySourceChart x q ∈
          orientedBoundaryAtlas.charts
  /-- Boundary-target charts lie in the oriented boundary atlas. -/
  boundaryTarget_mem :
    forall x, x ∈ family.toTargetImageResolvedFamily.activeCharts ->
      forall q, q ∈ family.toTargetImageResolvedFamily.localPieces x ->
        family.toTargetImageResolvedFamily.boundaryTargetChart x q ∈
          orientedBoundaryAtlas.charts

namespace M8TargetImageIFTInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/-- The pure resolved target-image family induced by the IFT-facing data. -/
abbrev resolvedFamily
    (D :
      M8TargetImageIFTInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    BoundaryChartTargetImageResolvedFamily I omega M BoundaryPiece :=
  D.family.toTargetImageResolvedFamily

/-- Forget the IFT-facing source down to the existing resolved-family M8 input. -/
def toResolvedInput
    (D :
      M8TargetImageIFTInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece where
  family := D.resolvedFamily
  sourceExtendedBox := D.sourceExtendedBox
  partitionTargetChart := D.partitionTargetChart
  partitionTargetBox := D.partitionTargetBox
  partitionSelectedBox := D.partitionSelectedBox
  boundaryPartitionTerm := D.boundaryPartitionTerm
  boundaryPartitionTerm_eq := D.boundaryPartitionTerm_eq
  active_eq := D.active_eq
  source_mem := D.source_mem
  boundarySource_mem := D.boundarySource_mem
  boundaryTarget_mem := D.boundaryTarget_mem

/-- IFT-facing target-image data in the exact shape consumed by M8. -/
def toM8TargetImageInput
    (D :
      M8TargetImageIFTInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece :=
  D.toResolvedInput.toM8TargetImageInput

@[simp]
theorem toResolvedInput_family
    (D :
      M8TargetImageIFTInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    D.toResolvedInput.family = D.resolvedFamily :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages
    (D :
      M8TargetImageIFTInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    D.toM8TargetImageInput.targetImages =
      D.toResolvedInput.toM8TargetImageInput.targetImages :=
  rfl

/-- Direct M8 input constructor using IFT-facing target-image data. -/
def toM8GlobalStokesInput
    [IsManifold I 1 M]
    (D :
      M8TargetImageIFTInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition
        D.toM8TargetImageInput.targetImages)
    (measureLocalization_boundaryTerm :
      D.boundaryPartitionTerm = measureLocalization.boundaryPartitionTerm)
    (artificialFaces : ArtificialFaceResolvedData M Unit)
    (artificialFaces_active :
      artificialFaces.activeCharts = selectedPartition.active)
    (artificialFaces_pieces :
      artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (artificialFaces_term :
      artificialFaces.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm) :
    M8GlobalStokesInput I omega BoundaryPiece :=
  D.toResolvedInput.toM8GlobalStokesInput formData
    selectedPartition_supportSet measureLocalization
    measureLocalization_boundaryTerm artificialFaces artificialFaces_active
    artificialFaces_pieces artificialFaces_term

end M8TargetImageIFTInput

end TargetImageIFTToM8

end Stokes

end
