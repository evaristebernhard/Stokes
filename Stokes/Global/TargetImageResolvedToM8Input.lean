import Stokes.Global.TargetImageToM8

/-!
# Resolved target-image families as M8 input

This file composes the pure boundary-chart target-image package
`BoundaryChartTargetImageResolvedFamily` with the global
`BoundaryTargetImageToAssemblyInput` adapter and the M8-facing
`M8TargetImageInput` adapter.

The only new data here are the global fields that do not belong in the pure
`BoundaryChart` layer: source extended boxes, boundary-partition endpoint
boxes, and oriented-atlas membership facts.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section TargetImageResolvedToM8Input

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

/--
M8-facing target-image input built from a pure resolved boundary-chart family.

The `family` field is pure `BoundaryChart` data.  The remaining fields are the
global assembly and M8 alignment facts needed to turn it into an
`M8TargetImageInput`.
-/
structure M8TargetImageResolvedInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (BoundaryPiece : Type b) where
  /-- Pure resolved boundary-chart target-image family. -/
  family : BoundaryChartTargetImageResolvedFamily I omega M BoundaryPiece
  /-- Extended source boxes needed by local boundary Stokes. -/
  sourceExtendedBox :
    forall x, x ∈ family.activeCharts ->
      forall q, q ∈ family.localPieces x ->
        boundaryChartExtendedBox I (family.sourceChart x q)
          (family.boundarySourceChart x q) omega
          (family.sourceLowerCorner x q) (family.sourceUpperCorner x q)
  /-- Chart used for the selected boundary-partition representative. -/
  partitionTargetChart : M -> BoundaryPiece -> M
  /-- Target-box selection for the COV from transported boundary term to partition term. -/
  partitionTargetBox :
    (x : M) -> (q : BoundaryPiece) ->
      BoundaryChartTargetBoxSelection I
        (family.boundarySourceChart x q)
        (family.boundaryTargetChart x q)
        (family.targetLowerCorner x q)
        (family.targetUpperCorner x q)
  /-- Selected auxiliary target box for the selected partition representative. -/
  partitionSelectedBox :
    forall x, x ∈ family.activeCharts ->
      forall q, q ∈ family.localPieces x ->
        boundaryChartSelectedBox I
          (family.boundaryTargetChart x q)
          (partitionTargetChart x q) omega
          ((partitionTargetBox x q).lowerCorner)
          ((partitionTargetBox x q).upperCorner)
  /-- Boundary partition term used by the global reconstruction package. -/
  boundaryPartitionTerm : M -> BoundaryPiece -> Real
  /-- Endpoint identification for the selected boundary partition term. -/
  boundaryPartitionTerm_eq :
    forall x, x ∈ family.activeCharts ->
      forall q, q ∈ family.localPieces x ->
        boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I
            (family.boundaryTargetChart x q) (partitionTargetChart x q) omega
            ((partitionTargetBox x q).lowerCorner)
            ((partitionTargetBox x q).upperCorner)
  /-- The resolved family uses the selected partition active set. -/
  active_eq : family.activeCharts = selectedPartition.active
  /-- Source charts lie in the oriented boundary atlas. -/
  source_mem :
    forall x, x ∈ family.activeCharts ->
      forall q, q ∈ family.localPieces x ->
        family.sourceChart x q ∈ orientedBoundaryAtlas.charts
  /-- Boundary-source charts lie in the oriented boundary atlas. -/
  boundarySource_mem :
    forall x, x ∈ family.activeCharts ->
      forall q, q ∈ family.localPieces x ->
        family.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts
  /-- Boundary-target charts lie in the oriented boundary atlas. -/
  boundaryTarget_mem :
    forall x, x ∈ family.activeCharts ->
      forall q, q ∈ family.localPieces x ->
        family.boundaryTargetChart x q ∈ orientedBoundaryAtlas.charts

namespace M8TargetImageResolvedInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/-- The global assembly input induced by resolved target-image data. -/
def toAssemblyInput
    (D :
      M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    BoundaryTargetImageToAssemblyInput I omega M BoundaryPiece :=
  BoundaryTargetImageToAssemblyInput.ofResolvedFamily D.family
    D.sourceExtendedBox D.partitionTargetChart D.partitionTargetBox
    D.partitionSelectedBox D.boundaryPartitionTerm
    D.boundaryPartitionTerm_eq

@[simp]
theorem toAssemblyInput_activeCharts
    (D :
      M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    D.toAssemblyInput.activeCharts = D.family.activeCharts :=
  rfl

@[simp]
theorem toAssemblyInput_boundaryPieces
    (D :
      M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    D.toAssemblyInput.boundaryPieces = D.family.localPieces :=
  rfl

@[simp]
theorem toAssemblyInput_boundaryPartitionTerm
    (D :
      M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    D.toAssemblyInput.boundaryPartitionTerm = D.boundaryPartitionTerm :=
  rfl

/-- The target-image family exposed to M8. -/
abbrev targetImages
    (D :
      M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    BoundaryPieceFamilyInput I omega M BoundaryPiece :=
  D.toAssemblyInput.targetImageData.toBoundaryPieceFamilyInput

/-- Resolved target-image data in the exact shape expected by M8. -/
def toM8TargetImageInput
    (D :
      M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece where
  assembly := D.toAssemblyInput
  active_eq := by
    simpa [toAssemblyInput] using D.active_eq
  source_mem := by
    intro x hx q hq
    simpa [toAssemblyInput] using
      D.source_mem x (by simpa [toAssemblyInput] using hx)
        q (by simpa [toAssemblyInput] using hq)
  boundarySource_mem := by
    intro x hx q hq
    simpa [toAssemblyInput] using
      D.boundarySource_mem x (by simpa [toAssemblyInput] using hx)
        q (by simpa [toAssemblyInput] using hq)
  boundaryTarget_mem := by
    intro x hx q hq
    simpa [toAssemblyInput] using
      D.boundaryTarget_mem x (by simpa [toAssemblyInput] using hx)
        q (by simpa [toAssemblyInput] using hq)

@[simp]
theorem toM8TargetImageInput_assembly
    (D :
      M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    D.toM8TargetImageInput.assembly = D.toAssemblyInput :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages
    (D :
      M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    D.toM8TargetImageInput.targetImages = D.targetImages :=
  rfl

@[simp]
theorem toM8TargetImageInput_active
    (D :
      M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    D.toM8TargetImageInput.targetImages.activeCharts =
      selectedPartition.active := by
  simpa using D.toM8TargetImageInput.targetImages_active

/--
Construct an M8 global input by first resolving target-image data to
`M8TargetImageInput`, then calling `M8GlobalStokesInput.ofTargetImageInput`.
-/
def toM8GlobalStokesInput
    [IsManifold I 1 M]
    (D :
      M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
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
  M8GlobalStokesInput.ofTargetImageInput formData orientedBoundaryAtlas
    selectedPartition selectedPartition_supportSet D.toM8TargetImageInput
    measureLocalization
    (by simpa [toM8TargetImageInput, toAssemblyInput] using
      measureLocalization_boundaryTerm)
    artificialFaces artificialFaces_active artificialFaces_pieces
    artificialFaces_term

@[simp]
theorem toM8GlobalStokesInput_targetImages
    [IsManifold I 1 M]
    (D :
      M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
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
    (D.toM8GlobalStokesInput formData selectedPartition_supportSet
      measureLocalization measureLocalization_boundaryTerm artificialFaces
      artificialFaces_active artificialFaces_pieces
      artificialFaces_term).targetImages =
        D.toM8TargetImageInput.targetImages :=
  rfl

end M8TargetImageResolvedInput

namespace BoundaryChartTargetImageResolvedFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/-- Direct constructor from a pure resolved target-image family to the M8 wrapper input. -/
def toM8ResolvedInput
    (F : BoundaryChartTargetImageResolvedFamily I omega M BoundaryPiece)
    (sourceExtendedBox :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          boundaryChartExtendedBox I (F.sourceChart x q)
            (F.boundarySourceChart x q) omega
            (F.sourceLowerCorner x q) (F.sourceUpperCorner x q))
    (partitionTargetChart : M -> BoundaryPiece -> M)
    (partitionTargetBox :
      (x : M) -> (q : BoundaryPiece) ->
        BoundaryChartTargetBoxSelection I
          (F.boundarySourceChart x q) (F.boundaryTargetChart x q)
          (F.targetLowerCorner x q) (F.targetUpperCorner x q))
    (partitionSelectedBox :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          boundaryChartSelectedBox I
            (F.boundaryTargetChart x q) (partitionTargetChart x q) omega
            ((partitionTargetBox x q).lowerCorner)
            ((partitionTargetBox x q).upperCorner))
    (boundaryPartitionTerm : M -> BoundaryPiece -> Real)
    (boundaryPartitionTerm_eq :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          boundaryPartitionTerm x q =
            projectLocalBoundaryIntegral I
              (F.boundaryTargetChart x q) (partitionTargetChart x q) omega
              ((partitionTargetBox x q).lowerCorner)
              ((partitionTargetBox x q).upperCorner))
    (active_eq : F.activeCharts = selectedPartition.active)
    (source_mem :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          F.sourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundarySource_mem :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          F.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundaryTarget_mem :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          F.boundaryTargetChart x q ∈ orientedBoundaryAtlas.charts) :
    M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece where
  family := F
  sourceExtendedBox := sourceExtendedBox
  partitionTargetChart := partitionTargetChart
  partitionTargetBox := partitionTargetBox
  partitionSelectedBox := partitionSelectedBox
  boundaryPartitionTerm := boundaryPartitionTerm
  boundaryPartitionTerm_eq := boundaryPartitionTerm_eq
  active_eq := active_eq
  source_mem := source_mem
  boundarySource_mem := boundarySource_mem
  boundaryTarget_mem := boundaryTarget_mem

/-- Direct constructor from a pure resolved family to `M8TargetImageInput`. -/
def toM8TargetImageInput
    (F : BoundaryChartTargetImageResolvedFamily I omega M BoundaryPiece)
    (sourceExtendedBox :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          boundaryChartExtendedBox I (F.sourceChart x q)
            (F.boundarySourceChart x q) omega
            (F.sourceLowerCorner x q) (F.sourceUpperCorner x q))
    (partitionTargetChart : M -> BoundaryPiece -> M)
    (partitionTargetBox :
      (x : M) -> (q : BoundaryPiece) ->
        BoundaryChartTargetBoxSelection I
          (F.boundarySourceChart x q) (F.boundaryTargetChart x q)
          (F.targetLowerCorner x q) (F.targetUpperCorner x q))
    (partitionSelectedBox :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          boundaryChartSelectedBox I
            (F.boundaryTargetChart x q) (partitionTargetChart x q) omega
            ((partitionTargetBox x q).lowerCorner)
            ((partitionTargetBox x q).upperCorner))
    (boundaryPartitionTerm : M -> BoundaryPiece -> Real)
    (boundaryPartitionTerm_eq :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          boundaryPartitionTerm x q =
            projectLocalBoundaryIntegral I
              (F.boundaryTargetChart x q) (partitionTargetChart x q) omega
              ((partitionTargetBox x q).lowerCorner)
              ((partitionTargetBox x q).upperCorner))
    (active_eq : F.activeCharts = selectedPartition.active)
    (source_mem :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          F.sourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundarySource_mem :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          F.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundaryTarget_mem :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          F.boundaryTargetChart x q ∈ orientedBoundaryAtlas.charts) :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece :=
  (F.toM8ResolvedInput sourceExtendedBox partitionTargetChart
    partitionTargetBox partitionSelectedBox boundaryPartitionTerm
    boundaryPartitionTerm_eq active_eq source_mem boundarySource_mem
    boundaryTarget_mem).toM8TargetImageInput

end BoundaryChartTargetImageResolvedFamily

namespace M8GlobalStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/--
M8 global input constructor that accepts resolved target-image data as one
package and delegates the target-image fields to
`M8GlobalStokesInput.ofTargetImageInput`.
-/
def ofResolvedTargetImageInput
    [IsManifold I 1 M]
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageResolved :
      M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition
        targetImageResolved.toM8TargetImageInput.targetImages)
    (measureLocalization_boundaryTerm :
      targetImageResolved.boundaryPartitionTerm =
        measureLocalization.boundaryPartitionTerm)
    (artificialFaces : ArtificialFaceResolvedData M Unit)
    (artificialFaces_active :
      artificialFaces.activeCharts = selectedPartition.active)
    (artificialFaces_pieces :
      artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (artificialFaces_term :
      artificialFaces.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm) :
    M8GlobalStokesInput I omega BoundaryPiece :=
  targetImageResolved.toM8GlobalStokesInput formData
    selectedPartition_supportSet measureLocalization
    measureLocalization_boundaryTerm artificialFaces artificialFaces_active
    artificialFaces_pieces artificialFaces_term

@[simp]
theorem ofResolvedTargetImageInput_targetImages
    [IsManifold I 1 M]
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageResolved :
      M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition
        targetImageResolved.toM8TargetImageInput.targetImages)
    (measureLocalization_boundaryTerm :
      targetImageResolved.boundaryPartitionTerm =
        measureLocalization.boundaryPartitionTerm)
    (artificialFaces : ArtificialFaceResolvedData M Unit)
    (artificialFaces_active :
      artificialFaces.activeCharts = selectedPartition.active)
    (artificialFaces_pieces :
      artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (artificialFaces_term :
      artificialFaces.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm) :
    (ofResolvedTargetImageInput (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (orientedBoundaryAtlas := orientedBoundaryAtlas)
      (BoundaryPiece := BoundaryPiece)
      formData selectedPartition_supportSet targetImageResolved
      measureLocalization measureLocalization_boundaryTerm artificialFaces
      artificialFaces_active artificialFaces_pieces artificialFaces_term).targetImages =
        targetImageResolved.toM8TargetImageInput.targetImages :=
  rfl

end M8GlobalStokesInput

end TargetImageResolvedToM8Input

end Stokes

end
