import Stokes.BoundaryChart.ControlledTargetBoxFromLocalInverseAuto
import Stokes.BoundaryChart.TargetBoxToM8Glue
import Stokes.Global.TargetImageResolvedToM8Input

/-!
# Controlled boundary target boxes as M8 input

This file is a global glue layer for the controlled-target-box route.

The pure boundary-chart layer now provides
`BoundaryChartControlledTargetBoxSelectionData`: one chosen later target box
with compact-image and local-inverse data, together with the fact that it
contains the selected target image box.  M8 does not want those pointwise
fields directly; it wants a resolved target-image family and then the standard
`M8TargetImageInput` / `M8GlobalStokesInput` packages.

The definitions below package that conversion.  No new analysis is proved
here: all geometric content stays in the controlled target data and in the
already existing target-image-to-M8 constructors.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section BoundaryControlledTargetToM8Auto

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {Piece : Type p}

/--
A finite boundary target-image family whose target boxes are supplied by the
controlled-target-box API.

The selected target corners are retained as audit data, while the actual M8
target-image box is the controlled later target box.  Thus downstream M8
constructors consume `controlledTarget.targetBoxSelection` and no longer need
the compact-image/local-inverse halves as naked arguments.
-/
structure BoundaryChartControlledTargetImageFamily {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n) (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in this boundary target-image family. -/
  activeCharts : Finset Chart
  /-- Finite local boundary pieces attached to each active chart label. -/
  localPieces : Chart -> Finset Piece
  /-- Source chart for the original boundary chart integral. -/
  sourceChart : Chart -> Piece -> M
  /-- Boundary chart reached from the source chart by the target-image COV. -/
  boundarySourceChart : Chart -> Piece -> M
  /-- Auxiliary target chart used for the transported boundary integral. -/
  boundaryTargetChart : Chart -> Piece -> M
  /-- Source lower corner. -/
  sourceLowerCorner : Chart -> Piece -> Fin (n + 1) -> Real
  /-- Source upper corner. -/
  sourceUpperCorner : Chart -> Piece -> Fin (n + 1) -> Real
  /-- Selected target-image lower corner contained in the controlled target. -/
  selectedTargetLowerCorner : Chart -> Piece -> Fin (n + 1) -> Real
  /-- Selected target-image upper corner contained in the controlled target. -/
  selectedTargetUpperCorner : Chart -> Piece -> Fin (n + 1) -> Real
  /-- Target point around which the controlled target was selected. -/
  targetPoint : Chart -> Piece -> Fin n -> Real
  /-- Target-side set in which the controlled later target box lies. -/
  targetSet : Chart -> Piece -> Set (Fin n -> Real)
  /-- Controlled target-box data for every family entry. -/
  controlledTarget :
    forall x q,
      BoundaryChartControlledTargetBoxSelectionData I
        (sourceChart x q) (boundarySourceChart x q)
        (sourceLowerCorner x q) (sourceUpperCorner x q)
        (selectedTargetLowerCorner x q) (selectedTargetUpperCorner x q)
        (targetPoint x q) (targetSet x q)
  /-- Selected source boundary boxes on active pieces. -/
  sourceSelectedBox :
    forall x, x ∈ activeCharts ->
      forall q, q ∈ localPieces x ->
        boundaryChartSelectedBox I (sourceChart x q)
          (boundarySourceChart x q) omega
          (sourceLowerCorner x q) (sourceUpperCorner x q)
  /--
  Selected auxiliary target boxes on the controlled target boxes.  This is the
  second chart change used by the boundary partition endpoint.
  -/
  targetSelectedBox :
    forall x, x ∈ activeCharts ->
      forall q, q ∈ localPieces x ->
        boundaryChartSelectedBox I (boundarySourceChart x q)
          (boundaryTargetChart x q) omega
          ((controlledTarget x q).laterLowerCorner)
          ((controlledTarget x q).laterUpperCorner)

namespace BoundaryChartControlledTargetImageFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/-- The controlled target-box selection used as the resolved target box. -/
def targetBoxSelection
    (F : BoundaryChartControlledTargetImageFamily I omega Chart Piece)
    (x : Chart) (q : Piece) :
    BoundaryChartTargetBoxSelection I (F.sourceChart x q)
      (F.boundarySourceChart x q)
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q) :=
  (F.controlledTarget x q).targetBoxSelection

/-- Lower corner of the M8-facing controlled target box. -/
def targetLowerCorner
    (F : BoundaryChartControlledTargetImageFamily I omega Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) -> Real :=
  (F.controlledTarget x q).laterLowerCorner

/-- Upper corner of the M8-facing controlled target box. -/
def targetUpperCorner
    (F : BoundaryChartControlledTargetImageFamily I omega Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) -> Real :=
  (F.controlledTarget x q).laterUpperCorner

/-- The selected target-image box is contained in the controlled M8 target. -/
theorem selectedTarget_subset_target
    (F : BoundaryChartControlledTargetImageFamily I omega Chart Piece)
    (x : Chart) (q : Piece) :
    lowerZeroFaceDomain (F.selectedTargetLowerCorner x q)
        (F.selectedTargetUpperCorner x q) ⊆
      lowerZeroFaceDomain (F.targetLowerCorner x q)
        (F.targetUpperCorner x q) := by
  simpa [targetLowerCorner, targetUpperCorner] using
    (F.controlledTarget x q).selectedTarget_subset_laterTarget

/-- The chosen target point lies in the controlled M8 target box. -/
theorem targetPoint_mem
    (F : BoundaryChartControlledTargetImageFamily I omega Chart Piece)
    (x : Chart) (q : Piece) :
    F.targetPoint x q ∈
      lowerZeroFaceDomain (F.targetLowerCorner x q)
        (F.targetUpperCorner x q) := by
  simpa [targetLowerCorner, targetUpperCorner] using
    (F.controlledTarget x q).targetPoint_mem

/-- The controlled M8 target box lies in the recorded target-side set. -/
theorem target_subset_set
    (F : BoundaryChartControlledTargetImageFamily I omega Chart Piece)
    (x : Chart) (q : Piece) :
    lowerZeroFaceDomain (F.targetLowerCorner x q)
        (F.targetUpperCorner x q) ⊆
      F.targetSet x q := by
  simpa [targetLowerCorner, targetUpperCorner] using
    (F.controlledTarget x q).laterTarget_subset_set

/-- Image data supplied by the controlled target box. -/
theorem imageData
    (F : BoundaryChartControlledTargetImageFamily I omega Chart Piece)
    (x : Chart) (q : Piece) :
    boundaryChartSelectedBoxImageData I (F.sourceChart x q)
      (F.boundarySourceChart x q)
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x q) (F.targetUpperCorner x q) := by
  simpa [targetLowerCorner, targetUpperCorner] using
    (F.controlledTarget x q).imageData

/-- One active piece as selected-box target-image auto data. -/
def selectedBoxTargetImageAutoData
    (F : BoundaryChartControlledTargetImageFamily I omega Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    BoundaryChartSelectedBoxTargetImageAutoData I
      (F.sourceChart x q) (F.boundarySourceChart x q) omega
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q) :=
  (F.controlledTarget x q).toSelectedBoxTargetImageAutoData
    (F.sourceSelectedBox x hx q hq)

@[simp]
theorem selectedBoxTargetImageAutoData_targetLowerCorner
    (F : BoundaryChartControlledTargetImageFamily I omega Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    (F.selectedBoxTargetImageAutoData x hx q hq).targetLowerCorner =
      F.targetLowerCorner x q := by
  rfl

@[simp]
theorem selectedBoxTargetImageAutoData_targetUpperCorner
    (F : BoundaryChartControlledTargetImageFamily I omega Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    (F.selectedBoxTargetImageAutoData x hx q hq).targetUpperCorner =
      F.targetUpperCorner x q := by
  rfl

/-- Resolved target-image family consumed by the existing global/M8 adapters. -/
def toTargetImageResolvedFamily
    (F : BoundaryChartControlledTargetImageFamily I omega Chart Piece) :
    BoundaryChartTargetImageResolvedFamily I omega Chart Piece where
  activeCharts := F.activeCharts
  localPieces := F.localPieces
  sourceChart := F.sourceChart
  boundarySourceChart := F.boundarySourceChart
  boundaryTargetChart := F.boundaryTargetChart
  sourceLowerCorner := F.sourceLowerCorner
  sourceUpperCorner := F.sourceUpperCorner
  sourceSelectedBox := F.sourceSelectedBox
  targetBox := F.targetBoxSelection
  targetSelectedBox := by
    intro x hx q hq
    simpa [targetBoxSelection] using F.targetSelectedBox x hx q hq

@[simp]
theorem toTargetImageResolvedFamily_activeCharts
    (F : BoundaryChartControlledTargetImageFamily I omega Chart Piece) :
    F.toTargetImageResolvedFamily.activeCharts = F.activeCharts :=
  rfl

@[simp]
theorem toTargetImageResolvedFamily_localPieces
    (F : BoundaryChartControlledTargetImageFamily I omega Chart Piece) :
    F.toTargetImageResolvedFamily.localPieces = F.localPieces :=
  rfl

@[simp]
theorem toTargetImageResolvedFamily_targetBox
    (F : BoundaryChartControlledTargetImageFamily I omega Chart Piece)
    (x : Chart) (q : Piece) :
    F.toTargetImageResolvedFamily.targetBox x q =
      F.targetBoxSelection x q :=
  rfl

/--
Global fields needed to turn a controlled target-image family into the M8
resolved target-image input.

The lower boundary-chart target data are now a single `family` value.  The
remaining fields are exactly the global assembly data: source extended boxes,
boundary-partition endpoint boxes, active-set alignment, and oriented-atlas
membership.
-/
structure M8ResolvedFields
    (F : BoundaryChartControlledTargetImageFamily I omega M Piece)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M) where
  /-- Extended source boxes needed by local boundary Stokes. -/
  sourceExtendedBox :
    forall x, x ∈ F.toTargetImageResolvedFamily.activeCharts ->
      forall q, q ∈ F.toTargetImageResolvedFamily.localPieces x ->
        boundaryChartExtendedBox I
          (F.toTargetImageResolvedFamily.sourceChart x q)
          (F.toTargetImageResolvedFamily.boundarySourceChart x q) omega
          (F.toTargetImageResolvedFamily.sourceLowerCorner x q)
          (F.toTargetImageResolvedFamily.sourceUpperCorner x q)
  /-- Chart used for the selected boundary-partition representative. -/
  partitionTargetChart : M -> Piece -> M
  /-- Target-box selection for the final boundary-partition representative. -/
  partitionTargetBox :
    (x : M) -> (q : Piece) ->
      BoundaryChartTargetBoxSelection I
        (F.toTargetImageResolvedFamily.boundarySourceChart x q)
        (F.toTargetImageResolvedFamily.boundaryTargetChart x q)
        (F.toTargetImageResolvedFamily.targetLowerCorner x q)
        (F.toTargetImageResolvedFamily.targetUpperCorner x q)
  /-- Selected auxiliary target box for the final boundary-partition representative. -/
  partitionSelectedBox :
    forall x, x ∈ F.toTargetImageResolvedFamily.activeCharts ->
      forall q, q ∈ F.toTargetImageResolvedFamily.localPieces x ->
        boundaryChartSelectedBox I
          (F.toTargetImageResolvedFamily.boundaryTargetChart x q)
          (partitionTargetChart x q) omega
          ((partitionTargetBox x q).lowerCorner)
          ((partitionTargetBox x q).upperCorner)
  /-- Boundary partition term used by global reconstruction. -/
  boundaryPartitionTerm : M -> Piece -> Real
  /-- Endpoint identification for the selected boundary partition term. -/
  boundaryPartitionTerm_eq :
    forall x, x ∈ F.toTargetImageResolvedFamily.activeCharts ->
      forall q, q ∈ F.toTargetImageResolvedFamily.localPieces x ->
        boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I
            (F.toTargetImageResolvedFamily.boundaryTargetChart x q)
            (partitionTargetChart x q) omega
            ((partitionTargetBox x q).lowerCorner)
            ((partitionTargetBox x q).upperCorner)
  /-- The controlled family uses the selected partition active set. -/
  active_eq :
    F.toTargetImageResolvedFamily.activeCharts = selectedPartition.active
  /-- Source charts lie in the oriented boundary atlas. -/
  source_mem :
    forall x, x ∈ F.toTargetImageResolvedFamily.activeCharts ->
      forall q, q ∈ F.toTargetImageResolvedFamily.localPieces x ->
        F.toTargetImageResolvedFamily.sourceChart x q ∈
          orientedBoundaryAtlas.charts
  /-- Boundary-source charts lie in the oriented boundary atlas. -/
  boundarySource_mem :
    forall x, x ∈ F.toTargetImageResolvedFamily.activeCharts ->
      forall q, q ∈ F.toTargetImageResolvedFamily.localPieces x ->
        F.toTargetImageResolvedFamily.boundarySourceChart x q ∈
          orientedBoundaryAtlas.charts
  /-- Boundary-target charts lie in the oriented boundary atlas. -/
  boundaryTarget_mem :
    forall x, x ∈ F.toTargetImageResolvedFamily.activeCharts ->
      forall q, q ∈ F.toTargetImageResolvedFamily.localPieces x ->
        F.toTargetImageResolvedFamily.boundaryTargetChart x q ∈
          orientedBoundaryAtlas.charts

namespace M8ResolvedFields

variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
variable {F : BoundaryChartControlledTargetImageFamily I omega M Piece}

/-- The packaged fields as the existing M8 resolved target-image input. -/
def toM8ResolvedInput
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas Piece :=
  F.toTargetImageResolvedFamily.toM8ResolvedInput D.sourceExtendedBox
    D.partitionTargetChart D.partitionTargetBox D.partitionSelectedBox
    D.boundaryPartitionTerm D.boundaryPartitionTerm_eq D.active_eq
    D.source_mem D.boundarySource_mem D.boundaryTarget_mem

/-- The packaged fields as the final `M8TargetImageInput`. -/
def toM8TargetImageInput
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas Piece :=
  D.toM8ResolvedInput.toM8TargetImageInput

@[simp]
theorem toM8ResolvedInput_family
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    D.toM8ResolvedInput.family = F.toTargetImageResolvedFamily :=
  rfl

@[simp]
theorem toM8ResolvedInput_boundaryPartitionTerm
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    D.toM8ResolvedInput.boundaryPartitionTerm =
      D.boundaryPartitionTerm :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    D.toM8TargetImageInput.targetImages =
      D.toM8ResolvedInput.toM8TargetImageInput.targetImages :=
  rfl

/-- Direct M8 global input constructor from controlled target-image fields. -/
def toM8GlobalStokesInput
    [IsManifold I 1 M]
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas)
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition
        D.toM8TargetImageInput.targetImages)
    (measureLocalization_boundaryTerm :
      D.boundaryPartitionTerm =
        measureLocalization.boundaryPartitionTerm)
    (artificialFaces : ArtificialFaceResolvedData M Unit)
    (artificialFaces_active :
      artificialFaces.activeCharts = selectedPartition.active)
    (artificialFaces_pieces :
      artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (artificialFaces_term :
      artificialFaces.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm) :
    M8GlobalStokesInput I omega Piece :=
  D.toM8ResolvedInput.toM8GlobalStokesInput formData
    selectedPartition_supportSet measureLocalization
    (by simpa [toM8ResolvedInput] using measureLocalization_boundaryTerm)
    artificialFaces artificialFaces_active artificialFaces_pieces
    artificialFaces_term

end M8ResolvedFields

end BoundaryChartControlledTargetImageFamily

/--
One M8-facing package whose target-image component is a controlled target-image
family plus the global fields needed to assemble it.
-/
structure M8BoundaryControlledTargetInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (BoundaryPiece : Type p) where
  /-- Controlled boundary target-image family. -/
  family : BoundaryChartControlledTargetImageFamily I omega M BoundaryPiece
  /-- Global assembly fields for the controlled family. -/
  fields :
    family.M8ResolvedFields selectedPartition orientedBoundaryAtlas

namespace M8BoundaryControlledTargetInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
variable {BoundaryPiece : Type p}

/-- Forget the controlled source to the existing M8 resolved target-image input. -/
def toM8ResolvedInput
    (D :
      M8BoundaryControlledTargetInput I omega selectedPartition
        orientedBoundaryAtlas BoundaryPiece) :
    M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece :=
  D.fields.toM8ResolvedInput

/-- Controlled target-image data in the exact target-image shape consumed by M8. -/
def toM8TargetImageInput
    (D :
      M8BoundaryControlledTargetInput I omega selectedPartition
        orientedBoundaryAtlas BoundaryPiece) :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece :=
  D.fields.toM8TargetImageInput

@[simp]
theorem toM8ResolvedInput_family
    (D :
      M8BoundaryControlledTargetInput I omega selectedPartition
        orientedBoundaryAtlas BoundaryPiece) :
    D.toM8ResolvedInput.family = D.family.toTargetImageResolvedFamily :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages
    (D :
      M8BoundaryControlledTargetInput I omega selectedPartition
        orientedBoundaryAtlas BoundaryPiece) :
    D.toM8TargetImageInput.targetImages =
      D.toM8ResolvedInput.toM8TargetImageInput.targetImages :=
  rfl

/-- Direct M8 global input constructor from the controlled target package. -/
def toM8GlobalStokesInput
    [IsManifold I 1 M]
    (D :
      M8BoundaryControlledTargetInput I omega selectedPartition
        orientedBoundaryAtlas BoundaryPiece)
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition
        D.toM8TargetImageInput.targetImages)
    (measureLocalization_boundaryTerm :
      D.fields.boundaryPartitionTerm =
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
  D.fields.toM8GlobalStokesInput formData selectedPartition_supportSet
    measureLocalization measureLocalization_boundaryTerm artificialFaces
    artificialFaces_active artificialFaces_pieces artificialFaces_term

/-- Measure-level Stokes theorem obtained from the controlled target package. -/
theorem stokes
    [IsManifold I 1 M]
    (D :
      M8BoundaryControlledTargetInput I omega selectedPartition
        orientedBoundaryAtlas BoundaryPiece)
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition
        D.toM8TargetImageInput.targetImages)
    (measureLocalization_boundaryTerm :
      D.fields.boundaryPartitionTerm =
        measureLocalization.boundaryPartitionTerm)
    (artificialFaces : ArtificialFaceResolvedData M Unit)
    (artificialFaces_active :
      artificialFaces.activeCharts = selectedPartition.active)
    (artificialFaces_pieces :
      artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (artificialFaces_term :
      artificialFaces.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm) :
    measureLocalization.bulkMeasureIntegral =
      measureLocalization.boundaryMeasureIntegral :=
  (D.toM8GlobalStokesInput formData selectedPartition_supportSet
    measureLocalization measureLocalization_boundaryTerm artificialFaces
    artificialFaces_active artificialFaces_pieces artificialFaces_term).stokes

end M8BoundaryControlledTargetInput

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/--
Source-shrink/open-partial-homeomorphism families induce controlled target-image
families by using the source-shrink target itself as the controlled target.
-/
def toControlledTargetImageFamily
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega Chart Piece) :
    BoundaryChartControlledTargetImageFamily I omega Chart Piece where
  activeCharts := F.activeCharts
  localPieces := F.localPieces
  sourceChart := F.sourceChart
  boundarySourceChart := F.boundarySourceChart
  boundaryTargetChart := F.boundaryTargetChart
  sourceLowerCorner := F.sourceLowerCorner
  sourceUpperCorner := F.sourceUpperCorner
  selectedTargetLowerCorner := F.targetLowerCorner
  selectedTargetUpperCorner := F.targetUpperCorner
  targetPoint := F.targetPoint
  targetSet := fun x q =>
    lowerZeroFaceDomain (F.ambientTargetLowerCorner x q)
      (F.ambientTargetUpperCorner x q)
  controlledTarget := fun x q =>
    (F.shrinkData x q).toControlledTargetBoxSelectionInAmbient
  sourceSelectedBox := by
    intro x hx q hq
    simpa [sourceLowerCorner, sourceUpperCorner] using
      F.sourceSelectedBox x hx q hq
  targetSelectedBox := by
    intro x hx q hq
    simpa [targetLowerCorner, targetUpperCorner,
      BoundaryChartSourceShrinkOpenPartialHomeomorphData.toControlledTargetBoxSelectionInAmbient,
      BoundaryChartSourceShrinkOpenPartialHomeomorphData.toControlledTargetBoxSelectionSelf,
      BoundaryChartTargetBoxSelection.toControlledTargetBoxSelectionSelf,
      BoundaryChartControlledTargetBoxSelectionData.ofTargetBoxSelection] using
      F.targetSelectedBox x hx q hq

@[simp]
theorem toControlledTargetImageFamily_activeCharts
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega Chart Piece) :
    F.toControlledTargetImageFamily.activeCharts = F.activeCharts :=
  rfl

@[simp]
theorem toControlledTargetImageFamily_localPieces
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega Chart Piece) :
    F.toControlledTargetImageFamily.localPieces = F.localPieces :=
  rfl

@[simp]
theorem toControlledTargetImageFamily_targetBoxSelection
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega Chart Piece)
    (x : Chart) (q : Piece) :
    F.toControlledTargetImageFamily.targetBoxSelection x q =
      F.targetBoxSelection x q :=
  rfl

@[simp]
theorem toControlledTargetImageFamily_resolvedFamily
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega Chart Piece) :
    F.toControlledTargetImageFamily.toTargetImageResolvedFamily =
      F.toTargetImageResolvedFamily :=
  rfl

end BoundaryChartSourceShrinkOpenPartialHomeomorphFamily

end BoundaryControlledTargetToM8Auto

end Stokes

end
