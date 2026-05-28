import Stokes.BoundaryChart.OrientationMathlibBridge
import Stokes.Global.OrientedAtlasToM8

/-!
# Mathlib orientation bridges as M8 orientation fields

This file is a global-facing adapter for the pure boundary-chart orientation
bridge in `Stokes.BoundaryChart.OrientationMathlibBridge`.

The future mathlib oriented-atlas object remains abstract.  We only forget it
to the project-local `BoundaryChartOrientedAtlas`, then expose the two
target-image chart membership facts required by `M8GlobalStokesInput`.
-/

noncomputable section

open Set
open scoped BigOperators Manifold Topology

namespace Stokes

section OrientationBridgeToM8

universe u v w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

/--
Global-facing package turning a future mathlib oriented-atlas bridge into the
orientation fields consumed by M8.

The bridge supplies the project-local oriented atlas.  The two membership
fields are intentionally explicit because a selected target-image family may
use only a finite subfamily of the atlas charts.
-/
structure M8OrientationBridgeFields {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (Orient : Type v) where
  /-- A future mathlib oriented-atlas object, exposed through the project bridge. -/
  bridge : BoundaryChartMathlibOrientedAtlasBridge I M Orient
  /-- Source charts of the M8 target-image family lie in the bridge atlas. -/
  source_mem :
    forall x, x ∈ targetImages.activeCharts ->
      forall q, q ∈ targetImages.boundaryPieces x ->
        targetImages.sourceChart x q ∈ bridge.charts
  /-- Boundary-source charts of the M8 target-image family lie in the bridge atlas. -/
  boundarySource_mem :
    forall x, x ∈ targetImages.activeCharts ->
      forall q, q ∈ targetImages.boundaryPieces x ->
        targetImages.boundarySourceChart x q ∈ bridge.charts

namespace M8OrientationBridgeFields

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {Orient : Type v}

/-- The project-local oriented atlas exposed by the external bridge. -/
def orientedBoundaryAtlas
    (D : M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient) :
    BoundaryChartOrientedAtlas I M :=
  D.bridge.toBoundaryChartOrientedAtlas

@[simp]
theorem orientedBoundaryAtlas_charts
    (D : M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient) :
    D.orientedBoundaryAtlas.charts = D.bridge.charts :=
  rfl

/--
The bridge records that boundary chart transitions preserve the boundary face
and tangent directions on natural boundary overlaps.
-/
theorem transitionCompatibleOn_boundarySource
    (D : M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient)
    {x0 x1 : M}
    (hx0 : x0 ∈ D.orientedBoundaryAtlas.charts)
    (hx1 : x1 ∈ D.orientedBoundaryAtlas.charts) :
    boundaryChartTransitionCompatibleOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) := by
  simpa [orientedBoundaryAtlas] using D.bridge.compatibleOn hx0 hx1

/--
The bridge records preservation of the induced boundary orientation on natural
boundary overlaps.
-/
theorem preservesOrientationOn_boundarySource
    (D : M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient)
    {x0 x1 : M}
    (hx0 : x0 ∈ D.orientedBoundaryAtlas.charts)
    (hx1 : x1 ∈ D.orientedBoundaryAtlas.charts) :
    boundaryChartPreservesOrientationOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) := by
  simpa [orientedBoundaryAtlas] using D.bridge.preservesOrientationOn hx0 hx1

/--
Mathlib-orientation bridge data on any subset of a natural boundary overlap.
-/
def orientationMapDataOn_subset
    (D : M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient)
    {x0 x1 : M}
    (hx0 : x0 ∈ D.orientedBoundaryAtlas.charts)
    (hx1 : x1 ∈ D.orientedBoundaryAtlas.charts)
    {s : Set (Fin n -> Real)}
    (hs : s ⊆ boundaryChartTransitionBoundarySource I x0 x1) :
    BoundaryChartOrientationMapDataOn I x0 x1 s :=
  D.bridge.orientationMapDataOn_subset
    (by simpa [orientedBoundaryAtlas] using hx0)
    (by simpa [orientedBoundaryAtlas] using hx1) hs

/-- Mathlib-orientation bridge data on the natural boundary overlap. -/
def orientationMapDataOn_boundarySource
    (D : M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient)
    {x0 x1 : M}
    (hx0 : x0 ∈ D.orientedBoundaryAtlas.charts)
    (hx1 : x1 ∈ D.orientedBoundaryAtlas.charts) :
    BoundaryChartOrientationMapDataOn I x0 x1
      (boundaryChartTransitionBoundarySource I x0 x1) :=
  D.bridge.orientationMapDataOn_boundarySource
    (by simpa [orientedBoundaryAtlas] using hx0)
    (by simpa [orientedBoundaryAtlas] using hx1)

/--
Mathlib-orientation bridge data for the selected source box of one M8 target
boundary piece.
-/
def targetImages_sourceSelectedBoxOrientationMapDataOn
    (D : M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient)
    {x : M} (hx : x ∈ targetImages.activeCharts)
    {q : BoundaryPiece} (hq : q ∈ targetImages.boundaryPieces x) :
    BoundaryChartOrientationMapDataOn I
      (targetImages.sourceChart x q) (targetImages.boundarySourceChart x q)
      (lowerZeroFaceDomain (targetImages.sourceLowerCorner x q)
        (targetImages.sourceUpperCorner x q)) :=
  D.bridge.orientationMapDataOn_selectedBox
    (by simpa [orientedBoundaryAtlas] using
      D.source_mem x hx q hq)
    (by simpa [orientedBoundaryAtlas] using
      D.boundarySource_mem x hx q hq)
    (targetImages.sourceSelectedBox hx hq)

/--
The selected source box of one M8 target boundary piece preserves the induced
boundary orientation.
-/
theorem targetImages_sourceSelectedBox_preservesOrientationOn
    (D : M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient)
    {x : M} (hx : x ∈ targetImages.activeCharts)
    {q : BoundaryPiece} (hq : q ∈ targetImages.boundaryPieces x) :
    boundaryChartPreservesOrientationOn I
      (targetImages.sourceChart x q) (targetImages.boundarySourceChart x q)
      (lowerZeroFaceDomain (targetImages.sourceLowerCorner x q)
        (targetImages.sourceUpperCorner x q)) :=
  boundaryChartPreservesOrientationOn_of_orientationMapDataOn I
    (targetImages.sourceChart x q) (targetImages.boundarySourceChart x q)
    (D.targetImages_sourceSelectedBoxOrientationMapDataOn hx hq)

/--
The selected source box of one M8 target boundary piece is orientation
compatible in the Jacobian-positive sense.
-/
theorem targetImages_sourceSelectedBox_orientationCompatibleOn
    (D : M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient)
    {x : M} (hx : x ∈ targetImages.activeCharts)
    {q : BoundaryPiece} (hq : q ∈ targetImages.boundaryPieces x) :
    boundaryChartOrientationCompatibleOn I
      (targetImages.sourceChart x q) (targetImages.boundarySourceChart x q)
      (lowerZeroFaceDomain (targetImages.sourceLowerCorner x q)
        (targetImages.sourceUpperCorner x q)) :=
  boundaryChartOrientationCompatibleOn_of_orientationMapDataOn I
    (targetImages.sourceChart x q) (targetImages.boundarySourceChart x q)
    (D.targetImages_sourceSelectedBoxOrientationMapDataOn hx hq)

/-- Convert the external orientation bridge package to the M8 target-orientation fields. -/
def toM8TargetOrientationFields
    (D : M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient) :
    M8TargetOrientationFields I omega BoundaryPiece targetImages where
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  source_mem := by
    intro x hx q hq
    simpa [orientedBoundaryAtlas] using D.source_mem x hx q hq
  boundarySource_mem := by
    intro x hx q hq
    simpa [orientedBoundaryAtlas] using D.boundarySource_mem x hx q hq

@[simp]
theorem toM8TargetOrientationFields_orientedBoundaryAtlas
    (D : M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient) :
    D.toM8TargetOrientationFields.orientedBoundaryAtlas =
      D.orientedBoundaryAtlas :=
  rfl

/-- Source-chart membership in the exact field shape consumed by M8. -/
theorem targetImages_source_mem
    (D : M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient) :
    forall x, x ∈ targetImages.activeCharts ->
      forall q, q ∈ targetImages.boundaryPieces x ->
        targetImages.sourceChart x q ∈
          D.toM8TargetOrientationFields.orientedBoundaryAtlas.charts :=
  D.toM8TargetOrientationFields.targetImages_source_mem

/-- Boundary-source chart membership in the exact field shape consumed by M8. -/
theorem targetImages_boundarySource_mem
    (D : M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient) :
    forall x, x ∈ targetImages.activeCharts ->
      forall q, q ∈ targetImages.boundaryPieces x ->
        targetImages.boundarySourceChart x q ∈
          D.toM8TargetOrientationFields.orientedBoundaryAtlas.charts :=
  D.toM8TargetOrientationFields.targetImages_boundarySource_mem

theorem toM8TargetOrientationFields_sourceSelectedBox_preservesOrientationOn
    (D : M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient)
    {x : M} (hx : x ∈ targetImages.activeCharts)
    {q : BoundaryPiece} (hq : q ∈ targetImages.boundaryPieces x) :
    boundaryChartPreservesOrientationOn I
      (targetImages.sourceChart x q) (targetImages.boundarySourceChart x q)
      (lowerZeroFaceDomain (targetImages.sourceLowerCorner x q)
        (targetImages.sourceUpperCorner x q)) :=
  D.targetImages_sourceSelectedBox_preservesOrientationOn hx hq

end M8OrientationBridgeFields

namespace BoundaryChartMathlibOrientedAtlasBridge

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {Orient : Type v}

/-- Package an oriented-atlas bridge and target-image membership facts for M8. -/
def toM8OrientationBridgeFields
    (B : BoundaryChartMathlibOrientedAtlasBridge I M Orient)
    (source_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.sourceChart x q ∈ B.charts)
    (boundarySource_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.boundarySourceChart x q ∈ B.charts) :
    M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient where
  bridge := B
  source_mem := source_mem
  boundarySource_mem := boundarySource_mem

/-- Directly expose an oriented-atlas bridge as M8 target-orientation fields. -/
def toM8TargetOrientationFields
    (B : BoundaryChartMathlibOrientedAtlasBridge I M Orient)
    (source_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.sourceChart x q ∈ B.charts)
    (boundarySource_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.boundarySourceChart x q ∈ B.charts) :
    M8TargetOrientationFields I omega BoundaryPiece targetImages :=
  (B.toM8OrientationBridgeFields source_mem boundarySource_mem).toM8TargetOrientationFields

@[simp]
theorem toM8TargetOrientationFields_orientedBoundaryAtlas
    (B : BoundaryChartMathlibOrientedAtlasBridge I M Orient)
    (source_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.sourceChart x q ∈ B.charts)
    (boundarySource_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.boundarySourceChart x q ∈ B.charts) :
    (B.toM8TargetOrientationFields (omega := omega)
      (BoundaryPiece := BoundaryPiece) (targetImages := targetImages)
      source_mem boundarySource_mem).orientedBoundaryAtlas =
        B.toBoundaryChartOrientedAtlas :=
  rfl

end BoundaryChartMathlibOrientedAtlasBridge

namespace BoundaryChartMathlibOrientedManifoldBridge

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {Orient : Type v}

/--
All-chart oriented-manifold bridges automatically supply the target-image
membership facts required by M8, since their associated atlas has chart set
`univ`.
-/
def toM8OrientationBridgeFields
    (B : BoundaryChartMathlibOrientedManifoldBridge I M Orient) :
    M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient where
  bridge := B.toMathlibOrientedAtlasBridge
  source_mem := by
    intro x hx q hq
    simp [BoundaryChartMathlibOrientedManifoldBridge.toMathlibOrientedAtlasBridge]
  boundarySource_mem := by
    intro x hx q hq
    simp [BoundaryChartMathlibOrientedManifoldBridge.toMathlibOrientedAtlasBridge]

/-- Direct M8 target-orientation fields from an all-chart oriented-manifold bridge. -/
def toM8TargetOrientationFields
    (B : BoundaryChartMathlibOrientedManifoldBridge I M Orient) :
    M8TargetOrientationFields I omega BoundaryPiece targetImages :=
  B.toM8OrientationBridgeFields.toM8TargetOrientationFields

@[simp]
theorem toM8TargetOrientationFields_orientedBoundaryAtlas
    (B : BoundaryChartMathlibOrientedManifoldBridge I M Orient) :
    (B.toM8TargetOrientationFields (omega := omega)
      (BoundaryPiece := BoundaryPiece) (targetImages := targetImages)
      ).orientedBoundaryAtlas =
        B.toMathlibOrientedAtlasBridge.toBoundaryChartOrientedAtlas :=
  rfl

end BoundaryChartMathlibOrientedManifoldBridge

namespace BoundaryChartOrientedAtlas

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

/--
Compatibility constructor for the current project-local oriented atlas.  It
routes through the bridge API with `Unit` external orientation payload.
-/
def toM8OrientationBridgeFields
    (A : BoundaryChartOrientedAtlas I M)
    (source_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.sourceChart x q ∈ A.charts)
    (boundarySource_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.boundarySourceChart x q ∈ A.charts) :
    M8OrientationBridgeFields I omega BoundaryPiece targetImages Unit :=
  A.toMathlibBridge.toM8OrientationBridgeFields
    (by
      intro x hx q hq
      simpa using source_mem x hx q hq)
    (by
      intro x hx q hq
      simpa using boundarySource_mem x hx q hq)

@[simp]
theorem toM8OrientationBridgeFields_orientedBoundaryAtlas
    (A : BoundaryChartOrientedAtlas I M)
    (source_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.sourceChart x q ∈ A.charts)
    (boundarySource_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.boundarySourceChart x q ∈ A.charts) :
    (A.toM8OrientationBridgeFields (omega := omega)
      (BoundaryPiece := BoundaryPiece) (targetImages := targetImages)
      source_mem boundarySource_mem).orientedBoundaryAtlas = A := by
  rfl

/--
Compatibility constructor for the current project-local oriented atlas as the
orientation package consumed directly by M8.
-/
def toM8TargetOrientationFields
    (A : BoundaryChartOrientedAtlas I M)
    (source_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.sourceChart x q ∈ A.charts)
    (boundarySource_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.boundarySourceChart x q ∈ A.charts) :
    M8TargetOrientationFields I omega BoundaryPiece targetImages :=
  (A.toM8OrientationBridgeFields source_mem boundarySource_mem).toM8TargetOrientationFields

@[simp]
theorem toM8TargetOrientationFields_orientedBoundaryAtlas
    (A : BoundaryChartOrientedAtlas I M)
    (source_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.sourceChart x q ∈ A.charts)
    (boundarySource_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.boundarySourceChart x q ∈ A.charts) :
    (A.toM8TargetOrientationFields (omega := omega)
      (BoundaryPiece := BoundaryPiece) (targetImages := targetImages)
      source_mem boundarySource_mem).orientedBoundaryAtlas = A := by
  rfl

end BoundaryChartOrientedAtlas

namespace M8GlobalStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {Orient : Type v}

/--
Constructor for `M8GlobalStokesInput` that takes its orientation data from a
future mathlib oriented-atlas bridge package.
-/
def ofOrientationBridgeFields
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
      M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient)
    (targetBoundaryTerm_eq_partition :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBoundaryTerm targetImages x q =
            measureLocalization.boundaryPartitionTerm x q) :
    M8GlobalStokesInput I omega BoundaryPiece :=
  M8GlobalStokesInput.ofTargetOrientationFields
    formData selectedPartition selectedPartition_supportSet
    targetImages targetImages_active measureLocalization
    artificialFaces artificialFaces_active artificialFaces_pieces
    artificialFaces_term targetOrientation.toM8TargetOrientationFields
    targetBoundaryTerm_eq_partition

@[simp]
theorem ofOrientationBridgeFields_orientedBoundaryAtlas
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
      M8OrientationBridgeFields I omega BoundaryPiece targetImages Orient)
    (targetBoundaryTerm_eq_partition :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBoundaryTerm targetImages x q =
            measureLocalization.boundaryPartitionTerm x q) :
    (ofOrientationBridgeFields (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece)
      formData selectedPartition selectedPartition_supportSet
      targetImages targetImages_active measureLocalization
      artificialFaces artificialFaces_active artificialFaces_pieces
      artificialFaces_term targetOrientation
      targetBoundaryTerm_eq_partition).orientedBoundaryAtlas =
        targetOrientation.toM8TargetOrientationFields.orientedBoundaryAtlas :=
  rfl

end M8GlobalStokesInput

end OrientationBridgeToM8

end Stokes

end
