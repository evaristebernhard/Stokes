import Stokes.BoundaryChart.TargetBoxSourceShrinkIFT
import Stokes.BoundaryChart.TargetImageSelectedBoxBuilder
import Stokes.Global.TargetImageResolvedToM8Input

/-!
# Source-shrink target boxes as target-image / M8 input

This file is a small adapter layer.  The source-shrink/IFT route produces
`BoundaryChartSourceShrinkOpenPartialHomeomorphData`, whose main downstream
payload is a `BoundaryChartTargetBoxSelection` for the shrunken source box.

The selected-box and M8 pipelines consume the same payload through
`BoundaryChartSelectedBoxTargetImageAutoData` or
`BoundaryChartTargetImageResolvedFamily`.  The constructors below make that
route explicit without proving new geometry.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section ManifoldBoundary

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace BoundaryChartSourceShrinkMapsToData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {x0 x1 : M} {omega : ManifoldForm I M n}
variable {a b c d e f : Fin (n + 1) -> Real} {u y : Fin n -> Real}

/--
Selected-box auto data from source-shrink maps-to data plus a named continuous
local inverse on the same target box.
-/
def toSelectedBoxTargetImageAutoDataOfContinuousLocalInverse
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b e f u)
    (he0 : e 0 = 0) (hle : e <= f)
    (hy : y ∈ lowerZeroFaceDomain e f)
    (hsubset : lowerZeroFaceDomain e f ⊆ lowerZeroFaceDomain c d)
    (G :
      BoundaryChartContinuousLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner e f y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 omega
        D.sourceLowerCorner D.sourceUpperCorner) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 omega
      D.sourceLowerCorner D.sourceUpperCorner :=
  BoundaryChartSelectedBoxTargetImageAutoData.ofTargetBoxSelection hbox
    (D.toInverseTargetBoxDataOfContinuousLocalInverse
      he0 hle hy hsubset G).targetBoxSelection

/-- The auto-data target box is the one produced by the source-shrink route. -/
@[simp]
theorem toSelectedBoxTargetImageAutoDataOfContinuousLocalInverse_targetBox
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b e f u)
    (he0 : e 0 = 0) (hle : e <= f)
    (hy : y ∈ lowerZeroFaceDomain e f)
    (hsubset : lowerZeroFaceDomain e f ⊆ lowerZeroFaceDomain c d)
    (G :
      BoundaryChartContinuousLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner e f y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 omega
        D.sourceLowerCorner D.sourceUpperCorner) :
    (D.toSelectedBoxTargetImageAutoDataOfContinuousLocalInverse
      he0 hle hy hsubset G hbox).targetBox =
      (D.toInverseTargetBoxDataOfContinuousLocalInverse
        he0 hle hy hsubset G).targetBoxSelection :=
  rfl

/-- Image data exposed through the selected-box builder API. -/
theorem selectedBoxTargetImageAutoData_imageData_of_continuousLocalInverse
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b e f u)
    (he0 : e 0 = 0) (hle : e <= f)
    (hy : y ∈ lowerZeroFaceDomain e f)
    (hsubset : lowerZeroFaceDomain e f ⊆ lowerZeroFaceDomain c d)
    (G :
      BoundaryChartContinuousLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner e f y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 omega
        D.sourceLowerCorner D.sourceUpperCorner) :
    boundaryChartSelectedBoxImageData I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner e f :=
  (D.toSelectedBoxTargetImageAutoDataOfContinuousLocalInverse
    he0 hle hy hsubset G hbox).imageData

end BoundaryChartSourceShrinkMapsToData

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {x0 x1 : M} {omega : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) -> Real} {u y : Fin n -> Real}

/-- Target lower corner of the produced target-box selection. -/
@[simp]
theorem targetBoxSelection_lowerCorner
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y) :
    D.targetBoxSelection.lowerCorner = D.targetLowerCorner :=
  rfl

/-- Target upper corner of the produced target-box selection. -/
@[simp]
theorem targetBoxSelection_upperCorner
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y) :
    D.targetBoxSelection.upperCorner = D.targetUpperCorner :=
  rfl

/-- The synchronized local-homeomorphism data as selected-box auto data. -/
def toSelectedBoxTargetImageAutoData
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 omega
        D.sourceLowerCorner D.sourceUpperCorner) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 omega
      D.sourceLowerCorner D.sourceUpperCorner :=
  BoundaryChartSelectedBoxTargetImageAutoData.ofTargetBoxSelection hbox
    D.targetBoxSelection

/-- The selected-box auto data keeps the source selected box. -/
@[simp]
theorem toSelectedBoxTargetImageAutoData_selectedBox
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 omega
        D.sourceLowerCorner D.sourceUpperCorner) :
    (D.toSelectedBoxTargetImageAutoData hbox).selectedBox = hbox :=
  rfl

/-- The selected-box auto data keeps the source-shrink target box. -/
@[simp]
theorem toSelectedBoxTargetImageAutoData_targetBox
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 omega
        D.sourceLowerCorner D.sourceUpperCorner) :
    (D.toSelectedBoxTargetImageAutoData hbox).targetBox =
      D.targetBoxSelection :=
  rfl

/-- Image data exposed through the selected-box builder API. -/
theorem selectedBoxTargetImageAutoData_imageData
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 omega
        D.sourceLowerCorner D.sourceUpperCorner) :
    boundaryChartSelectedBoxImageData I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner
      D.targetLowerCorner D.targetUpperCorner := by
  simpa using (D.toSelectedBoxTargetImageAutoData hbox).imageData

/-- Local inverse data exposed through the selected-box builder API. -/
theorem selectedBoxTargetImageAutoData_localInverse
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 omega
        D.sourceLowerCorner D.sourceUpperCorner) :
    boundaryChartLocalInverseData I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner
      D.targetLowerCorner D.targetUpperCorner := by
  simpa using (D.toSelectedBoxTargetImageAutoData hbox).targetBox.localInverse

end BoundaryChartSourceShrinkOpenPartialHomeomorphData

/--
Family-level target-image input built from source-shrink local-homeomorphism
data.

The ambient source/target boxes are audit data for the source-shrink step.  The
resolved target-image family below exposes the selected shrunken source box and
the selected target box carried by `shrinkData`.
-/
structure BoundaryChartSourceShrinkOpenPartialHomeomorphFamily {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n) (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in this target-image family. -/
  activeCharts : Finset Chart
  /-- Finite local boundary pieces attached to each active chart label. -/
  localPieces : Chart -> Finset Piece
  /-- Source chart for the original boundary chart integral. -/
  sourceChart : Chart -> Piece -> M
  /-- Boundary chart reached from the source chart by the target-image COV. -/
  boundarySourceChart : Chart -> Piece -> M
  /-- Auxiliary target chart used for the transported boundary integral. -/
  boundaryTargetChart : Chart -> Piece -> M
  /-- Ambient source lower corner before source shrinking. -/
  ambientSourceLowerCorner : Chart -> Piece -> Fin (n + 1) -> Real
  /-- Ambient source upper corner before source shrinking. -/
  ambientSourceUpperCorner : Chart -> Piece -> Fin (n + 1) -> Real
  /-- Ambient target lower corner before target shrinking. -/
  ambientTargetLowerCorner : Chart -> Piece -> Fin (n + 1) -> Real
  /-- Ambient target upper corner before target shrinking. -/
  ambientTargetUpperCorner : Chart -> Piece -> Fin (n + 1) -> Real
  /-- Source point around which the source box was shrunk. -/
  sourcePoint : Chart -> Piece -> Fin n -> Real
  /-- Target point around which the target box was selected. -/
  targetPoint : Chart -> Piece -> Fin n -> Real
  /-- Source-shrink / local-homeomorphism data for every family entry. -/
  shrinkData :
    forall x q,
      BoundaryChartSourceShrinkOpenPartialHomeomorphData I
        (sourceChart x q) (boundarySourceChart x q)
        (ambientSourceLowerCorner x q) (ambientSourceUpperCorner x q)
        (ambientTargetLowerCorner x q) (ambientTargetUpperCorner x q)
        (sourcePoint x q) (targetPoint x q)
  /-- Selected source boundary boxes on active shrunken pieces. -/
  sourceSelectedBox :
    forall x, x ∈ activeCharts ->
      forall q, q ∈ localPieces x ->
        boundaryChartSelectedBox I (sourceChart x q) (boundarySourceChart x q) omega
          ((shrinkData x q).sourceLowerCorner)
          ((shrinkData x q).sourceUpperCorner)
  /-- Selected auxiliary target boxes on active target-image pieces. -/
  targetSelectedBox :
    forall x, x ∈ activeCharts ->
      forall q, q ∈ localPieces x ->
        boundaryChartSelectedBox I (boundarySourceChart x q) (boundaryTargetChart x q)
          omega ((shrinkData x q).targetLowerCorner)
            ((shrinkData x q).targetUpperCorner)

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Lower corner of the selected shrunken source box. -/
def sourceLowerCorner
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) -> Real :=
  (F.shrinkData x q).sourceLowerCorner

/-- Upper corner of the selected shrunken source box. -/
def sourceUpperCorner
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) -> Real :=
  (F.shrinkData x q).sourceUpperCorner

/-- Lower corner of the selected target box. -/
def targetLowerCorner
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) -> Real :=
  (F.shrinkData x q).targetLowerCorner

/-- Upper corner of the selected target box. -/
def targetUpperCorner
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) -> Real :=
  (F.shrinkData x q).targetUpperCorner

/-- Target-box selection produced by the source-shrink route. -/
def targetBoxSelection
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega Chart Piece)
    (x : Chart) (q : Piece) :
    BoundaryChartTargetBoxSelection I (F.sourceChart x q) (F.boundarySourceChart x q)
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q) :=
  (F.shrinkData x q).targetBoxSelection

/-- One active source-shrink piece as selected-box target-image auto data. -/
def selectedBoxTargetImageAutoData
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    BoundaryChartSelectedBoxTargetImageAutoData I
      (F.sourceChart x q) (F.boundarySourceChart x q) omega
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q) :=
  (F.shrinkData x q).toSelectedBoxTargetImageAutoData
    (by simpa [sourceLowerCorner, sourceUpperCorner] using
      F.sourceSelectedBox x hx q hq)

/-- Resolved target-image family consumed by the existing global/M8 adapters. -/
def toTargetImageResolvedFamily
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega Chart Piece) :
    BoundaryChartTargetImageResolvedFamily I omega Chart Piece where
  activeCharts := F.activeCharts
  localPieces := F.localPieces
  sourceChart := F.sourceChart
  boundarySourceChart := F.boundarySourceChart
  boundaryTargetChart := F.boundaryTargetChart
  sourceLowerCorner := F.sourceLowerCorner
  sourceUpperCorner := F.sourceUpperCorner
  sourceSelectedBox := by
    intro x hx q hq
    simpa [sourceLowerCorner, sourceUpperCorner] using
      F.sourceSelectedBox x hx q hq
  targetBox := F.targetBoxSelection
  targetSelectedBox := by
    intro x hx q hq
    simpa [targetBoxSelection, targetLowerCorner, targetUpperCorner] using
      F.targetSelectedBox x hx q hq

/-- The resolved-family target box is exactly the source-shrink target box. -/
@[simp]
theorem toTargetImageResolvedFamily_targetBox
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega Chart Piece)
    (x : Chart) (q : Piece) :
    F.toTargetImageResolvedFamily.targetBox x q =
      F.targetBoxSelection x q :=
  rfl

/-- Active family pieces expose the selected-box builder data. -/
theorem selectedBoxTargetImageAutoData_imageData
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    boundaryChartSelectedBoxImageData I (F.sourceChart x q) (F.boundarySourceChart x q)
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x q) (F.targetUpperCorner x q) := by
  simpa [selectedBoxTargetImageAutoData, targetLowerCorner, targetUpperCorner] using
    (F.selectedBoxTargetImageAutoData x hx q hq).imageData

/-- Partition lower corner selected for the final boundary partition term. -/
def partitionLowerCorner
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega M Piece)
    (partitionTargetBox :
      (x : M) -> (q : Piece) ->
        BoundaryChartTargetBoxSelection I
          (F.boundarySourceChart x q) (F.boundaryTargetChart x q)
          ((F.targetBoxSelection x q).lowerCorner)
          ((F.targetBoxSelection x q).upperCorner))
    (x : M) (q : Piece) : Fin (n + 1) -> Real :=
  (partitionTargetBox x q).lowerCorner

/-- Partition upper corner selected for the final boundary partition term. -/
def partitionUpperCorner
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega M Piece)
    (partitionTargetBox :
      (x : M) -> (q : Piece) ->
        BoundaryChartTargetBoxSelection I
          (F.boundarySourceChart x q) (F.boundaryTargetChart x q)
          ((F.targetBoxSelection x q).lowerCorner)
          ((F.targetBoxSelection x q).upperCorner))
    (x : M) (q : Piece) : Fin (n + 1) -> Real :=
  (partitionTargetBox x q).upperCorner

/--
The global fields still needed to turn a source-shrink target-image family into
the M8 resolved target-image input.

This is intentionally just a packaging layer: it does not prove local
openness, IFT facts, or any new geometry.  It groups the source extended boxes,
boundary-partition endpoint data, active-set alignment, and oriented-atlas
membership facts so downstream constructors can take one field package instead
of ten independent arguments.
-/
structure M8ResolvedFields
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega M Piece)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M) where
  /-- Extended source boxes needed by local boundary Stokes. -/
  sourceExtendedBox :
    forall x, x ∈ F.activeCharts ->
      forall q, q ∈ F.localPieces x ->
        boundaryChartExtendedBox I (F.sourceChart x q) (F.boundarySourceChart x q)
          omega (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
  /-- Chart used for the selected boundary-partition representative. -/
  partitionTargetChart : M -> Piece -> M
  /-- Target-box selection for the final boundary-partition representative. -/
  partitionTargetBox :
    (x : M) -> (q : Piece) ->
      BoundaryChartTargetBoxSelection I
        (F.boundarySourceChart x q) (F.boundaryTargetChart x q)
        ((F.targetBoxSelection x q).lowerCorner)
        ((F.targetBoxSelection x q).upperCorner)
  /-- Selected auxiliary target box for the final boundary-partition representative. -/
  partitionSelectedBox :
    forall x, x ∈ F.activeCharts ->
      forall q, q ∈ F.localPieces x ->
        boundaryChartSelectedBox I
          (F.boundaryTargetChart x q) (partitionTargetChart x q) omega
          ((partitionTargetBox x q).lowerCorner)
          ((partitionTargetBox x q).upperCorner)
  /-- Boundary partition term used by global reconstruction. -/
  boundaryPartitionTerm : M -> Piece -> Real
  /-- Endpoint identification for the selected boundary partition term. -/
  boundaryPartitionTerm_eq :
    forall x, x ∈ F.activeCharts ->
      forall q, q ∈ F.localPieces x ->
        boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I
            (F.boundaryTargetChart x q) (partitionTargetChart x q) omega
            ((partitionTargetBox x q).lowerCorner)
            ((partitionTargetBox x q).upperCorner)
  /-- The source-shrink family uses the selected partition active set. -/
  active_eq : F.activeCharts = selectedPartition.active
  /-- Source charts lie in the oriented boundary atlas. -/
  source_mem :
    forall x, x ∈ F.activeCharts ->
      forall q, q ∈ F.localPieces x ->
        F.sourceChart x q ∈ orientedBoundaryAtlas.charts
  /-- Boundary-source charts lie in the oriented boundary atlas. -/
  boundarySource_mem :
    forall x, x ∈ F.activeCharts ->
      forall q, q ∈ F.localPieces x ->
        F.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts
  /-- Boundary-target charts lie in the oriented boundary atlas. -/
  boundaryTarget_mem :
    forall x, x ∈ F.activeCharts ->
      forall q, q ∈ F.localPieces x ->
        F.boundaryTargetChart x q ∈ orientedBoundaryAtlas.charts

namespace M8ResolvedFields

variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
variable {F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega M Piece}

/-- Partition lower corner selected by the packaged target box. -/
def partitionLowerCorner
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas)
    (x : M) (q : Piece) : Fin (n + 1) -> Real :=
  (D.partitionTargetBox x q).lowerCorner

/-- Partition upper corner selected by the packaged target box. -/
def partitionUpperCorner
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas)
    (x : M) (q : Piece) : Fin (n + 1) -> Real :=
  (D.partitionTargetBox x q).upperCorner

/-- Selected boundary-partition box, rewritten with the named corner projections. -/
theorem partitionSelectedBox_named
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas)
    (x : M) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    boundaryChartSelectedBox I
      (F.boundaryTargetChart x q) (D.partitionTargetChart x q) omega
      (D.partitionLowerCorner x q) (D.partitionUpperCorner x q) := by
  simpa [partitionLowerCorner, partitionUpperCorner] using
    D.partitionSelectedBox x hx q hq

/-- Boundary partition endpoint identity, rewritten with named corner projections. -/
theorem boundaryPartitionTerm_eq_named
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas)
    (x : M) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    D.boundaryPartitionTerm x q =
      projectLocalBoundaryIntegral I
        (F.boundaryTargetChart x q) (D.partitionTargetChart x q) omega
        (D.partitionLowerCorner x q) (D.partitionUpperCorner x q) := by
  simpa [partitionLowerCorner, partitionUpperCorner] using
    D.boundaryPartitionTerm_eq x hx q hq

/-- Source chart membership projection for the packaged oriented-atlas data. -/
theorem sourceChart_mem
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas)
    (x : M) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    F.sourceChart x q ∈ orientedBoundaryAtlas.charts :=
  D.source_mem x hx q hq

/-- Boundary-source chart membership projection for the packaged oriented-atlas data. -/
theorem boundarySourceChart_mem
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas)
    (x : M) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    F.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts :=
  D.boundarySource_mem x hx q hq

/-- Boundary-target chart membership projection for the packaged oriented-atlas data. -/
theorem boundaryTargetChart_mem
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas)
    (x : M) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    F.boundaryTargetChart x q ∈ orientedBoundaryAtlas.charts :=
  D.boundaryTarget_mem x hx q hq

/-- Source-shrink family active set rewritten to the selected partition active set. -/
theorem active_eq_selected
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    F.activeCharts = selectedPartition.active :=
  D.active_eq

/-- The packaged fields as the existing M8 resolved target-image input. -/
def toM8ResolvedInput
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas Piece :=
  F.toTargetImageResolvedFamily.toM8ResolvedInput D.sourceExtendedBox D.partitionTargetChart
    D.partitionTargetBox D.partitionSelectedBox D.boundaryPartitionTerm
    D.boundaryPartitionTerm_eq D.active_eq D.source_mem
    D.boundarySource_mem D.boundaryTarget_mem

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
theorem toM8ResolvedInput_partitionTargetChart
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    D.toM8ResolvedInput.partitionTargetChart = D.partitionTargetChart :=
  rfl

@[simp]
theorem toM8ResolvedInput_partitionTargetBox
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas)
    (x : M) (q : Piece) :
    D.toM8ResolvedInput.partitionTargetBox x q = D.partitionTargetBox x q :=
  rfl

@[simp]
theorem toM8ResolvedInput_boundaryPartitionTerm
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    D.toM8ResolvedInput.boundaryPartitionTerm = D.boundaryPartitionTerm :=
  rfl

@[simp]
theorem toM8ResolvedInput_active_eq
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    D.toM8ResolvedInput.active_eq = D.active_eq :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    D.toM8TargetImageInput.targetImages =
      D.toM8ResolvedInput.toM8TargetImageInput.targetImages :=
  rfl

end M8ResolvedFields

/-- Source-shrink families in the exact resolved input shape used by M8. -/
def toM8ResolvedInput
    {selectedPartition : SelectedBoxPartitionOfUnity I omega}
    {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega M Piece)
    (sourceExtendedBox :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          boundaryChartExtendedBox I (F.sourceChart x q) (F.boundarySourceChart x q)
            omega (F.sourceLowerCorner x q) (F.sourceUpperCorner x q))
    (partitionTargetChart : M -> Piece -> M)
    (partitionTargetBox :
      (x : M) -> (q : Piece) ->
        BoundaryChartTargetBoxSelection I
          (F.boundarySourceChart x q) (F.boundaryTargetChart x q)
          ((F.targetBoxSelection x q).lowerCorner)
          ((F.targetBoxSelection x q).upperCorner))
    (partitionSelectedBox :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          boundaryChartSelectedBox I
            (F.boundaryTargetChart x q) (partitionTargetChart x q) omega
            ((partitionTargetBox x q).lowerCorner)
            ((partitionTargetBox x q).upperCorner))
    (boundaryPartitionTerm : M -> Piece -> Real)
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
    M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas Piece :=
  F.toTargetImageResolvedFamily.toM8ResolvedInput sourceExtendedBox
    partitionTargetChart partitionTargetBox partitionSelectedBox
    boundaryPartitionTerm boundaryPartitionTerm_eq active_eq
    source_mem boundarySource_mem boundaryTarget_mem

/-- Source-shrink family plus packaged global fields as M8 resolved input. -/
def toM8ResolvedInputOfFields
    {selectedPartition : SelectedBoxPartitionOfUnity I omega}
    {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega M Piece)
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas Piece :=
  D.toM8ResolvedInput

/-- Source-shrink family plus packaged global fields as `M8TargetImageInput`. -/
def toM8TargetImageInputOfFields
    {selectedPartition : SelectedBoxPartitionOfUnity I omega}
    {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega M Piece)
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas Piece :=
  D.toM8TargetImageInput

end BoundaryChartSourceShrinkOpenPartialHomeomorphFamily

end ManifoldBoundary

end Stokes

end
