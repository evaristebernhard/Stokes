import Stokes.BoundaryChart.TargetImageSelectedBoxBuilder

/-!
# Target boxes from local openness / IFT data

This file is the first nontrivial target-box construction layer after local
openness.  Local openness chooses a small lower-zero target box inside the image
of the source box.  To turn that box into the downstream
`BoundaryChartTargetBoxSelection`, we still need compact-image control for the
same chosen target box.

The definitions below do not prove compact-image containment from compactness.
They isolate exactly that remaining geometric input as
`boundaryChartCompactCoordinateImageForLocalInverseTargets`, then construct the
target-box records consumed by the selected-box target-image API.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section ManifoldBoundary

universe u w p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Local openness, plus compact-image control for whichever target box it selects,
produces a packaged target-box selection.

This is the precise box-level bridge missing from the older local-openness
records: the open-mapping step gives the inverse-image inclusion, while
`hcompact` supplies compact image containment for the same selected corners.
-/
theorem exists_boundaryChartTargetBoxSelection_of_localOpenness_compactImage
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y)
    (hcompact :
      boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y) :
    ∃ target : BoundaryChartTargetBoxSelection I x0 x1 a b,
      y ∈ lowerZeroFaceDomain target.lowerCorner target.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          target.lowerCorner target.upperCorner := by
  rcases exists_lowerZeroFaceDomain_subset_of_mem_nhds himage with
    ⟨c, d, hc0, hle, hy, hsubset⟩
  have hlocal : boundaryChartLocalInverseData I x0 x1 a b c d :=
    boundaryChartLocalInverseData.of_inverseImageBoxSelection hsubset
  let target : BoundaryChartTargetBoxSelection I x0 x1 a b :=
    BoundaryChartTargetBoxSelection.mkOfCompactCoordinateImageBoxSelection
      c d hc0 hle (hcompact c d hc0 hle hy hlocal) hlocal
  exact ⟨target, hy, target.imageData⟩

/--
Selected-box auto-data from local openness plus compact-image control for the
target selected by local openness.
-/
theorem exists_selectedBoxTargetImageAutoData_of_localOpenness_compactImage
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y)
    (hcompact :
      boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y) :
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          D.targetLowerCorner D.targetUpperCorner := by
  rcases exists_boundaryChartTargetBoxSelection_of_localOpenness_compactImage
      himage hcompact with
    ⟨target, hmem, himageData⟩
  refine ⟨BoundaryChartSelectedBoxTargetImageAutoData.ofTargetBoxSelection
      hbox target, ?_, ?_⟩
  · simpa [BoundaryChartSelectedBoxTargetImageAutoData.targetLowerCorner,
      BoundaryChartSelectedBoxTargetImageAutoData.targetUpperCorner] using hmem
  · simpa [BoundaryChartSelectedBoxTargetImageAutoData.targetLowerCorner,
      BoundaryChartSelectedBoxTargetImageAutoData.targetUpperCorner] using himageData

/--
Finite local-openness cover without explicit target corners.

For each active source sub-box, local openness gives a neighborhood statement at
`targetPoint q`.  The compact-image field is still the honest geometric input:
it must hold for the particular target box selected from that neighborhood.
-/
structure BoundaryChartLocalOpennessCompactImageCover {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b : Fin (n + 1) → Real) (Piece : Type p)
    extends BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece where
  /-- Target point around which local openness selects a target lower-zero box. -/
  targetPoint : Piece → Fin n → Real
  /-- Local-openness neighborhood statement for each active source sub-box. -/
  image_mem_nhds :
    ∀ q, q ∈ activePieces →
      (boundaryChartTransition I x0 x1) ''
          lowerZeroFaceDomain (sourceLowerCorner q) (sourceUpperCorner q) ∈
        𝓝 (targetPoint q)
  /-- Compact-image control for whichever target box local openness selects. -/
  compactImageForLocalInverseTargets :
    ∀ q, q ∈ activePieces →
      boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1
        (sourceLowerCorner q) (sourceUpperCorner q) (targetPoint q)

namespace BoundaryChartLocalOpennessCompactImageCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/-- The target-box selection chosen from one active local-openness cover piece. -/
def targetBoxSelection
    (C : BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    BoundaryChartTargetBoxSelection I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) :=
  Classical.choose
    (exists_boundaryChartTargetBoxSelection_of_localOpenness_compactImage
      (C.image_mem_nhds q hq) (C.compactImageForLocalInverseTargets q hq))

/-- The selected target box contains the local-openness target point. -/
theorem targetBoxSelection_targetPoint_mem
    (C : BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    C.targetPoint q ∈
      lowerZeroFaceDomain (C.targetBoxSelection q hq).lowerCorner
        (C.targetBoxSelection q hq).upperCorner :=
  (Classical.choose_spec
    (exists_boundaryChartTargetBoxSelection_of_localOpenness_compactImage
      (C.image_mem_nhds q hq) (C.compactImageForLocalInverseTargets q hq))).1

/-- The selected target box carries the downstream image-data predicate. -/
theorem targetBoxSelection_imageData
    (C : BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    boundaryChartSelectedBoxImageData I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)
      (C.targetBoxSelection q hq).lowerCorner
      (C.targetBoxSelection q hq).upperCorner :=
  (Classical.choose_spec
    (exists_boundaryChartTargetBoxSelection_of_localOpenness_compactImage
      (C.image_mem_nhds q hq) (C.compactImageForLocalInverseTargets q hq))).2

/--
Materialize the older explicit-corner local-openness cover.

Inactive pieces receive dummy corners; all geometric fields are only required on
active pieces, where the corners are the ones selected by local openness.
-/
def toLocalOpennessTargetCover
    (C : BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece) :
    BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece := by
  classical
  let zeroLower : Fin (n + 1) → Real := lowerZeroTargetLowerCorner (fun _ : Fin n => 0)
  let zeroUpper : Fin (n + 1) → Real := lowerZeroTargetUpperCorner (fun _ : Fin n => 0)
  let targetLowerCorner : Piece → Fin (n + 1) → Real :=
    fun q =>
      if hq : q ∈ C.activePieces then
        (C.targetBoxSelection q hq).lowerCorner
      else
        zeroLower
  let targetUpperCorner : Piece → Fin (n + 1) → Real :=
    fun q =>
      if hq : q ∈ C.activePieces then
        (C.targetBoxSelection q hq).upperCorner
      else
        zeroUpper
  refine
    { toBoundaryChartCompactSourceBoxCover := C.toBoundaryChartCompactSourceBoxCover
      targetPoint := C.targetPoint
      targetLowerCorner := targetLowerCorner
      targetUpperCorner := targetUpperCorner
      targetLowerCorner_zero := ?_
      targetLower_le_targetUpper := ?_
      targetPoint_mem := ?_
      image_mem_nhds := C.image_mem_nhds
      targetBox_subset_image := ?_
      compactImage := ?_ }
  · intro q hq
    dsimp [targetLowerCorner]
    rw [dif_pos hq]
    exact (C.targetBoxSelection q hq).lowerCorner_zero
  · intro q hq
    dsimp [targetLowerCorner, targetUpperCorner]
    rw [dif_pos hq, dif_pos hq]
    exact (C.targetBoxSelection q hq).lower_le_upper
  · intro q hq
    dsimp [targetLowerCorner, targetUpperCorner]
    rw [dif_pos hq, dif_pos hq]
    exact C.targetBoxSelection_targetPoint_mem q hq
  · intro q hq
    dsimp [targetLowerCorner, targetUpperCorner]
    rw [dif_pos hq, dif_pos hq]
    exact (C.targetBoxSelection q hq).localInverse.inverseImageBoxSelection
  · intro q hq
    dsimp [targetLowerCorner, targetUpperCorner]
    rw [dif_pos hq, dif_pos hq]
    exact (C.targetBoxSelection q hq).compactImage

@[simp]
theorem toLocalOpennessTargetCover_activePieces
    (C : BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece) :
    C.toLocalOpennessTargetCover.activePieces = C.activePieces :=
  rfl

@[simp]
theorem toLocalOpennessTargetCover_targetLowerCorner
    (C : BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    C.toLocalOpennessTargetCover.targetLowerCorner q =
      (C.targetBoxSelection q hq).lowerCorner := by
  simp [toLocalOpennessTargetCover, hq]

@[simp]
theorem toLocalOpennessTargetCover_targetUpperCorner
    (C : BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    C.toLocalOpennessTargetCover.targetUpperCorner q =
      (C.targetBoxSelection q hq).upperCorner := by
  simp [toLocalOpennessTargetCover, hq]

/-- One active cover piece as selected-box target-image auto data. -/
def toSelectedBoxTargetImageAutoData
    {ω : ManifoldForm I M n}
    (C : BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) :=
  C.toLocalOpennessTargetCover.toSelectedBoxTargetImageAutoData q hq hbox

end BoundaryChartLocalOpennessCompactImageCover

/--
IFT-facing finite cover without explicit target corners.

The IFT fields prove local openness.  The compact-image-for-selected-targets
field is intentionally still explicit; it is the remaining compact image box
selection lemma needed after the inverse-function/local-openness step.
-/
structure BoundaryChartIFTCompactImageCoverData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b : Fin (n + 1) → Real) (Piece : Type p)
    extends BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece where
  /-- Source point at which local openness is applied for each active piece. -/
  sourcePoint : Piece → Fin n → Real
  /-- The source point lies in the corresponding source box. -/
  sourcePoint_mem :
    ∀ q, q ∈ activePieces →
      sourcePoint q ∈ lowerZeroFaceDomain (sourceLowerCorner q) (sourceUpperCorner q)
  /-- The corresponding source box is a neighborhood of the source point. -/
  source_mem_nhds :
    ∀ q, q ∈ activePieces →
      lowerZeroFaceDomain (sourceLowerCorner q) (sourceUpperCorner q) ∈
        𝓝 (sourcePoint q)
  /-- Strict derivative hypothesis used by the inverse-function theorem. -/
  hasStrictFDerivAt :
    ∀ q, q ∈ activePieces →
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 (sourcePoint q))
        (sourcePoint q)
  /-- Surjectivity of the tangential derivative at the source point. -/
  tangentMap_surjective :
    ∀ q, q ∈ activePieces →
      (boundaryChartTransitionTangentMap I x0 x1 (sourcePoint q)).range = ⊤
  /-- Compact-image control for the target box selected by local openness. -/
  compactImageForLocalInverseTargets :
    ∀ q, q ∈ activePieces →
      boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1
        (sourceLowerCorner q) (sourceUpperCorner q)
        (boundaryChartTransition I x0 x1 (sourcePoint q))

namespace BoundaryChartIFTCompactImageCoverData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/-- The target point produced by the boundary chart transition. -/
def targetPoint
    (D : BoundaryChartIFTCompactImageCoverData I x0 x1 a b Piece)
    (q : Piece) : Fin n → Real :=
  boundaryChartTransition I x0 x1 (D.sourcePoint q)

/-- Local openness for one active source box, derived from the IFT-facing fields. -/
theorem image_mem_nhds
    (D : BoundaryChartIFTCompactImageCoverData I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces) :
    (boundaryChartTransition I x0 x1) ''
        lowerZeroFaceDomain (D.sourceLowerCorner q) (D.sourceUpperCorner q) ∈
      𝓝 (D.targetPoint q) :=
  boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
    (D.hasStrictFDerivAt q hq) (D.tangentMap_surjective q hq)
    (D.source_mem_nhds q hq)

/-- Forget IFT-facing data to the local-openness-plus-compact-image cover. -/
def toLocalOpennessCompactImageCover
    (D : BoundaryChartIFTCompactImageCoverData I x0 x1 a b Piece) :
    BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece where
  toBoundaryChartCompactSourceBoxCover := D.toBoundaryChartCompactSourceBoxCover
  targetPoint := D.targetPoint
  image_mem_nhds := D.image_mem_nhds
  compactImageForLocalInverseTargets := D.compactImageForLocalInverseTargets

/-- Materialize explicit target boxes from the IFT/local-openness route. -/
def toLocalOpennessTargetCover
    (D : BoundaryChartIFTCompactImageCoverData I x0 x1 a b Piece) :
    BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece :=
  D.toLocalOpennessCompactImageCover.toLocalOpennessTargetCover

/-- One active IFT cover piece as selected-box target-image auto data. -/
def toSelectedBoxTargetImageAutoData
    {ω : ManifoldForm I M n}
    (D : BoundaryChartIFTCompactImageCoverData I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q)) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) :=
  D.toLocalOpennessCompactImageCover.toSelectedBoxTargetImageAutoData q hq hbox

end BoundaryChartIFTCompactImageCoverData

end ManifoldBoundary

end Stokes

end
