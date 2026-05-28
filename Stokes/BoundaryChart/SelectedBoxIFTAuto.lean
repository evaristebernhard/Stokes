import Stokes.BoundaryChart.CompactImageFromIFTAuto

/-!
# Selected-box IFT target-image automation

This file exposes the selected-box route through the IFT/local-openness target
selector in caller-facing shapes.  The point is to stop passing either
`IsCompact ((boundaryChartTransition ...) '' ...)` or the raw
`boundaryChartCompactCoordinateImageForLocalInverseTargets` predicate.

The remaining honest geometric field is the compact coordinate image-box
containment: after compactness selects a coordinate image box, each selected
local-inverse target must contain it.
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
Pointwise IFT data for a selected source boundary box.

Compared with the older target-box constructors, callers no longer provide
compactness of the source image or the raw
`compactImageForLocalInverseTargets` predicate.  Compactness is generated from
`selectedBox`; callers keep only the real containment obligation for the
compact coordinate image box selected from that compact image.
-/
structure BoundaryChartSelectedBoxIFTPointAutoData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) where
  /-- Selected source boundary box. -/
  selectedBox : boundaryChartSelectedBox I x0 x1 ω a b
  /-- Source point where local openness is applied. -/
  sourcePoint : Fin n → Real
  /-- The source point lies in the selected box. -/
  sourcePoint_mem : sourcePoint ∈ lowerZeroFaceDomain a b
  /-- The selected box is a neighborhood of the source point. -/
  source_mem_nhds : lowerZeroFaceDomain a b ∈ 𝓝 sourcePoint
  /-- Strict derivative of the boundary chart transition at the source point. -/
  hasStrictFDerivAt :
    HasStrictFDerivAt (boundaryChartTransition I x0 x1)
      (boundaryChartTransitionTangentMap I x0 x1 sourcePoint) sourcePoint
  /-- Surjectivity of the tangential derivative. -/
  tangentMap_surjective :
    (boundaryChartTransitionTangentMap I x0 x1 sourcePoint).range = ⊤
  /--
  The compact coordinate image box selected from the source image lies in each
  local-inverse target selected around the image point.
  -/
  compactBox_subset :
    ∀ e f : Fin n → Real, e ≤ f →
      compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
        (lowerZeroFaceDomain a b) e f →
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        boundaryChartTransition I x0 x1 sourcePoint ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            Set.Icc e f ⊆
              Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)

namespace BoundaryChartSelectedBoxIFTPointAutoData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/-- The target point produced by the boundary chart transition. -/
def targetPoint
    (D : BoundaryChartSelectedBoxIFTPointAutoData I x0 x1 ω a b) :
    Fin n → Real :=
  boundaryChartTransition I x0 x1 D.sourcePoint

/-- Local openness generated from the strict derivative and surjectivity fields. -/
theorem image_mem_nhds
    (D : BoundaryChartSelectedBoxIFTPointAutoData I x0 x1 ω a b) :
    (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈
      𝓝 D.targetPoint :=
  boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
    D.hasStrictFDerivAt D.tangentMap_surjective D.source_mem_nhds

/--
The compact-image predicate consumed by `TargetBoxFromIFT`, generated from the
selected source box plus the compact image-box containment field.
-/
theorem compactImageForLocalInverseTargets
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTPointAutoData I x0 x1 ω a b) :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b
      D.targetPoint := by
  simpa [targetPoint] using
    boundaryChartCompactCoordinateImageForLocalInverseTargets_of_selectedBox
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (y := D.targetPoint)
      D.selectedBox (by
        simpa [targetPoint] using D.compactBox_subset)

/-- The older point-auto input shape, with compact-image control generated. -/
def toPointAutoInputs
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTPointAutoData I x0 x1 ω a b) :
    BoundaryChartSelectedBoxPointAutoInputs I x0 x1 ω a b where
  selectedBox := D.selectedBox
  sourcePoint := D.sourcePoint
  sourcePoint_mem := D.sourcePoint_mem
  source_mem_nhds := D.source_mem_nhds
  compactImageForLocalInverseTargets :=
    D.compactImageForLocalInverseTargets

/--
Selected-box target-image data from the IFT fields, with image compactness
generated from the selected source box.
-/
theorem exists_autoData
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTPointAutoData I x0 x1 ω a b) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      D.targetPoint ∈
          lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          T.targetLowerCorner T.targetUpperCorner := by
  simpa [targetPoint] using
    exists_selectedBoxTargetImageAutoData_of_IFT_selectedBox
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (u := D.sourcePoint)
      D.selectedBox D.source_mem_nhds D.hasStrictFDerivAt
      D.tangentMap_surjective D.compactBox_subset

/-- A chosen target-image data package for downstream constructors. -/
def autoData
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTPointAutoData I x0 x1 ω a b) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b :=
  Classical.choose D.exists_autoData

/-- The chosen target box contains the IFT image point. -/
theorem autoData_targetPoint_mem
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTPointAutoData I x0 x1 ω a b) :
    D.targetPoint ∈
      lowerZeroFaceDomain (D.autoData).targetLowerCorner
        (D.autoData).targetUpperCorner :=
  (Classical.choose_spec D.exists_autoData).1

/-- The chosen target box carries the downstream image-data predicate. -/
theorem autoData_imageData
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTPointAutoData I x0 x1 ω a b) :
    boundaryChartSelectedBoxImageData I x0 x1 a b
      (D.autoData).targetLowerCorner (D.autoData).targetUpperCorner :=
  (Classical.choose_spec D.exists_autoData).2

/-- The target-box selection chosen by the pointwise selected-box IFT route. -/
def targetBoxSelection
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTPointAutoData I x0 x1 ω a b) :
    BoundaryChartTargetBoxSelection I x0 x1 a b :=
  D.autoData.targetBox

@[simp]
theorem targetBoxSelection_imageData
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTPointAutoData I x0 x1 ω a b) :
    boundaryChartSelectedBoxImageData I x0 x1 a b
      (D.targetBoxSelection).lowerCorner (D.targetBoxSelection).upperCorner :=
  D.targetBoxSelection.imageData

end BoundaryChartSelectedBoxIFTPointAutoData

/--
Finite selected-box IFT data for a compact source-box cover.

This is the finite-cover analogue of
`BoundaryChartSelectedBoxIFTPointAutoData`.  The generated projection is the
existing `BoundaryChartIFTCompactImageCoverData`, but without asking callers
for raw compact-image predicates on each active source box.
-/
structure BoundaryChartSelectedBoxIFTCompactCoverAutoData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) (Piece : Type p)
    extends BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece where
  /-- Source point at which local openness is applied for each active piece. -/
  sourcePoint : Piece → Fin n → Real
  /-- Selected source boxes on active pieces. -/
  selectedBox :
    ∀ q, q ∈ activePieces →
      boundaryChartSelectedBox I x0 x1 ω (sourceLowerCorner q) (sourceUpperCorner q)
  /-- The source point lies in the corresponding active source box. -/
  sourcePoint_mem :
    ∀ q, q ∈ activePieces →
      sourcePoint q ∈ lowerZeroFaceDomain (sourceLowerCorner q) (sourceUpperCorner q)
  /-- The corresponding active source box is a neighborhood of the source point. -/
  source_mem_nhds :
    ∀ q, q ∈ activePieces →
      lowerZeroFaceDomain (sourceLowerCorner q) (sourceUpperCorner q) ∈
        𝓝 (sourcePoint q)
  /-- Strict derivative of the boundary chart transition on each active piece. -/
  hasStrictFDerivAt :
    ∀ q, q ∈ activePieces →
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 (sourcePoint q))
        (sourcePoint q)
  /-- Surjectivity of the tangential derivative on each active piece. -/
  tangentMap_surjective :
    ∀ q, q ∈ activePieces →
      (boundaryChartTransitionTangentMap I x0 x1 (sourcePoint q)).range = ⊤
  /-- Compact image-box containment for the active local-inverse target. -/
  compactBox_subset :
    ∀ q, q ∈ activePieces →
      ∀ e f : Fin n → Real, e ≤ f →
        compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
          (lowerZeroFaceDomain (sourceLowerCorner q) (sourceUpperCorner q)) e f →
        ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
          boundaryChartTransition I x0 x1 (sourcePoint q) ∈ lowerZeroFaceDomain c d →
            boundaryChartLocalInverseData I x0 x1
              (sourceLowerCorner q) (sourceUpperCorner q) c d →
              Set.Icc e f ⊆
                Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)

namespace BoundaryChartSelectedBoxIFTCompactCoverAutoData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}

/-- Target point for one finite-cover source piece. -/
def targetPoint
    (D : BoundaryChartSelectedBoxIFTCompactCoverAutoData I x0 x1 ω a b Piece)
    (q : Piece) : Fin n → Real :=
  boundaryChartTransition I x0 x1 (D.sourcePoint q)

/--
Forget the selected-box finite-cover data to the existing IFT compact-image
cover; compactness of each active source image is generated from the selected
box on that piece.
-/
def toIFTCompactImageCoverData
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTCompactCoverAutoData I x0 x1 ω a b Piece) :
    BoundaryChartIFTCompactImageCoverData I x0 x1 a b Piece :=
  BoundaryChartIFTCompactImageCoverData.ofSelectedBox
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (ω := ω)
    D.toBoundaryChartCompactSourceBoxCover
    D.sourcePoint D.selectedBox D.sourcePoint_mem D.source_mem_nhds
    D.hasStrictFDerivAt D.tangentMap_surjective D.compactBox_subset

@[simp]
theorem toIFTCompactImageCoverData_activePieces
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTCompactCoverAutoData I x0 x1 ω a b Piece) :
    D.toIFTCompactImageCoverData.activePieces = D.activePieces :=
  rfl

@[simp]
theorem toIFTCompactImageCoverData_sourceLowerCorner
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTCompactCoverAutoData I x0 x1 ω a b Piece)
    (q : Piece) :
    D.toIFTCompactImageCoverData.sourceLowerCorner q = D.sourceLowerCorner q :=
  rfl

@[simp]
theorem toIFTCompactImageCoverData_sourceUpperCorner
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTCompactCoverAutoData I x0 x1 ω a b Piece)
    (q : Piece) :
    D.toIFTCompactImageCoverData.sourceUpperCorner q = D.sourceUpperCorner q :=
  rfl

/-- Local-openness compact-image cover generated from selected active boxes. -/
def toLocalOpennessCompactImageCover
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTCompactCoverAutoData I x0 x1 ω a b Piece) :
    BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece :=
  D.toIFTCompactImageCoverData.toLocalOpennessCompactImageCover

/-- One active cover piece as selected-box target-image auto data. -/
def selectedBoxTargetImageAutoData
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTCompactCoverAutoData I x0 x1 ω a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) :=
  D.toIFTCompactImageCoverData.toSelectedBoxTargetImageAutoData
    q hq (D.selectedBox q hq)

/-- The generated active-piece auto data exposes image data for its selected target. -/
theorem selectedBoxTargetImageAutoData_imageData
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTCompactCoverAutoData I x0 x1 ω a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces) :
    boundaryChartSelectedBoxImageData I x0 x1
      (D.sourceLowerCorner q) (D.sourceUpperCorner q)
      (D.selectedBoxTargetImageAutoData q hq).targetLowerCorner
      (D.selectedBoxTargetImageAutoData q hq).targetUpperCorner :=
  (D.selectedBoxTargetImageAutoData q hq).imageData

end BoundaryChartSelectedBoxIFTCompactCoverAutoData

end ManifoldBoundary

end Stokes

end
