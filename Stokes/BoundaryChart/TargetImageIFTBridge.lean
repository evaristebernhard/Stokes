import Stokes.BoundaryChart.TargetImageLocalOpenness
import Stokes.BoundaryChart.TransitionDerivative

/-!
# Target-image covers from inverse-function/local-openness data

This is a pure `BoundaryChart` bridge.  It packages the inverse-function-facing
inputs which produce the `image_mem_nhds` field of
`BoundaryChartLocalOpennessTargetCover`.

The genuinely geometric box-selection outputs are still explicit fields:
local openness gives a neighborhood of the image point, but selecting compatible
source/target boxes and compact-image bounds remains a separate chart-box
construction.
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

/--
Inverse-function-facing data for a finite source boundary-box cover.

For each active source box we keep a point `sourcePoint q`, a strict Frechet
derivative with surjective tangential map at that point, and the fact that the
source box is a neighborhood of the point.  Those fields prove the local
openness statement consumed by `BoundaryChartLocalOpennessTargetCover`.

The final target-box inclusions are deliberately still fields: this keeps the
choice of a concrete target lower-zero box separate from the analytic IFT step.
-/
structure BoundaryChartIFTTargetCoverData {n : Nat}
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
  /-- Lower corner of the selected target lower-zero box. -/
  targetLowerCorner : Piece → Fin (n + 1) → Real
  /-- Upper corner of the selected target lower-zero box. -/
  targetUpperCorner : Piece → Fin (n + 1) → Real
  /-- Lower-zero convention for selected target lower corners. -/
  targetLowerCorner_zero :
    ∀ q, q ∈ activePieces → targetLowerCorner q 0 = 0
  /-- Coordinatewise order of selected target corners. -/
  targetLower_le_targetUpper :
    ∀ q, q ∈ activePieces → targetLowerCorner q ≤ targetUpperCorner q
  /-- The image point lies in the selected target lower-zero box. -/
  targetPoint_mem :
    ∀ q, q ∈ activePieces →
      boundaryChartTransition I x0 x1 (sourcePoint q) ∈
        lowerZeroFaceDomain (targetLowerCorner q) (targetUpperCorner q)
  /-- The selected target box lies in the source image. -/
  targetBox_subset_image :
    ∀ q, q ∈ activePieces →
      boundaryChartInverseImageBoxSelection I x0 x1
        (sourceLowerCorner q) (sourceUpperCorner q)
        (targetLowerCorner q) (targetUpperCorner q)
  /-- The source sub-box image lies in the selected target box. -/
  compactImage :
    ∀ q, q ∈ activePieces →
      boundaryChartCompactImageBoxSelection I x0 x1
        (sourceLowerCorner q) (sourceUpperCorner q)
        (targetLowerCorner q) (targetUpperCorner q)

namespace BoundaryChartIFTTargetCoverData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/-- The target point selected by the inverse-function/local-openness step. -/
def targetPoint
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) : Fin n → Real :=
  boundaryChartTransition I x0 x1 (D.sourcePoint q)

/-- Local openness for one active source box, derived from the IFT-facing fields. -/
theorem image_mem_nhds
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces) :
    (boundaryChartTransition I x0 x1) ''
        lowerZeroFaceDomain (D.sourceLowerCorner q) (D.sourceUpperCorner q) ∈
      𝓝 (D.targetPoint q) :=
  boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
    (D.hasStrictFDerivAt q hq) (D.tangentMap_surjective q hq)
    (D.source_mem_nhds q hq)

/-- Package IFT-facing data as the existing local-openness target-cover record. -/
def toLocalOpennessTargetCover
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece) :
    BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece where
  toBoundaryChartCompactSourceBoxCover := D.toBoundaryChartCompactSourceBoxCover
  targetPoint := D.targetPoint
  targetLowerCorner := D.targetLowerCorner
  targetUpperCorner := D.targetUpperCorner
  targetLowerCorner_zero := D.targetLowerCorner_zero
  targetLower_le_targetUpper := D.targetLower_le_targetUpper
  targetPoint_mem := D.targetPoint_mem
  image_mem_nhds := D.image_mem_nhds
  targetBox_subset_image := D.targetBox_subset_image
  compactImage := D.compactImage

/-- The local-openness projection preserves active pieces. -/
@[simp]
theorem toLocalOpennessTargetCover_activePieces
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece) :
    D.toLocalOpennessTargetCover.activePieces = D.activePieces :=
  rfl

/-- The local-openness projection preserves source lower corners. -/
@[simp]
theorem toLocalOpennessTargetCover_sourceLowerCorner
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) :
    D.toLocalOpennessTargetCover.sourceLowerCorner q = D.sourceLowerCorner q :=
  rfl

/-- The local-openness projection preserves source upper corners. -/
@[simp]
theorem toLocalOpennessTargetCover_sourceUpperCorner
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) :
    D.toLocalOpennessTargetCover.sourceUpperCorner q = D.sourceUpperCorner q :=
  rfl

/-- The local-openness projection preserves target lower corners. -/
@[simp]
theorem toLocalOpennessTargetCover_targetLowerCorner
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) :
    D.toLocalOpennessTargetCover.targetLowerCorner q = D.targetLowerCorner q :=
  rfl

/-- The local-openness projection preserves target upper corners. -/
@[simp]
theorem toLocalOpennessTargetCover_targetUpperCorner
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) :
    D.toLocalOpennessTargetCover.targetUpperCorner q = D.targetUpperCorner q :=
  rfl

/-- Compact-image cover obtained from the IFT-facing target-cover data. -/
def toCompactImageCover
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece) :
    BoundaryChartCompactImageCover I x0 x1 a b Piece :=
  D.toLocalOpennessTargetCover.toCompactImageCover

/-- Target-box selection for one active source piece. -/
def toTargetBoxSelection
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces) :
    BoundaryChartTargetBoxSelection I x0 x1
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) :=
  D.toLocalOpennessTargetCover.toTargetBoxSelection q hq

/--
Constructor from orientation compatibility instead of an explicit surjectivity
field.
-/
def ofOrientationCompatible
    (sourceCover : BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece)
    (sourcePoint : Piece → Fin n → Real)
    (sourcePoint_mem :
      ∀ q, q ∈ sourceCover.activePieces →
        sourcePoint q ∈
          lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
            (sourceCover.sourceUpperCorner q))
    (source_mem_nhds :
      ∀ q, q ∈ sourceCover.activePieces →
        lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
            (sourceCover.sourceUpperCorner q) ∈ 𝓝 (sourcePoint q))
    (hasStrictFDerivAt :
      ∀ q, q ∈ sourceCover.activePieces →
        HasStrictFDerivAt (boundaryChartTransition I x0 x1)
          (boundaryChartTransitionTangentMap I x0 x1 (sourcePoint q))
          (sourcePoint q))
    (orientationCompatible :
      ∀ q, q ∈ sourceCover.activePieces →
        boundaryChartOrientationCompatibleOn I x0 x1
          (lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
            (sourceCover.sourceUpperCorner q)))
    (targetLowerCorner targetUpperCorner : Piece → Fin (n + 1) → Real)
    (targetLowerCorner_zero :
      ∀ q, q ∈ sourceCover.activePieces → targetLowerCorner q 0 = 0)
    (targetLower_le_targetUpper :
      ∀ q, q ∈ sourceCover.activePieces → targetLowerCorner q ≤ targetUpperCorner q)
    (targetPoint_mem :
      ∀ q, q ∈ sourceCover.activePieces →
        boundaryChartTransition I x0 x1 (sourcePoint q) ∈
          lowerZeroFaceDomain (targetLowerCorner q) (targetUpperCorner q))
    (targetBox_subset_image :
      ∀ q, q ∈ sourceCover.activePieces →
        boundaryChartInverseImageBoxSelection I x0 x1
          (sourceCover.sourceLowerCorner q) (sourceCover.sourceUpperCorner q)
          (targetLowerCorner q) (targetUpperCorner q))
    (compactImage :
      ∀ q, q ∈ sourceCover.activePieces →
        boundaryChartCompactImageBoxSelection I x0 x1
          (sourceCover.sourceLowerCorner q) (sourceCover.sourceUpperCorner q)
          (targetLowerCorner q) (targetUpperCorner q)) :
    BoundaryChartIFTTargetCoverData I x0 x1 a b Piece where
  toBoundaryChartCompactSourceBoxCover := sourceCover
  sourcePoint := sourcePoint
  sourcePoint_mem := sourcePoint_mem
  source_mem_nhds := source_mem_nhds
  hasStrictFDerivAt := hasStrictFDerivAt
  tangentMap_surjective := by
    intro q hq
    exact boundaryChartTransitionTangentMap_range_eq_top_of_orientationCompatibleOn
      (orientationCompatible q hq) (sourcePoint_mem q hq)
  targetLowerCorner := targetLowerCorner
  targetUpperCorner := targetUpperCorner
  targetLowerCorner_zero := targetLowerCorner_zero
  targetLower_le_targetUpper := targetLower_le_targetUpper
  targetPoint_mem := targetPoint_mem
  targetBox_subset_image := targetBox_subset_image
  compactImage := compactImage

end BoundaryChartIFTTargetCoverData

/--
Family-level IFT-facing input for resolved target images.

This mirrors `BoundaryChartLocalOpennessTargetImageFamily`, but lets callers
provide strict-derivative/local-openness data first and then project to the
existing target-image API.
-/
structure BoundaryChartIFTTargetImageFamily {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n) (Chart : Type c) (Piece : Type p) where
  /-- Finite active chart labels. -/
  activeCharts : Finset Chart
  /-- Source chart for each chart label. -/
  sourceChart : Chart → M
  /-- Boundary chart reached from each source chart. -/
  boundarySourceChart : Chart → M
  /-- Auxiliary target boundary chart for each local piece. -/
  boundaryTargetChart : Chart → Piece → M
  /-- Coarse source lower corner for each chart label. -/
  chartLowerCorner : Chart → Fin (n + 1) → Real
  /-- Coarse source upper corner for each chart label. -/
  chartUpperCorner : Chart → Fin (n + 1) → Real
  /-- IFT-facing target-cover data for each chart label. -/
  cover :
    ∀ x,
      BoundaryChartIFTTargetCoverData I (sourceChart x) (boundarySourceChart x)
        (chartLowerCorner x) (chartUpperCorner x) Piece
  /-- Inactive-piece default target boxes for proof-free resolved families. -/
  defaultTargetBox :
    ∀ x q,
      BoundaryChartTargetBoxSelection I (sourceChart x) (boundarySourceChart x)
        ((cover x).sourceLowerCorner q) ((cover x).sourceUpperCorner q)
  /-- Selected source boundary boxes on active pieces. -/
  sourceSelectedBox :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ (cover x).activePieces →
        boundaryChartSelectedBox I (sourceChart x) (boundarySourceChart x) ω
          ((cover x).sourceLowerCorner q) ((cover x).sourceUpperCorner q)
  /-- Selected auxiliary target boxes on active pieces. -/
  targetSelectedBox :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ (cover x).activePieces →
        boundaryChartSelectedBox I (boundarySourceChart x) (boundaryTargetChart x q) ω
          ((cover x).targetLowerCorner q) ((cover x).targetUpperCorner q)

namespace BoundaryChartIFTTargetImageFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Forget IFT-facing data down to the existing local-openness family package. -/
def toLocalOpennessTargetImageFamily
    (F : BoundaryChartIFTTargetImageFamily I ω Chart Piece) :
    BoundaryChartLocalOpennessTargetImageFamily I ω Chart Piece where
  activeCharts := F.activeCharts
  sourceChart := F.sourceChart
  boundarySourceChart := F.boundarySourceChart
  boundaryTargetChart := F.boundaryTargetChart
  chartLowerCorner := F.chartLowerCorner
  chartUpperCorner := F.chartUpperCorner
  cover := fun x => (F.cover x).toLocalOpennessTargetCover
  defaultTargetBox := F.defaultTargetBox
  sourceSelectedBox := F.sourceSelectedBox
  targetSelectedBox := F.targetSelectedBox

/-- Resolved target-image family obtained from IFT-facing data. -/
def toTargetImageResolvedFamily
    (F : BoundaryChartIFTTargetImageFamily I ω Chart Piece) :
    BoundaryChartTargetImageResolvedFamily I ω Chart Piece :=
  F.toLocalOpennessTargetImageFamily.toTargetImageResolvedFamily

/-- The local pieces are the active pieces of the IFT-facing cover. -/
theorem toTargetImageResolvedFamily_localPieces
    (F : BoundaryChartIFTTargetImageFamily I ω Chart Piece)
    (x : Chart) :
    F.toTargetImageResolvedFamily.localPieces x = (F.cover x).activePieces :=
  rfl

/-- Active resolved target boxes agree with the IFT-facing selected target boxes. -/
theorem toTargetImageResolvedFamily_targetBox
    (F : BoundaryChartIFTTargetImageFamily I ω Chart Piece)
    (x : Chart) (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    F.toTargetImageResolvedFamily.targetBox x q =
      (F.cover x).toTargetBoxSelection q hq := by
  simpa [toTargetImageResolvedFamily, toLocalOpennessTargetImageFamily] using
    BoundaryChartLocalOpennessTargetImageFamily.toTargetImageResolvedFamily_targetBox
      (F := F.toLocalOpennessTargetImageFamily) x q hq

/-- The image-data projection on active pieces is supplied by the IFT-facing cover. -/
theorem targetImageData
    (F : BoundaryChartIFTTargetImageFamily I ω Chart Piece)
    (x : Chart) (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    boundaryChartSelectedBoxImageData I (F.sourceChart x) (F.boundarySourceChart x)
      ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q)
      ((F.cover x).targetLowerCorner q) ((F.cover x).targetUpperCorner q) :=
  (F.cover x).toLocalOpennessTargetCover.imageData q hq

end BoundaryChartIFTTargetImageFamily

end ManifoldBoundary

end Stokes

end
