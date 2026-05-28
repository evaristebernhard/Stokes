import Stokes.BoundaryChart.TargetImageFromLocalInverse

/-!
# Target-image families from local openness data

This file is a pure `BoundaryChart` layer.  It names the geometric output that
the local-openness / inverse-function step is expected to provide, and projects
that output into the existing compact-image, target-box-family, and resolved
target-image APIs.

The hard analytic statement remains explicit: later files should prove the
`targetBox_subset_image` fields from local openness and target-box selection.
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
Local-openness target data for a finite cover of one source boundary box.

The field `image_mem_nhds` records the local-openness neighborhood statement.
The field `targetBox_subset_image` is the selected-box consequence that turns
local openness into an inverse-image selection.  Together with `compactImage`,
this gives the image data needed by boundary chart change-of-variables.
-/
structure BoundaryChartLocalOpennessTargetCover {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b : Fin (n + 1) → Real) (Piece : Type p)
    extends BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece where
  /-- Point in the target image around which the local-openness box was selected. -/
  targetPoint : Piece → Fin n → Real
  /-- Lower corner of the selected target lower-zero box. -/
  targetLowerCorner : Piece → Fin (n + 1) → Real
  /-- Upper corner of the selected target lower-zero box. -/
  targetUpperCorner : Piece → Fin (n + 1) → Real
  /-- Lower-zero convention for the selected target lower corner. -/
  targetLowerCorner_zero :
    ∀ q, q ∈ activePieces → targetLowerCorner q 0 = 0
  /-- Coordinatewise order of selected target corners. -/
  targetLower_le_targetUpper :
    ∀ q, q ∈ activePieces → targetLowerCorner q ≤ targetUpperCorner q
  /-- The target point lies in the selected target lower-zero box. -/
  targetPoint_mem :
    ∀ q, q ∈ activePieces →
      targetPoint q ∈ lowerZeroFaceDomain (targetLowerCorner q) (targetUpperCorner q)
  /-- Local-openness neighborhood statement for the active source sub-box image. -/
  image_mem_nhds :
    ∀ q, q ∈ activePieces →
      (boundaryChartTransition I x0 x1) ''
          lowerZeroFaceDomain (sourceLowerCorner q) (sourceUpperCorner q) ∈
        𝓝 (targetPoint q)
  /--
  Selected target box lies in the source image.  This is the concrete box-level
  output obtained after applying local openness and choosing a small target box.
  -/
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

namespace BoundaryChartLocalOpennessTargetCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/-- The source lower-zero domain of one local-openness cover member. -/
def sourceDomain
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece) (q : Piece) :
    Set (Fin n → Real) :=
  lowerZeroFaceDomain (C.sourceLowerCorner q) (C.sourceUpperCorner q)

/-- The target lower-zero domain of one local-openness cover member. -/
def targetDomain
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece) (q : Piece) :
    Set (Fin n → Real) :=
  lowerZeroFaceDomain (C.targetLowerCorner q) (C.targetUpperCorner q)

/-- Local inverse data derived from the local-openness selected-box inclusion. -/
theorem localInverse
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    boundaryChartLocalInverseData I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)
      (C.targetLowerCorner q) (C.targetUpperCorner q) :=
  boundaryChartLocalInverseData.of_inverseImageBoxSelection
    (C.targetBox_subset_image q hq)

/-- Image data for one active local-openness cover member. -/
theorem imageData
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    boundaryChartSelectedBoxImageData I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)
      (C.targetLowerCorner q) (C.targetUpperCorner q) :=
  boundaryChartSelectedBoxImageData_of_compactImage_localInverseData
    (C.compactImage q hq) (C.localInverse q hq)

/-- Materialize the existing compact-image cover package. -/
def toCompactImageCover
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece) :
    BoundaryChartCompactImageCover I x0 x1 a b Piece where
  toBoundaryChartCompactSourceBoxCover := C.toBoundaryChartCompactSourceBoxCover
  targetPoint := C.targetPoint
  targetLowerCorner := C.targetLowerCorner
  targetUpperCorner := C.targetUpperCorner
  targetLowerCorner_zero := C.targetLowerCorner_zero
  targetLower_le_targetUpper := C.targetLower_le_targetUpper
  targetPoint_mem := C.targetPoint_mem
  compactImage := C.compactImage
  localInverse := C.localInverse

/-- Package one active local-openness member as a target-box selection. -/
def toTargetBoxSelection
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    BoundaryChartTargetBoxSelection I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) :=
  C.toCompactImageCover.toTargetBoxSelection q hq

/-- The compact-image cover projection keeps the selected target lower corner. -/
theorem toCompactImageCover_targetLowerCorner
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (q : Piece) :
    C.toCompactImageCover.targetLowerCorner q = C.targetLowerCorner q :=
  rfl

/-- The compact-image cover projection keeps the selected target upper corner. -/
theorem toCompactImageCover_targetUpperCorner
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (q : Piece) :
    C.toCompactImageCover.targetUpperCorner q = C.targetUpperCorner q :=
  rfl

/--
Build local-openness target data from an already materialized compact-image
cover, keeping the local-openness neighborhood statement as an explicit audit
field.
-/
def ofCompactImageCover
    (C : BoundaryChartCompactImageCover I x0 x1 a b Piece)
    (image_mem_nhds :
      ∀ q, q ∈ C.activePieces →
        (boundaryChartTransition I x0 x1) ''
            lowerZeroFaceDomain (C.sourceLowerCorner q) (C.sourceUpperCorner q) ∈
          𝓝 (C.targetPoint q)) :
    BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece where
  toBoundaryChartCompactSourceBoxCover := C.toBoundaryChartCompactSourceBoxCover
  targetPoint := C.targetPoint
  targetLowerCorner := C.targetLowerCorner
  targetUpperCorner := C.targetUpperCorner
  targetLowerCorner_zero := C.targetLowerCorner_zero
  targetLower_le_targetUpper := C.targetLower_le_targetUpper
  targetPoint_mem := C.targetPoint_mem
  image_mem_nhds := image_mem_nhds
  targetBox_subset_image := fun q hq => (C.localInverse q hq).inverseImageBoxSelection
  compactImage := C.compactImage

/-- The compact-image-cover constructor projects back to the original compact cover. -/
theorem ofCompactImageCover_toCompactImageCover
    (C : BoundaryChartCompactImageCover I x0 x1 a b Piece)
    (image_mem_nhds :
      ∀ q, q ∈ C.activePieces →
        (boundaryChartTransition I x0 x1) ''
            lowerZeroFaceDomain (C.sourceLowerCorner q) (C.sourceUpperCorner q) ∈
          𝓝 (C.targetPoint q)) :
    (ofCompactImageCover C image_mem_nhds).toCompactImageCover = C := by
  rfl

end BoundaryChartLocalOpennessTargetCover

/--
Family-level local-openness input for resolved target images.

This is the constructor-facing shape: local openness chooses target boxes for
each source cover, and the existing target-image machinery consumes the
materialized compact-image covers.
-/
structure BoundaryChartLocalOpennessTargetImageFamily {n : Nat}
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
  /-- Local-openness cover selected for each chart label. -/
  cover :
    ∀ x,
      BoundaryChartLocalOpennessTargetCover I (sourceChart x) (boundarySourceChart x)
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

namespace BoundaryChartLocalOpennessTargetImageFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Local pieces induced by the local-openness cover of each active chart. -/
def localPieces
    (F : BoundaryChartLocalOpennessTargetImageFamily I ω Chart Piece) :
    Chart → Finset Piece :=
  fun x => (F.cover x).activePieces

/-- Existing compact-image cover family obtained from local-openness data. -/
def compactImageCover
    (F : BoundaryChartLocalOpennessTargetImageFamily I ω Chart Piece)
    (x : Chart) :
    BoundaryChartCompactImageCover I (F.sourceChart x) (F.boundarySourceChart x)
      (F.chartLowerCorner x) (F.chartUpperCorner x) Piece :=
  (F.cover x).toCompactImageCover

/-- Target-box-family selection obtained from local-openness data. -/
def toTargetBoxFamilySelection
    (F : BoundaryChartLocalOpennessTargetImageFamily I ω Chart Piece) :
    BoundaryChartTargetBoxFamilySelection I ω Chart Piece :=
  BoundaryChartTargetBoxFamilySelection.ofCompactImageCoverFamily
    F.activeCharts F.sourceChart F.boundarySourceChart
    F.chartLowerCorner F.chartUpperCorner F.compactImageCover
    F.sourceSelectedBox

/-- The target-box-family projection uses the local-openness target selection. -/
theorem toTargetBoxFamilySelection_targetSelection
    (F : BoundaryChartLocalOpennessTargetImageFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    F.toTargetBoxFamilySelection.targetSelection x hx q hq =
      (F.cover x).toTargetBoxSelection q hq := by
  rfl

/-- Resolved target-image family obtained from local-openness data. -/
def toTargetImageResolvedFamily
    (F : BoundaryChartLocalOpennessTargetImageFamily I ω Chart Piece) :
    BoundaryChartTargetImageResolvedFamily I ω Chart Piece :=
  BoundaryChartTargetImageResolvedFamily.ofCompactImageCoverFamily
    F.activeCharts F.sourceChart F.boundarySourceChart F.boundaryTargetChart
    F.chartLowerCorner F.chartUpperCorner F.compactImageCover
    F.defaultTargetBox F.sourceSelectedBox F.targetSelectedBox

/-- Active resolved target boxes are exactly the local-openness target selections. -/
theorem toTargetImageResolvedFamily_targetBox
    (F : BoundaryChartLocalOpennessTargetImageFamily I ω Chart Piece)
    (x : Chart) (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    F.toTargetImageResolvedFamily.targetBox x q =
      (F.cover x).toTargetBoxSelection q hq := by
  classical
  simpa [toTargetImageResolvedFamily, compactImageCover,
    BoundaryChartLocalOpennessTargetCover.toTargetBoxSelection] using
    BoundaryChartTargetImageResolvedFamily.ofCompactImageCoverFamily_targetBox
      (I := I) (ω := ω) (activeCharts := F.activeCharts)
      (sourceChart := F.sourceChart)
      (boundarySourceChart := F.boundarySourceChart)
      (boundaryTargetChart := F.boundaryTargetChart)
      (chartLowerCorner := F.chartLowerCorner)
      (chartUpperCorner := F.chartUpperCorner)
      (cover := F.compactImageCover)
      (defaultTargetBox := F.defaultTargetBox)
      (sourceSelectedBox := F.sourceSelectedBox)
      (targetSelectedBox := F.targetSelectedBox)
      x q hq

/-- Active target boxes selected by local openness expose image data. -/
theorem targetImageData
    (F : BoundaryChartLocalOpennessTargetImageFamily I ω Chart Piece)
    (x : Chart) (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    boundaryChartSelectedBoxImageData I (F.sourceChart x) (F.boundarySourceChart x)
      ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q)
      ((F.cover x).targetLowerCorner q) ((F.cover x).targetUpperCorner q) :=
  (F.cover x).imageData q hq

end BoundaryChartLocalOpennessTargetImageFamily

end ManifoldBoundary

end Stokes

end
