import Stokes.BoundaryChart.TargetBoxFromIFT

/-!
# Compact-image containment for boundary target boxes

`TargetBoxFromIFT` still needs the field
`boundaryChartCompactCoordinateImageForLocalInverseTargets`: local openness can
choose a small target lower-zero box contained in the source image, but that
does not by itself imply that the whole source box image is contained in the
same target box.  This file isolates the honest extra containment needed for
that step.

The useful split is:

* compactness/continuity gives one coordinate box containing the source image;
* the local-inverse target box must be known to contain that coordinate box.

That second statement is the real geometric box-alignment obligation.
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

/-- Convert boundary lower-zero compact-image containment to the tangential
coordinate-box predicate used by `TargetBoxFromIFT`. -/
theorem compactCoordinateImageBoxSelection_of_boundaryChartCompactImageBoxSelection
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hcompact : boundaryChartCompactImageBoxSelection I x0 x1 a b c d) :
    compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b)
      (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d) := by
  intro z hz
  rcases hz with ⟨u, hu, rfl⟩
  exact hcompact ⟨u, hu, rfl⟩

/-- The older lower-zero target-box predicate implies the newer coordinate-box
predicate required by `TargetBoxFromIFT`. -/
theorem boundaryChartCompactCoordinateImageForLocalInverseTargets_of_boundary
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (hcompact :
      boundaryChartCompactImageForLocalInverseTargets I x0 x1 a b y) :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y := by
  intro c d hc0 hle hy hlocal
  exact compactCoordinateImageBoxSelection_of_boundaryChartCompactImageBoxSelection
    (hcompact c d hc0 hle hy hlocal)

/-- Conversely, the coordinate-box predicate materializes the lower-zero
target-box predicate. -/
theorem boundaryChartCompactImageForLocalInverseTargets_of_coordinate
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (hcompact :
      boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y) :
    boundaryChartCompactImageForLocalInverseTargets I x0 x1 a b y := by
  intro c d hc0 hle hy hlocal
  exact boundaryChartCompactImageBoxSelection_of_compactCoordinateImageBoxSelection
    (hcompact c d hc0 hle hy hlocal)

/--
A compact coordinate box for the source image, together with the extra fact
that every local-inverse target box selected around `y` contains that compact
image box.

This is strictly weaker than pretending local openness proves compact-image
containment: the final field is the genuine box-alignment obligation.
-/
structure BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b : Fin (n + 1) → Real) (y : Fin n → Real) where
  /-- Lower corner of a coordinate box containing the source image. -/
  imageLowerCorner : Fin n → Real
  /-- Upper corner of a coordinate box containing the source image. -/
  imageUpperCorner : Fin n → Real
  /-- Coordinatewise ordering of the image-bounding box. -/
  imageLower_le_imageUpper : imageLowerCorner ≤ imageUpperCorner
  /-- The source boundary-box image is contained in the image-bounding box. -/
  compactImage :
    compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) imageLowerCorner imageUpperCorner
  /-- Every local-inverse target box selected at `y` contains that image box. -/
  selectedTarget_contains_imageBox :
    ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
      y ∈ lowerZeroFaceDomain c d →
        boundaryChartLocalInverseData I x0 x1 a b c d →
          Set.Icc imageLowerCorner imageUpperCorner ⊆
            Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)

namespace BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {y : Fin n → Real}

/-- Consume the separated compact-image box and target-containment fields as
the predicate expected by `TargetBoxFromIFT`. -/
theorem compactImageForLocalInverseTargets
    (D : BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets
      I x0 x1 a b y) :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y := by
  intro c d hc0 hle hy hlocal z hz
  exact D.selectedTarget_contains_imageBox c d hc0 hle hy hlocal
    (D.compactImage hz)

/-- Constructor from an already selected boundary target box, provided future
local-inverse targets are known to contain the selected target's image box. -/
def ofTargetBoxSelection
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (target_contains_selectedImageBox :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            Set.Icc (boundaryFaceLowerCorner target.lowerCorner)
                (boundaryFaceUpperCorner target.upperCorner) ⊆
              Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets
      I x0 x1 a b y where
  imageLowerCorner := boundaryFaceLowerCorner target.lowerCorner
  imageUpperCorner := boundaryFaceUpperCorner target.upperCorner
  imageLower_le_imageUpper := by
    intro i
    exact target.lower_le_upper i.succ
  compactImage :=
    compactCoordinateImageBoxSelection_of_boundaryChartCompactImageBoxSelection
      target.compactImage
  selectedTarget_contains_imageBox := target_contains_selectedImageBox

/-- Constructor from compactness of the source image plus the promise that
whichever coordinate box compactness selects is contained in all local-inverse
target boxes under consideration. -/
def ofIsCompactImage
    (hK : IsCompact
      ((boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b))
    (selectedTarget_contains_compactBox :
      ∀ e f : Fin n → Real, e ≤ f →
        compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
          (lowerZeroFaceDomain a b) e f →
          ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
            y ∈ lowerZeroFaceDomain c d →
              boundaryChartLocalInverseData I x0 x1 a b c d →
                Set.Icc e f ⊆
                  Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets
      I x0 x1 a b y := by
  let hexists :=
    exists_compactCoordinateImageBoxSelection_of_isCompact_image
      (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b) hK
  let e : Fin n → Real := Classical.choose hexists
  let hexists_f := Classical.choose_spec hexists
  let f : Fin n → Real := Classical.choose hexists_f
  let hselected := Classical.choose_spec hexists_f
  have hef : e ≤ f := hselected.1
  have hcompact :
      compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
        (lowerZeroFaceDomain a b) e f := hselected.2
  exact
    { imageLowerCorner := e
      imageUpperCorner := f
      imageLower_le_imageUpper := hef
      compactImage := hcompact
      selectedTarget_contains_imageBox :=
        selectedTarget_contains_compactBox e f hef hcompact }

/-- Direct theorem form of `ofIsCompactImage`. -/
theorem compactImageForLocalInverseTargets_of_isCompactImage
    (hK : IsCompact
      ((boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b))
    (selectedTarget_contains_compactBox :
      ∀ e f : Fin n → Real, e ≤ f →
        compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
          (lowerZeroFaceDomain a b) e f →
          ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
            y ∈ lowerZeroFaceDomain c d →
              boundaryChartLocalInverseData I x0 x1 a b c d →
                Set.Icc e f ⊆
                  Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y :=
  (ofIsCompactImage (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (y := y) hK selectedTarget_contains_compactBox).compactImageForLocalInverseTargets

end BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets

namespace BoundaryChartTargetBoxSelection

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real}

/-- Coordinate-box compact-image projection from a selected target box. -/
theorem compactCoordinateImage
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b)
      (boundaryFaceLowerCorner target.lowerCorner)
      (boundaryFaceUpperCorner target.upperCorner) :=
  compactCoordinateImageBoxSelection_of_boundaryChartCompactImageBoxSelection
    target.compactImage

/-- A selected target box gives the compact-image-for-local-inverse-targets
predicate once later local-inverse target boxes are known to contain it. -/
theorem compactImageForLocalInverseTargets_of_contains
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) {y : Fin n → Real}
    (target_contains_selectedImageBox :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            Set.Icc (boundaryFaceLowerCorner target.lowerCorner)
                (boundaryFaceUpperCorner target.upperCorner) ⊆
              Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y :=
  (BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets.ofTargetBoxSelection
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b) (y := y)
    target target_contains_selectedImageBox).compactImageForLocalInverseTargets

end BoundaryChartTargetBoxSelection

/-- Local-openness cover with compact image factored through a compact
coordinate image box. -/
structure BoundaryChartLocalOpennessCompactImageBoxCover {n : Nat}
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
  /-- Compact image box plus target-containment data for each active piece. -/
  compactImageBoxForLocalInverseTargets :
    ∀ q, q ∈ activePieces →
      BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets I x0 x1
        (sourceLowerCorner q) (sourceUpperCorner q) (targetPoint q)

namespace BoundaryChartLocalOpennessCompactImageBoxCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/-- Projection to the predicate consumed by `BoundaryChartLocalOpennessCompactImageCover`. -/
theorem compactImageForLocalInverseTargets
    (C : BoundaryChartLocalOpennessCompactImageBoxCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) (C.targetPoint q) :=
  (C.compactImageBoxForLocalInverseTargets q hq).compactImageForLocalInverseTargets

/-- Forget the compact-image-box witness to the existing local-openness compact-image cover. -/
def toLocalOpennessCompactImageCover
    (C : BoundaryChartLocalOpennessCompactImageBoxCover I x0 x1 a b Piece) :
    BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece where
  toBoundaryChartCompactSourceBoxCover := C.toBoundaryChartCompactSourceBoxCover
  targetPoint := C.targetPoint
  image_mem_nhds := C.image_mem_nhds
  compactImageForLocalInverseTargets := C.compactImageForLocalInverseTargets

end BoundaryChartLocalOpennessCompactImageBoxCover

namespace BoundaryChartLocalOpennessTargetCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/-- Convert explicit local-openness target data into the compact-image-box
shape, assuming later local-inverse target boxes contain the explicit target
image box. -/
def toCompactImageBoxCover
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (target_contains_selectedImageBox :
      ∀ q, q ∈ C.activePieces →
        ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
          C.targetPoint q ∈ lowerZeroFaceDomain c d →
            boundaryChartLocalInverseData I x0 x1
              (C.sourceLowerCorner q) (C.sourceUpperCorner q) c d →
              Set.Icc (boundaryFaceLowerCorner (C.targetLowerCorner q))
                  (boundaryFaceUpperCorner (C.targetUpperCorner q)) ⊆
                Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    BoundaryChartLocalOpennessCompactImageBoxCover I x0 x1 a b Piece where
  toBoundaryChartCompactSourceBoxCover := C.toBoundaryChartCompactSourceBoxCover
  targetPoint := C.targetPoint
  image_mem_nhds := C.image_mem_nhds
  compactImageBoxForLocalInverseTargets := fun q hq =>
    { imageLowerCorner := boundaryFaceLowerCorner (C.targetLowerCorner q)
      imageUpperCorner := boundaryFaceUpperCorner (C.targetUpperCorner q)
      imageLower_le_imageUpper := by
        intro i
        exact C.targetLower_le_targetUpper q hq i.succ
      compactImage :=
        compactCoordinateImageBoxSelection_of_boundaryChartCompactImageBoxSelection
          (C.compactImage q hq)
      selectedTarget_contains_imageBox :=
        target_contains_selectedImageBox q hq }

/-- Direct constructor to the existing `TargetBoxFromIFT` local-openness record. -/
def toLocalOpennessCompactImageCoverOfContains
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (target_contains_selectedImageBox :
      ∀ q, q ∈ C.activePieces →
        ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
          C.targetPoint q ∈ lowerZeroFaceDomain c d →
            boundaryChartLocalInverseData I x0 x1
              (C.sourceLowerCorner q) (C.sourceUpperCorner q) c d →
              Set.Icc (boundaryFaceLowerCorner (C.targetLowerCorner q))
                  (boundaryFaceUpperCorner (C.targetUpperCorner q)) ⊆
                Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece :=
  (C.toCompactImageBoxCover target_contains_selectedImageBox).toLocalOpennessCompactImageCover

end BoundaryChartLocalOpennessTargetCover

/-- IFT-facing cover with compact image factored through compact coordinate
image boxes. -/
structure BoundaryChartIFTCompactImageBoxCoverData {n : Nat}
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
  /-- Compact image box plus target-containment data for each active piece. -/
  compactImageBoxForLocalInverseTargets :
    ∀ q, q ∈ activePieces →
      BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets I x0 x1
        (sourceLowerCorner q) (sourceUpperCorner q)
        (boundaryChartTransition I x0 x1 (sourcePoint q))

namespace BoundaryChartIFTCompactImageBoxCoverData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/-- The target point produced by the boundary chart transition. -/
def targetPoint
    (D : BoundaryChartIFTCompactImageBoxCoverData I x0 x1 a b Piece)
    (q : Piece) : Fin n → Real :=
  boundaryChartTransition I x0 x1 (D.sourcePoint q)

/-- Projection to the predicate consumed by `BoundaryChartIFTCompactImageCoverData`. -/
theorem compactImageForLocalInverseTargets
    (D : BoundaryChartIFTCompactImageBoxCoverData I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces) :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) (D.targetPoint q) := by
  simpa [targetPoint] using
    (D.compactImageBoxForLocalInverseTargets q hq).compactImageForLocalInverseTargets

/-- Forget the compact-image-box witness to the existing IFT compact-image cover data. -/
def toIFTCompactImageCoverData
    (D : BoundaryChartIFTCompactImageBoxCoverData I x0 x1 a b Piece) :
    BoundaryChartIFTCompactImageCoverData I x0 x1 a b Piece where
  toBoundaryChartCompactSourceBoxCover := D.toBoundaryChartCompactSourceBoxCover
  sourcePoint := D.sourcePoint
  sourcePoint_mem := D.sourcePoint_mem
  source_mem_nhds := D.source_mem_nhds
  hasStrictFDerivAt := D.hasStrictFDerivAt
  tangentMap_surjective := D.tangentMap_surjective
  compactImageForLocalInverseTargets := D.compactImageForLocalInverseTargets

/-- Local-openness compact-image cover obtained from the IFT-facing data. -/
def toLocalOpennessCompactImageCover
    (D : BoundaryChartIFTCompactImageBoxCoverData I x0 x1 a b Piece) :
    BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece :=
  D.toIFTCompactImageCoverData.toLocalOpennessCompactImageCover

end BoundaryChartIFTCompactImageBoxCoverData

namespace BoundaryChartIFTTargetCoverData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/-- Convert explicit IFT target-cover data into the compact-image-box shape,
assuming later local-inverse target boxes contain the explicit target image
box. -/
def toCompactImageBoxCoverData
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (target_contains_selectedImageBox :
      ∀ q, q ∈ D.activePieces →
        ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
          D.targetPoint q ∈ lowerZeroFaceDomain c d →
            boundaryChartLocalInverseData I x0 x1
              (D.sourceLowerCorner q) (D.sourceUpperCorner q) c d →
              Set.Icc (boundaryFaceLowerCorner (D.targetLowerCorner q))
                  (boundaryFaceUpperCorner (D.targetUpperCorner q)) ⊆
                Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    BoundaryChartIFTCompactImageBoxCoverData I x0 x1 a b Piece where
  toBoundaryChartCompactSourceBoxCover := D.toBoundaryChartCompactSourceBoxCover
  sourcePoint := D.sourcePoint
  sourcePoint_mem := D.sourcePoint_mem
  source_mem_nhds := D.source_mem_nhds
  hasStrictFDerivAt := D.hasStrictFDerivAt
  tangentMap_surjective := D.tangentMap_surjective
  compactImageBoxForLocalInverseTargets := fun q hq =>
    { imageLowerCorner := boundaryFaceLowerCorner (D.targetLowerCorner q)
      imageUpperCorner := boundaryFaceUpperCorner (D.targetUpperCorner q)
      imageLower_le_imageUpper := by
        intro i
        exact D.targetLower_le_targetUpper q hq i.succ
      compactImage :=
        compactCoordinateImageBoxSelection_of_boundaryChartCompactImageBoxSelection
          (D.compactImage q hq)
      selectedTarget_contains_imageBox :=
        target_contains_selectedImageBox q hq }

/-- Direct constructor to the existing `TargetBoxFromIFT` IFT compact-image record. -/
def toIFTCompactImageCoverDataOfContains
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (target_contains_selectedImageBox :
      ∀ q, q ∈ D.activePieces →
        ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
          D.targetPoint q ∈ lowerZeroFaceDomain c d →
            boundaryChartLocalInverseData I x0 x1
              (D.sourceLowerCorner q) (D.sourceUpperCorner q) c d →
              Set.Icc (boundaryFaceLowerCorner (D.targetLowerCorner q))
                  (boundaryFaceUpperCorner (D.targetUpperCorner q)) ⊆
                Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    BoundaryChartIFTCompactImageCoverData I x0 x1 a b Piece :=
  (D.toCompactImageBoxCoverData target_contains_selectedImageBox).toIFTCompactImageCoverData

end BoundaryChartIFTTargetCoverData

end ManifoldBoundary

end Stokes

end
