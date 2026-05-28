import Stokes.BoundaryChart.SelectedBoxContainsAuto

/-!
# Selected image boxes from target-box data

`SelectedBoxContainsAuto` names the useful caller-facing package
`BoundaryChartSelectedImageBoxContainment`: a selected source boundary box plus
one fixed compact coordinate image box contained in all later local-inverse
targets.  This file builds that package from the target-box and compact-image
box data already produced by the target selection pipeline.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section ManifoldBoundary

universe u w p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace BoundaryChartSelectedImageBoxContainment

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {y : Fin n → Real}

/-- Constructor from the explicit compact coordinate image-box witness. -/
def ofCompactCoordinateImageBoxForLocalInverseTargets
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (imageBox :
      BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets
        I x0 x1 a b y) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y where
  selectedBox := hbox
  imageBoxForLocalInverseTargets := imageBox

@[simp]
theorem ofCompactCoordinateImageBoxForLocalInverseTargets_selectedBox
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (imageBox :
      BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets
        I x0 x1 a b y) :
    (ofCompactCoordinateImageBoxForLocalInverseTargets
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (y := y) hbox imageBox).selectedBox = hbox :=
  rfl

@[simp]
theorem ofCompactCoordinateImageBoxForLocalInverseTargets_imageBox
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (imageBox :
      BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets
        I x0 x1 a b y) :
    (ofCompactCoordinateImageBoxForLocalInverseTargets
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (y := y) hbox imageBox).imageBoxForLocalInverseTargets =
        imageBox :=
  rfl

/--
Constructor from an already selected target box, provided all later
local-inverse targets contain that selected target's tangential image box.
-/
def ofTargetBoxSelection
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (target_contains_selectedImageBox :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            Set.Icc (boundaryFaceLowerCorner target.lowerCorner)
                (boundaryFaceUpperCorner target.upperCorner) ⊆
              Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y :=
  ofCompactCoordinateImageBoxForLocalInverseTargets hbox
    (BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets.ofTargetBoxSelection
      (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b) (y := y)
      target target_contains_selectedImageBox)

/-- Predicate projection generated from a target box and containment promise. -/
theorem compactImageForLocalInverseTargets_ofTargetBoxSelection
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (target_contains_selectedImageBox :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            Set.Icc (boundaryFaceLowerCorner target.lowerCorner)
                (boundaryFaceUpperCorner target.upperCorner) ⊆
              Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y :=
  (ofTargetBoxSelection
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    (a := a) (b := b) (y := y)
    hbox target target_contains_selectedImageBox).compactImageForLocalInverseTargets

/--
Local-openness target-image data from one selected target box and a later-target
containment promise.  Callers no longer build
`BoundaryChartSelectedImageBoxContainment` by hand.
-/
theorem exists_autoData_of_localOpenness_targetBoxSelection
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (target_contains_selectedImageBox :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            Set.Icc (boundaryFaceLowerCorner target.lowerCorner)
                (boundaryFaceUpperCorner target.upperCorner) ⊆
              Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d))
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          T.targetLowerCorner T.targetUpperCorner :=
  exists_autoData_of_localOpenness
    (ofTargetBoxSelection
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (y := y)
      hbox target target_contains_selectedImageBox)
    himage

/-- Local-openness target-image data from an explicit compact image-box witness. -/
theorem exists_autoData_of_localOpenness_imageBox
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (imageBox :
      BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets
        I x0 x1 a b y)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          T.targetLowerCorner T.targetUpperCorner :=
  exists_autoData_of_localOpenness
    (ofCompactCoordinateImageBoxForLocalInverseTargets
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (y := y) hbox imageBox)
    himage

/-- Local-openness plus target-box containment gives oriented-atlas COV. -/
theorem exists_orientedCOV_of_localOpenness_targetBoxSelection_orientedAtlas
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (target_contains_selectedImageBox :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            Set.Icc (boundaryFaceLowerCorner target.lowerCorner)
                (boundaryFaceUpperCorner target.upperCorner) ⊆
              Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d))
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner :=
  exists_orientedChangeOfVariables_of_localOpenness_orientedAtlas
    (ofTargetBoxSelection
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (y := y)
      hbox target target_contains_selectedImageBox)
    A hx0 hx1 himage

/-- Local-openness plus target-box containment gives oriented-manifold COV. -/
theorem exists_orientedCOV_of_localOpenness_targetBoxSelection_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (target_contains_selectedImageBox :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            Set.Icc (boundaryFaceLowerCorner target.lowerCorner)
                (boundaryFaceUpperCorner target.upperCorner) ⊆
              Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d))
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner :=
  exists_orientedChangeOfVariables_of_localOpenness_orientedManifold
    (ofTargetBoxSelection
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (y := y)
      hbox target target_contains_selectedImageBox)
    himage

/-- Local-openness plus an explicit compact image-box witness gives oriented-atlas COV. -/
theorem exists_orientedCOV_of_localOpenness_imageBox_orientedAtlas
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (imageBox :
      BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets
        I x0 x1 a b y)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner :=
  exists_orientedChangeOfVariables_of_localOpenness_orientedAtlas
    (ofCompactCoordinateImageBoxForLocalInverseTargets
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (y := y) hbox imageBox)
    A hx0 hx1 himage

/-- Local-openness plus an explicit compact image-box witness gives oriented-manifold COV. -/
theorem exists_orientedCOV_of_localOpenness_imageBox_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (imageBox :
      BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets
        I x0 x1 a b y)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner :=
  exists_orientedChangeOfVariables_of_localOpenness_orientedManifold
    (ofCompactCoordinateImageBoxForLocalInverseTargets
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (y := y) hbox imageBox)
    himage

/-- IFT plus target-box containment gives oriented-atlas COV. -/
theorem exists_orientedCOV_of_IFT_targetBoxSelection_orientedAtlas
    [IsManifold I 1 M]
    {u : Fin n → Real}
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hderiv :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤)
    (target_contains_selectedImageBox :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            Set.Icc (boundaryFaceLowerCorner target.lowerCorner)
                (boundaryFaceUpperCorner target.upperCorner) ⊆
              Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner :=
  exists_orientedChangeOfVariables_of_localOpenness_orientedAtlas
    (ofTargetBoxSelection
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (y := boundaryChartTransition I x0 x1 u)
      hbox target target_contains_selectedImageBox)
    A hx0 hx1
    (boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
      hderiv hsurj hsource)

/-- IFT plus target-box containment gives oriented-manifold COV. -/
theorem exists_orientedCOV_of_IFT_targetBoxSelection_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hderiv :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤)
    (target_contains_selectedImageBox :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            Set.Icc (boundaryFaceLowerCorner target.lowerCorner)
                (boundaryFaceUpperCorner target.upperCorner) ⊆
              Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner :=
  exists_orientedChangeOfVariables_of_localOpenness_orientedManifold
    (ofTargetBoxSelection
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (y := boundaryChartTransition I x0 x1 u)
      hbox target target_contains_selectedImageBox)
    (boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
      hderiv hsurj hsource)

/-- IFT plus an explicit compact image-box witness gives oriented-atlas COV. -/
theorem exists_orientedCOV_of_IFT_imageBox_orientedAtlas
    [IsManifold I 1 M]
    {u : Fin n → Real}
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (imageBox :
      BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets
        I x0 x1 a b (boundaryChartTransition I x0 x1 u))
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hderiv :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner :=
  exists_orientedChangeOfVariables_of_localOpenness_orientedAtlas
    (ofCompactCoordinateImageBoxForLocalInverseTargets
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (y := boundaryChartTransition I x0 x1 u)
      hbox imageBox)
    A hx0 hx1
    (boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
      hderiv hsurj hsource)

/-- IFT plus an explicit compact image-box witness gives oriented-manifold COV. -/
theorem exists_orientedCOV_of_IFT_imageBox_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (imageBox :
      BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets
        I x0 x1 a b (boundaryChartTransition I x0 x1 u))
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hderiv :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner :=
  exists_orientedChangeOfVariables_of_localOpenness_orientedManifold
    (ofCompactCoordinateImageBoxForLocalInverseTargets
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (y := boundaryChartTransition I x0 x1 u)
      hbox imageBox)
    (boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
      hderiv hsurj hsource)

end BoundaryChartSelectedImageBoxContainment

namespace BoundaryChartLocalOpennessCompactImageBoxCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
Expose a compact-image-box local-openness cover as selected-box containment
data once selected source boxes are supplied for the active pieces.
-/
def toSelectedBoxLocalOpennessContainsCoverAutoData
    (C : BoundaryChartLocalOpennessCompactImageBoxCover I x0 x1 a b Piece)
    (selectedBox :
      ∀ q, q ∈ C.activePieces →
        boundaryChartSelectedBox I x0 x1 ω
          (C.sourceLowerCorner q) (C.sourceUpperCorner q)) :
    BoundaryChartSelectedBoxLocalOpennessContainsCoverAutoData
      I x0 x1 ω a b Piece where
  toBoundaryChartCompactSourceBoxCover := C.toBoundaryChartCompactSourceBoxCover
  targetPoint := C.targetPoint
  image_mem_nhds := C.image_mem_nhds
  selectedImageBoxContainment := fun q hq =>
    BoundaryChartSelectedImageBoxContainment.ofCompactCoordinateImageBoxForLocalInverseTargets
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := C.sourceLowerCorner q) (b := C.sourceUpperCorner q)
      (y := C.targetPoint q)
      (selectedBox q hq) (C.compactImageBoxForLocalInverseTargets q hq)

/-- Forget the selected-box containment cover to the existing local-openness compact-image cover. -/
theorem toSelectedBoxLocalOpennessContainsCoverAutoData_forget
    (C : BoundaryChartLocalOpennessCompactImageBoxCover I x0 x1 a b Piece)
    (selectedBox :
      ∀ q, q ∈ C.activePieces →
        boundaryChartSelectedBox I x0 x1 ω
          (C.sourceLowerCorner q) (C.sourceUpperCorner q)) :
    (C.toSelectedBoxLocalOpennessContainsCoverAutoData
      (ω := ω) selectedBox).toLocalOpennessCompactImageCover =
        C.toLocalOpennessCompactImageCover := by
  rfl

end BoundaryChartLocalOpennessCompactImageBoxCover

namespace BoundaryChartIFTCompactImageBoxCoverData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
Expose an IFT compact-image-box cover as selected-box containment data once
selected source boxes are supplied for active pieces.
-/
def toSelectedBoxIFTContainsCompactCoverAutoData
    (D : BoundaryChartIFTCompactImageBoxCoverData I x0 x1 a b Piece)
    (selectedBox :
      ∀ q, q ∈ D.activePieces →
        boundaryChartSelectedBox I x0 x1 ω
          (D.sourceLowerCorner q) (D.sourceUpperCorner q)) :
    BoundaryChartSelectedBoxIFTContainsCompactCoverAutoData
      I x0 x1 ω a b Piece where
  toBoundaryChartCompactSourceBoxCover := D.toBoundaryChartCompactSourceBoxCover
  sourcePoint := D.sourcePoint
  sourcePoint_mem := D.sourcePoint_mem
  source_mem_nhds := D.source_mem_nhds
  hasStrictFDerivAt := D.hasStrictFDerivAt
  tangentMap_surjective := D.tangentMap_surjective
  selectedImageBoxContainment := fun q hq =>
    BoundaryChartSelectedImageBoxContainment.ofCompactCoordinateImageBoxForLocalInverseTargets
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := D.sourceLowerCorner q) (b := D.sourceUpperCorner q)
      (y := boundaryChartTransition I x0 x1 (D.sourcePoint q))
      (selectedBox q hq) (D.compactImageBoxForLocalInverseTargets q hq)

/-- Forget the selected-box IFT containment cover to the existing IFT compact-image cover. -/
theorem toSelectedBoxIFTContainsCompactCoverAutoData_forget
    (D : BoundaryChartIFTCompactImageBoxCoverData I x0 x1 a b Piece)
    (selectedBox :
      ∀ q, q ∈ D.activePieces →
        boundaryChartSelectedBox I x0 x1 ω
          (D.sourceLowerCorner q) (D.sourceUpperCorner q)) :
    (D.toSelectedBoxIFTContainsCompactCoverAutoData
      (ω := ω) selectedBox).toIFTCompactImageCoverData =
        D.toIFTCompactImageCoverData := by
  rfl

end BoundaryChartIFTCompactImageBoxCoverData

namespace BoundaryChartLocalOpennessTargetCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
Build selected-box containment data from an explicit local-openness target cover
and the containment of each selected target image box in later local-inverse
targets.
-/
def toSelectedBoxContainsCoverAutoDataOfContains
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (selectedBox :
      ∀ q, q ∈ C.activePieces →
        boundaryChartSelectedBox I x0 x1 ω
          (C.sourceLowerCorner q) (C.sourceUpperCorner q))
    (target_contains_selectedImageBox :
      ∀ q, q ∈ C.activePieces →
        ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
          C.targetPoint q ∈ lowerZeroFaceDomain c d →
            boundaryChartLocalInverseData I x0 x1
              (C.sourceLowerCorner q) (C.sourceUpperCorner q) c d →
              Set.Icc (boundaryFaceLowerCorner (C.targetLowerCorner q))
                  (boundaryFaceUpperCorner (C.targetUpperCorner q)) ⊆
                Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    BoundaryChartSelectedBoxLocalOpennessContainsCoverAutoData
      I x0 x1 ω a b Piece :=
  BoundaryChartLocalOpennessCompactImageBoxCover.toSelectedBoxLocalOpennessContainsCoverAutoData
    (C.toCompactImageBoxCover target_contains_selectedImageBox) selectedBox

end BoundaryChartLocalOpennessTargetCover

namespace BoundaryChartIFTTargetCoverData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
Build selected-box IFT containment data from an explicit IFT target cover and
the containment of each selected target image box in later local-inverse
targets.
-/
def toSelectedBoxIFTContainsCompactCoverAutoDataOfContains
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (selectedBox :
      ∀ q, q ∈ D.activePieces →
        boundaryChartSelectedBox I x0 x1 ω
          (D.sourceLowerCorner q) (D.sourceUpperCorner q))
    (target_contains_selectedImageBox :
      ∀ q, q ∈ D.activePieces →
        ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
          D.targetPoint q ∈ lowerZeroFaceDomain c d →
            boundaryChartLocalInverseData I x0 x1
              (D.sourceLowerCorner q) (D.sourceUpperCorner q) c d →
              Set.Icc (boundaryFaceLowerCorner (D.targetLowerCorner q))
                  (boundaryFaceUpperCorner (D.targetUpperCorner q)) ⊆
                Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    BoundaryChartSelectedBoxIFTContainsCompactCoverAutoData
      I x0 x1 ω a b Piece :=
  BoundaryChartIFTCompactImageBoxCoverData.toSelectedBoxIFTContainsCompactCoverAutoData
    (D.toCompactImageBoxCoverData target_contains_selectedImageBox) selectedBox

end BoundaryChartIFTTargetCoverData

end ManifoldBoundary

end Stokes

end
