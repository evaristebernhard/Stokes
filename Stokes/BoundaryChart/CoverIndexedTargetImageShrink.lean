import Stokes.BoundaryChart.CoverIndexedTargetImageConstructor
import Stokes.BoundaryChart.CompactImageBoxContainmentAuto
import Stokes.BoundaryChart.CompactImageFromIFTAuto
import Stokes.BoundaryChart.LaterTargetShrinkFromSelectionAuto
import Stokes.BoundaryChart.TargetBoxSourceShrinkIFT

/-!
# Cover-indexed target-image shrink constructors

This file is the cover-indexed-facing shrink layer for boundary target images.

The previous target-image constructor can already turn selected image-box
containment into `BoundaryChartTransitionCompactBoxData`.  Here we remove one
more manual field: when a target box has later-target shrink data, the selected
image-box containment is built automatically and immediately projected to the
transition compact-box package consumed downstream.
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

namespace BoundaryChartTargetBoxSelection

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {y : Fin n → Real}

/--
A selected target box together with later-target shrink data produces the
transition compact-box package from local openness.  This avoids exposing the
intermediate `BoundaryChartSelectedImageBoxContainment` record at call sites.
-/
theorem exists_transitionCompactBoxData_of_localOpenness_shrink
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1 a b
        target.lowerCorner target.upperCorner y)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartTransitionCompactBoxData I x0 x1 a b,
      y ∈ lowerZeroFaceDomain T.lowerCorner T.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          T.lowerCorner T.upperCorner := by
  exact (target.selectedImageBoxContainmentOfShrink hbox shrink)
    |>.exists_transitionCompactBoxData_of_localOpenness himage

/--
IFT/local-openness version of
`exists_transitionCompactBoxData_of_localOpenness_shrink`.
-/
theorem exists_transitionCompactBoxData_of_IFT_shrink
    {u : Fin n → Real}
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1 a b
        target.lowerCorner target.upperCorner
        (boundaryChartTransition I x0 x1 u))
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hderiv :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤) :
    ∃ T : BoundaryChartTransitionCompactBoxData I x0 x1 a b,
      boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain T.lowerCorner T.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          T.lowerCorner T.upperCorner := by
  exact (target.selectedImageBoxContainmentOfShrink hbox shrink)
    |>.exists_transitionCompactBoxData_of_IFT hsource hderiv hsurj

end BoundaryChartTargetBoxSelection

namespace BoundaryChartLocalOpennessTargetCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
One active local-openness target-cover member already contains the two concrete
image-data halves (`targetBox_subset_image` and `compactImage`).  Therefore it
can be projected directly to transition compact-box data, with no
later-target-shrink callback.
-/
def transitionCompactBoxData
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    BoundaryChartTransitionCompactBoxData I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) :=
  (C.toTargetBoxSelection q hq).toTransitionCompactBoxData

/--
Direct compact-box existence from one active local-openness cover member.

This is the primitive constructor to prefer when the cover already stores the
selected target image/bijection fields.  The older later-target-shrink route is
only needed when the target image data itself has not yet been materialized.
-/
theorem exists_transitionCompactBoxData
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    ∃ T : BoundaryChartTransitionCompactBoxData I x0 x1
        (C.sourceLowerCorner q) (C.sourceUpperCorner q),
      C.targetPoint q ∈ lowerZeroFaceDomain T.lowerCorner T.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1
          (C.sourceLowerCorner q) (C.sourceUpperCorner q)
          T.lowerCorner T.upperCorner := by
  refine ⟨C.transitionCompactBoxData q hq, ?_, ?_⟩
  · simpa [transitionCompactBoxData,
      BoundaryChartTargetBoxSelection.toTransitionCompactBoxData] using
      C.targetPoint_mem q hq
  · simpa [transitionCompactBoxData,
      BoundaryChartTargetBoxSelection.toTransitionCompactBoxData] using
      C.imageData q hq

end BoundaryChartLocalOpennessTargetCover

namespace BoundaryChartIFTTargetCoverData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
One active IFT target-cover member as transition compact-box data.  The IFT
fields generate the local-openness neighborhood, while the explicit selected
target-box fields in the cover already provide image data.
-/
def transitionCompactBoxData
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces) :
    BoundaryChartTransitionCompactBoxData I x0 x1
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) :=
  (D.toTargetBoxSelection q hq).toTransitionCompactBoxData

/--
Direct compact-box existence from one active IFT cover member, without a
later-target-shrink package.
-/
theorem exists_transitionCompactBoxData
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces) :
    ∃ T : BoundaryChartTransitionCompactBoxData I x0 x1
        (D.sourceLowerCorner q) (D.sourceUpperCorner q),
      D.targetPoint q ∈ lowerZeroFaceDomain T.lowerCorner T.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1
          (D.sourceLowerCorner q) (D.sourceUpperCorner q)
          T.lowerCorner T.upperCorner := by
  refine ⟨D.transitionCompactBoxData q hq, ?_, ?_⟩
  · simpa [transitionCompactBoxData,
      BoundaryChartTargetBoxSelection.toTransitionCompactBoxData] using
      D.targetPoint_mem q hq
  · simpa [transitionCompactBoxData,
      BoundaryChartTargetBoxSelection.toTransitionCompactBoxData] using
      D.toLocalOpennessTargetCover.imageData q hq

end BoundaryChartIFTTargetCoverData

/-- Top-level spelling of the target-box/shrink local-openness constructor. -/
theorem exists_boundaryChartTransitionCompactBoxData_of_localOpenness_targetBoxShrink
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1 a b
        target.lowerCorner target.upperCorner y)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartTransitionCompactBoxData I x0 x1 a b,
      y ∈ lowerZeroFaceDomain T.lowerCorner T.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          T.lowerCorner T.upperCorner :=
  target.exists_transitionCompactBoxData_of_localOpenness_shrink hbox shrink himage

/-- Top-level IFT spelling of the target-box/shrink constructor. -/
theorem exists_boundaryChartTransitionCompactBoxData_of_IFT_targetBoxShrink
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} {u : Fin n → Real}
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1 a b
        target.lowerCorner target.upperCorner
        (boundaryChartTransition I x0 x1 u))
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hderiv :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤) :
    ∃ T : BoundaryChartTransitionCompactBoxData I x0 x1 a b,
      boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain T.lowerCorner T.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          T.lowerCorner T.upperCorner :=
  target.exists_transitionCompactBoxData_of_IFT_shrink
    hbox shrink hsource hderiv hsurj

namespace BoundaryChartLocalOpennessTargetCoverLaterShrinkData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}
variable {C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece}

/--
One active local-openness cover piece plus later-target shrink data gives the
transition compact-box package for that piece.
-/
theorem exists_transitionCompactBoxData
    (S : BoundaryChartLocalOpennessTargetCoverLaterShrinkData C)
    (q : Piece) (hq : q ∈ C.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)) :
    ∃ T : BoundaryChartTransitionCompactBoxData I x0 x1
        (C.sourceLowerCorner q) (C.sourceUpperCorner q),
      C.targetPoint q ∈ lowerZeroFaceDomain T.lowerCorner T.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1
          (C.sourceLowerCorner q) (C.sourceUpperCorner q)
          T.lowerCorner T.upperCorner := by
  exact (C.toTargetBoxSelection q hq)
    |>.exists_transitionCompactBoxData_of_localOpenness_shrink
      hbox (S.laterTargetShrink q hq) (C.image_mem_nhds q hq)

end BoundaryChartLocalOpennessTargetCoverLaterShrinkData

namespace BoundaryChartIFTTargetCoverLaterShrinkData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}
variable {D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece}

/--
One active IFT cover piece plus later-target shrink data gives the transition
compact-box package for that piece.  The local-openness neighborhood is
generated from the strict derivative and surjective tangential map stored in
the IFT cover.
-/
theorem exists_transitionCompactBoxData
    (S : BoundaryChartIFTTargetCoverLaterShrinkData D)
    (q : Piece) (hq : q ∈ D.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q)) :
    ∃ T : BoundaryChartTransitionCompactBoxData I x0 x1
        (D.sourceLowerCorner q) (D.sourceUpperCorner q),
      D.targetPoint q ∈ lowerZeroFaceDomain T.lowerCorner T.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1
          (D.sourceLowerCorner q) (D.sourceUpperCorner q)
          T.lowerCorner T.upperCorner := by
  exact (D.toTargetBoxSelection q hq)
    |>.exists_transitionCompactBoxData_of_localOpenness_shrink
      hbox (S.laterTargetShrink q hq) (D.image_mem_nhds q hq)

end BoundaryChartIFTTargetCoverLaterShrinkData

namespace BoundaryChartSourceShrinkInverseTargetBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {a b c d e f : Fin (n + 1) → Real} {u y : Fin n → Real}

/-- Completed source-shrink target-box data as transition compact-box data. -/
def toTransitionCompactBoxData
    (D : BoundaryChartSourceShrinkInverseTargetBoxData
      I x0 x1 a b c d e f u y) :
    BoundaryChartTransitionCompactBoxData I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner :=
  D.targetBoxSelection.toTransitionCompactBoxData

/--
Completed source-shrink inverse-target data directly gives the transition
compact-box package for its shrunken source and selected target.  This is the
field-eliminating route when source shrink has already synchronized the
`MapsTo` and local-inverse halves.
-/
theorem exists_transitionCompactBoxData
    (D : BoundaryChartSourceShrinkInverseTargetBoxData
      I x0 x1 a b c d e f u y) :
    ∃ T : BoundaryChartTransitionCompactBoxData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner,
      y ∈ lowerZeroFaceDomain T.lowerCorner T.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1
          D.sourceLowerCorner D.sourceUpperCorner
          T.lowerCorner T.upperCorner := by
  refine ⟨D.toTransitionCompactBoxData, ?_, ?_⟩
  · simpa [toTransitionCompactBoxData,
      BoundaryChartTargetBoxSelection.toTransitionCompactBoxData] using
      D.targetPoint_mem
  · simpa [toTransitionCompactBoxData,
      BoundaryChartTargetBoxSelection.toTransitionCompactBoxData] using
      D.imageData

/--
The target box stored in completed source-shrink data is a neighborhood of `y`
only when supplied by the caller; under that natural hypothesis, the source
image is also a neighborhood of `y`, because the packaged local inverse gives
surjectivity onto the selected target box.
-/
theorem image_mem_nhds_of_target_mem_nhds
    (D : BoundaryChartSourceShrinkInverseTargetBoxData
      I x0 x1 a b c d e f u y)
    (htarget : lowerZeroFaceDomain e f ∈ 𝓝 y) :
    (boundaryChartTransition I x0 x1) ''
        lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner ∈ 𝓝 y := by
  refine mem_of_superset htarget ?_
  intro z hz
  rcases D.imageData.surjOn hz with ⟨v, hv, hvz⟩
  exact ⟨v, hv, hvz⟩

/--
Completed source-shrink data plus ambient later-target shrink data produces
transition compact-box data, without manually constructing selected image-box
containment.
-/
theorem exists_transitionCompactBoxData_of_ambientShrink
    {ω : ManifoldForm I M n}
    (D : BoundaryChartSourceShrinkInverseTargetBoxData
      I x0 x1 a b c d e f u y)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner)
    (htarget : lowerZeroFaceDomain e f ∈ 𝓝 y)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d y) :
    ∃ T : BoundaryChartTransitionCompactBoxData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner,
      y ∈ lowerZeroFaceDomain T.lowerCorner T.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1
          D.sourceLowerCorner D.sourceUpperCorner
          T.lowerCorner T.upperCorner := by
  exact (D.toSelectedImageBoxContainmentOfAmbientShrink hbox shrink)
    |>.exists_transitionCompactBoxData_of_localOpenness
      (D.image_mem_nhds_of_target_mem_nhds htarget)

end BoundaryChartSourceShrinkInverseTargetBoxData

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {a b c d : Fin (n + 1) → Real} {u y : Fin n → Real}

/-- Open-partial-homeomorphism source-shrink data as transition compact-box data. -/
def toTransitionCompactBoxData
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData
      I x0 x1 a b c d u y) :
    BoundaryChartTransitionCompactBoxData I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner :=
  D.targetBoxSelection.toTransitionCompactBoxData

/--
Synchronized open-partial-homeomorphism source-shrink data directly produces
the transition compact-box package.  No later-target-shrink datum is needed:
the record already stores the selected target box, source-to-target maps-to,
and inverse maps-to fields.
-/
theorem exists_transitionCompactBoxData
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData
      I x0 x1 a b c d u y) :
    ∃ T : BoundaryChartTransitionCompactBoxData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner,
      y ∈ lowerZeroFaceDomain T.lowerCorner T.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1
          D.sourceLowerCorner D.sourceUpperCorner
          T.lowerCorner T.upperCorner := by
  refine ⟨D.toTransitionCompactBoxData, ?_, ?_⟩
  · simpa [toTransitionCompactBoxData,
      BoundaryChartTargetBoxSelection.toTransitionCompactBoxData] using
      D.targetPoint_mem
  · simpa [toTransitionCompactBoxData,
      BoundaryChartTargetBoxSelection.toTransitionCompactBoxData] using
      D.imageData

/--
The selected source image is a target-side neighborhood in the synchronized
open-partial-homeomorphism source-shrink route.  The proof uses the stored
target-neighborhood field and the local inverse/surjectivity projection.
-/
theorem image_mem_nhds
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData
      I x0 x1 a b c d u y) :
    (boundaryChartTransition I x0 x1) ''
        lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner ∈ 𝓝 y := by
  refine mem_of_superset D.target_mem_nhds ?_
  intro z hz
  rcases D.imageData_surjOn hz with ⟨v, hv, hvz⟩
  exact ⟨v, hv, hvz⟩

/--
Open-partial-homeomorphism source-shrink data plus ambient later-target shrink
data produces transition compact-box data, eliminating both the local-openness
field and the selected image-box containment field from downstream inputs.
-/
theorem exists_transitionCompactBoxData_of_ambientShrink
    {ω : ManifoldForm I M n}
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData
      I x0 x1 a b c d u y)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d y) :
    ∃ T : BoundaryChartTransitionCompactBoxData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner,
      y ∈ lowerZeroFaceDomain T.lowerCorner T.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1
          D.sourceLowerCorner D.sourceUpperCorner
          T.lowerCorner T.upperCorner := by
  exact (D.toSelectedImageBoxContainmentOfAmbientShrink hbox shrink)
    |>.exists_transitionCompactBoxData_of_localOpenness D.image_mem_nhds

end BoundaryChartSourceShrinkOpenPartialHomeomorphData

end ManifoldBoundary

end Stokes

end
