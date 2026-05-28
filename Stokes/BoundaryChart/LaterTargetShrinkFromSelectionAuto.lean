import Stokes.BoundaryChart.SelectedImageBoxContainmentFromShrinkAuto
import Stokes.BoundaryChart.TargetImageIFTBridge

/-!
# Later-target shrink data from selected boundary target boxes

`SelectedImageBoxContainmentFromShrinkAuto` reduces the remaining
selected-image-box callback to the statement that a chosen target box is
contained in every later local-inverse target.  Existing local-openness / IFT
target-cover data already fixes the selected target corners, but it does not
store the later-target shrink inequalities.

This file names that missing geometric datum in a reusable pointwise form and
projects it through the explicit local-openness and IFT target-cover APIs.  The
new records keep the real box-shrink obligation visible while avoiding long
callbacks at call sites.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section ManifoldBoundary

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Coordinatewise shrink data saying that a fixed selected target box is contained
in every later local-inverse target box selected around `y`.

The inequalities are the natural output of a chart-box shrink construction:
later lower corners lie below the selected lower corner, and selected upper
corners lie below later upper corners.
-/
structure BoundaryChartLaterTargetShrinkData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b selectedLower selectedUpper : Fin (n + 1) → Real)
    (y : Fin n → Real) where
  /-- Later target lower corners lie below the selected target lower corner. -/
  later_lower_le_selected_lower :
    ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
      y ∈ lowerZeroFaceDomain c d →
        boundaryChartLocalInverseData I x0 x1 a b c d →
          ∀ i : Fin n, c i.succ ≤ selectedLower i.succ
  /-- The selected target upper corner lies below every later target upper corner. -/
  selected_upper_le_later_upper :
    ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
      y ∈ lowerZeroFaceDomain c d →
        boundaryChartLocalInverseData I x0 x1 a b c d →
          ∀ i : Fin n, selectedUpper i.succ ≤ d i.succ

namespace BoundaryChartLaterTargetShrinkData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {a b selectedLower selectedUpper : Fin (n + 1) → Real}
variable {y : Fin n → Real}

/-- Convert coordinatewise shrink inequalities to the selected-target
containment record consumed downstream. -/
def toSelectedTargetContainsLaterTargets
    (D : BoundaryChartLaterTargetShrinkData
      I x0 x1 a b selectedLower selectedUpper y) :
    BoundaryChartSelectedTargetContainsLaterTargets
      I x0 x1 a b selectedLower selectedUpper y :=
  BoundaryChartSelectedTargetContainsLaterTargets.ofTangentBounds
    D.later_lower_le_selected_lower D.selected_upper_le_later_upper

/-- The same conversion in the ambient-target spelling used by source-shrink
data. -/
def toAmbientTargetContainsLaterTargets
    (D : BoundaryChartLaterTargetShrinkData
      I x0 x1 a b selectedLower selectedUpper y) :
    BoundaryChartAmbientTargetContainsLaterTargets
      I x0 x1 a b selectedLower selectedUpper y :=
  D.toSelectedTargetContainsLaterTargets

/-- Callback form expected by the selected-image-box constructors. -/
theorem target_contains_selectedImageBox
    (D : BoundaryChartLaterTargetShrinkData
      I x0 x1 a b selectedLower selectedUpper y) :
    ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
      y ∈ lowerZeroFaceDomain c d →
        boundaryChartLocalInverseData I x0 x1 a b c d →
          Set.Icc (boundaryFaceLowerCorner selectedLower)
              (boundaryFaceUpperCorner selectedUpper) ⊆
            Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d) :=
  D.toSelectedTargetContainsLaterTargets.target_contains_selectedImageBox

/-- Lower-zero target-domain containment induced by the shrink data. -/
theorem selectedTarget_subset_laterTargets
    (D : BoundaryChartLaterTargetShrinkData
      I x0 x1 a b selectedLower selectedUpper y)
    {c d : Fin (n + 1) → Real} (hc0 : c 0 = 0) (hle : c ≤ d)
    (hy : y ∈ lowerZeroFaceDomain c d)
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    lowerZeroFaceDomain selectedLower selectedUpper ⊆ lowerZeroFaceDomain c d :=
  D.toSelectedTargetContainsLaterTargets.selectedTarget_subset_laterTargets
    c d hc0 hle hy hlocal

end BoundaryChartLaterTargetShrinkData

namespace BoundaryChartTargetBoxSelection

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {y : Fin n → Real}

/-- A selected target-box record plus shrink data gives the downstream
selected-target containment record. -/
def selectedTargetContainsLaterTargetsOfShrink
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1 a b
        target.lowerCorner target.upperCorner y) :
    BoundaryChartSelectedTargetContainsLaterTargets I x0 x1 a b
      target.lowerCorner target.upperCorner y :=
  shrink.toSelectedTargetContainsLaterTargets

/-- Selected-image-box containment from a target-box selection and its
later-target shrink data. -/
def selectedImageBoxContainmentOfShrink
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1 a b
        target.lowerCorner target.upperCorner y) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y :=
  target.selectedImageBoxContainmentOfLowerZeroSubsetLater hbox
    (target.selectedTargetContainsLaterTargetsOfShrink shrink)

end BoundaryChartTargetBoxSelection

namespace BoundaryChartLocalOpennessTargetCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/-- Pointwise selected-target containment for one active local-openness target
cover member, generated from coordinatewise later-target shrink data. -/
def selectedTargetContainsLaterTargetsOfShrink
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (q : Piece) (_hq : q ∈ C.activePieces)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1
        (C.sourceLowerCorner q) (C.sourceUpperCorner q)
        (C.targetLowerCorner q) (C.targetUpperCorner q) (C.targetPoint q)) :
    BoundaryChartSelectedTargetContainsLaterTargets I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)
      (C.targetLowerCorner q) (C.targetUpperCorner q) (C.targetPoint q) :=
  shrink.toSelectedTargetContainsLaterTargets

/-- Compact-image-box cover from explicit local-openness target data plus
later-target shrink data for every active selected target box. -/
def toCompactImageBoxCoverOfShrink
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (shrink :
      ∀ q, q ∈ C.activePieces →
        BoundaryChartLaterTargetShrinkData I x0 x1
          (C.sourceLowerCorner q) (C.sourceUpperCorner q)
          (C.targetLowerCorner q) (C.targetUpperCorner q) (C.targetPoint q)) :
    BoundaryChartLocalOpennessCompactImageBoxCover I x0 x1 a b Piece :=
  C.toCompactImageBoxCover fun q hq =>
    (shrink q hq).target_contains_selectedImageBox

/-- Existing local-openness compact-image cover generated from explicit target
selection and later-target shrink data. -/
def toLocalOpennessCompactImageCoverOfShrink
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (shrink :
      ∀ q, q ∈ C.activePieces →
        BoundaryChartLaterTargetShrinkData I x0 x1
          (C.sourceLowerCorner q) (C.sourceUpperCorner q)
          (C.targetLowerCorner q) (C.targetUpperCorner q) (C.targetPoint q)) :
    BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece :=
  (C.toCompactImageBoxCoverOfShrink shrink).toLocalOpennessCompactImageCover

end BoundaryChartLocalOpennessTargetCover

/-- Cover-level shrink package for explicit local-openness target-cover data. -/
structure BoundaryChartLocalOpennessTargetCoverLaterShrinkData {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece) where
  /-- Later-target shrink data for every active selected target box. -/
  laterTargetShrink :
    ∀ q, q ∈ C.activePieces →
      BoundaryChartLaterTargetShrinkData I x0 x1
        (C.sourceLowerCorner q) (C.sourceUpperCorner q)
        (C.targetLowerCorner q) (C.targetUpperCorner q) (C.targetPoint q)

namespace BoundaryChartLocalOpennessTargetCoverLaterShrinkData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}
variable {C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece}

/-- Pointwise projection to the selected-target containment record. -/
def selectedTargetContainsLaterTargets
    (D : BoundaryChartLocalOpennessTargetCoverLaterShrinkData C)
    (q : Piece) (hq : q ∈ C.activePieces) :
    BoundaryChartSelectedTargetContainsLaterTargets I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)
      (C.targetLowerCorner q) (C.targetUpperCorner q) (C.targetPoint q) :=
  (D.laterTargetShrink q hq).toSelectedTargetContainsLaterTargets

/-- Compact-image-box cover generated from the packaged cover-level shrink
data. -/
def toCompactImageBoxCover
    (D : BoundaryChartLocalOpennessTargetCoverLaterShrinkData C) :
    BoundaryChartLocalOpennessCompactImageBoxCover I x0 x1 a b Piece :=
  C.toCompactImageBoxCoverOfShrink D.laterTargetShrink

/-- Existing local-openness compact-image cover generated from the packaged
cover-level shrink data. -/
def toLocalOpennessCompactImageCover
    (D : BoundaryChartLocalOpennessTargetCoverLaterShrinkData C) :
    BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece :=
  C.toLocalOpennessCompactImageCoverOfShrink D.laterTargetShrink

end BoundaryChartLocalOpennessTargetCoverLaterShrinkData

namespace BoundaryChartIFTTargetCoverData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/-- Pointwise selected-target containment for one active IFT target-cover member,
generated from coordinatewise later-target shrink data. -/
def selectedTargetContainsLaterTargetsOfShrink
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) (_hq : q ∈ D.activePieces)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1
        (D.sourceLowerCorner q) (D.sourceUpperCorner q)
        (D.targetLowerCorner q) (D.targetUpperCorner q) (D.targetPoint q)) :
    BoundaryChartSelectedTargetContainsLaterTargets I x0 x1
      (D.sourceLowerCorner q) (D.sourceUpperCorner q)
      (D.targetLowerCorner q) (D.targetUpperCorner q) (D.targetPoint q) :=
  shrink.toSelectedTargetContainsLaterTargets

/-- Compact-image-box IFT cover data from explicit IFT target data plus
later-target shrink data for every active selected target box. -/
def toCompactImageBoxCoverDataOfShrink
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (shrink :
      ∀ q, q ∈ D.activePieces →
        BoundaryChartLaterTargetShrinkData I x0 x1
          (D.sourceLowerCorner q) (D.sourceUpperCorner q)
          (D.targetLowerCorner q) (D.targetUpperCorner q) (D.targetPoint q)) :
    BoundaryChartIFTCompactImageBoxCoverData I x0 x1 a b Piece :=
  D.toCompactImageBoxCoverData fun q hq =>
    (shrink q hq).target_contains_selectedImageBox

/-- Existing IFT compact-image cover generated from explicit target selection
and later-target shrink data. -/
def toIFTCompactImageCoverDataOfShrink
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (shrink :
      ∀ q, q ∈ D.activePieces →
        BoundaryChartLaterTargetShrinkData I x0 x1
          (D.sourceLowerCorner q) (D.sourceUpperCorner q)
          (D.targetLowerCorner q) (D.targetUpperCorner q) (D.targetPoint q)) :
    BoundaryChartIFTCompactImageCoverData I x0 x1 a b Piece :=
  (D.toCompactImageBoxCoverDataOfShrink shrink).toIFTCompactImageCoverData

end BoundaryChartIFTTargetCoverData

/-- Cover-level shrink package for explicit IFT target-cover data. -/
structure BoundaryChartIFTTargetCoverLaterShrinkData {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece) where
  /-- Later-target shrink data for every active selected target box. -/
  laterTargetShrink :
    ∀ q, q ∈ D.activePieces →
      BoundaryChartLaterTargetShrinkData I x0 x1
        (D.sourceLowerCorner q) (D.sourceUpperCorner q)
        (D.targetLowerCorner q) (D.targetUpperCorner q) (D.targetPoint q)

namespace BoundaryChartIFTTargetCoverLaterShrinkData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}
variable {D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece}

/-- Pointwise projection to the selected-target containment record. -/
def selectedTargetContainsLaterTargets
    (S : BoundaryChartIFTTargetCoverLaterShrinkData D)
    (q : Piece) (hq : q ∈ D.activePieces) :
    BoundaryChartSelectedTargetContainsLaterTargets I x0 x1
      (D.sourceLowerCorner q) (D.sourceUpperCorner q)
      (D.targetLowerCorner q) (D.targetUpperCorner q) (D.targetPoint q) :=
  (S.laterTargetShrink q hq).toSelectedTargetContainsLaterTargets

/-- Compact-image-box IFT cover data generated from the packaged cover-level
shrink data. -/
def toCompactImageBoxCoverData
    (S : BoundaryChartIFTTargetCoverLaterShrinkData D) :
    BoundaryChartIFTCompactImageBoxCoverData I x0 x1 a b Piece :=
  D.toCompactImageBoxCoverDataOfShrink S.laterTargetShrink

/-- Existing IFT compact-image cover generated from the packaged cover-level
shrink data. -/
def toIFTCompactImageCoverData
    (S : BoundaryChartIFTTargetCoverLaterShrinkData D) :
    BoundaryChartIFTCompactImageCoverData I x0 x1 a b Piece :=
  D.toIFTCompactImageCoverDataOfShrink S.laterTargetShrink

end BoundaryChartIFTTargetCoverLaterShrinkData

namespace BoundaryChartSourceShrinkInverseTargetBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d e f : Fin (n + 1) → Real} {u y : Fin n → Real}

/-- Completed source-shrink data consumes pointwise ambient later-target shrink
data without exposing the coordinatewise callbacks again. -/
def ambientTargetContainsLaterTargetsOfShrink
    (D : BoundaryChartSourceShrinkInverseTargetBoxData
      I x0 x1 a b c d e f u y)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d y) :
    BoundaryChartAmbientTargetContainsLaterTargets I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner c d y :=
  shrink.toAmbientTargetContainsLaterTargets

/-- Selected-image-box containment for completed source-shrink data from
ambient later-target shrink data. -/
def toSelectedImageBoxContainmentOfAmbientShrink
    (D : BoundaryChartSourceShrinkInverseTargetBoxData
      I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d y) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner y :=
  D.toSelectedImageBoxContainmentOfAmbientContainsLaterTargets hbox
    (D.ambientTargetContainsLaterTargetsOfShrink shrink)

end BoundaryChartSourceShrinkInverseTargetBoxData

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real} {u y : Fin n → Real}

/-- Open-partial-homeomorphism source-shrink data consumes pointwise ambient
later-target shrink data without exposing the coordinatewise callbacks again. -/
def ambientTargetContainsLaterTargetsOfShrink
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData
      I x0 x1 a b c d u y)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d y) :
    BoundaryChartAmbientTargetContainsLaterTargets I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner c d y :=
  shrink.toAmbientTargetContainsLaterTargets

/-- Selected-image-box containment for open-partial-homeomorphism source-shrink
data from ambient later-target shrink data. -/
def toSelectedImageBoxContainmentOfAmbientShrink
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData
      I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d y) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner y :=
  D.toSelectedImageBoxContainmentOfAmbientContainsLaterTargets hbox
    (D.ambientTargetContainsLaterTargetsOfShrink shrink)

end BoundaryChartSourceShrinkOpenPartialHomeomorphData

end ManifoldBoundary

end Stokes

end
