import Stokes.BoundaryChart.ControlledTargetBoxFromIFTAuto
import Stokes.BoundaryChart.LaterTargetShrinkFromSelectionAuto

/-!
# Compact image-box containment for controlled target boxes

`ControlledTargetBoxFromIFTAuto` still exposes older constructors whose input is
the broad callback saying that every compact coordinate image box chosen from a
source image lies in every later local-inverse target.  The selected-box/shrink
route normally gives a sharper object: one fixed compact image box, together
with later-target shrink data proving that this box lies in every selected
local-inverse target.

This file packages that sharper data as the compact-image predicate consumed by
the controlled-target constructors, and then exposes local-openness/IFT
constructors that avoid the older `hcontains` / `compactBox_subset` fields.
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
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {y : Fin n → Real}

/--
A selected target box plus later-target shrink data gives the compact-image
predicate needed by the local-openness/IFT target selector.
-/
theorem compactImageForLocalInverseTargetsOfShrink
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1 a b
        target.lowerCorner target.upperCorner y) :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y :=
  target.compactImageForLocalInverseTargets_of_contains
    shrink.target_contains_selectedImageBox

/--
The explicit compact image-box witness obtained from a target box and shrink
data.  This is the fixed-box replacement for the older arbitrary-box callback.
-/
def compactImageBoxForLocalInverseTargetsOfShrink
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1 a b
        target.lowerCorner target.upperCorner y) :
    BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets I x0 x1 a b y :=
  BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets.ofTargetBoxSelection
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b) (y := y)
    target shrink.target_contains_selectedImageBox

end BoundaryChartTargetBoxSelection

namespace BoundaryChartSelectedImageBoxContainment

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {y : Fin n → Real}
variable {U : Set (Fin n → Real)}

/-- Local-openness plus selected image-box containment gives a controlled
target box inside a prescribed target-side neighborhood. -/
theorem exists_controlledTargetBoxSelection_of_localOpenness
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y)
    (hU : U ∈ 𝓝 y)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d y U,
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_localOpenness_compactImage_subset
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (y := y) (U := U) hU himage D.compactImageForLocalInverseTargets

/-- Image-neighborhood spelling of the selected image-box route. -/
theorem exists_controlledTargetBoxSelectionInImage
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d y
            ((boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b),
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d :=
  D.exists_controlledTargetBoxSelection_of_localOpenness
    (U := (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b)
    himage himage

/-- IFT/local-openness spelling of the selected image-box route. -/
theorem exists_controlledTargetBoxSelection_of_IFT
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b
      (boundaryChartTransition I x0 x1 u))
    (hU : U ∈ 𝓝 (boundaryChartTransition I x0 x1 u))
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hderiv :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d (boundaryChartTransition I x0 x1 u) U,
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d :=
  D.exists_controlledTargetBoxSelection_of_localOpenness hU
    (boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
      hderiv hsurj hsource)

end BoundaryChartSelectedImageBoxContainment

/--
Local openness plus an explicitly selected target box and shrink data gives a
controlled target box.  The compact image-box containment is generated from the
selected target/shrink pair rather than from the older `hcontains` callback.
-/
theorem exists_controlledTargetBoxSelection_of_localOpenness_targetBoxShrink
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real}
    {y : Fin n → Real} {U : Set (Fin n → Real)}
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1 a b
        target.lowerCorner target.upperCorner y)
    (hU : U ∈ 𝓝 y)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d y U,
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_localOpenness_compactImage_subset
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (y := y) (U := U) hU himage
    (target.compactImageForLocalInverseTargetsOfShrink shrink)

/--
IFT version of `exists_controlledTargetBoxSelection_of_localOpenness_targetBoxShrink`.
-/
theorem exists_controlledTargetBoxSelection_of_IFT_targetBoxShrink
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real} {U : Set (Fin n → Real)}
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1 a b
        target.lowerCorner target.upperCorner
        (boundaryChartTransition I x0 x1 u))
    (hU : U ∈ 𝓝 (boundaryChartTransition I x0 x1 u))
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hderiv :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d (boundaryChartTransition I x0 x1 u) U,
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_localOpenness_targetBoxShrink
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (y := boundaryChartTransition I x0 x1 u) (U := U)
    target shrink hU
    (boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
      hderiv hsurj hsource)

/-- Local-openness plus an explicit compact image-box witness gives a
controlled target box. -/
theorem exists_controlledTargetBoxSelection_of_localOpenness_imageBox
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real}
    {y : Fin n → Real} {U : Set (Fin n → Real)}
    (imageBox :
      BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets
        I x0 x1 a b y)
    (hU : U ∈ 𝓝 y)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d y U,
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_localOpenness_compactImage_subset
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (y := y) (U := U) hU himage imageBox.compactImageForLocalInverseTargets

/-- IFT version of the explicit compact image-box controlled-target route. -/
theorem exists_controlledTargetBoxSelection_of_IFT_imageBox
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real} {U : Set (Fin n → Real)}
    (imageBox :
      BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets
        I x0 x1 a b (boundaryChartTransition I x0 x1 u))
    (hU : U ∈ 𝓝 (boundaryChartTransition I x0 x1 u))
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hderiv :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d (boundaryChartTransition I x0 x1 u) U,
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_localOpenness_imageBox
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (y := boundaryChartTransition I x0 x1 u) (U := U)
    imageBox hU
    (boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
      hderiv hsurj hsource)

namespace BoundaryChartSelectedBoxIFTPointContainsAutoData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/--
Pointwise selected-box IFT data with fixed image-box containment produces a
controlled target box, avoiding the older pointwise `compactBox_subset` field.
-/
theorem exists_controlledTargetBoxSelection
    (D : BoundaryChartSelectedBoxIFTPointContainsAutoData I x0 x1 ω a b)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 D.targetPoint) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d D.targetPoint U,
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d := by
  simpa [targetPoint] using
    D.selectedImageBoxContainment.exists_controlledTargetBoxSelection_of_localOpenness
      (U := U) hU D.image_mem_nhds

/-- Canonical controlled target box chosen from the fixed-image-box IFT data. -/
def controlledTargetBoxSelection
    (D : BoundaryChartSelectedBoxIFTPointContainsAutoData I x0 x1 ω a b)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 D.targetPoint) :
    Σ c : Fin (n + 1) → Real, Σ d : Fin (n + 1) → Real,
      BoundaryChartControlledTargetBoxSelectionData
        I x0 x1 a b c d D.targetPoint U :=
  ⟨Classical.choose (D.exists_controlledTargetBoxSelection hU),
    Classical.choose
      (Classical.choose_spec (D.exists_controlledTargetBoxSelection hU)),
    Classical.choose
      (Classical.choose_spec
        (Classical.choose_spec (D.exists_controlledTargetBoxSelection hU)))⟩

end BoundaryChartSelectedBoxIFTPointContainsAutoData

namespace BoundaryChartSelectedBoxLocalOpennessContainsCoverAutoData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
One active local-openness cover piece with fixed selected image-box containment
produces a controlled target box.
-/
theorem exists_controlledTargetBoxSelection
    (D : BoundaryChartSelectedBoxLocalOpennessContainsCoverAutoData
      I x0 x1 ω a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 (D.sourceLowerCorner q) (D.sourceUpperCorner q)
            c d (D.targetPoint q) U,
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d :=
  (D.selectedImageBoxContainment q hq).exists_controlledTargetBoxSelection_of_localOpenness
    (U := U) hU (D.image_mem_nhds q hq)

end BoundaryChartSelectedBoxLocalOpennessContainsCoverAutoData

namespace BoundaryChartSelectedBoxIFTContainsCompactCoverAutoData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
One active IFT cover piece with fixed selected image-box containment produces a
controlled target box.
-/
theorem exists_controlledTargetBoxSelection
    (D : BoundaryChartSelectedBoxIFTContainsCompactCoverAutoData
      I x0 x1 ω a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 (D.sourceLowerCorner q) (D.sourceUpperCorner q)
            c d (D.targetPoint q) U,
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d := by
  simpa [targetPoint] using
    (D.selectedImageBoxContainment q hq).exists_controlledTargetBoxSelection_of_localOpenness
      (U := U) hU
      (boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
        (D.hasStrictFDerivAt q hq) (D.tangentMap_surjective q hq)
        (D.source_mem_nhds q hq))

end BoundaryChartSelectedBoxIFTContainsCompactCoverAutoData

namespace BoundaryChartIFTTargetCoverLaterShrinkData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}
variable {D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece}

/--
One active IFT target-cover piece plus later-target shrink data produces a
controlled target box without exposing compact-box callbacks.
-/
theorem exists_controlledTargetBoxSelection
    (S : BoundaryChartIFTTargetCoverLaterShrinkData D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 (D.sourceLowerCorner q) (D.sourceUpperCorner q)
            c d (D.targetPoint q) U,
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_localOpenness_targetBoxShrink
    (I := I) (x0 := x0) (x1 := x1)
    (a := D.sourceLowerCorner q) (b := D.sourceUpperCorner q)
    (y := D.targetPoint q) (U := U)
    (D.toTargetBoxSelection q hq)
    (S.laterTargetShrink q hq)
    hU (D.image_mem_nhds q hq)

end BoundaryChartIFTTargetCoverLaterShrinkData

end ManifoldBoundary

end Stokes

end
