import Stokes.BoundaryChart.CompactImageBoxContainmentAuto
import Stokes.BoundaryChart.SelectedBoxContainsAuto
import Stokes.BoundaryChart.SelectedImageBoxContainmentFromShrinkAuto
import Stokes.BoundaryChart.ControlledTargetBoxFromIFTAuto

/-!
# Controlled target boxes with no compact-containment callback

This file is the caller-facing endpoint of the selected-box route for
controlled target boxes.  Earlier layers replaced the old arbitrary
`compactBox_subset` / `hcontains` callbacks with one selected target box and
later-target shrink data.  The declarations here make that replacement
available directly at the local-openness, IFT, pointwise, and finite-cover
interfaces.
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

/--
Local-openness controlled-target constructor whose only remaining containment
input is the natural coordinatewise later-target shrink bound for the selected
target box.
-/
theorem exists_controlledTargetBoxSelection_of_localOpenness_targetBoxTangentBounds
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real}
    {y : Fin n → Real} {U : Set (Fin n → Real)}
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (hlower :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            ∀ i : Fin n, c i.succ ≤ target.lowerCorner i.succ)
    (hupper :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            ∀ i : Fin n, target.upperCorner i.succ ≤ d i.succ)
    (hU : U ∈ 𝓝 y)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ D : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d y U,
        D.laterLowerCorner = c ∧ D.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_localOpenness_targetBoxShrink
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (y := y) (U := U) target
    { later_lower_le_selected_lower := hlower
      selected_upper_le_later_upper := hupper }
    hU himage

/--
IFT controlled-target constructor with no `compactBox_subset` or `hcontains`
argument.  The selected target box is controlled by tangent-coordinate shrink
bounds.
-/
theorem exists_controlledTargetBoxSelection_of_IFT_targetBoxTangentBounds
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real} {U : Set (Fin n → Real)}
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (hU : U ∈ 𝓝 (boundaryChartTransition I x0 x1 u))
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hderiv :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤)
    (hlower :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            ∀ i : Fin n, c i.succ ≤ target.lowerCorner i.succ)
    (hupper :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            ∀ i : Fin n, target.upperCorner i.succ ≤ d i.succ) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ D : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d (boundaryChartTransition I x0 x1 u) U,
        D.laterLowerCorner = c ∧ D.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_IFT_targetBoxShrink
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (u := u) (U := U) target
    { later_lower_le_selected_lower := hlower
      selected_upper_le_later_upper := hupper }
    hU hsource hderiv hsurj

namespace BoundaryChartSelectedBoxIFTPointContainsAutoData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {u : Fin n → Real}

/--
Build pointwise selected-box IFT containment data from a selected target box and
later-target shrink data.
-/
def ofTargetBoxShrink
    (sourcePoint_mem : u ∈ lowerZeroFaceDomain a b)
    (source_mem_nhds : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hasStrictFDerivAt :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (tangentMap_surjective :
      (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1 a b
        target.lowerCorner target.upperCorner
        (boundaryChartTransition I x0 x1 u)) :
    BoundaryChartSelectedBoxIFTPointContainsAutoData I x0 x1 ω a b where
  sourcePoint := u
  sourcePoint_mem := sourcePoint_mem
  source_mem_nhds := source_mem_nhds
  hasStrictFDerivAt := hasStrictFDerivAt
  tangentMap_surjective := tangentMap_surjective
  selectedImageBoxContainment :=
    target.selectedImageBoxContainmentOfShrink hbox shrink

/--
Pointwise selected-box IFT containment data from tangent-coordinate shrink
bounds.
-/
def ofTargetBoxTangentBounds
    (sourcePoint_mem : u ∈ lowerZeroFaceDomain a b)
    (source_mem_nhds : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hasStrictFDerivAt :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (tangentMap_surjective :
      (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (hlower :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            ∀ i : Fin n, c i.succ ≤ target.lowerCorner i.succ)
    (hupper :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            ∀ i : Fin n, target.upperCorner i.succ ≤ d i.succ) :
    BoundaryChartSelectedBoxIFTPointContainsAutoData I x0 x1 ω a b :=
  ofTargetBoxShrink
    (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b) (u := u)
    sourcePoint_mem source_mem_nhds hasStrictFDerivAt tangentMap_surjective
    hbox target
    { later_lower_le_selected_lower := hlower
      selected_upper_le_later_upper := hupper }

/--
Pointwise selected-box IFT data from shrink bounds produces a controlled target
box in any prescribed target-side neighborhood.
-/
theorem exists_controlledTargetBoxSelection_ofTargetBoxShrink
    (sourcePoint_mem : u ∈ lowerZeroFaceDomain a b)
    (source_mem_nhds : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hasStrictFDerivAt :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (tangentMap_surjective :
      (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1 a b
        target.lowerCorner target.upperCorner
        (boundaryChartTransition I x0 x1 u))
    {U : Set (Fin n → Real)}
    (hU : U ∈ 𝓝 (boundaryChartTransition I x0 x1 u)) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d (boundaryChartTransition I x0 x1 u) U,
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d := by
  simpa [targetPoint] using
    (ofTargetBoxShrink
      (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b) (u := u)
      sourcePoint_mem source_mem_nhds hasStrictFDerivAt tangentMap_surjective
      hbox target shrink).exists_controlledTargetBoxSelection hU

end BoundaryChartSelectedBoxIFTPointContainsAutoData

namespace BoundaryChartLocalOpennessTargetCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
Expose a local-openness target cover as selected-box containment data using
only per-piece later-target shrink data.
-/
def toSelectedBoxLocalOpennessContainsCoverAutoDataOfShrink
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (selectedBox :
      ∀ q, q ∈ C.activePieces →
        boundaryChartSelectedBox I x0 x1 ω
          (C.sourceLowerCorner q) (C.sourceUpperCorner q))
    (shrink :
      ∀ q, q ∈ C.activePieces →
        BoundaryChartLaterTargetShrinkData I x0 x1
          (C.sourceLowerCorner q) (C.sourceUpperCorner q)
          (C.targetLowerCorner q) (C.targetUpperCorner q)
          (C.targetPoint q)) :
    BoundaryChartSelectedBoxLocalOpennessContainsCoverAutoData
      I x0 x1 ω a b Piece :=
  (C.toCompactImageBoxCoverOfShrink shrink).toSelectedBoxLocalOpennessContainsCoverAutoData
    selectedBox

/--
One active local-openness cover member plus later-target shrink data produces a
controlled target box with no compact-containment callback.
-/
theorem exists_controlledTargetBoxSelectionOfShrink
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1
        (C.sourceLowerCorner q) (C.sourceUpperCorner q)
        (C.targetLowerCorner q) (C.targetUpperCorner q)
        (C.targetPoint q))
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ D : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 (C.sourceLowerCorner q) (C.sourceUpperCorner q)
            c d (C.targetPoint q) U,
        D.laterLowerCorner = c ∧ D.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_localOpenness_targetBoxShrink
    (I := I) (x0 := x0) (x1 := x1)
    (a := C.sourceLowerCorner q) (b := C.sourceUpperCorner q)
    (y := C.targetPoint q) (U := U)
    (C.toTargetBoxSelection q hq) shrink hU (C.image_mem_nhds q hq)

end BoundaryChartLocalOpennessTargetCover

namespace BoundaryChartIFTTargetCoverData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
Expose an IFT target cover as selected-box containment data using only
per-piece later-target shrink data.
-/
def toSelectedBoxIFTContainsCompactCoverAutoDataOfShrink
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (selectedBox :
      ∀ q, q ∈ D.activePieces →
        boundaryChartSelectedBox I x0 x1 ω
          (D.sourceLowerCorner q) (D.sourceUpperCorner q))
    (shrink :
      ∀ q, q ∈ D.activePieces →
        BoundaryChartLaterTargetShrinkData I x0 x1
          (D.sourceLowerCorner q) (D.sourceUpperCorner q)
          (D.targetLowerCorner q) (D.targetUpperCorner q)
          (D.targetPoint q)) :
    BoundaryChartSelectedBoxIFTContainsCompactCoverAutoData
      I x0 x1 ω a b Piece :=
  (D.toCompactImageBoxCoverDataOfShrink shrink).toSelectedBoxIFTContainsCompactCoverAutoData
    selectedBox

/--
One active IFT target-cover member plus later-target shrink data produces a
controlled target box with no `compactBox_subset` or `hcontains` field.
-/
theorem exists_controlledTargetBoxSelectionOfShrink
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1
        (D.sourceLowerCorner q) (D.sourceUpperCorner q)
        (D.targetLowerCorner q) (D.targetUpperCorner q)
        (D.targetPoint q))
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
    (D.toTargetBoxSelection q hq) shrink hU (D.image_mem_nhds q hq)

end BoundaryChartIFTTargetCoverData

end ManifoldBoundary

end Stokes

end
