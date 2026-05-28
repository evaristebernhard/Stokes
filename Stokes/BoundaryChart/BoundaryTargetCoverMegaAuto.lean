import Stokes.BoundaryChart.SelectedTargetBoxFromControlledCoverAuto
import Stokes.BoundaryChart.TargetBoxToM8Glue

/-!
# Boundary target-cover mega constructors

This file packages the now-standard boundary-target route:

* a local-openness or IFT target cover;
* cover-level later-target shrink data;
* selected source boxes;
* optional M8-facing global fields.

The pointwise records expose selected-image containment, target-box selection,
selected-box target-image data, and controlled-target choices without forcing
callers to destruct the `Sigma` returned by the existence/choice layer.  The
family records then assemble the same cover data into the resolved target-image
family and the `M8TargetImageResolvedInput` shape.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section ManifoldBoundary

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-! ## Pointwise local-openness cover package -/

/--
One local-openness target cover plus the two pieces every downstream consumer
usually wants: a later-target shrink package and selected source boxes on all
active cover pieces.
-/
structure BoundaryChartLocalOpennessTargetCoverMegaData {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}
    (ω : ManifoldForm I M n)
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece) where
  /-- Later-target shrink data for each active target box. -/
  shrink : BoundaryChartLocalOpennessTargetCoverLaterShrinkData C
  /-- Selected source boxes on active source sub-boxes. -/
  selectedBox :
    ∀ q, q ∈ C.activePieces →
      boundaryChartSelectedBox I x0 x1 ω
        (C.sourceLowerCorner q) (C.sourceUpperCorner q)

namespace BoundaryChartLocalOpennessTargetCoverMegaData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}
variable {C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece}

/-- The selected-target containment record for one active piece. -/
def selectedTargetContainsLaterTargets
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces) :
    BoundaryChartSelectedTargetContainsLaterTargets I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)
      (C.targetLowerCorner q) (C.targetUpperCorner q) (C.targetPoint q) :=
  D.shrink.selectedTargetContainsLaterTargets q hq

/-- Selected-image containment for one active piece. -/
def selectedImageBoxContainment
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) (C.targetPoint q) :=
  D.shrink.selectedImageBoxContainment q hq (D.selectedBox q hq)

/-- Cover-level selected-box/local-openness containment data. -/
def toSelectedBoxLocalOpennessContainsCoverAutoData
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C) :
    BoundaryChartSelectedBoxLocalOpennessContainsCoverAutoData
      I x0 x1 ω a b Piece :=
  D.shrink.toSelectedBoxLocalOpennessContainsCoverAutoData D.selectedBox

/-- The target-box selection fixed by the local-openness cover. -/
def targetBoxSelection
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces) :
    BoundaryChartTargetBoxSelection I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) :=
  C.toTargetBoxSelection q hq

@[simp]
theorem targetBoxSelection_lowerCorner
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces) :
    (D.targetBoxSelection q hq).lowerCorner = C.targetLowerCorner q :=
  rfl

@[simp]
theorem targetBoxSelection_upperCorner
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces) :
    (D.targetBoxSelection q hq).upperCorner = C.targetUpperCorner q :=
  rfl

/-- Selected-box target-image data from the fixed local-openness target box. -/
def selectedBoxTargetImageAutoData
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) :=
  BoundaryChartSelectedBoxTargetImageAutoData.ofTargetBoxSelection
    (D.selectedBox q hq) (D.targetBoxSelection q hq)

@[simp]
theorem selectedBoxTargetImageAutoData_selectedBox
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces) :
    (D.selectedBoxTargetImageAutoData q hq).selectedBox = D.selectedBox q hq :=
  rfl

@[simp]
theorem selectedBoxTargetImageAutoData_targetBox
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces) :
    (D.selectedBoxTargetImageAutoData q hq).targetBox =
      D.targetBoxSelection q hq :=
  rfl

@[simp]
theorem selectedBoxTargetImageAutoData_targetLowerCorner
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces) :
    (D.selectedBoxTargetImageAutoData q hq).targetLowerCorner =
      C.targetLowerCorner q :=
  rfl

@[simp]
theorem selectedBoxTargetImageAutoData_targetUpperCorner
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces) :
    (D.selectedBoxTargetImageAutoData q hq).targetUpperCorner =
      C.targetUpperCorner q :=
  rfl

/-- Image-data projection through the selected-box target-image package. -/
theorem imageData
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces) :
    boundaryChartSelectedBoxImageData I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)
      (C.targetLowerCorner q) (C.targetUpperCorner q) := by
  simpa using (D.selectedBoxTargetImageAutoData q hq).imageData

/-- Map-to projection for the chosen target box. -/
theorem mapsTo
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces) :
    MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain (C.sourceLowerCorner q) (C.sourceUpperCorner q))
      (lowerZeroFaceDomain (C.targetLowerCorner q) (C.targetUpperCorner q)) := by
  simpa using (D.selectedBoxTargetImageAutoData q hq).mapsTo

/-- Surjectivity projection for the chosen target box. -/
theorem surjOn
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces) :
    SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain (C.sourceLowerCorner q) (C.sourceUpperCorner q))
      (lowerZeroFaceDomain (C.targetLowerCorner q) (C.targetUpperCorner q)) := by
  simpa using (D.selectedBoxTargetImageAutoData q hq).surjOn

/-- The chosen controlled target from the cover-level shrink package. -/
def controlledTargetChoice
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    Σ c : Fin (n + 1) → Real, Σ d : Fin (n + 1) → Real,
      BoundaryChartControlledTargetBoxSelectionData
        I x0 x1 (C.sourceLowerCorner q) (C.sourceUpperCorner q)
          c d (C.targetPoint q) U :=
  D.shrink.controlledTargetBoxSelection q hq hU

/-- Lower corner selected by the controlled-target choice. -/
def controlledLowerCorner
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    Fin (n + 1) → Real :=
  (D.controlledTargetChoice q hq hU).1

/-- Upper corner selected by the controlled-target choice. -/
def controlledUpperCorner
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    Fin (n + 1) → Real :=
  (D.controlledTargetChoice q hq hU).2.1

/-- Controlled-target data with the chosen corners named. -/
def controlledTargetData
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 (C.sourceLowerCorner q) (C.sourceUpperCorner q)
        (D.controlledLowerCorner q hq hU) (D.controlledUpperCorner q hq hU)
        (C.targetPoint q) U :=
  (D.controlledTargetChoice q hq hU).2.2

@[simp]
theorem controlledTargetData_laterLowerCorner
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    (D.controlledTargetData q hq hU).laterLowerCorner =
      D.controlledLowerCorner q hq hU :=
  by
    simpa [controlledTargetData, controlledLowerCorner, controlledTargetChoice] using
      D.shrink.controlledTargetBoxSelection_laterLowerCorner q hq hU

@[simp]
theorem controlledTargetData_laterUpperCorner
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    (D.controlledTargetData q hq hU).laterUpperCorner =
      D.controlledUpperCorner q hq hU :=
  by
    simpa [controlledTargetData, controlledUpperCorner, controlledTargetChoice] using
      D.shrink.controlledTargetBoxSelection_laterUpperCorner q hq hU

/-- The controlled target as a standard target-box selection. -/
def controlledTargetBoxSelection
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    BoundaryChartTargetBoxSelection I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) :=
  (D.controlledTargetData q hq hU).targetBoxSelection

/-- Selected-box target-image data built from the controlled target. -/
def controlledSelectedBoxTargetImageAutoData
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) :=
  (D.controlledTargetData q hq hU).toSelectedBoxTargetImageAutoData
    (D.selectedBox q hq)

@[simp]
theorem controlledSelectedBoxTargetImageAutoData_targetLowerCorner
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    (D.controlledSelectedBoxTargetImageAutoData q hq hU).targetLowerCorner =
      D.controlledLowerCorner q hq hU := by
  simpa [controlledSelectedBoxTargetImageAutoData] using
    BoundaryChartControlledTargetBoxSelectionData.toSelectedBoxTargetImageAutoData_targetLowerCorner
      (D.controlledTargetData q hq hU) (D.selectedBox q hq)

@[simp]
theorem controlledSelectedBoxTargetImageAutoData_targetUpperCorner
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    (D.controlledSelectedBoxTargetImageAutoData q hq hU).targetUpperCorner =
      D.controlledUpperCorner q hq hU := by
  simpa [controlledSelectedBoxTargetImageAutoData] using
    BoundaryChartControlledTargetBoxSelectionData.toSelectedBoxTargetImageAutoData_targetUpperCorner
      (D.controlledTargetData q hq hU) (D.selectedBox q hq)

/-- Controlled-target image-data projection with named corners. -/
theorem controlledImageData
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    boundaryChartSelectedBoxImageData I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)
      (D.controlledLowerCorner q hq hU) (D.controlledUpperCorner q hq hU) := by
  simpa using (D.controlledSelectedBoxTargetImageAutoData q hq hU).imageData

/-- Controlled target point membership with named corners. -/
theorem controlledTargetPoint_mem
    (D : BoundaryChartLocalOpennessTargetCoverMegaData ω C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    C.targetPoint q ∈ lowerZeroFaceDomain
      (D.controlledLowerCorner q hq hU) (D.controlledUpperCorner q hq hU) :=
  by
    simpa using (D.controlledTargetData q hq hU).targetPoint_mem

end BoundaryChartLocalOpennessTargetCoverMegaData

/-! ## Pointwise IFT cover package -/

/--
IFT target cover plus later-target shrink and selected source boxes.  This is
parallel to `BoundaryChartLocalOpennessTargetCoverMegaData`.
-/
structure BoundaryChartIFTTargetCoverMegaData {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}
    (ω : ManifoldForm I M n)
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece) where
  /-- Later-target shrink data for each active target box. -/
  shrink : BoundaryChartIFTTargetCoverLaterShrinkData D
  /-- Selected source boxes on active source sub-boxes. -/
  selectedBox :
    ∀ q, q ∈ D.activePieces →
      boundaryChartSelectedBox I x0 x1 ω
        (D.sourceLowerCorner q) (D.sourceUpperCorner q)

namespace BoundaryChartIFTTargetCoverMegaData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}
variable {D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece}

/-- Forget IFT fields down to the local-openness mega package. -/
def toLocalOpennessMegaData
    (T : BoundaryChartIFTTargetCoverMegaData ω D) :
    BoundaryChartLocalOpennessTargetCoverMegaData ω D.toLocalOpennessTargetCover where
  shrink :=
    { laterTargetShrink := by
        intro q hq
        simpa [BoundaryChartIFTTargetCoverData.toLocalOpennessTargetCover] using
          T.shrink.laterTargetShrink q hq }
  selectedBox := by
    intro q hq
    simpa [BoundaryChartIFTTargetCoverData.toLocalOpennessTargetCover] using
      T.selectedBox q hq

/-- The selected-target containment record for one active IFT piece. -/
def selectedTargetContainsLaterTargets
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces) :
    BoundaryChartSelectedTargetContainsLaterTargets I x0 x1
      (D.sourceLowerCorner q) (D.sourceUpperCorner q)
      (D.targetLowerCorner q) (D.targetUpperCorner q) (D.targetPoint q) :=
  T.shrink.selectedTargetContainsLaterTargets q hq

/-- Selected-image containment for one active IFT piece. -/
def selectedImageBoxContainment
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) (D.targetPoint q) :=
  T.shrink.selectedImageBoxContainment q hq (T.selectedBox q hq)

/-- Cover-level selected-box/IFT containment data. -/
def toSelectedBoxIFTContainsCompactCoverAutoData
    (T : BoundaryChartIFTTargetCoverMegaData ω D) :
    BoundaryChartSelectedBoxIFTContainsCompactCoverAutoData
      I x0 x1 ω a b Piece :=
  T.shrink.toSelectedBoxIFTContainsCompactCoverAutoData T.selectedBox

/-- The target-box selection fixed by the IFT cover. -/
def targetBoxSelection
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces) :
    BoundaryChartTargetBoxSelection I x0 x1
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) :=
  D.toTargetBoxSelection q hq

@[simp]
theorem targetBoxSelection_lowerCorner
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces) :
    (T.targetBoxSelection q hq).lowerCorner = D.targetLowerCorner q :=
  rfl

@[simp]
theorem targetBoxSelection_upperCorner
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces) :
    (T.targetBoxSelection q hq).upperCorner = D.targetUpperCorner q :=
  rfl

/-- Selected-box target-image data from the fixed IFT target box. -/
def selectedBoxTargetImageAutoData
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) :=
  BoundaryChartSelectedBoxTargetImageAutoData.ofTargetBoxSelection
    (T.selectedBox q hq) (T.targetBoxSelection q hq)

@[simp]
theorem selectedBoxTargetImageAutoData_targetLowerCorner
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces) :
    (T.selectedBoxTargetImageAutoData q hq).targetLowerCorner =
      D.targetLowerCorner q :=
  rfl

@[simp]
theorem selectedBoxTargetImageAutoData_targetUpperCorner
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces) :
    (T.selectedBoxTargetImageAutoData q hq).targetUpperCorner =
      D.targetUpperCorner q :=
  rfl

/-- Image-data projection through the IFT selected-box target-image package. -/
theorem imageData
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces) :
    boundaryChartSelectedBoxImageData I x0 x1
      (D.sourceLowerCorner q) (D.sourceUpperCorner q)
      (D.targetLowerCorner q) (D.targetUpperCorner q) := by
  simpa using (T.selectedBoxTargetImageAutoData q hq).imageData

/-- The chosen controlled target from the IFT shrink package. -/
def controlledTargetChoice
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    Σ c : Fin (n + 1) → Real, Σ d : Fin (n + 1) → Real,
      BoundaryChartControlledTargetBoxSelectionData
        I x0 x1 (D.sourceLowerCorner q) (D.sourceUpperCorner q)
          c d (D.targetPoint q) U :=
  T.shrink.controlledTargetBoxSelection q hq hU

/-- Lower corner selected by the controlled IFT target choice. -/
def controlledLowerCorner
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    Fin (n + 1) → Real :=
  (T.controlledTargetChoice q hq hU).1

/-- Upper corner selected by the controlled IFT target choice. -/
def controlledUpperCorner
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    Fin (n + 1) → Real :=
  (T.controlledTargetChoice q hq hU).2.1

/-- Controlled IFT target data with named chosen corners. -/
def controlledTargetData
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 (D.sourceLowerCorner q) (D.sourceUpperCorner q)
        (T.controlledLowerCorner q hq hU) (T.controlledUpperCorner q hq hU)
        (D.targetPoint q) U :=
  (T.controlledTargetChoice q hq hU).2.2

@[simp]
theorem controlledTargetData_laterLowerCorner
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    (T.controlledTargetData q hq hU).laterLowerCorner =
      T.controlledLowerCorner q hq hU :=
  by
    simpa [controlledTargetData, controlledLowerCorner, controlledTargetChoice] using
      T.shrink.controlledTargetBoxSelection_laterLowerCorner q hq hU

@[simp]
theorem controlledTargetData_laterUpperCorner
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    (T.controlledTargetData q hq hU).laterUpperCorner =
      T.controlledUpperCorner q hq hU :=
  by
    simpa [controlledTargetData, controlledUpperCorner, controlledTargetChoice] using
      T.shrink.controlledTargetBoxSelection_laterUpperCorner q hq hU

/-- The controlled IFT target as a standard target-box selection. -/
def controlledTargetBoxSelection
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    BoundaryChartTargetBoxSelection I x0 x1
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) :=
  (T.controlledTargetData q hq hU).targetBoxSelection

/-- Selected-box target-image data built from the controlled IFT target. -/
def controlledSelectedBoxTargetImageAutoData
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) :=
  (T.controlledTargetData q hq hU).toSelectedBoxTargetImageAutoData
    (T.selectedBox q hq)

@[simp]
theorem controlledSelectedBoxTargetImageAutoData_targetLowerCorner
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    (T.controlledSelectedBoxTargetImageAutoData q hq hU).targetLowerCorner =
      T.controlledLowerCorner q hq hU := by
  simpa [controlledSelectedBoxTargetImageAutoData] using
    BoundaryChartControlledTargetBoxSelectionData.toSelectedBoxTargetImageAutoData_targetLowerCorner
      (T.controlledTargetData q hq hU) (T.selectedBox q hq)

@[simp]
theorem controlledSelectedBoxTargetImageAutoData_targetUpperCorner
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    (T.controlledSelectedBoxTargetImageAutoData q hq hU).targetUpperCorner =
      T.controlledUpperCorner q hq hU := by
  simpa [controlledSelectedBoxTargetImageAutoData] using
    BoundaryChartControlledTargetBoxSelectionData.toSelectedBoxTargetImageAutoData_targetUpperCorner
      (T.controlledTargetData q hq hU) (T.selectedBox q hq)

/-- Controlled IFT target image-data projection with named corners. -/
theorem controlledImageData
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    boundaryChartSelectedBoxImageData I x0 x1
      (D.sourceLowerCorner q) (D.sourceUpperCorner q)
      (T.controlledLowerCorner q hq hU) (T.controlledUpperCorner q hq hU) := by
  simpa using (T.controlledSelectedBoxTargetImageAutoData q hq hU).imageData

/-- Controlled IFT target point membership with named corners. -/
theorem controlledTargetPoint_mem
    (T : BoundaryChartIFTTargetCoverMegaData ω D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    D.targetPoint q ∈ lowerZeroFaceDomain
      (T.controlledLowerCorner q hq hU) (T.controlledUpperCorner q hq hU) :=
  by
    simpa using (T.controlledTargetData q hq hU).targetPoint_mem

end BoundaryChartIFTTargetCoverMegaData

/-! ## Family-level local-openness package -/

/--
Family-level local-openness target package, enriched with later-target shrink
data for each cover.  This is the natural pre-M8 shape when chart labels have
not yet been specialized to manifold points.
-/
structure BoundaryChartLocalOpennessTargetCoverMegaFamily {n : Nat}
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
  /-- Cover-level later-target shrink data. -/
  laterShrink :
    ∀ x, BoundaryChartLocalOpennessTargetCoverLaterShrinkData (cover x)
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

namespace BoundaryChartLocalOpennessTargetCoverMegaFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Local pieces are the active pieces of each cover. -/
def localPieces
    (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω Chart Piece) :
    Chart → Finset Piece :=
  fun x => (F.cover x).activePieces

/-- One active chart as a pointwise local-openness mega package. -/
def coverMegaData
    (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts) :
    BoundaryChartLocalOpennessTargetCoverMegaData ω (F.cover x) where
  shrink := F.laterShrink x
  selectedBox := F.sourceSelectedBox x hx

/-- Forget down to the existing local-openness target-image family. -/
def toTargetImageFamily
    (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω Chart Piece) :
    BoundaryChartLocalOpennessTargetImageFamily I ω Chart Piece where
  activeCharts := F.activeCharts
  sourceChart := F.sourceChart
  boundarySourceChart := F.boundarySourceChart
  boundaryTargetChart := F.boundaryTargetChart
  chartLowerCorner := F.chartLowerCorner
  chartUpperCorner := F.chartUpperCorner
  cover := F.cover
  defaultTargetBox := F.defaultTargetBox
  sourceSelectedBox := F.sourceSelectedBox
  targetSelectedBox := F.targetSelectedBox

/-- Resolved target-image family produced by the enriched local-openness package. -/
def toTargetImageResolvedFamily
    (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω Chart Piece) :
    BoundaryChartTargetImageResolvedFamily I ω Chart Piece :=
  F.toTargetImageFamily.toTargetImageResolvedFamily

@[simp]
theorem toTargetImageFamily_activeCharts
    (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω Chart Piece) :
    F.toTargetImageFamily.activeCharts = F.activeCharts :=
  rfl

@[simp]
theorem toTargetImageResolvedFamily_activeCharts
    (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω Chart Piece) :
    F.toTargetImageResolvedFamily.activeCharts = F.activeCharts :=
  rfl

@[simp]
theorem toTargetImageResolvedFamily_localPieces
    (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω Chart Piece)
    (x : Chart) :
    F.toTargetImageResolvedFamily.localPieces x = (F.cover x).activePieces :=
  rfl

/-- Active resolved target boxes are the local-openness target selections. -/
theorem toTargetImageResolvedFamily_targetBox
    (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω Chart Piece)
    (x : Chart) (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    F.toTargetImageResolvedFamily.targetBox x q =
      (F.cover x).toTargetBoxSelection q hq := by
  simpa [toTargetImageResolvedFamily, toTargetImageFamily] using
    BoundaryChartLocalOpennessTargetImageFamily.toTargetImageResolvedFamily_targetBox
      (F := F.toTargetImageFamily) x q hq

/-- Active selected-box target-image data from a family member. -/
def selectedBoxTargetImageAutoData
    (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    BoundaryChartSelectedBoxTargetImageAutoData I
      (F.sourceChart x) (F.boundarySourceChart x) ω
      ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q) :=
  (F.coverMegaData x hx).selectedBoxTargetImageAutoData q hq

/-- Active selected-image containment from a family member. -/
def selectedImageBoxContainment
    (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    BoundaryChartSelectedImageBoxContainment I
      (F.sourceChart x) (F.boundarySourceChart x) ω
      ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q)
      ((F.cover x).targetPoint q) :=
  (F.coverMegaData x hx).selectedImageBoxContainment q hq

/-- Active controlled target data with named corners from a family member. -/
def controlledTargetData
    (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 ((F.cover x).targetPoint q)) :
    BoundaryChartControlledTargetBoxSelectionData I
      (F.sourceChart x) (F.boundarySourceChart x)
      ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q)
      ((F.coverMegaData x hx).controlledLowerCorner q hq hU)
      ((F.coverMegaData x hx).controlledUpperCorner q hq hU)
      ((F.cover x).targetPoint q) U :=
  (F.coverMegaData x hx).controlledTargetData q hq hU

/-! ### M8-facing wrappers for local-openness mega families -/

/--
Global/M8 fields needed after the pure local-openness target-cover package has
built the resolved target-image family.
-/
structure M8ResolvedFields
    (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω M Piece)
    (selectedPartition : SelectedBoxPartitionOfUnity I ω)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M) where
  /-- Extended source boxes needed by local boundary Stokes. -/
  sourceExtendedBox :
    ∀ x, x ∈ F.toTargetImageResolvedFamily.activeCharts →
      ∀ q, q ∈ F.toTargetImageResolvedFamily.localPieces x →
        boundaryChartExtendedBox I
          (F.toTargetImageResolvedFamily.sourceChart x q)
          (F.toTargetImageResolvedFamily.boundarySourceChart x q) ω
          (F.toTargetImageResolvedFamily.sourceLowerCorner x q)
          (F.toTargetImageResolvedFamily.sourceUpperCorner x q)
  /-- Chart used for the selected boundary-partition representative. -/
  partitionTargetChart : M → Piece → M
  /-- Target box for the final boundary-partition representative. -/
  partitionTargetBox :
    (x : M) → (q : Piece) →
      BoundaryChartTargetBoxSelection I
        (F.toTargetImageResolvedFamily.boundarySourceChart x q)
        (F.toTargetImageResolvedFamily.boundaryTargetChart x q)
        (F.toTargetImageResolvedFamily.targetLowerCorner x q)
        (F.toTargetImageResolvedFamily.targetUpperCorner x q)
  /-- Selected auxiliary target boxes for boundary partition representatives. -/
  partitionSelectedBox :
    ∀ x, x ∈ F.toTargetImageResolvedFamily.activeCharts →
      ∀ q, q ∈ F.toTargetImageResolvedFamily.localPieces x →
        boundaryChartSelectedBox I
          (F.toTargetImageResolvedFamily.boundaryTargetChart x q)
          (partitionTargetChart x q) ω
          ((partitionTargetBox x q).lowerCorner)
          ((partitionTargetBox x q).upperCorner)
  /-- Boundary partition term used by global reconstruction. -/
  boundaryPartitionTerm : M → Piece → Real
  /-- Endpoint identification for the selected boundary partition term. -/
  boundaryPartitionTerm_eq :
    ∀ x, x ∈ F.toTargetImageResolvedFamily.activeCharts →
      ∀ q, q ∈ F.toTargetImageResolvedFamily.localPieces x →
        boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I
            (F.toTargetImageResolvedFamily.boundaryTargetChart x q)
            (partitionTargetChart x q) ω
            ((partitionTargetBox x q).lowerCorner)
            ((partitionTargetBox x q).upperCorner)
  /-- Active-set alignment with the selected partition. -/
  active_eq : F.toTargetImageResolvedFamily.activeCharts = selectedPartition.active
  /-- Source charts lie in the oriented boundary atlas. -/
  source_mem :
    ∀ x, x ∈ F.toTargetImageResolvedFamily.activeCharts →
      ∀ q, q ∈ F.toTargetImageResolvedFamily.localPieces x →
        F.toTargetImageResolvedFamily.sourceChart x q ∈ orientedBoundaryAtlas.charts
  /-- Boundary-source charts lie in the oriented boundary atlas. -/
  boundarySource_mem :
    ∀ x, x ∈ F.toTargetImageResolvedFamily.activeCharts →
      ∀ q, q ∈ F.toTargetImageResolvedFamily.localPieces x →
        F.toTargetImageResolvedFamily.boundarySourceChart x q ∈
          orientedBoundaryAtlas.charts
  /-- Boundary-target charts lie in the oriented boundary atlas. -/
  boundaryTarget_mem :
    ∀ x, x ∈ F.toTargetImageResolvedFamily.activeCharts →
      ∀ q, q ∈ F.toTargetImageResolvedFamily.localPieces x →
        F.toTargetImageResolvedFamily.boundaryTargetChart x q ∈
          orientedBoundaryAtlas.charts

namespace M8ResolvedFields

variable {selectedPartition : SelectedBoxPartitionOfUnity I ω}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
variable {F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω M Piece}

/-- The packaged fields as the existing M8 resolved target-image input. -/
def toM8ResolvedInput
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    M8TargetImageResolvedInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  F.toTargetImageResolvedFamily.toM8ResolvedInput D.sourceExtendedBox
    D.partitionTargetChart D.partitionTargetBox D.partitionSelectedBox
    D.boundaryPartitionTerm D.boundaryPartitionTerm_eq D.active_eq
    D.source_mem D.boundarySource_mem D.boundaryTarget_mem

/-- The packaged fields as `M8TargetImageInput`. -/
def toM8TargetImageInput
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  D.toM8ResolvedInput.toM8TargetImageInput

@[simp]
theorem toM8ResolvedInput_family
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    D.toM8ResolvedInput.family = F.toTargetImageResolvedFamily :=
  rfl

@[simp]
theorem toM8ResolvedInput_boundaryPartitionTerm
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    D.toM8ResolvedInput.boundaryPartitionTerm = D.boundaryPartitionTerm :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    D.toM8TargetImageInput.targetImages =
      D.toM8ResolvedInput.toM8TargetImageInput.targetImages :=
  rfl

end M8ResolvedFields

end BoundaryChartLocalOpennessTargetCoverMegaFamily

/-! ## Family-level IFT package -/

/--
Family-level IFT target package, enriched with later-target shrink data.  It
projects to both the IFT target-image family and the local-openness mega family.
-/
structure BoundaryChartIFTTargetCoverMegaFamily {n : Nat}
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
  /-- IFT target cover selected for each chart label. -/
  cover :
    ∀ x,
      BoundaryChartIFTTargetCoverData I (sourceChart x) (boundarySourceChart x)
        (chartLowerCorner x) (chartUpperCorner x) Piece
  /-- Cover-level later-target shrink data. -/
  laterShrink :
    ∀ x, BoundaryChartIFTTargetCoverLaterShrinkData (cover x)
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

namespace BoundaryChartIFTTargetCoverMegaFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Local pieces are the active pieces of each IFT cover. -/
def localPieces
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω Chart Piece) :
    Chart → Finset Piece :=
  fun x => (F.cover x).activePieces

/-- One active chart as a pointwise IFT mega package. -/
def coverMegaData
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts) :
    BoundaryChartIFTTargetCoverMegaData ω (F.cover x) where
  shrink := F.laterShrink x
  selectedBox := F.sourceSelectedBox x hx

/-- Forget down to the existing IFT target-image family. -/
def toIFTTargetImageFamily
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω Chart Piece) :
    BoundaryChartIFTTargetImageFamily I ω Chart Piece where
  activeCharts := F.activeCharts
  sourceChart := F.sourceChart
  boundarySourceChart := F.boundarySourceChart
  boundaryTargetChart := F.boundaryTargetChart
  chartLowerCorner := F.chartLowerCorner
  chartUpperCorner := F.chartUpperCorner
  cover := F.cover
  defaultTargetBox := F.defaultTargetBox
  sourceSelectedBox := F.sourceSelectedBox
  targetSelectedBox := F.targetSelectedBox

/-- Forget IFT data down to the local-openness mega family. -/
def toLocalOpennessMegaFamily
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω Chart Piece) :
    BoundaryChartLocalOpennessTargetCoverMegaFamily I ω Chart Piece where
  activeCharts := F.activeCharts
  sourceChart := F.sourceChart
  boundarySourceChart := F.boundarySourceChart
  boundaryTargetChart := F.boundaryTargetChart
  chartLowerCorner := F.chartLowerCorner
  chartUpperCorner := F.chartUpperCorner
  cover := fun x => (F.cover x).toLocalOpennessTargetCover
  laterShrink := by
    intro x
    exact
      { laterTargetShrink := by
          intro q hq
          simpa [BoundaryChartIFTTargetCoverData.toLocalOpennessTargetCover] using
            (F.laterShrink x).laterTargetShrink q hq }
  defaultTargetBox := by
    intro x q
    simpa [BoundaryChartIFTTargetCoverData.toLocalOpennessTargetCover] using
      F.defaultTargetBox x q
  sourceSelectedBox := by
    intro x hx q hq
    simpa [BoundaryChartIFTTargetCoverData.toLocalOpennessTargetCover] using
      F.sourceSelectedBox x hx q hq
  targetSelectedBox := by
    intro x hx q hq
    simpa [BoundaryChartIFTTargetCoverData.toLocalOpennessTargetCover] using
      F.targetSelectedBox x hx q hq

/-- Resolved target-image family produced by the enriched IFT package. -/
def toTargetImageResolvedFamily
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω Chart Piece) :
    BoundaryChartTargetImageResolvedFamily I ω Chart Piece :=
  F.toIFTTargetImageFamily.toTargetImageResolvedFamily

@[simp]
theorem toTargetImageResolvedFamily_activeCharts
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω Chart Piece) :
    F.toTargetImageResolvedFamily.activeCharts = F.activeCharts :=
  rfl

@[simp]
theorem toTargetImageResolvedFamily_localPieces
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω Chart Piece)
    (x : Chart) :
    F.toTargetImageResolvedFamily.localPieces x = (F.cover x).activePieces :=
  rfl

/-- Active resolved target boxes are the IFT target selections. -/
theorem toTargetImageResolvedFamily_targetBox
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω Chart Piece)
    (x : Chart) (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    F.toTargetImageResolvedFamily.targetBox x q =
      (F.cover x).toTargetBoxSelection q hq := by
  simpa [toTargetImageResolvedFamily, toIFTTargetImageFamily] using
    BoundaryChartIFTTargetImageFamily.toTargetImageResolvedFamily_targetBox
      (F := F.toIFTTargetImageFamily) x q hq

/-- Active selected-box target-image data from an IFT family member. -/
def selectedBoxTargetImageAutoData
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    BoundaryChartSelectedBoxTargetImageAutoData I
      (F.sourceChart x) (F.boundarySourceChart x) ω
      ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q) :=
  (F.coverMegaData x hx).selectedBoxTargetImageAutoData q hq

/-- Active selected-image containment from an IFT family member. -/
def selectedImageBoxContainment
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    BoundaryChartSelectedImageBoxContainment I
      (F.sourceChart x) (F.boundarySourceChart x) ω
      ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q)
      ((F.cover x).targetPoint q) :=
  (F.coverMegaData x hx).selectedImageBoxContainment q hq

/-! ### M8-facing wrappers for IFT mega families -/

/-- M8 fields for an IFT mega family, implemented by forgetting to resolved data. -/
abbrev M8ResolvedFields
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω M Piece)
    (selectedPartition : SelectedBoxPartitionOfUnity I ω)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M) :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.M8ResolvedFields
    F.toLocalOpennessMegaFamily selectedPartition orientedBoundaryAtlas

namespace M8ResolvedFields

variable {selectedPartition : SelectedBoxPartitionOfUnity I ω}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
variable {F : BoundaryChartIFTTargetCoverMegaFamily I ω M Piece}

/-- The packaged IFT fields as M8 resolved target-image input. -/
def toM8ResolvedInput
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    M8TargetImageResolvedInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.M8ResolvedFields.toM8ResolvedInput D

/-- The packaged IFT fields as `M8TargetImageInput`. -/
def toM8TargetImageInput
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.M8ResolvedFields.toM8TargetImageInput D

@[simp]
theorem toM8ResolvedInput_family
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    D.toM8ResolvedInput.family =
      F.toLocalOpennessMegaFamily.toTargetImageResolvedFamily :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    D.toM8TargetImageInput.targetImages =
      D.toM8ResolvedInput.toM8TargetImageInput.targetImages :=
  rfl

end M8ResolvedFields

end BoundaryChartIFTTargetCoverMegaFamily

end ManifoldBoundary

end Stokes

end
