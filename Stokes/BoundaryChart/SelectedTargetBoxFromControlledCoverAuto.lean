import Stokes.BoundaryChart.ControlledTargetFromSourceShrinkCoverAuto

/-!
# Selected target boxes from controlled cover data

This file is a small constructor layer over the controlled target-box route.
The lower modules already prove the geometry from local-openness/IFT target
covers plus later-target shrink data.  Here we expose the pointwise and
cover-level packages that downstream chart-change code wants to consume.
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

namespace BoundaryChartLocalOpennessTargetCoverLaterShrinkData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}
variable {C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece}

/-- Pointwise selected-image containment from a local-openness target cover and
its packaged later-target shrink data. -/
def selectedImageBoxContainment
    (S : BoundaryChartLocalOpennessTargetCoverLaterShrinkData C)
    (q : Piece) (hq : q ∈ C.activePieces)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        (C.sourceLowerCorner q) (C.sourceUpperCorner q)) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) (C.targetPoint q) :=
  (C.toTargetBoxSelection q hq).selectedImageBoxContainmentOfShrink
    hbox (S.laterTargetShrink q hq)

/-- Cover-level selected-box containment data from a local-openness target cover
and packaged later-target shrink data. -/
def toSelectedBoxLocalOpennessContainsCoverAutoData
    (S : BoundaryChartLocalOpennessTargetCoverLaterShrinkData C)
    (selectedBox :
      ∀ q, q ∈ C.activePieces →
        boundaryChartSelectedBox I x0 x1 ω
          (C.sourceLowerCorner q) (C.sourceUpperCorner q)) :
    BoundaryChartSelectedBoxLocalOpennessContainsCoverAutoData
      I x0 x1 ω a b Piece :=
  C.toSelectedBoxLocalOpennessContainsCoverAutoDataOfShrink
    selectedBox S.laterTargetShrink

/-- A canonical controlled target-box choice for one active local-openness cover
piece, obtained from the existing existence theorem. -/
def controlledTargetBoxSelection
    (S : BoundaryChartLocalOpennessTargetCoverLaterShrinkData C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    Σ c : Fin (n + 1) → Real, Σ d : Fin (n + 1) → Real,
      BoundaryChartControlledTargetBoxSelectionData
        I x0 x1 (C.sourceLowerCorner q) (C.sourceUpperCorner q)
          c d (C.targetPoint q) U :=
  ⟨Classical.choose (S.exists_controlledTargetBoxSelection q hq hU),
    Classical.choose
      (Classical.choose_spec (S.exists_controlledTargetBoxSelection q hq hU)),
    Classical.choose
      (Classical.choose_spec
        (Classical.choose_spec (S.exists_controlledTargetBoxSelection q hq hU)))⟩

/-- The chosen controlled box remembers the selected lower corner in its later
lower-corner field. -/
theorem controlledTargetBoxSelection_laterLowerCorner
    (S : BoundaryChartLocalOpennessTargetCoverLaterShrinkData C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    (S.controlledTargetBoxSelection q hq hU).2.2.laterLowerCorner =
      (S.controlledTargetBoxSelection q hq hU).1 := by
  dsimp [controlledTargetBoxSelection]
  exact
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (S.exists_controlledTargetBoxSelection q hq hU)))).1

/-- The chosen controlled box remembers the selected upper corner in its later
upper-corner field. -/
theorem controlledTargetBoxSelection_laterUpperCorner
    (S : BoundaryChartLocalOpennessTargetCoverLaterShrinkData C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    (S.controlledTargetBoxSelection q hq hU).2.2.laterUpperCorner =
      (S.controlledTargetBoxSelection q hq hU).2.1 := by
  dsimp [controlledTargetBoxSelection]
  exact
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (S.exists_controlledTargetBoxSelection q hq hU)))).2

/-- Forget the canonical controlled target to the standard selected target-box
record. -/
def controlledTargetBoxAsTargetBoxSelection
    (S : BoundaryChartLocalOpennessTargetCoverLaterShrinkData C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    BoundaryChartTargetBoxSelection I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) :=
  (S.controlledTargetBoxSelection q hq hU).2.2.targetBoxSelection

/-- Selected-box target-image auto-data produced from the canonical controlled
target choice. -/
def controlledSelectedBoxTargetImageAutoData
    (S : BoundaryChartLocalOpennessTargetCoverLaterShrinkData C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q))
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        (C.sourceLowerCorner q) (C.sourceUpperCorner q)) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) :=
  (S.controlledTargetBoxSelection q hq hU).2.2.toSelectedBoxTargetImageAutoData
    hbox

end BoundaryChartLocalOpennessTargetCoverLaterShrinkData

namespace BoundaryChartIFTTargetCoverLaterShrinkData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}
variable {D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece}

/-- Pointwise selected-image containment from an IFT target cover and its
packaged later-target shrink data. -/
def selectedImageBoxContainment
    (S : BoundaryChartIFTTargetCoverLaterShrinkData D)
    (q : Piece) (hq : q ∈ D.activePieces)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        (D.sourceLowerCorner q) (D.sourceUpperCorner q)) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) (D.targetPoint q) :=
  (D.toTargetBoxSelection q hq).selectedImageBoxContainmentOfShrink
    hbox (S.laterTargetShrink q hq)

/-- Cover-level selected-box IFT containment data from an IFT target cover and
packaged later-target shrink data. -/
def toSelectedBoxIFTContainsCompactCoverAutoData
    (S : BoundaryChartIFTTargetCoverLaterShrinkData D)
    (selectedBox :
      ∀ q, q ∈ D.activePieces →
        boundaryChartSelectedBox I x0 x1 ω
          (D.sourceLowerCorner q) (D.sourceUpperCorner q)) :
    BoundaryChartSelectedBoxIFTContainsCompactCoverAutoData
      I x0 x1 ω a b Piece :=
  D.toSelectedBoxIFTContainsCompactCoverAutoDataOfShrink
    selectedBox S.laterTargetShrink

/-- A canonical controlled target-box choice for one active IFT cover piece,
obtained from the existing existence theorem. -/
def controlledTargetBoxSelection
    (S : BoundaryChartIFTTargetCoverLaterShrinkData D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    Σ c : Fin (n + 1) → Real, Σ d : Fin (n + 1) → Real,
      BoundaryChartControlledTargetBoxSelectionData
        I x0 x1 (D.sourceLowerCorner q) (D.sourceUpperCorner q)
          c d (D.targetPoint q) U :=
  ⟨Classical.choose (S.exists_controlledTargetBoxSelectionOfShrinkPackage q hq hU),
    Classical.choose
      (Classical.choose_spec
        (S.exists_controlledTargetBoxSelectionOfShrinkPackage q hq hU)),
    Classical.choose
      (Classical.choose_spec
        (Classical.choose_spec
          (S.exists_controlledTargetBoxSelectionOfShrinkPackage q hq hU)))⟩

/-- The chosen controlled box remembers the selected lower corner in its later
lower-corner field. -/
theorem controlledTargetBoxSelection_laterLowerCorner
    (S : BoundaryChartIFTTargetCoverLaterShrinkData D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    (S.controlledTargetBoxSelection q hq hU).2.2.laterLowerCorner =
      (S.controlledTargetBoxSelection q hq hU).1 := by
  dsimp [controlledTargetBoxSelection]
  exact
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (S.exists_controlledTargetBoxSelectionOfShrinkPackage q hq hU)))).1

/-- The chosen controlled box remembers the selected upper corner in its later
upper-corner field. -/
theorem controlledTargetBoxSelection_laterUpperCorner
    (S : BoundaryChartIFTTargetCoverLaterShrinkData D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    (S.controlledTargetBoxSelection q hq hU).2.2.laterUpperCorner =
      (S.controlledTargetBoxSelection q hq hU).2.1 := by
  dsimp [controlledTargetBoxSelection]
  exact
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (S.exists_controlledTargetBoxSelectionOfShrinkPackage q hq hU)))).2

/-- Forget the canonical controlled target to the standard selected target-box
record. -/
def controlledTargetBoxAsTargetBoxSelection
    (S : BoundaryChartIFTTargetCoverLaterShrinkData D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    BoundaryChartTargetBoxSelection I x0 x1
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) :=
  (S.controlledTargetBoxSelection q hq hU).2.2.targetBoxSelection

/-- Selected-box target-image auto-data produced from the canonical controlled
target choice. -/
def controlledSelectedBoxTargetImageAutoData
    (S : BoundaryChartIFTTargetCoverLaterShrinkData D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q))
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        (D.sourceLowerCorner q) (D.sourceUpperCorner q)) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) :=
  (S.controlledTargetBoxSelection q hq hU).2.2.toSelectedBoxTargetImageAutoData
    hbox

end BoundaryChartIFTTargetCoverLaterShrinkData

end ManifoldBoundary

end Stokes

end
