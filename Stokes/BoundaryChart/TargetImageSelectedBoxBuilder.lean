import Stokes.BoundaryChart.TargetImageSelectedBoxAuto

/-!
# Boundary target-image selected-box builders

This file is a thin naming/projection layer over
`TargetImageSelectedBoxAuto`, `TargetImageLocalOpenness`, and
`TargetImageIFTBridge`.

It deliberately does not prove any new local-openness, inverse-function, or open
mapping theorem.  The geometric fields selecting concrete target boxes are still
the fields of the imported structures; this file only makes those fields easy to
consume from downstream boundary/global assembly code.
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

namespace BoundaryChartSelectedBoxTargetImageAutoData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

@[simp]
theorem ofTargetBoxSelection_selectedBox
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    (ofTargetBoxSelection hbox target).selectedBox = hbox :=
  rfl

@[simp]
theorem ofTargetBoxSelection_targetBox
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    (ofTargetBoxSelection hbox target).targetBox = target :=
  rfl

@[simp]
theorem ofTargetBoxSelection_targetLowerCorner
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    (ofTargetBoxSelection hbox target).targetLowerCorner = target.lowerCorner :=
  rfl

@[simp]
theorem ofTargetBoxSelection_targetUpperCorner
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    (ofTargetBoxSelection hbox target).targetUpperCorner = target.upperCorner :=
  rfl

/-- Stable projection name for the target-box image data inside auto data. -/
theorem targetBox_imageData
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b) :
    boundaryChartSelectedBoxImageData I x0 x1 a b
      D.targetBox.lowerCorner D.targetBox.upperCorner :=
  D.targetBox.imageData

/-- Stable projection name for the local inverse inside auto data. -/
theorem targetBox_localInverse
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b) :
    boundaryChartLocalInverseData I x0 x1 a b
      D.targetBox.lowerCorner D.targetBox.upperCorner :=
  D.targetBox.localInverse

end BoundaryChartSelectedBoxTargetImageAutoData

namespace BoundaryChartLocalOpennessTargetCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
One active local-openness cover piece as selected-box target-image auto data.

This is only a stable namespace alias for
`BoundaryChartSelectedBoxTargetImageAutoData.ofLocalOpennessTargetCover`.
-/
def toSelectedBoxTargetImageAutoData
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) :=
  BoundaryChartSelectedBoxTargetImageAutoData.ofLocalOpennessTargetCover
    C q hq hbox

@[simp]
theorem toSelectedBoxTargetImageAutoData_selectedBox
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)) :
    (C.toSelectedBoxTargetImageAutoData q hq hbox).selectedBox = hbox :=
  rfl

@[simp]
theorem toSelectedBoxTargetImageAutoData_targetBox
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)) :
    (C.toSelectedBoxTargetImageAutoData q hq hbox).targetBox =
      C.toTargetBoxSelection q hq :=
  rfl

@[simp]
theorem toSelectedBoxTargetImageAutoData_targetLowerCorner
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)) :
    (C.toSelectedBoxTargetImageAutoData q hq hbox).targetLowerCorner =
      C.targetLowerCorner q :=
  rfl

@[simp]
theorem toSelectedBoxTargetImageAutoData_targetUpperCorner
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)) :
    (C.toSelectedBoxTargetImageAutoData q hq hbox).targetUpperCorner =
      C.targetUpperCorner q :=
  rfl

/-- The selected-box auto-data image predicate is exactly the cover image data. -/
theorem toSelectedBoxTargetImageAutoData_imageData
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)) :
    (C.toSelectedBoxTargetImageAutoData q hq hbox).imageData =
      C.imageData q hq := by
  rfl

end BoundaryChartLocalOpennessTargetCover

namespace BoundaryChartIFTTargetCoverData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
One active IFT-facing cover piece as selected-box target-image auto data.

The IFT/local-openness work is already contained in `D.toTargetBoxSelection`;
this wrapper only provides a stable builder name.
-/
def toSelectedBoxTargetImageAutoData
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q)) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) :=
  BoundaryChartSelectedBoxTargetImageAutoData.ofIFTTargetCoverData
    D q hq hbox

@[simp]
theorem toSelectedBoxTargetImageAutoData_selectedBox
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q)) :
    (D.toSelectedBoxTargetImageAutoData q hq hbox).selectedBox = hbox :=
  rfl

@[simp]
theorem toSelectedBoxTargetImageAutoData_targetBox
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q)) :
    (D.toSelectedBoxTargetImageAutoData q hq hbox).targetBox =
      D.toTargetBoxSelection q hq :=
  rfl

@[simp]
theorem toSelectedBoxTargetImageAutoData_targetLowerCorner
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q)) :
    (D.toSelectedBoxTargetImageAutoData q hq hbox).targetLowerCorner =
      D.targetLowerCorner q :=
  rfl

@[simp]
theorem toSelectedBoxTargetImageAutoData_targetUpperCorner
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q)) :
    (D.toSelectedBoxTargetImageAutoData q hq hbox).targetUpperCorner =
      D.targetUpperCorner q :=
  rfl

/-- The selected-box auto-data image predicate is the IFT-facing cover image data. -/
theorem toSelectedBoxTargetImageAutoData_imageData
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q)) :
    (D.toSelectedBoxTargetImageAutoData q hq hbox).imageData =
      D.toLocalOpennessTargetCover.imageData q hq := by
  rfl

end BoundaryChartIFTTargetCoverData

namespace BoundaryChartLocalOpennessTargetImageFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Stable builder name for active local-openness family pieces. -/
def selectedBoxTargetImageAutoData
    (F : BoundaryChartLocalOpennessTargetImageFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    BoundaryChartSelectedBoxTargetImageAutoData I
      (F.sourceChart x) (F.boundarySourceChart x) ω
      ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q) :=
  F.autoData x hx q hq

@[simp]
theorem selectedBoxTargetImageAutoData_targetBox
    (F : BoundaryChartLocalOpennessTargetImageFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    (F.selectedBoxTargetImageAutoData x hx q hq).targetBox =
      (F.cover x).toTargetBoxSelection q hq :=
  rfl

@[simp]
theorem selectedBoxTargetImageAutoData_targetLowerCorner
    (F : BoundaryChartLocalOpennessTargetImageFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    (F.selectedBoxTargetImageAutoData x hx q hq).targetLowerCorner =
      (F.cover x).targetLowerCorner q :=
  rfl

@[simp]
theorem selectedBoxTargetImageAutoData_targetUpperCorner
    (F : BoundaryChartLocalOpennessTargetImageFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    (F.selectedBoxTargetImageAutoData x hx q hq).targetUpperCorner =
      (F.cover x).targetUpperCorner q :=
  rfl

/-- Active local-openness family pieces expose the exact downstream image data. -/
theorem selectedBoxTargetImageAutoData_imageData
    (F : BoundaryChartLocalOpennessTargetImageFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    (F.selectedBoxTargetImageAutoData x hx q hq).imageData =
      F.targetImageData x q hq := by
  rfl

end BoundaryChartLocalOpennessTargetImageFamily

namespace BoundaryChartIFTTargetImageFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Stable builder name for active IFT-facing family pieces. -/
def selectedBoxTargetImageAutoData
    (F : BoundaryChartIFTTargetImageFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    BoundaryChartSelectedBoxTargetImageAutoData I
      (F.sourceChart x) (F.boundarySourceChart x) ω
      ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q) :=
  F.autoData x hx q hq

@[simp]
theorem selectedBoxTargetImageAutoData_targetBox
    (F : BoundaryChartIFTTargetImageFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    (F.selectedBoxTargetImageAutoData x hx q hq).targetBox =
      (F.cover x).toTargetBoxSelection q hq :=
  rfl

@[simp]
theorem selectedBoxTargetImageAutoData_targetLowerCorner
    (F : BoundaryChartIFTTargetImageFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    (F.selectedBoxTargetImageAutoData x hx q hq).targetLowerCorner =
      (F.cover x).targetLowerCorner q :=
  rfl

@[simp]
theorem selectedBoxTargetImageAutoData_targetUpperCorner
    (F : BoundaryChartIFTTargetImageFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    (F.selectedBoxTargetImageAutoData x hx q hq).targetUpperCorner =
      (F.cover x).targetUpperCorner q :=
  rfl

/-- Active IFT-facing family pieces expose the exact downstream image data. -/
theorem selectedBoxTargetImageAutoData_imageData
    (F : BoundaryChartIFTTargetImageFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    (F.selectedBoxTargetImageAutoData x hx q hq).imageData =
      F.targetImageData x q hq := by
  rfl

end BoundaryChartIFTTargetImageFamily

namespace BoundaryChartSelectedBoxLocalInverseAutoInputs

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/--
Direct target-box selection theorem extracted from selected-box local-inverse
auto inputs.

The compact-image-for-local-inverse-targets field is still the real geometric
input; this theorem only forgets the selected-box auto-data wrapper.
-/
theorem exists_targetBoxSelection
    (T : BoundaryChartSelectedBoxLocalInverseAutoInputs I x0 x1 ω a b) :
    ∃ target : BoundaryChartTargetBoxSelection I x0 x1 a b,
      T.targetPoint ∈ lowerZeroFaceDomain target.lowerCorner target.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          target.lowerCorner target.upperCorner := by
  rcases T.exists_autoData with ⟨D, hmem, himage⟩
  refine ⟨D.targetBox, ?_, ?_⟩
  · simpa [BoundaryChartSelectedBoxTargetImageAutoData.targetLowerCorner,
      BoundaryChartSelectedBoxTargetImageAutoData.targetUpperCorner] using hmem
  · exact D.targetBox.imageData

end BoundaryChartSelectedBoxLocalInverseAutoInputs

namespace BoundaryChartSelectedBoxPointAutoInputs

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/-- Oriented-atlas target-box selection extracted from point auto inputs. -/
theorem exists_targetBoxSelection_of_orientedAtlas
    [IsManifold I ⊤ M]
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (T : BoundaryChartSelectedBoxPointAutoInputs I x0 x1 ω a b) :
    ∃ target : BoundaryChartTargetBoxSelection I x0 x1 a b,
      T.targetPoint ∈ lowerZeroFaceDomain target.lowerCorner target.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          target.lowerCorner target.upperCorner := by
  rcases T.exists_autoData_of_orientedAtlas A hx0 hx1 with
    ⟨D, hmem, himage⟩
  refine ⟨D.targetBox, ?_, ?_⟩
  · simpa [BoundaryChartSelectedBoxTargetImageAutoData.targetLowerCorner,
      BoundaryChartSelectedBoxTargetImageAutoData.targetUpperCorner] using hmem
  · exact D.targetBox.imageData

/-- Oriented-manifold target-box selection extracted from point auto inputs. -/
theorem exists_targetBoxSelection_of_orientedManifold
    [IsManifold I ⊤ M] [BoundaryChartOrientedManifold I M]
    (T : BoundaryChartSelectedBoxPointAutoInputs I x0 x1 ω a b) :
    ∃ target : BoundaryChartTargetBoxSelection I x0 x1 a b,
      T.targetPoint ∈ lowerZeroFaceDomain target.lowerCorner target.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          target.lowerCorner target.upperCorner := by
  rcases T.exists_autoData_of_orientedManifold with ⟨D, hmem, himage⟩
  refine ⟨D.targetBox, ?_, ?_⟩
  · simpa [BoundaryChartSelectedBoxTargetImageAutoData.targetLowerCorner,
      BoundaryChartSelectedBoxTargetImageAutoData.targetUpperCorner] using hmem
  · exact D.targetBox.imageData

end BoundaryChartSelectedBoxPointAutoInputs

end ManifoldBoundary

end Stokes

end
