import Stokes.BoundaryChart.TargetImageIFTBridge

/-!
# Selected-box target-image automation

This file is a pure `BoundaryChart` naming layer.  It packages the target-image
data that can already be produced from a selected source boundary box plus
local-inverse/local-openness/IFT-facing inputs.

The remaining geometric choice is still explicit in the input:
`boundaryChartCompactCoordinateImageForLocalInverseTargets` says that whichever
small target box the local-inverse theorem selects also contains the compact
image of the source box.  Proving this field from local openness / inverse
function theorem and compact box selection is the next mathematical step.
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
Single selected-source-box target-image data.

The `targetBox` field is the automatically consumed output: it contains the
selected target boundary box, compact-image containment, and local right-inverse
data.  The constructors below build this record from existing local-inverse,
local-openness, and IFT-facing packages.
-/
structure BoundaryChartSelectedBoxTargetImageAutoData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) where
  /-- Selected source boundary box. -/
  selectedBox : boundaryChartSelectedBox I x0 x1 ω a b
  /-- Selected target box with compact-image and local-inverse data. -/
  targetBox : BoundaryChartTargetBoxSelection I x0 x1 a b

namespace BoundaryChartSelectedBoxTargetImageAutoData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/-- Lower corner of the selected target boundary-coordinate box. -/
def targetLowerCorner
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b) :
    Fin (n + 1) → Real :=
  D.targetBox.lowerCorner

/-- Upper corner of the selected target boundary-coordinate box. -/
def targetUpperCorner
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b) :
    Fin (n + 1) → Real :=
  D.targetBox.upperCorner

theorem targetLowerCorner_zero
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b) :
    D.targetLowerCorner 0 = 0 :=
  D.targetBox.lowerCorner_zero

theorem targetLower_le_targetUpper
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b) :
    D.targetLowerCorner ≤ D.targetUpperCorner :=
  D.targetBox.lower_le_upper

/-- Compact image control carried by the selected target box. -/
theorem compactImage
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b) :
    boundaryChartCompactImageBoxSelection I x0 x1 a b
      D.targetLowerCorner D.targetUpperCorner :=
  D.targetBox.compactImage

/-- Local right-inverse data carried by the selected target box. -/
theorem localInverse
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b) :
    boundaryChartLocalInverseData I x0 x1 a b
      D.targetLowerCorner D.targetUpperCorner :=
  D.targetBox.localInverse

/-- Image data consumed by boundary chart change-of-variables wrappers. -/
theorem imageData
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b) :
    boundaryChartSelectedBoxImageData I x0 x1 a b
      D.targetLowerCorner D.targetUpperCorner :=
  D.targetBox.imageData

/-- Map-to projection of the packaged image data. -/
theorem mapsTo
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b) :
    MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b)
      (lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner) :=
  D.imageData.mapsTo

/-- Surjectivity projection supplied by the packaged local inverse. -/
theorem surjOn
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b) :
    SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b)
      (lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner) :=
  D.imageData.surjOn

/-- Constructor from an already selected target box. -/
def ofTargetBoxSelection
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b where
  selectedBox := hbox
  targetBox := target

/-- Constructor from compact-image and local-inverse halves. -/
def ofCompactImageLocalInverseData
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (c d : Fin (n + 1) → Real) (hc0 : c 0 = 0) (hle : c ≤ d)
    (hcompact : boundaryChartCompactImageBoxSelection I x0 x1 a b c d)
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b :=
  ofTargetBoxSelection hbox
    (BoundaryChartTargetBoxSelection.mkOfCompactImageLocalInverseData
      c d hc0 hle hcompact hlocal)

/-- Constructor from one active member of a local-openness target cover. -/
def ofLocalOpennessTargetCover
    {a₀ b₀ : Fin (n + 1) → Real} {Piece : Type p}
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a₀ b₀ Piece)
    (q : Piece) (hq : q ∈ C.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) :=
  ofTargetBoxSelection hbox (C.toTargetBoxSelection q hq)

/-- Constructor from one active member of an IFT-facing target cover. -/
def ofIFTTargetCoverData
    {a₀ b₀ : Fin (n + 1) → Real} {Piece : Type p}
    (C : BoundaryChartIFTTargetCoverData I x0 x1 a₀ b₀ Piece)
    (q : Piece) (hq : q ∈ C.activePieces)
    (hbox : boundaryChartSelectedBox I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) :=
  ofTargetBoxSelection hbox (C.toTargetBoxSelection q hq)

/--
Selected-box image-constructor data, once orientation-map hypotheses are
available.
-/
def toSelectedBoxImageConstructorData
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b)
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hdata :
      BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b)) :
    BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b where
  selectedBox := D.selectedBox
  targetSelection := D.targetBox
  compatibleOn := hcompat
  orientationMapDataOn := hdata

/-- Oriented-atlas version of the selected-box image-constructor data. -/
def toSelectedBoxImageConstructorDataOfOrientedAtlas
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b)
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts) :
    BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b :=
  BoundaryChartSelectedBoxImageConstructorData.ofOrientedAtlas
    A hx0 hx1 D.selectedBox D.targetBox

/-- Oriented-manifold version of the selected-box image-constructor data. -/
def toSelectedBoxImageConstructorDataOfOrientedManifold
    [BoundaryChartOrientedManifold I M]
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b) :
    BoundaryChartSelectedBoxImageConstructorData I x0 x1 ω a b :=
  BoundaryChartSelectedBoxImageConstructorData.ofOrientedManifold
    D.selectedBox D.targetBox

end BoundaryChartSelectedBoxTargetImageAutoData

/--
Input fields currently needed to automate selected target-box construction from
an explicit local-inverse existence theorem.

The only non-local-inverse geometric field is
`compactImageForLocalInverseTargets`: it is the compact-image target-box
selection lemma that is not yet derived automatically from IFT/local openness.
-/
structure BoundaryChartSelectedBoxLocalInverseAutoInputs {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) where
  /-- Selected source boundary box. -/
  selectedBox : boundaryChartSelectedBox I x0 x1 ω a b
  /-- Target point around which the local inverse selects a small target box. -/
  targetPoint : Fin n → Real
  /-- Existence of a selected target box carrying local-inverse data. -/
  existsLocalInverseData :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      targetPoint ∈ lowerZeroFaceDomain c d ∧
        boundaryChartLocalInverseData I x0 x1 a b c d
  /--
  Compact-image control for the local-inverse target box.  This is the current
  missing automatic bridge from local openness / compact box selection.
  -/
  compactImageForLocalInverseTargets :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b targetPoint

namespace BoundaryChartSelectedBoxLocalInverseAutoInputs

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/-- Build selected-box target-image data from explicit local-inverse inputs. -/
theorem exists_autoData
    (T : BoundaryChartSelectedBoxLocalInverseAutoInputs I x0 x1 ω a b) :
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      T.targetPoint ∈ lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          D.targetLowerCorner D.targetUpperCorner := by
  rcases exists_boundaryChartTargetBoxSelection_of_exists_localInverseData
      T.existsLocalInverseData T.compactImageForLocalInverseTargets with
    ⟨target, hmem, himage⟩
  refine ⟨BoundaryChartSelectedBoxTargetImageAutoData.ofTargetBoxSelection
      T.selectedBox target, hmem, ?_⟩
  simpa [BoundaryChartSelectedBoxTargetImageAutoData.ofTargetBoxSelection,
    BoundaryChartSelectedBoxTargetImageAutoData.targetLowerCorner,
    BoundaryChartSelectedBoxTargetImageAutoData.targetUpperCorner] using himage

end BoundaryChartSelectedBoxLocalInverseAutoInputs

/--
Pointwise selected-box inputs for the oriented-atlas/oriented-manifold local
inverse theorem.

Compared with `BoundaryChartSelectedBoxLocalInverseAutoInputs`, the
`existsLocalInverseData` field is replaced by the source point and neighborhood
data from which the existing oriented chart API obtains a local inverse.
-/
structure BoundaryChartSelectedBoxPointAutoInputs {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) where
  /-- Selected source boundary box. -/
  selectedBox : boundaryChartSelectedBox I x0 x1 ω a b
  /-- Source point where the local inverse theorem is applied. -/
  sourcePoint : Fin n → Real
  /-- The source point lies in the selected boundary box. -/
  sourcePoint_mem : sourcePoint ∈ lowerZeroFaceDomain a b
  /-- The selected boundary box is a neighborhood of the source point. -/
  source_mem_nhds : lowerZeroFaceDomain a b ∈ 𝓝 sourcePoint
  /--
  Compact-image control for the target point produced by the transition.  This
  is still the concrete box-image selection bridge needed after local openness.
  -/
  compactImageForLocalInverseTargets :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b
      (boundaryChartTransition I x0 x1 sourcePoint)

namespace BoundaryChartSelectedBoxPointAutoInputs

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/-- Target point in the boundary target coordinates. -/
def targetPoint
    (T : BoundaryChartSelectedBoxPointAutoInputs I x0 x1 ω a b) :
    Fin n → Real :=
  boundaryChartTransition I x0 x1 T.sourcePoint

/-- Oriented-atlas constructor for selected-box target-image data. -/
theorem exists_autoData_of_orientedAtlas
    [IsManifold I ⊤ M]
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (T : BoundaryChartSelectedBoxPointAutoInputs I x0 x1 ω a b) :
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      T.targetPoint ∈ lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          D.targetLowerCorner D.targetUpperCorner := by
  rcases exists_boundaryChartTargetBoxSelection_of_selectedBox_orientedAtlas
      A hx0 hx1 T.selectedBox T.sourcePoint_mem T.source_mem_nhds
      T.compactImageForLocalInverseTargets with
    ⟨target, hmem, himage⟩
  refine ⟨BoundaryChartSelectedBoxTargetImageAutoData.ofTargetBoxSelection
      T.selectedBox target, hmem, ?_⟩
  simpa [targetPoint,
    BoundaryChartSelectedBoxTargetImageAutoData.ofTargetBoxSelection,
    BoundaryChartSelectedBoxTargetImageAutoData.targetLowerCorner,
    BoundaryChartSelectedBoxTargetImageAutoData.targetUpperCorner] using himage

/-- Oriented-manifold constructor for selected-box target-image data. -/
theorem exists_autoData_of_orientedManifold
    [IsManifold I ⊤ M] [BoundaryChartOrientedManifold I M]
    (T : BoundaryChartSelectedBoxPointAutoInputs I x0 x1 ω a b) :
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      T.targetPoint ∈ lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          D.targetLowerCorner D.targetUpperCorner := by
  rcases exists_boundaryChartTargetBoxSelection_of_selectedBox_orientedManifold
      T.selectedBox T.sourcePoint_mem T.source_mem_nhds
      T.compactImageForLocalInverseTargets with
    ⟨target, hmem, himage⟩
  refine ⟨BoundaryChartSelectedBoxTargetImageAutoData.ofTargetBoxSelection
      T.selectedBox target, hmem, ?_⟩
  simpa [targetPoint,
    BoundaryChartSelectedBoxTargetImageAutoData.ofTargetBoxSelection,
    BoundaryChartSelectedBoxTargetImageAutoData.targetLowerCorner,
    BoundaryChartSelectedBoxTargetImageAutoData.targetUpperCorner] using himage

end BoundaryChartSelectedBoxPointAutoInputs

namespace BoundaryChartLocalOpennessTargetImageFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/--
Named projection from local-openness target-image data to the resolved
target-image family used downstream.
-/
def toSelectedBoxTargetImageResolvedFamily
    (F : BoundaryChartLocalOpennessTargetImageFamily I ω Chart Piece) :
    BoundaryChartTargetImageResolvedFamily I ω Chart Piece :=
  F.toTargetImageResolvedFamily

/-- Active local-openness pieces expose the selected source-box auto data. -/
def autoData
    (F : BoundaryChartLocalOpennessTargetImageFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    BoundaryChartSelectedBoxTargetImageAutoData I
      (F.sourceChart x) (F.boundarySourceChart x) ω
      ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q) :=
  BoundaryChartSelectedBoxTargetImageAutoData.ofLocalOpennessTargetCover
    (F.cover x) q hq (F.sourceSelectedBox x hx q hq)

/-- The auto-data target image agrees with the local-openness image-data field. -/
theorem autoData_imageData
    (F : BoundaryChartLocalOpennessTargetImageFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    (F.autoData x hx q hq).imageData = F.targetImageData x q hq := by
  rfl

end BoundaryChartLocalOpennessTargetImageFamily

namespace BoundaryChartIFTTargetImageFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/--
Named projection from IFT-facing target-image data to the resolved target-image
family used downstream.
-/
def toSelectedBoxTargetImageResolvedFamily
    (F : BoundaryChartIFTTargetImageFamily I ω Chart Piece) :
    BoundaryChartTargetImageResolvedFamily I ω Chart Piece :=
  F.toTargetImageResolvedFamily

/-- Active IFT pieces expose the selected source-box auto data. -/
def autoData
    (F : BoundaryChartIFTTargetImageFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    BoundaryChartSelectedBoxTargetImageAutoData I
      (F.sourceChart x) (F.boundarySourceChart x) ω
      ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q) :=
  BoundaryChartSelectedBoxTargetImageAutoData.ofIFTTargetCoverData
    (F.cover x) q hq (F.sourceSelectedBox x hx q hq)

/-- The auto-data target image agrees with the IFT-facing image-data field. -/
theorem autoData_imageData
    (F : BoundaryChartIFTTargetImageFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    (F.autoData x hx q hq).imageData = F.targetImageData x q hq := by
  rfl

end BoundaryChartIFTTargetImageFamily

end ManifoldBoundary

end Stokes

end
