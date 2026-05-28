import Stokes.BoundaryChart.CompactImageCover
import Stokes.BoundaryChart.SelectedBoxImageConstructor

/-!
# Finite families of selected target boundary boxes

This file is a pure boundary-chart selection layer.  It batches the single-box
target selection constructors over a finite family of selected source boundary
boxes, while keeping all global reconstruction and partition bookkeeping out of
the import graph.
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

namespace BoundaryChartCompactImageCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
Package one active compact-image cover member as the target-box selection used
by family-level boundary chart constructors.
-/
def toTargetBoxSelection
    (C : BoundaryChartCompactImageCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    BoundaryChartTargetBoxSelection I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) where
  lowerCorner := C.targetLowerCorner q
  upperCorner := C.targetUpperCorner q
  lowerCorner_zero := C.targetLowerCorner_zero q hq
  lower_le_upper := C.targetLower_le_targetUpper q hq
  compactImage := C.compactImage q hq
  localInverse := C.localInverse q hq

end BoundaryChartCompactImageCover

namespace BoundaryChartCompactImageForLocalInverseTargetCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
After materializing compact-image control, one active local-inverse target cover
member gives the standard target-box selection package.
-/
def toTargetBoxSelection
    (C : BoundaryChartCompactImageForLocalInverseTargetCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    BoundaryChartTargetBoxSelection I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) :=
  C.toCompactImageCover.toTargetBoxSelection q hq

end BoundaryChartCompactImageForLocalInverseTargetCover

/--
A finite family of source boundary boxes together with selected target boxes.

The target data is only required for active pieces, hence the target corners are
indexed by the membership proofs for the active chart and local piece.  Each
active target stores both halves needed for image data: compact image control
and local right-inverse data.
-/
structure BoundaryChartTargetBoxFamilySelection {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n) (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in the boundary-box family. -/
  activeCharts : Finset Chart
  /-- Finite local pieces attached to each active chart label. -/
  localPieces : Chart → Finset Piece
  /-- Source chart for the boundary chart transition. -/
  sourceChart : Chart → Piece → M
  /-- Boundary chart reached from the source chart. -/
  boundarySourceChart : Chart → Piece → M
  /-- Lower corner of the selected source boundary box. -/
  sourceLowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Upper corner of the selected source boundary box. -/
  sourceUpperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Selected source boundary boxes for every active piece. -/
  sourceSelectedBox :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ localPieces x →
        boundaryChartSelectedBox I (sourceChart x q) (boundarySourceChart x q) ω
          (sourceLowerCorner x q) (sourceUpperCorner x q)
  /-- Lower corner of each selected target boundary box. -/
  targetLowerCorner :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ localPieces x → Fin (n + 1) → Real
  /-- Upper corner of each selected target boundary box. -/
  targetUpperCorner :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ localPieces x → Fin (n + 1) → Real
  /-- The selected target lower corners lie on the lower zero face. -/
  targetLowerCorner_zero :
    ∀ x, (hx : x ∈ activeCharts) →
      ∀ q, (hq : q ∈ localPieces x) →
        targetLowerCorner x hx q hq 0 = 0
  /-- Coordinatewise ordering of selected target box corners. -/
  targetLower_le_targetUpper :
    ∀ x, (hx : x ∈ activeCharts) →
      ∀ q, (hq : q ∈ localPieces x) →
        targetLowerCorner x hx q hq ≤ targetUpperCorner x hx q hq
  /-- Compact image control for every active source boundary box. -/
  compactImage :
    ∀ x, (hx : x ∈ activeCharts) →
      ∀ q, (hq : q ∈ localPieces x) →
        boundaryChartCompactImageBoxSelection I (sourceChart x q)
          (boundarySourceChart x q) (sourceLowerCorner x q) (sourceUpperCorner x q)
          (targetLowerCorner x hx q hq) (targetUpperCorner x hx q hq)
  /-- Local right-inverse data on every selected target boundary box. -/
  localInverse :
    ∀ x, (hx : x ∈ activeCharts) →
      ∀ q, (hq : q ∈ localPieces x) →
        boundaryChartLocalInverseData I (sourceChart x q) (boundarySourceChart x q)
          (sourceLowerCorner x q) (sourceUpperCorner x q)
          (targetLowerCorner x hx q hq) (targetUpperCorner x hx q hq)

namespace BoundaryChartTargetBoxFamilySelection

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Package one active target entry as `BoundaryChartTargetBoxSelection`. -/
def targetSelection
    (F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    BoundaryChartTargetBoxSelection I (F.sourceChart x q) (F.boundarySourceChart x q)
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q) where
  lowerCorner := F.targetLowerCorner x hx q hq
  upperCorner := F.targetUpperCorner x hx q hq
  lowerCorner_zero := F.targetLowerCorner_zero x hx q hq
  lower_le_upper := F.targetLower_le_targetUpper x hx q hq
  compactImage := F.compactImage x hx q hq
  localInverse := F.localInverse x hx q hq

/-- Image-data projection for one active family entry. -/
theorem imageData
    (F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    boundaryChartSelectedBoxImageData I (F.sourceChart x q) (F.boundarySourceChart x q)
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x hx q hq) (F.targetUpperCorner x hx q hq) :=
  (F.targetSelection x hx q hq).imageData

/-- Map-to projection for one active family entry. -/
theorem mapsTo
    (F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    MapsTo (boundaryChartTransition I (F.sourceChart x q) (F.boundarySourceChart x q))
      (lowerZeroFaceDomain (F.sourceLowerCorner x q) (F.sourceUpperCorner x q))
      (lowerZeroFaceDomain (F.targetLowerCorner x hx q hq)
        (F.targetUpperCorner x hx q hq)) :=
  (F.imageData x hx q hq).mapsTo

/-- Surjectivity projection for one active family entry. -/
theorem surjOn
    (F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    SurjOn (boundaryChartTransition I (F.sourceChart x q) (F.boundarySourceChart x q))
      (lowerZeroFaceDomain (F.sourceLowerCorner x q) (F.sourceUpperCorner x q))
      (lowerZeroFaceDomain (F.targetLowerCorner x hx q hq)
        (F.targetUpperCorner x hx q hq)) :=
  (F.imageData x hx q hq).surjOn

/--
Build the selected-box image constructor package for one active entry from
explicit orientation-facing hypotheses.
-/
def selectedBoxImageConstructorData
    (F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x)
    (hcompat :
      boundaryChartTransitionCompatibleOn I (F.sourceChart x q) (F.boundarySourceChart x q)
        (lowerZeroFaceDomain (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)))
    (hdata :
      BoundaryChartOrientationMapDataOn I (F.sourceChart x q) (F.boundarySourceChart x q)
        (lowerZeroFaceDomain (F.sourceLowerCorner x q) (F.sourceUpperCorner x q))) :
    BoundaryChartSelectedBoxImageConstructorData I
      (F.sourceChart x q) (F.boundarySourceChart x q) ω
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q) where
  selectedBox := F.sourceSelectedBox x hx q hq
  targetSelection := F.targetSelection x hx q hq
  compatibleOn := hcompat
  orientationMapDataOn := hdata

/-- Selected-box orientation/COV bridge data for one active entry. -/
def selectedBoxOrientationCovData
    (F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x)
    (hcompat :
      boundaryChartTransitionCompatibleOn I (F.sourceChart x q) (F.boundarySourceChart x q)
        (lowerZeroFaceDomain (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)))
    (hdata :
      BoundaryChartOrientationMapDataOn I (F.sourceChart x q) (F.boundarySourceChart x q)
        (lowerZeroFaceDomain (F.sourceLowerCorner x q) (F.sourceUpperCorner x q))) :
    BoundaryChartSelectedBoxOrientationCovData I
      (F.sourceChart x q) (F.boundarySourceChart x q) ω
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x hx q hq) (F.targetUpperCorner x hx q hq) :=
  (F.selectedBoxImageConstructorData x hx q hq hcompat hdata)
    |>.BoundaryChartSelectedBoxOrientationCovData

/-- Oriented change-of-variables data for one active entry. -/
theorem orientedChangeOfVariables [IsManifold I 1 M]
    (F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x)
    (hcompat :
      boundaryChartTransitionCompatibleOn I (F.sourceChart x q) (F.boundarySourceChart x q)
        (lowerZeroFaceDomain (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)))
    (hdata :
      BoundaryChartOrientationMapDataOn I (F.sourceChart x q) (F.boundarySourceChart x q)
        (lowerZeroFaceDomain (F.sourceLowerCorner x q) (F.sourceUpperCorner x q))) :
    boundaryChartOrientedChangeOfVariables I
      (F.sourceChart x q) (F.boundarySourceChart x q) ω
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x hx q hq) (F.targetUpperCorner x hx q hq) :=
  (F.selectedBoxOrientationCovData x hx q hq hcompat hdata).orientedChangeOfVariables

/-- Oriented-atlas constructor package for one active entry. -/
def selectedBoxImageConstructorDataOfOrientedAtlas
    (F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x)
    (hsource : F.sourceChart x q ∈ A.charts)
    (hboundarySource : F.boundarySourceChart x q ∈ A.charts) :
    BoundaryChartSelectedBoxImageConstructorData I
      (F.sourceChart x q) (F.boundarySourceChart x q) ω
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q) :=
  BoundaryChartSelectedBoxImageConstructorData.ofOrientedAtlas
    A hsource hboundarySource (F.sourceSelectedBox x hx q hq)
    (F.targetSelection x hx q hq)

/-- Oriented-atlas selected-box orientation/COV data for one active entry. -/
def selectedBoxOrientationCovDataOfOrientedAtlas
    (F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x)
    (hsource : F.sourceChart x q ∈ A.charts)
    (hboundarySource : F.boundarySourceChart x q ∈ A.charts) :
    BoundaryChartSelectedBoxOrientationCovData I
      (F.sourceChart x q) (F.boundarySourceChart x q) ω
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x hx q hq) (F.targetUpperCorner x hx q hq) :=
  (F.selectedBoxImageConstructorDataOfOrientedAtlas
    A x hx q hq hsource hboundarySource)
    |>.BoundaryChartSelectedBoxOrientationCovData

/-- Oriented-atlas change-of-variables data for one active entry. -/
theorem orientedChangeOfVariablesOfOrientedAtlas [IsManifold I 1 M]
    (F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x)
    (hsource : F.sourceChart x q ∈ A.charts)
    (hboundarySource : F.boundarySourceChart x q ∈ A.charts) :
    boundaryChartOrientedChangeOfVariables I
      (F.sourceChart x q) (F.boundarySourceChart x q) ω
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x hx q hq) (F.targetUpperCorner x hx q hq) :=
  (F.selectedBoxOrientationCovDataOfOrientedAtlas
    A x hx q hq hsource hboundarySource).orientedChangeOfVariables

/-- Oriented-manifold constructor package for one active entry. -/
def selectedBoxImageConstructorDataOfOrientedManifold
    [BoundaryChartOrientedManifold I M]
    (F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    BoundaryChartSelectedBoxImageConstructorData I
      (F.sourceChart x q) (F.boundarySourceChart x q) ω
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q) :=
  BoundaryChartSelectedBoxImageConstructorData.ofOrientedManifold
    (F.sourceSelectedBox x hx q hq) (F.targetSelection x hx q hq)

/-- Oriented-manifold selected-box orientation/COV data for one active entry. -/
def selectedBoxOrientationCovDataOfOrientedManifold
    [BoundaryChartOrientedManifold I M]
    (F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    BoundaryChartSelectedBoxOrientationCovData I
      (F.sourceChart x q) (F.boundarySourceChart x q) ω
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x hx q hq) (F.targetUpperCorner x hx q hq) :=
  (F.selectedBoxImageConstructorDataOfOrientedManifold x hx q hq)
    |>.BoundaryChartSelectedBoxOrientationCovData

/-- Oriented-manifold change-of-variables data for one active entry. -/
theorem orientedChangeOfVariablesOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    boundaryChartOrientedChangeOfVariables I
      (F.sourceChart x q) (F.boundarySourceChart x q) ω
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x hx q hq) (F.targetUpperCorner x hx q hq) :=
  (F.selectedBoxOrientationCovDataOfOrientedManifold x hx q hq).orientedChangeOfVariables

/-- Constructor from already packaged per-piece target selections. -/
def ofTargetSelection
    (activeCharts : Finset Chart) (localPieces : Chart → Finset Piece)
    (sourceChart boundarySourceChart : Chart → Piece → M)
    (sourceLowerCorner sourceUpperCorner : Chart → Piece → Fin (n + 1) → Real)
    (sourceSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartSelectedBox I (sourceChart x q) (boundarySourceChart x q) ω
            (sourceLowerCorner x q) (sourceUpperCorner x q))
    (targetSelection :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          BoundaryChartTargetBoxSelection I (sourceChart x q) (boundarySourceChart x q)
            (sourceLowerCorner x q) (sourceUpperCorner x q)) :
    BoundaryChartTargetBoxFamilySelection I ω Chart Piece where
  activeCharts := activeCharts
  localPieces := localPieces
  sourceChart := sourceChart
  boundarySourceChart := boundarySourceChart
  sourceLowerCorner := sourceLowerCorner
  sourceUpperCorner := sourceUpperCorner
  sourceSelectedBox := sourceSelectedBox
  targetLowerCorner := fun x hx q hq => (targetSelection x hx q hq).lowerCorner
  targetUpperCorner := fun x hx q hq => (targetSelection x hx q hq).upperCorner
  targetLowerCorner_zero := fun x hx q hq =>
    (targetSelection x hx q hq).lowerCorner_zero
  targetLower_le_targetUpper := fun x hx q hq =>
    (targetSelection x hx q hq).lower_le_upper
  compactImage := fun x hx q hq => (targetSelection x hx q hq).compactImage
  localInverse := fun x hx q hq => (targetSelection x hx q hq).localInverse

/-- Constructor from compact-image and local-inverse data for every active piece. -/
def ofCompactImageLocalInverseData
    (activeCharts : Finset Chart) (localPieces : Chart → Finset Piece)
    (sourceChart boundarySourceChart : Chart → Piece → M)
    (sourceLowerCorner sourceUpperCorner : Chart → Piece → Fin (n + 1) → Real)
    (sourceSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartSelectedBox I (sourceChart x q) (boundarySourceChart x q) ω
            (sourceLowerCorner x q) (sourceUpperCorner x q))
    (targetLowerCorner :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x → Fin (n + 1) → Real)
    (targetUpperCorner :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x → Fin (n + 1) → Real)
    (targetLowerCorner_zero :
      ∀ x, (hx : x ∈ activeCharts) →
        ∀ q, (hq : q ∈ localPieces x) →
          targetLowerCorner x hx q hq 0 = 0)
    (targetLower_le_targetUpper :
      ∀ x, (hx : x ∈ activeCharts) →
        ∀ q, (hq : q ∈ localPieces x) →
          targetLowerCorner x hx q hq ≤ targetUpperCorner x hx q hq)
    (compactImage :
      ∀ x, (hx : x ∈ activeCharts) →
        ∀ q, (hq : q ∈ localPieces x) →
          boundaryChartCompactImageBoxSelection I (sourceChart x q)
            (boundarySourceChart x q) (sourceLowerCorner x q) (sourceUpperCorner x q)
            (targetLowerCorner x hx q hq) (targetUpperCorner x hx q hq))
    (localInverse :
      ∀ x, (hx : x ∈ activeCharts) →
        ∀ q, (hq : q ∈ localPieces x) →
          boundaryChartLocalInverseData I (sourceChart x q) (boundarySourceChart x q)
            (sourceLowerCorner x q) (sourceUpperCorner x q)
            (targetLowerCorner x hx q hq) (targetUpperCorner x hx q hq)) :
    BoundaryChartTargetBoxFamilySelection I ω Chart Piece where
  activeCharts := activeCharts
  localPieces := localPieces
  sourceChart := sourceChart
  boundarySourceChart := boundarySourceChart
  sourceLowerCorner := sourceLowerCorner
  sourceUpperCorner := sourceUpperCorner
  sourceSelectedBox := sourceSelectedBox
  targetLowerCorner := targetLowerCorner
  targetUpperCorner := targetUpperCorner
  targetLowerCorner_zero := targetLowerCorner_zero
  targetLower_le_targetUpper := targetLower_le_targetUpper
  compactImage := compactImage
  localInverse := localInverse

/--
Constructor from compact source-box packages and per-piece target selections.

This is the family analogue of
`BoundaryChartSelectedBoxImageConstructorData.ofBoundaryCompactBoxSelectionData`,
but it stops at target-box/image-data selection and stays in the pure boundary
chart layer.
-/
def ofBoundaryCompactBoxSelectionData
    (activeCharts : Finset Chart) (localPieces : Chart → Finset Piece)
    (sourceChart boundarySourceChart : Chart → Piece → M)
    (source :
      ∀ x q,
        BoundaryCompactBoxSelectionData I (sourceChart x q) (boundarySourceChart x q) ω)
    (targetSelection :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          BoundaryChartTargetBoxSelection I (sourceChart x q) (boundarySourceChart x q)
            (source x q).a (source x q).b) :
    BoundaryChartTargetBoxFamilySelection I ω Chart Piece :=
  ofTargetSelection activeCharts localPieces sourceChart boundarySourceChart
    (fun x q => (source x q).a) (fun x q => (source x q).b)
    (fun x _ q _ => (source x q).selectedBox) targetSelection

/--
Build a target-box family from per-chart compact-image covers.

For each active chart label, the cover's active pieces become the local pieces,
and each active cover member supplies compact-image and local-inverse data.
-/
def ofCompactImageCoverFamily
    (activeCharts : Finset Chart)
    (sourceChart boundarySourceChart : Chart → M)
    (chartLowerCorner chartUpperCorner : Chart → Fin (n + 1) → Real)
    (cover :
      ∀ x,
        BoundaryChartCompactImageCover I (sourceChart x) (boundarySourceChart x)
          (chartLowerCorner x) (chartUpperCorner x) Piece)
    (sourceSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ (cover x).activePieces →
          boundaryChartSelectedBox I (sourceChart x) (boundarySourceChart x) ω
            ((cover x).sourceLowerCorner q) ((cover x).sourceUpperCorner q)) :
    BoundaryChartTargetBoxFamilySelection I ω Chart Piece :=
  ofTargetSelection activeCharts (fun x => (cover x).activePieces)
    (fun x _ => sourceChart x) (fun x _ => boundarySourceChart x)
    (fun x q => (cover x).sourceLowerCorner q)
    (fun x q => (cover x).sourceUpperCorner q)
    (fun x hx q hq => sourceSelectedBox x hx q hq)
    (fun x _ q hq => (cover x).toTargetBoxSelection q hq)

/-- The compact-cover family constructor keeps the cover's target box on active pieces. -/
theorem ofCompactImageCoverFamily_targetSelection
    (activeCharts : Finset Chart)
    (sourceChart boundarySourceChart : Chart → M)
    (chartLowerCorner chartUpperCorner : Chart → Fin (n + 1) → Real)
    (cover :
      ∀ x,
        BoundaryChartCompactImageCover I (sourceChart x) (boundarySourceChart x)
          (chartLowerCorner x) (chartUpperCorner x) Piece)
    (sourceSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ (cover x).activePieces →
          boundaryChartSelectedBox I (sourceChart x) (boundarySourceChart x) ω
            ((cover x).sourceLowerCorner q) ((cover x).sourceUpperCorner q))
    (x : Chart) (hx : x ∈ activeCharts)
    (q : Piece) (hq : q ∈ (cover x).activePieces) :
    (ofCompactImageCoverFamily activeCharts sourceChart boundarySourceChart
        chartLowerCorner chartUpperCorner cover sourceSelectedBox).targetSelection
      x hx q hq = (cover x).toTargetBoxSelection q hq := by
  rfl

/--
The same compact-cover family constructor, starting from the local-inverse
target-cover input and materializing compact-image control piecewise.
-/
def ofCompactImageForLocalInverseTargetCoverFamily
    (activeCharts : Finset Chart)
    (sourceChart boundarySourceChart : Chart → M)
    (chartLowerCorner chartUpperCorner : Chart → Fin (n + 1) → Real)
    (cover :
      ∀ x,
        BoundaryChartCompactImageForLocalInverseTargetCover I
          (sourceChart x) (boundarySourceChart x)
          (chartLowerCorner x) (chartUpperCorner x) Piece)
    (sourceSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ (cover x).activePieces →
          boundaryChartSelectedBox I (sourceChart x) (boundarySourceChart x) ω
            ((cover x).sourceLowerCorner q) ((cover x).sourceUpperCorner q)) :
    BoundaryChartTargetBoxFamilySelection I ω Chart Piece :=
  ofCompactImageCoverFamily activeCharts sourceChart boundarySourceChart
    chartLowerCorner chartUpperCorner
    (fun x => (cover x).toCompactImageCover) sourceSelectedBox

/--
The local-inverse-target-cover constructor keeps the materialized cover's target
box on active pieces.
-/
theorem ofCompactImageForLocalInverseTargetCoverFamily_targetSelection
    (activeCharts : Finset Chart)
    (sourceChart boundarySourceChart : Chart → M)
    (chartLowerCorner chartUpperCorner : Chart → Fin (n + 1) → Real)
    (cover :
      ∀ x,
        BoundaryChartCompactImageForLocalInverseTargetCover I
          (sourceChart x) (boundarySourceChart x)
          (chartLowerCorner x) (chartUpperCorner x) Piece)
    (sourceSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ (cover x).activePieces →
          boundaryChartSelectedBox I (sourceChart x) (boundarySourceChart x) ω
            ((cover x).sourceLowerCorner q) ((cover x).sourceUpperCorner q))
    (x : Chart) (hx : x ∈ activeCharts)
    (q : Piece) (hq : q ∈ (cover x).activePieces) :
    (ofCompactImageForLocalInverseTargetCoverFamily activeCharts
        sourceChart boundarySourceChart chartLowerCorner chartUpperCorner
        cover sourceSelectedBox).targetSelection x hx q hq =
      (cover x).toTargetBoxSelection q hq := by
  rfl

end BoundaryChartTargetBoxFamilySelection

/--
Batch target-box selection from oriented-atlas source boxes.

For every active source box, the single-box oriented-atlas theorem selects a
target boundary box carrying compact image control, local inverse data, and
therefore image data.
-/
theorem exists_boundaryChartTargetBoxFamilySelection_of_selectedBoxes_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M]
    {ω : ManifoldForm I M n} {Chart : Type c} {Piece : Type p}
    (A : BoundaryChartOrientedAtlas I M)
    (activeCharts : Finset Chart) (localPieces : Chart → Finset Piece)
    (sourceChart boundarySourceChart : Chart → Piece → M)
    (sourceLowerCorner sourceUpperCorner : Chart → Piece → Fin (n + 1) → Real)
    (sourceSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartSelectedBox I (sourceChart x q) (boundarySourceChart x q) ω
            (sourceLowerCorner x q) (sourceUpperCorner x q))
    (hsourceChart :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x → sourceChart x q ∈ A.charts)
    (hboundarySourceChart :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x → boundarySourceChart x q ∈ A.charts)
    (u : Chart → Piece → Fin n → Real)
    (hu :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          u x q ∈ lowerZeroFaceDomain (sourceLowerCorner x q) (sourceUpperCorner x q))
    (hsource :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          lowerZeroFaceDomain (sourceLowerCorner x q) (sourceUpperCorner x q) ∈
            𝓝 (u x q))
    (hcompact :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartCompactCoordinateImageForLocalInverseTargets I
            (sourceChart x q) (boundarySourceChart x q)
            (sourceLowerCorner x q) (sourceUpperCorner x q)
            (boundaryChartTransition I (sourceChart x q) (boundarySourceChart x q)
              (u x q))) :
    ∃ F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece,
      (∀ x, (hx : x ∈ F.activeCharts) →
        ∀ q, (hq : q ∈ F.localPieces x) →
          boundaryChartTransition I (F.sourceChart x q) (F.boundarySourceChart x q)
              (u x q) ∈
            lowerZeroFaceDomain (F.targetLowerCorner x hx q hq)
              (F.targetUpperCorner x hx q hq)) := by
  classical
  let htarget :
      ∀ x, (hx : x ∈ activeCharts) →
        ∀ q, (hq : q ∈ localPieces x) →
          ∃ D : BoundaryChartTargetBoxSelection I (sourceChart x q)
              (boundarySourceChart x q) (sourceLowerCorner x q) (sourceUpperCorner x q),
            boundaryChartTransition I (sourceChart x q) (boundarySourceChart x q)
                (u x q) ∈ lowerZeroFaceDomain D.lowerCorner D.upperCorner ∧
              boundaryChartSelectedBoxImageData I (sourceChart x q)
                (boundarySourceChart x q) (sourceLowerCorner x q) (sourceUpperCorner x q)
                D.lowerCorner D.upperCorner := by
    intro x hx q hq
    exact exists_boundaryChartTargetBoxSelection_of_selectedBox_orientedAtlas
      A (hsourceChart x hx q hq) (hboundarySourceChart x hx q hq)
      (sourceSelectedBox x hx q hq) (hu x hx q hq) (hsource x hx q hq)
      (hcompact x hx q hq)
  let targetSelection :
      ∀ x, (hx : x ∈ activeCharts) →
        ∀ q, (hq : q ∈ localPieces x) →
          BoundaryChartTargetBoxSelection I (sourceChart x q) (boundarySourceChart x q)
            (sourceLowerCorner x q) (sourceUpperCorner x q) :=
    fun x hx q hq => Classical.choose (htarget x hx q hq)
  refine ⟨BoundaryChartTargetBoxFamilySelection.ofTargetSelection
    activeCharts localPieces sourceChart boundarySourceChart
    sourceLowerCorner sourceUpperCorner sourceSelectedBox targetSelection, ?_⟩
  intro x hx q hq
  exact (Classical.choose_spec (htarget x hx q hq)).1

/--
Batch target-box selection from global oriented-boundary-manifold source boxes.
-/
theorem exists_boundaryChartTargetBoxFamilySelection_of_selectedBoxes_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M] [BoundaryChartOrientedManifold I M]
    {ω : ManifoldForm I M n} {Chart : Type c} {Piece : Type p}
    (activeCharts : Finset Chart) (localPieces : Chart → Finset Piece)
    (sourceChart boundarySourceChart : Chart → Piece → M)
    (sourceLowerCorner sourceUpperCorner : Chart → Piece → Fin (n + 1) → Real)
    (sourceSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartSelectedBox I (sourceChart x q) (boundarySourceChart x q) ω
            (sourceLowerCorner x q) (sourceUpperCorner x q))
    (u : Chart → Piece → Fin n → Real)
    (hu :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          u x q ∈ lowerZeroFaceDomain (sourceLowerCorner x q) (sourceUpperCorner x q))
    (hsource :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          lowerZeroFaceDomain (sourceLowerCorner x q) (sourceUpperCorner x q) ∈
            𝓝 (u x q))
    (hcompact :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartCompactCoordinateImageForLocalInverseTargets I
            (sourceChart x q) (boundarySourceChart x q)
            (sourceLowerCorner x q) (sourceUpperCorner x q)
            (boundaryChartTransition I (sourceChart x q) (boundarySourceChart x q)
              (u x q))) :
    ∃ F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece,
      (∀ x, (hx : x ∈ F.activeCharts) →
        ∀ q, (hq : q ∈ F.localPieces x) →
          boundaryChartTransition I (F.sourceChart x q) (F.boundarySourceChart x q)
              (u x q) ∈
            lowerZeroFaceDomain (F.targetLowerCorner x hx q hq)
              (F.targetUpperCorner x hx q hq)) := by
  classical
  let htarget :
      ∀ x, (hx : x ∈ activeCharts) →
        ∀ q, (hq : q ∈ localPieces x) →
          ∃ D : BoundaryChartTargetBoxSelection I (sourceChart x q)
              (boundarySourceChart x q) (sourceLowerCorner x q) (sourceUpperCorner x q),
            boundaryChartTransition I (sourceChart x q) (boundarySourceChart x q)
                (u x q) ∈ lowerZeroFaceDomain D.lowerCorner D.upperCorner ∧
              boundaryChartSelectedBoxImageData I (sourceChart x q)
                (boundarySourceChart x q) (sourceLowerCorner x q) (sourceUpperCorner x q)
                D.lowerCorner D.upperCorner := by
    intro x hx q hq
    exact exists_boundaryChartTargetBoxSelection_of_selectedBox_orientedManifold
      (sourceSelectedBox x hx q hq) (hu x hx q hq) (hsource x hx q hq)
      (hcompact x hx q hq)
  let targetSelection :
      ∀ x, (hx : x ∈ activeCharts) →
        ∀ q, (hq : q ∈ localPieces x) →
          BoundaryChartTargetBoxSelection I (sourceChart x q) (boundarySourceChart x q)
            (sourceLowerCorner x q) (sourceUpperCorner x q) :=
    fun x hx q hq => Classical.choose (htarget x hx q hq)
  refine ⟨BoundaryChartTargetBoxFamilySelection.ofTargetSelection
    activeCharts localPieces sourceChart boundarySourceChart
    sourceLowerCorner sourceUpperCorner sourceSelectedBox targetSelection, ?_⟩
  intro x hx q hq
  exact (Classical.choose_spec (htarget x hx q hq)).1

end ManifoldBoundary

end Stokes

end
