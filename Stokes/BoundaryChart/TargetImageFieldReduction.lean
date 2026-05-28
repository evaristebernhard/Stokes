import Stokes.BoundaryChart.TargetBoxFamilySelection
import Stokes.BoundaryChart.OrientedAtlasSelectedBoxCOV

/-!
# Boundary chart target-image field reduction

This file is a pure `BoundaryChart` glue layer.  It resolves the target-image
fields of a finite boundary-chart family into one proof-free target-box
function, then reuses the existing target-box family and oriented-atlas COV
constructors.

No global reconstruction, partition, or assembly data is imported here.
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
Target-image data for a finite boundary-chart family after resolving the target
box to a proof-free field.

The `targetBox` field is the single source of target-image truth: it contains
the target corners, compact-image containment, and local right-inverse data.
The projections below recover the older proof-indexed
`BoundaryChartTargetBoxFamilySelection` shape and the COV-family shape used by
`OrientedAtlasSelectedBoxCOV`.
-/
structure BoundaryChartTargetImageResolvedFamily {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n) (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in this boundary target-image family. -/
  activeCharts : Finset Chart
  /-- Finite local boundary pieces attached to each active chart label. -/
  localPieces : Chart → Finset Piece
  /-- Source chart for the original boundary chart integral. -/
  sourceChart : Chart → Piece → M
  /-- Boundary chart reached from the source chart by COV. -/
  boundarySourceChart : Chart → Piece → M
  /-- Auxiliary target chart used to write the transported boundary integral. -/
  boundaryTargetChart : Chart → Piece → M
  /-- Source lower corner. -/
  sourceLowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Source upper corner. -/
  sourceUpperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Selected source boundary box for every active family piece. -/
  sourceSelectedBox :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ localPieces x →
        boundaryChartSelectedBox I (sourceChart x q) (boundarySourceChart x q) ω
          (sourceLowerCorner x q) (sourceUpperCorner x q)
  /--
  Resolved target-image box.  This single field carries target corners,
  compact-image control, and local right-inverse data.
  -/
  targetBox :
    ∀ x q,
      BoundaryChartTargetBoxSelection I (sourceChart x q) (boundarySourceChart x q)
        (sourceLowerCorner x q) (sourceUpperCorner x q)
  /-- Selected target boundary box for every active family piece. -/
  targetSelectedBox :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ localPieces x →
        boundaryChartSelectedBox I (boundarySourceChart x q)
          (boundaryTargetChart x q) ω
          ((targetBox x q).lowerCorner) ((targetBox x q).upperCorner)

namespace BoundaryChartTargetImageResolvedFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Target lower corner selected for a family piece. -/
def targetLowerCorner
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) → Real :=
  (F.targetBox x q).lowerCorner

/-- Target upper corner selected for a family piece. -/
def targetUpperCorner
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) → Real :=
  (F.targetBox x q).upperCorner

/-- Target lower corners satisfy the lower-zero-face convention. -/
theorem targetLowerCorner_zero
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (q : Piece) :
    F.targetLowerCorner x q 0 = 0 :=
  (F.targetBox x q).lowerCorner_zero

/-- Target lower and upper corners are coordinatewise ordered. -/
theorem targetLower_le_targetUpper
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (q : Piece) :
    F.targetLowerCorner x q ≤ F.targetUpperCorner x q :=
  (F.targetBox x q).lower_le_upper

/-- Compact image control supplied by the resolved target box. -/
theorem compactImage
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (q : Piece) :
    boundaryChartCompactImageBoxSelection I (F.sourceChart x q)
      (F.boundarySourceChart x q) (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x q) (F.targetUpperCorner x q) :=
  (F.targetBox x q).compactImage

/-- Local right-inverse data supplied by the resolved target box. -/
theorem localInverse
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (q : Piece) :
    boundaryChartLocalInverseData I (F.sourceChart x q) (F.boundarySourceChart x q)
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x q) (F.targetUpperCorner x q) :=
  (F.targetBox x q).localInverse

/-- The selected auxiliary target box, written using the resolved corner names. -/
theorem selectedTargetBox
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    boundaryChartSelectedBox I (F.boundarySourceChart x q)
      (F.boundaryTargetChart x q) ω
      (F.targetLowerCorner x q) (F.targetUpperCorner x q) := by
  simpa [targetLowerCorner, targetUpperCorner] using
    F.targetSelectedBox x hx q hq

/-- Image-data projection for one resolved family piece. -/
theorem imageData
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (q : Piece) :
    boundaryChartSelectedBoxImageData I (F.sourceChart x q) (F.boundarySourceChart x q)
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x q) (F.targetUpperCorner x q) :=
  (F.targetBox x q).imageData

/-- Map-to projection for one resolved family piece. -/
theorem mapsTo
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (q : Piece) :
    MapsTo (boundaryChartTransition I (F.sourceChart x q) (F.boundarySourceChart x q))
      (lowerZeroFaceDomain (F.sourceLowerCorner x q) (F.sourceUpperCorner x q))
      (lowerZeroFaceDomain (F.targetLowerCorner x q) (F.targetUpperCorner x q)) :=
  (F.imageData x q).mapsTo

/-- Surjectivity projection for one resolved family piece. -/
theorem surjOn
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (q : Piece) :
    SurjOn (boundaryChartTransition I (F.sourceChart x q) (F.boundarySourceChart x q))
      (lowerZeroFaceDomain (F.sourceLowerCorner x q) (F.sourceUpperCorner x q))
      (lowerZeroFaceDomain (F.targetLowerCorner x q) (F.targetUpperCorner x q)) :=
  (F.imageData x q).surjOn

/-- Recover the older proof-indexed target-box family shape. -/
def toTargetBoxFamilySelection
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece) :
    BoundaryChartTargetBoxFamilySelection I ω Chart Piece where
  activeCharts := F.activeCharts
  localPieces := F.localPieces
  sourceChart := F.sourceChart
  boundarySourceChart := F.boundarySourceChart
  sourceLowerCorner := F.sourceLowerCorner
  sourceUpperCorner := F.sourceUpperCorner
  sourceSelectedBox := F.sourceSelectedBox
  targetLowerCorner := fun x _ q _ => F.targetLowerCorner x q
  targetUpperCorner := fun x _ q _ => F.targetUpperCorner x q
  targetLowerCorner_zero := fun x _ q _ => F.targetLowerCorner_zero x q
  targetLower_le_targetUpper := fun x _ q _ => F.targetLower_le_targetUpper x q
  compactImage := fun x _ q _ => F.compactImage x q
  localInverse := fun x _ q _ => F.localInverse x q

/-- The proof-indexed family selection keeps the resolved target box on active pieces. -/
theorem toTargetBoxFamilySelection_targetSelection
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    (F.toTargetBoxFamilySelection).targetSelection x hx q hq = F.targetBox x q := by
  rfl

/-- Local inverse data exposed through the proof-indexed target-box family. -/
theorem toTargetBoxFamilySelection_localInverse
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    boundaryChartLocalInverseData I
      ((F.toTargetBoxFamilySelection).sourceChart x q)
      ((F.toTargetBoxFamilySelection).boundarySourceChart x q)
      ((F.toTargetBoxFamilySelection).sourceLowerCorner x q)
      ((F.toTargetBoxFamilySelection).sourceUpperCorner x q)
      ((F.toTargetBoxFamilySelection).targetLowerCorner x hx q hq)
      ((F.toTargetBoxFamilySelection).targetUpperCorner x hx q hq) :=
  (F.toTargetBoxFamilySelection).localInverse x hx q hq

/-- The selected target boundary box exposed through the proof-indexed family. -/
theorem toTargetBoxFamilySelection_selectedTargetBox
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    boundaryChartSelectedBox I (F.boundarySourceChart x q)
      (F.boundaryTargetChart x q) ω
      ((F.toTargetBoxFamilySelection).targetLowerCorner x hx q hq)
      ((F.toTargetBoxFamilySelection).targetUpperCorner x hx q hq) := by
  simpa [toTargetBoxFamilySelection, targetLowerCorner, targetUpperCorner] using
    F.selectedTargetBox x hx q hq

/-- Build the selected-box COV family shape consumed by oriented-atlas COV. -/
def toSelectedBoxCOVFamilyData
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece) :
    BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece where
  activeCharts := F.activeCharts
  localPieces := F.localPieces
  sourceChart := F.sourceChart
  boundarySourceChart := F.boundarySourceChart
  boundaryTargetChart := F.boundaryTargetChart
  sourceLowerCorner := F.sourceLowerCorner
  sourceUpperCorner := F.sourceUpperCorner
  sourceSelectedBox := F.sourceSelectedBox
  targetBox := F.targetBox
  targetSelectedBox := F.targetSelectedBox

/-- The COV-family projection keeps the resolved target box field. -/
theorem toSelectedBoxCOVFamilyData_targetBox
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (q : Piece) :
    (F.toSelectedBoxCOVFamilyData).targetBox x q = F.targetBox x q :=
  rfl

/-- Local inverse data exposed through the selected-box COV family. -/
theorem toSelectedBoxCOVFamilyData_localInverse
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (q : Piece) :
    boundaryChartLocalInverseData I
      ((F.toSelectedBoxCOVFamilyData).sourceChart x q)
      ((F.toSelectedBoxCOVFamilyData).boundarySourceChart x q)
      ((F.toSelectedBoxCOVFamilyData).sourceLowerCorner x q)
      ((F.toSelectedBoxCOVFamilyData).sourceUpperCorner x q)
      ((F.toSelectedBoxCOVFamilyData).targetLowerCorner x q)
      ((F.toSelectedBoxCOVFamilyData).targetUpperCorner x q) := by
  simpa [toSelectedBoxCOVFamilyData,
    BoundaryChartSelectedBoxCOVFamilyData.targetLowerCorner,
    BoundaryChartSelectedBoxCOVFamilyData.targetUpperCorner] using
    F.localInverse x q

/-- The selected target boundary box exposed through the selected-box COV family. -/
theorem toSelectedBoxCOVFamilyData_selectedTargetBox
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    boundaryChartSelectedBox I
      ((F.toSelectedBoxCOVFamilyData).boundarySourceChart x q)
      ((F.toSelectedBoxCOVFamilyData).boundaryTargetChart x q) ω
      ((F.toSelectedBoxCOVFamilyData).targetLowerCorner x q)
      ((F.toSelectedBoxCOVFamilyData).targetUpperCorner x q) := by
  simpa [toSelectedBoxCOVFamilyData,
    BoundaryChartSelectedBoxCOVFamilyData.targetLowerCorner,
    BoundaryChartSelectedBoxCOVFamilyData.targetUpperCorner,
    targetLowerCorner, targetUpperCorner] using
    F.selectedTargetBox x hx q hq

/-- Constructor from a proof-free target-box field. -/
def ofTargetBox
    (activeCharts : Finset Chart) (localPieces : Chart → Finset Piece)
    (sourceChart boundarySourceChart boundaryTargetChart : Chart → Piece → M)
    (sourceLowerCorner sourceUpperCorner : Chart → Piece → Fin (n + 1) → Real)
    (sourceSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartSelectedBox I (sourceChart x q) (boundarySourceChart x q) ω
            (sourceLowerCorner x q) (sourceUpperCorner x q))
    (targetBox :
      ∀ x q,
        BoundaryChartTargetBoxSelection I (sourceChart x q) (boundarySourceChart x q)
          (sourceLowerCorner x q) (sourceUpperCorner x q))
    (targetSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartSelectedBox I (boundarySourceChart x q)
            (boundaryTargetChart x q) ω
            ((targetBox x q).lowerCorner) ((targetBox x q).upperCorner)) :
    BoundaryChartTargetImageResolvedFamily I ω Chart Piece where
  activeCharts := activeCharts
  localPieces := localPieces
  sourceChart := sourceChart
  boundarySourceChart := boundarySourceChart
  boundaryTargetChart := boundaryTargetChart
  sourceLowerCorner := sourceLowerCorner
  sourceUpperCorner := sourceUpperCorner
  sourceSelectedBox := sourceSelectedBox
  targetBox := targetBox
  targetSelectedBox := targetSelectedBox

/--
Resolve a proof-indexed target-box family by supplying a proof-free target-box
representative that agrees with the active entries.
-/
def ofTargetBoxFamilySelection
    (F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece)
    (boundaryTargetChart : Chart → Piece → M)
    (targetBox :
      ∀ x q,
        BoundaryChartTargetBoxSelection I (F.sourceChart x q)
          (F.boundarySourceChart x q)
          (F.sourceLowerCorner x q) (F.sourceUpperCorner x q))
    (targetBox_eq :
      ∀ x, (hx : x ∈ F.activeCharts) →
        ∀ q, (hq : q ∈ F.localPieces x) →
          targetBox x q = F.targetSelection x hx q hq)
    (targetSelectedBox :
      ∀ x, (hx : x ∈ F.activeCharts) →
        ∀ q, (hq : q ∈ F.localPieces x) →
          boundaryChartSelectedBox I (F.boundarySourceChart x q)
            (boundaryTargetChart x q) ω
            (F.targetLowerCorner x hx q hq) (F.targetUpperCorner x hx q hq)) :
    BoundaryChartTargetImageResolvedFamily I ω Chart Piece where
  activeCharts := F.activeCharts
  localPieces := F.localPieces
  sourceChart := F.sourceChart
  boundarySourceChart := F.boundarySourceChart
  boundaryTargetChart := boundaryTargetChart
  sourceLowerCorner := F.sourceLowerCorner
  sourceUpperCorner := F.sourceUpperCorner
  sourceSelectedBox := F.sourceSelectedBox
  targetBox := targetBox
  targetSelectedBox := by
    intro x hx q hq
    simpa [targetBox_eq x hx q hq,
      BoundaryChartTargetBoxFamilySelection.targetSelection] using
      targetSelectedBox x hx q hq

/-- Oriented-atlas COV family from resolved target-image data. -/
def toChangeOfVariablesFamilyOfOrientedAtlas [IsManifold I 1 M]
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.localPieces x → F.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.localPieces x → F.boundarySourceChart x q ∈ A.charts) :
    BoundaryChartChangeOfVariablesFamily I ω Chart Piece :=
  F.toSelectedBoxCOVFamilyData.toChangeOfVariablesFamilyOfOrientedAtlas
    A hsource hboundarySource

/-- Oriented-manifold COV family from resolved target-image data. -/
def toChangeOfVariablesFamilyOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece) :
    BoundaryChartChangeOfVariablesFamily I ω Chart Piece :=
  F.toSelectedBoxCOVFamilyData.toChangeOfVariablesFamilyOfOrientedManifold

/-- Oriented-atlas selected-box orientation/COV data for one active entry. -/
def selectedBoxOrientationCovDataOfOrientedAtlas
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x)
    (hsource : F.sourceChart x q ∈ A.charts)
    (hboundarySource : F.boundarySourceChart x q ∈ A.charts) :
    BoundaryChartSelectedBoxOrientationCovData I
      (F.sourceChart x q) (F.boundarySourceChart x q) ω
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x q) (F.targetUpperCorner x q) :=
  (F.toTargetBoxFamilySelection).selectedBoxOrientationCovDataOfOrientedAtlas
    A x hx q hq hsource hboundarySource

/-- Oriented-atlas change-of-variables data for one active entry. -/
theorem orientedChangeOfVariablesOfOrientedAtlas [IsManifold I 1 M]
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x)
    (hsource : F.sourceChart x q ∈ A.charts)
    (hboundarySource : F.boundarySourceChart x q ∈ A.charts) :
    boundaryChartOrientedChangeOfVariables I
      (F.sourceChart x q) (F.boundarySourceChart x q) ω
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x q) (F.targetUpperCorner x q) :=
  (F.selectedBoxOrientationCovDataOfOrientedAtlas
    A x hx q hq hsource hboundarySource).orientedChangeOfVariables

/-- Oriented-manifold selected-box orientation/COV data for one active entry. -/
def selectedBoxOrientationCovDataOfOrientedManifold
    [BoundaryChartOrientedManifold I M]
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    BoundaryChartSelectedBoxOrientationCovData I
      (F.sourceChart x q) (F.boundarySourceChart x q) ω
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x q) (F.targetUpperCorner x q) :=
  (F.toTargetBoxFamilySelection).selectedBoxOrientationCovDataOfOrientedManifold
    x hx q hq

/-- Oriented-manifold change-of-variables data for one active entry. -/
theorem orientedChangeOfVariablesOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    boundaryChartOrientedChangeOfVariables I
      (F.sourceChart x q) (F.boundarySourceChart x q) ω
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x q) (F.targetUpperCorner x q) :=
  (F.selectedBoxOrientationCovDataOfOrientedManifold x hx q hq).orientedChangeOfVariables

end BoundaryChartTargetImageResolvedFamily

/--
Top-level oriented-atlas constructor from resolved target-image data to a
finite boundary-chart COV family.
-/
def boundaryChartChangeOfVariablesFamily_of_orientedAtlas_targetImageResolvedFamily
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] {ω : ManifoldForm I M n}
    {Chart : Type c} {Piece : Type p}
    (A : BoundaryChartOrientedAtlas I M)
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece)
    (hsource :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.localPieces x → F.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.localPieces x → F.boundarySourceChart x q ∈ A.charts) :
    BoundaryChartChangeOfVariablesFamily I ω Chart Piece :=
  F.toChangeOfVariablesFamilyOfOrientedAtlas A hsource hboundarySource

/--
Top-level oriented-manifold constructor from resolved target-image data to a
finite boundary-chart COV family.
-/
def boundaryChartChangeOfVariablesFamily_of_orientedManifold_targetImageResolvedFamily
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    {ω : ManifoldForm I M n} {Chart : Type c} {Piece : Type p}
    (F : BoundaryChartTargetImageResolvedFamily I ω Chart Piece) :
    BoundaryChartChangeOfVariablesFamily I ω Chart Piece :=
  F.toChangeOfVariablesFamilyOfOrientedManifold

end ManifoldBoundary

end Stokes

end
