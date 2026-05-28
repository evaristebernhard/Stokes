import Stokes.BoundaryChart.ChangeOfVariablesFamily
import Stokes.BoundaryChart.SelectedBoxImageConstructor
import Stokes.BoundaryChart.TransitionDerivative

/-!
# Oriented-atlas selected-box COV families

This file is a pure `BoundaryChart` glue layer.  It turns a finite family of
selected source boundary boxes, together with selected target image boxes, into
the `BoundaryChartChangeOfVariablesFamily` package used by the finite-sum
change-of-variables wrappers.
-/

noncomputable section

open Set
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Selected-box and target-box data for a finite boundary-chart COV family.

The source selected box and target image selection produce the oriented COV
package for each active piece.  The target selected box is the auxiliary
selected-box representative required by `BoundaryChartChangeOfVariablesFamily`
to rewrite the transported in-chart term as a target boundary-chart integral.
-/
structure BoundaryChartSelectedBoxCOVFamilyData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n) (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in this family. -/
  activeCharts : Finset Chart
  /-- Finite local boundary pieces attached to each chart label. -/
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
  /-- Selected target image box for the transition from source to boundary source. -/
  targetBox :
    (x : Chart) → (q : Piece) →
      BoundaryChartTargetBoxSelection I (sourceChart x q) (boundarySourceChart x q)
        (sourceLowerCorner x q) (sourceUpperCorner x q)
  /--
  Selected auxiliary target boundary box for the transported target integral.
  Its corners are the corners selected by `targetBox`.
  -/
  targetSelectedBox :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ localPieces x →
        boundaryChartSelectedBox I (boundarySourceChart x q) (boundaryTargetChart x q) ω
          ((targetBox x q).lowerCorner) ((targetBox x q).upperCorner)

namespace BoundaryChartSelectedBoxCOVFamilyData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Target lower corner selected for a family piece. -/
def targetLowerCorner
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) → Real :=
  (data.targetBox x q).lowerCorner

/-- Target upper corner selected for a family piece. -/
def targetUpperCorner
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) → Real :=
  (data.targetBox x q).upperCorner

/-- Target lower corners satisfy the lower-zero-face convention. -/
theorem targetLowerCorner_zero
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece)
    (x : Chart) (q : Piece) :
    data.targetLowerCorner x q 0 = 0 :=
  (data.targetBox x q).lowerCorner_zero

/-- Target lower and upper corners are coordinatewise ordered. -/
theorem targetLower_le_targetUpper
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece)
    (x : Chart) (q : Piece) :
    data.targetLowerCorner x q ≤ data.targetUpperCorner x q :=
  (data.targetBox x q).lower_le_upper

/-- Image-data projection supplied by the selected target box. -/
theorem targetImageData
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece)
    (x : Chart) (q : Piece) :
    boundaryChartSelectedBoxImageData I (data.sourceChart x q)
      (data.boundarySourceChart x q) (data.sourceLowerCorner x q)
      (data.sourceUpperCorner x q) (data.targetLowerCorner x q)
      (data.targetUpperCorner x q) := by
  simpa [targetLowerCorner, targetUpperCorner] using
    (data.targetBox x q).imageData

/--
Selected-box image constructor data for one active piece, with orientation data
coming from an oriented boundary-chart atlas.
-/
def selectedBoxImageConstructorDataOfOrientedAtlas
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (x : Chart) (hx : x ∈ data.activeCharts)
    (q : Piece) (hq : q ∈ data.localPieces x)
    (hsource : data.sourceChart x q ∈ A.charts)
    (hboundarySource : data.boundarySourceChart x q ∈ A.charts) :
    BoundaryChartSelectedBoxImageConstructorData I
      (data.sourceChart x q) (data.boundarySourceChart x q) ω
      (data.sourceLowerCorner x q) (data.sourceUpperCorner x q) :=
  BoundaryChartSelectedBoxImageConstructorData.ofOrientedAtlas
    A hsource hboundarySource (data.sourceSelectedBox x hx q hq)
    (data.targetBox x q)

/--
Selected-box orientation/COV data for one active piece, with orientation data
coming from an oriented boundary-chart atlas.
-/
def selectedBoxOrientationCovDataOfOrientedAtlas
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (x : Chart) (hx : x ∈ data.activeCharts)
    (q : Piece) (hq : q ∈ data.localPieces x)
    (hsource : data.sourceChart x q ∈ A.charts)
    (hboundarySource : data.boundarySourceChart x q ∈ A.charts) :
    BoundaryChartSelectedBoxOrientationCovData I
      (data.sourceChart x q) (data.boundarySourceChart x q) ω
      (data.sourceLowerCorner x q) (data.sourceUpperCorner x q)
      (data.targetLowerCorner x q) (data.targetUpperCorner x q) := by
  simpa [targetLowerCorner, targetUpperCorner] using
    (data.selectedBoxImageConstructorDataOfOrientedAtlas
      A x hx q hq hsource hboundarySource)
      |>.BoundaryChartSelectedBoxOrientationCovData

/-- Oriented-atlas COV projection for one active selected boundary-chart box. -/
theorem orientedChangeOfVariablesOfOrientedAtlas [IsManifold I 1 M]
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (x : Chart) (hx : x ∈ data.activeCharts)
    (q : Piece) (hq : q ∈ data.localPieces x)
    (hsource : data.sourceChart x q ∈ A.charts)
    (hboundarySource : data.boundarySourceChart x q ∈ A.charts) :
    boundaryChartOrientedChangeOfVariables I
      (data.sourceChart x q) (data.boundarySourceChart x q) ω
      (data.sourceLowerCorner x q) (data.sourceUpperCorner x q)
      (data.targetLowerCorner x q) (data.targetUpperCorner x q) :=
  (data.selectedBoxOrientationCovDataOfOrientedAtlas
    A x hx q hq hsource hboundarySource).orientedChangeOfVariables

/--
Projection to the raw COV hypotheses for one active selected boundary-chart
box, with orientation data coming from an oriented boundary-chart atlas.
-/
theorem changeOfVariablesHypothesesOfOrientedAtlas [IsManifold I 1 M]
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (x : Chart) (hx : x ∈ data.activeCharts)
    (q : Piece) (hq : q ∈ data.localPieces x)
    (hsource : data.sourceChart x q ∈ A.charts)
    (hboundarySource : data.boundarySourceChart x q ∈ A.charts) :
    boundaryChartTransitionCompatibleOn I (data.sourceChart x q)
        (data.boundarySourceChart x q)
        (lowerZeroFaceDomain (data.sourceLowerCorner x q)
          (data.sourceUpperCorner x q)) ∧
      boundaryChartOrientationCompatibleOn I (data.sourceChart x q)
        (data.boundarySourceChart x q)
        (lowerZeroFaceDomain (data.sourceLowerCorner x q)
          (data.sourceUpperCorner x q)) ∧
        (∀ u ∈ lowerZeroFaceDomain (data.sourceLowerCorner x q)
            (data.sourceUpperCorner x q),
          HasFDerivWithinAt
            (boundaryChartTransition I (data.sourceChart x q)
              (data.boundarySourceChart x q))
            (boundaryChartTransitionTangentMap I (data.sourceChart x q)
              (data.boundarySourceChart x q) u)
            (lowerZeroFaceDomain (data.sourceLowerCorner x q)
              (data.sourceUpperCorner x q)) u) ∧
          Set.InjOn
            (boundaryChartTransition I (data.sourceChart x q)
              (data.boundarySourceChart x q))
            (lowerZeroFaceDomain (data.sourceLowerCorner x q)
              (data.sourceUpperCorner x q)) ∧
            (boundaryChartTransition I (data.sourceChart x q)
                (data.boundarySourceChart x q)) ''
                lowerZeroFaceDomain (data.sourceLowerCorner x q)
                  (data.sourceUpperCorner x q) =
              lowerZeroFaceDomain (data.targetLowerCorner x q)
                (data.targetUpperCorner x q) :=
  (data.selectedBoxOrientationCovDataOfOrientedAtlas
    A x hx q hq hsource hboundarySource).changeOfVariablesHypotheses

/--
Selected-box image constructor data for one active piece, with orientation data
coming from global oriented-boundary-manifold data.
-/
def selectedBoxImageConstructorDataOfOrientedManifold
    [BoundaryChartOrientedManifold I M]
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece)
    (x : Chart) (hx : x ∈ data.activeCharts)
    (q : Piece) (hq : q ∈ data.localPieces x) :
    BoundaryChartSelectedBoxImageConstructorData I
      (data.sourceChart x q) (data.boundarySourceChart x q) ω
      (data.sourceLowerCorner x q) (data.sourceUpperCorner x q) :=
  BoundaryChartSelectedBoxImageConstructorData.ofOrientedManifold
    (data.sourceSelectedBox x hx q hq) (data.targetBox x q)

/--
Selected-box orientation/COV data for one active piece, with orientation data
coming from global oriented-boundary-manifold data.
-/
def selectedBoxOrientationCovDataOfOrientedManifold
    [BoundaryChartOrientedManifold I M]
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece)
    (x : Chart) (hx : x ∈ data.activeCharts)
    (q : Piece) (hq : q ∈ data.localPieces x) :
    BoundaryChartSelectedBoxOrientationCovData I
      (data.sourceChart x q) (data.boundarySourceChart x q) ω
      (data.sourceLowerCorner x q) (data.sourceUpperCorner x q)
      (data.targetLowerCorner x q) (data.targetUpperCorner x q) := by
  simpa [targetLowerCorner, targetUpperCorner] using
    (data.selectedBoxImageConstructorDataOfOrientedManifold x hx q hq)
      |>.BoundaryChartSelectedBoxOrientationCovData

/-- Oriented-manifold COV projection for one active selected boundary-chart box. -/
theorem orientedChangeOfVariablesOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece)
    (x : Chart) (hx : x ∈ data.activeCharts)
    (q : Piece) (hq : q ∈ data.localPieces x) :
    boundaryChartOrientedChangeOfVariables I
      (data.sourceChart x q) (data.boundarySourceChart x q) ω
      (data.sourceLowerCorner x q) (data.sourceUpperCorner x q)
      (data.targetLowerCorner x q) (data.targetUpperCorner x q) :=
  (data.selectedBoxOrientationCovDataOfOrientedManifold
    x hx q hq).orientedChangeOfVariables

/--
Projection to the raw COV hypotheses for one active selected boundary-chart
box, with orientation data coming from global oriented-boundary-manifold data.
-/
theorem changeOfVariablesHypothesesOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece)
    (x : Chart) (hx : x ∈ data.activeCharts)
    (q : Piece) (hq : q ∈ data.localPieces x) :
    boundaryChartTransitionCompatibleOn I (data.sourceChart x q)
        (data.boundarySourceChart x q)
        (lowerZeroFaceDomain (data.sourceLowerCorner x q)
          (data.sourceUpperCorner x q)) ∧
      boundaryChartOrientationCompatibleOn I (data.sourceChart x q)
        (data.boundarySourceChart x q)
        (lowerZeroFaceDomain (data.sourceLowerCorner x q)
          (data.sourceUpperCorner x q)) ∧
        (∀ u ∈ lowerZeroFaceDomain (data.sourceLowerCorner x q)
            (data.sourceUpperCorner x q),
          HasFDerivWithinAt
            (boundaryChartTransition I (data.sourceChart x q)
              (data.boundarySourceChart x q))
            (boundaryChartTransitionTangentMap I (data.sourceChart x q)
              (data.boundarySourceChart x q) u)
            (lowerZeroFaceDomain (data.sourceLowerCorner x q)
              (data.sourceUpperCorner x q)) u) ∧
          Set.InjOn
            (boundaryChartTransition I (data.sourceChart x q)
              (data.boundarySourceChart x q))
            (lowerZeroFaceDomain (data.sourceLowerCorner x q)
              (data.sourceUpperCorner x q)) ∧
            (boundaryChartTransition I (data.sourceChart x q)
                (data.boundarySourceChart x q)) ''
                lowerZeroFaceDomain (data.sourceLowerCorner x q)
                  (data.sourceUpperCorner x q) =
              lowerZeroFaceDomain (data.targetLowerCorner x q)
                (data.targetUpperCorner x q) :=
  (data.selectedBoxOrientationCovDataOfOrientedManifold
    x hx q hq).changeOfVariablesHypotheses

/--
Build a COV family from an oriented boundary atlas and selected source/target
box data.
-/
def toChangeOfVariablesFamilyOfOrientedAtlas [IsManifold I 1 M]
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      ∀ x, x ∈ data.activeCharts →
        ∀ q, q ∈ data.localPieces x → data.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ data.activeCharts →
        ∀ q, q ∈ data.localPieces x → data.boundarySourceChart x q ∈ A.charts) :
    BoundaryChartChangeOfVariablesFamily I ω Chart Piece where
  activeCharts := data.activeCharts
  localPieces := data.localPieces
  sourceChart := data.sourceChart
  boundarySourceChart := data.boundarySourceChart
  boundaryTargetChart := data.boundaryTargetChart
  sourceLowerCorner := data.sourceLowerCorner
  sourceUpperCorner := data.sourceUpperCorner
  targetLowerCorner := data.targetLowerCorner
  targetUpperCorner := data.targetUpperCorner
  changeOfVariables := by
    intro x hx q hq
    exact
      data.orientedChangeOfVariablesOfOrientedAtlas A x hx q hq
        (hsource x hx q hq) (hboundarySource x hx q hq)
  targetSelectedBox := by
    intro x hx q hq
    exact data.targetSelectedBox x hx q hq

/--
Build a COV family from global oriented-boundary-manifold data and selected
source/target box data.
-/
def toChangeOfVariablesFamilyOfOrientedManifold [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M]
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece) :
    BoundaryChartChangeOfVariablesFamily I ω Chart Piece where
  activeCharts := data.activeCharts
  localPieces := data.localPieces
  sourceChart := data.sourceChart
  boundarySourceChart := data.boundarySourceChart
  boundaryTargetChart := data.boundaryTargetChart
  sourceLowerCorner := data.sourceLowerCorner
  sourceUpperCorner := data.sourceUpperCorner
  targetLowerCorner := data.targetLowerCorner
  targetUpperCorner := data.targetUpperCorner
  changeOfVariables := by
    intro x hx q hq
    exact data.orientedChangeOfVariablesOfOrientedManifold x hx q hq
  targetSelectedBox := by
    intro x hx q hq
    exact data.targetSelectedBox x hx q hq

end BoundaryChartSelectedBoxCOVFamilyData

/--
Top-level oriented-atlas wrapper from selected source boxes and target-box
selections to a finite boundary-chart COV family.
-/
def boundaryChartChangeOfVariablesFamily_of_orientedAtlas_selectedBox_targetBox
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] {ω : ManifoldForm I M n}
    {Chart : Type c} {Piece : Type p}
    (A : BoundaryChartOrientedAtlas I M)
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece)
    (hsource :
      ∀ x, x ∈ data.activeCharts →
        ∀ q, q ∈ data.localPieces x → data.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ data.activeCharts →
        ∀ q, q ∈ data.localPieces x → data.boundarySourceChart x q ∈ A.charts) :
    BoundaryChartChangeOfVariablesFamily I ω Chart Piece :=
  data.toChangeOfVariablesFamilyOfOrientedAtlas A hsource hboundarySource

/--
Top-level oriented-manifold wrapper from selected source boxes and target-box
selections to a finite boundary-chart COV family.
-/
def boundaryChartChangeOfVariablesFamily_of_orientedManifold_selectedBox_targetBox
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    {ω : ManifoldForm I M n} {Chart : Type c} {Piece : Type p}
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece) :
    BoundaryChartChangeOfVariablesFamily I ω Chart Piece :=
  data.toChangeOfVariablesFamilyOfOrientedManifold

end ManifoldBoundary

end Stokes

end
