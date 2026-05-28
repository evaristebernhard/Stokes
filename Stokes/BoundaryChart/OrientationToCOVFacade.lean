import Stokes.BoundaryChart.BoundaryChartCOVFacade
import Stokes.BoundaryChart.OrientedAtlasFromMathlib

/-!
# Orientation-to-COV facade

This file is a theorem-facing bridge from the current orientation records to
the boundary-chart change-of-variables facade.

The boundary COV layer already consumes either a project-local
`BoundaryChartOrientedAtlas` plus chart-membership proofs, or a typeclass
`BoundaryChartOrientedManifold`.  The declarations here remove one more layer
of glue for callers working with the mathlib-facing orientation records:

* atlas-level records are projected to `BoundaryChartOrientedAtlas`;
* all-chart manifold records are installed as a local
  `BoundaryChartOrientedManifold` instance;
* selected-box and source-shrink COV routes can then be called directly.

No upstream mathlib oriented-manifold theorem is assumed here.  The remaining
honest bridge is still the construction of `BoundaryChartMathlibOrientation...`
or `BoundaryChartMathlibOriented...` data from a future upstream API.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section ManifoldBoundary

universe u v w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace BoundaryChartSelectedBoxTargetImageAutoData

variable {𝓞 : Type v}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/-- Selected target-image data plus mathlib-orientation atlas data gives the
selected-box COV statement.  The only remaining atlas-specific inputs are the
two chart-membership proofs. -/
theorem orientedChangeOfVariablesOfMathlibOrientationAtlasData
    [IsManifold I 1 M]
    (T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b)
    (O : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (hx0 : x0 ∈ O.charts) (hx1 : x1 ∈ O.charts) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
      T.targetLowerCorner T.targetUpperCorner :=
  T.orientedChangeOfVariablesOfOrientedAtlas O.toBoundaryChartOrientedAtlas
    (by simpa using hx0) (by simpa using hx1)

/-- Selected target-image data plus the older mathlib-facing atlas bridge gives
the selected-box COV statement. -/
theorem orientedChangeOfVariablesOfMathlibOrientedAtlasBridge
    [IsManifold I 1 M]
    (T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b)
    (O : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (hx0 : x0 ∈ O.charts) (hx1 : x1 ∈ O.charts) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
      T.targetLowerCorner T.targetUpperCorner :=
  T.orientedChangeOfVariablesOfOrientedAtlas O.toBoundaryChartOrientedAtlas
    (by simpa using hx0) (by simpa using hx1)

/-- All-chart mathlib-orientation manifold data can be used directly as the
orientation input for selected-box COV. -/
theorem orientedChangeOfVariablesOfMathlibOrientationManifoldData
    [IsManifold I 1 M]
    (T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b)
    (O : BoundaryChartMathlibOrientationManifoldData I M 𝓞) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
      T.targetLowerCorner T.targetUpperCorner := by
  letI : BoundaryChartOrientedManifold I M := O.toBoundaryChartOrientedManifold
  exact T.orientedChangeOfVariablesOfOrientedManifold

/-- Older all-chart mathlib-facing manifold bridges can likewise be installed
as local project orientation data for selected-box COV. -/
theorem orientedChangeOfVariablesOfMathlibOrientedManifoldBridge
    [IsManifold I 1 M]
    (T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b)
    (O : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
      T.targetLowerCorner T.targetUpperCorner := by
  letI : BoundaryChartOrientedManifold I M := O.toBoundaryChartOrientedManifold
  exact T.orientedChangeOfVariablesOfOrientedManifold

end BoundaryChartSelectedBoxTargetImageAutoData

namespace BoundaryChartSelectedImageBoxContainment

variable {𝓞 : Type v}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {y : Fin n → Real}

/-- Local-openness selected-image containment route with mathlib-orientation
atlas data. -/
theorem exists_orientedChangeOfVariablesOfMathlibOrientationAtlasData
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y)
    (O : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (hx0 : x0 ∈ O.charts) (hx1 : x1 ∈ O.charts)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner :=
  D.exists_orientedChangeOfVariables_of_localOpenness_orientedAtlas
    O.toBoundaryChartOrientedAtlas (by simpa using hx0) (by simpa using hx1)
    himage

/-- Local-openness selected-image containment route with the older
mathlib-facing atlas bridge. -/
theorem exists_orientedChangeOfVariablesOfMathlibOrientedAtlasBridge
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y)
    (O : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (hx0 : x0 ∈ O.charts) (hx1 : x1 ∈ O.charts)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner :=
  D.exists_orientedChangeOfVariables_of_localOpenness_orientedAtlas
    O.toBoundaryChartOrientedAtlas (by simpa using hx0) (by simpa using hx1)
    himage

/-- Local-openness selected-image containment route with all-chart
mathlib-orientation manifold data. -/
theorem exists_orientedChangeOfVariablesOfMathlibOrientationManifoldData
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y)
    (O : BoundaryChartMathlibOrientationManifoldData I M 𝓞)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner := by
  letI : BoundaryChartOrientedManifold I M := O.toBoundaryChartOrientedManifold
  exact D.exists_orientedChangeOfVariables_of_localOpenness_orientedManifold
    himage

/-- Local-openness selected-image containment route with the older all-chart
mathlib-facing manifold bridge. -/
theorem exists_orientedChangeOfVariablesOfMathlibOrientedManifoldBridge
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y)
    (O : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner := by
  letI : BoundaryChartOrientedManifold I M := O.toBoundaryChartOrientedManifold
  exact D.exists_orientedChangeOfVariables_of_localOpenness_orientedManifold
    himage

end BoundaryChartSelectedImageBoxContainment

namespace BoundaryChartSourceShrinkInverseTargetBoxData

variable {𝓞 : Type v}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d e f : Fin (n + 1) → Real} {u y : Fin n → Real}

/-- Completed source-shrink inverse-target data plus mathlib-orientation atlas
data gives COV for the selected source and selected target. -/
theorem selectedCOVOfMathlibOrientationAtlasData
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (O : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (hx0 : x0 ∈ O.charts) (hx1 : x1 ∈ O.charts) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner e f :=
  D.selectedCOVOfOrientedAtlas hbox O.toBoundaryChartOrientedAtlas
    (by simpa using hx0) (by simpa using hx1)

/-- Completed source-shrink inverse-target data plus the older mathlib-facing
atlas bridge gives COV for the selected source and selected target. -/
theorem selectedCOVOfMathlibOrientedAtlasBridge
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (O : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (hx0 : x0 ∈ O.charts) (hx1 : x1 ∈ O.charts) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner e f :=
  D.selectedCOVOfOrientedAtlas hbox O.toBoundaryChartOrientedAtlas
    (by simpa using hx0) (by simpa using hx1)

/-- All-chart mathlib-orientation manifold data as the orientation input for
completed source-shrink inverse-target COV. -/
theorem selectedCOVOfMathlibOrientationManifoldData
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (O : BoundaryChartMathlibOrientationManifoldData I M 𝓞) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner e f := by
  letI : BoundaryChartOrientedManifold I M := O.toBoundaryChartOrientedManifold
  exact D.selectedCOVOfOrientedManifold hbox

/-- Older all-chart mathlib-facing manifold bridge as the orientation input for
completed source-shrink inverse-target COV. -/
theorem selectedCOVOfMathlibOrientedManifoldBridge
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (O : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner e f := by
  letI : BoundaryChartOrientedManifold I M := O.toBoundaryChartOrientedManifold
  exact D.selectedCOVOfOrientedManifold hbox

/-- Local-openness selected COV from source-shrink inverse-target data, ambient
tangent shrink, and all-chart mathlib-orientation manifold data. -/
theorem exists_selectedCOVOfAmbientTangentBoundsMathlibOrientationManifoldData
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (O : BoundaryChartMathlibOrientationManifoldData I M 𝓞)
    (himage :
      (boundaryChartTransition I x0 x1) ''
          lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner ∈ 𝓝 y)
    (hlower :
      ∀ c' d' : Fin (n + 1) → Real, c' 0 = 0 → c' ≤ d' →
        y ∈ lowerZeroFaceDomain c' d' →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner c' d' →
            ∀ i : Fin n, c' i.succ ≤ c i.succ)
    (hupper :
      ∀ c' d' : Fin (n + 1) → Real, c' 0 = 0 → c' ≤ d' →
        y ∈ lowerZeroFaceDomain c' d' →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner c' d' →
            ∀ i : Fin n, d i.succ ≤ d' i.succ) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω
          D.sourceLowerCorner D.sourceUpperCorner
          T.targetLowerCorner T.targetUpperCorner := by
  letI : BoundaryChartOrientedManifold I M := O.toBoundaryChartOrientedManifold
  exact D.exists_selectedCOVOfAmbientTangentBoundsOrientedManifold
    hbox himage hlower hupper

/-- Same source-shrink local-openness route using the older all-chart
mathlib-facing manifold bridge. -/
theorem exists_selectedCOVOfAmbientTangentBoundsMathlibOrientedManifoldBridge
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (O : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞)
    (himage :
      (boundaryChartTransition I x0 x1) ''
          lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner ∈ 𝓝 y)
    (hlower :
      ∀ c' d' : Fin (n + 1) → Real, c' 0 = 0 → c' ≤ d' →
        y ∈ lowerZeroFaceDomain c' d' →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner c' d' →
            ∀ i : Fin n, c' i.succ ≤ c i.succ)
    (hupper :
      ∀ c' d' : Fin (n + 1) → Real, c' 0 = 0 → c' ≤ d' →
        y ∈ lowerZeroFaceDomain c' d' →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner c' d' →
            ∀ i : Fin n, d i.succ ≤ d' i.succ) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω
          D.sourceLowerCorner D.sourceUpperCorner
          T.targetLowerCorner T.targetUpperCorner := by
  letI : BoundaryChartOrientedManifold I M := O.toBoundaryChartOrientedManifold
  exact D.exists_selectedCOVOfAmbientTangentBoundsOrientedManifold
    hbox himage hlower hupper

end BoundaryChartSourceShrinkInverseTargetBoxData

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphData

variable {𝓞 : Type v}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real} {u y : Fin n → Real}

/-- Synchronized source-shrink local-homeomorphism data plus
mathlib-orientation atlas data gives COV for the selected source and target. -/
theorem selectedCOVOfMathlibOrientationAtlasData
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (O : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (hx0 : x0 ∈ O.charts) (hx1 : x1 ∈ O.charts) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner
      D.targetLowerCorner D.targetUpperCorner :=
  D.selectedCOVOfOrientedAtlas hbox O.toBoundaryChartOrientedAtlas
    (by simpa using hx0) (by simpa using hx1)

/-- Synchronized source-shrink local-homeomorphism data plus the older
mathlib-facing atlas bridge gives COV for the selected source and target. -/
theorem selectedCOVOfMathlibOrientedAtlasBridge
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (O : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (hx0 : x0 ∈ O.charts) (hx1 : x1 ∈ O.charts) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner
      D.targetLowerCorner D.targetUpperCorner :=
  D.selectedCOVOfOrientedAtlas hbox O.toBoundaryChartOrientedAtlas
    (by simpa using hx0) (by simpa using hx1)

/-- All-chart mathlib-orientation manifold data as the orientation input for
synchronized source-shrink local-homeomorphism COV. -/
theorem selectedCOVOfMathlibOrientationManifoldData
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (O : BoundaryChartMathlibOrientationManifoldData I M 𝓞) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner
      D.targetLowerCorner D.targetUpperCorner := by
  letI : BoundaryChartOrientedManifold I M := O.toBoundaryChartOrientedManifold
  exact D.selectedCOVOfOrientedManifold hbox

/-- Older all-chart mathlib-facing manifold bridge as the orientation input for
synchronized source-shrink local-homeomorphism COV. -/
theorem selectedCOVOfMathlibOrientedManifoldBridge
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (O : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner
      D.targetLowerCorner D.targetUpperCorner := by
  letI : BoundaryChartOrientedManifold I M := O.toBoundaryChartOrientedManifold
  exact D.selectedCOVOfOrientedManifold hbox

/-- Local-openness selected COV from synchronized source-shrink data, ambient
tangent shrink, and all-chart mathlib-orientation manifold data. -/
theorem exists_selectedCOVOfAmbientTangentBoundsMathlibOrientationManifoldData
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (O : BoundaryChartMathlibOrientationManifoldData I M 𝓞)
    (hlower :
      ∀ c' d' : Fin (n + 1) → Real, c' 0 = 0 → c' ≤ d' →
        y ∈ lowerZeroFaceDomain c' d' →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner c' d' →
            ∀ i : Fin n, c' i.succ ≤ c i.succ)
    (hupper :
      ∀ c' d' : Fin (n + 1) → Real, c' 0 = 0 → c' ≤ d' →
        y ∈ lowerZeroFaceDomain c' d' →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner c' d' →
            ∀ i : Fin n, d i.succ ≤ d' i.succ) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω
          D.sourceLowerCorner D.sourceUpperCorner
          T.targetLowerCorner T.targetUpperCorner := by
  letI : BoundaryChartOrientedManifold I M := O.toBoundaryChartOrientedManifold
  exact D.exists_selectedCOVOfAmbientTangentBoundsOrientedManifold
    hbox hlower hupper

/-- Same synchronized source-shrink local-openness route using the older
all-chart mathlib-facing manifold bridge. -/
theorem exists_selectedCOVOfAmbientTangentBoundsMathlibOrientedManifoldBridge
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (O : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞)
    (hlower :
      ∀ c' d' : Fin (n + 1) → Real, c' 0 = 0 → c' ≤ d' →
        y ∈ lowerZeroFaceDomain c' d' →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner c' d' →
            ∀ i : Fin n, c' i.succ ≤ c i.succ)
    (hupper :
      ∀ c' d' : Fin (n + 1) → Real, c' 0 = 0 → c' ≤ d' →
        y ∈ lowerZeroFaceDomain c' d' →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner c' d' →
            ∀ i : Fin n, d i.succ ≤ d' i.succ) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω
          D.sourceLowerCorner D.sourceUpperCorner
          T.targetLowerCorner T.targetUpperCorner := by
  letI : BoundaryChartOrientedManifold I M := O.toBoundaryChartOrientedManifold
  exact D.exists_selectedCOVOfAmbientTangentBoundsOrientedManifold
    hbox hlower hupper

end BoundaryChartSourceShrinkOpenPartialHomeomorphData

end ManifoldBoundary

end Stokes

end
