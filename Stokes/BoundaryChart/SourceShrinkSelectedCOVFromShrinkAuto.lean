import Stokes.BoundaryChart.SourceShrinkSelectedCOVFacade
import Stokes.BoundaryChart.SelectedImageBoxContainmentFromShrinkAuto

/-!
# Source-shrink selected COV from shrink data

`SourceShrinkSelectedCOVFacade` reduces the boundary chart COV route to one
named geometric callback:
`boundaryChartSelectedTargetImageBoxContainedInFutureTargets`.
`SelectedImageBoxContainmentFromShrinkAuto` proves that callback from the
source-shrink target containment records used by the box-selection pipeline.

This file is the theorem-facing composition layer: callers can provide ambient
target containment, or its coordinatewise tangent-bound spelling, and get the
selected COV existence statement directly.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section ManifoldBoundary

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace BoundaryChartSourceShrinkInverseTargetBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d e f : Fin (n + 1) → Real} {u y : Fin n → Real}

/--
Completed source-shrink inverse-target data plus an ambient-target containment
record directly gives the local-openness selected COV route from oriented-atlas
data.  This is the shrink-data version of
`exists_selectedCOVOfTargetContainsOrientedAtlas`.
-/
theorem exists_selectedCOVOfAmbientContainsOrientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (himage :
      (boundaryChartTransition I x0 x1) ''
          lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner ∈ 𝓝 y)
    (hambient :
      BoundaryChartAmbientTargetContainsLaterTargets I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω
          D.sourceLowerCorner D.sourceUpperCorner
          T.targetLowerCorner T.targetUpperCorner :=
  (D.toSelectedImageBoxContainmentOfAmbientContainsLaterTargets
      hbox hambient).exists_orientedChangeOfVariables_of_localOpenness_orientedAtlas
    A hx0 hx1 himage

/--
Oriented-manifold spelling of
`exists_selectedCOVOfAmbientContainsOrientedAtlas`.
-/
theorem exists_selectedCOVOfAmbientContainsOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (himage :
      (boundaryChartTransition I x0 x1) ''
          lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner ∈ 𝓝 y)
    (hambient :
      BoundaryChartAmbientTargetContainsLaterTargets I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω
          D.sourceLowerCorner D.sourceUpperCorner
          T.targetLowerCorner T.targetUpperCorner :=
  (D.toSelectedImageBoxContainmentOfAmbientContainsLaterTargets
      hbox hambient).exists_orientedChangeOfVariables_of_localOpenness_orientedManifold
    himage

/--
Coordinatewise tangent-bound version of the inverse-target local-openness
selected COV route from oriented-atlas data.
-/
theorem exists_selectedCOVOfAmbientTangentBoundsOrientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
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
          T.targetLowerCorner T.targetUpperCorner :=
  (D.toSelectedImageBoxContainmentOfAmbientTangentBounds
      hbox hlower hupper).exists_orientedChangeOfVariables_of_localOpenness_orientedAtlas
    A hx0 hx1 himage

/--
Coordinatewise tangent-bound version of the inverse-target local-openness
selected COV route from global oriented-manifold data.
-/
theorem exists_selectedCOVOfAmbientTangentBoundsOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
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
          T.targetLowerCorner T.targetUpperCorner :=
  (D.toSelectedImageBoxContainmentOfAmbientTangentBounds
      hbox hlower hupper).exists_orientedChangeOfVariables_of_localOpenness_orientedManifold
    himage

end BoundaryChartSourceShrinkInverseTargetBoxData

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real} {u y : Fin n → Real}

/--
Open-partial-homeomorphism source-shrink data plus ambient-target containment
directly gives the local-openness selected COV route from oriented-atlas data.
The source-image neighborhood fact is derived from the synchronized
source-shrink record.
-/
theorem exists_selectedCOVOfAmbientContainsOrientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hambient :
      BoundaryChartAmbientTargetContainsLaterTargets I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω
          D.sourceLowerCorner D.sourceUpperCorner
          T.targetLowerCorner T.targetUpperCorner :=
  (D.toSelectedImageBoxContainmentOfAmbientContainsLaterTargets
      hbox hambient).exists_orientedChangeOfVariables_of_localOpenness_orientedAtlas
    A hx0 hx1 D.sourceImage_mem_nhds_targetPoint

/--
Oriented-manifold spelling of
`exists_selectedCOVOfAmbientContainsOrientedAtlas`.
-/
theorem exists_selectedCOVOfAmbientContainsOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (hambient :
      BoundaryChartAmbientTargetContainsLaterTargets I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω
          D.sourceLowerCorner D.sourceUpperCorner
          T.targetLowerCorner T.targetUpperCorner :=
  (D.toSelectedImageBoxContainmentOfAmbientContainsLaterTargets
      hbox hambient).exists_orientedChangeOfVariables_of_localOpenness_orientedManifold
    D.sourceImage_mem_nhds_targetPoint

/--
Coordinatewise tangent-bound version of the open-partial-homeomorphism selected
COV route from oriented-atlas data.
-/
theorem exists_selectedCOVOfAmbientTangentBoundsOrientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
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
          T.targetLowerCorner T.targetUpperCorner :=
  (D.toSelectedImageBoxContainmentOfAmbientTangentBounds
      hbox hlower hupper).exists_orientedChangeOfVariables_of_localOpenness_orientedAtlas
    A hx0 hx1 D.sourceImage_mem_nhds_targetPoint

/--
Coordinatewise tangent-bound version of the open-partial-homeomorphism selected
COV route from global oriented-manifold data.
-/
theorem exists_selectedCOVOfAmbientTangentBoundsOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
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
          T.targetLowerCorner T.targetUpperCorner :=
  (D.toSelectedImageBoxContainmentOfAmbientTangentBounds
      hbox hlower hupper).exists_orientedChangeOfVariables_of_localOpenness_orientedManifold
    D.sourceImage_mem_nhds_targetPoint

end BoundaryChartSourceShrinkOpenPartialHomeomorphData

end ManifoldBoundary

end Stokes

end
