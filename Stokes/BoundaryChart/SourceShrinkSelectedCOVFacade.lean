import Stokes.BoundaryChart.SourceShrinkMapsToAuto
import Stokes.BoundaryChart.SelectedImageBoxFromTargetAuto

/-!
# Source-shrink facade for selected boundary-chart COV

The source-shrink boundary-chart route now has several small automation layers:
maps-to data, selected image boxes, target-box containment, local-openness/IFT
target selection, and orientation.  This facade gives theorem-facing entry
points that keep those intermediate records out of callers.

The remaining honest geometric input is named as one predicate:
the selected target image box must lie in every later local-inverse target box.
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

/--
The last geometric box-containment hypothesis in the source-shrink facade:
the already selected target image box is contained in every later target box
on which the local inverse is used.

This is the named replacement for the longer `hcontains` callbacks that appear
in lower-level selected-image-box APIs.
-/
def boundaryChartSelectedTargetImageBoxContainedInFutureTargets {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M)
    (a b targetLower targetUpper : Fin (n + 1) → Real)
    (y : Fin n → Real) : Prop :=
  ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
    y ∈ lowerZeroFaceDomain c d →
      boundaryChartLocalInverseData I x0 x1 a b c d →
        Set.Icc (boundaryFaceLowerCorner targetLower)
            (boundaryFaceUpperCorner targetUpper) ⊆
          Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)

namespace BoundaryChartSourceShrinkInverseTargetBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d e f : Fin (n + 1) → Real} {u y : Fin n → Real}

/--
Facade: completed source-shrink inverse-target data plus a selected source box
directly gives oriented boundary-chart COV from oriented-atlas membership.
-/
theorem selectedCOVOfOrientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner e f :=
  D.orientedChangeOfVariablesOfOrientedAtlas hbox A hx0 hx1

/--
Facade: completed source-shrink inverse-target data plus a selected source box
directly gives oriented boundary-chart COV from global oriented-manifold data.
-/
theorem selectedCOVOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner e f :=
  D.orientedChangeOfVariablesOfOrientedManifold hbox

/--
Facade for the local-openness target-selector route.  The caller supplies the
completed source-shrink inverse data, a selected source box, local-openness of
the selected source image at `y`, and the single named future-target containment
hypothesis.
-/
theorem exists_selectedCOVOfTargetContainsOrientedAtlas
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
    (hgeometry :
      boundaryChartSelectedTargetImageBoxContainedInFutureTargets I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner e f y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω
          D.sourceLowerCorner D.sourceUpperCorner
          T.targetLowerCorner T.targetUpperCorner :=
  (D.toSelectedImageBoxContainmentOfTargetContains hbox hgeometry).exists_orientedChangeOfVariables_of_localOpenness_orientedAtlas
    A hx0 hx1 himage

/--
Oriented-manifold spelling of
`exists_selectedCOVOfTargetContainsOrientedAtlas`.
-/
theorem exists_selectedCOVOfTargetContainsOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (himage :
      (boundaryChartTransition I x0 x1) ''
          lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner ∈ 𝓝 y)
    (hgeometry :
      boundaryChartSelectedTargetImageBoxContainedInFutureTargets I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner e f y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω
          D.sourceLowerCorner D.sourceUpperCorner
          T.targetLowerCorner T.targetUpperCorner :=
  (D.toSelectedImageBoxContainmentOfTargetContains hbox hgeometry).exists_orientedChangeOfVariables_of_localOpenness_orientedManifold
    himage

end BoundaryChartSourceShrinkInverseTargetBoxData

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real} {u y : Fin n → Real}

/--
The synchronized local-homeomorphism source-shrink data already proves that the
selected source image is a neighborhood of its target point: the selected target
box is a neighborhood, and image data gives surjectivity onto that target box.
-/
theorem sourceImage_mem_nhds_targetPoint
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y) :
    (boundaryChartTransition I x0 x1) ''
        lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner ∈ 𝓝 y := by
  refine mem_of_superset D.target_mem_nhds ?_
  intro z hz
  rcases D.imageData_surjOn hz with ⟨v, hv, hvz⟩
  exact ⟨v, hv, hvz⟩

/--
Facade: synchronized source-shrink local-homeomorphism data plus a selected
source box directly gives oriented boundary-chart COV from oriented-atlas
membership.
-/
theorem selectedCOVOfOrientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner
      D.targetLowerCorner D.targetUpperCorner :=
  D.orientedChangeOfVariablesOfOrientedAtlas hbox A hx0 hx1

/--
Facade: synchronized source-shrink local-homeomorphism data plus a selected
source box directly gives oriented boundary-chart COV from global
oriented-manifold data.
-/
theorem selectedCOVOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner
      D.targetLowerCorner D.targetUpperCorner :=
  D.orientedChangeOfVariablesOfOrientedManifold hbox

/--
Facade for the local-openness target-selector route from synchronized
local-homeomorphism data.  Unlike the inverse-target-box version, the
local-openness neighborhood fact is derived from `D`, so the only remaining
geometric input is the final future-target containment hypothesis.
-/
theorem exists_selectedCOVOfTargetContainsOrientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hgeometry :
      boundaryChartSelectedTargetImageBoxContainedInFutureTargets I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner
        D.targetLowerCorner D.targetUpperCorner y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω
          D.sourceLowerCorner D.sourceUpperCorner
          T.targetLowerCorner T.targetUpperCorner :=
  (D.toSelectedImageBoxContainmentOfTargetContains hbox hgeometry).exists_orientedChangeOfVariables_of_localOpenness_orientedAtlas
    A hx0 hx1 D.sourceImage_mem_nhds_targetPoint

/--
Oriented-manifold spelling of
`exists_selectedCOVOfTargetContainsOrientedAtlas`.
-/
theorem exists_selectedCOVOfTargetContainsOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (hgeometry :
      boundaryChartSelectedTargetImageBoxContainedInFutureTargets I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner
        D.targetLowerCorner D.targetUpperCorner y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω
          D.sourceLowerCorner D.sourceUpperCorner
          T.targetLowerCorner T.targetUpperCorner :=
  (D.toSelectedImageBoxContainmentOfTargetContains hbox hgeometry).exists_orientedChangeOfVariables_of_localOpenness_orientedManifold
    D.sourceImage_mem_nhds_targetPoint

end BoundaryChartSourceShrinkOpenPartialHomeomorphData

end ManifoldBoundary

end Stokes

end
