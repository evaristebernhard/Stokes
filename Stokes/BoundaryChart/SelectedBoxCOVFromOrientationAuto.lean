import Stokes.BoundaryChart.ChangeOfVariables
import Stokes.BoundaryChart.TargetBoxSourceShrinkIFT
import Stokes.BoundaryChart.TargetImageSelectedBoxBuilder

/-!
# Selected-box COV from automatic orientation and target-image data

This file is an endpoint layer for the current boundary-chart pipeline.  It
turns selected source boxes, oriented-atlas/manifold data, and the target-image
packages produced by local inverse / source-shrink constructions directly into
`boundaryChartOrientedChangeOfVariables`.

The integral equality is still supplied by the mathlib change-of-variables route
in `ChangeOfVariables.lean`; the theorems here only discharge its derivative,
orientation, injectivity, and image-data hypotheses from the selected-box APIs.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section ManifoldBoundary

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace BoundaryChartSelectedBoxTargetImageAutoData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/--
Selected-box target-image auto data plus oriented-atlas membership gives the
oriented boundary chart change-of-variables package.
-/
theorem orientedChangeOfVariablesOfOrientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b)
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
      D.targetLowerCorner D.targetUpperCorner :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedAtlas_imageData
    A hx0 hx1 ω a b D.targetLowerCorner D.targetUpperCorner
    D.selectedBox D.imageData

/--
Selected-box target-image auto data plus global oriented-boundary-manifold data
gives the oriented boundary chart change-of-variables package.
-/
theorem orientedChangeOfVariablesOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
      D.targetLowerCorner D.targetUpperCorner :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedManifold_imageData
    x0 x1 ω a b D.targetLowerCorner D.targetUpperCorner
    D.selectedBox D.imageData

end BoundaryChartSelectedBoxTargetImageAutoData

namespace BoundaryChartSelectedBoxLocalInverseAutoInputs

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/--
Local-inverse target selection plus oriented-atlas data selects a target box and
immediately proves the oriented boundary chart COV statement for it.
-/
theorem exists_orientedChangeOfVariablesOfOrientedAtlas
    [IsManifold I 1 M]
    (T : BoundaryChartSelectedBoxLocalInverseAutoInputs I x0 x1 ω a b)
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts) :
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      T.targetPoint ∈ lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          D.targetLowerCorner D.targetUpperCorner := by
  rcases T.exists_autoData with ⟨D, hmem, _himage⟩
  exact ⟨D, hmem, D.orientedChangeOfVariablesOfOrientedAtlas A hx0 hx1⟩

/--
Local-inverse target selection plus global oriented-boundary-manifold data
selects a target box and immediately proves the oriented boundary chart COV
statement for it.
-/
theorem exists_orientedChangeOfVariablesOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (T : BoundaryChartSelectedBoxLocalInverseAutoInputs I x0 x1 ω a b) :
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      T.targetPoint ∈ lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          D.targetLowerCorner D.targetUpperCorner := by
  rcases T.exists_autoData with ⟨D, hmem, _himage⟩
  exact ⟨D, hmem, D.orientedChangeOfVariablesOfOrientedManifold⟩

end BoundaryChartSelectedBoxLocalInverseAutoInputs

namespace BoundaryChartSelectedBoxPointAutoInputs

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/--
Pointwise oriented-atlas local-inverse construction, followed all the way to
the oriented boundary chart COV statement for the selected target box.
-/
theorem exists_orientedChangeOfVariablesOfOrientedAtlas
    [IsManifold I ⊤ M]
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (T : BoundaryChartSelectedBoxPointAutoInputs I x0 x1 ω a b) :
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      T.targetPoint ∈ lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          D.targetLowerCorner D.targetUpperCorner := by
  rcases T.exists_autoData_of_orientedAtlas A hx0 hx1 with ⟨D, hmem, _himage⟩
  exact ⟨D, hmem, D.orientedChangeOfVariablesOfOrientedAtlas A hx0 hx1⟩

/--
Pointwise oriented-manifold local-inverse construction, followed all the way to
the oriented boundary chart COV statement for the selected target box.
-/
theorem exists_orientedChangeOfVariablesOfOrientedManifold
    [IsManifold I ⊤ M] [BoundaryChartOrientedManifold I M]
    (T : BoundaryChartSelectedBoxPointAutoInputs I x0 x1 ω a b) :
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      T.targetPoint ∈ lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          D.targetLowerCorner D.targetUpperCorner := by
  rcases T.exists_autoData_of_orientedManifold with ⟨D, hmem, _himage⟩
  exact ⟨D, hmem, D.orientedChangeOfVariablesOfOrientedManifold⟩

end BoundaryChartSelectedBoxPointAutoInputs

namespace BoundaryChartSourceShrinkMapsToData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d e f : Fin (n + 1) → Real} {u y : Fin n → Real}

/--
Source-shrink maps-to data plus a continuous local inverse gives oriented COV
for the shrunken source and target boxes, using oriented-atlas data for
orientation and compatibility.
-/
theorem orientedChangeOfVariablesOfContinuousLocalInverseOfOrientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b e f u)
    (he0 : e 0 = 0) (hle : e ≤ f)
    (hy : y ∈ lowerZeroFaceDomain e f)
    (hsubset : lowerZeroFaceDomain e f ⊆ lowerZeroFaceDomain c d)
    (G :
      BoundaryChartContinuousLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner e f y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner e f :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedAtlas_imageData
    A hx0 hx1 ω D.sourceLowerCorner D.sourceUpperCorner e f hbox
    (D.imageData_of_continuousLocalInverse he0 hle hy hsubset G)

/--
Source-shrink maps-to data plus a continuous local inverse gives oriented COV
for the shrunken source and target boxes, using global oriented-manifold data.
-/
theorem orientedChangeOfVariablesOfContinuousLocalInverseOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b e f u)
    (he0 : e 0 = 0) (hle : e ≤ f)
    (hy : y ∈ lowerZeroFaceDomain e f)
    (hsubset : lowerZeroFaceDomain e f ⊆ lowerZeroFaceDomain c d)
    (G :
      BoundaryChartContinuousLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner e f y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner e f :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedManifold_imageData
    x0 x1 ω D.sourceLowerCorner D.sourceUpperCorner e f hbox
    (D.imageData_of_continuousLocalInverse he0 hle hy hsubset G)

end BoundaryChartSourceShrinkMapsToData

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real} {u y : Fin n → Real}

/--
Synchronized source-shrink local-homeomorphism data gives oriented COV for the
selected shrunken source and target boxes, using oriented-atlas data.
-/
theorem orientedChangeOfVariablesOfOrientedAtlas
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
  boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedAtlas_imageData
    A hx0 hx1 ω D.sourceLowerCorner D.sourceUpperCorner
    D.targetLowerCorner D.targetUpperCorner hbox D.imageData

/--
Synchronized source-shrink local-homeomorphism data gives oriented COV for the
selected shrunken source and target boxes, using global oriented-manifold data.
-/
theorem orientedChangeOfVariablesOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner
      D.targetLowerCorner D.targetUpperCorner :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedManifold_imageData
    x0 x1 ω D.sourceLowerCorner D.sourceUpperCorner
    D.targetLowerCorner D.targetUpperCorner hbox D.imageData

end BoundaryChartSourceShrinkOpenPartialHomeomorphData

end ManifoldBoundary

end Stokes

end
