import Stokes.BoundaryChart.OrientationToCOVFacade

/-!
# Orientation atlas membership automation

Atlas-level boundary-chart COV routes need two small membership proofs:
the source chart and the boundary-source chart must belong to the oriented
atlas.  This file packages those two proofs and threads the package through the
main selected-box/source-shrink COV facades.

This is deliberately a `BoundaryChart`-level wrapper.  It does not import the
global M8 membership constructors; global code can project its resolved
membership data into this two-chart record when it calls the local COV route.
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

/--
The two atlas-membership facts needed by an atlas-level boundary chart COV
statement.

`source_mem` is for the source chart center `x0`; `boundarySource_mem` is for
the target/boundary-source chart center `x1`.
-/
structure BoundaryChartOrientationMembership
    (charts : Set M) (x0 x1 : M) where
  /-- The source chart center belongs to the oriented atlas. -/
  source_mem : x0 ∈ charts
  /-- The boundary-source chart center belongs to the oriented atlas. -/
  boundarySource_mem : x1 ∈ charts

namespace BoundaryChartOrientationMembership

variable {charts : Set M} {x0 x1 : M}

/-- Constructor from the two raw membership proofs. -/
def of_mem (hx0 : x0 ∈ charts) (hx1 : x1 ∈ charts) :
    BoundaryChartOrientationMembership charts x0 x1 where
  source_mem := hx0
  boundarySource_mem := hx1

/-- All-chart atlas membership, used by all-chart orientation data. -/
def of_univ (x0 x1 : M) :
    BoundaryChartOrientationMembership (univ : Set M) x0 x1 where
  source_mem := mem_univ x0
  boundarySource_mem := mem_univ x1

@[simp]
theorem source_mem_of_mem (hx0 : x0 ∈ charts) (hx1 : x1 ∈ charts) :
    (of_mem (charts := charts) (x0 := x0) (x1 := x1) hx0 hx1).source_mem =
      hx0 := by
  rfl

@[simp]
theorem boundarySource_mem_of_mem (hx0 : x0 ∈ charts) (hx1 : x1 ∈ charts) :
    (of_mem (charts := charts) (x0 := x0) (x1 := x1) hx0 hx1).boundarySource_mem =
      hx1 := by
  rfl

@[simp]
theorem source_mem_of_univ (x0 x1 : M) :
    (of_univ x0 x1).source_mem = mem_univ x0 := by
  rfl

@[simp]
theorem boundarySource_mem_of_univ (x0 x1 : M) :
    (of_univ x0 x1).boundarySource_mem = mem_univ x1 := by
  rfl

end BoundaryChartOrientationMembership

namespace BoundaryChartMathlibOrientationAtlasData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {𝓞 : Type v}
variable {x0 x1 : M}

/-- Package atlas membership for mathlib-orientation atlas data. -/
def orientationMembership
    (O : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (hx0 : x0 ∈ O.charts) (hx1 : x1 ∈ O.charts) :
    BoundaryChartOrientationMembership O.charts x0 x1 :=
  BoundaryChartOrientationMembership.of_mem hx0 hx1

/-- Source membership after forgetting mathlib-orientation data to the local atlas. -/
theorem orientationMembership_source_toBoundaryChartOrientedAtlas
    (O : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (m : BoundaryChartOrientationMembership O.charts x0 x1) :
    x0 ∈ O.toBoundaryChartOrientedAtlas.charts := by
  simpa using m.source_mem

/-- Boundary-source membership after forgetting mathlib-orientation data to the local atlas. -/
theorem orientationMembership_boundarySource_toBoundaryChartOrientedAtlas
    (O : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (m : BoundaryChartOrientationMembership O.charts x0 x1) :
    x1 ∈ O.toBoundaryChartOrientedAtlas.charts := by
  simpa using m.boundarySource_mem

end BoundaryChartMathlibOrientationAtlasData

namespace BoundaryChartMathlibOrientationManifoldData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {𝓞 : Type v}

/-- All-chart mathlib-orientation manifold data gives membership for every chart pair. -/
def orientationMembership
    (O : BoundaryChartMathlibOrientationManifoldData I M 𝓞)
    (x0 x1 : M) :
    BoundaryChartOrientationMembership O.toBoundaryChartOrientedAtlas.charts x0 x1 where
  source_mem := by
    simp
  boundarySource_mem := by
    simp

end BoundaryChartMathlibOrientationManifoldData

namespace BoundaryChartMathlibOrientedAtlasBridge

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {𝓞 : Type v}
variable {x0 x1 : M}

/-- Package atlas membership for the older mathlib-facing atlas bridge. -/
def orientationMembership
    (O : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (hx0 : x0 ∈ O.charts) (hx1 : x1 ∈ O.charts) :
    BoundaryChartOrientationMembership O.charts x0 x1 :=
  BoundaryChartOrientationMembership.of_mem hx0 hx1

/-- Source membership after forgetting the bridge to the local atlas. -/
theorem orientationMembership_source_toBoundaryChartOrientedAtlas
    (O : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (m : BoundaryChartOrientationMembership O.charts x0 x1) :
    x0 ∈ O.toBoundaryChartOrientedAtlas.charts := by
  simpa using m.source_mem

/-- Boundary-source membership after forgetting the bridge to the local atlas. -/
theorem orientationMembership_boundarySource_toBoundaryChartOrientedAtlas
    (O : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (m : BoundaryChartOrientationMembership O.charts x0 x1) :
    x1 ∈ O.toBoundaryChartOrientedAtlas.charts := by
  simpa using m.boundarySource_mem

end BoundaryChartMathlibOrientedAtlasBridge

namespace BoundaryChartMathlibOrientedManifoldBridge

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {𝓞 : Type v}

/-- All-chart mathlib-facing manifold bridge gives membership for every chart pair. -/
def orientationMembership
    (O : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞)
    (x0 x1 : M) :
    BoundaryChartOrientationMembership O.toMathlibOrientedAtlasBridge.charts x0 x1 where
  source_mem := by
    simp
  boundarySource_mem := by
    simp

end BoundaryChartMathlibOrientedManifoldBridge

namespace BoundaryChartSelectedBoxTargetImageAutoData

variable {𝓞 : Type v}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/-- Selected target-image COV using a bundled atlas-membership pair. -/
theorem orientedChangeOfVariablesOfOrientationMembership
    [IsManifold I 1 M]
    (T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b)
    (A : BoundaryChartOrientedAtlas I M)
    (m : BoundaryChartOrientationMembership A.charts x0 x1) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
      T.targetLowerCorner T.targetUpperCorner :=
  T.orientedChangeOfVariablesOfOrientedAtlas A m.source_mem m.boundarySource_mem

/-- Mathlib-orientation atlas data plus bundled membership gives selected-box COV. -/
theorem orientedChangeOfVariablesOfMathlibOrientationAtlasMembership
    [IsManifold I 1 M]
    (T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b)
    (O : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (m : BoundaryChartOrientationMembership O.charts x0 x1) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
      T.targetLowerCorner T.targetUpperCorner :=
  T.orientedChangeOfVariablesOfMathlibOrientationAtlasData
    O m.source_mem m.boundarySource_mem

/-- Older mathlib-facing atlas bridge plus bundled membership gives selected-box COV. -/
theorem orientedChangeOfVariablesOfMathlibOrientedAtlasMembership
    [IsManifold I 1 M]
    (T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b)
    (O : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (m : BoundaryChartOrientationMembership O.charts x0 x1) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
      T.targetLowerCorner T.targetUpperCorner :=
  T.orientedChangeOfVariablesOfMathlibOrientedAtlasBridge
    O m.source_mem m.boundarySource_mem

end BoundaryChartSelectedBoxTargetImageAutoData

namespace BoundaryChartSelectedImageBoxContainment

variable {𝓞 : Type v}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {y : Fin n → Real}

/-- Local-openness selected-image route using a bundled atlas-membership pair. -/
theorem exists_orientedChangeOfVariablesOfOrientationMembership
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y)
    (A : BoundaryChartOrientedAtlas I M)
    (m : BoundaryChartOrientationMembership A.charts x0 x1)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner :=
  D.exists_orientedChangeOfVariables_of_localOpenness_orientedAtlas
    A m.source_mem m.boundarySource_mem himage

/-- Mathlib-orientation atlas data plus bundled membership for selected-image COV. -/
theorem exists_orientedChangeOfVariablesOfMathlibOrientationAtlasMembership
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y)
    (O : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (m : BoundaryChartOrientationMembership O.charts x0 x1)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner :=
  D.exists_orientedChangeOfVariablesOfMathlibOrientationAtlasData
    O m.source_mem m.boundarySource_mem himage

/-- Older mathlib-facing atlas bridge plus bundled membership for selected-image COV. -/
theorem exists_orientedChangeOfVariablesOfMathlibOrientedAtlasMembership
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y)
    (O : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞)
    (m : BoundaryChartOrientationMembership O.charts x0 x1)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner :=
  D.exists_orientedChangeOfVariablesOfMathlibOrientedAtlasBridge
    O m.source_mem m.boundarySource_mem himage

end BoundaryChartSelectedImageBoxContainment

namespace BoundaryChartSourceShrinkInverseTargetBoxData

variable {𝓞 : Type v}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d e f : Fin (n + 1) → Real} {u y : Fin n → Real}

/-- Source-shrink selected COV using a bundled atlas-membership pair. -/
theorem selectedCOVOfOrientationMembership
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (A : BoundaryChartOrientedAtlas I M)
    (m : BoundaryChartOrientationMembership A.charts x0 x1) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner e f :=
  D.selectedCOVOfOrientedAtlas hbox A m.source_mem m.boundarySource_mem

/-- Source-shrink selected COV from mathlib-orientation atlas data and bundled membership. -/
theorem selectedCOVOfMathlibOrientationAtlasMembership
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (O : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (m : BoundaryChartOrientationMembership O.charts x0 x1) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner e f :=
  D.selectedCOVOfMathlibOrientationAtlasData
    hbox O m.source_mem m.boundarySource_mem

/-- Ambient-tangent local-openness route using a bundled atlas-membership pair. -/
theorem exists_selectedCOVOfAmbientTangentBoundsOrientationMembership
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (A : BoundaryChartOrientedAtlas I M)
    (m : BoundaryChartOrientationMembership A.charts x0 x1)
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
  D.exists_selectedCOVOfAmbientTangentBoundsOrientedAtlas
    hbox A m.source_mem m.boundarySource_mem himage hlower hupper

end BoundaryChartSourceShrinkInverseTargetBoxData

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphData

variable {𝓞 : Type v}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real} {u y : Fin n → Real}

/-- Source-shrink local-homeomorphism COV using a bundled atlas-membership pair. -/
theorem selectedCOVOfOrientationMembership
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (A : BoundaryChartOrientedAtlas I M)
    (m : BoundaryChartOrientationMembership A.charts x0 x1) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner
      D.targetLowerCorner D.targetUpperCorner :=
  D.selectedCOVOfOrientedAtlas hbox A m.source_mem m.boundarySource_mem

/-- Local-homeomorphism selected COV from mathlib-orientation atlas data and bundled membership. -/
theorem selectedCOVOfMathlibOrientationAtlasMembership
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (O : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (m : BoundaryChartOrientationMembership O.charts x0 x1) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner
      D.targetLowerCorner D.targetUpperCorner :=
  D.selectedCOVOfMathlibOrientationAtlasData
    hbox O m.source_mem m.boundarySource_mem

/-- Ambient-tangent local-openness route using a bundled atlas-membership pair. -/
theorem exists_selectedCOVOfAmbientTangentBoundsOrientationMembership
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (A : BoundaryChartOrientedAtlas I M)
    (m : BoundaryChartOrientationMembership A.charts x0 x1)
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
  D.exists_selectedCOVOfAmbientTangentBoundsOrientedAtlas
    hbox A m.source_mem m.boundarySource_mem hlower hupper

end BoundaryChartSourceShrinkOpenPartialHomeomorphData

end ManifoldBoundary

end Stokes

end
