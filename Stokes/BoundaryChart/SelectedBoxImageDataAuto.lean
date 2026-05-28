import Stokes.BoundaryChart.CompactImageFromIFTAuto
import Stokes.BoundaryChart.SelectedBoxCOVFromOrientationAuto

/-!
# Selected-box image data automation

This module provides theorem-facing entry points that go directly from selected
boundary boxes and local-openness/IFT data to oriented boundary-chart
change-of-variables statements.  The target image data, compact image fact, and
local-inverse target box are materialized internally by the selected-box target
image pipeline.
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

/--
Local openness plus compact-image-box containment, with compactness generated
from the selected source box, directly produces oriented-atlas boundary COV.
-/
theorem exists_boundaryChartOrientedChangeOfVariables_of_localOpenness_selectedBox_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y)
    (hcontains :
      ∀ e f : Fin n → Real, e ≤ f →
        compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
          (lowerZeroFaceDomain a b) e f →
          ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
            y ∈ lowerZeroFaceDomain c d →
              boundaryChartLocalInverseData I x0 x1 a b c d →
                Set.Icc e f ⊆
                  Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          D.targetLowerCorner D.targetUpperCorner := by
  rcases exists_selectedBoxTargetImageAutoData_of_localOpenness_selectedBox
      (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b)
      (y := y) hbox himage hcontains with
    ⟨D, hmem, _himageData⟩
  exact ⟨D, hmem, D.orientedChangeOfVariablesOfOrientedAtlas A hx0 hx1⟩

/--
Local openness plus compact-image-box containment, with compactness generated
from the selected source box, directly produces oriented-manifold boundary COV.
-/
theorem exists_boundaryChartOrientedChangeOfVariables_of_localOpenness_selectedBox_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y)
    (hcontains :
      ∀ e f : Fin n → Real, e ≤ f →
        compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
          (lowerZeroFaceDomain a b) e f →
          ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
            y ∈ lowerZeroFaceDomain c d →
              boundaryChartLocalInverseData I x0 x1 a b c d →
                Set.Icc e f ⊆
                  Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          D.targetLowerCorner D.targetUpperCorner := by
  rcases exists_selectedBoxTargetImageAutoData_of_localOpenness_selectedBox
      (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b)
      (y := y) hbox himage hcontains with
    ⟨D, hmem, _himageData⟩
  exact ⟨D, hmem, D.orientedChangeOfVariablesOfOrientedManifold⟩

/--
IFT/local-openness plus compact-image-box containment, with compactness
generated from the selected source box, directly produces oriented-atlas
boundary COV.
-/
theorem exists_boundaryChartOrientedChangeOfVariables_of_IFT_selectedBox_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} {u : Fin n → Real}
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hderiv :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤)
    (hcontains :
      ∀ e f : Fin n → Real, e ≤ f →
        compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
          (lowerZeroFaceDomain a b) e f →
          ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
            boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d →
              boundaryChartLocalInverseData I x0 x1 a b c d →
                Set.Icc e f ⊆
                  Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          D.targetLowerCorner D.targetUpperCorner := by
  rcases exists_selectedBoxTargetImageAutoData_of_IFT_selectedBox
      (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b)
      (u := u) hbox hsource hderiv hsurj hcontains with
    ⟨D, hmem, _himageData⟩
  exact ⟨D, hmem, D.orientedChangeOfVariablesOfOrientedAtlas A hx0 hx1⟩

/--
IFT/local-openness plus compact-image-box containment, with compactness
generated from the selected source box, directly produces oriented-manifold
boundary COV.
-/
theorem exists_boundaryChartOrientedChangeOfVariables_of_IFT_selectedBox_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hderiv :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤)
    (hcontains :
      ∀ e f : Fin n → Real, e ≤ f →
        compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
          (lowerZeroFaceDomain a b) e f →
          ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
            boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d →
              boundaryChartLocalInverseData I x0 x1 a b c d →
                Set.Icc e f ⊆
                  Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          D.targetLowerCorner D.targetUpperCorner := by
  rcases exists_selectedBoxTargetImageAutoData_of_IFT_selectedBox
      (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b)
      (u := u) hbox hsource hderiv hsurj hcontains with
    ⟨D, hmem, _himageData⟩
  exact ⟨D, hmem, D.orientedChangeOfVariablesOfOrientedManifold⟩

end ManifoldBoundary

end Stokes

end
