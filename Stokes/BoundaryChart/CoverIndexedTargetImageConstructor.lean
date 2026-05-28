import Stokes.BoundaryChart.SelectedBoxContainsAuto

/-!
# Cover-indexed target-image constructors

This file is the cover-indexed-facing boundary-chart target-image layer.  The
older downstream code often asks for `BoundaryChartTransitionCompactBoxData`,
while the newer IFT/local-openness pipeline naturally produces either a
`BoundaryChartTargetBoxSelection` or selected image-box containment data.

The lemmas below remove that mismatch.  They turn the existing target-box and
selected-image-box constructors into the compact-box data consumed by boundary
chart change-of-variables, without exposing the raw
`boundaryChartCompactImageForLocalInverseTargets` field at call sites.
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

namespace BoundaryChartTargetBoxSelection

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real}

/--
Forget a target-box selection to the older transition compact-box package.

This is the exact data shape consumed by several boundary chart COV and
cover-indexed constructors.
-/
def toTransitionCompactBoxData
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    BoundaryChartTransitionCompactBoxData I x0 x1 a b where
  lowerCorner := target.lowerCorner
  upperCorner := target.upperCorner
  lowerCorner_zero := target.lowerCorner_zero
  lower_le_upper := target.lower_le_upper
  compactImage := target.compactImage
  localInverse := target.localInverse

@[simp]
theorem toTransitionCompactBoxData_lowerCorner
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    target.toTransitionCompactBoxData.lowerCorner = target.lowerCorner :=
  rfl

@[simp]
theorem toTransitionCompactBoxData_upperCorner
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    target.toTransitionCompactBoxData.upperCorner = target.upperCorner :=
  rfl

/-- The transition compact-box image predicate is the target-box image predicate. -/
theorem toTransitionCompactBoxData_imageData
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    target.toTransitionCompactBoxData.imageData = target.imageData :=
  rfl

end BoundaryChartTargetBoxSelection

namespace BoundaryChartSelectedBoxTargetImageAutoData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/-- Selected-box auto data as transition compact-box data. -/
def toTransitionCompactBoxData
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b) :
    BoundaryChartTransitionCompactBoxData I x0 x1 a b :=
  D.targetBox.toTransitionCompactBoxData

@[simp]
theorem toTransitionCompactBoxData_lowerCorner
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b) :
    D.toTransitionCompactBoxData.lowerCorner = D.targetLowerCorner :=
  rfl

@[simp]
theorem toTransitionCompactBoxData_upperCorner
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b) :
    D.toTransitionCompactBoxData.upperCorner = D.targetUpperCorner :=
  rfl

/-- Auto-data image data is preserved by the transition compact-box projection. -/
theorem toTransitionCompactBoxData_imageData
    (D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b) :
    D.toTransitionCompactBoxData.imageData = D.imageData :=
  rfl

end BoundaryChartSelectedBoxTargetImageAutoData

/--
Local openness plus direct source-image containment produces transition
compact-box data, eliminating the explicit
`boundaryChartCompactImageForLocalInverseTargets` input.
-/
theorem exists_boundaryChartTransitionCompactBoxData_of_localOpenness_image_subset
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y)
    (hsubset :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ⊆
              lowerZeroFaceDomain c d) :
    ∃ D : BoundaryChartTransitionCompactBoxData I x0 x1 a b,
      y ∈ lowerZeroFaceDomain D.lowerCorner D.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          D.lowerCorner D.upperCorner := by
  rcases exists_boundaryChartTargetBoxSelection_of_localOpenness_image_subset
      (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
      (y := y) himage hsubset with
    ⟨target, hmem, himageData⟩
  refine ⟨target.toTransitionCompactBoxData, ?_, ?_⟩
  · simpa [BoundaryChartTargetBoxSelection.toTransitionCompactBoxData] using hmem
  · simpa [BoundaryChartTargetBoxSelection.toTransitionCompactBoxData] using himageData

/--
Local openness plus compact source-image box containment produces transition
compact-box data.  This is the compact-image version of the preceding theorem:
compactness chooses one coordinate image box, and the caller proves that box is
contained in every later local-inverse target.
-/
theorem exists_boundaryChartTransitionCompactBoxData_of_localOpenness_isCompactImage
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y)
    (hK : IsCompact
      ((boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b))
    (hcontains :
      ∀ e f : Fin n → Real, e ≤ f →
        compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
          (lowerZeroFaceDomain a b) e f →
          ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
            y ∈ lowerZeroFaceDomain c d →
              boundaryChartLocalInverseData I x0 x1 a b c d →
                Set.Icc e f ⊆
                  Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    ∃ D : BoundaryChartTransitionCompactBoxData I x0 x1 a b,
      y ∈ lowerZeroFaceDomain D.lowerCorner D.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          D.lowerCorner D.upperCorner := by
  rcases exists_boundaryChartTargetBoxSelection_of_localOpenness_isCompactImage
      (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
      (y := y) himage hK hcontains with
    ⟨target, hmem, himageData⟩
  refine ⟨target.toTransitionCompactBoxData, ?_, ?_⟩
  · simpa [BoundaryChartTargetBoxSelection.toTransitionCompactBoxData] using hmem
  · simpa [BoundaryChartTargetBoxSelection.toTransitionCompactBoxData] using himageData

/--
Selected source boxes generate compactness of the source image internally, so
only the compact-box containment obligation remains.
-/
theorem exists_boundaryChartTransitionCompactBoxData_of_localOpenness_selectedBox
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
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
    ∃ D : BoundaryChartTransitionCompactBoxData I x0 x1 a b,
      y ∈ lowerZeroFaceDomain D.lowerCorner D.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          D.lowerCorner D.upperCorner := by
  rcases exists_boundaryChartTargetBoxSelection_of_localOpenness_selectedBox
      (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b)
      (y := y) hbox himage hcontains with
    ⟨target, hmem, himageData⟩
  refine ⟨target.toTransitionCompactBoxData, ?_, ?_⟩
  · simpa [BoundaryChartTargetBoxSelection.toTransitionCompactBoxData] using hmem
  · simpa [BoundaryChartTargetBoxSelection.toTransitionCompactBoxData] using himageData

/--
IFT/local-openness version of
`exists_boundaryChartTransitionCompactBoxData_of_localOpenness_selectedBox`.
-/
theorem exists_boundaryChartTransitionCompactBoxData_of_IFT_selectedBox
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
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
    ∃ D : BoundaryChartTransitionCompactBoxData I x0 x1 a b,
      boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain D.lowerCorner D.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          D.lowerCorner D.upperCorner := by
  exact exists_boundaryChartTransitionCompactBoxData_of_localOpenness_selectedBox
    (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b)
    (y := boundaryChartTransition I x0 x1 u)
    hbox
    (boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
      hderiv hsurj hsource)
    hcontains

namespace BoundaryChartSelectedImageBoxContainment

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {y : Fin n → Real}

/--
Selected image-box containment plus local openness produces transition
compact-box data.  This is the fixed-image-box replacement for the raw
`compactImageForLocalInverseTargets` predicate.
-/
theorem exists_transitionCompactBoxData_of_localOpenness
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartTransitionCompactBoxData I x0 x1 a b,
      y ∈ lowerZeroFaceDomain T.lowerCorner T.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          T.lowerCorner T.upperCorner := by
  rcases D.exists_autoData_of_localOpenness himage with
    ⟨auto, hmem, himageData⟩
  refine ⟨auto.toTransitionCompactBoxData, ?_, ?_⟩
  · simpa [BoundaryChartSelectedBoxTargetImageAutoData.toTransitionCompactBoxData] using hmem
  · simpa [BoundaryChartSelectedBoxTargetImageAutoData.toTransitionCompactBoxData] using himageData

/--
IFT/local-openness form of `exists_transitionCompactBoxData_of_localOpenness`
for selected image-box containment.
-/
theorem exists_transitionCompactBoxData_of_IFT
    {u : Fin n → Real}
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b
      (boundaryChartTransition I x0 x1 u))
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hderiv :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤) :
    ∃ T : BoundaryChartTransitionCompactBoxData I x0 x1 a b,
      boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain T.lowerCorner T.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          T.lowerCorner T.upperCorner := by
  exact D.exists_transitionCompactBoxData_of_localOpenness
    (boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
      hderiv hsurj hsource)

end BoundaryChartSelectedImageBoxContainment

namespace BoundaryChartSelectedBoxIFTPointContainsAutoData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/--
Pointwise selected-box IFT data with fixed selected image-box containment
directly produces the transition compact-box package.
-/
theorem exists_transitionCompactBoxData
    (D : BoundaryChartSelectedBoxIFTPointContainsAutoData I x0 x1 ω a b) :
    ∃ T : BoundaryChartTransitionCompactBoxData I x0 x1 a b,
      D.targetPoint ∈ lowerZeroFaceDomain T.lowerCorner T.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          T.lowerCorner T.upperCorner := by
  rcases D.exists_autoData with ⟨auto, hmem, himageData⟩
  refine ⟨auto.toTransitionCompactBoxData, ?_, ?_⟩
  · simpa [BoundaryChartSelectedBoxTargetImageAutoData.toTransitionCompactBoxData] using hmem
  · simpa [BoundaryChartSelectedBoxTargetImageAutoData.toTransitionCompactBoxData] using himageData

end BoundaryChartSelectedBoxIFTPointContainsAutoData

end ManifoldBoundary

end Stokes

end
