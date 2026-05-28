import Stokes.BoundaryChart.TargetBoxCompactImage

/-!
# Compact-image targets from IFT/local-openness data

This file removes one layer of manual target-image bookkeeping.  Local
openness/IFT selects a target lower-zero box by proving that the selected box
lies in the source image.  The remaining compact-image side is discharged here
from an actual source-image containment fact, or from compactness plus a
compact coordinate box that is known to lie in each selected local-inverse
target box.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section ManifoldBoundary

universe u w p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- A selected boundary chart box has compact image under the boundary chart
transition.  This packages the compact-domain/continuous-image step so
downstream IFT target-box constructors no longer need it as a separate field. -/
theorem boundaryChartTransition_isCompact_image_of_selectedBox
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    IsCompact
      ((boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b) :=
  (isCompact_lowerZeroFaceDomain a b).image_of_continuousOn
    (boundaryChartTransition_continuousOn_of_selectedBox hbox)

/-- Source-image containment in a lower-zero target box gives the coordinate
compact-image predicate for the same target box. -/
theorem compactCoordinateImageBoxSelection_of_boundaryImage_subset_lowerZeroFaceDomain
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hsubset :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ⊆
        lowerZeroFaceDomain c d) :
    compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b)
      (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d) := by
  simpa [compactCoordinateImageBoxSelection,
    lowerZeroFaceDomain_eq_Icc_boundaryFaceCorners] using hsubset

/-- Source-image `MapsTo` control for every local-inverse target box produces
the compact-coordinate image predicate expected by the local-openness target
selector. -/
theorem boundaryChartCompactCoordinateImageForLocalInverseTargets_of_mapsTo
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (hmaps :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            MapsTo (boundaryChartTransition I x0 x1)
              (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y := by
  intro c d hc0 hle hy hlocal
  exact compactCoordinateImageBoxSelection_of_boundaryImage_subset_lowerZeroFaceDomain
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (c := c) (d := d) (by
      intro z hz
      rcases hz with ⟨u, hu, rfl⟩
      exact hmaps c d hc0 hle hy hlocal hu)

/-- Source-image subset control for every local-inverse target box produces the
compact-coordinate image predicate expected by the local-openness target
selector. -/
theorem boundaryChartCompactCoordinateImageForLocalInverseTargets_of_image_subset
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (hsubset :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ⊆
              lowerZeroFaceDomain c d) :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y := by
  intro c d hc0 hle hy hlocal
  exact compactCoordinateImageBoxSelection_of_boundaryImage_subset_lowerZeroFaceDomain
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (c := c) (d := d) (hsubset c d hc0 hle hy hlocal)

/-- Boundary-box spelling of
`boundaryChartCompactCoordinateImageForLocalInverseTargets_of_image_subset`. -/
theorem boundaryChartCompactImageForLocalInverseTargets_of_image_subset
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (hsubset :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ⊆
              lowerZeroFaceDomain c d) :
    boundaryChartCompactImageForLocalInverseTargets I x0 x1 a b y := by
  exact boundaryChartCompactImageForLocalInverseTargets_of_coordinate
    (boundaryChartCompactCoordinateImageForLocalInverseTargets_of_image_subset
      (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
      (y := y) hsubset)

/-- A fixed compact coordinate image box, together with containment of that
box in every selected local-inverse target, gives the local-inverse-target
compact-image predicate. -/
theorem boundaryChartCompactCoordinateImageForLocalInverseTargets_of_compactBox
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    {e f : Fin n → Real}
    (hcompact :
      compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
        (lowerZeroFaceDomain a b) e f)
    (hcontains :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            Set.Icc e f ⊆
              Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y := by
  intro c d hc0 hle hy hlocal z hz
  exact hcontains c d hc0 hle hy hlocal (hcompact hz)

/-- Compactness of the source boundary-box image plus containment of the
compact coordinate image box in each selected local-inverse target gives the
local-inverse-target compact-image predicate. -/
theorem boundaryChartCompactCoordinateImageForLocalInverseTargets_of_isCompactImage
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {y : Fin n → Real}
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
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y :=
  BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets.compactImageForLocalInverseTargets_of_isCompactImage
      (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
      (y := y) hK hcontains

/-- A selected source box supplies the compact-image fact needed by the
local-inverse-target compact-image predicate. -/
theorem boundaryChartCompactCoordinateImageForLocalInverseTargets_of_selectedBox
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcontains :
      ∀ e f : Fin n → Real, e ≤ f →
        compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
          (lowerZeroFaceDomain a b) e f →
          ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
            y ∈ lowerZeroFaceDomain c d →
              boundaryChartLocalInverseData I x0 x1 a b c d →
                Set.Icc e f ⊆
                  Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y :=
  boundaryChartCompactCoordinateImageForLocalInverseTargets_of_isCompactImage
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (y := y)
    (boundaryChartTransition_isCompact_image_of_selectedBox hbox)
    hcontains

/-- Local openness plus source-image containment for the selected
local-inverse target box gives a target-box selection. -/
theorem exists_boundaryChartTargetBoxSelection_of_localOpenness_image_subset
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
    ∃ target : BoundaryChartTargetBoxSelection I x0 x1 a b,
      y ∈ lowerZeroFaceDomain target.lowerCorner target.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          target.lowerCorner target.upperCorner :=
  exists_boundaryChartTargetBoxSelection_of_localOpenness_compactImage
    himage
    (boundaryChartCompactCoordinateImageForLocalInverseTargets_of_image_subset
      (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
      (y := y) hsubset)

/-- Local openness plus compact source-image box containment gives a target-box
selection without manually supplying `compactImageForLocalInverseTargets`. -/
theorem exists_boundaryChartTargetBoxSelection_of_localOpenness_isCompactImage
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
    ∃ target : BoundaryChartTargetBoxSelection I x0 x1 a b,
      y ∈ lowerZeroFaceDomain target.lowerCorner target.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          target.lowerCorner target.upperCorner :=
  exists_boundaryChartTargetBoxSelection_of_localOpenness_compactImage
    himage
    (boundaryChartCompactCoordinateImageForLocalInverseTargets_of_isCompactImage
      (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
      (y := y) hK hcontains)

/-- Local openness plus a selected source box gives target-box selection
without separately supplying compactness of the source image. -/
theorem exists_boundaryChartTargetBoxSelection_of_localOpenness_selectedBox
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
    ∃ target : BoundaryChartTargetBoxSelection I x0 x1 a b,
      y ∈ lowerZeroFaceDomain target.lowerCorner target.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          target.lowerCorner target.upperCorner :=
  exists_boundaryChartTargetBoxSelection_of_localOpenness_isCompactImage
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (y := y) himage
    (boundaryChartTransition_isCompact_image_of_selectedBox hbox)
    hcontains

/-- Selected-box auto-data from local openness plus source-image containment
for the selected local-inverse target box. -/
theorem exists_selectedBoxTargetImageAutoData_of_localOpenness_image_subset
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y)
    (hsubset :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ⊆
              lowerZeroFaceDomain c d) :
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          D.targetLowerCorner D.targetUpperCorner :=
  exists_selectedBoxTargetImageAutoData_of_localOpenness_compactImage
    hbox himage
    (boundaryChartCompactCoordinateImageForLocalInverseTargets_of_image_subset
      (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
      (y := y) hsubset)

/-- Selected-box auto-data from local openness plus compact source-image box
containment. -/
theorem exists_selectedBoxTargetImageAutoData_of_localOpenness_isCompactImage
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
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
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          D.targetLowerCorner D.targetUpperCorner :=
  exists_selectedBoxTargetImageAutoData_of_localOpenness_compactImage
    hbox himage
    (boundaryChartCompactCoordinateImageForLocalInverseTargets_of_isCompactImage
      (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
      (y := y) hK hcontains)

/-- Selected-box auto-data from local openness and the selected source-box
itself, with compactness of the source image generated internally. -/
theorem exists_selectedBoxTargetImageAutoData_of_localOpenness_selectedBox
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
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          D.targetLowerCorner D.targetUpperCorner :=
  exists_selectedBoxTargetImageAutoData_of_localOpenness_isCompactImage
    (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b)
    (y := y) hbox himage
    (boundaryChartTransition_isCompact_image_of_selectedBox hbox)
    hcontains

/-- IFT-facing selected-box auto-data from compact source-image box
containment.  The local-openness hypothesis is produced by the existing
strict-derivative/open-mapping lemma. -/
theorem exists_selectedBoxTargetImageAutoData_of_IFT_isCompactImage
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hderiv :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤)
    (hK : IsCompact
      ((boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b))
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
        boundaryChartSelectedBoxImageData I x0 x1 a b
          D.targetLowerCorner D.targetUpperCorner :=
  exists_selectedBoxTargetImageAutoData_of_localOpenness_isCompactImage
    (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b)
    (y := boundaryChartTransition I x0 x1 u)
    hbox
    (boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
      hderiv hsurj hsource)
    hK hcontains

/-- IFT-facing selected-box auto-data where the selected source box also
generates the compact source-image fact. -/
theorem exists_selectedBoxTargetImageAutoData_of_IFT_selectedBox
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
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          D.targetLowerCorner D.targetUpperCorner :=
  exists_selectedBoxTargetImageAutoData_of_IFT_isCompactImage
    (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b)
    (u := u) hbox hsource hderiv hsurj
    (boundaryChartTransition_isCompact_image_of_selectedBox hbox)
    hcontains

namespace BoundaryChartLocalOpennessCompactImageCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/-- Build the existing local-openness compact-image cover from per-piece
source-image containment into every selected local-inverse target box. -/
def ofImageSubset
    (sourceCover : BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece)
    (targetPoint : Piece → Fin n → Real)
    (image_mem_nhds :
      ∀ q, q ∈ sourceCover.activePieces →
        (boundaryChartTransition I x0 x1) ''
            lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
              (sourceCover.sourceUpperCorner q) ∈ 𝓝 (targetPoint q))
    (image_subset :
      ∀ q, q ∈ sourceCover.activePieces →
        ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
          targetPoint q ∈ lowerZeroFaceDomain c d →
            boundaryChartLocalInverseData I x0 x1
              (sourceCover.sourceLowerCorner q) (sourceCover.sourceUpperCorner q) c d →
              (boundaryChartTransition I x0 x1) ''
                  lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
                    (sourceCover.sourceUpperCorner q) ⊆
                lowerZeroFaceDomain c d) :
    BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece where
  toBoundaryChartCompactSourceBoxCover := sourceCover
  targetPoint := targetPoint
  image_mem_nhds := image_mem_nhds
  compactImageForLocalInverseTargets := fun q hq =>
    boundaryChartCompactCoordinateImageForLocalInverseTargets_of_image_subset
      (I := I) (x0 := x0) (x1 := x1)
      (a := sourceCover.sourceLowerCorner q)
      (b := sourceCover.sourceUpperCorner q)
      (y := targetPoint q) (image_subset q hq)

/-- Build the existing local-openness compact-image cover from compactness of
each source-box image and containment of the selected compact coordinate box in
every selected local-inverse target. -/
def ofIsCompactImage
    (sourceCover : BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece)
    (targetPoint : Piece → Fin n → Real)
    (image_mem_nhds :
      ∀ q, q ∈ sourceCover.activePieces →
        (boundaryChartTransition I x0 x1) ''
            lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
              (sourceCover.sourceUpperCorner q) ∈ 𝓝 (targetPoint q))
    (isCompact_image :
      ∀ q, q ∈ sourceCover.activePieces →
        IsCompact
          ((boundaryChartTransition I x0 x1) ''
            lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
              (sourceCover.sourceUpperCorner q)))
    (compactBox_subset :
      ∀ q, q ∈ sourceCover.activePieces →
        ∀ e f : Fin n → Real, e ≤ f →
          compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
            (lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
              (sourceCover.sourceUpperCorner q)) e f →
          ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
            targetPoint q ∈ lowerZeroFaceDomain c d →
              boundaryChartLocalInverseData I x0 x1
                (sourceCover.sourceLowerCorner q) (sourceCover.sourceUpperCorner q) c d →
                Set.Icc e f ⊆
                  Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece where
  toBoundaryChartCompactSourceBoxCover := sourceCover
  targetPoint := targetPoint
  image_mem_nhds := image_mem_nhds
  compactImageForLocalInverseTargets := fun q hq =>
    boundaryChartCompactCoordinateImageForLocalInverseTargets_of_isCompactImage
      (I := I) (x0 := x0) (x1 := x1)
      (a := sourceCover.sourceLowerCorner q)
      (b := sourceCover.sourceUpperCorner q)
      (y := targetPoint q)
      (isCompact_image q hq) (compactBox_subset q hq)

/-- Build the existing local-openness compact-image cover from selected source
boxes, generating compactness of each source-box image internally. -/
def ofSelectedBox
    [IsManifold I 1 M]
    {ω : ManifoldForm I M n}
    (sourceCover : BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece)
    (targetPoint : Piece → Fin n → Real)
    (selectedBox :
      ∀ q, q ∈ sourceCover.activePieces →
        boundaryChartSelectedBox I x0 x1 ω
          (sourceCover.sourceLowerCorner q)
          (sourceCover.sourceUpperCorner q))
    (image_mem_nhds :
      ∀ q, q ∈ sourceCover.activePieces →
        (boundaryChartTransition I x0 x1) ''
            lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
              (sourceCover.sourceUpperCorner q) ∈ 𝓝 (targetPoint q))
    (compactBox_subset :
      ∀ q, q ∈ sourceCover.activePieces →
        ∀ e f : Fin n → Real, e ≤ f →
          compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
            (lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
              (sourceCover.sourceUpperCorner q)) e f →
          ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
            targetPoint q ∈ lowerZeroFaceDomain c d →
              boundaryChartLocalInverseData I x0 x1
                (sourceCover.sourceLowerCorner q) (sourceCover.sourceUpperCorner q) c d →
                Set.Icc e f ⊆
                  Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece :=
  ofIsCompactImage
    (I := I) (x0 := x0) (x1 := x1)
    sourceCover targetPoint image_mem_nhds
    (fun q hq =>
      boundaryChartTransition_isCompact_image_of_selectedBox
        (I := I) (x0 := x0) (x1 := x1)
        (ω := ω) (a := sourceCover.sourceLowerCorner q)
        (b := sourceCover.sourceUpperCorner q) (selectedBox q hq))
    compactBox_subset

end BoundaryChartLocalOpennessCompactImageCover

namespace BoundaryChartIFTCompactImageCoverData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/-- Build the existing IFT compact-image cover data from per-piece source-image
containment into every selected local-inverse target box. -/
def ofImageSubset
    (sourceCover : BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece)
    (sourcePoint : Piece → Fin n → Real)
    (sourcePoint_mem :
      ∀ q, q ∈ sourceCover.activePieces →
        sourcePoint q ∈
          lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
            (sourceCover.sourceUpperCorner q))
    (source_mem_nhds :
      ∀ q, q ∈ sourceCover.activePieces →
        lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
          (sourceCover.sourceUpperCorner q) ∈ 𝓝 (sourcePoint q))
    (hasStrictFDerivAt :
      ∀ q, q ∈ sourceCover.activePieces →
        HasStrictFDerivAt (boundaryChartTransition I x0 x1)
          (boundaryChartTransitionTangentMap I x0 x1 (sourcePoint q))
          (sourcePoint q))
    (tangentMap_surjective :
      ∀ q, q ∈ sourceCover.activePieces →
        (boundaryChartTransitionTangentMap I x0 x1 (sourcePoint q)).range = ⊤)
    (image_subset :
      ∀ q, q ∈ sourceCover.activePieces →
        ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
          boundaryChartTransition I x0 x1 (sourcePoint q) ∈
              lowerZeroFaceDomain c d →
            boundaryChartLocalInverseData I x0 x1
              (sourceCover.sourceLowerCorner q) (sourceCover.sourceUpperCorner q) c d →
              (boundaryChartTransition I x0 x1) ''
                  lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
                    (sourceCover.sourceUpperCorner q) ⊆
                lowerZeroFaceDomain c d) :
    BoundaryChartIFTCompactImageCoverData I x0 x1 a b Piece where
  toBoundaryChartCompactSourceBoxCover := sourceCover
  sourcePoint := sourcePoint
  sourcePoint_mem := sourcePoint_mem
  source_mem_nhds := source_mem_nhds
  hasStrictFDerivAt := hasStrictFDerivAt
  tangentMap_surjective := tangentMap_surjective
  compactImageForLocalInverseTargets := fun q hq =>
    boundaryChartCompactCoordinateImageForLocalInverseTargets_of_image_subset
      (I := I) (x0 := x0) (x1 := x1)
      (a := sourceCover.sourceLowerCorner q)
      (b := sourceCover.sourceUpperCorner q)
      (y := boundaryChartTransition I x0 x1 (sourcePoint q))
      (image_subset q hq)

/-- Build the existing IFT compact-image cover data from compactness of each
source-box image and containment of the selected compact coordinate box in each
selected local-inverse target. -/
def ofIsCompactImage
    (sourceCover : BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece)
    (sourcePoint : Piece → Fin n → Real)
    (sourcePoint_mem :
      ∀ q, q ∈ sourceCover.activePieces →
        sourcePoint q ∈
          lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
            (sourceCover.sourceUpperCorner q))
    (source_mem_nhds :
      ∀ q, q ∈ sourceCover.activePieces →
        lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
          (sourceCover.sourceUpperCorner q) ∈ 𝓝 (sourcePoint q))
    (hasStrictFDerivAt :
      ∀ q, q ∈ sourceCover.activePieces →
        HasStrictFDerivAt (boundaryChartTransition I x0 x1)
          (boundaryChartTransitionTangentMap I x0 x1 (sourcePoint q))
          (sourcePoint q))
    (tangentMap_surjective :
      ∀ q, q ∈ sourceCover.activePieces →
        (boundaryChartTransitionTangentMap I x0 x1 (sourcePoint q)).range = ⊤)
    (isCompact_image :
      ∀ q, q ∈ sourceCover.activePieces →
        IsCompact
          ((boundaryChartTransition I x0 x1) ''
            lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
              (sourceCover.sourceUpperCorner q)))
    (compactBox_subset :
      ∀ q, q ∈ sourceCover.activePieces →
        ∀ e f : Fin n → Real, e ≤ f →
          compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
            (lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
              (sourceCover.sourceUpperCorner q)) e f →
          ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
            boundaryChartTransition I x0 x1 (sourcePoint q) ∈
                lowerZeroFaceDomain c d →
              boundaryChartLocalInverseData I x0 x1
                (sourceCover.sourceLowerCorner q) (sourceCover.sourceUpperCorner q) c d →
                Set.Icc e f ⊆
                  Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    BoundaryChartIFTCompactImageCoverData I x0 x1 a b Piece where
  toBoundaryChartCompactSourceBoxCover := sourceCover
  sourcePoint := sourcePoint
  sourcePoint_mem := sourcePoint_mem
  source_mem_nhds := source_mem_nhds
  hasStrictFDerivAt := hasStrictFDerivAt
  tangentMap_surjective := tangentMap_surjective
  compactImageForLocalInverseTargets := fun q hq =>
    boundaryChartCompactCoordinateImageForLocalInverseTargets_of_isCompactImage
      (I := I) (x0 := x0) (x1 := x1)
      (a := sourceCover.sourceLowerCorner q)
      (b := sourceCover.sourceUpperCorner q)
      (y := boundaryChartTransition I x0 x1 (sourcePoint q))
      (isCompact_image q hq) (compactBox_subset q hq)

/-- Build the existing IFT compact-image cover data from selected source
boxes, generating compactness of each source-box image internally. -/
def ofSelectedBox
    [IsManifold I 1 M]
    {ω : ManifoldForm I M n}
    (sourceCover : BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece)
    (sourcePoint : Piece → Fin n → Real)
    (selectedBox :
      ∀ q, q ∈ sourceCover.activePieces →
        boundaryChartSelectedBox I x0 x1 ω
          (sourceCover.sourceLowerCorner q)
          (sourceCover.sourceUpperCorner q))
    (sourcePoint_mem :
      ∀ q, q ∈ sourceCover.activePieces →
        sourcePoint q ∈
          lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
            (sourceCover.sourceUpperCorner q))
    (source_mem_nhds :
      ∀ q, q ∈ sourceCover.activePieces →
        lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
          (sourceCover.sourceUpperCorner q) ∈ 𝓝 (sourcePoint q))
    (hasStrictFDerivAt :
      ∀ q, q ∈ sourceCover.activePieces →
        HasStrictFDerivAt (boundaryChartTransition I x0 x1)
          (boundaryChartTransitionTangentMap I x0 x1 (sourcePoint q))
          (sourcePoint q))
    (tangentMap_surjective :
      ∀ q, q ∈ sourceCover.activePieces →
        (boundaryChartTransitionTangentMap I x0 x1 (sourcePoint q)).range = ⊤)
    (compactBox_subset :
      ∀ q, q ∈ sourceCover.activePieces →
        ∀ e f : Fin n → Real, e ≤ f →
          compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
            (lowerZeroFaceDomain (sourceCover.sourceLowerCorner q)
              (sourceCover.sourceUpperCorner q)) e f →
          ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
            boundaryChartTransition I x0 x1 (sourcePoint q) ∈
                lowerZeroFaceDomain c d →
              boundaryChartLocalInverseData I x0 x1
                (sourceCover.sourceLowerCorner q) (sourceCover.sourceUpperCorner q) c d →
                Set.Icc e f ⊆
                  Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    BoundaryChartIFTCompactImageCoverData I x0 x1 a b Piece :=
  ofIsCompactImage
    (I := I) (x0 := x0) (x1 := x1)
    sourceCover sourcePoint sourcePoint_mem source_mem_nhds
    hasStrictFDerivAt tangentMap_surjective
    (fun q hq =>
      boundaryChartTransition_isCompact_image_of_selectedBox
        (I := I) (x0 := x0) (x1 := x1)
        (ω := ω) (a := sourceCover.sourceLowerCorner q)
        (b := sourceCover.sourceUpperCorner q) (selectedBox q hq))
    compactBox_subset

end BoundaryChartIFTCompactImageCoverData

end ManifoldBoundary

end Stokes

end
