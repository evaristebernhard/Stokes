import Stokes.BoundaryChart.SelectedBoxIFTAuto
import Stokes.BoundaryChart.SelectedBoxImageDataAuto

/-!
# Selected image-box containment for boundary-chart IFT routes

`SelectedBoxIFTAuto` still exposes a strong containment callback: every compact
coordinate box that happens to contain the selected source image must lie in
each later local-inverse target.  The chart-box selection step should instead
produce one chosen compact image box and prove that this chosen box is contained
in the relevant local-inverse targets.

This file names that weaker, more geometric input and projects it back to the
existing selected-box local-openness / IFT APIs.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section ManifoldBoundary

universe u w p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Local openness plus direct source-image containment into every selected
local-inverse target produces oriented-atlas boundary COV.  This is the
target-image-containment route: callers no longer expose the arbitrary compact
image-box `hcontains` callback.
-/
theorem exists_orientedCOV_of_localOpenness_image_subset_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
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
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          D.targetLowerCorner D.targetUpperCorner := by
  rcases exists_selectedBoxTargetImageAutoData_of_localOpenness_image_subset
      (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b)
      (y := y) hbox himage hsubset with
    ⟨D, hmem, _himageData⟩
  exact ⟨D, hmem, D.orientedChangeOfVariablesOfOrientedAtlas A hx0 hx1⟩

/--
Local openness plus direct source-image containment into every selected
local-inverse target produces oriented-manifold boundary COV.
-/
theorem exists_orientedCOV_of_localOpenness_image_subset_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
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
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          D.targetLowerCorner D.targetUpperCorner := by
  rcases exists_selectedBoxTargetImageAutoData_of_localOpenness_image_subset
      (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b)
      (y := y) hbox himage hsubset with
    ⟨D, hmem, _himageData⟩
  exact ⟨D, hmem, D.orientedChangeOfVariablesOfOrientedManifold⟩

/--
Maps-to control is often the natural output of a selected-box shrink.  This
spelling converts it to the image-subset route and then produces oriented-atlas
boundary COV.
-/
theorem exists_orientedCOV_of_localOpenness_mapsTo_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y)
    (hmaps :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            MapsTo (boundaryChartTransition I x0 x1)
              (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          D.targetLowerCorner D.targetUpperCorner :=
  exists_orientedCOV_of_localOpenness_image_subset_orientedAtlas
    (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b)
    (y := y) A hx0 hx1 hbox himage
    (by
      intro c d hc0 hle hy hlocal z hz
      rcases hz with ⟨u, hu, rfl⟩
      exact hmaps c d hc0 hle hy hlocal hu)

/-- Oriented-manifold spelling of the maps-to route. -/
theorem exists_orientedCOV_of_localOpenness_mapsTo_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y)
    (hmaps :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            MapsTo (boundaryChartTransition I x0 x1)
              (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          D.targetLowerCorner D.targetUpperCorner :=
  exists_orientedCOV_of_localOpenness_image_subset_orientedManifold
    (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b)
    (y := y) hbox himage
    (by
      intro c d hc0 hle hy hlocal z hz
      rcases hz with ⟨u, hu, rfl⟩
      exact hmaps c d hc0 hle hy hlocal hu)

/--
IFT/local-openness plus direct source-image containment produces oriented-atlas
boundary COV.
-/
theorem exists_orientedCOV_of_IFT_image_subset_orientedAtlas
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
    (hsubset :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ⊆
              lowerZeroFaceDomain c d) :
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          D.targetLowerCorner D.targetUpperCorner :=
  exists_orientedCOV_of_localOpenness_image_subset_orientedAtlas
    (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b)
    (y := boundaryChartTransition I x0 x1 u) A hx0 hx1 hbox
    (boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
      hderiv hsurj hsource)
    hsubset

/-- Oriented-manifold spelling of the IFT/source-image-subset route. -/
theorem exists_orientedCOV_of_IFT_image_subset_orientedManifold
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
    (hsubset :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ⊆
              lowerZeroFaceDomain c d) :
    ∃ D : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          D.targetLowerCorner D.targetUpperCorner :=
  exists_orientedCOV_of_localOpenness_image_subset_orientedManifold
    (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b)
    (y := boundaryChartTransition I x0 x1 u) hbox
    (boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
      hderiv hsurj hsource)
    hsubset

/--
A selected source boundary box plus one selected compact coordinate image box
that is contained in every later local-inverse target box.

This is the caller-facing replacement for the stronger `hcontains` callback
used by `SelectedBoxIFTAuto`: downstream code no longer has to quantify over
all possible compact image boxes.
-/
structure BoundaryChartSelectedImageBoxContainment {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) (y : Fin n → Real) where
  /-- The selected source boundary box. -/
  selectedBox : boundaryChartSelectedBox I x0 x1 ω a b
  /-- A chosen compact image box and its containment in all relevant targets. -/
  imageBoxForLocalInverseTargets :
    BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets I x0 x1 a b y

namespace BoundaryChartSelectedImageBoxContainment

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {y : Fin n → Real}

/-- Lower corner of the selected compact coordinate image box. -/
def imageLowerCorner
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y) :
    Fin n → Real :=
  D.imageBoxForLocalInverseTargets.imageLowerCorner

/-- Upper corner of the selected compact coordinate image box. -/
def imageUpperCorner
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y) :
    Fin n → Real :=
  D.imageBoxForLocalInverseTargets.imageUpperCorner

/-- The selected image box has ordered corners. -/
theorem imageLower_le_imageUpper
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y) :
    D.imageLowerCorner ≤ D.imageUpperCorner :=
  D.imageBoxForLocalInverseTargets.imageLower_le_imageUpper

/-- The source image is contained in the selected compact image box. -/
theorem compactImage
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y) :
    compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) D.imageLowerCorner D.imageUpperCorner :=
  D.imageBoxForLocalInverseTargets.compactImage

/-- The selected compact image box is contained in every local-inverse target. -/
theorem selectedTarget_contains_imageBox
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y)
    {c d : Fin (n + 1) → Real} (hc0 : c 0 = 0) (hle : c ≤ d)
    (hy : y ∈ lowerZeroFaceDomain c d)
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    Set.Icc D.imageLowerCorner D.imageUpperCorner ⊆
      Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d) :=
  D.imageBoxForLocalInverseTargets.selectedTarget_contains_imageBox
    c d hc0 hle hy hlocal

/--
Projection to the compact-image predicate consumed by `TargetBoxFromIFT`.
This is the key bridge from fixed selected image boxes back to the older API.
-/
theorem compactImageForLocalInverseTargets
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y) :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y :=
  D.imageBoxForLocalInverseTargets.compactImageForLocalInverseTargets

/-- Build the existing explicit-local-inverse selected-box input shape. -/
def toLocalInverseAutoInputs
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y)
    (hlocal :
      ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
        y ∈ lowerZeroFaceDomain c d ∧
          boundaryChartLocalInverseData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxLocalInverseAutoInputs I x0 x1 ω a b where
  selectedBox := D.selectedBox
  targetPoint := y
  existsLocalInverseData := hlocal
  compactImageForLocalInverseTargets := D.compactImageForLocalInverseTargets

/-- Local openness plus selected image-box containment produces target-image data. -/
theorem exists_autoData_of_localOpenness
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          T.targetLowerCorner T.targetUpperCorner :=
  exists_selectedBoxTargetImageAutoData_of_localOpenness_compactImage
    D.selectedBox himage D.compactImageForLocalInverseTargets

/--
Oriented-atlas COV from local openness and selected image-box containment.
Compared with `SelectedBoxImageDataAuto`, callers supply the fixed selected
image box rather than the stronger arbitrary-box `hcontains` function.
-/
theorem exists_orientedChangeOfVariables_of_localOpenness_orientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y)
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner := by
  rcases D.exists_autoData_of_localOpenness himage with ⟨T, hmem, _himageData⟩
  exact ⟨T, hmem, T.orientedChangeOfVariablesOfOrientedAtlas A hx0 hx1⟩

/--
Oriented-manifold COV from local openness and selected image-box containment.
-/
theorem exists_orientedChangeOfVariables_of_localOpenness_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner := by
  rcases D.exists_autoData_of_localOpenness himage with ⟨T, hmem, _himageData⟩
  exact ⟨T, hmem, T.orientedChangeOfVariablesOfOrientedManifold⟩

end BoundaryChartSelectedImageBoxContainment

/--
Pointwise IFT selected-box data whose compact-image side is a fixed selected
image box, rather than an arbitrary-box containment callback.
-/
structure BoundaryChartSelectedBoxIFTPointContainsAutoData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) where
  /-- Source point where local openness is applied. -/
  sourcePoint : Fin n → Real
  /-- The source point lies in the selected box. -/
  sourcePoint_mem : sourcePoint ∈ lowerZeroFaceDomain a b
  /-- The selected box is a neighborhood of the source point. -/
  source_mem_nhds : lowerZeroFaceDomain a b ∈ 𝓝 sourcePoint
  /-- Strict derivative of the boundary chart transition at the source point. -/
  hasStrictFDerivAt :
    HasStrictFDerivAt (boundaryChartTransition I x0 x1)
      (boundaryChartTransitionTangentMap I x0 x1 sourcePoint) sourcePoint
  /-- Surjectivity of the tangential derivative. -/
  tangentMap_surjective :
    (boundaryChartTransitionTangentMap I x0 x1 sourcePoint).range = ⊤
  /-- Selected source box plus fixed compact-image containment. -/
  selectedImageBoxContainment :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b
      (boundaryChartTransition I x0 x1 sourcePoint)

namespace BoundaryChartSelectedBoxIFTPointContainsAutoData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/-- The selected source boundary box. -/
theorem selectedBox
    (D : BoundaryChartSelectedBoxIFTPointContainsAutoData I x0 x1 ω a b) :
    boundaryChartSelectedBox I x0 x1 ω a b :=
  D.selectedImageBoxContainment.selectedBox

/-- The target point produced by the boundary chart transition. -/
def targetPoint
    (D : BoundaryChartSelectedBoxIFTPointContainsAutoData I x0 x1 ω a b) :
    Fin n → Real :=
  boundaryChartTransition I x0 x1 D.sourcePoint

/-- Local openness generated from the strict derivative and surjectivity fields. -/
theorem image_mem_nhds
    (D : BoundaryChartSelectedBoxIFTPointContainsAutoData I x0 x1 ω a b) :
    (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈
      𝓝 D.targetPoint :=
  boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
    D.hasStrictFDerivAt D.tangentMap_surjective D.source_mem_nhds

/-- Compact-image control for the IFT target point, from the selected image box. -/
theorem compactImageForLocalInverseTargets
    (D : BoundaryChartSelectedBoxIFTPointContainsAutoData I x0 x1 ω a b) :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b
      D.targetPoint := by
  simpa [targetPoint] using
    D.selectedImageBoxContainment.compactImageForLocalInverseTargets

/-- The older point-auto input shape, with compact-image control generated. -/
def toPointAutoInputs
    (D : BoundaryChartSelectedBoxIFTPointContainsAutoData I x0 x1 ω a b) :
    BoundaryChartSelectedBoxPointAutoInputs I x0 x1 ω a b where
  selectedBox := D.selectedBox
  sourcePoint := D.sourcePoint
  sourcePoint_mem := D.sourcePoint_mem
  source_mem_nhds := D.source_mem_nhds
  compactImageForLocalInverseTargets :=
    D.compactImageForLocalInverseTargets

/-- IFT selected image-box containment produces target-image data. -/
theorem exists_autoData
    (D : BoundaryChartSelectedBoxIFTPointContainsAutoData I x0 x1 ω a b) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      D.targetPoint ∈
          lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b
          T.targetLowerCorner T.targetUpperCorner :=
  D.selectedImageBoxContainment.exists_autoData_of_localOpenness
    D.image_mem_nhds

/-- IFT selected image-box containment directly produces oriented-atlas COV. -/
theorem exists_orientedChangeOfVariablesOfOrientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTPointContainsAutoData I x0 x1 ω a b)
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      D.targetPoint ∈
          lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner := by
  rcases D.exists_autoData with ⟨T, hmem, _himageData⟩
  exact ⟨T, hmem, T.orientedChangeOfVariablesOfOrientedAtlas A hx0 hx1⟩

/-- IFT selected image-box containment directly produces oriented-manifold COV. -/
theorem exists_orientedChangeOfVariablesOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryChartSelectedBoxIFTPointContainsAutoData I x0 x1 ω a b) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      D.targetPoint ∈
          lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner := by
  rcases D.exists_autoData with ⟨T, hmem, _himageData⟩
  exact ⟨T, hmem, T.orientedChangeOfVariablesOfOrientedManifold⟩

end BoundaryChartSelectedBoxIFTPointContainsAutoData

/--
Finite local-openness cover with selected source boxes and fixed selected image
boxes on active pieces.
-/
structure BoundaryChartSelectedBoxLocalOpennessContainsCoverAutoData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) (Piece : Type p)
    extends BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece where
  /-- Target point around which local openness selects a target lower-zero box. -/
  targetPoint : Piece → Fin n → Real
  /-- Local-openness neighborhood statement for each active source sub-box. -/
  image_mem_nhds :
    ∀ q, q ∈ activePieces →
      (boundaryChartTransition I x0 x1) ''
          lowerZeroFaceDomain (sourceLowerCorner q) (sourceUpperCorner q) ∈
        𝓝 (targetPoint q)
  /-- Selected source box plus fixed image-box containment for each active piece. -/
  selectedImageBoxContainment :
    ∀ q, q ∈ activePieces →
      BoundaryChartSelectedImageBoxContainment I x0 x1 ω
        (sourceLowerCorner q) (sourceUpperCorner q) (targetPoint q)

namespace BoundaryChartSelectedBoxLocalOpennessContainsCoverAutoData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}

/-- Compact-image control for one active local-openness cover piece. -/
theorem compactImageForLocalInverseTargets
    (D : BoundaryChartSelectedBoxLocalOpennessContainsCoverAutoData
      I x0 x1 ω a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces) :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) (D.targetPoint q) :=
  (D.selectedImageBoxContainment q hq).compactImageForLocalInverseTargets

/-- Forget to the existing local-openness compact-image cover. -/
def toLocalOpennessCompactImageCover
    (D : BoundaryChartSelectedBoxLocalOpennessContainsCoverAutoData
      I x0 x1 ω a b Piece) :
    BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece where
  toBoundaryChartCompactSourceBoxCover := D.toBoundaryChartCompactSourceBoxCover
  targetPoint := D.targetPoint
  image_mem_nhds := D.image_mem_nhds
  compactImageForLocalInverseTargets := D.compactImageForLocalInverseTargets

/-- One active cover piece as selected-box target-image auto data. -/
def selectedBoxTargetImageAutoData
    (D : BoundaryChartSelectedBoxLocalOpennessContainsCoverAutoData
      I x0 x1 ω a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) :=
  D.toLocalOpennessCompactImageCover.toSelectedBoxTargetImageAutoData
    q hq (D.selectedImageBoxContainment q hq).selectedBox

/-- The active-piece auto data exposes image data for its selected target. -/
theorem selectedBoxTargetImageAutoData_imageData
    (D : BoundaryChartSelectedBoxLocalOpennessContainsCoverAutoData
      I x0 x1 ω a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces) :
    boundaryChartSelectedBoxImageData I x0 x1
      (D.sourceLowerCorner q) (D.sourceUpperCorner q)
      (D.selectedBoxTargetImageAutoData q hq).targetLowerCorner
      (D.selectedBoxTargetImageAutoData q hq).targetUpperCorner :=
  (D.selectedBoxTargetImageAutoData q hq).imageData

end BoundaryChartSelectedBoxLocalOpennessContainsCoverAutoData

/--
Finite IFT cover with selected source boxes and fixed selected image boxes on
active pieces.
-/
structure BoundaryChartSelectedBoxIFTContainsCompactCoverAutoData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) (Piece : Type p)
    extends BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece where
  /-- Source point at which local openness is applied for each active piece. -/
  sourcePoint : Piece → Fin n → Real
  /-- The source point lies in the corresponding active source box. -/
  sourcePoint_mem :
    ∀ q, q ∈ activePieces →
      sourcePoint q ∈ lowerZeroFaceDomain (sourceLowerCorner q) (sourceUpperCorner q)
  /-- The corresponding active source box is a neighborhood of the source point. -/
  source_mem_nhds :
    ∀ q, q ∈ activePieces →
      lowerZeroFaceDomain (sourceLowerCorner q) (sourceUpperCorner q) ∈
        𝓝 (sourcePoint q)
  /-- Strict derivative of the boundary chart transition on each active piece. -/
  hasStrictFDerivAt :
    ∀ q, q ∈ activePieces →
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 (sourcePoint q))
        (sourcePoint q)
  /-- Surjectivity of the tangential derivative on each active piece. -/
  tangentMap_surjective :
    ∀ q, q ∈ activePieces →
      (boundaryChartTransitionTangentMap I x0 x1 (sourcePoint q)).range = ⊤
  /-- Selected source box plus fixed image-box containment for each active piece. -/
  selectedImageBoxContainment :
    ∀ q, q ∈ activePieces →
      BoundaryChartSelectedImageBoxContainment I x0 x1 ω
        (sourceLowerCorner q) (sourceUpperCorner q)
        (boundaryChartTransition I x0 x1 (sourcePoint q))

namespace BoundaryChartSelectedBoxIFTContainsCompactCoverAutoData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}

/-- Target point for one finite-cover source piece. -/
def targetPoint
    (D : BoundaryChartSelectedBoxIFTContainsCompactCoverAutoData
      I x0 x1 ω a b Piece)
    (q : Piece) : Fin n → Real :=
  boundaryChartTransition I x0 x1 (D.sourcePoint q)

/-- Compact-image control for one active IFT cover piece. -/
theorem compactImageForLocalInverseTargets
    (D : BoundaryChartSelectedBoxIFTContainsCompactCoverAutoData
      I x0 x1 ω a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces) :
    boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) (D.targetPoint q) := by
  simpa [targetPoint] using
    (D.selectedImageBoxContainment q hq).compactImageForLocalInverseTargets

/-- Forget to the existing IFT compact-image cover data. -/
def toIFTCompactImageCoverData
    (D : BoundaryChartSelectedBoxIFTContainsCompactCoverAutoData
      I x0 x1 ω a b Piece) :
    BoundaryChartIFTCompactImageCoverData I x0 x1 a b Piece where
  toBoundaryChartCompactSourceBoxCover := D.toBoundaryChartCompactSourceBoxCover
  sourcePoint := D.sourcePoint
  sourcePoint_mem := D.sourcePoint_mem
  source_mem_nhds := D.source_mem_nhds
  hasStrictFDerivAt := D.hasStrictFDerivAt
  tangentMap_surjective := D.tangentMap_surjective
  compactImageForLocalInverseTargets := D.compactImageForLocalInverseTargets

/-- Local-openness compact-image cover generated from the IFT data. -/
def toLocalOpennessCompactImageCover
    (D : BoundaryChartSelectedBoxIFTContainsCompactCoverAutoData
      I x0 x1 ω a b Piece) :
    BoundaryChartLocalOpennessCompactImageCover I x0 x1 a b Piece :=
  D.toIFTCompactImageCoverData.toLocalOpennessCompactImageCover

/-- One active cover piece as selected-box target-image auto data. -/
def selectedBoxTargetImageAutoData
    (D : BoundaryChartSelectedBoxIFTContainsCompactCoverAutoData
      I x0 x1 ω a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
      (D.sourceLowerCorner q) (D.sourceUpperCorner q) :=
  D.toIFTCompactImageCoverData.toSelectedBoxTargetImageAutoData
    q hq (D.selectedImageBoxContainment q hq).selectedBox

/-- The active-piece auto data exposes image data for its selected target. -/
theorem selectedBoxTargetImageAutoData_imageData
    (D : BoundaryChartSelectedBoxIFTContainsCompactCoverAutoData
      I x0 x1 ω a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces) :
    boundaryChartSelectedBoxImageData I x0 x1
      (D.sourceLowerCorner q) (D.sourceUpperCorner q)
      (D.selectedBoxTargetImageAutoData q hq).targetLowerCorner
      (D.selectedBoxTargetImageAutoData q hq).targetUpperCorner :=
  (D.selectedBoxTargetImageAutoData q hq).imageData

end BoundaryChartSelectedBoxIFTContainsCompactCoverAutoData

end ManifoldBoundary

end Stokes

end
