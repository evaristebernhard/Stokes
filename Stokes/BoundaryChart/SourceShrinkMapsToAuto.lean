import Stokes.BoundaryChart.SelectedBoxContainsAuto
import Stokes.BoundaryChart.TargetBoxSourceShrinkIFT

/-!
# Source-shrink `MapsTo` automation

The source-shrink route already selects a smaller source boundary box and a
target lower-zero box whose image/local-inverse data match.  This file exposes
that data in the shapes consumed by the selected-box target-image and oriented
COV APIs, so callers no longer have to restate the same `MapsTo` or image
subset facts by hand.
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

namespace BoundaryChartSourceShrinkMapsToData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real} {u y : Fin n → Real}

/-- The source-shrink `MapsTo` field, named in the selected-target vocabulary. -/
theorem mapsTo_selectedTarget
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u) :
    MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner)
      (lowerZeroFaceDomain c d) :=
  D.mapsTo_target

/-- The selected shrunken source image lies in the selected target box. -/
theorem image_subset_selectedTarget
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u) :
    (boundaryChartTransition I x0 x1) ''
        lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner ⊆
      lowerZeroFaceDomain c d := by
  intro z hz
  rcases hz with ⟨v, hv, rfl⟩
  exact D.mapsTo_selectedTarget hv

/-- Coordinate compact-image form of the selected source-shrink target box. -/
theorem compactCoordinateImageBoxSelection_selectedTarget
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u) :
    compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner)
      (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d) :=
  compactCoordinateImageBoxSelection_of_boundaryImage_subset_lowerZeroFaceDomain
    (I := I) (x0 := x0) (x1 := x1)
    (a := D.sourceLowerCorner) (b := D.sourceUpperCorner)
    (c := c) (d := d) D.image_subset_selectedTarget

/-- Source-shrink maps-to data plus the matching local inverse as selected-box
target-image auto data. -/
def selectedBoxTargetImageAutoDataOfLocalInverse
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u)
    (hc0 : c 0 = 0) (hle : c ≤ d)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner :=
  BoundaryChartSelectedBoxTargetImageAutoData.ofTargetBoxSelection hbox
    (D.targetBoxSelection hc0 hle hlocal)

/-- The auto data produced from source-shrink maps-to data keeps the selected
target corners. -/
@[simp]
theorem selectedBoxTargetImageAutoDataOfLocalInverse_targetLowerCorner
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u)
    (hc0 : c 0 = 0) (hle : c ≤ d)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner) :
    (D.selectedBoxTargetImageAutoDataOfLocalInverse hc0 hle hlocal hbox).targetLowerCorner = c :=
  rfl

/-- The auto data produced from source-shrink maps-to data keeps the selected
target corners. -/
@[simp]
theorem selectedBoxTargetImageAutoDataOfLocalInverse_targetUpperCorner
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u)
    (hc0 : c 0 = 0) (hle : c ≤ d)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner) :
    (D.selectedBoxTargetImageAutoDataOfLocalInverse hc0 hle hlocal hbox).targetUpperCorner = d :=
  rfl

/-- Image-data projection for the source-shrink selected target. -/
theorem selectedBoxTargetImageAutoDataOfLocalInverse_imageData
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u)
    (hc0 : c 0 = 0) (hle : c ≤ d)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner) :
    boundaryChartSelectedBoxImageData I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner c d := by
  simpa using
    (D.selectedBoxTargetImageAutoDataOfLocalInverse
      (ω := ω) hc0 hle hlocal hbox).imageData

/-- Oriented-atlas COV directly from source-shrink maps-to data and the matching
local inverse. -/
theorem orientedChangeOfVariablesOfLocalInverseOrientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u)
    (hc0 : c 0 = 0) (hle : c ≤ d)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner c d := by
  simpa using
    (D.selectedBoxTargetImageAutoDataOfLocalInverse
      (ω := ω) hc0 hle hlocal hbox).orientedChangeOfVariablesOfOrientedAtlas
        A hx0 hx1

/-- Oriented-manifold COV directly from source-shrink maps-to data and the
matching local inverse. -/
theorem orientedChangeOfVariablesOfLocalInverseOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u)
    (hc0 : c 0 = 0) (hle : c ≤ d)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner c d := by
  simpa using
    (D.selectedBoxTargetImageAutoDataOfLocalInverse
      (ω := ω) hc0 hle hlocal hbox).orientedChangeOfVariablesOfOrientedManifold

/-- Build the selected-image-box containment shape from a source-shrink target
box plus the remaining future-target containment check. -/
def selectedImageBoxContainmentOfTargetContains
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u)
    (hc0 : c 0 = 0) (hle : c ≤ d)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (hcontains :
      ∀ e f : Fin (n + 1) → Real, e 0 = 0 → e ≤ f →
        y ∈ lowerZeroFaceDomain e f →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner e f →
            Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d) ⊆
              Set.Icc (boundaryFaceLowerCorner e) (boundaryFaceUpperCorner f)) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner y where
  selectedBox := hbox
  imageBoxForLocalInverseTargets :=
    BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets.ofTargetBoxSelection
      (D.targetBoxSelection hc0 hle hlocal) hcontains

end BoundaryChartSourceShrinkMapsToData

namespace BoundaryChartSourceShrinkInverseTargetBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d e f : Fin (n + 1) → Real} {u y : Fin n → Real}

/-- The completed source-shrink record exposes the selected target `MapsTo`. -/
theorem mapsTo_selectedTarget
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y) :
    MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner)
      (lowerZeroFaceDomain e f) :=
  D.mapsTo_target

/-- Image-subset projection of the completed source-shrink selected target. -/
theorem image_subset_selectedTarget
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y) :
    (boundaryChartTransition I x0 x1) ''
        lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner ⊆
      lowerZeroFaceDomain e f := by
  intro z hz
  rcases hz with ⟨v, hv, rfl⟩
  exact D.mapsTo_selectedTarget hv

/-- Completed source-shrink data as selected-box target-image auto data. -/
def toSelectedBoxTargetImageAutoData
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner :=
  BoundaryChartSelectedBoxTargetImageAutoData.ofTargetBoxSelection hbox
    D.targetBoxSelection

@[simp]
theorem toSelectedBoxTargetImageAutoData_targetLowerCorner
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner) :
    (D.toSelectedBoxTargetImageAutoData hbox).targetLowerCorner = e :=
  rfl

@[simp]
theorem toSelectedBoxTargetImageAutoData_targetUpperCorner
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner) :
    (D.toSelectedBoxTargetImageAutoData hbox).targetUpperCorner = f :=
  rfl

/-- Image-data projection through selected-box target-image auto data. -/
theorem toSelectedBoxTargetImageAutoData_imageData
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner) :
    boundaryChartSelectedBoxImageData I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner e f := by
  simpa using (D.toSelectedBoxTargetImageAutoData (ω := ω) hbox).imageData

/-- Oriented-atlas COV from completed source-shrink target-box data. -/
theorem orientedChangeOfVariablesOfOrientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner e f := by
  simpa using
    (D.toSelectedBoxTargetImageAutoData (ω := ω) hbox).orientedChangeOfVariablesOfOrientedAtlas
      A hx0 hx1

/-- Oriented-manifold COV from completed source-shrink target-box data. -/
theorem orientedChangeOfVariablesOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner e f := by
  simpa using
    (D.toSelectedBoxTargetImageAutoData (ω := ω) hbox).orientedChangeOfVariablesOfOrientedManifold

/-- Completed source-shrink data as the selected-image-box containment shape,
assuming only the remaining future-target containment of the selected target
image box. -/
def toSelectedImageBoxContainmentOfTargetContains
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (hcontains :
      ∀ c' d' : Fin (n + 1) → Real, c' 0 = 0 → c' ≤ d' →
        y ∈ lowerZeroFaceDomain c' d' →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner c' d' →
            Set.Icc (boundaryFaceLowerCorner e) (boundaryFaceUpperCorner f) ⊆
              Set.Icc (boundaryFaceLowerCorner c') (boundaryFaceUpperCorner d')) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner y where
  selectedBox := hbox
  imageBoxForLocalInverseTargets :=
    BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets.ofTargetBoxSelection
      D.targetBoxSelection hcontains

end BoundaryChartSourceShrinkInverseTargetBoxData

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real} {u y : Fin n → Real}

/-- `MapsTo` projection of synchronized source-shrink local-homeomorphism data. -/
theorem mapsTo_selectedTarget
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y) :
    MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner)
      (lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner) :=
  D.mapsTo_target

/-- Image-subset projection of synchronized source-shrink local-homeomorphism data. -/
theorem image_subset_selectedTarget
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y) :
    (boundaryChartTransition I x0 x1) ''
        lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner ⊆
      lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner := by
  intro z hz
  rcases hz with ⟨v, hv, rfl⟩
  exact D.mapsTo_selectedTarget hv

/-- The selected target box supplied by source-shrink data gives the selected
image-box containment shape once future local-inverse targets are known to
contain that selected image box. -/
def toSelectedImageBoxContainmentOfTargetContains
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (hcontains :
      ∀ c' d' : Fin (n + 1) → Real, c' 0 = 0 → c' ≤ d' →
        y ∈ lowerZeroFaceDomain c' d' →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner c' d' →
            Set.Icc (boundaryFaceLowerCorner D.targetLowerCorner)
                (boundaryFaceUpperCorner D.targetUpperCorner) ⊆
              Set.Icc (boundaryFaceLowerCorner c') (boundaryFaceUpperCorner d')) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner y where
  selectedBox := hbox
  imageBoxForLocalInverseTargets :=
    BoundaryChartCompactCoordinateImageBoxForLocalInverseTargets.ofTargetBoxSelection
      D.targetBoxSelection hcontains

end BoundaryChartSourceShrinkOpenPartialHomeomorphData

end ManifoldBoundary

end Stokes

end
