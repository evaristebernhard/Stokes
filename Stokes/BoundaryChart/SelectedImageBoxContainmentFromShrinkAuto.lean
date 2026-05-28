import Stokes.BoundaryChart.SelectedImageBoxFromTargetAuto
import Stokes.BoundaryChart.SourceShrinkMapsToAuto

/-!
# Selected image-box containment from target shrink data

`SelectedImageBoxFromTargetAuto` still exposes the callback saying that the
already selected target image box is contained in every later local-inverse
target box.  This file records the two reusable ways that callback normally
arises:

* directly from lower-zero target-box containment;
* from a selected target box lying in an ambient target box, with the ambient
  target box lying in all later targets.
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

/-- Lower-zero target-box containment is exactly tangential `Icc` containment. -/
theorem boundaryFaceIcc_subset_of_lowerZeroFaceDomain_subset {n : Nat}
    {c d e f : Fin (n + 1) → Real}
    (hsubset : lowerZeroFaceDomain c d ⊆ lowerZeroFaceDomain e f) :
    Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d) ⊆
      Set.Icc (boundaryFaceLowerCorner e) (boundaryFaceUpperCorner f) := by
  simpa [lowerZeroFaceDomain_eq_Icc_boundaryFaceCorners] using hsubset

/-- Tangential `Icc` containment rephrased as lower-zero target-box containment. -/
theorem lowerZeroFaceDomain_subset_of_boundaryFaceIcc_subset {n : Nat}
    {c d e f : Fin (n + 1) → Real}
    (hsubset :
      Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d) ⊆
        Set.Icc (boundaryFaceLowerCorner e) (boundaryFaceUpperCorner f)) :
    lowerZeroFaceDomain c d ⊆ lowerZeroFaceDomain e f := by
  simpa [lowerZeroFaceDomain_eq_Icc_boundaryFaceCorners] using hsubset

/-- The selected target box is contained in every later local-inverse target. -/
structure BoundaryChartSelectedTargetContainsLaterTargets {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b selectedLower selectedUpper : Fin (n + 1) → Real)
    (y : Fin n → Real) where
  /-- Later local-inverse target boxes contain the fixed selected target box. -/
  selectedTarget_subset_laterTargets :
    ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
      y ∈ lowerZeroFaceDomain c d →
        boundaryChartLocalInverseData I x0 x1 a b c d →
          lowerZeroFaceDomain selectedLower selectedUpper ⊆ lowerZeroFaceDomain c d

namespace BoundaryChartSelectedTargetContainsLaterTargets

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b selectedLower selectedUpper : Fin (n + 1) → Real}
variable {y : Fin n → Real}

/-- Convert the natural lower-zero containment record to the callback expected by
the selected-image-box constructors. -/
theorem target_contains_selectedImageBox
    (D : BoundaryChartSelectedTargetContainsLaterTargets
      I x0 x1 a b selectedLower selectedUpper y) :
    ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
      y ∈ lowerZeroFaceDomain c d →
        boundaryChartLocalInverseData I x0 x1 a b c d →
          Set.Icc (boundaryFaceLowerCorner selectedLower)
              (boundaryFaceUpperCorner selectedUpper) ⊆
            Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d) := by
  intro c d hc0 hle hy hlocal
  exact boundaryFaceIcc_subset_of_lowerZeroFaceDomain_subset
    (D.selectedTarget_subset_laterTargets c d hc0 hle hy hlocal)

/-- Constructor from direct lower-zero target containment. -/
def ofLowerZeroSubset
    (hsubset :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            lowerZeroFaceDomain selectedLower selectedUpper ⊆
              lowerZeroFaceDomain c d) :
    BoundaryChartSelectedTargetContainsLaterTargets
      I x0 x1 a b selectedLower selectedUpper y where
  selectedTarget_subset_laterTargets := hsubset

/-- Constructor from coordinatewise shrink inequalities. -/
def ofTangentBounds
    (hlower :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            ∀ i : Fin n, c i.succ ≤ selectedLower i.succ)
    (hupper :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            ∀ i : Fin n, selectedUpper i.succ ≤ d i.succ) :
    BoundaryChartSelectedTargetContainsLaterTargets
      I x0 x1 a b selectedLower selectedUpper y where
  selectedTarget_subset_laterTargets := by
    intro c d hc0 hle hy hlocal
    exact lowerZeroFaceDomain_subset_of_tangent_bounds
      (a := c) (b := d) (a' := selectedLower) (b' := selectedUpper)
      (hlower c d hc0 hle hy hlocal) (hupper c d hc0 hle hy hlocal)

/-- Transport selected-target containment through a containing ambient target. -/
def ofSubsetAmbient {ambientLower ambientUpper : Fin (n + 1) → Real}
    (hselected_subset_ambient :
      lowerZeroFaceDomain selectedLower selectedUpper ⊆
        lowerZeroFaceDomain ambientLower ambientUpper)
    (hambient :
      BoundaryChartSelectedTargetContainsLaterTargets
        I x0 x1 a b ambientLower ambientUpper y) :
    BoundaryChartSelectedTargetContainsLaterTargets
      I x0 x1 a b selectedLower selectedUpper y where
  selectedTarget_subset_laterTargets := by
    intro c d hc0 hle hy hlocal
    exact hselected_subset_ambient.trans
      (hambient.selectedTarget_subset_laterTargets c d hc0 hle hy hlocal)

end BoundaryChartSelectedTargetContainsLaterTargets

/-- Ambient target box containment for the selected source box.  This is the
record used when source-shrink data already proves
`selectedTarget ⊆ ambientTarget`; callers only provide that the ambient target
is contained in the later local-inverse targets. -/
abbrev BoundaryChartAmbientTargetContainsLaterTargets {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b ambientLower ambientUpper : Fin (n + 1) → Real)
    (y : Fin n → Real) :=
  BoundaryChartSelectedTargetContainsLaterTargets
    I x0 x1 a b ambientLower ambientUpper y

namespace BoundaryChartTargetBoxSelection

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {y : Fin n → Real}

/-- Selected-image-box containment from a target box and lower-zero containment
in later local-inverse target boxes. -/
def selectedImageBoxContainmentOfLowerZeroSubsetLater
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hlater :
      BoundaryChartSelectedTargetContainsLaterTargets
        I x0 x1 a b target.lowerCorner target.upperCorner y) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y :=
  BoundaryChartSelectedImageBoxContainment.ofTargetBoxSelection
    (I := I) (x0 := x0) (x1 := x1) (ω := ω) (a := a) (b := b)
    (y := y) hbox target hlater.target_contains_selectedImageBox

/-- Tangential bound spelling of
`selectedImageBoxContainmentOfLowerZeroSubsetLater`. -/
def selectedImageBoxContainmentOfTangentBoundsLater
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hlower :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            ∀ i : Fin n, c i.succ ≤ target.lowerCorner i.succ)
    (hupper :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            ∀ i : Fin n, target.upperCorner i.succ ≤ d i.succ) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω a b y :=
  target.selectedImageBoxContainmentOfLowerZeroSubsetLater hbox
    (BoundaryChartSelectedTargetContainsLaterTargets.ofTangentBounds
      (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
      (selectedLower := target.lowerCorner)
      (selectedUpper := target.upperCorner) (y := y) hlower hupper)

end BoundaryChartTargetBoxSelection

namespace BoundaryChartSourceShrinkMapsToData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real} {u y : Fin n → Real}

/-- Source-shrink selected target containment from lower-zero containment in
later local-inverse targets. -/
def selectedTargetContainsLaterTargetsOfLowerZeroSubset
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u)
    (hsubset :
      ∀ e f : Fin (n + 1) → Real, e 0 = 0 → e ≤ f →
        y ∈ lowerZeroFaceDomain e f →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner e f →
            lowerZeroFaceDomain c d ⊆ lowerZeroFaceDomain e f) :
    BoundaryChartSelectedTargetContainsLaterTargets I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner c d y :=
  BoundaryChartSelectedTargetContainsLaterTargets.ofLowerZeroSubset hsubset

/-- Source-shrink selected target containment from coordinatewise shrink
inequalities. -/
def selectedTargetContainsLaterTargetsOfTangentBounds
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u)
    (hlower :
      ∀ e f : Fin (n + 1) → Real, e 0 = 0 → e ≤ f →
        y ∈ lowerZeroFaceDomain e f →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner e f →
            ∀ i : Fin n, e i.succ ≤ c i.succ)
    (hupper :
      ∀ e f : Fin (n + 1) → Real, e 0 = 0 → e ≤ f →
        y ∈ lowerZeroFaceDomain e f →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner e f →
            ∀ i : Fin n, d i.succ ≤ f i.succ) :
    BoundaryChartSelectedTargetContainsLaterTargets I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner c d y :=
  BoundaryChartSelectedTargetContainsLaterTargets.ofTangentBounds hlower hupper

/-- Source-shrink selected-image-box containment with the remaining containment
expressed as lower-zero target-box inclusion. -/
def selectedImageBoxContainmentOfLowerZeroSubsetLater
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u)
    (hc0 : c 0 = 0) (hle : c ≤ d)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (hsubset :
      ∀ e f : Fin (n + 1) → Real, e 0 = 0 → e ≤ f →
        y ∈ lowerZeroFaceDomain e f →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner e f →
            lowerZeroFaceDomain c d ⊆ lowerZeroFaceDomain e f) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner y :=
  D.selectedImageBoxContainmentOfTargetContains hc0 hle hlocal hbox
    (D.selectedTargetContainsLaterTargetsOfLowerZeroSubset hsubset).target_contains_selectedImageBox

/-- Source-shrink selected-image-box containment with coordinatewise later-target
shrink inequalities. -/
def selectedImageBoxContainmentOfTangentBoundsLater
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u)
    (hc0 : c 0 = 0) (hle : c ≤ d)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (hlower :
      ∀ e f : Fin (n + 1) → Real, e 0 = 0 → e ≤ f →
        y ∈ lowerZeroFaceDomain e f →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner e f →
            ∀ i : Fin n, e i.succ ≤ c i.succ)
    (hupper :
      ∀ e f : Fin (n + 1) → Real, e 0 = 0 → e ≤ f →
        y ∈ lowerZeroFaceDomain e f →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner e f →
            ∀ i : Fin n, d i.succ ≤ f i.succ) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner y :=
  D.selectedImageBoxContainmentOfTargetContains hc0 hle hlocal hbox
    (D.selectedTargetContainsLaterTargetsOfTangentBounds
      hlower hupper).target_contains_selectedImageBox

end BoundaryChartSourceShrinkMapsToData

namespace BoundaryChartSourceShrinkInverseTargetBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d e f : Fin (n + 1) → Real} {u y : Fin n → Real}

/-- The selected target box of completed source-shrink data lies in its ambient
target box, in the tangential `Icc` spelling. -/
theorem selectedTarget_subset_ambientIcc
    (D : BoundaryChartSourceShrinkInverseTargetBoxData
      I x0 x1 a b c d e f u y) :
    Set.Icc (boundaryFaceLowerCorner e) (boundaryFaceUpperCorner f) ⊆
      Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d) :=
  boundaryFaceIcc_subset_of_lowerZeroFaceDomain_subset D.targetSubset_original

/-- Completed source-shrink data gives later-target containment once the
ambient target box is known to be contained in those later targets. -/
def selectedTargetContainsLaterTargetsOfAmbient
    (D : BoundaryChartSourceShrinkInverseTargetBoxData
      I x0 x1 a b c d e f u y)
    (hambient :
      BoundaryChartAmbientTargetContainsLaterTargets I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d y) :
    BoundaryChartSelectedTargetContainsLaterTargets I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner e f y :=
  BoundaryChartSelectedTargetContainsLaterTargets.ofSubsetAmbient
    D.targetSubset_original hambient

/-- Ambient-target containment from coordinatewise later-target shrink
inequalities. -/
def ambientTargetContainsLaterTargetsOfTangentBounds
    (D : BoundaryChartSourceShrinkInverseTargetBoxData
      I x0 x1 a b c d e f u y)
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
    BoundaryChartAmbientTargetContainsLaterTargets I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner c d y :=
  BoundaryChartSelectedTargetContainsLaterTargets.ofTangentBounds hlower hupper

/-- Completed source-shrink data as selected-image-box containment, using an
ambient-target containment record. -/
def toSelectedImageBoxContainmentOfAmbientContainsLaterTargets
    (D : BoundaryChartSourceShrinkInverseTargetBoxData
      I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (hambient :
      BoundaryChartAmbientTargetContainsLaterTargets I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d y) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner y :=
  D.toSelectedImageBoxContainmentOfTargetContains hbox
    (D.selectedTargetContainsLaterTargetsOfAmbient
      hambient).target_contains_selectedImageBox

/-- Completed source-shrink data as selected-image-box containment, using
coordinatewise containment of the ambient target in later targets. -/
def toSelectedImageBoxContainmentOfAmbientTangentBounds
    (D : BoundaryChartSourceShrinkInverseTargetBoxData
      I x0 x1 a b c d e f u y)
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
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner y :=
  D.toSelectedImageBoxContainmentOfAmbientContainsLaterTargets hbox
    (D.ambientTargetContainsLaterTargetsOfTangentBounds hlower hupper)

end BoundaryChartSourceShrinkInverseTargetBoxData

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real} {u y : Fin n → Real}

/-- The selected target box of open-partial-homeomorphism source-shrink data
lies in its ambient target box, in the tangential `Icc` spelling. -/
theorem selectedTarget_subset_ambientIcc
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData
      I x0 x1 a b c d u y) :
    Set.Icc (boundaryFaceLowerCorner D.targetLowerCorner)
        (boundaryFaceUpperCorner D.targetUpperCorner) ⊆
      Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d) :=
  boundaryFaceIcc_subset_of_lowerZeroFaceDomain_subset D.targetSubset_original

/-- Open-partial-homeomorphism source-shrink data gives later-target containment
once the ambient target box is contained in those later targets. -/
def selectedTargetContainsLaterTargetsOfAmbient
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData
      I x0 x1 a b c d u y)
    (hambient :
      BoundaryChartAmbientTargetContainsLaterTargets I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d y) :
    BoundaryChartSelectedTargetContainsLaterTargets I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner
      D.targetLowerCorner D.targetUpperCorner y :=
  BoundaryChartSelectedTargetContainsLaterTargets.ofSubsetAmbient
    D.targetSubset_original hambient

/-- Ambient-target containment from coordinatewise later-target shrink
inequalities. -/
def ambientTargetContainsLaterTargetsOfTangentBounds
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData
      I x0 x1 a b c d u y)
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
    BoundaryChartAmbientTargetContainsLaterTargets I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner c d y :=
  BoundaryChartSelectedTargetContainsLaterTargets.ofTangentBounds hlower hupper

/-- Open-partial-homeomorphism source-shrink data as selected-image-box
containment, using an ambient-target containment record. -/
def toSelectedImageBoxContainmentOfAmbientContainsLaterTargets
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData
      I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 ω
        D.sourceLowerCorner D.sourceUpperCorner)
    (hambient :
      BoundaryChartAmbientTargetContainsLaterTargets I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d y) :
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner y :=
  D.toSelectedImageBoxContainmentOfTargetContains hbox
    (D.selectedTargetContainsLaterTargetsOfAmbient
      hambient).target_contains_selectedImageBox

/-- Open-partial-homeomorphism source-shrink data as selected-image-box
containment, using coordinatewise containment of the ambient target in later
targets. -/
def toSelectedImageBoxContainmentOfAmbientTangentBounds
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData
      I x0 x1 a b c d u y)
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
    BoundaryChartSelectedImageBoxContainment I x0 x1 ω
      D.sourceLowerCorner D.sourceUpperCorner y :=
  D.toSelectedImageBoxContainmentOfAmbientContainsLaterTargets hbox
    (D.ambientTargetContainsLaterTargetsOfTangentBounds hlower hupper)

end BoundaryChartSourceShrinkOpenPartialHomeomorphData

end ManifoldBoundary

end Stokes

end
