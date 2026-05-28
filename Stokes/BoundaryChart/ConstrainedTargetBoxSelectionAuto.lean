import Stokes.BoundaryChart.LaterTargetShrinkFromSelectionAuto
import Stokes.BoundaryChart.SelectedBoxCOVFromOrientationAuto

/-!
# Constrained target-box selection

The earlier local-openness automation quantified over every later target box
that a local-inverse theorem might select.  That is too strong for the intended
box-selection strategy: the caller should select a later target box in a
controlled way, with enough room to contain the fixed selected image box, and
then use that chosen box directly.

This file packages that controlled choice.  It also provides an adapter back to
the older `BoundaryChartLaterTargetShrinkData` API when a downstream selection
policy explicitly guarantees that all future targets contain the controlled
box.
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
Controlled later target-box data around a boundary target point.

The selected target image box is described by `selectedLower` and
`selectedUpper`.  The fields `later_lower_le_selected_lower` and
`selected_upper_le_later_upper` say that the newly chosen later box contains
that selected box.  The neighborhood/subset fields record that this choice was
made inside a prescribed target-side set `U`.

Unlike the older local-openness callback, this record fixes one concrete target
box and carries the compact-image/local-inverse halves needed for boundary COV.
-/
structure BoundaryChartControlledTargetBoxSelectionData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b selectedLower selectedUpper : Fin (n + 1) → Real)
    (y : Fin n → Real) (U : Set (Fin n → Real)) where
  /-- Lower corner of the controlled later target box. -/
  laterLowerCorner : Fin (n + 1) → Real
  /-- Upper corner of the controlled later target box. -/
  laterUpperCorner : Fin (n + 1) → Real
  /-- Boundary convention for the controlled target lower corner. -/
  laterLowerCorner_zero : laterLowerCorner 0 = 0
  /-- Coordinatewise order of the controlled target corners. -/
  laterLower_le_laterUpper : laterLowerCorner ≤ laterUpperCorner
  /-- The target point lies in the controlled target box. -/
  targetPoint_mem :
    y ∈ lowerZeroFaceDomain laterLowerCorner laterUpperCorner
  /-- The controlled target box is a neighborhood of the target point. -/
  laterTarget_mem_nhds :
    lowerZeroFaceDomain laterLowerCorner laterUpperCorner ∈ 𝓝 y
  /-- The controlled target box lies in the prescribed target-side set. -/
  laterTarget_subset_set :
    lowerZeroFaceDomain laterLowerCorner laterUpperCorner ⊆ U
  /-- The controlled lower corner is below the selected lower corner. -/
  later_lower_le_selected_lower :
    ∀ i : Fin n, laterLowerCorner i.succ ≤ selectedLower i.succ
  /-- The selected upper corner is below the controlled upper corner. -/
  selected_upper_le_later_upper :
    ∀ i : Fin n, selectedUpper i.succ ≤ laterUpperCorner i.succ
  /-- Compact-image containment for the controlled target box. -/
  compactImage :
    boundaryChartCompactImageBoxSelection I x0 x1 a b
      laterLowerCorner laterUpperCorner
  /-- Local right-inverse data on the controlled target box. -/
  localInverse :
    boundaryChartLocalInverseData I x0 x1 a b
      laterLowerCorner laterUpperCorner

namespace BoundaryChartControlledTargetBoxSelectionData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {a b selectedLower selectedUpper : Fin (n + 1) → Real}
variable {y : Fin n → Real} {U : Set (Fin n → Real)}

/-- The fixed selected target box lies in the controlled later target box. -/
theorem selectedTarget_subset_laterTarget
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U) :
    lowerZeroFaceDomain selectedLower selectedUpper ⊆
      lowerZeroFaceDomain D.laterLowerCorner D.laterUpperCorner :=
  lowerZeroFaceDomain_subset_of_tangent_bounds
    D.later_lower_le_selected_lower D.selected_upper_le_later_upper

/-- Tangential `Icc` spelling of `selectedTarget_subset_laterTarget`. -/
theorem selectedTargetIcc_subset_laterTargetIcc
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U) :
    Set.Icc (boundaryFaceLowerCorner selectedLower)
        (boundaryFaceUpperCorner selectedUpper) ⊆
      Set.Icc (boundaryFaceLowerCorner D.laterLowerCorner)
        (boundaryFaceUpperCorner D.laterUpperCorner) :=
  boundaryFaceIcc_subset_of_lowerZeroFaceDomain_subset
    D.selectedTarget_subset_laterTarget

/-- Package the controlled target as the standard target-box selection. -/
def targetBoxSelection
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U) :
    BoundaryChartTargetBoxSelection I x0 x1 a b :=
  BoundaryChartTargetBoxSelection.mkOfCompactImageLocalInverseData
    D.laterLowerCorner D.laterUpperCorner D.laterLowerCorner_zero
    D.laterLower_le_laterUpper D.compactImage D.localInverse

/-- Image data for the controlled target box. -/
theorem imageData
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U) :
    boundaryChartSelectedBoxImageData I x0 x1 a b
      D.laterLowerCorner D.laterUpperCorner :=
  D.targetBoxSelection.imageData

/-- Build selected-box target-image auto-data from the controlled target. -/
def toSelectedBoxTargetImageAutoData {ω : ManifoldForm I M n}
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b :=
  BoundaryChartSelectedBoxTargetImageAutoData.ofTargetBoxSelection
    hbox D.targetBoxSelection

/-- The auto-data produced from a controlled target remembers the controlled lower corner. -/
@[simp]
theorem toSelectedBoxTargetImageAutoData_targetLowerCorner
    {ω : ManifoldForm I M n}
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    (D.toSelectedBoxTargetImageAutoData hbox).targetLowerCorner =
      D.laterLowerCorner :=
  rfl

/-- The auto-data produced from a controlled target remembers the controlled upper corner. -/
@[simp]
theorem toSelectedBoxTargetImageAutoData_targetUpperCorner
    {ω : ManifoldForm I M n}
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    (D.toSelectedBoxTargetImageAutoData hbox).targetUpperCorner =
      D.laterUpperCorner :=
  rfl

/-- The target point membership projected through the selected-box auto data. -/
theorem targetPoint_mem_autoData
    {ω : ManifoldForm I M n}
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    y ∈ lowerZeroFaceDomain
      (D.toSelectedBoxTargetImageAutoData hbox).targetLowerCorner
      (D.toSelectedBoxTargetImageAutoData hbox).targetUpperCorner := by
  simpa using D.targetPoint_mem

/-- Direct oriented-atlas COV for the controlled target box. -/
theorem orientedChangeOfVariablesOfOrientedAtlas
    [IsManifold I 1 M] {ω : ManifoldForm I M n}
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
      D.laterLowerCorner D.laterUpperCorner :=
  (D.toSelectedBoxTargetImageAutoData hbox).orientedChangeOfVariablesOfOrientedAtlas
    A hx0 hx1

/-- Direct oriented-manifold COV for the controlled target box. -/
theorem orientedChangeOfVariablesOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    {ω : ManifoldForm I M n}
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
      D.laterLowerCorner D.laterUpperCorner :=
  (D.toSelectedBoxTargetImageAutoData hbox).orientedChangeOfVariablesOfOrientedManifold

/-- Existential oriented-atlas spelling, matching the local-openness output shape. -/
theorem exists_orientedChangeOfVariablesOfOrientedAtlas
    [IsManifold I 1 M] {ω : ManifoldForm I M n}
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner := by
  refine ⟨D.toSelectedBoxTargetImageAutoData hbox, ?_, ?_⟩
  · exact D.targetPoint_mem_autoData hbox
  · simpa using D.orientedChangeOfVariablesOfOrientedAtlas hbox A hx0 hx1

/-- Existential oriented-manifold spelling, matching the local-openness output shape. -/
theorem exists_orientedChangeOfVariablesOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    {ω : ManifoldForm I M n}
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    ∃ T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 ω a b,
      y ∈ lowerZeroFaceDomain T.targetLowerCorner T.targetUpperCorner ∧
        boundaryChartOrientedChangeOfVariables I x0 x1 ω a b
          T.targetLowerCorner T.targetUpperCorner := by
  refine ⟨D.toSelectedBoxTargetImageAutoData hbox, ?_, ?_⟩
  · exact D.targetPoint_mem_autoData hbox
  · simpa using D.orientedChangeOfVariablesOfOrientedManifold hbox

/--
If a later selection policy guarantees that every future target contains the
controlled target box, then the older selected-target-containment record follows.
-/
def toSelectedTargetContainsLaterTargetsOfFutureSubset
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U)
    (hfuture :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            lowerZeroFaceDomain D.laterLowerCorner D.laterUpperCorner ⊆
              lowerZeroFaceDomain c d) :
    BoundaryChartSelectedTargetContainsLaterTargets
      I x0 x1 a b selectedLower selectedUpper y :=
  BoundaryChartSelectedTargetContainsLaterTargets.ofLowerZeroSubset
    (by
      intro c d hc0 hle hy hlocal
      exact D.selectedTarget_subset_laterTarget.trans
        (hfuture c d hc0 hle hy hlocal))

/-- Constructor from an already materialized target-box selection. -/
def ofTargetBoxSelection
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (hy :
      y ∈ lowerZeroFaceDomain target.lowerCorner target.upperCorner)
    (hnhds :
      lowerZeroFaceDomain target.lowerCorner target.upperCorner ∈ 𝓝 y)
    (hsubset :
      lowerZeroFaceDomain target.lowerCorner target.upperCorner ⊆ U)
    (hlower :
      ∀ i : Fin n, target.lowerCorner i.succ ≤ selectedLower i.succ)
    (hupper :
      ∀ i : Fin n, selectedUpper i.succ ≤ target.upperCorner i.succ) :
    BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U where
  laterLowerCorner := target.lowerCorner
  laterUpperCorner := target.upperCorner
  laterLowerCorner_zero := target.lowerCorner_zero
  laterLower_le_laterUpper := target.lower_le_upper
  targetPoint_mem := hy
  laterTarget_mem_nhds := hnhds
  laterTarget_subset_set := hsubset
  later_lower_le_selected_lower := hlower
  selected_upper_le_later_upper := hupper
  compactImage := target.compactImage
  localInverse := target.localInverse

/--
The simplest controlled choice: if the selected/ambient target box itself is a
neighborhood of `y`, lies in `U`, and has the two image-data halves, use it as
the later target.
-/
def ofSelf
    (hzero : selectedLower 0 = 0)
    (hle : selectedLower ≤ selectedUpper)
    (hy : y ∈ lowerZeroFaceDomain selectedLower selectedUpper)
    (hnhds : lowerZeroFaceDomain selectedLower selectedUpper ∈ 𝓝 y)
    (hsubset : lowerZeroFaceDomain selectedLower selectedUpper ⊆ U)
    (hcompact :
      boundaryChartCompactImageBoxSelection I x0 x1 a b
        selectedLower selectedUpper)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1 a b
        selectedLower selectedUpper) :
    BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U where
  laterLowerCorner := selectedLower
  laterUpperCorner := selectedUpper
  laterLowerCorner_zero := hzero
  laterLower_le_laterUpper := hle
  targetPoint_mem := hy
  laterTarget_mem_nhds := hnhds
  laterTarget_subset_set := hsubset
  later_lower_le_selected_lower := fun _ => le_rfl
  selected_upper_le_later_upper := fun _ => le_rfl
  compactImage := hcompact
  localInverse := hlocal

/-- Existence form of `ofSelf`, useful for target-side neighborhood selection scripts. -/
theorem exists_of_box_mem_nhds_subset
    (hzero : selectedLower 0 = 0)
    (hle : selectedLower ≤ selectedUpper)
    (hy : y ∈ lowerZeroFaceDomain selectedLower selectedUpper)
    (hnhds : lowerZeroFaceDomain selectedLower selectedUpper ∈ 𝓝 y)
    (hsubset : lowerZeroFaceDomain selectedLower selectedUpper ⊆ U)
    (hcompact :
      boundaryChartCompactImageBoxSelection I x0 x1 a b
        selectedLower selectedUpper)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1 a b
        selectedLower selectedUpper) :
    ∃ D : BoundaryChartControlledTargetBoxSelectionData
        I x0 x1 a b selectedLower selectedUpper y U,
      D.laterLowerCorner = selectedLower ∧
        D.laterUpperCorner = selectedUpper := by
  refine ⟨ofSelf (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
      (selectedLower := selectedLower) (selectedUpper := selectedUpper)
      (y := y) (U := U) hzero hle hy hnhds hsubset hcompact hlocal,
    rfl, rfl⟩

end BoundaryChartControlledTargetBoxSelectionData

/--
Future-target bounds relative to one controlled target.

This is the precise adapter for the old universal shrink API: later target boxes
must be selected by a policy that keeps them larger than the controlled target.
-/
structure BoundaryChartControlledTargetFutureBounds {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b selectedLower selectedUpper : Fin (n + 1) → Real}
    {y : Fin n → Real} {U : Set (Fin n → Real)}
    (D : BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U) where
  /-- Future target lower corners lie below the controlled target lower corner. -/
  future_lower_le_later_lower :
    ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
      y ∈ lowerZeroFaceDomain c d →
        boundaryChartLocalInverseData I x0 x1 a b c d →
          ∀ i : Fin n, c i.succ ≤ D.laterLowerCorner i.succ
  /-- The controlled target upper corner lies below all future upper corners. -/
  later_upper_le_future_upper :
    ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
      y ∈ lowerZeroFaceDomain c d →
        boundaryChartLocalInverseData I x0 x1 a b c d →
          ∀ i : Fin n, D.laterUpperCorner i.succ ≤ d i.succ

namespace BoundaryChartControlledTargetFutureBounds

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {a b selectedLower selectedUpper : Fin (n + 1) → Real}
variable {y : Fin n → Real} {U : Set (Fin n → Real)}
variable {D : BoundaryChartControlledTargetBoxSelectionData
  I x0 x1 a b selectedLower selectedUpper y U}

/-- Convert controlled future bounds to the old coordinatewise shrink record. -/
def toLaterTargetShrinkData
    (F : BoundaryChartControlledTargetFutureBounds D) :
    BoundaryChartLaterTargetShrinkData
      I x0 x1 a b selectedLower selectedUpper y where
  later_lower_le_selected_lower := by
    intro c d hc0 hle hy hlocal i
    exact (F.future_lower_le_later_lower c d hc0 hle hy hlocal i).trans
      (D.later_lower_le_selected_lower i)
  selected_upper_le_later_upper := by
    intro c d hc0 hle hy hlocal i
    exact (D.selected_upper_le_later_upper i).trans
      (F.later_upper_le_future_upper c d hc0 hle hy hlocal i)

/-- Convert controlled future bounds to the old selected-target containment record. -/
def toSelectedTargetContainsLaterTargets
    (F : BoundaryChartControlledTargetFutureBounds D) :
    BoundaryChartSelectedTargetContainsLaterTargets
      I x0 x1 a b selectedLower selectedUpper y :=
  F.toLaterTargetShrinkData.toSelectedTargetContainsLaterTargets

end BoundaryChartControlledTargetFutureBounds

end ManifoldBoundary

end Stokes

end
