import Stokes.Global.CoverIndexedZeroCompactRelativeTargetBox

/-!
# Target boxes selected from compact coordinate images

This file pushes the target-box side of the compact zero route one step closer
to the natural compact-support input.  The small geometric normalization is
important for boundary charts: an arbitrary compact coordinate box need not
have lower `0`-coordinate equal to `0`, while boundary target boxes do.

We therefore replace the lower `0` coordinate by `0`, keep the tangential
coordinates of the selected compact box, and enlarge the upper `0` coordinate
to `max 0 b₀`.  If the compact coordinate image lies in the upper half-space,
the normalized box still contains it and has the exact corner shape expected by
`BoundaryChartTargetBoxSelection`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section LowerZeroCompactCoordinateBox

variable {n : Nat}

namespace CompactCoordinateBoxSelection

/-- Lower-zero normalization of the lower corner of an ambient compact
coordinate box.  Tangential coordinates are inherited from the compact box. -/
def lowerZeroLower (B : CompactCoordinateBoxSelection (Fin (n + 1) → Real)) :
    Fin (n + 1) → Real :=
  lowerZeroTargetLowerCorner (boundaryFaceLowerCorner B.a)

/-- Lower-zero normalization of the upper corner of an ambient compact
coordinate box.  The `0` upper coordinate is enlarged to be at least `0`; the
tangential coordinates are inherited from the compact box. -/
def lowerZeroUpper (B : CompactCoordinateBoxSelection (Fin (n + 1) → Real)) :
    Fin (n + 1) → Real :=
  Fin.cases (max 0 (B.b 0)) (boundaryFaceUpperCorner B.b)

@[simp]
theorem lowerZeroLower_zero
    (B : CompactCoordinateBoxSelection (Fin (n + 1) → Real)) :
    B.lowerZeroLower 0 = 0 :=
  rfl

@[simp]
theorem lowerZeroLower_succ
    (B : CompactCoordinateBoxSelection (Fin (n + 1) → Real)) (i : Fin n) :
    B.lowerZeroLower i.succ = B.a i.succ :=
  rfl

@[simp]
theorem lowerZeroUpper_zero
    (B : CompactCoordinateBoxSelection (Fin (n + 1) → Real)) :
    B.lowerZeroUpper 0 = max 0 (B.b 0) :=
  rfl

@[simp]
theorem lowerZeroUpper_succ
    (B : CompactCoordinateBoxSelection (Fin (n + 1) → Real)) (i : Fin n) :
    B.lowerZeroUpper i.succ = B.b i.succ :=
  rfl

/-- The normalized lower-zero corners are ordered. -/
theorem lowerZeroLower_le_lowerZeroUpper
    (B : CompactCoordinateBoxSelection (Fin (n + 1) → Real)) :
    B.lowerZeroLower ≤ B.lowerZeroUpper := by
  intro j
  refine Fin.cases ?_ ?_ j
  · simp [lowerZeroLower, lowerZeroUpper]
  · intro i
    simpa [lowerZeroLower, lowerZeroUpper] using B.le i.succ

/-- If the boxed compact coordinate set lies in the upper half-space, then the
lower-zero normalized box still contains it. -/
theorem subset_Icc_lowerZero_of_subset_upperHalfSpace
    (B : CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (hhalf : B.K ⊆ upperHalfSpace n) :
    B.K ⊆ Icc B.lowerZeroLower B.lowerZeroUpper := by
  intro y hy
  have hyIcc : y ∈ Icc B.a B.b := B.subset_Icc hy
  constructor
  · intro j
    refine Fin.cases ?_ ?_ j
    · simpa [lowerZeroLower, upperHalfSpace] using hhalf hy
    · intro i
      simpa [lowerZeroLower] using hyIcc.1 i.succ
  · intro j
    refine Fin.cases ?_ ?_ j
    · exact (hyIcc.2 0).trans (le_max_right (0 : Real) (B.b 0))
    · intro i
      simpa [lowerZeroUpper] using hyIcc.2 i.succ

end CompactCoordinateBoxSelection

namespace BoundaryChartTargetBoxSelection

universe uM uH

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {a b : Fin (n + 1) → Real}

/-- Build a boundary target-box selection whose corners are the lower-zero
normalization of a compact coordinate box. -/
def ofCompactCoordinateBoxSelectionLowerZero
    (B : CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (hcompact :
      boundaryChartCompactImageBoxSelection I x0 x1 a b
        B.lowerZeroLower B.lowerZeroUpper)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1 a b
        B.lowerZeroLower B.lowerZeroUpper) :
    BoundaryChartTargetBoxSelection I x0 x1 a b :=
  mkOfCompactImageLocalInverseData
    B.lowerZeroLower B.lowerZeroUpper
    B.lowerZeroLower_zero B.lowerZeroLower_le_lowerZeroUpper
    hcompact hlocal

@[simp]
theorem ofCompactCoordinateBoxSelectionLowerZero_lowerCorner
    (B : CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (hcompact :
      boundaryChartCompactImageBoxSelection I x0 x1 a b
        B.lowerZeroLower B.lowerZeroUpper)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1 a b
        B.lowerZeroLower B.lowerZeroUpper) :
    (ofCompactCoordinateBoxSelectionLowerZero
      (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
      B hcompact hlocal).lowerCorner = B.lowerZeroLower :=
  rfl

@[simp]
theorem ofCompactCoordinateBoxSelectionLowerZero_upperCorner
    (B : CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (hcompact :
      boundaryChartCompactImageBoxSelection I x0 x1 a b
        B.lowerZeroLower B.lowerZeroUpper)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1 a b
        B.lowerZeroLower B.lowerZeroUpper) :
    (ofCompactCoordinateBoxSelectionLowerZero
      (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
      B hcompact hlocal).upperCorner = B.lowerZeroUpper :=
  rfl

end BoundaryChartTargetBoxSelection

end LowerZeroCompactCoordinateBox

section CoverIndexedZeroCompactTargetBoxSelection

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryTargetBoxData

/-- Construct cover-indexed target-box data from compact coordinate boxes whose
lower-zero normalized corners are also equipped with the boundary compact-image
and local-inverse halves.  The resulting `targetLower`/`targetUpper` are
definitionally aligned with the normalized compact-box corners. -/
def ofLowerZeroCompactCoordinateBoxSelections
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (box :
      {x : M // x ∈ C.boundaryCenters} →
        CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (compactImage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartCompactImageBoxSelection I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (box i).lowerZeroLower (box i).lowerZeroUpper)
    (localInverse :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartLocalInverseData I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (box i).lowerZeroLower (box i).lowerZeroUpper) :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega :=
  CoverIndexedBoundaryTargetBoxData.ofTargetSelection
    (C := C) (P := P) (ω := omega)
    targetChart sourceTargetSelectedBox
    (fun i =>
      BoundaryChartTargetBoxSelection.ofCompactCoordinateBoxSelectionLowerZero
        (I := I) (x0 := C.boundaryChart i.1) (x1 := targetChart i)
        (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
        (box i) (compactImage i) (localInverse i))

@[simp]
theorem ofLowerZeroCompactCoordinateBoxSelections_targetChart
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (box :
      {x : M // x ∈ C.boundaryCenters} →
        CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (compactImage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartCompactImageBoxSelection I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (box i).lowerZeroLower (box i).lowerZeroUpper)
    (localInverse :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartLocalInverseData I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (box i).lowerZeroLower (box i).lowerZeroUpper) :
    (ofLowerZeroCompactCoordinateBoxSelections
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      targetChart sourceTargetSelectedBox box compactImage localInverse).targetChart =
      targetChart :=
  rfl

@[simp]
theorem ofLowerZeroCompactCoordinateBoxSelections_targetLower
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (box :
      {x : M // x ∈ C.boundaryCenters} →
        CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (compactImage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartCompactImageBoxSelection I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (box i).lowerZeroLower (box i).lowerZeroUpper)
    (localInverse :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartLocalInverseData I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (box i).lowerZeroLower (box i).lowerZeroUpper)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    (ofLowerZeroCompactCoordinateBoxSelections
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      targetChart sourceTargetSelectedBox box compactImage localInverse).targetLower i =
      (box i).lowerZeroLower :=
  rfl

@[simp]
theorem ofLowerZeroCompactCoordinateBoxSelections_targetUpper
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (box :
      {x : M // x ∈ C.boundaryCenters} →
        CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (compactImage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartCompactImageBoxSelection I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (box i).lowerZeroLower (box i).lowerZeroUpper)
    (localInverse :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartLocalInverseData I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (box i).lowerZeroLower (box i).lowerZeroUpper)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    (ofLowerZeroCompactCoordinateBoxSelections
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      targetChart sourceTargetSelectedBox box compactImage localInverse).targetUpper i =
      (box i).lowerZeroUpper :=
  rfl

end CoverIndexedBoundaryTargetBoxData

namespace CoverIndexedZeroCompactRelativeTargetBoxData

variable
    {transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega}

/-- Construct the relative compact zero target-box package directly from
compact coordinate boxes, using the lower-zero normalized corners as the
selected target-box corners. -/
def ofLowerZeroCompactCoordinateBoxSelections
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetChart_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        transitionSupportData.targetChart i = targetChart i)
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (box :
      {x : M // x ∈ C.boundaryCenters} →
        CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (box_K_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (box i).K = chartCoordinateImage I (targetChart i) K)
    (box_subset_halfSpace :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (box i).K ⊆ upperHalfSpace n)
    (compactImage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartCompactImageBoxSelection I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (box i).lowerZeroLower (box i).lowerZeroUpper)
    (localInverse :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartLocalInverseData I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (box i).lowerZeroLower (box i).lowerZeroUpper)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (box i).lowerZeroLower (box i).lowerZeroUpper ⊆
          (extChartAt I (targetChart i)).target) :
    CoverIndexedZeroCompactRelativeTargetBoxData
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData := by
  let targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega :=
    CoverIndexedBoundaryTargetBoxData.ofLowerZeroCompactCoordinateBoxSelections
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      targetChart sourceTargetSelectedBox box compactImage localInverse
  refine
    { targetBox := targetBox
      targetChart_eq := ?_
      targetBox_subset_target := ?_
      coordinateImage_subset_targetBox := ?_ }
  · intro i
    simpa [targetBox] using targetChart_eq i
  · intro i
    simpa [targetBox] using targetBox_subset_target i
  · intro i y hy
    have hybox : y ∈ (box i).K := by
      simpa [box_K_eq i] using hy
    have hyIcc :
        y ∈ Icc (box i).lowerZeroLower (box i).lowerZeroUpper :=
      (box i).subset_Icc_lowerZero_of_subset_upperHalfSpace
        (box_subset_halfSpace i) hybox
    simpa [targetBox] using hyIcc

/-- `ChartCompactImage` spelling of
`ofLowerZeroCompactCoordinateBoxSelections`.  The selected compact coordinate
box is `(image i).box`, so the corner alignment is definitionally fixed by the
constructor above. -/
def ofLowerZeroChartCompactImages
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetChart_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        transitionSupportData.targetChart i = targetChart i)
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (image :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartCompactImage I (targetChart i))
    (image_K_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (image i).K = K)
    (coordinateImage_subset_halfSpace :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        chartCoordinateImage I (targetChart i) K ⊆ upperHalfSpace n)
    (compactImage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartCompactImageBoxSelection I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (image i).box.lowerZeroLower (image i).box.lowerZeroUpper)
    (localInverse :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartLocalInverseData I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (image i).box.lowerZeroLower (image i).box.lowerZeroUpper)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (image i).box.lowerZeroLower (image i).box.lowerZeroUpper ⊆
          (extChartAt I (targetChart i)).target) :
    CoverIndexedZeroCompactRelativeTargetBoxData
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData := by
  refine
    ofLowerZeroCompactCoordinateBoxSelections
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (transitionSupportData := transitionSupportData)
      targetChart targetChart_eq sourceTargetSelectedBox
      (fun i => (image i).box) ?_ ?_ compactImage localInverse
      targetBox_subset_target
  · intro i
    calc
      (image i).box.K = (image i).coordSupport := (image i).box_K_eq_coordSupport
      _ = chartCoordinateImage I (targetChart i) (image i).K := rfl
      _ = chartCoordinateImage I (targetChart i) K := by rw [image_K_eq i]
  · intro i y hy
    have hycoord : y ∈ chartCoordinateImage I (targetChart i) K := by
      simpa [
        (show (image i).box.K =
          chartCoordinateImage I (targetChart i) (image i).K from
          (image i).box_K_eq_coordSupport),
        image_K_eq i] using hy
    exact coordinateImage_subset_halfSpace i hycoord

end CoverIndexedZeroCompactRelativeTargetBoxData

end CoverIndexedZeroCompactTargetBoxSelection

end Stokes

end
