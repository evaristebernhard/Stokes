import Stokes.Global.CoverIndexedZeroCompactRefinedImageControl

/-!
# Image-control constructors from collar-style refined-box data

This file is a thin constructor layer above
`CoverIndexedZeroCompactRefinedImageControl`.

The current refined collar-facing theorem consumes both an
`imageControlFamily` and its ambient `imageControl_mapsTo` proof.  The natural
input one level upstream is smaller: target boxes for the canonical flattened
refined-box index, plus a whole-box closed-preimage shrink certificate.  The
definitions below package that data without using tangential boundary-face
control.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactFromCollarImageControl

universe uH uM uB

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type uB}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryBoxRefinedPartition

variable
    (D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P ω BoundaryPiece)

/--
Flattened image-control family from target boxes on the canonical
`D.RefinedBoxIndex`.
-/
def flattenedImageControlFamilyOfTargets
    [Fintype D.RefinedBoxIndex]
    (sourceChart_eq_boundaryChart :
      ∀ r : D.RefinedBoxIndex,
        D.sourceChart r.1 r.2.1 = C.boundaryChart r.1.1)
    (targetLower targetUpper :
      D.RefinedBoxIndex → Fin (n + 1) → Real) :
    CoverIndexedRefinedBoxImageControlFamily
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      D D.RefinedBoxIndex :=
  D.flattenedImageControlFamily
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    sourceChart_eq_boundaryChart targetLower targetUpper

/--
Explicit whole-box closed-preimage control as the refined family field.

The hypothesis is ambient control on the full refined source `Icc`, not a
boundary-face or tangential control statement.
-/
theorem closedPreimageShrinkFieldOfExplicit
    [Fintype D.RefinedBoxIndex]
    (sourceChart_eq_boundaryChart :
      ∀ r : D.RefinedBoxIndex,
        D.sourceChart r.1 r.2.1 = C.boundaryChart r.1.1)
    (targetLower targetUpper :
      D.RefinedBoxIndex → Fin (n + 1) → Real)
    (hpre :
      ∀ r : D.RefinedBoxIndex,
        Icc (D.lower r.1 r.2.1) (D.upper r.1 r.2.1) ⊆
          (ManifoldForm.chartTransition I
            (C.boundaryChart r.1.1) (D.targetChart r.1 r.2.1)) ⁻¹'
            Icc (targetLower r) (targetUpper r)) :
    (D.flattenedImageControlFamilyOfTargets
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      sourceChart_eq_boundaryChart targetLower targetUpper).ClosedPreimageShrinkField := by
  exact hpre

/--
Closed-preimage route for the flattened target-box family.
-/
theorem chartTransitionMapsToFieldOfClosedPreimage
    [Fintype D.RefinedBoxIndex]
    (sourceChart_eq_boundaryChart :
      ∀ r : D.RefinedBoxIndex,
        D.sourceChart r.1 r.2.1 = C.boundaryChart r.1.1)
    (targetLower targetUpper :
      D.RefinedBoxIndex → Fin (n + 1) → Real)
    (hpre :
      (D.flattenedImageControlFamilyOfTargets
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        sourceChart_eq_boundaryChart targetLower targetUpper).ClosedPreimageShrinkField) :
    (D.flattenedImageControlFamilyOfTargets
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      sourceChart_eq_boundaryChart targetLower targetUpper).ChartTransitionMapsToField := by
  exact
    CoverIndexedRefinedBoxImageControlFamily.chartTransitionMapsToField_of_refined_closedPreimageShrink
      (I := I) (K := K) (C := C)
      (D.flattenedImageControlFamilyOfTargets
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        sourceChart_eq_boundaryChart targetLower targetUpper)
      hpre

/--
One-shot whole-box closed-preimage route, stated without requiring callers to
name the flattened image-control family.
-/
theorem chartTransitionMapsToFieldOfExplicitClosedPreimage
    [Fintype D.RefinedBoxIndex]
    (sourceChart_eq_boundaryChart :
      ∀ r : D.RefinedBoxIndex,
        D.sourceChart r.1 r.2.1 = C.boundaryChart r.1.1)
    (targetLower targetUpper :
      D.RefinedBoxIndex → Fin (n + 1) → Real)
    (hpre :
      ∀ r : D.RefinedBoxIndex,
        Icc (D.lower r.1 r.2.1) (D.upper r.1 r.2.1) ⊆
          (ManifoldForm.chartTransition I
            (C.boundaryChart r.1.1) (D.targetChart r.1 r.2.1)) ⁻¹'
            Icc (targetLower r) (targetUpper r)) :
    (D.flattenedImageControlFamilyOfTargets
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      sourceChart_eq_boundaryChart targetLower targetUpper).ChartTransitionMapsToField :=
  D.chartTransitionMapsToFieldOfClosedPreimage
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    sourceChart_eq_boundaryChart targetLower targetUpper
    (D.closedPreimageShrinkFieldOfExplicit
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      sourceChart_eq_boundaryChart targetLower targetUpper hpre)

end CoverIndexedBoundaryBoxRefinedPartition

/--
Paired image-control fields consumed by collar-facing refined Stokes inputs.

This package lets an upstream constructor build the current
`imageControlFamily`/`imageControl_mapsTo` pair from one closed-preimage input.
-/
structure CoverIndexedFlattenedRefinedBoxImageControl
    (D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P ω BoundaryPiece)
    [Fintype D.RefinedBoxIndex] where
  imageControlFamily :
    CoverIndexedRefinedBoxImageControlFamily
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      D D.RefinedBoxIndex
  imageControl_mapsTo :
    imageControlFamily.ChartTransitionMapsToField (I := I) (K := K) (C := C)

namespace CoverIndexedBoundaryBoxRefinedPartition

variable
    (D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P ω BoundaryPiece)

/--
Build both image-control fields from flattened target boxes and a
`ClosedPreimageShrinkField`.
-/
def flattenedImageControlPackageOfClosedPreimage
    [Fintype D.RefinedBoxIndex]
    (sourceChart_eq_boundaryChart :
      ∀ r : D.RefinedBoxIndex,
        D.sourceChart r.1 r.2.1 = C.boundaryChart r.1.1)
    (targetLower targetUpper :
      D.RefinedBoxIndex → Fin (n + 1) → Real)
    (hpre :
      (D.flattenedImageControlFamilyOfTargets
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        sourceChart_eq_boundaryChart targetLower targetUpper).ClosedPreimageShrinkField) :
    CoverIndexedFlattenedRefinedBoxImageControl
      (I := I) (K := K) (C := C) (P := P) (ω := ω) D where
  imageControlFamily :=
    D.flattenedImageControlFamilyOfTargets
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      sourceChart_eq_boundaryChart targetLower targetUpper
  imageControl_mapsTo :=
    D.chartTransitionMapsToFieldOfClosedPreimage
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      sourceChart_eq_boundaryChart targetLower targetUpper hpre

/--
Build both image-control fields from explicit whole-box closed-preimage
control.
-/
def flattenedImageControlPackageOfExplicitClosedPreimage
    [Fintype D.RefinedBoxIndex]
    (sourceChart_eq_boundaryChart :
      ∀ r : D.RefinedBoxIndex,
        D.sourceChart r.1 r.2.1 = C.boundaryChart r.1.1)
    (targetLower targetUpper :
      D.RefinedBoxIndex → Fin (n + 1) → Real)
    (hpre :
      ∀ r : D.RefinedBoxIndex,
        Icc (D.lower r.1 r.2.1) (D.upper r.1 r.2.1) ⊆
          (ManifoldForm.chartTransition I
            (C.boundaryChart r.1.1) (D.targetChart r.1 r.2.1)) ⁻¹'
            Icc (targetLower r) (targetUpper r)) :
    CoverIndexedFlattenedRefinedBoxImageControl
      (I := I) (K := K) (C := C) (P := P) (ω := ω) D :=
  D.flattenedImageControlPackageOfClosedPreimage
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    sourceChart_eq_boundaryChart targetLower targetUpper
    (D.closedPreimageShrinkFieldOfExplicit
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      sourceChart_eq_boundaryChart targetLower targetUpper hpre)

end CoverIndexedBoundaryBoxRefinedPartition

end CoverIndexedZeroCompactFromCollarImageControl

end Stokes

end
