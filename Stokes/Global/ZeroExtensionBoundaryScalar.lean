import Stokes.ManifoldFormZero
import Stokes.Global.CoverIndexedBoundaryScalarSupportFromBoxes

/-!
# Zero-extension bridge for boundary scalar pieces

This file keeps the zero-extension layer at the scalar boundary-integrand
level.  It does not assert that the old ambient target representative
`ManifoldForm.inChart I x omega` is supported on a boundary image.  Instead it
records:

* the scalar lower-face integrand built from `ManifoldForm.inChartZero`,
* equality with the old scalar integrand on chart target points, and
* handoff lemmas that turn zero-scalar image support into the old scalar
  support field, provided the old scalar is only used on a face whose ambient
  inclusion lies in the target chart.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BasicBoundaryScalarZero

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/-- Target boundary scalar representative built from the zero-extended target
chart representative. -/
def boundaryTargetInChartZeroPieceIntegrand
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x : M) (ω : ManifoldForm I M n) (u : Fin n → Real) : Real :=
  outwardFirstBoundaryOrientationSign n *
    ManifoldForm.inChartZero I x ω (boundaryInclusion n u) (boundaryTangent n)

/-- On chart-target points, the zero-extended boundary scalar is the old
boundary scalar integrand. -/
theorem boundaryTargetInChartZeroPieceIntegrand_eq_old_of_boundaryInclusion_mem_target
    {x : M} {ω : ManifoldForm I M n} {u : Fin n → Real}
    (hu : boundaryInclusion n u ∈ (extChartAt I x).target) :
    boundaryTargetInChartZeroPieceIntegrand I x ω u =
      boundaryTargetInChartPieceIntegrand I x ω u := by
  simp [boundaryTargetInChartZeroPieceIntegrand,
    boundaryTargetInChartPieceIntegrand,
    ManifoldForm.inChartZero_eq_inChart_of_mem (I := I) (x0 := x)
      (ω := ω) hu]

/-- A nonzero zero-extended boundary scalar evaluation forces the
zero-extended ambient target chart form to be nonzero at the embedded boundary
coordinate. -/
theorem boundaryTargetInChartZeroPieceIntegrand_nonzero_inChartZero_nonzero
    {x : M} {ω : ManifoldForm I M n} {u : Fin n → Real}
    (h : boundaryTargetInChartZeroPieceIntegrand I x ω u ≠ 0) :
    ManifoldForm.inChartZero I x ω (boundaryInclusion n u) ≠ 0 := by
  intro hzero
  have hval :
      ManifoldForm.inChartZero I x ω (boundaryInclusion n u)
          (boundaryTangent n) = 0 := by
    rw [hzero]
    rfl
  apply h
  change
    outwardFirstBoundaryOrientationSign n *
        ManifoldForm.inChartZero I x ω (boundaryInclusion n u)
          (boundaryTangent n) = 0
  rw [hval, mul_zero]

/-- Ordinary support of the zero boundary scalar lies over the target chart
domain. -/
theorem boundaryTargetInChartZeroPieceIntegrand_support_subset_targetPreimage
    (x : M) (ω : ManifoldForm I M n) :
    Function.support (boundaryTargetInChartZeroPieceIntegrand I x ω) ⊆
      {u : Fin n → Real | boundaryInclusion n u ∈ (extChartAt I x).target} := by
  intro u hu
  have hform :
      ManifoldForm.inChartZero I x ω (boundaryInclusion n u) ≠ 0 :=
    boundaryTargetInChartZeroPieceIntegrand_nonzero_inChartZero_nonzero
      (I := I) (x := x) (ω := ω) hu
  exact ManifoldForm.inChartZero_support_subset_target
    (I := I) x ω hform

/-- If target-domain boundary coordinates are known to lie in the selected
boundary image, then the zero boundary scalar has ordinary support in that
image. -/
theorem boundaryTargetInChartZeroPieceIntegrand_support_subset_boundaryImage_of_targetPreimage_subset
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real}
    (htarget :
      {u : Fin n → Real | boundaryInclusion n u ∈ (extChartAt I x1).target} ⊆
        boundaryChartTransitionBoundaryImage I x0 x1 a b) :
    Function.support (boundaryTargetInChartZeroPieceIntegrand I x1 ω) ⊆
      boundaryChartTransitionBoundaryImage I x0 x1 a b :=
  (boundaryTargetInChartZeroPieceIntegrand_support_subset_targetPreimage
    (I := I) x1 ω).trans htarget

/-- Closed-image upgrade for zero boundary scalars.  Selected image data is
used only to know that the selected boundary image is closed. -/
theorem boundaryTargetInChartZeroPieceIntegrand_tsupport_subset_boundaryImage_of_support_subset
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d)
    (hsupport :
      Function.support (boundaryTargetInChartZeroPieceIntegrand I x1 ω) ⊆
        boundaryChartTransitionBoundaryImage I x0 x1 a b) :
    tsupport (boundaryTargetInChartZeroPieceIntegrand I x1 ω) ⊆
      boundaryChartTransitionBoundaryImage I x0 x1 a b :=
  tsupport_subset_of_support_subset_isClosed
    (isClosed_boundaryChartTransitionBoundaryImage_of_imageData
      (I := I) himage)
    hsupport

/-- Pointwise target-preimage version of zero-scalar topological support on
the selected boundary image. -/
theorem boundaryTargetInChartZeroPieceIntegrand_tsupport_subset_boundaryImage_of_targetPreimage_subset
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d)
    (htarget :
      {u : Fin n → Real | boundaryInclusion n u ∈ (extChartAt I x1).target} ⊆
        boundaryChartTransitionBoundaryImage I x0 x1 a b) :
    tsupport (boundaryTargetInChartZeroPieceIntegrand I x1 ω) ⊆
      boundaryChartTransitionBoundaryImage I x0 x1 a b :=
  boundaryTargetInChartZeroPieceIntegrand_tsupport_subset_boundaryImage_of_support_subset
    (I := I) himage
    (boundaryTargetInChartZeroPieceIntegrand_support_subset_boundaryImage_of_targetPreimage_subset
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) htarget)

/-- Equality wrapper on any boundary-coordinate face whose ambient inclusion
lies in the target chart. -/
theorem boundaryTargetInChartPieceIntegrand_eq_zeroPieceIntegrand_on_face
    {x : M} {ω : ManifoldForm I M n} {s : Set (Fin n → Real)}
    (hface_target :
      ∀ u ∈ s, boundaryInclusion n u ∈ (extChartAt I x).target)
    {u : Fin n → Real} (hu : u ∈ s) :
    boundaryTargetInChartPieceIntegrand I x ω u =
      boundaryTargetInChartZeroPieceIntegrand I x ω u := by
  exact
    (boundaryTargetInChartZeroPieceIntegrand_eq_old_of_boundaryInclusion_mem_target
      (I := I) (x := x) (ω := ω) (u := u)
      (hface_target u hu)).symm

/-- Transfer zero-scalar image support to the old scalar support, assuming old
nonzero points are confined to a face where the zero extension agrees with the
old representative. -/
theorem boundaryTargetInChartPieceIntegrand_support_subset_boundaryImage_of_zero_support_subset_on_face
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} {s : Set (Fin n → Real)}
    (hzeroSupport :
      Function.support (boundaryTargetInChartZeroPieceIntegrand I x1 ω) ⊆
        boundaryChartTransitionBoundaryImage I x0 x1 a b)
    (hold_face :
      Function.support (boundaryTargetInChartPieceIntegrand I x1 ω) ⊆ s)
    (hface_target :
      ∀ u ∈ s, boundaryInclusion n u ∈ (extChartAt I x1).target) :
    Function.support (boundaryTargetInChartPieceIntegrand I x1 ω) ⊆
      boundaryChartTransitionBoundaryImage I x0 x1 a b := by
  intro u hu
  have hu_face : u ∈ s := hold_face hu
  have heq :
      boundaryTargetInChartZeroPieceIntegrand I x1 ω u =
        boundaryTargetInChartPieceIntegrand I x1 ω u :=
    boundaryTargetInChartZeroPieceIntegrand_eq_old_of_boundaryInclusion_mem_target
      (I := I) (x := x1) (ω := ω) (u := u)
      (hface_target u hu_face)
  have hzero :
      boundaryTargetInChartZeroPieceIntegrand I x1 ω u ≠ 0 := by
    simpa [heq] using hu
  exact hzeroSupport hzero

/-- Target-box version of the preceding wrapper.  This is the useful form for
the current endpoint: it asks for old scalar support in the selected target
face and for the ambient selected target box to lie in the chart target. -/
theorem boundaryTargetInChartPieceIntegrand_support_subset_boundaryImage_of_zero_support_subset_on_targetBox
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b c d : Fin (n + 1) → Real}
    (hc0 : c 0 = 0) (hcd : c ≤ d)
    (hzeroSupport :
      Function.support (boundaryTargetInChartZeroPieceIntegrand I x1 ω) ⊆
        boundaryChartTransitionBoundaryImage I x0 x1 a b)
    (hold_face :
      Function.support (boundaryTargetInChartPieceIntegrand I x1 ω) ⊆
        boundaryTargetInChartPieceSet (n := n) c d)
    (htargetBox :
      Icc c d ⊆ (extChartAt I x1).target) :
    Function.support (boundaryTargetInChartPieceIntegrand I x1 ω) ⊆
      boundaryChartTransitionBoundaryImage I x0 x1 a b := by
  refine
    boundaryTargetInChartPieceIntegrand_support_subset_boundaryImage_of_zero_support_subset_on_face
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b)
      (s := boundaryTargetInChartPieceSet (n := n) c d)
      hzeroSupport hold_face ?_
  intro u hu
  exact htargetBox
    (boundaryInclusion_mem_Icc_of_mem_lowerZeroFaceDomain
      (n := n) (a := c) (b := d) hc0 hcd
      (by simpa [boundaryTargetInChartPieceSet] using hu))

end BasicBoundaryScalarZero

section CoverIndexedBoundaryScalarZero

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryTargetBoxData

variable
  (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω)

/-- Cover-indexed zero-scalar support-on-image field. -/
abbrev BoundaryZeroScalarSupportSubsetImageField : Prop :=
  ∀ i : {x : M // x ∈ C.boundaryCenters},
    Function.support
        (boundaryTargetInChartZeroPieceIntegrand I (D.targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
      boundaryChartTransitionBoundaryImage I
        (C.boundaryChart i.1) (D.targetChart i)
        (C.boundaryLower i.1) (C.boundaryUpper i.1)

/-- Target-preimage version of the zero-scalar image-support field. -/
theorem boundaryZeroScalarSupportSubsetImageField_of_targetPreimage_subset
    (htarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        {u : Fin n → Real |
            boundaryInclusion n u ∈ (extChartAt I (D.targetChart i)).target} ⊆
          boundaryChartTransitionBoundaryImage I
            (C.boundaryChart i.1) (D.targetChart i)
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    D.BoundaryZeroScalarSupportSubsetImageField := by
  intro i
  exact
    boundaryTargetInChartZeroPieceIntegrand_support_subset_boundaryImage_of_targetPreimage_subset
      (I := I)
      (x0 := C.boundaryChart i.1) (x1 := D.targetChart i)
      (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (htarget i)

/-- Transfer zero-scalar support to the old scalar support field consumed by
the scalar boundary endpoint.  The remaining face-domain input is precisely:
old scalar nonzero points lie in the selected target face, and the selected
ambient target box lies in the target chart. -/
theorem boundaryScalarSupportSubsetImageField_of_zeroScalarSupport_on_targetBox
    (hzeroSupport : D.BoundaryZeroScalarSupportSubsetImageField)
    (hold_face :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Function.support
            (boundaryTargetInChartPieceIntegrand I (D.targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          boundaryTargetInChartPieceSet (n := n)
            (D.targetLower i) (D.targetUpper i))
    (htargetBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.targetLower i) (D.targetUpper i) ⊆
          (extChartAt I (D.targetChart i)).target) :
    D.BoundaryScalarSupportSubsetImageField := by
  intro i
  exact
    boundaryTargetInChartPieceIntegrand_support_subset_boundaryImage_of_zero_support_subset_on_targetBox
      (I := I)
      (x0 := C.boundaryChart i.1) (x1 := D.targetChart i)
      (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (c := D.targetLower i) (d := D.targetUpper i)
      (D.targetLower_zero i) (D.targetLower_le_targetUpper i)
      (hzeroSupport i) (hold_face i) (htargetBox i)

end CoverIndexedBoundaryTargetBoxData

end CoverIndexedBoundaryScalarZero

end Stokes

end
