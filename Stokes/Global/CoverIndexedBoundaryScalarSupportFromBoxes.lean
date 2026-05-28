import Stokes.Global.CoverIndexedBoundaryScalarImageSupport

/-!
# Boundary scalar support from selected target boxes

This file proves the pointwise support bridge used by the scalar boundary
route.  The ambient target representative is not assumed to be supported on the
boundary-transition image.  Instead, if it is supported in the selected target
box `Icc c d`, then any nonzero lower-face scalar lies in the target
lower-zero face; selected image data identifies that face with the image of the
source boundary box.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BasicBoundaryScalarSupportFromBoxes

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/-- A nonzero boundary scalar evaluation forces the ambient target chart form
to be nonzero at the embedded boundary coordinate. -/
theorem boundaryTargetInChartPieceIntegrand_nonzero_inChart_nonzero
    {x : M} {ω : ManifoldForm I M n} {u : Fin n → Real}
    (h :
      boundaryTargetInChartPieceIntegrand I x ω u ≠ 0) :
    ManifoldForm.inChart I x ω (boundaryInclusion n u) ≠ 0 := by
  intro hzero
  have hval :
      ManifoldForm.inChart I x ω (boundaryInclusion n u)
          (boundaryTangent n) = 0 := by
    rw [hzero]
    rfl
  apply h
  change
    outwardFirstBoundaryOrientationSign n *
        ManifoldForm.inChart I x ω (boundaryInclusion n u)
          (boundaryTangent n) = 0
  rw [hval, mul_zero]

/-- If the ambient target chart representative is supported in the selected
target box, every nonzero boundary scalar point lies on the selected target
lower-zero face. -/
theorem boundaryTargetInChartPieceIntegrand_nonzero_mem_targetPieceSet_of_inChart_tsupport_subset_Icc
    {x : M} {ω : ManifoldForm I M n}
    {c d : Fin (n + 1) → Real}
    (hsupport :
      tsupport (ManifoldForm.inChart I x ω) ⊆ Icc c d)
    {u : Fin n → Real}
    (h :
      boundaryTargetInChartPieceIntegrand I x ω u ≠ 0) :
    u ∈ boundaryTargetInChartPieceSet (n := n) c d := by
  have hform :
      ManifoldForm.inChart I x ω (boundaryInclusion n u) ≠ 0 :=
    boundaryTargetInChartPieceIntegrand_nonzero_inChart_nonzero
      (I := I) (x := x) (ω := ω) h
  have hsupp :
      boundaryInclusion n u ∈ Function.support (ManifoldForm.inChart I x ω) :=
    hform
  have hIcc :
      boundaryInclusion n u ∈ Icc c d :=
    hsupport (subset_tsupport (ManifoldForm.inChart I x ω) hsupp)
  simpa [boundaryTargetInChartPieceSet] using
    (mem_lowerZeroFaceDomain_of_boundaryInclusion_mem_Icc
      (n := n) (a := c) (b := d) hIcc)

/-- Pointwise source of the scalar image-support condition: target-box support
plus selected image data sends every nonzero scalar boundary point into the
image of the selected source boundary box. -/
theorem boundaryTargetInChartPieceIntegrand_nonzero_mem_boundaryImage_of_inChart_tsupport_subset_Icc
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d)
    (hsupport :
      tsupport (ManifoldForm.inChart I x1 ω) ⊆ Icc c d)
    {u : Fin n → Real}
    (h :
      boundaryTargetInChartPieceIntegrand I x1 ω u ≠ 0) :
    u ∈ boundaryChartTransitionBoundaryImage I x0 x1 a b := by
  have hface :
      u ∈ boundaryTargetInChartPieceSet (n := n) c d :=
    boundaryTargetInChartPieceIntegrand_nonzero_mem_targetPieceSet_of_inChart_tsupport_subset_Icc
      (I := I) (x := x1) (ω := ω) (c := c) (d := d)
      hsupport h
  rw [boundaryChartTransitionBoundaryImage_eq_lowerZeroFaceDomain_of_imageData
    (I := I) himage]
  simpa [boundaryTargetInChartPieceSet] using hface

/-- Support-set version of
`boundaryTargetInChartPieceIntegrand_nonzero_mem_boundaryImage_of_inChart_tsupport_subset_Icc`. -/
theorem boundaryTargetInChartPieceIntegrand_support_subset_boundaryImage_of_inChart_tsupport_subset_Icc
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d)
    (hsupport :
      tsupport (ManifoldForm.inChart I x1 ω) ⊆ Icc c d) :
    Function.support (boundaryTargetInChartPieceIntegrand I x1 ω) ⊆
      boundaryChartTransitionBoundaryImage I x0 x1 a b := by
  intro u hu
  exact
    boundaryTargetInChartPieceIntegrand_nonzero_mem_boundaryImage_of_inChart_tsupport_subset_Icc
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (c := c) (d := d)
      himage hsupport hu

end BasicBoundaryScalarSupportFromBoxes

section CoverIndexedBoundaryScalarSupportFromBoxes

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

/-- Target-box support of the ambient target representatives gives the
pointwise nonzero scalar image field. -/
theorem boundaryScalarNonzeroMemImageField_of_targetInChart_tsupport_subset_Icc
    (targetInChart_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (D.targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          Icc (D.targetLower i) (D.targetUpper i)) :
    D.BoundaryScalarNonzeroMemImageField := by
  intro i u hu
  exact
    boundaryTargetInChartPieceIntegrand_nonzero_mem_boundaryImage_of_inChart_tsupport_subset_Icc
      (I := I)
      (x0 := C.boundaryChart i.1) (x1 := D.targetChart i)
      (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (c := D.targetLower i) (d := D.targetUpper i)
      (D.boundaryChartSelectedBoxImageData i)
      (targetInChart_tsupport_subset i) hu

/-- Target-box support of the ambient target representatives gives the scalar
support-on-image field consumed by the scalar boundary route. -/
theorem boundaryScalarSupportSubsetImageField_of_targetInChart_tsupport_subset_Icc
    (targetInChart_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (D.targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          Icc (D.targetLower i) (D.targetUpper i)) :
    D.BoundaryScalarSupportSubsetImageField := by
  intro i
  exact
    boundaryTargetInChartPieceIntegrand_support_subset_boundaryImage_of_inChart_tsupport_subset_Icc
      (I := I)
      (x0 := C.boundaryChart i.1) (x1 := D.targetChart i)
      (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (c := D.targetLower i) (d := D.targetUpper i)
      (D.boundaryChartSelectedBoxImageData i)
      (targetInChart_tsupport_subset i)

/-- Constructor from the existing target support/continuity package.  This is
the handoff used when localized/partition support control has already produced
ambient target-box support. -/
theorem boundaryScalarSupportSubsetImageField_of_supportContinuity
    {targetChart : {x : M // x ∈ C.boundaryCenters} → M}
    {targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real}
    (supportContinuity :
      CoverIndexedBoundaryTargetSupportContinuityData
        (C := C) P ω targetChart targetLower targetUpper)
    (htargetChart :
      targetChart = D.targetChart)
    (htargetLower :
      targetLower = D.targetLower)
    (htargetUpper :
      targetUpper = D.targetUpper) :
    D.BoundaryScalarSupportSubsetImageField := by
  subst htargetChart
  subst htargetLower
  subst htargetUpper
  exact
    D.boundaryScalarSupportSubsetImageField_of_targetInChart_tsupport_subset_Icc
      supportContinuity.targetInChart_tsupport_subset

/-- Constructor from ambient target `inChart` box data. -/
theorem boundaryScalarSupportSubsetImageField_of_targetInChartBoxData
    {targetChart : {x : M // x ∈ C.boundaryCenters} → M}
    {targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real}
    (targetData :
      CoverIndexedBoundaryTargetInChartBoxData
        (C := C) P ω targetChart targetLower targetUpper)
    (htargetChart :
      targetChart = D.targetChart)
    (htargetLower :
      targetLower = D.targetLower)
    (htargetUpper :
      targetUpper = D.targetUpper) :
    D.BoundaryScalarSupportSubsetImageField := by
  subst htargetChart
  subst htargetLower
  subst htargetUpper
  exact
    D.boundaryScalarSupportSubsetImageField_of_targetInChart_tsupport_subset_Icc
      targetData.targetInChart_tsupport_subset

end CoverIndexedBoundaryTargetBoxData

end CoverIndexedBoundaryScalarSupportFromBoxes

end Stokes

end
