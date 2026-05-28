import Stokes.Global.CoverIndexedBoundaryTargetImageSupport
import Stokes.Global.CoverIndexedBoundaryTargetSmoothnessConstructor

/-!
# Boundary scalar image support

This file records the support route that is actually natural for the boundary
term.  The ambient target representative `ManifoldForm.inChart I x omega` need
not be supported on the boundary-transition image: it is an ambient half-space
representative.  The boundary integral only uses the scalar lower-face
integrand

`boundaryTargetInChartPieceIntegrand I x omega`.

The constructors below therefore ask for support, or pointwise nonzero
membership, of this scalar integrand in the boundary-coordinate transition
image.  The selected target-image data then converts that into the exact
`boundaryPiece_tsupport_subset` field used by the target-boundary measure data.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BasicScalarImageSupport

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/-- Pointwise nonzero membership gives the ordinary support containment for
the boundary scalar target-piece integrand. -/
theorem boundaryTargetInChartPieceIntegrand_support_subset_boundaryImage_of_nonzero_mem
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real}
    (hmem :
      ∀ u, boundaryTargetInChartPieceIntegrand I x1 ω u ≠ 0 →
        u ∈ boundaryChartTransitionBoundaryImage I x0 x1 a b) :
    Function.support (boundaryTargetInChartPieceIntegrand I x1 ω) ⊆
      boundaryChartTransitionBoundaryImage I x0 x1 a b :=
  support_subset_of_nonzero_mem hmem

/-- Selected image data turns scalar support on the transition image into
support in the selected target lower-zero face. -/
theorem boundaryTargetInChartPieceIntegrand_tsupport_subset_targetPieceSet_of_support_subset
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d)
    (hsupport :
      Function.support (boundaryTargetInChartPieceIntegrand I x1 ω) ⊆
        boundaryChartTransitionBoundaryImage I x0 x1 a b) :
    tsupport (boundaryTargetInChartPieceIntegrand I x1 ω) ⊆
      boundaryTargetInChartPieceSet c d := by
  have hboundary :
      tsupport (boundaryTargetInChartPieceIntegrand I x1 ω) ⊆
        boundaryChartTransitionBoundaryImage I x0 x1 a b :=
    boundaryTargetInChartPieceIntegrand_tsupport_subset_boundaryImage_of_support_subset
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (c := c) (d := d) himage hsupport
  have hsubset :
      boundaryChartTransitionBoundaryImage I x0 x1 a b ⊆
        boundaryTargetInChartPieceSet (n := n) c d := by
    rw [boundaryChartTransitionBoundaryImage_eq_lowerZeroFaceDomain_of_imageData
      (I := I) himage]
    simp [boundaryTargetInChartPieceSet]
  exact hboundary.trans hsubset

/-- Pointwise nonzero version of
`boundaryTargetInChartPieceIntegrand_tsupport_subset_targetPieceSet_of_support_subset`. -/
theorem boundaryTargetInChartPieceIntegrand_tsupport_subset_targetPieceSet_of_nonzero_mem
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d)
    (hmem :
      ∀ u, boundaryTargetInChartPieceIntegrand I x1 ω u ≠ 0 →
        u ∈ boundaryChartTransitionBoundaryImage I x0 x1 a b) :
    tsupport (boundaryTargetInChartPieceIntegrand I x1 ω) ⊆
      boundaryTargetInChartPieceSet c d :=
  boundaryTargetInChartPieceIntegrand_tsupport_subset_targetPieceSet_of_support_subset
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    (a := a) (b := b) (c := c) (d := d) himage
    (boundaryTargetInChartPieceIntegrand_support_subset_boundaryImage_of_nonzero_mem
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) hmem)

end BasicScalarImageSupport

section CoverIndexedScalarImageSupport

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

/-- Cover-indexed scalar support-on-image hypothesis, written as a reusable
field type. -/
abbrev BoundaryScalarSupportSubsetImageField : Prop :=
  ∀ i : {x : M // x ∈ C.boundaryCenters},
    Function.support
        (boundaryTargetInChartPieceIntegrand I (D.targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
      boundaryChartTransitionBoundaryImage I
        (C.boundaryChart i.1) (D.targetChart i)
        (C.boundaryLower i.1) (C.boundaryUpper i.1)

/-- Cover-indexed pointwise nonzero form of the scalar support-on-image
hypothesis. -/
abbrev BoundaryScalarNonzeroMemImageField : Prop :=
  ∀ i : {x : M // x ∈ C.boundaryCenters},
    ∀ u,
      boundaryTargetInChartPieceIntegrand I (D.targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i)) u ≠ 0 →
        u ∈
          boundaryChartTransitionBoundaryImage I
            (C.boundaryChart i.1) (D.targetChart i)
            (C.boundaryLower i.1) (C.boundaryUpper i.1)

/-- Scalar support on the boundary-transition image gives topological support
on the selected target boundary image. -/
theorem boundaryScalar_tsupport_subset_boundaryImage_of_support_subset
    (hsupport : D.BoundaryScalarSupportSubsetImageField)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (boundaryTargetInChartPieceIntegrand I (D.targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
      boundaryChartTransitionBoundaryImage I
        (C.boundaryChart i.1) (D.targetChart i)
        (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  boundaryTargetInChartPieceIntegrand_tsupport_subset_boundaryImage_of_support_subset
    (I := I)
    (x0 := C.boundaryChart i.1) (x1 := D.targetChart i)
    (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
    (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
    (c := D.targetLower i) (d := D.targetUpper i)
    (D.boundaryChartSelectedBoxImageData i) (hsupport i)

/-- Pointwise nonzero version of
`boundaryScalar_tsupport_subset_boundaryImage_of_support_subset`. -/
theorem boundaryScalar_tsupport_subset_boundaryImage_of_nonzero_mem
    (hmem : D.BoundaryScalarNonzeroMemImageField)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (boundaryTargetInChartPieceIntegrand I (D.targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
      boundaryChartTransitionBoundaryImage I
        (C.boundaryChart i.1) (D.targetChart i)
        (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  D.boundaryScalar_tsupport_subset_boundaryImage_of_support_subset
    (fun i =>
      boundaryTargetInChartPieceIntegrand_support_subset_boundaryImage_of_nonzero_mem
        (I := I)
        (x0 := C.boundaryChart i.1) (x1 := D.targetChart i)
        (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
        (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
        (hmem i))
    i

/-- Scalar support on the boundary-transition image gives the exact
`boundaryPiece_tsupport_subset` field used by target-boundary measure data. -/
theorem boundaryPiece_tsupport_subset_of_scalarSupport_subset
    (hsupport : D.BoundaryScalarSupportSubsetImageField)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (P.coverIndexBoundaryTargetPieceIntegrand D.targetChart ω (Sum.inr i)) ⊆
      P.coverIndexBoundaryTargetPieceSet D.targetLower D.targetUpper
        (Sum.inr i) := by
  simpa [SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceSet,
    SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceIntegrand,
    boundaryTargetInChartPieceSet] using
    boundaryTargetInChartPieceIntegrand_tsupport_subset_targetPieceSet_of_support_subset
      (I := I)
      (x0 := C.boundaryChart i.1) (x1 := D.targetChart i)
      (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (c := D.targetLower i) (d := D.targetUpper i)
      (D.boundaryChartSelectedBoxImageData i) (hsupport i)

/-- Pointwise nonzero version of
`boundaryPiece_tsupport_subset_of_scalarSupport_subset`. -/
theorem boundaryPiece_tsupport_subset_of_scalarNonzero_mem
    (hmem : D.BoundaryScalarNonzeroMemImageField)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (P.coverIndexBoundaryTargetPieceIntegrand D.targetChart ω (Sum.inr i)) ⊆
      P.coverIndexBoundaryTargetPieceSet D.targetLower D.targetUpper
        (Sum.inr i) :=
  D.boundaryPiece_tsupport_subset_of_scalarSupport_subset
    (fun i =>
      boundaryTargetInChartPieceIntegrand_support_subset_boundaryImage_of_nonzero_mem
        (I := I)
        (x0 := C.boundaryChart i.1) (x1 := D.targetChart i)
        (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
        (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
        (hmem i))
    i

/-- Boundary piece continuity generated from localized chartwise smoothness,
without asking for ambient target support. -/
theorem boundaryPiece_continuousOn_of_localizedChartwiseSmooth
    (localizedChartwiseSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ManifoldForm.ChartwiseSmooth I
          (P.coverIndexLocalizedForm ω (Sum.inr i)))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.targetLower i) (D.targetUpper i) ⊆
          (extChartAt I (D.targetChart i)).target)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContinuousOn
      (P.coverIndexBoundaryTargetPieceIntegrand D.targetChart ω (Sum.inr i))
      (P.coverIndexBoundaryTargetPieceSet D.targetLower D.targetUpper
        (Sum.inr i)) := by
  simpa [SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceSet,
    SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceIntegrand] using
    boundaryTargetInChartPieceIntegrand_continuousOn_of_inChart_continuousOn
      (I := I) (x := D.targetChart i)
      (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
      (c := D.targetLower i) (d := D.targetUpper i)
      (D.targetLower_zero i) (D.targetLower_le_targetUpper i)
      ((D.targetInChart_contDiffOn_infty_of_localizedChartwiseSmooth
        localizedChartwiseSmooth targetBox_subset_target i).continuousOn)

/-- Target-boundary measure data from an oriented atlas, with boundary scalar
image support replacing the stronger ambient target-image support hypothesis. -/
def toTargetBoundaryMeasureDataOfOrientedAtlasScalarImageSupport
    [IsManifold I 1 M]
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      D.targetChart i ∈ A.charts)
    (localizedChartwiseSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ManifoldForm.ChartwiseSmooth I
          (P.coverIndexLocalizedForm ω (Sum.inr i)))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.targetLower i) (D.targetUpper i) ⊆
          (extChartAt I (D.targetChart i)).target)
    (scalarSupport : D.BoundaryScalarSupportSubsetImageField)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum D.targetChart ω y
          ∂(volume : Measure (Fin n → Real))) :
    CoverIndexedTargetBoundaryMeasureData
      (I := I) (K := K) C P ω :=
  CoverIndexedTargetBoundaryMeasureData.ofTargetSelectionOrientedAtlas
    (C := C) (P := P) (ω := ω)
    (targetChart := D.targetChart)
    localData A (fun i => D.targetSelection i)
    (fun i => D.sourceTargetSelectedBox i)
    hsource htarget
    (P.coverIndexBoundaryTargetPieceSum D.targetChart ω)
    globalIntegral globalIntegral_eq_integral
    (fun i =>
      P.coverIndexBoundaryTargetPieceSet_isCompact
        D.targetLower D.targetUpper (Sum.inr i))
    (D.boundaryPiece_continuousOn_of_localizedChartwiseSmooth
      localizedChartwiseSmooth targetBox_subset_target)
    (D.boundaryPiece_tsupport_subset_of_scalarSupport_subset scalarSupport)
    (P.coverIndexBoundaryTargetPieceSum_ae_eq_pieceSum D.targetChart ω)

/-- Pointwise nonzero variant of
`toTargetBoundaryMeasureDataOfOrientedAtlasScalarImageSupport`. -/
def toTargetBoundaryMeasureDataOfOrientedAtlasScalarNonzero
    [IsManifold I 1 M]
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      D.targetChart i ∈ A.charts)
    (localizedChartwiseSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ManifoldForm.ChartwiseSmooth I
          (P.coverIndexLocalizedForm ω (Sum.inr i)))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.targetLower i) (D.targetUpper i) ⊆
          (extChartAt I (D.targetChart i)).target)
    (scalarNonzero : D.BoundaryScalarNonzeroMemImageField)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum D.targetChart ω y
          ∂(volume : Measure (Fin n → Real))) :
    CoverIndexedTargetBoundaryMeasureData
      (I := I) (K := K) C P ω :=
  D.toTargetBoundaryMeasureDataOfOrientedAtlasScalarImageSupport
    localData A hsource htarget localizedChartwiseSmooth
    targetBox_subset_target
    (fun i =>
      boundaryTargetInChartPieceIntegrand_support_subset_boundaryImage_of_nonzero_mem
        (I := I)
        (x0 := C.boundaryChart i.1) (x1 := D.targetChart i)
        (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
        (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
        (scalarNonzero i))
    globalIntegral globalIntegral_eq_integral

/-- Target-boundary measure data from oriented-manifold data, with boundary
scalar image support replacing ambient target-image support. -/
def toTargetBoundaryMeasureDataOfOrientedManifoldScalarImageSupport
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (localizedChartwiseSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ManifoldForm.ChartwiseSmooth I
          (P.coverIndexLocalizedForm ω (Sum.inr i)))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.targetLower i) (D.targetUpper i) ⊆
          (extChartAt I (D.targetChart i)).target)
    (scalarSupport : D.BoundaryScalarSupportSubsetImageField)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum D.targetChart ω y
          ∂(volume : Measure (Fin n → Real))) :
    CoverIndexedTargetBoundaryMeasureData
      (I := I) (K := K) C P ω :=
  CoverIndexedTargetBoundaryMeasureData.ofTargetSelectionOrientedManifold
    (C := C) (P := P) (ω := ω)
    (targetChart := D.targetChart)
    localData (fun i => D.targetSelection i)
    (fun i => D.sourceTargetSelectedBox i)
    (P.coverIndexBoundaryTargetPieceSum D.targetChart ω)
    globalIntegral globalIntegral_eq_integral
    (fun i =>
      P.coverIndexBoundaryTargetPieceSet_isCompact
        D.targetLower D.targetUpper (Sum.inr i))
    (D.boundaryPiece_continuousOn_of_localizedChartwiseSmooth
      localizedChartwiseSmooth targetBox_subset_target)
    (D.boundaryPiece_tsupport_subset_of_scalarSupport_subset scalarSupport)
    (P.coverIndexBoundaryTargetPieceSum_ae_eq_pieceSum D.targetChart ω)

/-- Pointwise nonzero variant of
`toTargetBoundaryMeasureDataOfOrientedManifoldScalarImageSupport`. -/
def toTargetBoundaryMeasureDataOfOrientedManifoldScalarNonzero
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (localizedChartwiseSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ManifoldForm.ChartwiseSmooth I
          (P.coverIndexLocalizedForm ω (Sum.inr i)))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.targetLower i) (D.targetUpper i) ⊆
          (extChartAt I (D.targetChart i)).target)
    (scalarNonzero : D.BoundaryScalarNonzeroMemImageField)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum D.targetChart ω y
          ∂(volume : Measure (Fin n → Real))) :
    CoverIndexedTargetBoundaryMeasureData
      (I := I) (K := K) C P ω :=
  D.toTargetBoundaryMeasureDataOfOrientedManifoldScalarImageSupport
    localData localizedChartwiseSmooth targetBox_subset_target
    (fun i =>
      boundaryTargetInChartPieceIntegrand_support_subset_boundaryImage_of_nonzero_mem
        (I := I)
        (x0 := C.boundaryChart i.1) (x1 := D.targetChart i)
        (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
        (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
        (scalarNonzero i))
    globalIntegral globalIntegral_eq_integral

end CoverIndexedBoundaryTargetBoxData

end CoverIndexedScalarImageSupport

end Stokes

end
