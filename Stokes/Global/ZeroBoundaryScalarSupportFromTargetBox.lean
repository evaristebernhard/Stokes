import Stokes.Global.ZeroExtensionBoundaryScalar

/-!
# Zero boundary scalar support from target boxes

This file proves the zero-extension boundary scalar support bridge: support of
the zero-extended ambient target representative inside a selected target box
forces support of its lower-face scalar boundary integrand inside the selected
boundary transition image.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BasicZeroBoundaryScalarSupportFromTargetBox

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/-- A nonzero zero-extended boundary scalar evaluation lies on the selected
target lower-zero face when the zero-extended ambient representative is
supported in the ambient target box. -/
theorem boundaryTargetInChartZeroPieceIntegrand_nonzero_mem_targetPieceSet_of_inChartZero_tsupport_subset_Icc
    {x : M} {ω : ManifoldForm I M n}
    {c d : Fin (n + 1) → Real}
    (hsupport :
      tsupport (ManifoldForm.inChartZero I x ω) ⊆ Icc c d)
    {u : Fin n → Real}
    (h :
      boundaryTargetInChartZeroPieceIntegrand I x ω u ≠ 0) :
    u ∈ boundaryTargetInChartPieceSet (n := n) c d := by
  have hform :
      ManifoldForm.inChartZero I x ω (boundaryInclusion n u) ≠ 0 :=
    boundaryTargetInChartZeroPieceIntegrand_nonzero_inChartZero_nonzero
      (I := I) (x := x) (ω := ω) h
  have hsupp :
      boundaryInclusion n u ∈
        Function.support (ManifoldForm.inChartZero I x ω) :=
    hform
  have hIcc :
      boundaryInclusion n u ∈ Icc c d :=
    hsupport (subset_tsupport (ManifoldForm.inChartZero I x ω) hsupp)
  simpa [boundaryTargetInChartPieceSet] using
    (mem_lowerZeroFaceDomain_of_boundaryInclusion_mem_Icc
      (n := n) (a := c) (b := d) hIcc)

/-- Pointwise source of the zero boundary scalar image-support condition:
target-box support of `ManifoldForm.inChartZero` plus selected image data sends
every nonzero zero boundary scalar point into the image of the selected source
boundary box. -/
theorem boundaryTargetInChartZeroPieceIntegrand_nonzero_mem_boundaryImage_of_inChartZero_tsupport_subset_Icc
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b c d : Fin (n + 1) → Real}
    (hc0 : c 0 = 0) (hcd : c ≤ d)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d)
    (hsupport :
      tsupport (ManifoldForm.inChartZero I x1 ω) ⊆ Icc c d)
    {u : Fin n → Real}
    (h :
      boundaryTargetInChartZeroPieceIntegrand I x1 ω u ≠ 0) :
    u ∈ boundaryChartTransitionBoundaryImage I x0 x1 a b := by
  have hface :
      u ∈ boundaryTargetInChartPieceSet (n := n) c d :=
    boundaryTargetInChartZeroPieceIntegrand_nonzero_mem_targetPieceSet_of_inChartZero_tsupport_subset_Icc
      (I := I) (x := x1) (ω := ω) (c := c) (d := d)
      hsupport h
  have _ :
      boundaryInclusion n u ∈ Icc c d :=
    boundaryInclusion_mem_Icc_of_mem_lowerZeroFaceDomain
      (n := n) (a := c) (b := d) hc0 hcd
      (by simpa [boundaryTargetInChartPieceSet] using hface)
  rw [boundaryChartTransitionBoundaryImage_eq_lowerZeroFaceDomain_of_imageData
    (I := I) himage]
  simpa [boundaryTargetInChartPieceSet] using hface

/-- Support-set version of
`boundaryTargetInChartZeroPieceIntegrand_nonzero_mem_boundaryImage_of_inChartZero_tsupport_subset_Icc`. -/
theorem boundaryTargetInChartZeroPieceIntegrand_support_subset_boundaryImage_of_inChartZero_tsupport_subset_Icc
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b c d : Fin (n + 1) → Real}
    (hc0 : c 0 = 0) (hcd : c ≤ d)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d)
    (hsupport :
      tsupport (ManifoldForm.inChartZero I x1 ω) ⊆ Icc c d) :
    Function.support (boundaryTargetInChartZeroPieceIntegrand I x1 ω) ⊆
      boundaryChartTransitionBoundaryImage I x0 x1 a b := by
  intro u hu
  exact
    boundaryTargetInChartZeroPieceIntegrand_nonzero_mem_boundaryImage_of_inChartZero_tsupport_subset_Icc
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (c := c) (d := d)
      hc0 hcd himage hsupport hu

end BasicZeroBoundaryScalarSupportFromTargetBox

section CoverIndexedZeroBoundaryScalarSupportFromTargetBox

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

/-- Target-box support of the zero-extended ambient target representatives gives
the zero scalar support-on-image field. -/
theorem boundaryZeroScalarSupportSubsetImageField_of_targetInChartZero_tsupport_subset_Icc
    (targetInChartZero_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChartZero I (D.targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          Icc (D.targetLower i) (D.targetUpper i)) :
    D.BoundaryZeroScalarSupportSubsetImageField := by
  intro i
  exact
    boundaryTargetInChartZeroPieceIntegrand_support_subset_boundaryImage_of_inChartZero_tsupport_subset_Icc
      (I := I)
      (x0 := C.boundaryChart i.1) (x1 := D.targetChart i)
      (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (c := D.targetLower i) (d := D.targetUpper i)
      (D.targetLower_zero i) (D.targetLower_le_targetUpper i)
      (D.boundaryChartSelectedBoxImageData i)
      (targetInChartZero_tsupport_subset i)

end CoverIndexedBoundaryTargetBoxData

end CoverIndexedZeroBoundaryScalarSupportFromTargetBox

end Stokes

end
