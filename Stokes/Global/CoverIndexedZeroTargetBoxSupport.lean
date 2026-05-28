import Stokes.Global.CoverIndexedZeroEndpointScalarSupport
import Stokes.Global.ZeroBoundaryScalarSupportFromTargetBox

/-!
# Zero target-box support for cover-indexed boundary pieces

This file is the zero-extension analogue of
`CoverIndexedBoundaryScalarSupportFromBoxes`.

The mathematical point is local and small: if the zero-extended ambient target
chart representative is topologically supported in the selected target box
`Icc c d`, then any nonzero zero-boundary scalar on the lower face lies in the
selected target lower-zero face.  The stored
`boundaryChartSelectedBoxImageData` then identifies that face with the image of
the selected source boundary box.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedBoundaryZeroScalarSupportFromBoxes

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

/-- Cover-indexed pointwise nonzero form of the zero-scalar support-on-image
hypothesis. -/
abbrev BoundaryZeroScalarNonzeroMemImageField : Prop :=
  ∀ i : {x : M // x ∈ C.boundaryCenters},
    ∀ u,
      boundaryTargetInChartZeroPieceIntegrand I (D.targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i)) u ≠ 0 →
        u ∈
          boundaryChartTransitionBoundaryImage I
            (C.boundaryChart i.1) (D.targetChart i)
            (C.boundaryLower i.1) (C.boundaryUpper i.1)

/-- Target-box support of the zero-extended ambient target representatives
gives the pointwise nonzero zero-scalar image field. -/
theorem boundaryZeroScalarNonzeroMemImageField_of_targetInChartZero_tsupport_subset_Icc
    (targetInChartZero_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChartZero I (D.targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          Icc (D.targetLower i) (D.targetUpper i)) :
    D.BoundaryZeroScalarNonzeroMemImageField := by
  intro i u hu
  exact
    boundaryTargetInChartZeroPieceIntegrand_nonzero_mem_boundaryImage_of_inChartZero_tsupport_subset_Icc
      (I := I)
      (x0 := C.boundaryChart i.1) (x1 := D.targetChart i)
      (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (c := D.targetLower i) (d := D.targetUpper i)
      (D.targetLower_zero i) (D.targetLower_le_targetUpper i)
      (D.boundaryChartSelectedBoxImageData i)
      (targetInChartZero_tsupport_subset i) hu

end CoverIndexedBoundaryTargetBoxData

end CoverIndexedBoundaryZeroScalarSupportFromBoxes

section CompactSupportZeroEndpointTargetBoxSupport

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedCompactSupportZeroBoundarySupportData

/-- Boundary-support data for the zero-extension endpoint from target-box
support of the zero-extended ambient target representatives.

This is still parameterized by the old-scalar face support required to transfer
the zero-scalar image support back to the old scalar boundary representative
used by the existing endpoint. -/
def ofTargetInChartZeroTSupportSubsetIcc
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (targetInChartZero_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChartZero I (targetBox.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          Icc (targetBox.targetLower i) (targetBox.targetUpper i))
    (oldScalarSupport_subset_targetFace :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Function.support
            (boundaryTargetInChartPieceIntegrand I (targetBox.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          boundaryTargetInChartPieceSet (n := n)
            (targetBox.targetLower i) (targetBox.targetUpper i))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target) :
    CoverIndexedCompactSupportZeroBoundarySupportData
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      targetBox :=
  ofZeroScalarSupportOnTargetBox
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    targetBox
    (targetBox.boundaryZeroScalarSupportSubsetImageField_of_targetInChartZero_tsupport_subset_Icc
      targetInChartZero_tsupport_subset)
    oldScalarSupport_subset_targetFace targetBox_subset_target

end CoverIndexedCompactSupportZeroBoundarySupportData

end CompactSupportZeroEndpointTargetBoxSupport

end Stokes

end
