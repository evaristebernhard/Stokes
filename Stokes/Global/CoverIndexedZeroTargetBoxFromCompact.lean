import Stokes.Global.InChartZeroSupportFromGlobal
import Stokes.Global.CoverIndexedZeroTargetBoxSupport

/-!
# Zero target-box support from compact coordinate images

This file is the honest compact-support bridge for target zero representatives.

The global compact-support theorem gives support in the coordinate image of the
global support set `K`.  To get support in a selected target box, we keep the
real geometric hypothesis explicit:

`chartCoordinateImage I (targetChart i) K ⊆ Icc (targetLower i) (targetUpper i)`.

In particular, this file does not claim that a selected boundary image contains
the whole compact coordinate image.  It only packages the monotonicity step and
then feeds it to the zero-boundary scalar support constructors.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BasicInChartZeroTargetBoxFromCompact

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {x : M}
variable {ω : ManifoldForm I M n}
variable {c d : Fin (n + 1) → Real}

namespace ManifoldForm

/-- If a zero-extended chart representative is already supported in the compact
coordinate image, and that coordinate image lies in a target box, then it is
supported in the target box. -/
theorem inChartZero_tsupport_subset_Icc_of_tsupport_subset_chartCoordinateImage
    (hsupport :
      tsupport (inChartZero I x ω) ⊆ chartCoordinateImage I x K)
    (hcoord : chartCoordinateImage I x K ⊆ Icc c d) :
    tsupport (inChartZero I x ω) ⊆ Icc c d :=
  hsupport.trans hcoord

/-- Compact-support version of
`inChartZero_tsupport_subset_Icc_of_tsupport_subset_chartCoordinateImage`. -/
theorem inChartZero_tsupport_subset_Icc_of_globalManifoldSupport
    (hK : IsCompact K)
    (hsource : K ⊆ (extChartAt I x).source)
    (hωsupport : support I ω ⊆ K)
    (hcoord : chartCoordinateImage I x K ⊆ Icc c d) :
    tsupport (inChartZero I x ω) ⊆ Icc c d :=
  (inChartZero_tsupport_subset_chartCoordinateImage
    (I := I) (K := K) (x := x) (ω := ω)
    hK hsource hωsupport).trans hcoord

end ManifoldForm

end BasicInChartZeroTargetBoxFromCompact

section CoverIndexedZeroTargetBoxFromCompact

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

/-- The honest target-box containment field for the compact coordinate image in
each selected target chart. -/
abbrev TargetChartCoordinateImageSubsetIccField : Prop :=
  ∀ i : {x : M // x ∈ C.boundaryCenters},
    chartCoordinateImage I (D.targetChart i) K ⊆
      Icc (D.targetLower i) (D.targetUpper i)

/-- The target `Icc` support field for zero-extended target representatives. -/
abbrev TargetInChartZeroTSupportSubsetIccField : Prop :=
  ∀ i : {x : M // x ∈ C.boundaryCenters},
    tsupport
        (ManifoldForm.inChartZero I (D.targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
      Icc (D.targetLower i) (D.targetUpper i)

/-- Push the existing coordinate-image support field into the selected target
boxes. -/
theorem targetInChartZero_tsupport_subset_Icc_of_chartCoordinateImage_subset
    (hcoord : D.TargetChartCoordinateImageSubsetIccField)
    (hsupport : D.TargetInChartZeroTSupportSubsetCoordinateImageField) :
    D.TargetInChartZeroTSupportSubsetIccField := by
  intro i
  exact
    (hsupport i).trans (hcoord i)

/-- Global compact support plus target-chart source containment and the honest
coordinate-image-in-box hypothesis gives target `Icc` support for all target
zero representatives. -/
theorem targetInChartZero_tsupport_subset_Icc_of_globalManifoldSupport
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (D.targetChart i)).source)
    (hωsupport : ManifoldForm.support I ω ⊆ K)
    (hcoord : D.TargetChartCoordinateImageSubsetIccField) :
    D.TargetInChartZeroTSupportSubsetIccField :=
  D.targetInChartZero_tsupport_subset_Icc_of_chartCoordinateImage_subset
    hcoord
    (D.targetInChartZero_tsupport_subset_chartCoordinateImage_of_globalManifoldSupport
      hK hsource hωsupport)

/-- The same compact-support target-box bridge, immediately fed into the zero
boundary scalar support field. -/
theorem boundaryZeroScalarSupportSubsetImageField_of_globalManifoldSupport
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (D.targetChart i)).source)
    (hωsupport : ManifoldForm.support I ω ⊆ K)
    (hcoord : D.TargetChartCoordinateImageSubsetIccField) :
    D.BoundaryZeroScalarSupportSubsetImageField :=
  D.boundaryZeroScalarSupportSubsetImageField_of_targetInChartZero_tsupport_subset_Icc
    (D.targetInChartZero_tsupport_subset_Icc_of_globalManifoldSupport
      hK hsource hωsupport hcoord)

end CoverIndexedBoundaryTargetBoxData

end CoverIndexedZeroTargetBoxFromCompact

section CompactSupportZeroBoundarySupportFromCompact

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

/-- Boundary-support data for the zero-extension endpoint generated from
global compact support and an honest target coordinate-image box containment
field. -/
def ofGlobalManifoldSupportChartCoordinateImageSubsetIcc
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (targetBox.targetChart i)).source)
    (hωsupport : ManifoldForm.support I omega ⊆ K)
    (hcoord : targetBox.TargetChartCoordinateImageSubsetIccField)
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
  ofTargetInChartZeroTSupportSubsetIcc
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    targetBox
    (targetBox.targetInChartZero_tsupport_subset_Icc_of_globalManifoldSupport
      hK hsource hωsupport hcoord)
    oldScalarSupport_subset_targetFace targetBox_subset_target

end CoverIndexedCompactSupportZeroBoundarySupportData

end CompactSupportZeroBoundarySupportFromCompact

end Stokes

end
