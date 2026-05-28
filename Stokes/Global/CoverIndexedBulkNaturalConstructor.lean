import Stokes.Global.CoverIndexedNaturalConstructor
import Stokes.Global.CoverIndexedBulkContinuityConstructor
import Stokes.Global.CoverIndexedBulkInitialIntegralConstructor

/-!
# Natural bulk constructors for the cover-indexed compact-support route

`CoverIndexedCoordinateBulkData` still asks for closed-carrier continuity of
each localized scalar bulk piece.  In the geometric construction this is not an
independent analytic datum: it follows from the smoothness package
`CoverIndexedBulkSmoothnessFields`.

This file removes that hand-filled continuity field for the bulk side, while
leaving the genuinely mathematical bulk inputs explicit:

* support of each localized scalar piece in the assigned coordinate box;
* the local assigned-box set-integral identity;
* a.e. differentiability for the finite-sum reconstruction.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkNaturalConstructor

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {μBulk : Measure (Fin (n + 1) → Real)}

namespace CoverIndexedCoordinateBulkData

/--
Construct coordinate bulk data from the natural smoothness package.

Compared with `CoverIndexedCoordinateBulkData`, the caller no longer supplies
`piece_continuousOn_closedCarrier`; it is generated from
`CoverIndexedBulkSmoothnessFields`.
-/
def ofBulkSmoothness
    (sourceChart targetChart : M)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, bulkIntegrand I sourceChart targetChart ω y ∂μBulk)
    (formSupport_subset : ManifoldForm.support I ω ⊆ K)
    (smooth :
      SupportControlledSelectedPartition.CoverIndexedBulkSmoothnessFields
        (C := C) P ω sourceChart targetChart)
    (piece_tsupport_subset_assigned :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I sourceChart targetChart
                (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_assigned :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in C.assignedCoordinateBox j,
            bulkIntegrand I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j) y ∂μBulk)
    (piece_differentiable_ae :
      ∀ᶠ y in ae μBulk,
        ∀ j : C.CoverIndex,
          DifferentiableAt Real
            (ManifoldForm.transitionPullbackInChart I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j)) y) :
    CoverIndexedCoordinateBulkData
      (I := I) (K := K) C P ω μBulk where
  sourceChart := sourceChart
  targetChart := targetChart
  globalIntegral := globalIntegral
  globalIntegral_eq_integral := globalIntegral_eq_integral
  formSupport_subset := formSupport_subset
  piece_continuousOn_closedCarrier :=
    smooth.piece_continuousOn_closedCarrier
  piece_tsupport_subset_assigned := piece_tsupport_subset_assigned
  localBulk_eq_setIntegral_assigned := localBulk_eq_setIntegral_assigned
  piece_differentiable_ae := piece_differentiable_ae

@[simp]
theorem ofBulkSmoothness_sourceChart
    (sourceChart targetChart : M)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, bulkIntegrand I sourceChart targetChart ω y ∂μBulk)
    (formSupport_subset : ManifoldForm.support I ω ⊆ K)
    (smooth :
      SupportControlledSelectedPartition.CoverIndexedBulkSmoothnessFields
        (C := C) P ω sourceChart targetChart)
    (piece_tsupport_subset_assigned :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I sourceChart targetChart
                (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_assigned :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in C.assignedCoordinateBox j,
            bulkIntegrand I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j) y ∂μBulk)
    (piece_differentiable_ae :
      ∀ᶠ y in ae μBulk,
        ∀ j : C.CoverIndex,
          DifferentiableAt Real
            (ManifoldForm.transitionPullbackInChart I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j)) y) :
    (ofBulkSmoothness
      (C := C) (P := P) (ω := ω) (μBulk := μBulk)
      sourceChart targetChart globalIntegral globalIntegral_eq_integral
      formSupport_subset smooth piece_tsupport_subset_assigned
      localBulk_eq_setIntegral_assigned piece_differentiable_ae).sourceChart =
      sourceChart :=
  rfl

@[simp]
theorem ofBulkSmoothness_targetChart
    (sourceChart targetChart : M)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, bulkIntegrand I sourceChart targetChart ω y ∂μBulk)
    (formSupport_subset : ManifoldForm.support I ω ⊆ K)
    (smooth :
      SupportControlledSelectedPartition.CoverIndexedBulkSmoothnessFields
        (C := C) P ω sourceChart targetChart)
    (piece_tsupport_subset_assigned :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I sourceChart targetChart
                (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_assigned :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in C.assignedCoordinateBox j,
            bulkIntegrand I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j) y ∂μBulk)
    (piece_differentiable_ae :
      ∀ᶠ y in ae μBulk,
        ∀ j : C.CoverIndex,
          DifferentiableAt Real
            (ManifoldForm.transitionPullbackInChart I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j)) y) :
    (ofBulkSmoothness
      (C := C) (P := P) (ω := ω) (μBulk := μBulk)
      sourceChart targetChart globalIntegral globalIntegral_eq_integral
      formSupport_subset smooth piece_tsupport_subset_assigned
      localBulk_eq_setIntegral_assigned piece_differentiable_ae).targetChart =
      targetChart :=
  rfl

end CoverIndexedCoordinateBulkData

namespace SupportControlledSelectedPartition

/--
Canonical coordinate bulk data from natural bulk smoothness and the remaining
genuine bulk facts.
-/
def coordinateBulkData_of_bulkSmoothness
    (P : SupportControlledSelectedPartition C)
    (sourceChart targetChart : M)
    (globalBulkIntegral : Real)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral =
        ∫ y, bulkIntegrand I sourceChart targetChart ω y ∂μBulk)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (smooth :
      CoverIndexedBulkSmoothnessFields (C := C) P ω sourceChart targetChart)
    (piece_tsupport_subset_assigned :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I sourceChart targetChart
                (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_assigned :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in C.assignedCoordinateBox j,
            bulkIntegrand I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j) y ∂μBulk)
    (hdiff :
      ∀ᶠ y in ae μBulk,
        ∀ j : C.CoverIndex,
          DifferentiableAt Real
            (ManifoldForm.transitionPullbackInChart I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j)) y) :
    CoverIndexedCoordinateBulkData
      (I := I) (K := K) C P ω μBulk :=
  CoverIndexedCoordinateBulkData.ofBulkSmoothness
    (C := C) (P := P) (ω := ω) (μBulk := μBulk)
    sourceChart targetChart globalBulkIntegral
    globalBulkIntegral_eq_integral hωsupp smooth
    piece_tsupport_subset_assigned localBulk_eq_setIntegral_assigned hdiff

/--
Closed-carrier bulk data from natural bulk smoothness.

This is the bulk-side input expected by the represented global assembly, with
continuity and the assigned-box-to-closed-carrier transport generated by the
existing constructors.
-/
def coordinateClosedCarrierBulkData_of_bulkSmoothness
    [IsFiniteMeasureOnCompacts μBulk]
    (P : SupportControlledSelectedPartition C)
    (sourceChart targetChart : M)
    (globalBulkIntegral : Real)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral =
        ∫ y, bulkIntegrand I sourceChart targetChart ω y ∂μBulk)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (smooth :
      CoverIndexedBulkSmoothnessFields (C := C) P ω sourceChart targetChart)
    (piece_tsupport_subset_assigned :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I sourceChart targetChart
                (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_assigned :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in C.assignedCoordinateBox j,
            bulkIntegrand I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j) y ∂μBulk)
    (hdiff :
      ∀ᶠ y in ae μBulk,
        ∀ j : C.CoverIndex,
          DifferentiableAt Real
            (ManifoldForm.transitionPullbackInChart I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j)) y) :
    CoverIndexedClosedCarrierBulkData
      (I := I) (K := K) (μBulk := μBulk) C P ω :=
  (P.coordinateBulkData_of_bulkSmoothness
    (ω := ω) (μBulk := μBulk)
    sourceChart targetChart globalBulkIntegral
    globalBulkIntegral_eq_integral hωsupp smooth
    piece_tsupport_subset_assigned localBulk_eq_setIntegral_assigned hdiff
    ).toClosedCarrierBulkData

/--
Resolved bulk fields from natural bulk smoothness.
-/
def coordinateResolvedBulkFields_of_bulkSmoothness
    [IsFiniteMeasureOnCompacts μBulk]
    (P : SupportControlledSelectedPartition C)
    (sourceChart targetChart : M)
    (globalBulkIntegral : Real)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral =
        ∫ y, bulkIntegrand I sourceChart targetChart ω y ∂μBulk)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (smooth :
      CoverIndexedBulkSmoothnessFields (C := C) P ω sourceChart targetChart)
    (piece_tsupport_subset_assigned :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I sourceChart targetChart
                (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_assigned :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in C.assignedCoordinateBox j,
            bulkIntegrand I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j) y ∂μBulk)
    (hdiff :
      ∀ᶠ y in ae μBulk,
        ∀ j : C.CoverIndex,
          DifferentiableAt Real
            (ManifoldForm.transitionPullbackInChart I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j)) y) :
    CoverIndexedResolvedBulkFields
      (C := C) (ω := ω)
      (αBulk := Fin (n + 1) → Real) (μBulk := μBulk) P :=
  (P.coordinateClosedCarrierBulkData_of_bulkSmoothness
    (ω := ω) (μBulk := μBulk)
    sourceChart targetChart globalBulkIntegral
    globalBulkIntegral_eq_integral hωsupp smooth
    piece_tsupport_subset_assigned localBulk_eq_setIntegral_assigned hdiff
    ).toResolvedBulkFields

end SupportControlledSelectedPartition

end BulkNaturalConstructor

end Stokes

end
