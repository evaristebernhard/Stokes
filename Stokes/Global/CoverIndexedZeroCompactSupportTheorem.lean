import Stokes.Global.CoverIndexedZeroNaturalTheorem
import Stokes.Global.CoverIndexedZeroTargetBoxSupport
import Stokes.Global.InChartZeroSupportFromGlobal

/-!
# Compact-support zero-extension represented Stokes theorem

Endpoint wrappers for the zero-extension route.  The first theorem replaces
the zero-scalar support input by target-box support of the zero-extended target
chart representative.  The second derives that target-box support from global
compact support plus coordinate-image containment.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportZeroCompactSupportTheorem

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {muBulk : Measure (Fin (n + 1) → Real)}

/-- Target-box data for the zero-extension compact-support endpoint.

This record packages the target-domain, zero target-box support, and old
scalar face-support inputs that otherwise have to be threaded separately
through the represented endpoint. -/
structure CoverIndexedZeroCompactSupportTargetBoxData
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n) where
  targetBox :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega
  targetBox_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
        (extChartAt I (targetBox.targetChart i)).target
  targetInChartZero_tsupport_subset :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      tsupport
          (ManifoldForm.inChartZero I (targetBox.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
        Icc (targetBox.targetLower i) (targetBox.targetUpper i)
  oldScalarSupport_subset_targetFace :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Function.support
          (boundaryTargetInChartPieceIntegrand I (targetBox.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
        boundaryTargetInChartPieceSet (n := n)
          (targetBox.targetLower i) (targetBox.targetUpper i)

/-- Compact-support represented Stokes from zero target-chart box support.

Compared with `compactSupportRepresentedStokesZeroExtension_natural`, callers no
longer provide `BoundaryZeroScalarSupportSubsetImageField`; it is derived from
`targetInChartZero_tsupport_subset`. -/
theorem compactSupportRepresentedStokesZeroExtension_of_targetInChartZeroTSupport
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P omega)
    (neighborhoodDataInfty :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (measure_eq_volume :
      muBulk = (volume : Measure (Fin (n + 1) → Real)))
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target)
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
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real))) :
    (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) neighborhoodDataInfty measure_eq_volume).globalIntegral =
      globalBoundaryIntegral := by
  exact
    compactSupportRepresentedStokesZeroExtension_natural
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)
      carrierData neighborhoodDataInfty measure_eq_volume
      targetBox targetBox_subset_target
      (targetBox.boundaryZeroScalarSupportSubsetImageField_of_targetInChartZero_tsupport_subset_Icc
        targetInChartZero_tsupport_subset)
      oldScalarSupport_subset_targetFace
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral

/-- Record-packaged compact-support represented Stokes from zero target-chart
box support.

Compared with `compactSupportRepresentedStokesZeroExtension_natural`, the
target-box support handoff is supplied by one natural record instead of three
separate endpoint-facing support/domain hypotheses. -/
theorem compactSupportRepresentedStokesZeroExtension_of_targetBoxData
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P omega)
    (neighborhoodDataInfty :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (measure_eq_volume :
      muBulk = (volume : Measure (Fin (n + 1) → Real)))
    (targetData :
      CoverIndexedZeroCompactSupportTargetBoxData
        (I := I) (K := K) C P omega)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum targetData.targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real))) :
    (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) neighborhoodDataInfty measure_eq_volume).globalIntegral =
      globalBoundaryIntegral := by
  exact
    compactSupportRepresentedStokesZeroExtension_of_targetInChartZeroTSupport
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)
      carrierData neighborhoodDataInfty measure_eq_volume
      targetData.targetBox targetData.targetBox_subset_target
      targetData.targetInChartZero_tsupport_subset
      targetData.oldScalarSupport_subset_targetFace
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral

/-- Compact-support represented Stokes from global support and coordinate-image
containment of the selected target boxes.

This wrapper starts from manifold-side compact support: after choosing target
boxes that contain each target chart coordinate image of `K`, `inChartZero`
support in those boxes is automatic. -/
theorem compactSupportRepresentedStokesZeroExtension_of_globalSupport_coordinateImage
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P omega)
    (neighborhoodDataInfty :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (measure_eq_volume :
      muBulk = (volume : Measure (Fin (n + 1) → Real)))
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target)
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (targetBox.targetChart i)).source)
    (homegaSupport : ManifoldForm.support I omega ⊆ K)
    (coordinateImage_subset_targetBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        chartCoordinateImage I (targetBox.targetChart i) K ⊆
          Icc (targetBox.targetLower i) (targetBox.targetUpper i))
    (oldScalarSupport_subset_targetFace :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Function.support
            (boundaryTargetInChartPieceIntegrand I (targetBox.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          boundaryTargetInChartPieceSet (n := n)
            (targetBox.targetLower i) (targetBox.targetUpper i))
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real))) :
    (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) neighborhoodDataInfty measure_eq_volume).globalIntegral =
      globalBoundaryIntegral := by
  have hzeroCoord :
      targetBox.TargetInChartZeroTSupportSubsetCoordinateImageField :=
    targetBox.targetInChartZero_tsupport_subset_chartCoordinateImage_of_globalManifoldSupport
      (I := I) (K := K) (C := C) (P := P) (ω := omega)
      hK hsource homegaSupport
  exact
    compactSupportRepresentedStokesZeroExtension_of_targetInChartZeroTSupport
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)
      carrierData neighborhoodDataInfty measure_eq_volume
      targetBox targetBox_subset_target
      (fun i y hy => coordinateImage_subset_targetBox i (hzeroCoord i hy))
      oldScalarSupport_subset_targetFace
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral

end CompactSupportZeroCompactSupportTheorem

end Stokes

end
