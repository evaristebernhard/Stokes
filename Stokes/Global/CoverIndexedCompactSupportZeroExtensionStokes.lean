import Stokes.ManifoldFormZero
import Stokes.Global.CoverIndexedCompactSupportCInftyAssembly
import Stokes.Global.CoverIndexedBoundaryScalarSupportFromBoxes

/-!
# Zero-extension wrapper for compact-support represented Stokes

This file is a thin endpoint layer for the zero-extension route.

The existing represented endpoint
`compactSupportRepresentedStokesScalarInfty_of_orientedManifold` already has
the right local Stokes and boundary reconstruction content.  The purpose of
this file is to isolate the remaining endpoint inputs in the form needed by
the zero-extension plan:

* compact-support carrier data;
* natural `C^\infty` neighborhood data;
* selected target boundary boxes;
* target-box containment in chart targets;
* scalar support of the actual boundary integrand.

The final scalar-support field is the intended handoff point for the
zero-extension support workers.  As an immediately usable constructor, this
file also derives that scalar-support field from target ambient
`inChart` support in the selected target boxes.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportZeroExtensionStokes

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

/-- Boundary scalar-support data for the zero-extension endpoint.

This is deliberately stated at the level of the real scalar boundary
integrand.  Zero-extension support lemmas should target this field, avoiding
the false stronger claim that the full ambient target representative is
supported on the boundary image. -/
structure CoverIndexedCompactSupportZeroBoundarySupportData
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega) where
  scalarSupport : targetBox.BoundaryScalarSupportSubsetImageField

namespace CoverIndexedCompactSupportZeroBoundarySupportData

/-- Constructor from target-box support of the ambient target chart
representative.

This is the current non-zero-extension handoff.  Once the zero boundary
support worker proves the scalar support directly from `inChartZero`/local
box equality, it should feed the `scalarSupport` field above instead of this
stronger ambient support hypothesis. -/
def ofTargetInChartTSupportSubsetIcc
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (targetInChart_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (targetBox.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          Icc (targetBox.targetLower i) (targetBox.targetUpper i)) :
    CoverIndexedCompactSupportZeroBoundarySupportData
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      targetBox where
  scalarSupport :=
    targetBox.boundaryScalarSupportSubsetImageField_of_targetInChart_tsupport_subset_Icc
      targetInChart_tsupport_subset

end CoverIndexedCompactSupportZeroBoundarySupportData

/-- Grouped input for the compact-support represented Stokes endpoint along
the zero-extension route.

Compared with the raw scalar `C^\infty` endpoint, this record names the
boundary-support handoff separately.  The theorem below is intentionally only
an endpoint wrapper: it does not rebuild local Stokes, nor does it force any
particular proof of scalar boundary support. -/
structure CoverIndexedCompactSupportZeroExtensionStokesInput
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n)
    (muBulk : Measure (Fin (n + 1) → Real)) where
  carrierData :
    CoverIndexedCompactSupportCarrierData
      (I := I) (K := K) C P omega
  neighborhoodDataInfty :
    CoverIndexedCompactSupportNeighborhoodDataInfty
      (I := I) (K := K) C P omega
  measure_eq_volume :
    muBulk = (volume : Measure (Fin (n + 1) → Real))
  targetBox :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega
  targetBox_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
        (extChartAt I (targetBox.targetChart i)).target
  boundarySupport :
    CoverIndexedCompactSupportZeroBoundarySupportData
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      targetBox
  globalBoundaryIntegral : Real
  globalBoundaryIntegral_eq_integral :
    globalBoundaryIntegral =
      ∫ y, P.coverIndexBoundaryTargetPieceSum targetBox.targetChart omega y
        ∂(volume : Measure (Fin n → Real))

namespace CoverIndexedCompactSupportZeroExtensionStokesInput

variable
    (D :
      CoverIndexedCompactSupportZeroExtensionStokesInput
        (I := I) (K := K) C P omega muBulk)

/-- The assigned-self bulk input generated by the grouped zero-extension
endpoint data. -/
def assignedSelfBulkInput
    [IsFiniteMeasureOnCompacts muBulk] [IsManifold I ⊤ M] :
    CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P omega muBulk :=
  D.carrierData.assignedSelfBulkInputInfty
    (I := I) (K := K) (C := C) (P := P) (ω := omega)
    (μBulk := muBulk) D.neighborhoodDataInfty D.measure_eq_volume

/-- Compact-support represented Stokes from grouped zero-extension endpoint
data. -/
theorem representedStokes_of_orientedManifold
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    (D.assignedSelfBulkInput
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        (muBulk := muBulk)).globalIntegral =
      D.globalBoundaryIntegral := by
  exact
    compactSupportRepresentedStokesScalarInfty_of_orientedManifold
      (I := I) (K := K) (C := C) (P := P) (ω := omega)
      (μBulk := muBulk)
      D.carrierData D.neighborhoodDataInfty D.measure_eq_volume
      D.targetBox D.targetBox_subset_target D.boundarySupport.scalarSupport
      D.globalBoundaryIntegral D.globalBoundaryIntegral_eq_integral

end CoverIndexedCompactSupportZeroExtensionStokesInput

/-- Convenience constructor for the zero-extension endpoint input when scalar
boundary support is still obtained from target ambient `inChart` support in
the selected target boxes. -/
def compactSupportZeroExtensionStokesInputOfTargetInChartTSupport
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
    (targetInChart_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (targetBox.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          Icc (targetBox.targetLower i) (targetBox.targetUpper i))
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real))) :
    CoverIndexedCompactSupportZeroExtensionStokesInput
      (I := I) (K := K) C P omega muBulk where
  carrierData := carrierData
  neighborhoodDataInfty := neighborhoodDataInfty
  measure_eq_volume := measure_eq_volume
  targetBox := targetBox
  targetBox_subset_target := targetBox_subset_target
  boundarySupport :=
    CoverIndexedCompactSupportZeroBoundarySupportData.ofTargetInChartTSupportSubsetIcc
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      targetBox targetInChart_tsupport_subset
  globalBoundaryIntegral := globalBoundaryIntegral
  globalBoundaryIntegral_eq_integral := globalBoundaryIntegral_eq_integral

/-- Compact-support represented Stokes, stated with target-box support instead
of an explicit scalar-support field. -/
theorem compactSupportRepresentedStokesZeroExtension_of_targetInChartTSupport
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
    (targetInChart_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (targetBox.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          Icc (targetBox.targetLower i) (targetBox.targetUpper i))
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real))) :
    ((compactSupportZeroExtensionStokesInputOfTargetInChartTSupport
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        (muBulk := muBulk)
        carrierData neighborhoodDataInfty measure_eq_volume
        targetBox targetBox_subset_target targetInChart_tsupport_subset
        globalBoundaryIntegral globalBoundaryIntegral_eq_integral)
      |>.assignedSelfBulkInput
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        (muBulk := muBulk)).globalIntegral =
      globalBoundaryIntegral := by
  exact
    (compactSupportZeroExtensionStokesInputOfTargetInChartTSupport
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        (muBulk := muBulk)
        carrierData neighborhoodDataInfty measure_eq_volume
        targetBox targetBox_subset_target targetInChart_tsupport_subset
        globalBoundaryIntegral globalBoundaryIntegral_eq_integral)
      |>.representedStokes_of_orientedManifold
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        (muBulk := muBulk)

end CompactSupportZeroExtensionStokes

end Stokes

end
