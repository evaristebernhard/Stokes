import Stokes.Global.CoverIndexedCompactSupportZeroExtensionStokes
import Stokes.Global.ZeroExtensionBoundaryScalar

/-!
# Zero-extension endpoint scalar-support constructors

This file removes the last endpoint-facing use of ambient target
`inChart`-support for boundary scalar support.

The compact-support zero-extension endpoint consumes the old scalar boundary
integrand, because the existing represented Stokes assembly is phrased in
terms of the old chart representatives.  The support information, however, can
come from the zero-extended boundary scalar.  The bridge here packages the
existing pointwise transfer lemma:

* zero scalar support is contained in the selected boundary image;
* old scalar support is confined to the selected target face;
* the selected target box lies in the target chart.

Together these give the scalar-support field required by the endpoint.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportZeroEndpointScalarSupport

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

namespace CoverIndexedCompactSupportZeroBoundarySupportData

/-- Boundary-support data for the zero-extension endpoint from zero scalar
support on the selected boundary image.

The old scalar integrand is only required to have ordinary support on the
selected target face.  The zero scalar support supplies the image condition,
and `targetBox_subset_target` is exactly the domain where old and zero scalar
integrands agree. -/
def ofZeroScalarSupportOnTargetBox
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (zeroScalarSupport :
      targetBox.BoundaryZeroScalarSupportSubsetImageField)
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
      targetBox where
  scalarSupport :=
    targetBox.boundaryScalarSupportSubsetImageField_of_zeroScalarSupport_on_targetBox
      zeroScalarSupport oldScalarSupport_subset_targetFace targetBox_subset_target

end CoverIndexedCompactSupportZeroBoundarySupportData

/-- Convenience constructor for the zero-extension endpoint input from zero
boundary scalar support plus the old-scalar face-support condition. -/
def compactSupportZeroExtensionStokesInputOfZeroScalarSupport
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
    (zeroScalarSupport :
      targetBox.BoundaryZeroScalarSupportSubsetImageField)
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
    CoverIndexedCompactSupportZeroExtensionStokesInput
      (I := I) (K := K) C P omega muBulk where
  carrierData := carrierData
  neighborhoodDataInfty := neighborhoodDataInfty
  measure_eq_volume := measure_eq_volume
  targetBox := targetBox
  targetBox_subset_target := targetBox_subset_target
  boundarySupport :=
    CoverIndexedCompactSupportZeroBoundarySupportData.ofZeroScalarSupportOnTargetBox
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      targetBox zeroScalarSupport oldScalarSupport_subset_targetFace
      targetBox_subset_target
  globalBoundaryIntegral := globalBoundaryIntegral
  globalBoundaryIntegral_eq_integral := globalBoundaryIntegral_eq_integral

/-- Compact-support represented Stokes from zero boundary scalar support.

This is the zero-extension endpoint version that replaces the previous
ambient target `inChart` topological-support hypothesis with:

* zero scalar support in the boundary image;
* old scalar support in the chosen target face;
* selected target box contained in the target chart.
-/
theorem compactSupportRepresentedStokesZeroExtension_of_zeroScalarSupport
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
    (zeroScalarSupport :
      targetBox.BoundaryZeroScalarSupportSubsetImageField)
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
    ((compactSupportZeroExtensionStokesInputOfZeroScalarSupport
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        (muBulk := muBulk)
        carrierData neighborhoodDataInfty measure_eq_volume
        targetBox targetBox_subset_target zeroScalarSupport
        oldScalarSupport_subset_targetFace
        globalBoundaryIntegral globalBoundaryIntegral_eq_integral)
      |>.assignedSelfBulkInput
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        (muBulk := muBulk)).globalIntegral =
      globalBoundaryIntegral := by
  exact
    (compactSupportZeroExtensionStokesInputOfZeroScalarSupport
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        (muBulk := muBulk)
        carrierData neighborhoodDataInfty measure_eq_volume
        targetBox targetBox_subset_target zeroScalarSupport
        oldScalarSupport_subset_targetFace
        globalBoundaryIntegral globalBoundaryIntegral_eq_integral)
      |>.representedStokes_of_orientedManifold
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        (muBulk := muBulk)

end CompactSupportZeroEndpointScalarSupport

end Stokes

end
