import Stokes.Global.CoverIndexedZeroCompactAssemblyConstructor
import Stokes.Global.CoverIndexedZeroBoundaryScalarCompactTheorem
import Stokes.Global.CoverIndexedZeroBoundarySourceTargetSum
import Stokes.Global.CoverIndexedZeroTransitionSourceConstructors

/-!
# Natural compact-support zero assembly theorem

This file is the endpoint-facing integration layer for the current
zero-extension route.  It does not prove new support or shrink facts.  Instead
it assembles the facts currently available:

* compact global support gives target zero-scalar support;
* the zero target boundary scalar integral reconstructs the source-target
  boundary sum;
* the remaining source-side local data generate the zero bulk assembly.

The remaining explicit hypotheses are the honest local source-side fields:
neighborhood containment in the chart-transition source, openness of that
source, and zero-transition support inside the selected source half-space box.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactNaturalTheorem

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

/-- Compact-support represented Stokes for the zero-extension route, with the
global boundary reconstruction generated from the zero target scalar boundary
sum.

Compared with `CoverIndexedZeroCompactAssemblyConstructorInput`, callers no
longer provide a prebuilt `sourceTargetAssembly` or its
`globalBoundaryIntegral_eq_sourceTargetBoundarySum` field.  The theorem builds
that assembly package from:

* the remaining source-side local fields
  `sourceNeighborhood`, `sourceOpen`, and `zero_tsupport_subset_source`;
* selected target boxes whose charts agree with the transition target charts;
* compact global support and target coordinate-image containment.
-/
theorem compactSupportRepresentedStokesZeroCompact_of_globalSupport
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P omega)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (measure_eq_volume :
      muBulk = (volume : Measure (Fin (n + 1) → Real)))
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (sourceNeighborhood :
      CoverIndexedCompactSupportNeighborhoodDataInfty.BoundaryNeighborhoodSubsetTransitionSource
        (I := I) (K := K) neighborhoodData transitionSupportData)
    (sourceOpen :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen
          (ManifoldForm.chartTransitionSource I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)))
    (zero_tsupport_subset_source :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChartZero I
              (C.boundaryChart i.1) (transitionSupportData.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (targetChart_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        transitionSupportData.targetChart i = targetBox.targetChart i)
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
      targetBox.TargetChartCoordinateImageSubsetIccField)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real))) :
    (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) neighborhoodData measure_eq_volume).globalIntegral =
        globalBoundaryIntegral ∧
      transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        globalBoundaryIntegral := by
  have hzeroScalar :
      targetBox.BoundaryZeroScalarSupportSubsetImageField :=
    targetBox.boundaryZeroScalarSupportSubsetImageField_of_globalManifoldSupport
      (I := I) (K := K) (C := C) (P := P) (ω := omega)
      hK hsource homegaSupport coordinateImage_subset_targetBox
  have hboundarySum :
      globalBoundaryIntegral =
        Finset.sum C.boundaryCoverIndexFinset fun i =>
          projectLocalBoundaryIntegral I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
    targetBox.globalBoundaryIntegral_eq_transitionSourceTargetBoundarySum_of_zeroTargetBoundaryIntegral
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      carrierData neighborhoodData transitionSupportData targetChart_eq
      targetBox_subset_target hzeroScalar
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral
  let sourceTargetAssembly :
      CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput
        (I := I) (K := K) C P omega :=
    CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput.ofSourceNeighborhood
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      neighborhoodData transitionSupportData
      sourceNeighborhood sourceOpen zero_tsupport_subset_source
      globalBoundaryIntegral hboundarySum
  let D :
      CoverIndexedZeroCompactAssemblyConstructorInput
        (I := I) (K := K) C P omega muBulk := {
    carrierData := carrierData
    measure_eq_volume := measure_eq_volume
    targetBox := targetBox
    hK := hK
    hsource := hsource
    homegaSupport := homegaSupport
    coordinateImage_subset_targetBox := coordinateImage_subset_targetBox
    targetBox_subset_target := targetBox_subset_target
    sourceTargetAssembly := sourceTargetAssembly
    globalBoundaryIntegral_eq_integral := by
      simpa [sourceTargetAssembly] using globalBoundaryIntegral_eq_integral
  }
  simpa [sourceTargetAssembly, D] using
    D.representedStokes_and_zeroSourceTargetBulkAssembly
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)

end CoverIndexedZeroCompactNaturalTheorem

end Stokes

end
