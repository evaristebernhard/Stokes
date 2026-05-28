import Stokes.Global.CoverIndexedZeroBoundarySourceTargetSum
import Stokes.Global.CoverIndexedZeroTransitionSourceConstructors

/-!
# Zero-boundary assembly-input constructors

This module packages the zero target-boundary finite-sum reconstruction into
the exact field needed by `CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput`.

The mathematical content is already proved in
`CoverIndexedBoundaryTargetBoxData.
  globalBoundaryIntegral_eq_transitionSourceTargetBoundarySum_of_zeroTargetBoundaryIntegral`.
Here we expose that result in the constructor shape used by the zero-extension
assembly bridge.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroBoundaryAssemblyInputConstructor

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryTargetBoxData

variable
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)

/-- Construct the source-target boundary-sum field used by the zero assembly
bridge from the zero target-boundary scalar integral and the identification of
the transition-support target charts with the selected target-box charts. -/
theorem sourceTargetBoundarySumField_of_zeroTargetBoundaryIntegral
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P omega)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (targetChart_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        transitionSupportData.targetChart i = targetBox.targetChart i)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target)
    (zeroScalarSupport :
      targetBox.BoundaryZeroScalarSupportSubsetImageField)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real))) :
    globalBoundaryIntegral =
      Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBoundaryIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  targetBox.globalBoundaryIntegral_eq_transitionSourceTargetBoundarySum_of_zeroTargetBoundaryIntegral
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    carrierData neighborhoodData transitionSupportData targetChart_eq
    targetBox_subset_target zeroScalarSupport
    globalBoundaryIntegral globalBoundaryIntegral_eq_integral

end CoverIndexedBoundaryTargetBoxData

namespace CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput

/-- Build the zero source-target assembly input from a selected target-box
package and the zero target-boundary scalar integral.

The source-side neighborhood, openness, and zero-support hypotheses are still
the real local-analysis inputs.  The global boundary reconstruction field is
generated from `targetBox` by
`sourceTargetBoundarySumField_of_zeroTargetBoundaryIntegral`. -/
def ofTargetBoxZeroBoundaryIntegral
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P omega)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
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
    (zeroScalarSupport :
      targetBox.BoundaryZeroScalarSupportSubsetImageField)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real))) :
    CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput
      (I := I) (K := K) C P omega :=
  ofSourceNeighborhood
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    neighborhoodData transitionSupportData
    sourceNeighborhood sourceOpen zero_tsupport_subset_source
    globalBoundaryIntegral
    (targetBox.sourceTargetBoundarySumField_of_zeroTargetBoundaryIntegral
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      carrierData neighborhoodData transitionSupportData targetChart_eq
      targetBox_subset_target zeroScalarSupport
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral)

end CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput

end CoverIndexedZeroBoundaryAssemblyInputConstructor

end Stokes

end
