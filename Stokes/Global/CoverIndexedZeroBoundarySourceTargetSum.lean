import Stokes.Global.CoverIndexedZeroAssemblyBridge
import Stokes.Global.CoverIndexedZeroBoundaryScalarIntegral

/-!
# Zero-boundary target COV finite-sum reconstruction

This file fills the source-target boundary reconstruction field isolated by
`CoverIndexedZeroAssemblyBridge`.

The point is algebraically small but important: once the global boundary
representative is the zero-extended target scalar finite sum, the natural
boundary package reconstructs the full cover-index sum of
`P.coverIndexLocalBoundaryTerm`.  Interior indices contribute zero, while each
boundary index can be rewritten as the transported source-target
`projectLocalBoundaryIntegral` by selected-box chart-change invariance.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroBoundarySourceTargetSum

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace SupportControlledSelectedPartition

variable (P)

/-- For a selected boundary cover index, the source-self local boundary term is
the source-target project-local boundary integral whenever both selected boxes
are available. -/
theorem coverIndexLocalBoundaryTerm_eq_sourceTargetProjectLocalBoundaryIntegral
    [IsManifold I 1 M]
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    P.coverIndexLocalBoundaryTerm omega (Sum.inr i) =
      projectLocalBoundaryIntegral I
        (C.boundaryChart i.1) (targetChart i)
        (P.coverIndexLocalizedForm omega (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  simpa [SupportControlledSelectedPartition.coverIndexLocalBoundaryTerm,
    projectLocalBoundaryIntegral] using
    outwardFirstBoundaryChartIntegral_chartChange_invariant_of_selectedBoxes
      (I := I)
      (x0 := C.boundaryChart i.1)
      (x1 := C.boundaryChart i.1)
      (x2 := targetChart i)
      (ω := P.coverIndexLocalizedForm omega (Sum.inr i))
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (sourceSelfSelectedBox i) (sourceTargetSelectedBox i)

/-- The full cover-index local boundary sum is exactly the boundary-indexed sum
of transported source-target project-local boundary integrals.  Interior cover
indices vanish by definition. -/
theorem coverIndexLocalBoundarySum_eq_sourceTargetProjectLocalBoundarySum
    [IsManifold I 1 M]
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    (∑ j : C.CoverIndex, P.coverIndexLocalBoundaryTerm omega j) =
      Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBoundaryIntegral I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  classical
  have hboundaryOnly :
      (∑ j : C.CoverIndex, P.coverIndexLocalBoundaryTerm omega j) =
        ∑ i : {x : M // x ∈ C.boundaryCenters},
          P.coverIndexLocalBoundaryTerm omega (Sum.inr i) := by
    change
      (∑ j :
          ({x : M // x ∈ C.interiorCenters} ⊕
            {x : M // x ∈ C.boundaryCenters}),
          P.coverIndexLocalBoundaryTerm omega j) =
        ∑ i : {x : M // x ∈ C.boundaryCenters},
          P.coverIndexLocalBoundaryTerm omega (Sum.inr i)
    rw [Fintype.sum_sum_type]
    simp [SupportControlledSelectedPartition.coverIndexLocalBoundaryTerm]
  calc
    (∑ j : C.CoverIndex, P.coverIndexLocalBoundaryTerm omega j) =
        ∑ i : {x : M // x ∈ C.boundaryCenters},
          P.coverIndexLocalBoundaryTerm omega (Sum.inr i) := hboundaryOnly
    _ =
        Finset.sum C.boundaryCoverIndexFinset fun i =>
          projectLocalBoundaryIntegral I
            (C.boundaryChart i.1) (targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
      simp only [CompactSupportChartCoverSelection.boundaryCoverIndexFinset]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      exact
        P.coverIndexLocalBoundaryTerm_eq_sourceTargetProjectLocalBoundaryIntegral
          (I := I) (K := K) (C := C) (omega := omega)
          targetChart sourceSelfSelectedBox sourceTargetSelectedBox i

end SupportControlledSelectedPartition

namespace CoverIndexedBoundaryTargetBoxData

variable
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)

/-- Target-side zero-scalar boundary reconstruction gives exactly the
source-target project-local boundary sum for the target charts stored in the
selected target boxes. -/
theorem globalBoundaryIntegral_eq_sourceTargetBoundarySum_of_zeroTargetBoundaryIntegral
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P omega)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
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
          (C.boundaryChart i.1) (targetBox.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  let boundary :=
    targetBox.toZeroTargetBoundaryNaturalDataOfOrientedManifoldInfty
      (I := I) (K := K) (C := C) (P := P) (ω := omega)
      (CoverIndexedCompactSupportCarrierData.sourceSelfSelectedBoxInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        carrierData neighborhoodData)
      neighborhoodData.localizedChartwiseSmooth
      targetBox_subset_target zeroScalarSupport
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral
  calc
    globalBoundaryIntegral =
        ∑ j : C.CoverIndex, P.coverIndexLocalBoundaryTerm omega j := by
      simpa using boundary.localBoundarySum_eq_globalIntegral.symm
    _ =
        Finset.sum C.boundaryCoverIndexFinset fun i =>
          projectLocalBoundaryIntegral I
            (C.boundaryChart i.1) (targetBox.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
      exact
        P.coverIndexLocalBoundarySum_eq_sourceTargetProjectLocalBoundarySum
          (I := I) (K := K) (C := C) (omega := omega)
          targetBox.targetChart
          (CoverIndexedCompactSupportCarrierData.sourceSelfSelectedBoxInfty
            (I := I) (K := K) (C := C) (P := P) (ω := omega)
            carrierData neighborhoodData)
          (fun i => targetBox.sourceTargetSelectedBox i)

/-- Same reconstruction, with a transition-support target chart family supplied
separately.  The caller only has to identify it with the selected target-box
charts. -/
theorem globalBoundaryIntegral_eq_transitionSourceTargetBoundarySum_of_zeroTargetBoundaryIntegral
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
          (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  calc
    globalBoundaryIntegral =
        Finset.sum C.boundaryCoverIndexFinset fun i =>
          projectLocalBoundaryIntegral I
            (C.boundaryChart i.1) (targetBox.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
      exact
        targetBox.globalBoundaryIntegral_eq_sourceTargetBoundarySum_of_zeroTargetBoundaryIntegral
          (I := I) (K := K) (C := C) (P := P) (omega := omega)
          carrierData neighborhoodData targetBox_subset_target zeroScalarSupport
          globalBoundaryIntegral globalBoundaryIntegral_eq_integral
    _ =
        Finset.sum C.boundaryCoverIndexFinset fun i =>
          projectLocalBoundaryIntegral I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp [targetChart_eq i]

end CoverIndexedBoundaryTargetBoxData

end CoverIndexedZeroBoundarySourceTargetSum

end Stokes

end
