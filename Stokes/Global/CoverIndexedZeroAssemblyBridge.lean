import Stokes.Global.CoverIndexedZeroBulkMeasureConstructor
import Stokes.Global.CoverIndexedZeroBoundaryLocalStokesConstructor
import Stokes.Global.CoverIndexedZeroNaturalTheorem

/-!
# Zero-extension assembly bridge

This file connects the two zero-extension local ingredients that used to be
used separately:

* zero and old bulk scalar set-integrals agree on a source box with an open
  neighborhood inside the concrete chart-transition source;
* the old smooth transition representative satisfies local half-space Stokes,
  with artificial faces killed by the zero-extended support bound.

The output is a source-target boundary assembly statement: the finite sum of
zero-extended bulk set-integrals over selected boundary source boxes is equal
to the finite sum of the corresponding project-local boundary terms.  A small
record then isolates the remaining global-boundary reconstruction input, which
is where target COV and boundary-measure work still belongs.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroAssemblyBridge

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

namespace CoverIndexedCompactSupportNeighborhoodDataInfty

/-- The open boundary neighborhoods chosen in the compact-support package lie
inside the concrete source-to-target chart-transition domains.  This is the
neighborhood-strengthened form needed for comparing zero and old exterior
derivatives, stronger than mere closed-box containment. -/
abbrev BoundaryNeighborhoodSubsetTransitionSource
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega) : Prop :=
  ∀ i : {x : M // x ∈ C.boundaryCenters},
    neighborhoodData.boundaryNeighborhood i ⊆
      ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)

end CoverIndexedCompactSupportNeighborhoodDataInfty

namespace CoverIndexedCompactSupportTransitionSupportData

/-- The zero-extended source-to-target bulk set-integral attached to one
selected boundary chart box. -/
def boundaryZeroBulkSetIntegral
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (i : {x : M // x ∈ C.boundaryCenters}) : Real :=
  ∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
    zeroTransitionBulkIntegrand I
      (C.boundaryChart i.1) (transitionSupportData.targetChart i)
      (P.coverIndexLocalizedForm omega (Sum.inr i)) y ∂volume

/-- The finite boundary sum of zero-extended source-to-target bulk
set-integrals. -/
def boundaryZeroBulkSetIntegralSum
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega) : Real :=
  Finset.sum C.boundaryCoverIndexFinset fun i =>
    transitionSupportData.boundaryZeroBulkSetIntegral
      (I := I) (K := K) (C := C) (P := P) (omega := omega) i

/-- Per-boundary-index source-target bridge:
zero bulk set-integral equals the transported project-local boundary term.

This is the first real assembly step for the zero-extension route.  It composes
the zero/old bulk set-integral comparison with zero-support local Stokes, so
callers no longer need to provide those two local facts independently. -/
theorem boundary_zeroBulkSetIntegral_eq_projectLocalBoundaryIntegral_of_zero_tsupport_subset_source
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    [IsManifold I ⊤ M]
    (hsourceNeighborhood :
      CoverIndexedCompactSupportNeighborhoodDataInfty.BoundaryNeighborhoodSubsetTransitionSource
        (I := I) (K := K) neighborhoodData transitionSupportData)
    (hsourceOpen :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen
          (ManifoldForm.chartTransitionSource I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)))
    (hzero :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChartZero I
              (C.boundaryChart i.1) (transitionSupportData.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    transitionSupportData.boundaryZeroBulkSetIntegral
        (I := I) (K := K) (C := C) (P := P) (omega := omega) i =
      projectLocalBoundaryIntegral I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)
        (P.coverIndexLocalizedForm omega (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  have hzeroOld :
      (∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
          zeroTransitionBulkIntegrand I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i)) y ∂volume) =
        ∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
          bulkIntegrand I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i)) y ∂volume :=
    zeroTransitionBulkIntegrand_setIntegral_Icc_eq_bulkIntegrand_of_open_source
      (I := I)
      (x0 := C.boundaryChart i.1)
      (x1 := transitionSupportData.targetChart i)
      (ω := P.coverIndexLocalizedForm omega (Sum.inr i))
      (μ := volume)
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (U := neighborhoodData.boundaryNeighborhood i)
      (neighborhoodData.boundary_neighborhood_open i)
      (neighborhoodData.boundary_Icc_subset_neighborhood i)
      (hsourceNeighborhood i)
  have holdBulk :
      (∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
          bulkIntegrand I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i)) y ∂volume) =
        projectLocalBulkIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
    simp [projectLocalBulkIntegral, halfSpaceLocalTransitionBulkIntegral,
      halfSpaceLocalBulkIntegral, bulkIntegrand]
  have hlocal :
      projectLocalBulkIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) =
        projectLocalBoundaryIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
    neighborhoodData.boundary_projectLocalStokes_of_zero_tsupport_subset_source
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData i (hsourceOpen i) (hzero i)
  calc
    transitionSupportData.boundaryZeroBulkSetIntegral
        (I := I) (K := K) (C := C) (P := P) (omega := omega) i =
        ∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
          zeroTransitionBulkIntegrand I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i)) y ∂volume := by
      rfl
    _ =
        ∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
          bulkIntegrand I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i)) y ∂volume := hzeroOld
    _ =
        projectLocalBulkIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) := holdBulk
    _ =
        projectLocalBoundaryIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) := hlocal

/-- Per-boundary-index source-target bridge using the selected open boundary
neighborhood as the smoothness domain.

This version removes the ambient-open transition-source hypothesis from the
local assembly step. -/
theorem boundary_zeroBulkSetIntegral_eq_projectLocalBoundaryIntegral_of_zero_tsupport_subset_sourceNeighborhood
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    [IsManifold I ⊤ M]
    (hsourceNeighborhood :
      CoverIndexedCompactSupportNeighborhoodDataInfty.BoundaryNeighborhoodSubsetTransitionSource
        (I := I) (K := K) neighborhoodData transitionSupportData)
    (hzero :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChartZero I
              (C.boundaryChart i.1) (transitionSupportData.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    transitionSupportData.boundaryZeroBulkSetIntegral
        (I := I) (K := K) (C := C) (P := P) (omega := omega) i =
      projectLocalBoundaryIntegral I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)
        (P.coverIndexLocalizedForm omega (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  have hzeroOld :
      (∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
          zeroTransitionBulkIntegrand I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i)) y ∂volume) =
        ∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
          bulkIntegrand I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i)) y ∂volume :=
    zeroTransitionBulkIntegrand_setIntegral_Icc_eq_bulkIntegrand_of_open_source
      (I := I)
      (x0 := C.boundaryChart i.1)
      (x1 := transitionSupportData.targetChart i)
      (ω := P.coverIndexLocalizedForm omega (Sum.inr i))
      (μ := volume)
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (U := neighborhoodData.boundaryNeighborhood i)
      (neighborhoodData.boundary_neighborhood_open i)
      (neighborhoodData.boundary_Icc_subset_neighborhood i)
      (hsourceNeighborhood i)
  have holdBulk :
      (∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
          bulkIntegrand I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i)) y ∂volume) =
        projectLocalBulkIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
    simp [projectLocalBulkIntegral, halfSpaceLocalTransitionBulkIntegral,
      halfSpaceLocalBulkIntegral, bulkIntegrand]
  have hlocal :
      projectLocalBulkIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) =
        projectLocalBoundaryIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
    neighborhoodData.boundary_projectLocalStokes_of_zero_tsupport_subset_sourceNeighborhood
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData i (hsourceNeighborhood i) (hzero i)
  calc
    transitionSupportData.boundaryZeroBulkSetIntegral
        (I := I) (K := K) (C := C) (P := P) (omega := omega) i =
        ∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
          zeroTransitionBulkIntegrand I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i)) y ∂volume := by
      rfl
    _ =
        ∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
          bulkIntegrand I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i)) y ∂volume := hzeroOld
    _ =
        projectLocalBulkIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) := holdBulk
    _ =
        projectLocalBoundaryIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) := hlocal

/-- Finite-sum source-target bridge for all selected boundary boxes. -/
theorem boundary_zeroBulkSetIntegralSum_eq_projectLocalBoundarySum_of_zero_tsupport_subset_source
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    [IsManifold I ⊤ M]
    (hsourceNeighborhood :
      CoverIndexedCompactSupportNeighborhoodDataInfty.BoundaryNeighborhoodSubsetTransitionSource
        (I := I) (K := K) neighborhoodData transitionSupportData)
    (hsourceOpen :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen
          (ManifoldForm.chartTransitionSource I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)))
    (hzero :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChartZero I
              (C.boundaryChart i.1) (transitionSupportData.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    transitionSupportData.boundaryZeroBulkSetIntegralSum
        (I := I) (K := K) (C := C) (P := P) (omega := omega) =
      Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBoundaryIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact
    CoverIndexedCompactSupportTransitionSupportData.boundary_zeroBulkSetIntegral_eq_projectLocalBoundaryIntegral_of_zero_tsupport_subset_source
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      neighborhoodData transitionSupportData
      hsourceNeighborhood hsourceOpen hzero i

/-- Finite-sum source-target bridge for all selected boundary boxes using
selected boundary neighborhoods rather than ambient-open transition sources. -/
theorem boundary_zeroBulkSetIntegralSum_eq_projectLocalBoundarySum_of_zero_tsupport_subset_sourceNeighborhood
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    [IsManifold I ⊤ M]
    (hsourceNeighborhood :
      CoverIndexedCompactSupportNeighborhoodDataInfty.BoundaryNeighborhoodSubsetTransitionSource
        (I := I) (K := K) neighborhoodData transitionSupportData)
    (hzero :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChartZero I
              (C.boundaryChart i.1) (transitionSupportData.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    transitionSupportData.boundaryZeroBulkSetIntegralSum
        (I := I) (K := K) (C := C) (P := P) (omega := omega) =
      Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBoundaryIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact
    CoverIndexedCompactSupportTransitionSupportData.boundary_zeroBulkSetIntegral_eq_projectLocalBoundaryIntegral_of_zero_tsupport_subset_sourceNeighborhood
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      neighborhoodData transitionSupportData
      hsourceNeighborhood hzero i

end CoverIndexedCompactSupportTransitionSupportData

/-- Intermediate source-target assembly package for the zero-extension route.

The local zero-extension analysis is now generated from the neighborhood,
openness, and zero-support fields.  The remaining global field is exactly the
target-boundary reconstruction problem: identify the source-target
project-local boundary sum with the chosen global boundary integral. -/
structure CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n) where
  neighborhoodData :
    CoverIndexedCompactSupportNeighborhoodDataInfty
      (I := I) (K := K) C P omega
  transitionSupportData :
    CoverIndexedCompactSupportTransitionSupportData
      (I := I) (K := K) C P omega
  sourceNeighborhood :
    CoverIndexedCompactSupportNeighborhoodDataInfty.BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (K := K) neighborhoodData transitionSupportData
  sourceOpen :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      IsOpen
        (ManifoldForm.chartTransitionSource I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i))
  zero_tsupport_subset_source :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      tsupport
          (ManifoldForm.transitionPullbackInChartZero I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
        halfSpaceSupportBox
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
  globalBoundaryIntegral : Real
  /-- Remaining target COV / boundary-measure reconstruction input. -/
  globalBoundaryIntegral_eq_sourceTargetBoundarySum :
    globalBoundaryIntegral =
      Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBoundaryIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)

namespace CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput

variable
    (D :
      CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput
        (I := I) (K := K) C P omega)

/-- The generated local source-target equality, packaged as a finite-sum
assembly theorem. -/
theorem zeroBulkSetIntegralSum_eq_sourceTargetBoundarySum
    [IsManifold I ⊤ M] :
    D.transitionSupportData.boundaryZeroBulkSetIntegralSum
        (I := I) (K := K) (C := C) (P := P) (omega := omega) =
      Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBoundaryIntegral I
          (C.boundaryChart i.1) (D.transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  CoverIndexedCompactSupportTransitionSupportData.boundary_zeroBulkSetIntegralSum_eq_projectLocalBoundarySum_of_zero_tsupport_subset_source
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    D.neighborhoodData D.transitionSupportData
    D.sourceNeighborhood D.sourceOpen D.zero_tsupport_subset_source

/-- Source-target zero bulk assembly after the remaining boundary
reconstruction field is supplied. -/
theorem zeroBulkSetIntegralSum_eq_globalBoundaryIntegral
    [IsManifold I ⊤ M] :
    D.transitionSupportData.boundaryZeroBulkSetIntegralSum
        (I := I) (K := K) (C := C) (P := P) (omega := omega) =
      D.globalBoundaryIntegral := by
  calc
    D.transitionSupportData.boundaryZeroBulkSetIntegralSum
        (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        Finset.sum C.boundaryCoverIndexFinset fun i =>
          projectLocalBoundaryIntegral I
            (C.boundaryChart i.1) (D.transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
      D.zeroBulkSetIntegralSum_eq_sourceTargetBoundarySum
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
    _ = D.globalBoundaryIntegral :=
      D.globalBoundaryIntegral_eq_sourceTargetBoundarySum.symm

end CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput

/-- Endpoint-facing bridge record.

Besides the existing represented zero-extension endpoint inputs, this record
contains the source-target zero local assembly package above.  The two outputs
are deliberately separate: the first is the current represented compact-support
Stokes theorem, while the second records the stronger source-target zero bulk
local assembly that future target-COV/boundary-measure constructors should
connect to the endpoint. -/
structure CoverIndexedZeroAssemblyBridgeEndpointInput
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n)
    (muBulk : Measure (Fin (n + 1) → Real)) where
  carrierData :
    CoverIndexedCompactSupportCarrierData
      (I := I) (K := K) C P omega
  measure_eq_volume :
    muBulk = (volume : Measure (Fin (n + 1) → Real))
  targetBox :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega
  targetBox_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
        (extChartAt I (targetBox.targetChart i)).target
  zeroScalarSupport :
    targetBox.BoundaryZeroScalarSupportSubsetImageField
  oldScalarSupport_subset_targetFace :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Function.support
          (boundaryTargetInChartPieceIntegrand I (targetBox.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
        boundaryTargetInChartPieceSet (n := n)
          (targetBox.targetLower i) (targetBox.targetUpper i)
  sourceTargetAssembly :
    CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput
      (I := I) (K := K) C P omega
  globalBoundaryIntegral_eq_integral :
    sourceTargetAssembly.globalBoundaryIntegral =
      ∫ y, P.coverIndexBoundaryTargetPieceSum targetBox.targetChart omega y
        ∂(volume : Measure (Fin n → Real))

namespace CoverIndexedZeroAssemblyBridgeEndpointInput

variable
    (D :
      CoverIndexedZeroAssemblyBridgeEndpointInput
        (I := I) (K := K) C P omega muBulk)

/-- Current represented compact-support Stokes endpoint plus the generated
source-target zero bulk assembly equality.  The remaining bridge between these
two boundary descriptions is the target COV/global boundary-measure
reconstruction encoded in `sourceTargetAssembly.globalBoundaryIntegral_eq_sourceTargetBoundarySum`
and `globalBoundaryIntegral_eq_integral`. -/
theorem representedStokes_and_zeroSourceTargetBulkAssembly
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    (D.carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk)
        D.sourceTargetAssembly.neighborhoodData D.measure_eq_volume).globalIntegral =
        D.sourceTargetAssembly.globalBoundaryIntegral ∧
      D.sourceTargetAssembly.transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        D.sourceTargetAssembly.globalBoundaryIntegral := by
  refine ⟨?_, ?_⟩
  · exact
      compactSupportRepresentedStokesZeroExtension_natural
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        (muBulk := muBulk)
        D.carrierData D.sourceTargetAssembly.neighborhoodData
        D.measure_eq_volume
        D.targetBox D.targetBox_subset_target
        D.zeroScalarSupport D.oldScalarSupport_subset_targetFace
        D.sourceTargetAssembly.globalBoundaryIntegral
        D.globalBoundaryIntegral_eq_integral
  · exact
      D.sourceTargetAssembly.zeroBulkSetIntegralSum_eq_globalBoundaryIntegral
        (I := I) (K := K) (C := C) (P := P) (omega := omega)

end CoverIndexedZeroAssemblyBridgeEndpointInput

end CoverIndexedZeroAssemblyBridge

end Stokes

end
