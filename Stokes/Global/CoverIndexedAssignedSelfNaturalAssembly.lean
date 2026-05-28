import Stokes.Global.CoverIndexedBulkAssignedNaturalConstructor
import Stokes.Global.CoverIndexedBoundaryTargetBoxDataConstructor

/-!
# Assigned-self natural assembly for cover-indexed Stokes

This file connects the two cleaner middle-layer routes:

* bulk pieces are represented in their own assigned chart, avoiding a fixed
  bulk chart-change theorem;
* boundary pieces are represented through packaged target-box/image data.

The result is a direct constructor for `CoverIndexedNaturalAssemblyInput`,
which is the layer that already proves represented compact-support Stokes.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section AssignedSelfNaturalAssembly

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
variable [IsFiniteMeasureOnCompacts μBulk]

namespace CoverIndexedNaturalAssemblyInput

/--
Natural assembly from assigned-box local data, assigned-self bulk data, and
resolved target-boundary measure data.

This is the integration point that bypasses the older fixed-chart
`CoverIndexedCoordinateBulkData` endpoint.
-/
def ofAssignedSelfBulkTargetBoundary
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (bulk : CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk)
    (boundary : CoverIndexedTargetBoundaryMeasureData
      (I := I) (K := K) C P ω) :
    CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) where
  chartBoxCover := C
  controlledPartition := P
  localFields := localData.toLocalFields
  bulk := bulk.toClosedCarrierBulkData
  boundary := boundary.toNaturalBoundaryData

/--
Assigned-self bulk plus target-box data from an oriented atlas, using the
canonical target-piece-sum boundary representative.
-/
def ofAssignedSelfBulkTargetBoxOrientedAtlas
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (bulk : CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk)
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      targetBox.targetChart i ∈ A.charts)
    (supportContinuity :
      CoverIndexedBoundaryTargetSupportContinuityData
        (C := C) P ω targetBox.targetChart
        targetBox.targetLower targetBox.targetUpper)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum targetBox.targetChart ω y
          ∂(volume : Measure (Fin n → Real))) :
    CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) :=
  ofAssignedSelfBulkTargetBoundary
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (μBulk := μBulk) localData bulk
    (targetBox.toTargetBoundaryMeasureDataOfOrientedAtlas
      localData A hsource htarget supportContinuity
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral)

/--
Assigned-self bulk plus target-box data from the project-local oriented
manifold class, using the canonical target-piece-sum boundary representative.
-/
def ofAssignedSelfBulkTargetBoxOrientedManifold
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M]
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (bulk : CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk)
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω)
    (supportContinuity :
      CoverIndexedBoundaryTargetSupportContinuityData
        (C := C) P ω targetBox.targetChart
        targetBox.targetLower targetBox.targetUpper)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum targetBox.targetChart ω y
          ∂(volume : Measure (Fin n → Real))) :
    CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) :=
  ofAssignedSelfBulkTargetBoundary
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (μBulk := μBulk) localData bulk
    (targetBox.toTargetBoundaryMeasureDataOfOrientedManifold
      localData supportContinuity
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral)

/-- Stokes theorem for the generic assigned-self assembly route. -/
theorem stokes_ofAssignedSelfBulkTargetBoundary
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (bulk : CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk)
    (boundary : CoverIndexedTargetBoundaryMeasureData
      (I := I) (K := K) C P ω) :
    bulk.globalIntegral = boundary.globalIntegral := by
  simpa [ofAssignedSelfBulkTargetBoundary]
    using
      (ofAssignedSelfBulkTargetBoundary
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        (μBulk := μBulk) localData bulk boundary).stokes

end CoverIndexedNaturalAssemblyInput

end AssignedSelfNaturalAssembly

end Stokes

end
