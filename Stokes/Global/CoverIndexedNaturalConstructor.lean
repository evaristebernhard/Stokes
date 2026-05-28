import Stokes.Global.CoverIndexedNaturalAssembly
import Stokes.Global.CoverIndexedInteriorLocalFieldsConstructor
import Stokes.Global.CoverIndexedBoundarySmoothnessConstructor
import Stokes.Global.CoverIndexedBulkSetIntegralConstructor
import Stokes.Global.CoverIndexedBoundarySetIntegralConstructor

/-!
# Natural constructors for the cover-indexed compact-support route

This file collects existing middle-layer constructors into a smaller natural
input for the represented compact-support Stokes route.  It does not add new
semantic hypotheses: it just packages the local assigned-box data, coordinate
bulk data, and target-boundary change-of-variables data, then assembles the
existing `CoverIndexedNaturalAssemblyInput`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalConstructor

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

/--
Assigned-box local data in the form naturally produced by the compact-support
chart-box selection step.

The interior side uses `InteriorAssignedBoxCoordSupportFields`; the boundary
side uses `BoundaryAssignedBoxCoordSupportFields` together with grouped
smoothness data.  From this record we can build the local Stokes fields needed
by the global assembly.
-/
structure CoverIndexedAssignedBoxLocalData
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) where
  /-- Coordinate supports for interior selected cover pieces. -/
  interiorCoordSupport :
    {x : M // x ∈ C.interiorCenters} →
      Set (Fin (n + 1) → Real)
  /-- Packaged interior assigned-box fields. -/
  interiorAssignedFields :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      SupportControlledSelectedPartition.InteriorAssignedBoxCoordSupportFields
        P i ω (interiorCoordSupport i)
  /-- Coordinate supports for boundary selected cover pieces. -/
  boundaryCoordSupport :
    {x : M // x ∈ C.boundaryCenters} →
      Set (Fin (n + 1) → Real)
  /-- Smoothness neighborhoods for boundary selected cover pieces. -/
  boundaryNeighborhood :
    {x : M // x ∈ C.boundaryCenters} →
      Set (Fin (n + 1) → Real)
  /-- Packaged boundary assigned-box fields. -/
  boundaryAssignedFields :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      SupportControlledSelectedPartition.BoundaryAssignedBoxCoordSupportFields
        P i ω (boundaryCoordSupport i) (boundaryNeighborhood i)
  /-- Boundary coordinate supports map back into the compact support set. -/
  boundaryCoordMapsToSupport :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      ∀ y ∈ boundaryCoordSupport i,
        (extChartAt I (C.boundaryChart i.1)).symm y ∈ K
  /-- Boundary coordinate supports lie in the selected chart target. -/
  boundaryCoordSubsetTarget :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryCoordSupport i ⊆
        (extChartAt I (C.boundaryChart i.1)).target
  /-- Grouped boundary smoothness fields. -/
  smoothness :
    CoverIndexedBoundarySmoothnessFields P ω boundaryNeighborhood

namespace CoverIndexedAssignedBoxLocalData

/--
Build assigned-box local data from the natural smoothness input:
chartwise smoothness of the form plus target/overlap containment of the chosen
boundary neighborhoods.
-/
def ofChartwiseSmooth
    [IsManifold I ⊤ M]
    (interiorCoordSupport :
      {x : M // x ∈ C.interiorCenters} →
        Set (Fin (n + 1) → Real))
    (interiorAssignedFields :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        SupportControlledSelectedPartition.InteriorAssignedBoxCoordSupportFields
          P i ω (interiorCoordSupport i))
    (boundaryCoordSupport :
      {x : M // x ∈ C.boundaryCenters} →
        Set (Fin (n + 1) → Real))
    (boundaryNeighborhood :
      {x : M // x ∈ C.boundaryCenters} →
        Set (Fin (n + 1) → Real))
    (boundaryAssignedFields :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        SupportControlledSelectedPartition.BoundaryAssignedBoxCoordSupportFields
          P i ω (boundaryCoordSupport i) (boundaryNeighborhood i))
    (boundaryCoordMapsToSupport :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ∀ y ∈ boundaryCoordSupport i,
          (extChartAt I (C.boundaryChart i.1)).symm y ∈ K)
    (boundaryCoordSubsetTarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryCoordSupport i ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (homega : ManifoldForm.ChartwiseSmooth I ω)
    (boundaryNeighborhood_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryNeighborhood i ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (boundaryNeighborhood_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryNeighborhood i ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (C.boundaryChart i.1)) :
    CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω where
  interiorCoordSupport := interiorCoordSupport
  interiorAssignedFields := interiorAssignedFields
  boundaryCoordSupport := boundaryCoordSupport
  boundaryNeighborhood := boundaryNeighborhood
  boundaryAssignedFields := boundaryAssignedFields
  boundaryCoordMapsToSupport := boundaryCoordMapsToSupport
  boundaryCoordSubsetTarget := boundaryCoordSubsetTarget
  smoothness :=
    CoverIndexedBoundarySmoothnessFields.ofChartwiseSmooth
      (P := P) (omega := ω)
      homega boundaryNeighborhood_subset_target
      boundaryNeighborhood_subset_overlap

/-- Convert assigned-box local data into the local Stokes field package. -/
def toLocalFields
    [IsManifold I ⊤ M]
    (D : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω) :
    SupportControlledCoverIndexedLocalStokesFields P ω :=
  SupportControlledCoverIndexedLocalStokesFields.ofInteriorAndBoundaryAssignedBoxFields
    (P := P) (ω := ω)
    D.interiorCoordSupport
    D.interiorAssignedFields
    D.boundaryCoordSupport
    D.boundaryNeighborhood
    D.boundaryAssignedFields
    D.boundaryCoordMapsToSupport
    D.boundaryCoordSubsetTarget
    D.smoothness.coefficient_contDiffOn
    D.smoothness.form_contDiffOn

/-- The local bulk and boundary terms agree for every selected cover index. -/
theorem localBulk_eq_localBoundary
    [IsManifold I ⊤ M]
    (D : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω) :
    ∀ j : C.CoverIndex,
      P.coverIndexLocalBulkTerm ω j =
        P.coverIndexLocalBoundaryTerm ω j :=
  D.toLocalFields.localBulk_eq_localBoundary

end CoverIndexedAssignedBoxLocalData

/--
Coordinate bulk data before closed-carrier assembly.

The local bulk terms may still be known over the assigned strict coordinate
box.  The constructor below transports them to the closed carrier
`C.coverIndexClosedCarrier` and derives the finite piece-sum reconstruction.
-/
structure CoverIndexedCoordinateBulkData
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n)
    (μBulk : Measure (Fin (n + 1) → Real)) where
  /-- Source chart used for the represented bulk integrand. -/
  sourceChart : M
  /-- Target chart used for the represented bulk integrand. -/
  targetChart : M
  /-- Represented global bulk integral. -/
  globalIntegral : Real
  /-- The represented global bulk integral is the integral of the bulk integrand. -/
  globalIntegral_eq_integral :
    globalIntegral =
      ∫ y, bulkIntegrand I sourceChart targetChart ω y ∂μBulk
  /-- The manifold support of the form lies in the selected compact support set. -/
  formSupport_subset : ManifoldForm.support I ω ⊆ K
  /-- Local bulk representatives are continuous on closed carriers. -/
  piece_continuousOn_closedCarrier :
    ∀ j : C.CoverIndex,
      ContinuousOn
        (fun y =>
          bulkIntegrand I sourceChart targetChart
            (P.coverIndexLocalizedForm ω j) y)
        (C.coverIndexClosedCarrier j)
  /-- Local bulk representatives are supported in assigned strict boxes. -/
  piece_tsupport_subset_assigned :
    ∀ j : C.CoverIndex,
      tsupport
          (fun y =>
            bulkIntegrand I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j) y) ⊆
        C.assignedCoordinateBox j
  /-- Local bulk terms are first known as integrals over assigned strict boxes. -/
  localBulk_eq_setIntegral_assigned :
    ∀ j : C.CoverIndex,
      P.coverIndexLocalBulkTerm ω j =
        ∫ y in C.assignedCoordinateBox j,
          bulkIntegrand I sourceChart targetChart
            (P.coverIndexLocalizedForm ω j) y ∂μBulk
  /-- Differentiability of localized pullbacks a.e. for the finite-sum identity. -/
  piece_differentiable_ae :
    ∀ᶠ y in ae μBulk,
      ∀ j : C.CoverIndex,
        DifferentiableAt Real
          (ManifoldForm.transitionPullbackInChart I sourceChart targetChart
            (P.coverIndexLocalizedForm ω j)) y

namespace CoverIndexedCoordinateBulkData

/-- Local bulk terms transported from assigned boxes to closed carriers. -/
theorem localBulk_eq_setIntegral_closedCarrier
    (D : CoverIndexedCoordinateBulkData
      (I := I) (K := K) C P ω μBulk)
    (j : C.CoverIndex) :
    P.coverIndexLocalBulkTerm ω j =
      ∫ y in C.coverIndexClosedCarrier j,
        bulkIntegrand I D.sourceChart D.targetChart
          (P.coverIndexLocalizedForm ω j) y ∂μBulk :=
  localTerm_eq_setIntegral_over_superset_of_tsupport_subset
    (μ := μBulk)
    (s := C.assignedCoordinateBox j)
    (t := C.coverIndexClosedCarrier j)
    (f := fun y =>
      bulkIntegrand I D.sourceChart D.targetChart
        (P.coverIndexLocalizedForm ω j) y)
    (hs := C.measurableSet_assignedCoordinateBox j)
    (ht := (C.coverIndex_closedCarrier_isCompact j).measurableSet)
    (hst := C.coverIndex_openSupportBox_subset_closedCarrier j)
    (htsupport := D.piece_tsupport_subset_assigned j)
    (hlocal := D.localBulk_eq_setIntegral_assigned j)

/-- A.e. finite-sum reconstruction of the coordinate bulk integrand. -/
theorem integrand_ae_eq_pieceSum
    (D : CoverIndexedCoordinateBulkData
      (I := I) (K := K) C P ω μBulk) :
    bulkIntegrand I D.sourceChart D.targetChart ω =ᵐ[μBulk]
      fun y =>
        ∑ j : C.CoverIndex,
          bulkIntegrand I D.sourceChart D.targetChart
            (P.coverIndexLocalizedForm ω j) y := by
  classical
  have hraw :
      bulkIntegrand I D.sourceChart D.targetChart ω =ᵐ[μBulk]
        fun y =>
          ∑ j ∈ (Finset.univ : Finset C.CoverIndex),
            bulkIntegrand I D.sourceChart D.targetChart
              (ManifoldForm.localizedForm I
                (fun z => P.partition j z) ω) y :=
    _root_.Stokes.coverIndexed_bulkIntegrand_ae_eq_sum_localized_of_support_subset
      (I := I) (active := (Finset.univ : Finset C.CoverIndex))
      (ρ := fun j z => P.partition j z) (ω := ω)
      (K := K) P.finite_sum_eq_one D.formSupport_subset
      μBulk D.sourceChart D.targetChart
      (by
        filter_upwards [D.piece_differentiable_ae] with y hy
        intro j _hj
        simpa [SupportControlledSelectedPartition.coverIndexLocalizedForm]
          using hy j)
  refine hraw.trans (Filter.Eventually.of_forall ?_)
  intro y
  simp [SupportControlledSelectedPartition.coverIndexLocalizedForm]

/-- Convert coordinate bulk data into closed-carrier bulk data. -/
def toClosedCarrierBulkData
    (D : CoverIndexedCoordinateBulkData
      (I := I) (K := K) C P ω μBulk) :
    CoverIndexedClosedCarrierBulkData
      (I := I) (K := K) (μBulk := μBulk) C P ω where
  integrand := bulkIntegrand I D.sourceChart D.targetChart ω
  pieceIntegrand := fun j y =>
    bulkIntegrand I D.sourceChart D.targetChart
      (P.coverIndexLocalizedForm ω j) y
  globalIntegral := D.globalIntegral
  globalIntegral_eq_integral := D.globalIntegral_eq_integral
  piece_continuousOn_closedCarrier :=
    D.piece_continuousOn_closedCarrier
  piece_tsupport_subset_assignedCoordinateBox :=
    D.piece_tsupport_subset_assigned
  localBulk_eq_setIntegral_closedCarrier :=
    D.localBulk_eq_setIntegral_closedCarrier
  integrand_ae_eq_pieceSum :=
    D.integrand_ae_eq_pieceSum

@[simp]
theorem toClosedCarrierBulkData_globalIntegral
    (D : CoverIndexedCoordinateBulkData
      (I := I) (K := K) C P ω μBulk) :
    D.toClosedCarrierBulkData.globalIntegral = D.globalIntegral :=
  rfl

end CoverIndexedCoordinateBulkData

/--
Target-boundary measure data supplied by a boundary chart change-of-variables
family.

Interior cover indices are handled by the empty-carrier/zero-integrand
convention already used by `CoverIndexedBoundarySetIntegralConstructor`.
-/
structure CoverIndexedTargetBoundaryMeasureData
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) where
  /-- Target boundary chart for each selected boundary center. -/
  targetChart : {x : M // x ∈ C.boundaryCenters} → M
  /-- Lower target boxes for the boundary chart images. -/
  targetLower :
    {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real
  /-- Upper target boxes for the boundary chart images. -/
  targetUpper :
    {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real
  /-- Global scalar representative for the boundary integral. -/
  boundaryIntegrand : (Fin n → Real) → Real
  /-- Represented global boundary integral. -/
  globalIntegral : Real
  /-- The represented global boundary integral is the integral of its representative. -/
  globalIntegral_eq_integral :
    globalIntegral =
      ∫ y, boundaryIntegrand y ∂(volume : Measure (Fin n → Real))
  /-- Target boundary boxes are compact for genuine boundary indices. -/
  boundaryPiece_isCompact :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      IsCompact
        (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper
          (Sum.inr i))
  /-- Target boundary piece integrands are continuous on target boxes. -/
  boundaryPiece_continuousOn :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      ContinuousOn
        (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i))
        (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper
          (Sum.inr i))
  /-- Target boundary piece integrands are supported in target boxes. -/
  boundaryPiece_tsupport_subset :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      tsupport
          (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i)) ⊆
        P.coverIndexBoundaryTargetPieceSet targetLower targetUpper
          (Sum.inr i)
  /-- Source self-box selection, used to compare the recorded source boundary term. -/
  sourceSelfSelectedBox :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryChartSelectedBox I
        (C.boundaryChart i.1) (C.boundaryChart i.1)
        (P.coverIndexLocalizedForm ω (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1)
  /-- Source-target selected boxes. -/
  sourceTargetSelectedBox :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryChartSelectedBox I
        (C.boundaryChart i.1) (targetChart i)
        (P.coverIndexLocalizedForm ω (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1)
  /-- Oriented boundary chart change-of-variables data. -/
  orientedCOV :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryChartOrientedChangeOfVariables I
        (C.boundaryChart i.1) (targetChart i)
        (P.coverIndexLocalizedForm ω (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1)
        (targetLower i) (targetUpper i)
  /-- The global boundary representative is the finite sum of target pieces, a.e. -/
  boundaryIntegrand_ae_eq_pieceSum :
    boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
      fun y =>
        ∑ j : C.CoverIndex,
          P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y

namespace CoverIndexedTargetBoundaryMeasureData

/-- Local boundary terms as target set integrals from the oriented COV data. -/
theorem localBoundary_eq_setIntegral
    [IsManifold I 1 M]
    (D : CoverIndexedTargetBoundaryMeasureData (I := I) (K := K) C P ω)
    (j : C.CoverIndex) :
    P.coverIndexLocalBoundaryTerm ω j =
      ∫ y in P.coverIndexBoundaryTargetPieceSet
          D.targetLower D.targetUpper j,
        P.coverIndexBoundaryTargetPieceIntegrand
          D.targetChart ω j y ∂(volume : Measure (Fin n → Real)) :=
  P.coverIndexLocalBoundaryTerm_eq_targetSetIntegral_of_orientedCOV
    (ω := ω) D.targetChart D.targetLower D.targetUpper
    D.sourceSelfSelectedBox D.sourceTargetSelectedBox D.orientedCOV j

/-- Convert target-boundary COV measure data into natural boundary data. -/
def toNaturalBoundaryData
    [IsManifold I 1 M]
    (D : CoverIndexedTargetBoundaryMeasureData (I := I) (K := K) C P ω) :
    CoverIndexedNaturalBoundaryData
      (I := I) (K := K) (ω := ω)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) C P where
  integrand := D.boundaryIntegrand
  pieceSet :=
    P.coverIndexBoundaryTargetPieceSet D.targetLower D.targetUpper
  pieceIntegrand :=
    P.coverIndexBoundaryTargetPieceIntegrand D.targetChart ω
  globalIntegral := D.globalIntegral
  globalIntegral_eq_integral := D.globalIntegral_eq_integral
  piece_isCompact := by
    intro j
    rcases j with i | i
    · simp [SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceSet]
    · exact D.boundaryPiece_isCompact i
  piece_continuousOn := by
    intro j
    rcases j with i | i
    · simp [SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceSet,
        SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceIntegrand]
    · exact D.boundaryPiece_continuousOn i
  piece_tsupport_subset := by
    intro j
    rcases j with i | i
    · simp [SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceSet,
        SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceIntegrand]
    · exact D.boundaryPiece_tsupport_subset i
  localBoundary_eq_setIntegral :=
    D.localBoundary_eq_setIntegral
  integrand_ae_eq_pieceSum :=
    D.boundaryIntegrand_ae_eq_pieceSum

@[simp]
theorem toNaturalBoundaryData_globalIntegral
    [IsManifold I 1 M]
    (D : CoverIndexedTargetBoundaryMeasureData (I := I) (K := K) C P ω) :
    D.toNaturalBoundaryData.globalIntegral = D.globalIntegral :=
  rfl

end CoverIndexedTargetBoundaryMeasureData

/--
One-step natural input for represented compact-support Stokes.

Compared with `CoverIndexedNaturalAssemblyInput`, this constructor input no
longer asks callers to provide the large local-field record, closed-carrier
bulk record, or boundary natural record directly.  Those are generated from
the three grouped pieces below.
-/
structure CoverIndexedNaturalConstructorInput
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n)
    (μBulk : Measure (Fin (n + 1) → Real)) where
  /-- Assigned-box local data for local Stokes. -/
  localData : CoverIndexedAssignedBoxLocalData C P ω
  /-- Coordinate bulk data, transported internally to closed carriers. -/
  bulk : CoverIndexedCoordinateBulkData C P ω μBulk
  /-- Target-boundary COV measure data. -/
  boundary : CoverIndexedTargetBoundaryMeasureData C P ω

namespace CoverIndexedNaturalAssemblyInput

/--
Construct the natural assembly input from assigned-box local data, coordinate
bulk data, and target-boundary COV data.
-/
def ofAssignedBoxCoordinateBulkTargetBoundary
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (bulk : CoverIndexedCoordinateBulkData
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

end CoverIndexedNaturalAssemblyInput

namespace CoverIndexedNaturalConstructorInput

/-- Convert the grouped constructor input into the natural assembly input. -/
def toNaturalAssemblyInput
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (D : CoverIndexedNaturalConstructorInput
      (I := I) (K := K) C P ω μBulk) :
    CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) :=
  CoverIndexedNaturalAssemblyInput.ofAssignedBoxCoordinateBulkTargetBoundary
    (C := C) (P := P) (ω := ω) (μBulk := μBulk)
    D.localData D.bulk D.boundary

/-- Represented global bulk value carried by the constructor input. -/
abbrev globalBulk
    (D : CoverIndexedNaturalConstructorInput
      (I := I) (K := K) C P ω μBulk) :
    Real :=
  D.bulk.globalIntegral

/-- Represented global boundary value carried by the constructor input. -/
abbrev globalBoundary
    (D : CoverIndexedNaturalConstructorInput
      (I := I) (K := K) C P ω μBulk) :
    Real :=
  D.boundary.globalIntegral

@[simp]
theorem toNaturalAssemblyInput_globalBulk
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (D : CoverIndexedNaturalConstructorInput
      (I := I) (K := K) C P ω μBulk) :
    D.toNaturalAssemblyInput.globalBulk = D.globalBulk :=
  rfl

@[simp]
theorem toNaturalAssemblyInput_globalBoundary
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (D : CoverIndexedNaturalConstructorInput
      (I := I) (K := K) C P ω μBulk) :
    D.toNaturalAssemblyInput.globalBoundary = D.globalBoundary :=
  rfl

/-- Compact-support represented Stokes from the grouped natural constructor input. -/
theorem stokes
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (D : CoverIndexedNaturalConstructorInput
      (I := I) (K := K) C P ω μBulk) :
    D.globalBulk = D.globalBoundary := by
  exact D.toNaturalAssemblyInput.stokes

/-- Canonical represented Stokes from the grouped natural constructor input. -/
theorem canonical_stokes
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (D : CoverIndexedNaturalConstructorInput
      (I := I) (K := K) C P ω μBulk) :
    D.toNaturalAssemblyInput.canonicalIntegralInterface.stokesStatement := by
  exact D.toNaturalAssemblyInput.canonical_stokes

end CoverIndexedNaturalConstructorInput

end NaturalConstructor

end Stokes

end
