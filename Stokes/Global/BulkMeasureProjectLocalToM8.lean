import Stokes.Global.BoundaryMeasureToM8
import Stokes.Global.BulkMeasureFromPartition
import Stokes.Global.BulkMeasureToM8
import Stokes.Global.M8MeasureConstructors

/-!
# Project-local bulk measure localization adapters for M8

This file exposes project-local-facing bulk measure data in the exact M8
shapes.  It keeps the analytic handoff fields explicit: a.e. local-term
replacement, compact-support integrability, and the measure-box/project-local
identifications are still supplied by callers.

When the bulk localization has already been packaged by the selected-partition
constructor in `BulkMeasureFromPartition.lean`, the adapters route through
`BulkMeasureToM8.lean`.  When callers have the lower-level measure-local terms,
the adapters route through `M8MeasureConstructors.lean`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkMeasureProjectLocalToM8

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

namespace M8BulkMeasureConstructorData

/--
Forget the M8 selected-partition alignment fields and expose the existing
constructor-local bulk measure package.
-/
def toBulkMeasureLocalizationConstructorFields
    (D : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    BulkMeasureLocalizationConstructorFields
      (ι := M) (I := I) (ω := omega)
      (BoundaryChart := M) (BoundaryPiece := BoundaryPiece) where
  interior := D.localizedInterior
  boundary := targetImages
  measureTerms := D.measureTerms
  integrandAE := D.integrandAE
  integrability := D.integrability
  measureBoxAPI := D.measureBoxAPI

/-- Repackage constructor-local bulk measure data as the M8 bulk fields. -/
def toM8BulkMeasureFields
    (D : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    M8BulkMeasureFields I omega selectedPartition targetImages :=
  D.toBulkMeasureLocalizationConstructorFields.toM8BulkMeasureFields
    D.localized_active D.localized_coefficient D.targetImages_active

@[simp]
theorem toBulkMeasureLocalizationConstructorFields_interior
    (D : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    D.toBulkMeasureLocalizationConstructorFields.interior =
      D.localizedInterior :=
  rfl

@[simp]
theorem toBulkMeasureLocalizationConstructorFields_boundary
    (D : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    D.toBulkMeasureLocalizationConstructorFields.boundary =
      targetImages :=
  rfl

@[simp]
theorem toM8BulkMeasureFields_globalBulkIntegral
    (D : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    D.toM8BulkMeasureFields.globalBulkIntegral =
      D.measureTerms.globalBulkIntegral :=
  rfl

@[simp]
theorem toM8BulkMeasureFields_bulkMeasureIntegral
    (D : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    D.toM8BulkMeasureFields.bulkMeasureIntegral =
      D.measureTerms.bulkMeasureIntegral :=
  rfl

@[simp]
theorem toM8BulkMeasureFields_localizedInterior
    (D : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    D.toM8BulkMeasureFields.localizedInterior =
      D.localizedInterior :=
  rfl

/--
Complete constructor-local bulk data with an M8 boundary measure package.
-/
def toM8MeasureLocalizationData
    (D : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages))
    (boundary : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    M8MeasureLocalizationData I omega selectedPartition targetImages :=
  D.toM8BulkMeasureFields.toM8MeasureLocalizationData
    boundary.boundaryPartitionTerm
    boundary.globalBoundaryIntegral
    boundary.boundaryMeasureIntegral
    boundary.globalBoundaryIntegral_eq_boundaryMeasureIntegral
    boundary.boundaryMeasureIntegral_eq_partitionSum

@[simp]
theorem toM8MeasureLocalizationData_bulkMeasureIntegral
    (D : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages))
    (boundary : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    (D.toM8MeasureLocalizationData boundary).bulkMeasureIntegral =
      D.measureTerms.bulkMeasureIntegral :=
  rfl

@[simp]
theorem toM8MeasureLocalizationData_boundaryMeasureIntegral
    (D : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages))
    (boundary : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    (D.toM8MeasureLocalizationData boundary).boundaryMeasureIntegral =
      boundary.boundaryMeasureIntegral :=
  rfl

end M8BulkMeasureConstructorData

/--
Project-local-facing bulk measure constructor data for M8.

The localized interior package is already aligned with the selected partition.
The analytic measure-localization fields remain explicit, and the final field
identifies the analytic local terms with the existing project-local box terms.
-/
structure M8BulkMeasureProjectLocalData where
  /-- Selected-partition localized-interior alignment. -/
  localized : LocalizedInteriorM8Fields I omega selectedPartition
  /-- The target-image boundary family is indexed by the selected active set. -/
  targetImages_active :
    targetImages.activeCharts = selectedPartition.active
  /-- Measure-local finite-sum terms. -/
  measureTerms :
    BulkMeasureLocalizationTermFields localized.localizedInterior targetImages
  /-- A.e. replacement fields for local bulk integrands. -/
  integrandAE : BulkIntegrandAELocalFields measureTerms
  /-- Compact-support integrability hypotheses for the analytic localization. -/
  integrability : CompactSupportIntegrability integrandAE
  /-- Box-identification fields connecting analytic terms to project-local boxes. -/
  measureBoxAPI : MeasureBoxAPI integrandAE

namespace M8BulkMeasureProjectLocalData

/--
Constructor variant that starts from direct measure-local/project-local
identifications, then derives the existing `MeasureBoxAPI`.
-/
def ofMeasureLocalBoxTermAPI
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (targetImages_active :
      targetImages.activeCharts = selectedPartition.active)
    (measureTerms :
      BulkMeasureLocalizationTermFields localized.localizedInterior
        targetImages)
    (integrandAE : BulkIntegrandAELocalFields measureTerms)
    (integrability : CompactSupportIntegrability integrandAE)
    (measureLocalBox : MeasureLocalBoxTermAPI measureTerms) :
    M8BulkMeasureProjectLocalData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages) where
  localized := localized
  targetImages_active := targetImages_active
  measureTerms := measureTerms
  integrandAE := integrandAE
  integrability := integrability
  measureBoxAPI := measureLocalBox.toMeasureBoxAPI integrandAE

/-- View project-local-facing bulk data as the existing M8 constructor data. -/
def toM8BulkMeasureConstructorData
    (D : M8BulkMeasureProjectLocalData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages) where
  localizedInterior := D.localized.localizedInterior
  localized_active := D.localized.localized_active
  localized_coefficient := D.localized.localized_coefficient
  targetImages_active := D.targetImages_active
  measureTerms := D.measureTerms
  integrandAE := D.integrandAE
  integrability := D.integrability
  measureBoxAPI := D.measureBoxAPI

/-- Repackage project-local-facing bulk data as the M8 bulk fields. -/
def toM8BulkMeasureFields
    (D : M8BulkMeasureProjectLocalData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    M8BulkMeasureFields I omega selectedPartition targetImages :=
  D.toM8BulkMeasureConstructorData.toM8BulkMeasureFields

/-- Complete project-local-facing bulk data with an M8 boundary package. -/
def toM8MeasureLocalizationData
    (D : M8BulkMeasureProjectLocalData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages))
    (boundary : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    M8MeasureLocalizationData I omega selectedPartition targetImages :=
  D.toM8BulkMeasureConstructorData.toM8MeasureLocalizationData boundary

/--
Complete project-local-facing bulk data with natural boundary localization
fields.
-/
def toM8MeasureLocalizationDataOfBoundaryFields
    (D : M8BulkMeasureProjectLocalData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages))
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    {globalBoundaryIntegral : Real}
    (boundary :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    M8MeasureLocalizationData I omega selectedPartition targetImages :=
  M8MeasureLocalizationData.ofBulkAndBoundaryFields
    (I := I) (omega := omega)
    (selectedPartition := selectedPartition)
    (targetImages := targetImages)
    D.toM8BulkMeasureConstructorData boundaryPartitionTerm
    globalBoundaryIntegral boundary

@[simp]
theorem toM8BulkMeasureConstructorData_localizedInterior
    (D : M8BulkMeasureProjectLocalData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    D.toM8BulkMeasureConstructorData.localizedInterior =
      D.localized.localizedInterior :=
  rfl

@[simp]
theorem toM8BulkMeasureFields_globalBulkIntegral
    (D : M8BulkMeasureProjectLocalData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    D.toM8BulkMeasureFields.globalBulkIntegral =
      D.measureTerms.globalBulkIntegral :=
  rfl

@[simp]
theorem toM8BulkMeasureFields_bulkMeasureIntegral
    (D : M8BulkMeasureProjectLocalData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    D.toM8BulkMeasureFields.bulkMeasureIntegral =
      D.measureTerms.bulkMeasureIntegral :=
  rfl

@[simp]
theorem toM8MeasureLocalizationData_bulkMeasureIntegral
    (D : M8BulkMeasureProjectLocalData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages))
    (boundary : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    (D.toM8MeasureLocalizationData boundary).bulkMeasureIntegral =
      D.measureTerms.bulkMeasureIntegral :=
  rfl

@[simp]
theorem toM8MeasureLocalizationData_boundaryMeasureIntegral
    (D : M8BulkMeasureProjectLocalData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages))
    (boundary : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    (D.toM8MeasureLocalizationData boundary).boundaryMeasureIntegral =
      boundary.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem toM8MeasureLocalizationDataOfBoundaryFields_bulkMeasureIntegral
    (D : M8BulkMeasureProjectLocalData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages))
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    {globalBoundaryIntegral : Real}
    (boundary :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    (D.toM8MeasureLocalizationDataOfBoundaryFields boundary).bulkMeasureIntegral =
      D.measureTerms.bulkMeasureIntegral :=
  rfl

@[simp]
theorem toM8MeasureLocalizationDataOfBoundaryFields_boundaryMeasureIntegral
    (D : M8BulkMeasureProjectLocalData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages))
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    {globalBoundaryIntegral : Real}
    (boundary :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    (D.toM8MeasureLocalizationDataOfBoundaryFields boundary).boundaryMeasureIntegral =
      boundary.boundaryMeasureIntegral :=
  rfl

end M8BulkMeasureProjectLocalData

namespace BulkMeasureFromPartitionData

variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {globalBulkIntegral : Real}

/--
Selected-partition bulk measure localization, repackaged as the M8 bulk fields.

This route uses the represented global bulk integral itself as the M8 bulk
measure integral, matching the existing adapter in `BulkMeasureToM8.lean`.
-/
def toM8BulkMeasureFields
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral) :
    M8BulkMeasureFields I omega selectedPartition targetImages :=
  D.toBulkMeasureLocalizationFields.toM8BulkMeasureFields
    D.localized.localized_active D.localized.localized_coefficient
    D.boundary_active

/--
Complete selected-partition bulk measure localization with an M8 boundary
measure package.
-/
def toM8MeasureLocalizationData
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    (boundary : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    M8MeasureLocalizationData I omega selectedPartition targetImages :=
  D.toM8BulkMeasureFields.toM8MeasureLocalizationData
    boundary.boundaryPartitionTerm
    boundary.globalBoundaryIntegral
    boundary.boundaryMeasureIntegral
    boundary.globalBoundaryIntegral_eq_boundaryMeasureIntegral
    boundary.boundaryMeasureIntegral_eq_partitionSum

/--
Complete selected-partition bulk measure localization with natural boundary
measure fields.
-/
def toM8MeasureLocalizationDataOfBoundaryFields
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    {globalBoundaryIntegral : Real}
    (boundary :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    M8MeasureLocalizationData I omega selectedPartition targetImages :=
  D.toM8BulkMeasureFields.toM8MeasureLocalizationData
    boundaryPartitionTerm globalBoundaryIntegral
    boundary.boundaryMeasureIntegral
    boundary.globalBoundaryIntegral_eq_boundaryMeasureIntegral
    boundary.boundaryMeasureIntegral_eq_partitionSum

@[simp]
theorem toM8BulkMeasureFields_localizedInterior
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral) :
    D.toM8BulkMeasureFields.localizedInterior =
      D.localized.localizedInterior :=
  rfl

@[simp]
theorem toM8BulkMeasureFields_globalBulkIntegral
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral) :
    D.toM8BulkMeasureFields.globalBulkIntegral =
      globalBulkIntegral :=
  rfl

@[simp]
theorem toM8BulkMeasureFields_bulkMeasureIntegral
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral) :
    D.toM8BulkMeasureFields.bulkMeasureIntegral =
      globalBulkIntegral :=
  rfl

@[simp]
theorem toM8MeasureLocalizationData_bulkMeasureIntegral
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    (boundary : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    (D.toM8MeasureLocalizationData boundary).bulkMeasureIntegral =
      globalBulkIntegral :=
  rfl

@[simp]
theorem toM8MeasureLocalizationData_boundaryMeasureIntegral
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    (boundary : M8BoundaryMeasureData I omega selectedPartition targetImages) :
    (D.toM8MeasureLocalizationData boundary).boundaryMeasureIntegral =
      boundary.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem toM8MeasureLocalizationDataOfBoundaryFields_bulkMeasureIntegral
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    {globalBoundaryIntegral : Real}
    (boundary :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    (D.toM8MeasureLocalizationDataOfBoundaryFields boundary).bulkMeasureIntegral =
      globalBulkIntegral :=
  rfl

@[simp]
theorem toM8MeasureLocalizationDataOfBoundaryFields_boundaryMeasureIntegral
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    {boundaryPartitionTerm : M → BoundaryPiece → Real}
    {globalBoundaryIntegral : Real}
    (boundary :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    (D.toM8MeasureLocalizationDataOfBoundaryFields boundary).boundaryMeasureIntegral =
      boundary.boundaryMeasureIntegral :=
  rfl

end BulkMeasureFromPartitionData

end BulkMeasureProjectLocalToM8

end Stokes

end
