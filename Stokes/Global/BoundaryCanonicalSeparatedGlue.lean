import Stokes.Global.BoundaryCanonicalRouteFromContinuity
import Stokes.Global.NaturalCompactSupportSeparatedMeasures

/-!
# Boundary canonical route glue for separated measures

This module is a narrow adapter from the canonical boundary route input to the
boundary half of the separated-measures compact-support endpoint.

The analytic content remains in `BoundaryCanonicalRouteMeasureInput`; this file
only re-exposes it in the `NaturalBoundaryMeasureBuilderData` and
`SeparatedCompactSupportToM8MeasureData` shapes used downstream.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryCanonicalSeparatedGlue

universe u w b ab

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {AlphaBulk : Type ab} [TopologicalSpace AlphaBulk]
variable [MeasurableSpace AlphaBulk] [OpensMeasurableSpace AlphaBulk]
variable [T2Space AlphaBulk]
variable {muBulk : Measure AlphaBulk} [IsFiniteMeasureOnCompacts muBulk]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
variable
    {T :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}
variable {P : ProjectLocalGlobalStokesData I omega M BoundaryPiece}

namespace BoundaryCanonicalRouteMeasureInput

variable (R : BoundaryCanonicalRouteMeasureInput T P)

/--
Canonical route data, exposed as the natural boundary-measure builder package
over the lower-dimensional boundary chart space.
-/
def toNaturalBoundaryMeasureBuilderData
    [IsManifold I 1 M] :
    NaturalBoundaryMeasureBuilderData
      (α := Fin n -> Real) I omega selectedPartition T.targetImages
      (volume : Measure (Fin n -> Real)) where
  boundaryPartitionTerm := T.assembly.boundaryPartitionTerm
  compactFields :=
    R.toBoundaryMeasureFromTargetCOVInput
      |>.toCanonicalBoundaryTargetCompactSupportInput
      |>.canonicalBoundaryCompactFields
  globalBoundaryIntegral := P.globalBoundaryIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := by
    simpa using R.projectLocal.globalBoundaryIntegral_eq_boundaryMeasureIntegral

@[simp]
theorem toNaturalBoundaryMeasureBuilderData_boundaryPartitionTerm
    [IsManifold I 1 M] :
    R.toNaturalBoundaryMeasureBuilderData.boundaryPartitionTerm =
      T.assembly.boundaryPartitionTerm := by
  rfl

@[simp]
theorem toNaturalBoundaryMeasureBuilderData_globalBoundaryIntegral
    [IsManifold I 1 M] :
    R.toNaturalBoundaryMeasureBuilderData.globalBoundaryIntegral =
      P.globalBoundaryIntegral := by
  rfl

@[simp]
theorem toNaturalBoundaryMeasureBuilderData_boundaryMeasureIntegral
    [IsManifold I 1 M] :
    R.toNaturalBoundaryMeasureBuilderData.compactFields.boundaryMeasureIntegral =
      R.projectLocal.boundaryMeasureIntegral := by
  rfl

@[simp]
theorem toNaturalBoundaryMeasureBuilderData_toM8BoundaryMeasureData_boundaryPartitionTerm
    [IsManifold I 1 M] :
    R.toNaturalBoundaryMeasureBuilderData.toM8BoundaryMeasureData.boundaryPartitionTerm =
      T.assembly.boundaryPartitionTerm := by
  rfl

@[simp]
theorem toNaturalBoundaryMeasureBuilderData_toM8BoundaryMeasureData_globalBoundaryIntegral
    [IsManifold I 1 M] :
    R.toNaturalBoundaryMeasureBuilderData.toM8BoundaryMeasureData.globalBoundaryIntegral =
      P.globalBoundaryIntegral := by
  rfl

@[simp]
theorem toNaturalBoundaryMeasureBuilderData_toM8BoundaryMeasureData_boundaryMeasureIntegral
    [IsManifold I 1 M] :
    R.toNaturalBoundaryMeasureBuilderData.toM8BoundaryMeasureData.boundaryMeasureIntegral =
      R.projectLocal.boundaryMeasureIntegral := by
  rfl

/--
Assemble separated compact-support measure data from canonical boundary route
data plus an already-built bulk localization package.
-/
def toSeparatedBoundaryMeasureData
    [IsManifold I 1 M]
    {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := AlphaBulk) (μ := muBulk)
        selectedPartition T.targetImages globalBulkIntegral) :
    SeparatedCompactSupportToM8MeasureData
      (AlphaBulk := AlphaBulk) (AlphaBoundary := Fin n -> Real)
      I omega selectedPartition T.targetImages
      muBulk (volume : Measure (Fin n -> Real)) where
  globalBulkIntegral := globalBulkIntegral
  bulk := bulk
  boundary := R.toNaturalBoundaryMeasureBuilderData

@[simp]
theorem toSeparatedBoundaryMeasureData_boundary
    [IsManifold I 1 M]
    {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := AlphaBulk) (μ := muBulk)
        selectedPartition T.targetImages globalBulkIntegral) :
    (R.toSeparatedBoundaryMeasureData bulk).boundary =
      R.toNaturalBoundaryMeasureBuilderData := by
  rfl

@[simp]
theorem toSeparatedBoundaryMeasureData_globalBulkIntegral
    [IsManifold I 1 M]
    {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := AlphaBulk) (μ := muBulk)
        selectedPartition T.targetImages globalBulkIntegral) :
    (R.toSeparatedBoundaryMeasureData bulk).globalBulkIntegral =
      globalBulkIntegral := by
  rfl

@[simp]
theorem toSeparatedBoundaryMeasureData_boundaryPartitionTerm
    [IsManifold I 1 M]
    {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := AlphaBulk) (μ := muBulk)
        selectedPartition T.targetImages globalBulkIntegral) :
    (R.toSeparatedBoundaryMeasureData bulk).boundary.boundaryPartitionTerm =
      T.assembly.boundaryPartitionTerm := by
  rfl

@[simp]
theorem toSeparatedBoundaryMeasureData_globalBoundaryIntegral
    [IsManifold I 1 M]
    {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := AlphaBulk) (μ := muBulk)
        selectedPartition T.targetImages globalBulkIntegral) :
    (R.toSeparatedBoundaryMeasureData bulk).boundary.globalBoundaryIntegral =
      P.globalBoundaryIntegral := by
  rfl

@[simp]
theorem toSeparatedBoundaryMeasureData_boundaryMeasureIntegral
    [IsManifold I 1 M]
    {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := AlphaBulk) (μ := muBulk)
        selectedPartition T.targetImages globalBulkIntegral) :
    (R.toSeparatedBoundaryMeasureData bulk).boundary.compactFields.boundaryMeasureIntegral =
      R.projectLocal.boundaryMeasureIntegral := by
  rfl

@[simp]
theorem toSeparatedBoundaryMeasureData_toM8_boundaryPartitionTerm
    [IsManifold I 1 M]
    {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := AlphaBulk) (μ := muBulk)
        selectedPartition T.targetImages globalBulkIntegral) :
    (R.toSeparatedBoundaryMeasureData bulk).toM8MeasureLocalizationData.boundaryPartitionTerm =
      T.assembly.boundaryPartitionTerm := by
  rfl

@[simp]
theorem toSeparatedBoundaryMeasureData_toM8_globalBoundaryIntegral
    [IsManifold I 1 M]
    {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := AlphaBulk) (μ := muBulk)
        selectedPartition T.targetImages globalBulkIntegral) :
    (R.toSeparatedBoundaryMeasureData bulk).toM8MeasureLocalizationData.globalBoundaryIntegral =
      P.globalBoundaryIntegral := by
  rfl

@[simp]
theorem toSeparatedBoundaryMeasureData_toM8_boundaryMeasureIntegral
    [IsManifold I 1 M]
    {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := AlphaBulk) (μ := muBulk)
        selectedPartition T.targetImages globalBulkIntegral) :
    (R.toSeparatedBoundaryMeasureData bulk).toM8MeasureLocalizationData.boundaryMeasureIntegral =
      R.projectLocal.boundaryMeasureIntegral := by
  rfl

end BoundaryCanonicalRouteMeasureInput

end BoundaryCanonicalSeparatedGlue

end Stokes

end
