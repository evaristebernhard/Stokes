import Stokes.Global.BoundaryMeasureToM8

/-!
# Natural boundary measure builder, COV-facing

This module provides a boundary-only builder from the fieldized boundary COV
measure reconstruction package to the M8 boundary-measure package.

The analytic COV and boundary-measure facts remain in
`BoundaryCOVMeasureReconstructionFields`.  The active-chart and boundary-piece
alignment with the selected M8 data are explicit hypotheses.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalBoundaryMeasureBuilder2

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

namespace BoundaryChartChangeOfVariablesFamily.BoundaryCOVMeasureReconstructionFields

variable {F : BoundaryChartChangeOfVariablesFamily I omega M BoundaryPiece}
variable {boundaryPartitionTerm : M -> BoundaryPiece -> Real}
variable {globalBoundaryIntegral : Real}

/--
Convert COV boundary measure reconstruction fields to the M8 boundary package.

The two equality hypotheses are the only M8-specific bookkeeping: they identify
the COV family indices with the selected partition and target-image boundary
pieces.
-/
def toM8BoundaryMeasureData
    [IsManifold I 1 M]
    (D :
      BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
        globalBoundaryIntegral)
    (hactive : F.activeCharts = selectedPartition.active)
    (hpieces : F.localPieces = targetImages.boundaryPieces) :
    M8BoundaryMeasureData I omega selectedPartition targetImages :=
  M8BoundaryMeasureData.ofBoundaryCOVMeasureReconstructionFields
    (I := I) (omega := omega) (selectedPartition := selectedPartition)
    (targetImages := targetImages) D hactive hpieces

/--
Pointwise-piece variant of `toM8BoundaryMeasureData`.

This is useful for call sites that already carry piece alignment in the
pointwise shape used by several COV adapters.
-/
def toM8BoundaryMeasureDataOfPiecewise
    [IsManifold I 1 M]
    (D :
      BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
        globalBoundaryIntegral)
    (hactive : F.activeCharts = selectedPartition.active)
    (hpieces : forall x, F.localPieces x = targetImages.boundaryPieces x) :
    M8BoundaryMeasureData I omega selectedPartition targetImages :=
  D.toM8BoundaryMeasureData
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    hactive (funext hpieces)

@[simp]
theorem toM8BoundaryMeasureData_boundaryPartitionTerm
    [IsManifold I 1 M]
    (D :
      BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
        globalBoundaryIntegral)
    (hactive : F.activeCharts = selectedPartition.active)
    (hpieces : F.localPieces = targetImages.boundaryPieces) :
    (D.toM8BoundaryMeasureData
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      hactive hpieces).boundaryPartitionTerm =
      boundaryPartitionTerm :=
  rfl

@[simp]
theorem toM8BoundaryMeasureData_globalBoundaryIntegral
    [IsManifold I 1 M]
    (D :
      BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
        globalBoundaryIntegral)
    (hactive : F.activeCharts = selectedPartition.active)
    (hpieces : F.localPieces = targetImages.boundaryPieces) :
    (D.toM8BoundaryMeasureData
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      hactive hpieces).globalBoundaryIntegral =
      globalBoundaryIntegral :=
  rfl

@[simp]
theorem toM8BoundaryMeasureData_boundaryMeasureIntegral
    [IsManifold I 1 M]
    (D :
      BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
        globalBoundaryIntegral)
    (hactive : F.activeCharts = selectedPartition.active)
    (hpieces : F.localPieces = targetImages.boundaryPieces) :
    (D.toM8BoundaryMeasureData
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      hactive hpieces).boundaryMeasureIntegral =
      D.boundaryMeasureIntegral :=
  rfl

/-- Projection theorem for the selected M8 boundary finite sum. -/
theorem toM8BoundaryMeasureData_boundaryMeasureIntegral_eq_partitionSum
    [IsManifold I 1 M]
    (D :
      BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
        globalBoundaryIntegral)
    (hactive : F.activeCharts = selectedPartition.active)
    (hpieces : F.localPieces = targetImages.boundaryPieces) :
    (D.toM8BoundaryMeasureData
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      hactive hpieces).boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm :=
  (D.toM8BoundaryMeasureData
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    hactive hpieces).boundaryMeasureIntegral_eq_partitionSum

/--
Replace only the boundary half of an existing M8 measure-localization package
using COV boundary measure reconstruction fields.
-/
def replaceM8Boundary
    [IsManifold I 1 M]
    (D :
      BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
        globalBoundaryIntegral)
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (hactive : F.activeCharts = selectedPartition.active)
    (hpieces : F.localPieces = targetImages.boundaryPieces) :
    M8MeasureLocalizationData I omega selectedPartition targetImages :=
  E.withBoundaryMeasureData
    (D.toM8BoundaryMeasureData
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      hactive hpieces)

@[simp]
theorem replaceM8Boundary_boundaryPartitionTerm
    [IsManifold I 1 M]
    (D :
      BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
        globalBoundaryIntegral)
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (hactive : F.activeCharts = selectedPartition.active)
    (hpieces : F.localPieces = targetImages.boundaryPieces) :
    (D.replaceM8Boundary
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      E hactive hpieces).boundaryPartitionTerm =
      boundaryPartitionTerm :=
  rfl

@[simp]
theorem replaceM8Boundary_globalBoundaryIntegral
    [IsManifold I 1 M]
    (D :
      BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
        globalBoundaryIntegral)
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (hactive : F.activeCharts = selectedPartition.active)
    (hpieces : F.localPieces = targetImages.boundaryPieces) :
    (D.replaceM8Boundary
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      E hactive hpieces).globalBoundaryIntegral =
      globalBoundaryIntegral :=
  rfl

@[simp]
theorem replaceM8Boundary_boundaryMeasureIntegral
    [IsManifold I 1 M]
    (D :
      BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
        globalBoundaryIntegral)
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (hactive : F.activeCharts = selectedPartition.active)
    (hpieces : F.localPieces = targetImages.boundaryPieces) :
    (D.replaceM8Boundary
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      E hactive hpieces).boundaryMeasureIntegral =
      D.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem replaceM8Boundary_globalBulkIntegral
    [IsManifold I 1 M]
    (D :
      BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
        globalBoundaryIntegral)
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (hactive : F.activeCharts = selectedPartition.active)
    (hpieces : F.localPieces = targetImages.boundaryPieces) :
    (D.replaceM8Boundary
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      E hactive hpieces).globalBulkIntegral =
      E.globalBulkIntegral :=
  rfl

@[simp]
theorem replaceM8Boundary_bulkMeasureIntegral
    [IsManifold I 1 M]
    (D :
      BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
        globalBoundaryIntegral)
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (hactive : F.activeCharts = selectedPartition.active)
    (hpieces : F.localPieces = targetImages.boundaryPieces) :
    (D.replaceM8Boundary
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      E hactive hpieces).bulkMeasureIntegral =
      E.bulkMeasureIntegral :=
  rfl

end BoundaryChartChangeOfVariablesFamily.BoundaryCOVMeasureReconstructionFields

/--
Bundled COV-facing natural boundary builder data.

This record is only a convenience wrapper around the COV reconstruction fields
plus the explicit selected-partition/target-piece alignments.
-/
structure NaturalBoundaryCOVMeasureBuilderData
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece) where
  /-- Boundary COV family supplying source/target boundary terms. -/
  covFamily : BoundaryChartChangeOfVariablesFamily I omega M BoundaryPiece
  /-- Boundary partition term after COV transport. -/
  boundaryPartitionTerm : M -> BoundaryPiece -> Real
  /-- The represented global boundary integral. -/
  globalBoundaryIntegral : Real
  /-- Fieldized COV boundary-measure reconstruction data. -/
  covFields :
    BoundaryChartChangeOfVariablesFamily.BoundaryCOVMeasureReconstructionFields
      covFamily boundaryPartitionTerm globalBoundaryIntegral
  /-- The COV active charts are the selected active charts. -/
  active_eq : covFamily.activeCharts = selectedPartition.active
  /-- The COV local pieces are the selected target boundary pieces. -/
  pieces_eq : covFamily.localPieces = targetImages.boundaryPieces

namespace NaturalBoundaryCOVMeasureBuilderData

variable
    (D :
      NaturalBoundaryCOVMeasureBuilderData I omega selectedPartition
        targetImages)

/-- Convert bundled COV builder data directly to M8 boundary-measure data. -/
def toM8BoundaryMeasureData
    [IsManifold I 1 M] :
    M8BoundaryMeasureData I omega selectedPartition targetImages :=
  D.covFields.toM8BoundaryMeasureData
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    D.active_eq D.pieces_eq

@[simp]
theorem toM8BoundaryMeasureData_boundaryPartitionTerm
    [IsManifold I 1 M] :
    D.toM8BoundaryMeasureData.boundaryPartitionTerm =
      D.boundaryPartitionTerm :=
  rfl

@[simp]
theorem toM8BoundaryMeasureData_globalBoundaryIntegral
    [IsManifold I 1 M] :
    D.toM8BoundaryMeasureData.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

@[simp]
theorem toM8BoundaryMeasureData_boundaryMeasureIntegral
    [IsManifold I 1 M] :
    D.toM8BoundaryMeasureData.boundaryMeasureIntegral =
      D.covFields.boundaryMeasureIntegral :=
  rfl

/-- The bundled COV data supplies the M8 boundary finite-sum field. -/
theorem boundaryMeasureIntegral_eq_partitionSum
    [IsManifold I 1 M] :
    D.covFields.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces D.boundaryPartitionTerm :=
  D.toM8BoundaryMeasureData.boundaryMeasureIntegral_eq_partitionSum

/--
Replace only the boundary half of an existing M8 measure-localization package
from bundled COV boundary builder data.
-/
def replaceBoundary
    [IsManifold I 1 M]
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    M8MeasureLocalizationData I omega selectedPartition targetImages :=
  E.withBoundaryMeasureData D.toM8BoundaryMeasureData

@[simp]
theorem replaceBoundary_boundaryPartitionTerm
    [IsManifold I 1 M]
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    (D.replaceBoundary E).boundaryPartitionTerm =
      D.boundaryPartitionTerm :=
  rfl

@[simp]
theorem replaceBoundary_globalBoundaryIntegral
    [IsManifold I 1 M]
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    (D.replaceBoundary E).globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

@[simp]
theorem replaceBoundary_boundaryMeasureIntegral
    [IsManifold I 1 M]
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    (D.replaceBoundary E).boundaryMeasureIntegral =
      D.covFields.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem replaceBoundary_globalBulkIntegral
    [IsManifold I 1 M]
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    (D.replaceBoundary E).globalBulkIntegral =
      E.globalBulkIntegral :=
  rfl

@[simp]
theorem replaceBoundary_bulkMeasureIntegral
    [IsManifold I 1 M]
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    (D.replaceBoundary E).bulkMeasureIntegral =
      E.bulkMeasureIntegral :=
  rfl

end NaturalBoundaryCOVMeasureBuilderData

end NaturalBoundaryMeasureBuilder2

end Stokes

end
