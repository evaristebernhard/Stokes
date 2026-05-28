import Stokes.Global.BoundaryMeasureFromPartition
import Stokes.Global.BoundaryMeasureToM8

/-!
# Natural boundary measure builder

This module provides a boundary-only builder from compact/set-integral
boundary measure data to the M8 boundary-measure package.  It is intentionally
thin: the real analytic content remains in `BoundaryCompactMeasureFields` or
`BoundaryMeasureLocalizationData`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalBoundaryMeasureBuilder

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {α : Type a} [MeasurableSpace α]
variable {μ : Measure α}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

/--
Boundary-measure data in a natural selected-partition shape.

The compact/set-integral package supplies the actual boundary integral
localization theorem.  This record only records the represented global
boundary integral and aligns the package with the selected partition and target
boundary pieces used by M8.
-/
structure NaturalBoundaryMeasureBuilderData
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (μ : Measure α) where
  /-- Boundary partition term after all boundary chart changes. -/
  boundaryPartitionTerm : M → BoundaryPiece → Real
  /-- Compact/set-integral boundary measure localization package. -/
  compactFields :
    BoundaryCompactMeasureFields μ selectedPartition.active
      targetImages.boundaryPieces boundaryPartitionTerm
  /-- Represented global boundary integral. -/
  globalBoundaryIntegral : Real
  /-- The represented boundary integral agrees with the measure integral. -/
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :
    globalBoundaryIntegral = compactFields.boundaryMeasureIntegral

namespace NaturalBoundaryMeasureBuilderData

variable
    (D :
      NaturalBoundaryMeasureBuilderData
        (α := α) I omega selectedPartition targetImages μ)

/-- Convert to the analytic boundary measure-localization data. -/
def toBoundaryMeasureLocalizationData :
    BoundaryMeasureLocalizationData μ selectedPartition.active
      targetImages.boundaryPieces D.boundaryPartitionTerm :=
  D.compactFields.toBoundaryMeasureLocalizationData

@[simp]
theorem toBoundaryMeasureLocalizationData_boundaryMeasureIntegral :
    D.toBoundaryMeasureLocalizationData.boundaryMeasureIntegral =
      D.compactFields.boundaryMeasureIntegral :=
  rfl

/-- Convert to the fieldized boundary measure-localization package. -/
def toBoundaryMeasureLocalizationFields :
    BoundaryMeasureLocalizationFields selectedPartition.active
      targetImages.boundaryPieces D.boundaryPartitionTerm
      D.globalBoundaryIntegral :=
  D.toBoundaryMeasureLocalizationData.toBoundaryMeasureLocalizationFields
    D.globalBoundaryIntegral D.globalBoundaryIntegral_eq_boundaryMeasureIntegral

@[simp]
theorem toBoundaryMeasureLocalizationFields_boundaryMeasureIntegral :
    D.toBoundaryMeasureLocalizationFields.boundaryMeasureIntegral =
      D.compactFields.boundaryMeasureIntegral :=
  rfl

/-- Convert directly to the M8 boundary-measure package. -/
def toM8BoundaryMeasureData :
    M8BoundaryMeasureData I omega selectedPartition targetImages :=
  M8BoundaryMeasureData.ofBoundaryMeasureLocalizationFields
    (I := I) (omega := omega) (selectedPartition := selectedPartition)
    (targetImages := targetImages)
    D.toBoundaryMeasureLocalizationFields

@[simp]
theorem toM8BoundaryMeasureData_boundaryPartitionTerm :
    D.toM8BoundaryMeasureData.boundaryPartitionTerm =
      D.boundaryPartitionTerm :=
  rfl

@[simp]
theorem toM8BoundaryMeasureData_globalBoundaryIntegral :
    D.toM8BoundaryMeasureData.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

@[simp]
theorem toM8BoundaryMeasureData_boundaryMeasureIntegral :
    D.toM8BoundaryMeasureData.boundaryMeasureIntegral =
      D.compactFields.boundaryMeasureIntegral :=
  rfl

/-- The compact boundary package gives the M8 finite-sum boundary field. -/
theorem boundaryMeasureIntegral_eq_partitionSum :
    D.compactFields.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces D.boundaryPartitionTerm :=
  D.compactFields.boundaryMeasureIntegral_eq_partitionSum

/--
Replace the boundary half of an existing M8 measure-localization package using
natural boundary measure builder data.
-/
def replaceBoundary
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    M8MeasureLocalizationData I omega selectedPartition targetImages :=
  E.withBoundaryMeasureData D.toM8BoundaryMeasureData

@[simp]
theorem replaceBoundary_boundaryMeasureIntegral
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    (D.replaceBoundary E).boundaryMeasureIntegral =
      D.compactFields.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem replaceBoundary_boundaryPartitionTerm
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    (D.replaceBoundary E).boundaryPartitionTerm =
      D.boundaryPartitionTerm :=
  rfl

/--
Convenience constructor when the represented global boundary integral is chosen
to be the compact boundary measure integral itself.
-/
def ofBoundaryMeasureIntegral
    (boundaryPartitionTerm : M → BoundaryPiece → Real)
    (compactFields :
      BoundaryCompactMeasureFields μ selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm) :
    NaturalBoundaryMeasureBuilderData
      (α := α) I omega selectedPartition targetImages μ where
  boundaryPartitionTerm := boundaryPartitionTerm
  compactFields := compactFields
  globalBoundaryIntegral := compactFields.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := rfl

@[simp]
theorem ofBoundaryMeasureIntegral_globalBoundaryIntegral
    (boundaryPartitionTerm : M → BoundaryPiece → Real)
    (compactFields :
      BoundaryCompactMeasureFields μ selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm) :
    (ofBoundaryMeasureIntegral
      (I := I) (omega := omega) (selectedPartition := selectedPartition)
      (targetImages := targetImages) (μ := μ)
      boundaryPartitionTerm compactFields).globalBoundaryIntegral =
      compactFields.boundaryMeasureIntegral :=
  rfl

end NaturalBoundaryMeasureBuilderData

end NaturalBoundaryMeasureBuilder

end Stokes

end
