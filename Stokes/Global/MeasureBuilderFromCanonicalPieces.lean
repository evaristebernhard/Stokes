import Stokes.Global.BulkMeasureExtDerivFromPartition
import Stokes.Global.BoundaryMeasureFromTargetCOV
import Stokes.Global.CompactSupportSelectedBoxEndToEnd

/-!
# End-to-end input from canonical bulk and boundary pieces

This file composes three constructive routes that were previously separate:

* `SelectedPartitionBulkMeasureExtDerivInput` builds the selected bulk measure
  package from canonical partition/ext-derivative scalar terms plus explicit
  measure hypotheses;
* `BoundaryMeasureFromTargetCOVInput` builds canonical boundary target data
  from target-image COV plus the remaining source set-integral theorem;
* `CompactSupportSelectedBoxEndToEndData` connects selected boxes, strict
  margins, and localized chart alignment to `NaturalCompactSupportEndToEndInput`.

No new analytic theorem is hidden here.  The remaining hard facts are still
fields of the bulk and boundary input records.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section MeasureBuilderFromCanonicalPieces

universe u w b ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {ρ : SmoothPartitionOfUnity M I M univ}
variable {K : Set M} {hK : IsCompact K}
variable {μ : Measure (Fin (n + 1) → Real)}
variable [IsFiniteMeasureOnCompacts μ]

/--
Canonical-piece input for the current compact-support Stokes endpoint.

Compared with `NaturalCompactSupportEndToEndInput`, this record replaces the
bulk package and boundary target package by the more structured records that
were introduced for the next proof stage.
-/
structure NaturalCompactSupportCanonicalPiecesInput
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (K : Set M) (hK : IsCompact K)
    (μ : Measure (Fin (n + 1) → Real))
    [IsFiniteMeasureOnCompacts μ]
    [IsManifold I 1 M] where
  /-- Compactly supported smooth input form. -/
  formData : CompactlySupportedSmoothFormData I omega
  /-- The selected compact set is the support set recorded by `formData`. -/
  supportSet_eq : K = formData.supportSet
  /-- Compact-support finite active chart selection. -/
  selection : CompactSupportFiniteActiveSelection (I := I) ρ K hK omega
  /-- Smoothness data upgrading selected compact boxes to extended boxes. -/
  smoothness :
    ActiveCompactBoxSmoothness selection.finiteActive selection.supportData.box omega
  /-- Project-local oriented boundary chart atlas data. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Boundary target-image input over the selected partition. -/
  targetImageInput :
    M8TargetImageInput I omega
      (selection.selectedBoxPartitionOfUnity smoothness)
      orientedBoundaryAtlas BoundaryPiece
  /-- Canonical bulk measure input from partition exterior derivatives. -/
  bulkExtDeriv :
    SelectedPartitionBulkMeasureExtDerivInput
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages μ
  /-- Boundary compact-support input produced by target-image COV. -/
  boundaryCOV :
    BoundaryMeasureFromTargetCOVInput
      (α := Fin (n + 1) → Real) targetImageInput μ
  /-- The selected localized pieces use the selected chart label as source/target. -/
  localizedChartAlignment :
    LocalizedInteriorM8ChartAlignment
      bulkExtDeriv.toBulkMeasureFromPartitionData.localized
  /-- Strict outer margins around the selected boxes for the produced measure data. -/
  strictMargins :
    SelectedBoxStrictMarginData
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages
      ((boundaryCOV.toCanonicalBoundaryTargetCompactSupportInput)
        |>.toMeasureBuilderData bulkExtDeriv.toBulkMeasureFromPartitionData
        |>.toM8MeasureLocalizationData)

namespace NaturalCompactSupportCanonicalPiecesInput

variable [IsManifold I 1 M]
variable
    (D :
      NaturalCompactSupportCanonicalPiecesInput
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        I omega BoundaryPiece ρ K hK μ)

/-- The selected partition determined by the compact-support selection. -/
abbrev selectedPartition : SelectedBoxPartitionOfUnity I omega :=
  D.selection.selectedBoxPartitionOfUnity D.smoothness

/-- The selected bulk measure package produced by the canonical bulk route. -/
abbrev bulk :
    BulkMeasureFromPartitionData
      (α := Fin (n + 1) → Real) (μ := μ)
      D.selectedPartition D.targetImageInput.targetImages
      D.bulkExtDeriv.measureTerms.globalBulkIntegral :=
  D.bulkExtDeriv.toBulkMeasureFromPartitionData

/-- The canonical boundary target package produced by target-image COV. -/
abbrev boundaryTarget :
    CanonicalBoundaryTargetCompactSupportInput
      (α := Fin (n + 1) → Real) D.targetImageInput μ :=
  D.boundaryCOV.toCanonicalBoundaryTargetCompactSupportInput

/-- The selected-box end-to-end package induced by the canonical pieces. -/
def toCompactSupportSelectedBoxEndToEndData :
    CompactSupportSelectedBoxEndToEndData
      (α := Fin (n + 1) → Real)
      I omega BoundaryPiece ρ K hK μ where
  formData := D.formData
  supportSet_eq := D.supportSet_eq
  selection := D.selection
  smoothness := D.smoothness
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  targetImageInput := D.targetImageInput
  globalBulkIntegral := D.bulkExtDeriv.measureTerms.globalBulkIntegral
  bulk := D.bulk
  boundaryTarget := D.boundaryTarget
  localizedChartAlignment := D.localizedChartAlignment
  strictMargins := D.strictMargins

@[simp]
theorem toCompactSupportSelectedBoxEndToEndData_bulk :
    D.toCompactSupportSelectedBoxEndToEndData.bulk = D.bulk := by
  rfl

@[simp]
theorem toCompactSupportSelectedBoxEndToEndData_boundaryTarget :
    D.toCompactSupportSelectedBoxEndToEndData.boundaryTarget =
      D.boundaryTarget := by
  rfl

/-- The current end-to-end input obtained from canonical bulk/boundary pieces. -/
def toNaturalCompactSupportEndToEndInput :
    NaturalCompactSupportEndToEndInput
      (α := Fin (n + 1) → Real) I omega BoundaryPiece μ :=
  D.toCompactSupportSelectedBoxEndToEndData.toNaturalCompactSupportEndToEndInput

@[simp]
theorem toNaturalCompactSupportEndToEndInput_bulk :
    D.toNaturalCompactSupportEndToEndInput.bulk = D.bulk := by
  rfl

@[simp]
theorem toNaturalCompactSupportEndToEndInput_boundaryTarget :
    D.toNaturalCompactSupportEndToEndInput.boundaryTarget =
      D.boundaryTarget := by
  rfl

/--
Canonical compact-support Stokes from canonical bulk/boundary piece inputs.
-/
theorem canonical_stokes :
    D.toNaturalCompactSupportEndToEndInput
      |>.toNaturalCompactSupportStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement :=
  D.toNaturalCompactSupportEndToEndInput.canonical_stokes

end NaturalCompactSupportCanonicalPiecesInput

/--
Top-level wrapper: once the canonical bulk and boundary piece records are
constructed, they feed the current compact-support Stokes endpoint.
-/
theorem naturalCompactSupportStokes_canonical_of_canonicalPieces
    [IsManifold I 1 M]
    (D :
      NaturalCompactSupportCanonicalPiecesInput
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        I omega BoundaryPiece ρ K hK μ) :
    D.toNaturalCompactSupportEndToEndInput
      |>.toNaturalCompactSupportStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement :=
  D.canonical_stokes

end MeasureBuilderFromCanonicalPieces

end Stokes

end
