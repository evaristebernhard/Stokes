import Stokes.Global.NaturalMeasureStrictBuilder
import Stokes.Global.BoundaryTargetMeasureBuilderGlue
import Stokes.Global.CanonicalNaturalCompactSupport

/-!
# End-to-end remaining input for natural compact-support Stokes

The theorem `naturalCompactSupportStokes_canonical` is already available once a
`NaturalCompactSupportStokesInput` has been constructed.  This file packages the
remaining explicit fields in the current shortest construction route:

* compactly supported form data and the selected partition;
* target-image data and canonical boundary compact-support measure data;
* selected bulk measure data;
* compact-active box / localized-piece alignment needed for the strict-buffer
  artificial-face route.

No analytic, inverse-function, change-of-variables, or orientation theorem is
proved here.  The purpose is to make the remaining theorem debt precise and
easy to split across parallel work.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section EndToEndRemainingInput

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}

/--
Current end-to-end input for the compact-support Stokes route.

This record intentionally keeps the remaining mathematical obligations visible.
It is not a final natural theorem statement; it is a staging interface showing
which fields still need to be constructed from genuine manifold, target-box,
orientation, and measure-localization data.
-/
structure NaturalCompactSupportEndToEndInput
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (μ : Measure α) [IsFiniteMeasureOnCompacts μ] where
  /-- Compactly supported smooth input form. -/
  formData : CompactlySupportedSmoothFormData I omega
  /-- Project-local oriented boundary chart atlas data. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Selected partition of unity and chart boxes. -/
  selectedPartition : SelectedBoxPartitionOfUnity I omega
  /-- The selected partition is controlled by the compact support set. -/
  selectedPartition_supportSet :
    selectedPartition.K = formData.supportSet
  /-- Resolved target-image data for boundary pieces. -/
  targetImageInput :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece
  /-- The represented bulk integral value used by the selected bulk route. -/
  globalBulkIntegral : Real
  /-- Selected bulk measure localization data. -/
  bulk :
    BulkMeasureFromPartitionData
      (α := α) (μ := μ) selectedPartition targetImageInput.targetImages
      globalBulkIntegral
  /-- Canonical boundary compact-support data for the target-image route. -/
  boundaryTarget :
    CanonicalBoundaryTargetCompactSupportInput
      (α := α) targetImageInput μ
  /-- Compact active boxes used as inner boxes for artificial-face control. -/
  compactActiveBoxes : CompactActiveBoxData I omega
  /-- Selected partition and compact-active boxes are aligned. -/
  selectedPartitionAlignment :
    CompactActiveSelectedPartitionAlignment compactActiveBoxes selectedPartition
  /-- Measure-localized pieces use the selected chart label as source/target. -/
  localizedPieceAlignment :
    LocalizedInteriorPieceAlignment selectedPartition
      targetImageInput.targetImages
      (boundaryTarget.toMeasureBuilderData bulk).toM8MeasureLocalizationData
  /--
  The localized outer box lower corner is strictly below the selected inner
  lower corner.
  -/
  outer_lower_lt_selectedLower :
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      ((boundaryTarget.toMeasureBuilderData bulk).toM8MeasureLocalizationData
          |>.localizedInterior.piece x).lowerCorner j <
        selectedPartition.lower x j
  /--
  The selected inner upper corner is strictly below the localized outer upper
  corner.
  -/
  selectedUpper_lt_outer_upper :
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      selectedPartition.upper x j <
        ((boundaryTarget.toMeasureBuilderData bulk).toM8MeasureLocalizationData
          |>.localizedInterior.piece x).upperCorner j

namespace NaturalCompactSupportEndToEndInput

variable
    (D :
      NaturalCompactSupportEndToEndInput
        (α := α) I omega BoundaryPiece μ)

/-- The compact-support measure builder produced by the boundary-target glue. -/
def measureBuilder :
    CompactSupportMeasureToM8BuilderData
      (α := α) I omega D.selectedPartition D.targetImageInput.targetImages μ
      D.globalBulkIntegral D.boundaryTarget.globalBoundaryIntegral :=
  D.boundaryTarget.toMeasureBuilderData D.bulk

@[simp]
theorem measureBuilder_boundaryPartitionTerm :
    D.measureBuilder.toCompactSupportToM8MeasureData.boundaryPartitionTerm =
      D.targetImageInput.assembly.boundaryPartitionTerm := by
  rfl

/--
The strict-buffer alignment package induced by the explicit end-to-end fields.
-/
def naturalMeasureStrictBuilderAlignment :
    NaturalMeasureStrictBuilderAlignment
      D.targetImageInput D.measureBuilder D.compactActiveBoxes where
  selectedPartitionAlignment := D.selectedPartitionAlignment
  localizedPieceAlignment := D.localizedPieceAlignment
  outer_lower_lt_selectedLower := D.outer_lower_lt_selectedLower
  selectedUpper_lt_outer_upper := D.selectedUpper_lt_outer_upper
  target_boundaryPartitionTerm_eq_measureBuilder :=
    D.boundaryTarget.target_boundaryPartitionTerm_forMeasureBuilder D.bulk

@[simp]
theorem naturalMeasureStrictBuilderAlignment_selectedPartitionAlignment :
    D.naturalMeasureStrictBuilderAlignment.selectedPartitionAlignment =
      D.selectedPartitionAlignment := by
  rfl

/-- Convert the end-to-end input into the current natural compact-support input. -/
def toNaturalCompactSupportStokesInput :
    NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ :=
  D.naturalMeasureStrictBuilderAlignment.toNaturalCompactSupportStokesInput
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    D.formData D.selectedPartition_supportSet

@[simp]
theorem toNaturalCompactSupportStokesInput_measure :
    D.toNaturalCompactSupportStokesInput.measure =
      D.measureBuilder.toCompactSupportToM8MeasureData := by
  rfl

@[simp]
theorem toNaturalCompactSupportStokesInput_selectedPartition :
    D.toNaturalCompactSupportStokesInput.selectedPartition =
      D.selectedPartition := by
  rfl

@[simp]
theorem toNaturalCompactSupportStokesInput_targetImageInput :
    D.toNaturalCompactSupportStokesInput.targetImageInput =
      D.targetImageInput := by
  rfl

@[simp]
theorem toNaturalCompactSupportStokesInput_artificial :
    D.toNaturalCompactSupportStokesInput.artificial =
      (D.naturalMeasureStrictBuilderAlignment
        |>.toCompactActiveBoxStrictBufferAlignment
        |>.toLocalizedInteriorFormInnerBoxBuffer
        |>.toM8ArtificialFaceFields) := by
  rfl

/--
End-to-end compact-support Stokes in the current canonical theorem-facing
names.
-/
theorem canonical_stokes [IsManifold I 1 M] :
    D.toNaturalCompactSupportStokesInput.canonicalIntegralInterface.stokesStatement :=
  D.toNaturalCompactSupportStokesInput.canonical_stokes

end NaturalCompactSupportEndToEndInput

/--
Top-level end-to-end compact-support Stokes wrapper.

This is deliberately a wrapper around the natural compact-support theorem.  The
remaining work is to construct `NaturalCompactSupportEndToEndInput` from natural
manifold and measure data.
-/
theorem naturalCompactSupportStokes_canonical_of_endToEnd
    [IsManifold I 1 M]
    (D :
      NaturalCompactSupportEndToEndInput
        (α := α) I omega BoundaryPiece μ) :
    D.toNaturalCompactSupportStokesInput.canonicalIntegralInterface.stokesStatement :=
  D.canonical_stokes

end EndToEndRemainingInput

end Stokes

end
