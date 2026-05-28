import Stokes.Global.EndToEndRemainingInput
import Stokes.Global.CompactSupportFiniteActiveToBuilder
import Stokes.Global.LocalizedInteriorConstructorAlignment
import Stokes.Global.StrictInnerOuterBox

/-!
# Compact-support selected-box end-to-end route

This file packages the selected-box part of the compact-support end-to-end
route.  Starting from a `CompactSupportFiniteActiveSelection` and its
smoothness data, the selected partition and compact active boxes are fixed
definitionally.  The remaining non-definitional facts are kept explicit and
centralized:

* chart-label alignment for the measure-localized interior pieces;
* strict outer margins around the selected boxes;
* the existing bulk and canonical boundary target measure packages.

No compact-support chart-box theorem, measure localization theorem, or boundary
change-of-variables theorem is proved here.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportSelectedBoxEndToEnd

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
variable {ρ : SmoothPartitionOfUnity M I M univ}
variable {K : Set M} {hK : IsCompact K}

namespace ActiveStrictInnerOuterBoxSelections

variable {β : Type*}
variable {active : Finset β}
variable {coordSupport : β → Set (Fin (n + 1) → Real)}

/-- Active strict selections expose the lower coordinate margin. -/
theorem outerLower_lt_innerLower
    (D : ActiveStrictInnerOuterBoxSelections active coordSupport)
    {i : β} (hi : i ∈ active) (j : Fin (n + 1)) :
    D.outerLower i j < D.innerLower i j := by
  have hmem :
      D.innerLower i ∈ Set.Icc (D.innerLower i) (D.innerUpper i) := by
    exact ⟨le_rfl, D.inner_le_upper i hi⟩
  exact (D.innerIcc_subset_outerInterior i hi hmem j).1

/-- Active strict selections expose the upper coordinate margin. -/
theorem innerUpper_lt_outerUpper
    (D : ActiveStrictInnerOuterBoxSelections active coordSupport)
    {i : β} (hi : i ∈ active) (j : Fin (n + 1)) :
    D.innerUpper i j < D.outerUpper i j := by
  have hmem :
      D.innerUpper i ∈ Set.Icc (D.innerLower i) (D.innerUpper i) := by
    exact ⟨D.inner_le_upper i hi, le_rfl⟩
  exact (D.innerIcc_subset_outerInterior i hi hmem j).2

end ActiveStrictInnerOuterBoxSelections

/--
Strict margin data in the exact selected-box shape consumed by
`NaturalMeasureStrictBuilderAlignment`.

This is intentionally only the margin layer: it does not assert support
containment or local chart-domain facts.
-/
structure SelectedBoxStrictMarginData
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages) where
  outer_lower_lt_selectedLower :
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      (measureLocalization.localizedInterior.piece x).lowerCorner j <
        selectedPartition.lower x j
  selectedUpper_lt_outer_upper :
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      selectedPartition.upper x j <
        (measureLocalization.localizedInterior.piece x).upperCorner j

namespace SelectedBoxStrictMarginData

variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/--
Build selected-box strict margins from an active inner/outer selection plus
explicit identifications with the selected box corners and M8 outer corners.

The identifications are deliberately fields: `StrictInnerOuterBox` gives pure
coordinate margins, while choosing those boxes to be the M8 boxes is geometric
construction work for the surrounding chart-box selection layer.
-/
def ofActiveStrictInnerOuter
    {coordSupport : M → Set (Fin (n + 1) → Real)}
    (D :
      ActiveStrictInnerOuterBoxSelections selectedPartition.active
        coordSupport)
    (innerLower_eq_selectedLower :
      ∀ x, x ∈ selectedPartition.active →
        D.innerLower x = selectedPartition.lower x)
    (innerUpper_eq_selectedUpper :
      ∀ x, x ∈ selectedPartition.active →
        D.innerUpper x = selectedPartition.upper x)
    (outerLower_eq_pieceLower :
      ∀ x, x ∈ selectedPartition.active →
        D.outerLower x =
          (measureLocalization.localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_pieceUpper :
      ∀ x, x ∈ selectedPartition.active →
        D.outerUpper x =
          (measureLocalization.localizedInterior.piece x).upperCorner) :
    SelectedBoxStrictMarginData selectedPartition targetImages
      measureLocalization where
  outer_lower_lt_selectedLower := by
    intro x hx j
    have h := D.outerLower_lt_innerLower hx j
    rw [outerLower_eq_pieceLower x hx, innerLower_eq_selectedLower x hx] at h
    exact h
  selectedUpper_lt_outer_upper := by
    intro x hx j
    have h := D.innerUpper_lt_outerUpper hx j
    rw [innerUpper_eq_selectedUpper x hx, outerUpper_eq_pieceUpper x hx] at h
    exact h

end SelectedBoxStrictMarginData

/--
Selected-box end-to-end data produced by a compact-support finite-active
selection.

The fields `selection` and `smoothness` determine the selected partition and
compact active boxes.  The remaining data is exactly what is still needed to
feed the current natural measure/strict-buffer builder:
bulk measure data, canonical boundary target measure data, chart-label
alignment for localized pieces, and strict margins around the selected boxes.
-/
structure CompactSupportSelectedBoxEndToEndData
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (K : Set M) (hK : IsCompact K)
    (μ : Measure α) [IsFiniteMeasureOnCompacts μ] where
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
  /-- The represented bulk integral value used by the selected bulk route. -/
  globalBulkIntegral : Real
  /-- Selected bulk measure localization data. -/
  bulk :
    BulkMeasureFromPartitionData
      (α := α) (μ := μ)
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages globalBulkIntegral
  /-- Canonical boundary compact-support data for the target-image route. -/
  boundaryTarget :
    CanonicalBoundaryTargetCompactSupportInput
      (α := α) targetImageInput μ
  /-- The bulk-localized pieces have the selected chart label as source/target. -/
  localizedChartAlignment :
    LocalizedInteriorM8ChartAlignment bulk.localized
  /-- Strict M8 outer margins around the selected finite-active boxes. -/
  strictMargins :
    SelectedBoxStrictMarginData
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages
      (boundaryTarget.toMeasureBuilderData bulk).toM8MeasureLocalizationData

namespace CompactSupportSelectedBoxEndToEndData

variable
    (D :
      CompactSupportSelectedBoxEndToEndData
        (α := α) I omega BoundaryPiece ρ K hK μ)

/-- The selected partition determined by `selection` and `smoothness`. -/
abbrev selectedPartition : SelectedBoxPartitionOfUnity I omega :=
  D.selection.selectedBoxPartitionOfUnity D.smoothness

/-- The compact active boxes determined by the finite-active selection. -/
abbrev compactActiveBoxes : CompactActiveBoxData I omega :=
  D.selection.compactActiveBoxData

/-- The measure builder induced by the selected bulk data and canonical boundary data. -/
abbrev measureBuilder :
    CompactSupportMeasureToM8BuilderData
      (α := α) I omega D.selectedPartition D.targetImageInput.targetImages μ
      D.globalBulkIntegral D.boundaryTarget.globalBoundaryIntegral :=
  D.boundaryTarget.toMeasureBuilderData D.bulk

/-- Selected-partition alignment supplied definitionally by the compact-support selection. -/
def selectedPartitionAlignment :
    CompactActiveSelectedPartitionAlignment D.compactActiveBoxes
      D.selectedPartition :=
  D.selection.toCompactActiveSelectedPartitionAlignment D.smoothness

/-- Chart-label alignment for the measure-localized pieces. -/
def localizedPieceAlignment :
    LocalizedInteriorPieceAlignment D.selectedPartition
      D.targetImageInput.targetImages D.measureBuilder.toM8MeasureLocalizationData :=
  D.localizedChartAlignment.toPieceAlignment rfl

/-- Support-set compatibility in the shape expected by natural inputs. -/
theorem selectedPartition_supportSet :
    D.selectedPartition.K = D.formData.supportSet := by
  simpa [selectedPartition] using D.supportSet_eq

/--
The selected-box compact-support route produces the high-level
measure/strict-buffer alignment consumed by the natural builder.
-/
def toNaturalMeasureStrictBuilderAlignment :
    NaturalMeasureStrictBuilderAlignment
      D.targetImageInput D.measureBuilder D.compactActiveBoxes where
  selectedPartitionAlignment := D.selectedPartitionAlignment
  localizedPieceAlignment := D.localizedPieceAlignment
  outer_lower_lt_selectedLower :=
    D.strictMargins.outer_lower_lt_selectedLower
  selectedUpper_lt_outer_upper :=
    D.strictMargins.selectedUpper_lt_outer_upper
  target_boundaryPartitionTerm_eq_measureBuilder :=
    D.boundaryTarget.target_boundaryPartitionTerm_forMeasureBuilder D.bulk

@[simp]
theorem toNaturalMeasureStrictBuilderAlignment_selectedPartitionAlignment :
    D.toNaturalMeasureStrictBuilderAlignment.selectedPartitionAlignment =
      D.selectedPartitionAlignment := by
  rfl

@[simp]
theorem toNaturalMeasureStrictBuilderAlignment_localizedPieceAlignment :
    D.toNaturalMeasureStrictBuilderAlignment.localizedPieceAlignment =
      D.localizedPieceAlignment := by
  rfl

/--
The same selected-box package as the current end-to-end input record.  This is
the bridge into `naturalCompactSupportStokes_canonical_of_endToEnd`.
-/
def toNaturalCompactSupportEndToEndInput :
    NaturalCompactSupportEndToEndInput
      (α := α) I omega BoundaryPiece μ where
  formData := D.formData
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  selectedPartition := D.selectedPartition
  selectedPartition_supportSet := D.selectedPartition_supportSet
  targetImageInput := D.targetImageInput
  globalBulkIntegral := D.globalBulkIntegral
  bulk := D.bulk
  boundaryTarget := D.boundaryTarget
  compactActiveBoxes := D.compactActiveBoxes
  selectedPartitionAlignment := D.selectedPartitionAlignment
  localizedPieceAlignment := D.localizedPieceAlignment
  outer_lower_lt_selectedLower :=
    D.strictMargins.outer_lower_lt_selectedLower
  selectedUpper_lt_outer_upper :=
    D.strictMargins.selectedUpper_lt_outer_upper

@[simp]
theorem toNaturalCompactSupportEndToEndInput_selectedPartition :
    D.toNaturalCompactSupportEndToEndInput.selectedPartition =
      D.selectedPartition := by
  rfl

@[simp]
theorem toNaturalCompactSupportEndToEndInput_compactActiveBoxes :
    D.toNaturalCompactSupportEndToEndInput.compactActiveBoxes =
      D.compactActiveBoxes := by
  rfl

@[simp]
theorem toNaturalCompactSupportEndToEndInput_alignment :
    D.toNaturalCompactSupportEndToEndInput.naturalMeasureStrictBuilderAlignment =
      D.toNaturalMeasureStrictBuilderAlignment := by
  rfl

/--
Existence spelling for callers that want the selected compact-support branch as
a single high-level alignment witness.
-/
theorem exists_compactSupportSelectedPartition_withStrictBufferAlignment :
    ∃ A :
      NaturalMeasureStrictBuilderAlignment
        D.targetImageInput D.measureBuilder D.compactActiveBoxes,
      A = D.toNaturalMeasureStrictBuilderAlignment := by
  exact ⟨D.toNaturalMeasureStrictBuilderAlignment, rfl⟩

/-- Compact-support Stokes wrapper obtained once this selected-box package exists. -/
theorem canonical_stokes [IsManifold I 1 M] :
    D.toNaturalCompactSupportEndToEndInput
      |>.toNaturalCompactSupportStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement :=
  D.toNaturalCompactSupportEndToEndInput.canonical_stokes

end CompactSupportSelectedBoxEndToEndData

end CompactSupportSelectedBoxEndToEnd

end Stokes

end
