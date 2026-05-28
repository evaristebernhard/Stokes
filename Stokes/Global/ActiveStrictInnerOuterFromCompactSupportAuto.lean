import Stokes.Global.NaturalFiniteActiveFromCompactSupportAuto
import Stokes.Global.SelectedStrictMarginsFromChartBoxAuto
import Stokes.Global.CompactSupportStrictBufferFromActive

/-!
# Active strict inner/outer boxes from compact-support selections

This module reduces one of the remaining compact-support inputs: callers should
not have to manually manufacture an `ActiveStrictInnerOuterBoxSelections` record
once compact coordinate supports or selected chart-box containment are already
available.

The first group of declarations builds strict inner/outer boxes directly from
compactness of active coordinate supports.  The second group is the endpoint
useful route: when the selected closed chart box is already known to lie in the
strict localized-piece box, the active strict source is chosen definitionally
with inner box equal to the selected box and outer box equal to the localized
piece.  That removes the separate active strict-box object and the four corner
identification fields at downstream call sites.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory
open scoped Manifold Topology

namespace Stokes

section ActiveStrictInnerOuterFromCompactSupportAuto

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {rho : SmoothPartitionOfUnity M I M univ}

namespace ActiveChartCompactSupportData

variable {P : FiniteActiveOnCompact (M := M) I}

/-- Active compact-support data automatically supplies a strict inner/outer
box selection for its compact coordinate supports. -/
def toActiveStrictInnerOuterBoxSelections
    (D : ActiveChartCompactSupportData P omega) :
    ActiveStrictInnerOuterBoxSelections P.active D.coordSupport :=
  ActiveStrictInnerOuterBoxSelections.ofCompact D.isCompact_coordSupport

end ActiveChartCompactSupportData

namespace CompactSupportFiniteActiveSelection

variable {K : Set M} {hK : IsCompact K}

/-- Compact-support finite-active selections automatically supply strict
inner/outer boxes for their active coordinate supports. -/
def toActiveStrictInnerOuterBoxSelections
    (S :
      CompactSupportFiniteActiveSelection
        (I := I) rho K hK omega) :
    ActiveStrictInnerOuterBoxSelections
      S.finiteActive.active S.supportData.coordSupport :=
  S.supportData.toActiveStrictInnerOuterBoxSelections

end CompactSupportFiniteActiveSelection

namespace CompactlySupportedSmoothFormData.SourceChartCompactImagesOnSupport

variable {formData : CompactlySupportedSmoothFormData I omega}

/-- Compact chart-image source data automatically supplies strict inner/outer
boxes for the generated compact coordinate images. -/
def toActiveStrictInnerOuterBoxSelections
    (S :
      CompactlySupportedSmoothFormData.SourceChartCompactImagesOnSupport
        (I := I) (omega := omega) (rho := rho) formData) :
    ActiveStrictInnerOuterBoxSelections
      (formData.finiteActiveOnSupport (rho := rho)).active S.coordSupport :=
  ActiveStrictInnerOuterBoxSelections.ofCompact
    (fun _ hi => S.isCompact_coordSupport hi)

end CompactlySupportedSmoothFormData.SourceChartCompactImagesOnSupport

namespace CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData

variable {formData : CompactlySupportedSmoothFormData I omega}

/-- Natural compact-source data automatically supplies strict inner/outer boxes
for its generated compact coordinate images. -/
def toActiveStrictInnerOuterBoxSelections
    (D :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (I := I) (omega := omega) (rho := rho) formData) :
    ActiveStrictInnerOuterBoxSelections
      (formData.finiteActiveOnSupport (rho := rho)).active
      D.source.coordSupport :=
  D.source.toActiveStrictInnerOuterBoxSelections

end CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData

namespace SelectedBoxChartBoxStrictContainmentData

variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
    M8MeasureLocalizationData I omega selectedPartition targetImages}

/-- Selected-box containment supplies an active strict inner/outer source whose
inner boxes are exactly the selected boxes and whose outer boxes are exactly
the localized M8 piece boxes. -/
def toActiveStrictInnerOuterBoxSelections
    (C :
      SelectedBoxChartBoxStrictContainmentData selectedPartition targetImages
        measureLocalization)
    (coordSupport : M -> Set (Fin (n + 1) -> Real))
    (hcoord_subset_selected :
      forall x, x ∈ selectedPartition.active ->
        coordSupport x ⊆ Set.Icc (selectedPartition.lower x)
          (selectedPartition.upper x)) :
    ActiveStrictInnerOuterBoxSelections selectedPartition.active
      coordSupport where
  innerLower := selectedPartition.lower
  innerUpper := selectedPartition.upper
  outerLower := fun x =>
    (measureLocalization.localizedInterior.piece x).lowerCorner
  outerUpper := fun x =>
    (measureLocalization.localizedInterior.piece x).upperCorner
  inner_le_upper := by
    intro x hx
    exact selectedPartition.le hx
  outer_le_upper := by
    intro x hx j
    have hlow :
        (measureLocalization.localizedInterior.piece x).lowerCorner j <
          selectedPartition.lower x j :=
      C.outer_lower_lt_selectedLower x hx j
    have hsel : selectedPartition.lower x j ≤ selectedPartition.upper x j :=
      selectedPartition.le hx j
    have hup :
        selectedPartition.upper x j <
          (measureLocalization.localizedInterior.piece x).upperCorner j :=
      C.selectedUpper_lt_outer_upper x hx j
    exact le_of_lt ((hlow.trans_le hsel).trans hup)
  coordSupport_subset_innerIcc := hcoord_subset_selected
  innerIcc_subset_outerInterior := by
    intro x hx
    exact C.selectedBox_subset_pieceInterior x hx

@[simp]
theorem toActiveStrictInnerOuterBoxSelections_innerLower
    (C :
      SelectedBoxChartBoxStrictContainmentData selectedPartition targetImages
        measureLocalization)
    (coordSupport : M -> Set (Fin (n + 1) -> Real))
    (hcoord_subset_selected :
      forall x, x ∈ selectedPartition.active ->
        coordSupport x ⊆ Set.Icc (selectedPartition.lower x)
          (selectedPartition.upper x)) :
    (C.toActiveStrictInnerOuterBoxSelections coordSupport
      hcoord_subset_selected).innerLower = selectedPartition.lower := by
  rfl

@[simp]
theorem toActiveStrictInnerOuterBoxSelections_outerLower
    (C :
      SelectedBoxChartBoxStrictContainmentData selectedPartition targetImages
        measureLocalization)
    (coordSupport : M -> Set (Fin (n + 1) -> Real))
    (hcoord_subset_selected :
      forall x, x ∈ selectedPartition.active ->
        coordSupport x ⊆ Set.Icc (selectedPartition.lower x)
          (selectedPartition.upper x)) :
    (C.toActiveStrictInnerOuterBoxSelections coordSupport
      hcoord_subset_selected).outerLower =
        fun x => (measureLocalization.localizedInterior.piece x).lowerCorner := by
  rfl

end SelectedBoxChartBoxStrictContainmentData

namespace CompactSupportFiniteActiveSelection

variable {K : Set M} {hK : IsCompact K}

/-- The coordinate supports of a compact-support finite-active selection lie in
the selected chart boxes generated from that same selection. -/
theorem coordSupport_subset_selectedBox
    (S :
      CompactSupportFiniteActiveSelection
        (I := I) rho K hK omega)
    (smoothness :
      ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega) :
    forall x,
      x ∈ (S.selectedBoxPartitionOfUnity smoothness).active ->
        S.supportData.coordSupport x ⊆
          Set.Icc
            ((S.selectedBoxPartitionOfUnity smoothness).lower x)
            ((S.selectedBoxPartitionOfUnity smoothness).upper x) := by
  intro x hx y hy
  have hxActive : x ∈ S.finiteActive.active := by
    simpa using hx
  have hyBox :
      y ∈ Set.Icc (S.supportData.box x).a (S.supportData.box x).b := by
    exact (S.supportData.box x).subset_Icc (by
      simpa [S.supportData.box_K_eq_coordSupport hxActive] using hy)
  simpa [
    CompactSupportFiniteActiveSelection.selectedBoxPartitionOfUnity_lower_apply_compactActiveBoxData,
    CompactSupportFiniteActiveSelection.selectedBoxPartitionOfUnity_upper_apply_compactActiveBoxData,
    CompactActiveBoxData.lower, CompactActiveBoxData.upper] using hyBox

/-- Compact-support finite-active selections plus selected-box containment give
an active strict inner/outer source with inner boxes equal to the selected boxes
and outer boxes equal to the localized M8 pieces. -/
def toSelectedPieceActiveStrictInnerOuterBoxSelectionsOfChartBoxContainment
    (S :
      CompactSupportFiniteActiveSelection
        (I := I) rho K hK omega)
    (smoothness :
      ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega)
    {targetImages :
      BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega
        (S.selectedBoxPartitionOfUnity smoothness) targetImages}
    (C :
      SelectedBoxChartBoxStrictContainmentData
        (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization) :
    ActiveStrictInnerOuterBoxSelections
      (S.selectedBoxPartitionOfUnity smoothness).active
      S.supportData.coordSupport :=
  C.toActiveStrictInnerOuterBoxSelections S.supportData.coordSupport
    (S.coordSupport_subset_selectedBox smoothness)

/-- Selected-box containment gives selected strict margins for a compact-support
finite-active selection. -/
def selectedStrictMarginsOfChartBoxContainment
    (S :
      CompactSupportFiniteActiveSelection
        (I := I) rho K hK omega)
    (smoothness :
      ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega)
    {targetImages :
      BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega
        (S.selectedBoxPartitionOfUnity smoothness) targetImages}
    (C :
      SelectedBoxChartBoxStrictContainmentData
        (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization) :
    SelectedBoxStrictMarginData
      (S.selectedBoxPartitionOfUnity smoothness)
      targetImages measureLocalization :=
  C.toSelectedBoxStrictMarginData

/-- Selected-box containment gives the compact-active strict-buffer constructor
for a compact-support finite-active selection. -/
def strictBufferConstructorDataOfChartBoxContainment
    (S :
      CompactSupportFiniteActiveSelection
        (I := I) rho K hK omega)
    (smoothness :
      ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega)
    {targetImages :
      BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega
        (S.selectedBoxPartitionOfUnity smoothness) targetImages}
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment
        (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization)
    (C :
      SelectedBoxChartBoxStrictContainmentData
        (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization) :
    CompactActiveStrictBufferConstructorData S.compactActiveBoxData
      (S.selectedBoxPartitionOfUnity smoothness)
      targetImages measureLocalization :=
  S.toStrictBufferConstructorDataOfSelectedStrictMargins
    smoothness localizedPieceAlignment
    (S.selectedStrictMarginsOfChartBoxContainment smoothness C)

/-- Selected-box containment gives the support buffer consumed by the
artificial-face support-zero route. -/
def compactSupportBoxBufferOfChartBoxContainment
    (S :
      CompactSupportFiniteActiveSelection
        (I := I) rho K hK omega)
    (smoothness :
      ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega)
    {targetImages :
      BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega
        (S.selectedBoxPartitionOfUnity smoothness) targetImages}
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment
        (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization)
    (C :
      SelectedBoxChartBoxStrictContainmentData
        (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization) :
    CompactSupportBoxBuffer I omega
      (S.selectedBoxPartitionOfUnity smoothness)
      targetImages measureLocalization :=
  (S.strictBufferConstructorDataOfChartBoxContainment
      smoothness localizedPieceAlignment C)
    |>.toCompactActiveBoxStrictBufferAlignment
    |>.toCompactSupportBoxBuffer

end CompactSupportFiniteActiveSelection

namespace CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData

variable {formData : CompactlySupportedSmoothFormData I omega}
variable [IsManifold I 1 M]

/-- The compact coordinate supports generated by a natural compact-source
selection lie in the selected chart boxes of the generated finite-active
selection. -/
theorem coordSupport_subset_selectedBox
    (D :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (I := I) (omega := omega) (rho := rho) formData) :
    forall x,
      x ∈ D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition.active ->
        D.source.coordSupport x ⊆
          Set.Icc
            (D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition.lower x)
            (D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition.upper x) := by
  intro x hx
  have hxActive :
      x ∈ (formData.finiteActiveOnSupport (rho := rho)).active := by
    simpa [toNaturalFiniteActiveChartBoxSelectionData] using hx
  have h := D.source.coordSupport_subset_box hxActive
  simpa [toNaturalFiniteActiveChartBoxSelectionData,
    CompactSupportFiniteActiveSelection.selectedBoxPartitionOfUnity_lower_apply_compactActiveBoxData,
    CompactSupportFiniteActiveSelection.selectedBoxPartitionOfUnity_upper_apply_compactActiveBoxData,
    CompactActiveBoxData.lower, CompactActiveBoxData.upper] using h

/-- Natural compact-source data plus selected-box containment gives an active
strict inner/outer source with no extra corner-identification fields. -/
def toSelectedPieceActiveStrictInnerOuterBoxSelections
    (D :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (I := I) (omega := omega) (rho := rho) formData)
    {targetImages :
      BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega
        D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition
        targetImages}
    (C :
      SelectedBoxChartBoxStrictContainmentData
        D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition
        targetImages measureLocalization) :
    ActiveStrictInnerOuterBoxSelections
      D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition.active
      D.source.coordSupport :=
  C.toActiveStrictInnerOuterBoxSelections D.source.coordSupport
    D.coordSupport_subset_selectedBox

/-- The same containment directly gives selected strict margins for the natural
compact-source route. -/
def selectedStrictMarginsOfChartBoxContainment
    (D :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (I := I) (omega := omega) (rho := rho) formData)
    {targetImages :
      BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega
        D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition
        targetImages}
    (C :
      SelectedBoxChartBoxStrictContainmentData
        D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition
        targetImages measureLocalization) :
    SelectedBoxStrictMarginData
      D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition
      targetImages measureLocalization :=
  C.toSelectedBoxStrictMarginData

/-- Natural compact-source data plus selected-box containment gives the
strict-buffer constructor used by the artificial-face route. -/
def strictBufferConstructorDataOfChartBoxContainment
    (D :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (I := I) (omega := omega) (rho := rho) formData)
    {targetImages :
      BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega
        D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition
        targetImages}
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment
        D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition
        targetImages measureLocalization)
    (C :
      SelectedBoxChartBoxStrictContainmentData
        D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition
        targetImages measureLocalization) :
    CompactActiveStrictBufferConstructorData
      D.toNaturalFiniteActiveChartBoxSelectionData.compactActiveBoxData
      D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition
      targetImages measureLocalization :=
  D.toNaturalFiniteActiveChartBoxSelectionData.selection
    |>.toStrictBufferConstructorDataOfSelectedStrictMargins
      D.toNaturalFiniteActiveChartBoxSelectionData.smoothness
      localizedPieceAlignment
      (D.selectedStrictMarginsOfChartBoxContainment C)

/-- Natural compact-source data plus selected-box containment gives the
compact-support buffer consumed by the support-zero/artificial-face API. -/
def compactSupportBoxBufferOfChartBoxContainment
    (D :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (I := I) (omega := omega) (rho := rho) formData)
    {targetImages :
      BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega
        D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition
        targetImages}
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment
        D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition
        targetImages measureLocalization)
    (C :
      SelectedBoxChartBoxStrictContainmentData
        D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition
        targetImages measureLocalization) :
    CompactSupportBoxBuffer I omega
      D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition
      targetImages measureLocalization :=
  (D.strictBufferConstructorDataOfChartBoxContainment
      localizedPieceAlignment C)
    |>.toCompactActiveBoxStrictBufferAlignment
    |>.toCompactSupportBoxBuffer

end CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData

end ActiveStrictInnerOuterFromCompactSupportAuto

end Stokes

end
