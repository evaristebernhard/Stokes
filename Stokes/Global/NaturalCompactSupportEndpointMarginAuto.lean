import Stokes.Global.CompactSupportSelectedBoxEndToEnd
import Stokes.Global.NaturalCompactSupportEndpointConstructorFieldsAuto

/-!
# Compact-support endpoint strict-margin automation

`NaturalCompactSupportEndpointConstructorFieldsAuto` still exposed the two
pointwise strict-margin inequalities needed to push selected compact boxes into
the M8 localized outer boxes.  This module packages those inequalities as the
existing selected-box margin record, and also exposes the route from an active
inner/outer box selection.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportEndpointMarginAuto

universe u w b ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) → Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]

namespace NaturalCompactSupportEndpointSelectedReconstructionBaseSources

variable
    (S :
      NaturalCompactSupportEndpointSelectedReconstructionBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu)

/--
The selected-box strict-margin record specialized to the endpoint measure
localization assembled from selected reconstruction data.
-/
abbrev EndpointSelectedBoxStrictMargins :=
    SelectedBoxStrictMarginData
      S.endpointAutoBase.toBaseInput.selectedPartition
      S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
      S.endpointMeasureLocalization

/--
Endpoint strict margins generated from an active inner/outer box selection plus
the identifications saying that its inner boxes are the selected compact boxes
and its outer boxes are the endpoint localized M8 boxes.
-/
def endpointSelectedBoxStrictMarginsOfActiveStrictInnerOuter
    {coordSupport : M → Set (Fin (n + 1) → Real)}
    (D :
      ActiveStrictInnerOuterBoxSelections
        S.endpointAutoBase.toBaseInput.selectedPartition.active coordSupport)
    (innerLower_eq_selectedLower :
      ∀ x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active →
        D.innerLower x = S.endpointAutoBase.toBaseInput.selectedPartition.lower x)
    (innerUpper_eq_selectedUpper :
      ∀ x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active →
        D.innerUpper x = S.endpointAutoBase.toBaseInput.selectedPartition.upper x)
    (outerLower_eq_pieceLower :
      ∀ x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active →
        D.outerLower x =
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_pieceUpper :
      ∀ x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active →
        D.outerUpper x =
          (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner) :
    S.EndpointSelectedBoxStrictMargins :=
  SelectedBoxStrictMarginData.ofActiveStrictInnerOuter
    (selectedPartition := S.endpointAutoBase.toBaseInput.selectedPartition)
    (targetImages := S.endpointAutoBase.toBaseInput.targetImageInput.targetImages)
    (measureLocalization := S.endpointMeasureLocalization)
    D innerLower_eq_selectedLower innerUpper_eq_selectedUpper
    outerLower_eq_pieceLower outerUpper_eq_pieceUpper

/--
Compact-selection artificial alignment from constructor chart-label alignment
and the packaged selected-box strict-margin record.
-/
def compactSelectionArtificialAlignmentOfM8ChartAlignmentAndStrictMargins
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (margins : S.EndpointSelectedBoxStrictMargins) :
    EndpointCompactSelectionArtificialAlignment S.endpointAutoBase :=
  S.compactSelectionArtificialAlignmentOfM8ChartAlignment A
    margins.outer_lower_lt_selectedLower
    margins.selectedUpper_lt_outer_upper

@[simp]
theorem compactSelectionArtificialAlignment_strictMargins_localizedPieceAlignment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (margins : S.EndpointSelectedBoxStrictMargins) :
    (S.compactSelectionArtificialAlignmentOfM8ChartAlignmentAndStrictMargins
      A margins).localizedPieceAlignment =
        S.localizedPieceAlignmentOfM8ChartAlignment A := by
  rfl

/--
Selected/compact endpoint sources from constructor chart-label alignment and a
single packaged strict-margin witness.
-/
def toSelectedCompactSourcesOfM8ChartAlignmentAndStrictMargins
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (margins : S.EndpointSelectedBoxStrictMargins) :
    NaturalCompactSupportEndpointSelectedCompactSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu where
  base := S
  compactSelection :=
    S.compactSelectionArtificialAlignmentOfM8ChartAlignmentAndStrictMargins
      A margins

@[simp]
theorem toSelectedCompactSourcesOfM8ChartAlignmentAndStrictMargins_base
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (margins : S.EndpointSelectedBoxStrictMargins) :
    (S.toSelectedCompactSourcesOfM8ChartAlignmentAndStrictMargins
      A margins).base = S := by
  rfl

@[simp]
theorem toSelectedCompactSourcesOfM8ChartAlignmentAndStrictMargins_compactSelection
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (margins : S.EndpointSelectedBoxStrictMargins) :
    (S.toSelectedCompactSourcesOfM8ChartAlignmentAndStrictMargins
      A margins).compactSelection =
        S.compactSelectionArtificialAlignmentOfM8ChartAlignmentAndStrictMargins
          A margins := by
  rfl

/--
Endpoint Stokes from selected reconstruction, constructor chart-label
alignment, and one packaged selected-box strict-margin witness.
-/
theorem stokes_ofM8ChartAlignmentAndStrictMargins
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (margins : S.EndpointSelectedBoxStrictMargins) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  (S.toSelectedCompactSourcesOfM8ChartAlignmentAndStrictMargins
    A margins).stokes

/--
Endpoint Stokes from an active inner/outer box selection.  This is the bridge
from the pure coordinate strict-box selection layer into the endpoint theorem:
the two strict-margin inequalities are generated by the selection and the four
box-identification facts.
-/
theorem stokes_ofM8ChartAlignmentAndActiveStrictInnerOuter
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    {coordSupport : M → Set (Fin (n + 1) → Real)}
    (D :
      ActiveStrictInnerOuterBoxSelections
        S.endpointAutoBase.toBaseInput.selectedPartition.active coordSupport)
    (innerLower_eq_selectedLower :
      ∀ x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active →
        D.innerLower x = S.endpointAutoBase.toBaseInput.selectedPartition.lower x)
    (innerUpper_eq_selectedUpper :
      ∀ x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active →
        D.innerUpper x = S.endpointAutoBase.toBaseInput.selectedPartition.upper x)
    (outerLower_eq_pieceLower :
      ∀ x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active →
        D.outerLower x =
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_pieceUpper :
      ∀ x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active →
        D.outerUpper x =
          (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.stokes_ofM8ChartAlignmentAndStrictMargins A
    (S.endpointSelectedBoxStrictMarginsOfActiveStrictInnerOuter D
      innerLower_eq_selectedLower innerUpper_eq_selectedUpper
      outerLower_eq_pieceLower outerUpper_eq_pieceUpper)

end NaturalCompactSupportEndpointSelectedReconstructionBaseSources

end NaturalCompactSupportEndpointMarginAuto

end Stokes

end
