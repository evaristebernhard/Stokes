import Stokes.Global.NaturalCompactSupportEndpointConcrete

/-!
# Selected compact-support endpoint automation

This file tightens the current compact-support endpoint interface.  The previous
`NaturalCompactSupportEndpointSelectedCompactSources` record already removed
the raw bulk `extDerivAE` and artificial-face fields, but callers still had to
manually assemble `EndpointCompactSelectionArtificialAlignment`.

The constructors below keep the real remaining geometry visible as exactly the
three compact-selection fields: localized-piece chart alignment and the two
strict outer-margin inequalities.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportEndpointSelectedCompactAuto

universe u w b ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]

namespace NaturalCompactSupportEndpointSelectedReconstructionBaseSources

variable
    (S :
      NaturalCompactSupportEndpointSelectedReconstructionBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu)

/-- The auto-selected endpoint base generated from selected reconstruction data. -/
abbrev endpointAutoBase :
    NaturalCompactSupportEndpointAutoSelectedBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  S.toUnifiedBaseSources.toAutoSelectedBaseSources

/-- The endpoint M8 measure-localization data assembled from the base source. -/
abbrev endpointMeasureLocalization :
    M8MeasureLocalizationData I omega
      S.endpointAutoBase.toBaseInput.selectedPartition
      S.endpointAutoBase.toBaseInput.targetImageInput.targetImages :=
  S.endpointAutoBase.endpointMeasureLocalization

/--
Compact-selection artificial alignment generated from the three remaining
geometric compact-support fields.
-/
def compactSelectionArtificialAlignment
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment
        S.endpointAutoBase.toBaseInput.selectedPartition
        S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization)
    (outer_lower_lt_selectedLower :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner j <
            S.endpointAutoBase.toBaseInput.selectedPartition.lower x j)
    (selectedUpper_lt_outer_upper :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          S.endpointAutoBase.toBaseInput.selectedPartition.upper x j <
            (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner j) :
    EndpointCompactSelectionArtificialAlignment S.endpointAutoBase where
  localizedPieceAlignment := localizedPieceAlignment
  outer_lower_lt_selectedLower := outer_lower_lt_selectedLower
  selectedUpper_lt_outer_upper := selectedUpper_lt_outer_upper

@[simp]
theorem compactSelectionArtificialAlignment_localizedPieceAlignment
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment
        S.endpointAutoBase.toBaseInput.selectedPartition
        S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization)
    (outer_lower_lt_selectedLower :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner j <
            S.endpointAutoBase.toBaseInput.selectedPartition.lower x j)
    (selectedUpper_lt_outer_upper :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          S.endpointAutoBase.toBaseInput.selectedPartition.upper x j <
            (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner j) :
    (S.compactSelectionArtificialAlignment localizedPieceAlignment
      outer_lower_lt_selectedLower selectedUpper_lt_outer_upper).localizedPieceAlignment =
        localizedPieceAlignment :=
  rfl

/--
Build the selected/compact endpoint source directly from selected reconstruction
base data and the three compact-selection fields.
-/
def toSelectedCompactSourcesOfCompactSelectionFields
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment
        S.endpointAutoBase.toBaseInput.selectedPartition
        S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization)
    (outer_lower_lt_selectedLower :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner j <
            S.endpointAutoBase.toBaseInput.selectedPartition.lower x j)
    (selectedUpper_lt_outer_upper :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          S.endpointAutoBase.toBaseInput.selectedPartition.upper x j <
            (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner j) :
    NaturalCompactSupportEndpointSelectedCompactSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu where
  base := S
  compactSelection :=
    S.compactSelectionArtificialAlignment localizedPieceAlignment
      outer_lower_lt_selectedLower selectedUpper_lt_outer_upper

@[simp]
theorem toSelectedCompactSourcesOfCompactSelectionFields_base
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment
        S.endpointAutoBase.toBaseInput.selectedPartition
        S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization)
    (outer_lower_lt_selectedLower :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner j <
            S.endpointAutoBase.toBaseInput.selectedPartition.lower x j)
    (selectedUpper_lt_outer_upper :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          S.endpointAutoBase.toBaseInput.selectedPartition.upper x j <
            (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner j) :
    (S.toSelectedCompactSourcesOfCompactSelectionFields localizedPieceAlignment
      outer_lower_lt_selectedLower selectedUpper_lt_outer_upper).base = S :=
  rfl

@[simp]
theorem toSelectedCompactSourcesOfCompactSelectionFields_compactSelection
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment
        S.endpointAutoBase.toBaseInput.selectedPartition
        S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization)
    (outer_lower_lt_selectedLower :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner j <
            S.endpointAutoBase.toBaseInput.selectedPartition.lower x j)
    (selectedUpper_lt_outer_upper :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          S.endpointAutoBase.toBaseInput.selectedPartition.upper x j <
            (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner j) :
    (S.toSelectedCompactSourcesOfCompactSelectionFields localizedPieceAlignment
      outer_lower_lt_selectedLower selectedUpper_lt_outer_upper).compactSelection =
        S.compactSelectionArtificialAlignment localizedPieceAlignment
          outer_lower_lt_selectedLower selectedUpper_lt_outer_upper :=
  rfl

/--
Endpoint theorem from selected reconstruction plus the three compact-selection
fields, without exposing `EndpointCompactSelectionArtificialAlignment`.
-/
theorem stokes_ofCompactSelectionFields
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment
        S.endpointAutoBase.toBaseInput.selectedPartition
        S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization)
    (outer_lower_lt_selectedLower :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner j <
            S.endpointAutoBase.toBaseInput.selectedPartition.lower x j)
    (selectedUpper_lt_outer_upper :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          S.endpointAutoBase.toBaseInput.selectedPartition.upper x j <
            (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner j) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  (S.toSelectedCompactSourcesOfCompactSelectionFields localizedPieceAlignment
    outer_lower_lt_selectedLower selectedUpper_lt_outer_upper).stokes

end NaturalCompactSupportEndpointSelectedReconstructionBaseSources

end NaturalCompactSupportEndpointSelectedCompactAuto

end Stokes

end
