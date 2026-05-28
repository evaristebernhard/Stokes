import Stokes.Global.SelectedReconstructionSourceAuto
import Stokes.Global.NaturalCompactSupportEndpointMarginAuto

/-!
# Compact-support endpoint facade

This module is a thin caller-facing facade for the current compact-support
endpoint route.  It keeps the existing small files in place, but lets endpoint
callers use the source-packaged reconstruction record together with constructor
chart alignment and strict selected-box margin data.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportEndpointFacade

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

namespace NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources

variable
    (S :
      NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu)

/-- The previous endpoint base obtained by projecting the packaged source. -/
abbrev endpointSelectedReconstructionBase :
    NaturalCompactSupportEndpointSelectedReconstructionBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  S.toSelectedReconstructionBaseSources

/-- The auto-selected endpoint base hidden behind the facade. -/
abbrev endpointAutoBase :
    NaturalCompactSupportEndpointAutoSelectedBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  S.endpointSelectedReconstructionBase.endpointAutoBase

/-- The endpoint M8 measure-localization data hidden behind the facade. -/
abbrev endpointMeasureLocalization :
    M8MeasureLocalizationData I omega
      S.endpointAutoBase.toBaseInput.selectedPartition
      S.endpointAutoBase.toBaseInput.targetImageInput.targetImages :=
  S.endpointSelectedReconstructionBase.endpointMeasureLocalization

/-- Strict selected-box margins in the endpoint shape consumed by the facade. -/
abbrev EndpointSelectedBoxStrictMargins :=
    S.endpointSelectedReconstructionBase.EndpointSelectedBoxStrictMargins

/--
Build selected/compact endpoint sources from the source-packaged
reconstruction, constructor chart-label alignment, and one packaged strict
margin witness.
-/
def toSelectedCompactSourcesOfM8ChartAlignmentAndStrictMargins
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (margins : S.EndpointSelectedBoxStrictMargins) :
    NaturalCompactSupportEndpointSelectedCompactSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  S.endpointSelectedReconstructionBase
    |>.toSelectedCompactSourcesOfM8ChartAlignmentAndStrictMargins A margins

@[simp]
theorem toSelectedCompactSourcesOfM8ChartAlignmentAndStrictMargins_base
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (margins : S.EndpointSelectedBoxStrictMargins) :
    (S.toSelectedCompactSourcesOfM8ChartAlignmentAndStrictMargins A margins).base =
      S.endpointSelectedReconstructionBase := by
  rfl

/--
Endpoint Stokes from the facade inputs: source-packaged reconstruction,
constructor chart-label alignment, and a packaged strict selected-box margin
witness.
-/
theorem stokes_ofM8ChartAlignmentAndStrictMargins
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (margins : S.EndpointSelectedBoxStrictMargins) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.endpointSelectedReconstructionBase
    |>.stokes_ofM8ChartAlignmentAndStrictMargins A margins

/--
Endpoint Stokes from the facade inputs when strict margins are supplied by an
active inner/outer box selection plus the four box-identification facts.
-/
theorem stokes_ofM8ChartAlignmentAndActiveStrictInnerOuter
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (D :
      ActiveStrictInnerOuterBoxSelections
        S.endpointAutoBase.toBaseInput.selectedPartition.active coordSupport)
    (innerLower_eq_selectedLower :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        D.innerLower x = S.endpointAutoBase.toBaseInput.selectedPartition.lower x)
    (innerUpper_eq_selectedUpper :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        D.innerUpper x = S.endpointAutoBase.toBaseInput.selectedPartition.upper x)
    (outerLower_eq_pieceLower :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        D.outerLower x =
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_pieceUpper :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        D.outerUpper x =
          (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.endpointSelectedReconstructionBase
    |>.stokes_ofM8ChartAlignmentAndActiveStrictInnerOuter A D
      innerLower_eq_selectedLower innerUpper_eq_selectedUpper
      outerLower_eq_pieceLower outerUpper_eq_pieceUpper

end NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources

end NaturalCompactSupportEndpointFacade

end Stokes

end
