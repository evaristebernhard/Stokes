import Stokes.Global.LocalizedInteriorConstructorAlignment
import Stokes.Global.NaturalCompactSupportEndpointSelectedCompactAuto

/-!
# Compact-support endpoint from constructor chart fields

`NaturalCompactSupportEndpointSelectedCompactAuto` reduced the endpoint-facing
artificial cancellation input to three compact-selection fields.  This module
removes one more manual field in the common constructor route: callers can give
the localized-interior chart-label alignment carried by existing constructors,
and the endpoint-facing `LocalizedInteriorPieceAlignment` is produced here.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportEndpointConstructorFieldsAuto

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

/--
Localized-interior constructor chart labels generate the endpoint-facing piece
alignment for the assembled measure-localization package.
-/
def localizedPieceAlignmentOfM8ChartAlignment
    (A : LocalizedInteriorM8ChartAlignment S.localized) :
    LocalizedInteriorPieceAlignment
      S.endpointAutoBase.toBaseInput.selectedPartition
      S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
      S.endpointMeasureLocalization :=
  A.toPieceAlignment rfl

@[simp]
theorem localizedPieceAlignmentOfM8ChartAlignment_sourceChart_eq
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (x : M)
    (hx : x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active) :
    (S.localizedPieceAlignmentOfM8ChartAlignment A).sourceChart_eq x hx =
      A.sourceChart_eq x hx := by
  rfl

@[simp]
theorem localizedPieceAlignmentOfM8ChartAlignment_targetChart_eq
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (x : M)
    (hx : x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active) :
    (S.localizedPieceAlignmentOfM8ChartAlignment A).targetChart_eq x hx =
      A.targetChart_eq x hx := by
  rfl

/--
Compact-selection artificial alignment from constructor chart-label alignment
and the two remaining strict-margin fields.
-/
def compactSelectionArtificialAlignmentOfM8ChartAlignment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
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
    EndpointCompactSelectionArtificialAlignment S.endpointAutoBase :=
  S.compactSelectionArtificialAlignment
    (S.localizedPieceAlignmentOfM8ChartAlignment A)
    outer_lower_lt_selectedLower selectedUpper_lt_outer_upper

/--
Selected/compact endpoint sources from constructor chart-label alignment and
the two strict-margin fields.  This is the constructor-facing replacement for
passing a raw `LocalizedInteriorPieceAlignment`.
-/
def toSelectedCompactSourcesOfM8ChartAlignment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
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
    S.compactSelectionArtificialAlignmentOfM8ChartAlignment A
      outer_lower_lt_selectedLower selectedUpper_lt_outer_upper

@[simp]
theorem toSelectedCompactSourcesOfM8ChartAlignment_base
    (A : LocalizedInteriorM8ChartAlignment S.localized)
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
    (S.toSelectedCompactSourcesOfM8ChartAlignment A
      outer_lower_lt_selectedLower selectedUpper_lt_outer_upper).base = S :=
  rfl

/--
Endpoint Stokes from selected reconstruction, constructor chart-label
alignment, and the two compact selected-box strict-margin fields.
-/
theorem stokes_ofM8ChartAlignment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
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
  S.stokes_ofCompactSelectionFields
    (S.localizedPieceAlignmentOfM8ChartAlignment A)
    outer_lower_lt_selectedLower selectedUpper_lt_outer_upper

end NaturalCompactSupportEndpointSelectedReconstructionBaseSources

end NaturalCompactSupportEndpointConstructorFieldsAuto

end Stokes

end
