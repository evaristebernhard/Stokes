import Stokes.Global.NaturalFiniteActiveChartBoxSelectionAuto
import Stokes.Global.SelectedStrictMarginsFromChartBoxAuto
import Stokes.Global.NaturalCompactSupportEndpointNaturalInputAuto

/-!
# Endpoint selected strict margins from natural chart boxes

This module is a small automation layer around the current compact-support
endpoint route.  Once a natural finite-active chart-box selection and an
endpoint source have been assembled, the remaining geometric margin input is
most naturally stated either as selected chart-box containment in the localized
M8 piece, or as an active strict inner/outer box selection with corner
identifications.

The declarations below turn those geometric packages into the endpoint-facing
`EndpointSelectedBoxStrictMargins` record, then immediately expose the existing
selected-margin compact-support Stokes theorem.  No analytic, measure, or
change-of-variables theorem is proved here.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section EndpointSelectedStrictMarginsFromNaturalChartBoxesAuto

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

namespace NaturalCompactSupportEndpointEndToEndSources

variable {D : NaturalCompactSupportPartitionConstructorData I omega rho}
variable
    (E :
      NaturalCompactSupportEndpointEndToEndSources
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu)

/-- Endpoint-facing selected chart-box strict containment for an end-to-end source. -/
abbrev NaturalChartBoxStrictContainmentData :=
  SelectedBoxChartBoxStrictContainmentData
    (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition
    (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.targetImageInput.targetImages
    (endpointMeasureLocalization E)

/--
Selected strict margins generated from the endpoint selected chart-box
containment package.
-/
def endpointSelectedStrictMarginsOfChartBoxStrictContainment
    (C : NaturalChartBoxStrictContainmentData E) :
    (toSelectedReconstructionEndpointSource E).EndpointSelectedBoxStrictMargins :=
  C.toSelectedBoxStrictMarginData

/--
Selected strict margins generated from active strict inner/outer boxes after
identifying their inner corners with the selected chart box and their outer
corners with the localized M8 piece.
-/
def endpointSelectedStrictMarginsOfActiveStrictInnerOuter
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (boxes :
      ActiveStrictInnerOuterBoxSelections
        (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.active
        coordSupport)
    (innerLower_eq_selectedLower :
      forall x,
        x ∈ (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.active ->
          boxes.innerLower x =
            (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.lower x)
    (innerUpper_eq_selectedUpper :
      forall x,
        x ∈ (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.active ->
          boxes.innerUpper x =
            (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.upper x)
    (outerLower_eq_pieceLower :
      forall x,
        x ∈ (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.active ->
          boxes.outerLower x =
            ((endpointMeasureLocalization E).localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_pieceUpper :
      forall x,
        x ∈ (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.active ->
          boxes.outerUpper x =
            ((endpointMeasureLocalization E).localizedInterior.piece x).upperCorner) :
    (toSelectedReconstructionEndpointSource E).EndpointSelectedBoxStrictMargins :=
  SelectedBoxStrictMarginData.ofActiveStrictInnerOuter
    (selectedPartition :=
      (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition)
    (targetImages :=
      (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.targetImageInput.targetImages)
    (measureLocalization := endpointMeasureLocalization E)
    boxes innerLower_eq_selectedLower innerUpper_eq_selectedUpper
    outerLower_eq_pieceLower outerUpper_eq_pieceUpper

/--
End-to-end canonical compact-support Stokes from selected chart-box containment
instead of raw strict-margin functions.
-/
theorem canonical_stokes_ofM8ChartAlignmentAndChartBoxStrictContainment
    (A :
      LocalizedInteriorM8ChartAlignment
        (toSelectedReconstructionEndpointSource E).localized)
    (C : NaturalChartBoxStrictContainmentData E) :
    (canonicalIntegralInterface E).stokesStatement :=
  let S := toSelectedReconstructionEndpointSource E
  let L :=
    S.endpointLocalizedPieceStrictMarginsOfSelectedStrictMargins
      (S.endpointSelectedReconstructionBase.localizedPieceAlignmentOfM8ChartAlignment A)
      (endpointSelectedStrictMarginsOfChartBoxStrictContainment E C)
  canonical_stokes_ofM8ChartAlignmentAndLocalizedPieceStrictMargins E A
    L.pieceLower_lt_compactLower L.compactUpper_lt_pieceUpper

/-- Equality form of the chart-box-containment endpoint theorem. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndChartBoxStrictContainment
    (A :
      LocalizedInteriorM8ChartAlignment
        (toSelectedReconstructionEndpointSource E).localized)
    (C : NaturalChartBoxStrictContainmentData E) :
    (canonicalIntegralInterface E).manifoldExtDerivIntegral =
      (canonicalIntegralInterface E).boundaryFormIntegral :=
  by
    simpa [CanonicalIntegralInterface.stokesStatement] using
      canonical_stokes_ofM8ChartAlignmentAndChartBoxStrictContainment E A C

/--
End-to-end canonical compact-support Stokes from active strict inner/outer
boxes and their endpoint corner identifications.
-/
theorem canonical_stokes_ofM8ChartAlignmentAndActiveStrictInnerOuter
    (A :
      LocalizedInteriorM8ChartAlignment
        (toSelectedReconstructionEndpointSource E).localized)
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (boxes :
      ActiveStrictInnerOuterBoxSelections
        (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.active
        coordSupport)
    (innerLower_eq_selectedLower :
      forall x,
        x ∈ (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.active ->
          boxes.innerLower x =
            (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.lower x)
    (innerUpper_eq_selectedUpper :
      forall x,
        x ∈ (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.active ->
          boxes.innerUpper x =
            (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.upper x)
    (outerLower_eq_pieceLower :
      forall x,
        x ∈ (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.active ->
          boxes.outerLower x =
            ((endpointMeasureLocalization E).localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_pieceUpper :
      forall x,
        x ∈ (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.active ->
          boxes.outerUpper x =
            ((endpointMeasureLocalization E).localizedInterior.piece x).upperCorner) :
    (canonicalIntegralInterface E).stokesStatement :=
  let S := toSelectedReconstructionEndpointSource E
  let L :=
    S.endpointLocalizedPieceStrictMarginsOfSelectedStrictMargins
      (S.endpointSelectedReconstructionBase.localizedPieceAlignmentOfM8ChartAlignment A)
      (endpointSelectedStrictMarginsOfActiveStrictInnerOuter E boxes
        innerLower_eq_selectedLower innerUpper_eq_selectedUpper
        outerLower_eq_pieceLower outerUpper_eq_pieceUpper)
  canonical_stokes_ofM8ChartAlignmentAndLocalizedPieceStrictMargins E A
    L.pieceLower_lt_compactLower L.compactUpper_lt_pieceUpper

end NaturalCompactSupportEndpointEndToEndSources

namespace NaturalCompactSupportEndpointNaturalBoundaryMeasureInput

variable {D : NaturalFiniteActiveChartBoxSelectionData I omega rho}
variable
    (E :
      NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu)

/-- Endpoint-facing selected chart-box strict containment for a natural boundary/measure input. -/
abbrev NaturalChartBoxStrictContainmentData :=
  NaturalCompactSupportEndpointEndToEndSources.NaturalChartBoxStrictContainmentData
    E.toEndToEndSources

/--
Natural boundary/measure input route from selected chart-box containment to
endpoint strict margins.
-/
def endpointSelectedStrictMarginsOfChartBoxStrictContainment
    (C : NaturalChartBoxStrictContainmentData E) :
    E.toSelectedReconstructionEndpointSource.EndpointSelectedBoxStrictMargins :=
  NaturalCompactSupportEndpointEndToEndSources.endpointSelectedStrictMarginsOfChartBoxStrictContainment
    E.toEndToEndSources C

/--
Natural boundary/measure input route from active strict inner/outer boxes to
endpoint strict margins.
-/
def endpointSelectedStrictMarginsOfActiveStrictInnerOuter
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (boxes :
      ActiveStrictInnerOuterBoxSelections
        E.toSelectedReconstructionEndpointSource.endpointAutoBase.toBaseInput.selectedPartition.active
        coordSupport)
    (innerLower_eq_selectedLower :
      forall x,
        x ∈ E.toSelectedReconstructionEndpointSource.endpointAutoBase.toBaseInput.selectedPartition.active ->
          boxes.innerLower x =
            E.toSelectedReconstructionEndpointSource.endpointAutoBase.toBaseInput.selectedPartition.lower x)
    (innerUpper_eq_selectedUpper :
      forall x,
        x ∈ E.toSelectedReconstructionEndpointSource.endpointAutoBase.toBaseInput.selectedPartition.active ->
          boxes.innerUpper x =
            E.toSelectedReconstructionEndpointSource.endpointAutoBase.toBaseInput.selectedPartition.upper x)
    (outerLower_eq_pieceLower :
      forall x,
        x ∈ E.toSelectedReconstructionEndpointSource.endpointAutoBase.toBaseInput.selectedPartition.active ->
          boxes.outerLower x =
            (E.toSelectedReconstructionEndpointSource.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_pieceUpper :
      forall x,
        x ∈ E.toSelectedReconstructionEndpointSource.endpointAutoBase.toBaseInput.selectedPartition.active ->
          boxes.outerUpper x =
            (E.toSelectedReconstructionEndpointSource.endpointMeasureLocalization.localizedInterior.piece x).upperCorner) :
    E.toSelectedReconstructionEndpointSource.EndpointSelectedBoxStrictMargins :=
  NaturalCompactSupportEndpointEndToEndSources.endpointSelectedStrictMarginsOfActiveStrictInnerOuter
    E.toEndToEndSources boxes
    innerLower_eq_selectedLower innerUpper_eq_selectedUpper
    outerLower_eq_pieceLower outerUpper_eq_pieceUpper

/-- Natural boundary/measure endpoint theorem from selected chart-box containment. -/
theorem canonical_stokes_ofM8ChartAlignmentAndChartBoxStrictContainment
    (A :
      LocalizedInteriorM8ChartAlignment
        E.toSelectedReconstructionEndpointSource.localized)
    (C : NaturalChartBoxStrictContainmentData E) :
    E.canonicalIntegralInterface.stokesStatement :=
  E.canonical_stokes_ofM8ChartAlignmentAndStrictMargins A
    (E.endpointSelectedStrictMarginsOfChartBoxStrictContainment C)

/-- Equality form of the natural boundary/measure chart-box-containment route. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndChartBoxStrictContainment
    (A :
      LocalizedInteriorM8ChartAlignment
        E.toSelectedReconstructionEndpointSource.localized)
    (C : NaturalChartBoxStrictContainmentData E) :
    E.canonicalIntegralInterface.manifoldExtDerivIntegral =
      E.canonicalIntegralInterface.boundaryFormIntegral :=
  E.manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndStrictMargins A
    (E.endpointSelectedStrictMarginsOfChartBoxStrictContainment C)

end NaturalCompactSupportEndpointNaturalBoundaryMeasureInput

namespace NaturalCompactSupportEndpointNaturalInput

variable
    (N :
      NaturalCompactSupportEndpointNaturalInput
        I omega rho ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu)

/-- Endpoint-facing selected chart-box strict containment for a fully natural endpoint input. -/
abbrev NaturalChartBoxStrictContainmentData :=
  NaturalCompactSupportEndpointNaturalBoundaryMeasureInput.NaturalChartBoxStrictContainmentData
    N.boundaryMeasure

/-- Fully natural endpoint route from selected chart-box containment to strict margins. -/
def endpointSelectedStrictMarginsOfChartBoxStrictContainment
    (C : NaturalChartBoxStrictContainmentData N) :
    N.toSelectedReconstructionEndpointSource.EndpointSelectedBoxStrictMargins :=
  N.boundaryMeasure.endpointSelectedStrictMarginsOfChartBoxStrictContainment C

/-- Fully natural endpoint Stokes from selected chart-box containment. -/
theorem canonical_stokes_ofM8ChartAlignmentAndChartBoxStrictContainment
    (A :
      LocalizedInteriorM8ChartAlignment
        N.toSelectedReconstructionEndpointSource.localized)
    (C : NaturalChartBoxStrictContainmentData N) :
    N.canonicalIntegralInterface.stokesStatement :=
  N.canonical_stokes_ofM8ChartAlignmentAndStrictMargins A
    (N.endpointSelectedStrictMarginsOfChartBoxStrictContainment C)

/-- Equality form of the fully natural chart-box-containment endpoint route. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndChartBoxStrictContainment
    (A :
      LocalizedInteriorM8ChartAlignment
        N.toSelectedReconstructionEndpointSource.localized)
    (C : NaturalChartBoxStrictContainmentData N) :
    N.canonicalIntegralInterface.manifoldExtDerivIntegral =
      N.canonicalIntegralInterface.boundaryFormIntegral :=
  N.manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndStrictMargins A
    (N.endpointSelectedStrictMarginsOfChartBoxStrictContainment C)

end NaturalCompactSupportEndpointNaturalInput

end EndpointSelectedStrictMarginsFromNaturalChartBoxesAuto

end Stokes

end
