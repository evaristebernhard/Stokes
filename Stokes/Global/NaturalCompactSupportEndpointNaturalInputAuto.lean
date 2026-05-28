import Stokes.Global.NaturalFiniteActiveChartBoxSelectionAuto
import Stokes.Global.NaturalCompactSupportEndpointEndToEndAuto
import Stokes.Global.LocalizedPieceStrictMarginsAuto
import Stokes.Global.CanonicalCompactSupportEndpointFacade

/-!
# Natural compact-support endpoint inputs

This module pushes the compact-support endpoint theorem one layer closer to
the inputs a caller naturally has after choosing finite active chart boxes.

The entry point is `NaturalFiniteActiveChartBoxSelectionData`, which already
packages a compactly supported smooth form, finite active selected chart boxes,
and the chart-box smoothness neighborhoods.  The remaining endpoint data is
kept in a small boundary/measure record.  Strict margins are accepted in the
selected-box shape and are converted to the localized-piece margins consumed by
the existing canonical endpoint theorem.

There is no separate `NaturalStrictAlignmentFromFiniteSelectionAuto` module in
the current tree, so the genuine strict-margin construction remains an explicit
field at this layer.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportEndpointNaturalInputAuto

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

/--
The endpoint-side data left after the natural finite-active chart-box
selection has produced the selected partition and support bookkeeping.
-/
structure NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
    (D : NaturalFiniteActiveChartBoxSelectionData I omega rho)
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (BoundaryPiece : Type b)
    (mu : Measure (Fin (n + 1) -> Real))
    [IsFiniteMeasureOnCompacts mu]
    [IsManifold I 1 M] where
  /-- Oriented boundary-chart atlas used by the canonical boundary route. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Unified boundary source-shrink/project-local package. -/
  boundaryUnified :
    BoundarySourceAlignmentUnifiedData
      (I := I) (omega := omega)
      (selectedPartition := D.selectedPartition)
      (orientedBoundaryAtlas := orientedBoundaryAtlas)
      (BoundaryPiece := BoundaryPiece)
  /-- Localized interior pieces for the selected partition. -/
  localized : LocalizedInteriorM8Fields I omega D.selectedPartition
  /-- Selected reconstruction source, including active-set compatibility. -/
  reconstructionSource :
    SelectedPartitionReconstructionSource I omega D.selectedPartition
      boundaryUnified.toM8TargetImageInput.targetImages
      ExtInteriorPiece ExtBoundaryPiece
  /-- Chartwise measure used by the bulk a.e. comparison. -/
  extDerivMeasure : M -> M -> Measure (Fin (n + 1) -> Real)
  /-- Canonical local bulk facts for the selected interior pieces. -/
  bulkLocalFacts :
    SelectedPartitionBulkCanonicalLocalFacts D.selectedPartition
      boundaryUnified.toM8TargetImageInput.targetImages localized
  /-- The selected bulk measure is the ambient volume measure. -/
  measure_eq_volume : mu = volume
  /-- Lower-face continuity for the canonical boundary route. -/
  boundaryFaceContinuity :
    ProjectLocalBoundaryCanonicalFaceContinuityData
      boundaryUnified.toProjectLocalGlobalStokesData
  /-- Selected-target chart-change data for the canonical boundary route. -/
  boundaryChartChange :
    BoundaryChartChangeSelectedFamilyData
      boundaryUnified.toProjectLocalGlobalStokesData

namespace NaturalCompactSupportEndpointNaturalBoundaryMeasureInput

variable {D : NaturalFiniteActiveChartBoxSelectionData I omega rho}

/-- Forget the natural chart-box input to the existing end-to-end source shape. -/
def toEndToEndSources
    (E :
      NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu) :
    NaturalCompactSupportEndpointEndToEndSources
      (I := I) (omega := omega) (rho := rho)
      D.toPartitionConstructorData
      ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu where
  orientedBoundaryAtlas := E.orientedBoundaryAtlas
  boundaryUnified := E.boundaryUnified
  localized := E.localized
  reconstructionSource := E.reconstructionSource
  extDerivMeasure := E.extDerivMeasure
  bulkLocalFacts := E.bulkLocalFacts
  measure_eq_volume := E.measure_eq_volume
  boundaryFaceContinuity := E.boundaryFaceContinuity
  boundaryChartChange := E.boundaryChartChange

@[simp]
theorem toEndToEndSources_orientedBoundaryAtlas
    (E :
      NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu) :
    E.toEndToEndSources.orientedBoundaryAtlas =
      E.orientedBoundaryAtlas := by
  rfl

@[simp]
theorem toEndToEndSources_localized
    (E :
      NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu) :
    E.toEndToEndSources.localized =
      E.localized := by
  rfl

/-- The source-packaged endpoint generated from the natural input. -/
abbrev toSelectedReconstructionEndpointSource
    (E :
      NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu) :
    NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  E.toEndToEndSources.toSelectedReconstructionEndpointSource

/-- Canonical integral interface exposed by the generated endpoint. -/
abbrev canonicalIntegralInterface
    (E :
      NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu) :
    CanonicalIntegralInterface I omega :=
  E.toEndToEndSources.canonicalIntegralInterface

/--
Selected-box strict margins converted to the compact-active localized-piece
strict-margin package used by the strict-buffer route.
-/
def localizedPieceStrictMarginsOfSelectedMargins
    (E :
      NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu)
    (A :
      LocalizedInteriorM8ChartAlignment
        E.toSelectedReconstructionEndpointSource.localized)
    (margins :
      E.toSelectedReconstructionEndpointSource.EndpointSelectedBoxStrictMargins) :
    CompactActiveLocalizedPieceStrictMargins
      E.toSelectedReconstructionEndpointSource.selection.compactActiveBoxData
      E.toSelectedReconstructionEndpointSource.endpointAutoBase.toBaseInput.selectedPartition
      E.toSelectedReconstructionEndpointSource.endpointAutoBase.toBaseInput.targetImageInput.targetImages
      E.toSelectedReconstructionEndpointSource.endpointMeasureLocalization :=
  E.toSelectedReconstructionEndpointSource
    |>.endpointLocalizedPieceStrictMarginsOfSelectedStrictMargins
      (E.toSelectedReconstructionEndpointSource.endpointSelectedReconstructionBase
        |>.localizedPieceAlignmentOfM8ChartAlignment A)
      margins

/--
Canonical compact-support Stokes from natural chart-box input, boundary/measure
input, constructor chart alignment, and selected-box strict margins.
-/
theorem canonical_stokes_ofM8ChartAlignmentAndStrictMargins
    (E :
      NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu)
    (A :
      LocalizedInteriorM8ChartAlignment
        E.toSelectedReconstructionEndpointSource.localized)
    (margins :
      E.toSelectedReconstructionEndpointSource.EndpointSelectedBoxStrictMargins) :
    E.canonicalIntegralInterface.stokesStatement := by
  let L := E.localizedPieceStrictMarginsOfSelectedMargins A margins
  simpa [canonicalIntegralInterface, toSelectedReconstructionEndpointSource] using
    E.toSelectedReconstructionEndpointSource
      |>.canonical_stokes_ofM8ChartAlignmentAndLocalizedPieceStrictMargins A
        L.pieceLower_lt_compactLower L.compactUpper_lt_pieceUpper

/-- The same theorem displayed as the canonical equality. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndStrictMargins
    (E :
      NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu)
    (A :
      LocalizedInteriorM8ChartAlignment
        E.toSelectedReconstructionEndpointSource.localized)
    (margins :
      E.toSelectedReconstructionEndpointSource.EndpointSelectedBoxStrictMargins) :
    E.canonicalIntegralInterface.manifoldExtDerivIntegral =
      E.canonicalIntegralInterface.boundaryFormIntegral := by
  simpa [CanonicalIntegralInterface.stokesStatement] using
    E.canonical_stokes_ofM8ChartAlignmentAndStrictMargins A margins

end NaturalCompactSupportEndpointNaturalBoundaryMeasureInput

/--
Fully packaged natural compact-support endpoint input.

`chartBoxes` is built from the compactly supported smooth form plus finite
active chart-box choices.  `boundaryMeasure` contains the remaining canonical
boundary and measure packages over the selected partition generated by those
chart boxes.
-/
structure NaturalCompactSupportEndpointNaturalInput
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (rho : SmoothPartitionOfUnity M I M univ)
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (BoundaryPiece : Type b)
    (mu : Measure (Fin (n + 1) -> Real))
    [IsFiniteMeasureOnCompacts mu]
    [IsManifold I 1 M] where
  /-- Compactly supported form, finite active chart boxes, and smoothness neighborhoods. -/
  chartBoxes : NaturalFiniteActiveChartBoxSelectionData I omega rho
  /-- Boundary and measure data over the selected partition generated by `chartBoxes`. -/
  boundaryMeasure :
    NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
      (I := I) (omega := omega) (rho := rho)
      chartBoxes ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu

namespace NaturalCompactSupportEndpointNaturalInput

variable
    (N :
      NaturalCompactSupportEndpointNaturalInput
        I omega rho ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu)

/-- The selected partition constructor generated by the finite-active chart boxes. -/
abbrev toPartitionConstructorData :
    NaturalCompactSupportPartitionConstructorData I omega rho :=
  N.chartBoxes.toPartitionConstructorData

/-- The end-to-end endpoint source generated by the natural input. -/
abbrev toEndToEndSources :
    NaturalCompactSupportEndpointEndToEndSources
      (I := I) (omega := omega) (rho := rho)
      N.toPartitionConstructorData
      ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu :=
  N.boundaryMeasure.toEndToEndSources

/-- The source-packaged endpoint generated by the natural input. -/
abbrev toSelectedReconstructionEndpointSource :
    NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  N.boundaryMeasure.toSelectedReconstructionEndpointSource

/-- Canonical integral interface exposed by the natural endpoint. -/
abbrev canonicalIntegralInterface :
    CanonicalIntegralInterface I omega :=
  N.boundaryMeasure.canonicalIntegralInterface

/--
Natural endpoint theorem from constructor chart alignment and selected-box
strict margins.
-/
theorem canonical_stokes_ofM8ChartAlignmentAndStrictMargins
    (A :
      LocalizedInteriorM8ChartAlignment
        N.toSelectedReconstructionEndpointSource.localized)
    (margins :
      N.toSelectedReconstructionEndpointSource.EndpointSelectedBoxStrictMargins) :
    N.canonicalIntegralInterface.stokesStatement :=
  N.boundaryMeasure
    |>.canonical_stokes_ofM8ChartAlignmentAndStrictMargins A margins

/-- Natural endpoint theorem displayed as the canonical equality. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndStrictMargins
    (A :
      LocalizedInteriorM8ChartAlignment
        N.toSelectedReconstructionEndpointSource.localized)
    (margins :
      N.toSelectedReconstructionEndpointSource.EndpointSelectedBoxStrictMargins) :
    N.canonicalIntegralInterface.manifoldExtDerivIntegral =
      N.canonicalIntegralInterface.boundaryFormIntegral :=
  N.boundaryMeasure
    |>.manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndStrictMargins
      A margins

end NaturalCompactSupportEndpointNaturalInput

end NaturalCompactSupportEndpointNaturalInputAuto

end Stokes

end
