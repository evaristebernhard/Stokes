import Stokes.Global.LocalizedPieceStrictMarginsAuto
import Stokes.Global.NaturalCompactSupportEndpointEndToEndAuto

/-!
# Selected strict margins from chart-box containment

The selected-box route ultimately needs two coordinate inequalities around each
selected chart box.  A concrete chart-box selection more naturally produces the
single geometric fact that the selected closed box lies in the strict interior
of the localized M8 piece box.  This file proves the bridge from that
containment to `SelectedBoxStrictMarginData`, and exposes endpoint wrappers
that use the containment directly.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section SelectedStrictMarginsFromChartBoxAuto

universe u w b a ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/--
Chart-box strict containment in the selected-box coordinates.

For each selected active chart, the selected closed box is contained in the
strict open box carried by the localized M8 interior piece.
-/
structure SelectedBoxChartBoxStrictContainmentData
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages) where
  selectedBox_subset_pieceInterior :
    forall x, x ∈ selectedPartition.active ->
      Set.Icc (selectedPartition.lower x) (selectedPartition.upper x) ⊆
        boxInteriorSupportBox
          (measureLocalization.localizedInterior.piece x).lowerCorner
          (measureLocalization.localizedInterior.piece x).upperCorner

namespace SelectedBoxChartBoxStrictContainmentData

/-- Lower selected-box strict margin obtained by evaluating containment at the lower corner. -/
theorem outer_lower_lt_selectedLower
    (D :
      SelectedBoxChartBoxStrictContainmentData selectedPartition targetImages
        measureLocalization) :
    forall x, x ∈ selectedPartition.active -> forall j : Fin (n + 1),
      (measureLocalization.localizedInterior.piece x).lowerCorner j <
        selectedPartition.lower x j := by
  intro x hx j
  have hle := selectedPartition.le hx
  have hmem :
      selectedPartition.lower x ∈
        Set.Icc (selectedPartition.lower x) (selectedPartition.upper x) := by
    exact ⟨le_rfl, hle⟩
  exact (D.selectedBox_subset_pieceInterior x hx hmem j).1

/-- Upper selected-box strict margin obtained by evaluating containment at the upper corner. -/
theorem selectedUpper_lt_outer_upper
    (D :
      SelectedBoxChartBoxStrictContainmentData selectedPartition targetImages
        measureLocalization) :
    forall x, x ∈ selectedPartition.active -> forall j : Fin (n + 1),
      selectedPartition.upper x j <
        (measureLocalization.localizedInterior.piece x).upperCorner j := by
  intro x hx j
  have hle := selectedPartition.le hx
  have hmem :
      selectedPartition.upper x ∈
        Set.Icc (selectedPartition.lower x) (selectedPartition.upper x) := by
    exact ⟨hle, le_rfl⟩
  exact (D.selectedBox_subset_pieceInterior x hx hmem j).2

/-- The chart-box containment package produces the selected strict-margin API. -/
def toSelectedBoxStrictMarginData
    (D :
      SelectedBoxChartBoxStrictContainmentData selectedPartition targetImages
        measureLocalization) :
    SelectedBoxStrictMarginData selectedPartition targetImages
      measureLocalization where
  outer_lower_lt_selectedLower := D.outer_lower_lt_selectedLower
  selectedUpper_lt_outer_upper := D.selectedUpper_lt_outer_upper

/-- Containment can also feed the compact-active localized-piece strict-margin route. -/
def toCompactActiveLocalizedPieceStrictMargins
    (D :
      SelectedBoxChartBoxStrictContainmentData selectedPartition targetImages
        measureLocalization)
    {compactActiveBoxes : CompactActiveBoxData I omega}
    (alignment :
      CompactActiveSelectedPartitionAlignment compactActiveBoxes
        selectedPartition)
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment selectedPartition targetImages
        measureLocalization)
    (compactActive_subset_selected :
      forall x, x ∈ compactActiveBoxes.finiteActive.active ->
        x ∈ selectedPartition.active) :
    CompactActiveLocalizedPieceStrictMargins compactActiveBoxes
      selectedPartition targetImages measureLocalization :=
  D.toSelectedBoxStrictMarginData.toCompactActiveLocalizedPieceStrictMargins
    alignment localizedPieceAlignment compactActive_subset_selected

/-- Containment can feed the single-source strict-buffer constructor route. -/
def toCompactActiveStrictBufferConstructorData
    (D :
      SelectedBoxChartBoxStrictContainmentData selectedPartition targetImages
        measureLocalization)
    {compactActiveBoxes : CompactActiveBoxData I omega}
    (alignment :
      CompactActiveSelectedPartitionAlignment compactActiveBoxes
        selectedPartition)
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment selectedPartition targetImages
        measureLocalization)
    (compactActive_subset_selected :
      forall x, x ∈ compactActiveBoxes.finiteActive.active ->
        x ∈ selectedPartition.active) :
    CompactActiveStrictBufferConstructorData compactActiveBoxes
      selectedPartition targetImages measureLocalization :=
  (D.toCompactActiveLocalizedPieceStrictMargins alignment
    localizedPieceAlignment compactActive_subset_selected).toStrictBufferConstructorData

end SelectedBoxChartBoxStrictContainmentData

namespace SelectedBoxStrictMarginData

/--
The reverse direction: two selected strict margins give the corresponding
selected closed-box containment.
-/
def toSelectedBoxChartBoxStrictContainmentData
    (margins :
      SelectedBoxStrictMarginData selectedPartition targetImages
        measureLocalization) :
    SelectedBoxChartBoxStrictContainmentData selectedPartition targetImages
      measureLocalization where
  selectedBox_subset_pieceInterior := by
    intro x hx
    exact Icc_subset_boxInteriorSupportBox
      (margins.outer_lower_lt_selectedLower x hx)
      (margins.selectedUpper_lt_outer_upper x hx)

end SelectedBoxStrictMarginData

namespace SelectedBoxChartBoxStrictContainmentData

/--
Selected-box containment from an active strict inner/outer source whose inner
boxes are the selected boxes and whose outer boxes are the localized M8 pieces.
-/
def ofActiveStrictInnerOuter
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (strictBoxes :
      ActiveStrictInnerOuterBoxSelections selectedPartition.active
        coordSupport)
    (innerLower_eq_selectedLower :
      forall x, x ∈ selectedPartition.active ->
        strictBoxes.innerLower x = selectedPartition.lower x)
    (innerUpper_eq_selectedUpper :
      forall x, x ∈ selectedPartition.active ->
        strictBoxes.innerUpper x = selectedPartition.upper x)
    (outerLower_eq_pieceLower :
      forall x, x ∈ selectedPartition.active ->
        strictBoxes.outerLower x =
          (measureLocalization.localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_pieceUpper :
      forall x, x ∈ selectedPartition.active ->
        strictBoxes.outerUpper x =
          (measureLocalization.localizedInterior.piece x).upperCorner) :
    SelectedBoxChartBoxStrictContainmentData selectedPartition targetImages
      measureLocalization where
  selectedBox_subset_pieceInterior := by
    intro x hx y hy
    have hy' :
        y ∈ Set.Icc (strictBoxes.innerLower x) (strictBoxes.innerUpper x) := by
      simpa [innerLower_eq_selectedLower x hx,
        innerUpper_eq_selectedUpper x hx] using hy
    have h := strictBoxes.innerIcc_subset_outerInterior x hx hy'
    simpa [outerLower_eq_pieceLower x hx,
      outerUpper_eq_pieceUpper x hx] using h

/--
Selected-box containment from localized-piece outer-box data by rewriting the
selected box to the compact-active box.
-/
def ofCompactActiveLocalizedPieceOuterBoxData
    {compactActiveBoxes : CompactActiveBoxData I omega}
    (D :
      CompactActiveLocalizedPieceOuterBoxData compactActiveBoxes
        selectedPartition targetImages measureLocalization) :
    SelectedBoxChartBoxStrictContainmentData selectedPartition targetImages
      measureLocalization where
  selectedBox_subset_pieceInterior := by
    intro x hx y hy
    have hy' :
        y ∈ Set.Icc (compactActiveBoxes.lower x)
          (compactActiveBoxes.upper x) := by
      simpa [(D.selectedPartitionAlignment).lower_eq,
        (D.selectedPartitionAlignment).upper_eq] using hy
    exact D.compactBox_subset_pieceInterior x hx hy'

end SelectedBoxChartBoxStrictContainmentData

namespace CompactActiveLocalizedPieceOuterBoxData

variable {compactActiveBoxes : CompactActiveBoxData I omega}

/-- Localized-piece outer boxes expose selected chart-box containment. -/
def toSelectedBoxChartBoxStrictContainmentData
    (D :
      CompactActiveLocalizedPieceOuterBoxData compactActiveBoxes
        selectedPartition targetImages measureLocalization) :
    SelectedBoxChartBoxStrictContainmentData selectedPartition targetImages
      measureLocalization :=
  SelectedBoxChartBoxStrictContainmentData.ofCompactActiveLocalizedPieceOuterBoxData D

end CompactActiveLocalizedPieceOuterBoxData

section SelectedBoxEndToEnd

variable {alpha : Type a} [TopologicalSpace alpha] [MeasurableSpace alpha]
variable [OpensMeasurableSpace alpha] [T2Space alpha]
variable {muAlpha : Measure alpha} [IsFiniteMeasureOnCompacts muAlpha]
variable {rho : SmoothPartitionOfUnity M I M univ}
variable {K : Set M} {hK : IsCompact K}

/--
Selected-box end-to-end data with strict margins supplied as chart-box
containment rather than as two coordinate inequalities.
-/
structure CompactSupportSelectedBoxChartBoxEndToEndData
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (rho : SmoothPartitionOfUnity M I M univ)
    (K : Set M) (hK : IsCompact K)
    (muAlpha : Measure alpha) [IsFiniteMeasureOnCompacts muAlpha] where
  formData : CompactlySupportedSmoothFormData I omega
  supportSet_eq : K = formData.supportSet
  selection : CompactSupportFiniteActiveSelection (I := I) rho K hK omega
  smoothness :
    ActiveCompactBoxSmoothness selection.finiteActive selection.supportData.box omega
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  targetImageInput :
    M8TargetImageInput I omega
      (selection.selectedBoxPartitionOfUnity smoothness)
      orientedBoundaryAtlas BoundaryPiece
  globalBulkIntegral : Real
  bulk :
    BulkMeasureFromPartitionData
      (α := alpha) (μ := muAlpha)
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages globalBulkIntegral
  boundaryTarget :
    CanonicalBoundaryTargetCompactSupportInput
      (α := alpha) targetImageInput muAlpha
  localizedChartAlignment :
    LocalizedInteriorM8ChartAlignment bulk.localized
  chartBoxContainment :
    SelectedBoxChartBoxStrictContainmentData
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages
      (boundaryTarget.toMeasureBuilderData bulk).toM8MeasureLocalizationData

namespace CompactSupportSelectedBoxChartBoxEndToEndData

variable
    (D :
      CompactSupportSelectedBoxChartBoxEndToEndData
        I omega BoundaryPiece rho K hK muAlpha)

/-- The selected strict-margin package generated from chart-box containment. -/
def strictMargins :
    SelectedBoxStrictMarginData
      (D.selection.selectedBoxPartitionOfUnity D.smoothness)
      D.targetImageInput.targetImages
      (D.boundaryTarget.toMeasureBuilderData D.bulk).toM8MeasureLocalizationData :=
  D.chartBoxContainment.toSelectedBoxStrictMarginData

/-- Forget chart-box containment to the existing selected-box end-to-end input. -/
def toCompactSupportSelectedBoxEndToEndData :
    CompactSupportSelectedBoxEndToEndData
      (α := alpha) (μ := muAlpha) I omega BoundaryPiece rho K hK where
  formData := D.formData
  supportSet_eq := D.supportSet_eq
  selection := D.selection
  smoothness := D.smoothness
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  targetImageInput := D.targetImageInput
  globalBulkIntegral := D.globalBulkIntegral
  bulk := D.bulk
  boundaryTarget := D.boundaryTarget
  localizedChartAlignment := D.localizedChartAlignment
  strictMargins := D.strictMargins

/-- The chart-containment end-to-end package gives canonical compact-support Stokes. -/
theorem canonical_stokes [IsManifold I 1 M] :
    D.toCompactSupportSelectedBoxEndToEndData
      |>.toNaturalCompactSupportEndToEndInput
      |>.toNaturalCompactSupportStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement :=
  D.toCompactSupportSelectedBoxEndToEndData.canonical_stokes

end CompactSupportSelectedBoxChartBoxEndToEndData

end SelectedBoxEndToEnd

section EndpointSources

variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]

namespace NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources

variable
    (S :
      NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu)

/-- Endpoint-facing selected chart-box containment. -/
abbrev EndpointSelectedBoxChartBoxStrictContainmentData :=
  SelectedBoxChartBoxStrictContainmentData
    S.endpointAutoBase.toBaseInput.selectedPartition
    S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
    S.endpointMeasureLocalization

/-- Endpoint strict margins generated from selected chart-box containment. -/
def endpointSelectedBoxStrictMarginsOfChartBoxStrictContainment
    (D : S.EndpointSelectedBoxChartBoxStrictContainmentData) :
    S.EndpointSelectedBoxStrictMargins :=
  D.toSelectedBoxStrictMarginData

/-- Endpoint strict-buffer constructor generated from selected chart-box containment. -/
def endpointStrictBufferConstructorDataOfChartBoxStrictContainment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointSelectedBoxChartBoxStrictContainmentData) :
    CompactActiveStrictBufferConstructorData S.selection.compactActiveBoxData
      S.endpointAutoBase.toBaseInput.selectedPartition
      S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
      S.endpointMeasureLocalization :=
  S.endpointStrictBufferConstructorDataOfSelectedStrictMargins
    (S.endpointSelectedReconstructionBase.localizedPieceAlignmentOfM8ChartAlignment A)
    (S.endpointSelectedBoxStrictMarginsOfChartBoxStrictContainment D)

/--
Selected/compact endpoint sources from constructor chart-label alignment and
selected chart-box containment.
-/
def toSelectedCompactSourcesOfM8ChartAlignmentAndChartBoxStrictContainment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointSelectedBoxChartBoxStrictContainmentData) :
    NaturalCompactSupportEndpointSelectedCompactSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  S.toSelectedCompactSourcesOfM8ChartAlignmentAndStrictMargins A
    (S.endpointSelectedBoxStrictMarginsOfChartBoxStrictContainment D)

/-- Endpoint Stokes from constructor chart-label alignment and selected chart-box containment. -/
theorem stokes_ofM8ChartAlignmentAndChartBoxStrictContainment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointSelectedBoxChartBoxStrictContainmentData) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.stokes_ofM8ChartAlignmentAndStrictMargins A
    (S.endpointSelectedBoxStrictMarginsOfChartBoxStrictContainment D)

/-- Endpoint Stokes in canonical theorem-facing form from selected chart-box containment. -/
theorem canonical_stokes_ofM8ChartAlignmentAndChartBoxStrictContainment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointSelectedBoxChartBoxStrictContainmentData) :
    S.canonicalIntegralInterface.stokesStatement := by
  simpa [CanonicalIntegralInterface.stokesStatement,
    NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources.canonicalIntegralInterface]
    using S.stokes_ofM8ChartAlignmentAndChartBoxStrictContainment A D

/--
Endpoint canonical equality from constructor chart-label alignment and selected
chart-box containment.
-/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndChartBoxStrictContainment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointSelectedBoxChartBoxStrictContainmentData) :
    S.canonicalIntegralInterface.manifoldExtDerivIntegral =
      S.canonicalIntegralInterface.boundaryFormIntegral := by
  simpa [CanonicalIntegralInterface.stokesStatement] using
    S.canonical_stokes_ofM8ChartAlignmentAndChartBoxStrictContainment A D

end NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources

namespace NaturalCompactSupportEndpointExtDerivBaseSources

variable
    (S :
      NaturalCompactSupportEndpointExtDerivBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu)

/-- Ext-deriv endpoint-facing selected chart-box containment. -/
abbrev EndpointSelectedBoxChartBoxStrictContainmentData :=
  S.compactSupportEndpointSource.EndpointSelectedBoxChartBoxStrictContainmentData

/-- Ext-deriv endpoint Stokes from selected chart-box containment. -/
theorem stokes_ofM8ChartAlignmentAndChartBoxStrictContainment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointSelectedBoxChartBoxStrictContainmentData) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.compactSupportEndpointSource
    |>.stokes_ofM8ChartAlignmentAndChartBoxStrictContainment A D

/-- Ext-deriv endpoint Stokes in canonical theorem-facing form. -/
theorem canonical_stokes_ofM8ChartAlignmentAndChartBoxStrictContainment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointSelectedBoxChartBoxStrictContainmentData) :
    S.canonicalIntegralInterface.stokesStatement := by
  simpa [CanonicalIntegralInterface.stokesStatement,
    NaturalCompactSupportEndpointExtDerivBaseSources.canonicalIntegralInterface]
    using S.stokes_ofM8ChartAlignmentAndChartBoxStrictContainment A D

/-- Ext-deriv endpoint canonical equality from selected chart-box containment. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndChartBoxStrictContainment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointSelectedBoxChartBoxStrictContainmentData) :
    S.canonicalIntegralInterface.manifoldExtDerivIntegral =
      S.canonicalIntegralInterface.boundaryFormIntegral := by
  simpa [CanonicalIntegralInterface.stokesStatement] using
    S.canonical_stokes_ofM8ChartAlignmentAndChartBoxStrictContainment A D

end NaturalCompactSupportEndpointExtDerivBaseSources

end EndpointSources

end SelectedStrictMarginsFromChartBoxAuto

end Stokes

end
