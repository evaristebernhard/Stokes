import Stokes.Global.NaturalCompactSupportEndpointFacade
import Stokes.Global.SelectedReconstructionSourceConstructorsAuto
import Stokes.Global.NaturalCompactSupportEndpointMarginConstructorsAuto
import Stokes.Global.EndpointLocalizedOuterBoxFromCompactSelectionAuto
import Stokes.Global.CompactActiveStrictBufferConstructorAuto

/-!
# Public compact-support endpoint facade

This module is the stable caller-facing entry point for the current
compact-support endpoint route.  It keeps the older small constructor modules
in place, but hides the intermediate
`NaturalCompactSupportEndpointSelectedReconstructionBaseSources` and
`NaturalCompactSupportEndpointSelectedCompactSources` records from theorem
callers.

The preferred inputs are now:

* a source-packaged reconstruction endpoint source, or an older ext-deriv
  endpoint source that can generate one;
* constructor chart-label alignment with the M8 localized interior fields;
* localized outer-box containment, or a named compact-active outer-box package.
  A compact-active strict-buffer alignment can also be used directly.
  Constructor data for that strict-buffer alignment can be used directly too.

No new analytic statement is proved here.  The facade only composes existing
constructor routes into shorter public declarations.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportEndpointFacade

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

/-- Public name for compact-support endpoint data with a packaged selected
reconstruction source. -/
abbrev CompactSupportEndpointSource
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (rho : SmoothPartitionOfUnity M I M univ)
    (mu : Measure (Fin (n + 1) -> Real))
    [IsFiniteMeasureOnCompacts mu]
    [IsManifold I 1 M] :=
  NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources
    ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu

/-- Public name for the older ext-deriv endpoint source, which can generate a
packaged selected reconstruction source. -/
abbrev CompactSupportEndpointExtDerivSource
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (rho : SmoothPartitionOfUnity M I M univ)
    (mu : Measure (Fin (n + 1) -> Real))
    [IsFiniteMeasureOnCompacts mu]
    [IsManifold I 1 M] :=
  NaturalCompactSupportEndpointExtDerivBaseSources
    ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu

namespace NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources

variable
    (S :
      NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu)

/-- Localized outer-box data in the public source-packaged endpoint shape. -/
abbrev EndpointCompactActiveLocalizedOuterBoxData :=
  S.endpointSelectedReconstructionBase.EndpointCompactActiveLocalizedOuterBoxData

/-- Named compact-active outer-box data in the public source-packaged endpoint
shape. -/
abbrev EndpointCompactActiveOuterBoxData :=
  S.endpointSelectedReconstructionBase.EndpointCompactActiveOuterBoxData

/-- Strict endpoint margins generated from localized outer-box containment. -/
def endpointSelectedBoxStrictMarginsOfLocalizedOuterBox
    (D : S.EndpointCompactActiveLocalizedOuterBoxData) :
    S.EndpointSelectedBoxStrictMargins :=
  S.endpointSelectedReconstructionBase.endpointSelectedBoxStrictMarginsOfLocalizedOuterBox D

/-- Strict endpoint margins generated from named compact-active outer boxes. -/
def endpointSelectedBoxStrictMarginsOfOuterBox
    (D : S.EndpointCompactActiveOuterBoxData) :
    S.EndpointSelectedBoxStrictMargins :=
  S.endpointSelectedReconstructionBase.endpointSelectedBoxStrictMarginsOfOuterBox D

/-- Selected/compact endpoint source assembled from the public facade inputs:
source-packaged reconstruction, M8 chart alignment, and localized outer-box
containment. -/
def toSelectedCompactSourcesOfM8ChartAlignmentAndLocalizedOuterBox
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointCompactActiveLocalizedOuterBoxData) :
    NaturalCompactSupportEndpointSelectedCompactSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  S.toSelectedCompactSourcesOfM8ChartAlignmentAndStrictMargins A
    (S.endpointSelectedBoxStrictMarginsOfLocalizedOuterBox D)

@[simp]
theorem toSelectedCompactSourcesOfM8ChartAlignmentAndLocalizedOuterBox_base
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointCompactActiveLocalizedOuterBoxData) :
    (S.toSelectedCompactSourcesOfM8ChartAlignmentAndLocalizedOuterBox A D).base =
      S.endpointSelectedReconstructionBase := by
  rfl

/-- Endpoint Stokes from the public facade inputs and localized outer-box
containment. -/
theorem stokes_ofM8ChartAlignmentAndLocalizedOuterBox
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointCompactActiveLocalizedOuterBoxData) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.stokes_ofM8ChartAlignmentAndStrictMargins A
    (S.endpointSelectedBoxStrictMarginsOfLocalizedOuterBox D)

/-- Endpoint Stokes from the public facade inputs and a compact-active
strict-buffer alignment over the selected compact boxes. -/
theorem stokes_ofM8ChartAlignmentAndCompactActiveStrictBufferAlignment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (alignment :
      CompactActiveBoxStrictBufferAlignment S.selection.compactActiveBoxData
        S.endpointAutoBase.toBaseInput.selectedPartition
        S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.endpointSelectedReconstructionBase
    |>.stokes_ofM8ChartAlignmentAndCompactActiveStrictBufferAlignment A alignment

/-- Endpoint Stokes from single-source compact-active strict-buffer constructor
data.  This is the preferred endpoint-facing form once the selected compact
box, selected partition, and localized outer box have been aligned. -/
theorem stokes_ofM8ChartAlignmentAndStrictBufferConstructorData
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (constructorData :
      CompactActiveStrictBufferConstructorData S.selection.compactActiveBoxData
        S.endpointAutoBase.toBaseInput.selectedPartition
        S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.stokes_ofM8ChartAlignmentAndCompactActiveStrictBufferAlignment A
    constructorData.toCompactActiveBoxStrictBufferAlignment

/-- Endpoint Stokes from the public facade inputs and named compact-active
outer-box data. -/
theorem stokes_ofM8ChartAlignmentAndOuterBox
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointCompactActiveOuterBoxData) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.stokes_ofM8ChartAlignmentAndStrictMargins A
    (S.endpointSelectedBoxStrictMarginsOfOuterBox D)

/-- Strict endpoint margins generated from a compact-active strict inner/outer
selection.  This is a compatibility route for callers whose box constructor
still produces an `ActiveStrictInnerOuterBoxSelections` package. -/
def endpointSelectedBoxStrictMarginsOfCompactActiveStrictInnerOuter
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (D :
      ActiveStrictInnerOuterBoxSelections
        S.selection.compactActiveBoxData.finiteActive.active coordSupport)
    (innerLower_eq_compactLower :
      forall x, x ∈ S.selection.compactActiveBoxData.finiteActive.active ->
        D.innerLower x = S.selection.compactActiveBoxData.lower x)
    (innerUpper_eq_compactUpper :
      forall x, x ∈ S.selection.compactActiveBoxData.finiteActive.active ->
        D.innerUpper x = S.selection.compactActiveBoxData.upper x)
    (outerLower_eq_endpointPieceLower :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        D.outerLower x =
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_endpointPieceUpper :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        D.outerUpper x =
          (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner) :
    S.EndpointSelectedBoxStrictMargins :=
  S.endpointSelectedReconstructionBase
    |>.endpointSelectedBoxStrictMarginsOfCompactActiveStrictInnerOuter D
      innerLower_eq_compactLower innerUpper_eq_compactUpper
      outerLower_eq_endpointPieceLower outerUpper_eq_endpointPieceUpper

/-- Endpoint Stokes from a compact-active strict inner/outer box selection. -/
theorem stokes_ofM8ChartAlignmentAndCompactActiveStrictInnerOuter
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (D :
      ActiveStrictInnerOuterBoxSelections
        S.selection.compactActiveBoxData.finiteActive.active coordSupport)
    (innerLower_eq_compactLower :
      forall x, x ∈ S.selection.compactActiveBoxData.finiteActive.active ->
        D.innerLower x = S.selection.compactActiveBoxData.lower x)
    (innerUpper_eq_compactUpper :
      forall x, x ∈ S.selection.compactActiveBoxData.finiteActive.active ->
        D.innerUpper x = S.selection.compactActiveBoxData.upper x)
    (outerLower_eq_endpointPieceLower :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        D.outerLower x =
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_endpointPieceUpper :
      forall x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        D.outerUpper x =
          (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.stokes_ofM8ChartAlignmentAndStrictMargins A
    (S.endpointSelectedBoxStrictMarginsOfCompactActiveStrictInnerOuter D
      innerLower_eq_compactLower innerUpper_eq_compactUpper
      outerLower_eq_endpointPieceLower outerUpper_eq_endpointPieceUpper)

end NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources

namespace NaturalCompactSupportEndpointExtDerivBaseSources

variable
    (S :
      NaturalCompactSupportEndpointExtDerivBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu)

/-- The source-packaged endpoint facade generated from an ext-deriv endpoint
source. -/
abbrev compactSupportEndpointSource :
    NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  S.toSelectedReconstructionSourceBaseSources

/-- Localized outer-box data after converting an ext-deriv endpoint source to
the public source-packaged facade. -/
abbrev EndpointCompactActiveLocalizedOuterBoxData :=
  S.compactSupportEndpointSource.EndpointCompactActiveLocalizedOuterBoxData

/-- Named compact-active outer-box data after converting an ext-deriv endpoint
source to the public source-packaged facade. -/
abbrev EndpointCompactActiveOuterBoxData :=
  S.compactSupportEndpointSource.EndpointCompactActiveOuterBoxData

/-- The endpoint measure-localization data used by the public ext-deriv facade. -/
abbrev endpointMeasureLocalization :
    M8MeasureLocalizationData I omega
      S.compactSupportEndpointSource.endpointAutoBase.toBaseInput.selectedPartition
      S.compactSupportEndpointSource.endpointAutoBase.toBaseInput.targetImageInput.targetImages :=
  S.compactSupportEndpointSource.endpointMeasureLocalization

/-- Endpoint Stokes from an ext-deriv source, M8 chart alignment, and localized
outer-box containment. -/
theorem stokes_ofM8ChartAlignmentAndLocalizedOuterBox
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointCompactActiveLocalizedOuterBoxData) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.compactSupportEndpointSource.stokes_ofM8ChartAlignmentAndLocalizedOuterBox A D

/-- Endpoint Stokes from an ext-deriv source, M8 chart alignment, and a
compact-active strict-buffer alignment over the selected compact boxes. -/
theorem stokes_ofM8ChartAlignmentAndCompactActiveStrictBufferAlignment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (alignment :
      CompactActiveBoxStrictBufferAlignment S.selection.compactActiveBoxData
        S.compactSupportEndpointSource.endpointAutoBase.toBaseInput.selectedPartition
        S.compactSupportEndpointSource.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.compactSupportEndpointSource
    |>.stokes_ofM8ChartAlignmentAndCompactActiveStrictBufferAlignment A alignment

/-- Ext-deriv endpoint Stokes from single-source compact-active strict-buffer
constructor data. -/
theorem stokes_ofM8ChartAlignmentAndStrictBufferConstructorData
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (constructorData :
      CompactActiveStrictBufferConstructorData S.selection.compactActiveBoxData
        S.compactSupportEndpointSource.endpointAutoBase.toBaseInput.selectedPartition
        S.compactSupportEndpointSource.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.stokes_ofM8ChartAlignmentAndCompactActiveStrictBufferAlignment A
    constructorData.toCompactActiveBoxStrictBufferAlignment

/-- Endpoint Stokes from an ext-deriv source, M8 chart alignment, and named
compact-active outer-box data. -/
theorem stokes_ofM8ChartAlignmentAndOuterBox
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointCompactActiveOuterBoxData) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.compactSupportEndpointSource.stokes_ofM8ChartAlignmentAndOuterBox A D

/-- Endpoint Stokes from an ext-deriv source and a compact-active strict
inner/outer box selection. -/
theorem stokes_ofM8ChartAlignmentAndCompactActiveStrictInnerOuter
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (D :
      ActiveStrictInnerOuterBoxSelections
        S.selection.compactActiveBoxData.finiteActive.active coordSupport)
    (innerLower_eq_compactLower :
      forall x, x ∈ S.selection.compactActiveBoxData.finiteActive.active ->
        D.innerLower x = S.selection.compactActiveBoxData.lower x)
    (innerUpper_eq_compactUpper :
      forall x, x ∈ S.selection.compactActiveBoxData.finiteActive.active ->
        D.innerUpper x = S.selection.compactActiveBoxData.upper x)
    (outerLower_eq_endpointPieceLower :
      forall x,
        x ∈ S.compactSupportEndpointSource.endpointAutoBase.toBaseInput.selectedPartition.active ->
        D.outerLower x =
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_endpointPieceUpper :
      forall x,
        x ∈ S.compactSupportEndpointSource.endpointAutoBase.toBaseInput.selectedPartition.active ->
        D.outerUpper x =
          (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.compactSupportEndpointSource
    |>.stokes_ofM8ChartAlignmentAndCompactActiveStrictInnerOuter A D
      innerLower_eq_compactLower innerUpper_eq_compactUpper
      outerLower_eq_endpointPieceLower outerUpper_eq_endpointPieceUpper

end NaturalCompactSupportEndpointExtDerivBaseSources

end CompactSupportEndpointFacade

end Stokes

end
