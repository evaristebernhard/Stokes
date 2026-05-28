import Stokes.Global.NaturalCompactSupportEndpointMarginConstructorsAuto

/-!
# Endpoint localized outer boxes from compact-selection data

`NaturalCompactSupportEndpointMarginConstructorsAuto` introduced
`EndpointCompactActiveLocalizedOuterBoxData`: the constructor-facing geometric
fact that each selected compact active closed box lies inside the endpoint
localized outer box.

This file connects that record back to the already existing strict-buffer and
selected compact-support routes.  The useful direction is the strict-buffer
constructor: once the compact active boxes are the inner boxes of a
`CompactActiveBoxStrictBufferAlignment`, the desired closed-box containment is
just `Icc_subset_boxInteriorSupportBox`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section EndpointLocalizedOuterBoxFromCompactSelectionAuto

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

namespace EndpointCompactActiveLocalizedOuterBoxData

variable {S}

/--
Build endpoint localized-outer-box containment from the packaged endpoint
selected-box strict margins.

This is the reverse projection of the margin facts: a point in the selected
compact closed box is coordinatewise between the selected lower/upper corners,
so the strict lower/upper margin places it in the outer open box.
-/
def ofEndpointSelectedBoxStrictMargins
    (margins : S.EndpointSelectedBoxStrictMargins) :
    S.EndpointCompactActiveLocalizedOuterBoxData where
  compactBox_subset_endpointInterior := by
    intro x hxD
    have hx :
        x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active := by
      simpa [NaturalCompactSupportEndpointSelectedReconstructionBaseSources.endpointAutoBase]
        using hxD
    have hleft :
        ∀ j : Fin (n + 1),
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner j <
            S.selection.compactActiveBoxData.lower x j := by
      intro j
      simpa [NaturalCompactSupportEndpointSelectedReconstructionBaseSources.endpointAutoBase]
        using margins.outer_lower_lt_selectedLower x hx j
    have hright :
        ∀ j : Fin (n + 1),
          S.selection.compactActiveBoxData.upper x j <
            (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner j := by
      intro j
      simpa [NaturalCompactSupportEndpointSelectedReconstructionBaseSources.endpointAutoBase]
        using margins.selectedUpper_lt_outer_upper x hx j
    exact Icc_subset_boxInteriorSupportBox hleft hright

/--
Build endpoint localized-outer-box containment from the compact-selection
artificial alignment already used by the endpoint artificial-face route.
-/
def ofCompactSelectionArtificialAlignment
    (alignment : EndpointCompactSelectionArtificialAlignment S.endpointAutoBase) :
    S.EndpointCompactActiveLocalizedOuterBoxData :=
  ofEndpointSelectedBoxStrictMargins
    { outer_lower_lt_selectedLower := alignment.outer_lower_lt_selectedLower
      selectedUpper_lt_outer_upper := alignment.selectedUpper_lt_outer_upper }

/--
Build endpoint localized-outer-box containment from a compact-active
strict-buffer alignment.

This is the strongest constructor in this module: the input already names
`S.selection.compactActiveBoxData` as the inner closed boxes, so no selected-box
corner identification facts are needed.
-/
def ofCompactActiveBoxStrictBufferAlignment
    (alignment :
      CompactActiveBoxStrictBufferAlignment S.selection.compactActiveBoxData
        S.endpointAutoBase.toBaseInput.selectedPartition
        S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization) :
    S.EndpointCompactActiveLocalizedOuterBoxData where
  compactBox_subset_endpointInterior := by
    intro x hxD
    have hx :
        x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active := by
      simpa [NaturalCompactSupportEndpointSelectedReconstructionBaseSources.endpointAutoBase]
        using hxD
    exact Icc_subset_boxInteriorSupportBox
      (alignment.outer_lower_lt_innerLower x hx)
      (alignment.innerUpper_lt_outer_upper x hx)

end EndpointCompactActiveLocalizedOuterBoxData

/-- Endpoint localized-outer-box containment from packaged endpoint margins. -/
def endpointLocalizedOuterBoxDataOfStrictMargins
    (margins : S.EndpointSelectedBoxStrictMargins) :
    S.EndpointCompactActiveLocalizedOuterBoxData :=
  EndpointCompactActiveLocalizedOuterBoxData.ofEndpointSelectedBoxStrictMargins
    (S := S) margins

/--
Endpoint localized-outer-box containment from the existing compact-selection
artificial alignment package.
-/
def endpointLocalizedOuterBoxDataOfCompactSelectionAlignment
    (alignment : EndpointCompactSelectionArtificialAlignment S.endpointAutoBase) :
    S.EndpointCompactActiveLocalizedOuterBoxData :=
  EndpointCompactActiveLocalizedOuterBoxData.ofCompactSelectionArtificialAlignment
    (S := S) alignment

/--
Endpoint localized-outer-box containment from compact-active strict-buffer
alignment.
-/
def endpointLocalizedOuterBoxDataOfCompactActiveStrictBufferAlignment
    (alignment :
      CompactActiveBoxStrictBufferAlignment S.selection.compactActiveBoxData
        S.endpointAutoBase.toBaseInput.selectedPartition
        S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization) :
    S.EndpointCompactActiveLocalizedOuterBoxData :=
  EndpointCompactActiveLocalizedOuterBoxData.ofCompactActiveBoxStrictBufferAlignment
    (S := S) alignment

/--
Endpoint strict margins recovered from packaged margins through the localized
outer-box containment record.
-/
def endpointSelectedBoxStrictMarginsOfStrictMargins
    (margins : S.EndpointSelectedBoxStrictMargins) :
    S.EndpointSelectedBoxStrictMargins :=
  (S.endpointLocalizedOuterBoxDataOfStrictMargins margins)
    |>.toEndpointSelectedBoxStrictMargins

@[simp]
theorem endpointSelectedBoxStrictMarginsOfStrictMargins_outer_lower
    (margins : S.EndpointSelectedBoxStrictMargins) :
    (S.endpointSelectedBoxStrictMarginsOfStrictMargins margins).outer_lower_lt_selectedLower =
      (S.endpointLocalizedOuterBoxDataOfStrictMargins
        margins).outer_lower_lt_selectedLower := by
  rfl

/--
Endpoint Stokes from constructor chart alignment and a compact-active
strict-buffer alignment over the selected compact boxes.
-/
theorem stokes_ofM8ChartAlignmentAndCompactActiveStrictBufferAlignment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (alignment :
      CompactActiveBoxStrictBufferAlignment S.selection.compactActiveBoxData
        S.endpointAutoBase.toBaseInput.selectedPartition
        S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.stokes_ofM8ChartAlignmentAndLocalizedOuterBox A
    (S.endpointLocalizedOuterBoxDataOfCompactActiveStrictBufferAlignment
      alignment)

/--
Endpoint Stokes from constructor chart alignment plus an existing
compact-selection artificial alignment, routed through the localized-outer-box
record.
-/
theorem stokes_ofM8ChartAlignmentAndCompactSelectionAlignment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (alignment : EndpointCompactSelectionArtificialAlignment S.endpointAutoBase) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.stokes_ofM8ChartAlignmentAndLocalizedOuterBox A
    (S.endpointLocalizedOuterBoxDataOfCompactSelectionAlignment alignment)

end NaturalCompactSupportEndpointSelectedReconstructionBaseSources

end EndpointLocalizedOuterBoxFromCompactSelectionAuto

end Stokes

end
