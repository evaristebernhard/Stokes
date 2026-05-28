import Stokes.Global.NaturalCompactSupportEndpointMarginAuto

/-!
# Constructor-side endpoint strict-margin data

`NaturalCompactSupportEndpointMarginAuto` already lets the endpoint theorem use
one packaged `EndpointSelectedBoxStrictMargins` value instead of two loose
strict-margin inequalities.  This module moves one step closer to the actual
compact-support chart-box construction:

* the preferred input is now the geometric statement that each selected compact
  closed box lies in the interior of the endpoint localized outer box;
* a secondary adapter accepts a separately named outer box and identifies it
  with the endpoint localized piece;
* the old active inner/outer selection route is still available, but only as a
  way to produce the cleaner constructor-side record.

No new analytic theorem is hidden here: the remaining real obligation is the
localized outer-box containment itself.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportEndpointMarginConstructorsAuto

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
Constructor-side localized outer-box data for the endpoint.

The compact-support selection already determines the inner closed boxes through
`S.selection.compactActiveBoxData`.  The only geometric fact this record asks
for is that those closed boxes are strictly inside the localized outer boxes
stored in the endpoint measure localization.
-/
structure EndpointCompactActiveLocalizedOuterBoxData where
  compactBox_subset_endpointInterior :
    ∀ x, x ∈ S.selection.compactActiveBoxData.finiteActive.active →
      Set.Icc (S.selection.compactActiveBoxData.lower x)
          (S.selection.compactActiveBoxData.upper x) ⊆
        boxInteriorSupportBox
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner
          (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner

namespace EndpointCompactActiveLocalizedOuterBoxData

variable {S}

/--
Selected active endpoint labels are active for the compact active-box package
that generated the selected partition.
-/
theorem endpointActive_mem_compactActive
    {x : M}
    (hx : x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active) :
    x ∈ S.selection.compactActiveBoxData.finiteActive.active := by
  simpa [NaturalCompactSupportEndpointSelectedReconstructionBaseSources.endpointAutoBase]
    using hx

/--
Lower strict margin obtained by evaluating the localized outer-box containment
at the lower corner of the compact selected box.
-/
theorem outer_lower_lt_selectedLower
    (D : S.EndpointCompactActiveLocalizedOuterBoxData) :
    ∀ x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active →
      ∀ j : Fin (n + 1),
        (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner j <
          S.endpointAutoBase.toBaseInput.selectedPartition.lower x j := by
  intro x hx j
  have hxD := endpointActive_mem_compactActive (S := S) hx
  have hle := S.selection.compactActiveBoxData.le hxD
  have hmem :
      S.selection.compactActiveBoxData.lower x ∈
        Set.Icc (S.selection.compactActiveBoxData.lower x)
          (S.selection.compactActiveBoxData.upper x) :=
    ⟨le_rfl, hle⟩
  have hbox :=
    D.compactBox_subset_endpointInterior x hxD hmem j
  simpa [NaturalCompactSupportEndpointSelectedReconstructionBaseSources.endpointAutoBase]
    using hbox.1

/--
Upper strict margin obtained by evaluating the localized outer-box containment
at the upper corner of the compact selected box.
-/
theorem selectedUpper_lt_outer_upper
    (D : S.EndpointCompactActiveLocalizedOuterBoxData) :
    ∀ x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active →
      ∀ j : Fin (n + 1),
        S.endpointAutoBase.toBaseInput.selectedPartition.upper x j <
          (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner j := by
  intro x hx j
  have hxD := endpointActive_mem_compactActive (S := S) hx
  have hle := S.selection.compactActiveBoxData.le hxD
  have hmem :
      S.selection.compactActiveBoxData.upper x ∈
        Set.Icc (S.selection.compactActiveBoxData.lower x)
          (S.selection.compactActiveBoxData.upper x) :=
    ⟨hle, le_rfl⟩
  have hbox :=
    D.compactBox_subset_endpointInterior x hxD hmem j
  simpa [NaturalCompactSupportEndpointSelectedReconstructionBaseSources.endpointAutoBase]
    using hbox.2

/--
The clean constructor-side route to endpoint strict margins: no selected-box
corner identifications are exposed.
-/
def toEndpointSelectedBoxStrictMargins
    (D : S.EndpointCompactActiveLocalizedOuterBoxData) :
    S.EndpointSelectedBoxStrictMargins where
  outer_lower_lt_selectedLower := D.outer_lower_lt_selectedLower
  selectedUpper_lt_outer_upper := D.selectedUpper_lt_outer_upper

end EndpointCompactActiveLocalizedOuterBoxData

/-- Endpoint strict margins from localized outer-box containment. -/
def endpointSelectedBoxStrictMarginsOfLocalizedOuterBox
    (D : S.EndpointCompactActiveLocalizedOuterBoxData) :
    S.EndpointSelectedBoxStrictMargins :=
  D.toEndpointSelectedBoxStrictMargins

/--
Endpoint Stokes from constructor chart-label alignment and the localized
outer-box containment record.
-/
theorem stokes_ofM8ChartAlignmentAndLocalizedOuterBox
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointCompactActiveLocalizedOuterBoxData) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.stokes_ofM8ChartAlignmentAndStrictMargins A
    (S.endpointSelectedBoxStrictMarginsOfLocalizedOuterBox D)

/--
A constructor-side variant where the outer box is named separately.  This is
useful for local chart-box algorithms that first produce an outer box and only
later identify it with the endpoint localized piece.
-/
structure EndpointCompactActiveOuterBoxData where
  outerLower : M → Fin (n + 1) → Real
  outerUpper : M → Fin (n + 1) → Real
  compactBox_subset_outerInterior :
    ∀ x, x ∈ S.selection.compactActiveBoxData.finiteActive.active →
      Set.Icc (S.selection.compactActiveBoxData.lower x)
          (S.selection.compactActiveBoxData.upper x) ⊆
        boxInteriorSupportBox (outerLower x) (outerUpper x)
  outerLower_eq_endpointPieceLower :
    ∀ x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active →
      outerLower x =
        (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner
  outerUpper_eq_endpointPieceUpper :
    ∀ x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active →
      outerUpper x =
        (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner

namespace EndpointCompactActiveOuterBoxData

variable {S}

/-- Forget a named outer box to the localized endpoint outer-box record. -/
def toLocalizedOuterBoxData
    (D : S.EndpointCompactActiveOuterBoxData) :
    S.EndpointCompactActiveLocalizedOuterBoxData where
  compactBox_subset_endpointInterior := by
    intro x hxD y hy
    have hx :
        x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active := by
      simpa [NaturalCompactSupportEndpointSelectedReconstructionBaseSources.endpointAutoBase]
        using hxD
    have h := D.compactBox_subset_outerInterior x hxD hy
    simpa [D.outerLower_eq_endpointPieceLower x hx,
      D.outerUpper_eq_endpointPieceUpper x hx] using h

/-- Endpoint strict margins from a named constructor-side outer box. -/
def toEndpointSelectedBoxStrictMargins
    (D : S.EndpointCompactActiveOuterBoxData) :
    S.EndpointSelectedBoxStrictMargins :=
  D.toLocalizedOuterBoxData.toEndpointSelectedBoxStrictMargins

/--
Build the named outer-box record from an active strict inner/outer selection
whose inner box is the compact active selected box.
-/
def ofActiveStrictInnerOuter
    {coordSupport : M → Set (Fin (n + 1) → Real)}
    (D :
      ActiveStrictInnerOuterBoxSelections
        S.selection.compactActiveBoxData.finiteActive.active coordSupport)
    (innerLower_eq_compactLower :
      ∀ x, x ∈ S.selection.compactActiveBoxData.finiteActive.active →
        D.innerLower x = S.selection.compactActiveBoxData.lower x)
    (innerUpper_eq_compactUpper :
      ∀ x, x ∈ S.selection.compactActiveBoxData.finiteActive.active →
        D.innerUpper x = S.selection.compactActiveBoxData.upper x)
    (outerLower_eq_endpointPieceLower :
      ∀ x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active →
        D.outerLower x =
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_endpointPieceUpper :
      ∀ x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active →
        D.outerUpper x =
          (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner) :
    S.EndpointCompactActiveOuterBoxData where
  outerLower := D.outerLower
  outerUpper := D.outerUpper
  compactBox_subset_outerInterior := by
    intro x hxD y hy
    have hy' :
        y ∈ Set.Icc (D.innerLower x) (D.innerUpper x) := by
      simpa [innerLower_eq_compactLower x hxD,
        innerUpper_eq_compactUpper x hxD] using hy
    exact D.innerIcc_subset_outerInterior x hxD hy'
  outerLower_eq_endpointPieceLower := outerLower_eq_endpointPieceLower
  outerUpper_eq_endpointPieceUpper := outerUpper_eq_endpointPieceUpper

end EndpointCompactActiveOuterBoxData

/-- Endpoint strict margins from a named constructor-side outer box. -/
def endpointSelectedBoxStrictMarginsOfOuterBox
    (D : S.EndpointCompactActiveOuterBoxData) :
    S.EndpointSelectedBoxStrictMargins :=
  D.toEndpointSelectedBoxStrictMargins

/--
Endpoint strict margins from an active strict inner/outer selection over the
compact active box data.  Compared with
`endpointSelectedBoxStrictMarginsOfActiveStrictInnerOuter`, the active set and
inner selected boxes are now the constructor-side compact active boxes.
-/
def endpointSelectedBoxStrictMarginsOfCompactActiveStrictInnerOuter
    {coordSupport : M → Set (Fin (n + 1) → Real)}
    (D :
      ActiveStrictInnerOuterBoxSelections
        S.selection.compactActiveBoxData.finiteActive.active coordSupport)
    (innerLower_eq_compactLower :
      ∀ x, x ∈ S.selection.compactActiveBoxData.finiteActive.active →
        D.innerLower x = S.selection.compactActiveBoxData.lower x)
    (innerUpper_eq_compactUpper :
      ∀ x, x ∈ S.selection.compactActiveBoxData.finiteActive.active →
        D.innerUpper x = S.selection.compactActiveBoxData.upper x)
    (outerLower_eq_endpointPieceLower :
      ∀ x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active →
        D.outerLower x =
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_endpointPieceUpper :
      ∀ x, x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active →
        D.outerUpper x =
          (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner) :
    S.EndpointSelectedBoxStrictMargins :=
  (EndpointCompactActiveOuterBoxData.ofActiveStrictInnerOuter (S := S) D
    innerLower_eq_compactLower innerUpper_eq_compactUpper
    outerLower_eq_endpointPieceLower outerUpper_eq_endpointPieceUpper)
      |>.toEndpointSelectedBoxStrictMargins

end NaturalCompactSupportEndpointSelectedReconstructionBaseSources

end NaturalCompactSupportEndpointMarginConstructorsAuto

end Stokes

end
