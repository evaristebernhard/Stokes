import Stokes.Global.CompactSupportEndpointFacade

/-!
# Compact-active strict outer boxes from localized pieces

`CompactActiveStrictOuterBoxData` is the endpoint-facing source for strict
outer boxes around the compact active closed boxes.  Previous constructors still
asked callers to identify those named outer boxes with the lower/upper corners
stored in the M8 localized interior pieces.

This file fixes that direction of the API: the outer boxes are now defined to
be the localized-piece corners.  Callers provide the genuine geometry, namely
that the compact active box is strictly inside those localized-piece corners
(or the corresponding coordinatewise strict margins).  The equalities between
outer boxes and localized-piece corners become definitional.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactActiveStrictOuterBoxFromLocalizedPiecesAuto

universe u w b ei eb

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
variable {D : CompactActiveBoxData I omega}

/--
Localized-piece outer-box data for compact active boxes.

The outer box is not named independently: it is definitionally the lower/upper
corner pair stored in `measureLocalization.localizedInterior.piece x`.  The
only geometric input is that each compact active closed box lies in the
corresponding localized-piece open box.  The reverse active-set inclusion says
that every compact active box is one of the selected localized pieces.
-/
structure CompactActiveLocalizedPieceOuterBoxData
    (D : CompactActiveBoxData I omega)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages) where
  selectedPartitionAlignment :
    CompactActiveSelectedPartitionAlignment D selectedPartition
  localizedPieceAlignment :
    LocalizedInteriorPieceAlignment selectedPartition targetImages
      measureLocalization
  compactActive_subset_selected :
    forall x, x ∈ D.finiteActive.active -> x ∈ selectedPartition.active
  compactBox_subset_pieceInterior :
    forall x, x ∈ selectedPartition.active ->
      Set.Icc (D.lower x) (D.upper x) ⊆
        boxInteriorSupportBox
          (measureLocalization.localizedInterior.piece x).lowerCorner
          (measureLocalization.localizedInterior.piece x).upperCorner

namespace CompactActiveLocalizedPieceOuterBoxData

variable
    (A :
      CompactActiveLocalizedPieceOuterBoxData D selectedPartition targetImages
        measureLocalization)

/-- The selected and compact-active labels are equivalent for this package. -/
theorem selected_active_iff_compactActive
    (A :
      CompactActiveLocalizedPieceOuterBoxData D selectedPartition targetImages
        measureLocalization)
    (x : M) :
    x ∈ selectedPartition.active <-> x ∈ D.finiteActive.active :=
  ⟨(A.selectedPartitionAlignment).active_subset x,
    A.compactActive_subset_selected x⟩

/-- The localized-piece containment, reindexed by compact-active labels. -/
theorem compactBox_subset_pieceInterior_of_compactActive
    (A :
      CompactActiveLocalizedPieceOuterBoxData D selectedPartition targetImages
        measureLocalization) :
    forall x, x ∈ D.finiteActive.active ->
      Set.Icc (D.lower x) (D.upper x) ⊆
        boxInteriorSupportBox
          (measureLocalization.localizedInterior.piece x).lowerCorner
          (measureLocalization.localizedInterior.piece x).upperCorner := by
  intro x hx
  exact A.compactBox_subset_pieceInterior x
    (A.compactActive_subset_selected x hx)

/--
Forget localized-piece outer boxes to the previously used named strict outer
box data.  The named outer boxes are definitionally the localized-piece
corners.
-/
def toCompactActiveStrictOuterBoxData
    (A :
      CompactActiveLocalizedPieceOuterBoxData D selectedPartition targetImages
        measureLocalization) :
    CompactActiveStrictOuterBoxData D where
  outerLower := fun x =>
    (measureLocalization.localizedInterior.piece x).lowerCorner
  outerUpper := fun x =>
    (measureLocalization.localizedInterior.piece x).upperCorner
  compactBox_subset_outerInterior :=
    compactBox_subset_pieceInterior_of_compactActive A

@[simp]
theorem toCompactActiveStrictOuterBoxData_outerLower :
    A.toCompactActiveStrictOuterBoxData.outerLower =
      fun x => (measureLocalization.localizedInterior.piece x).lowerCorner := by
  rfl

@[simp]
theorem toCompactActiveStrictOuterBoxData_outerUpper :
    A.toCompactActiveStrictOuterBoxData.outerUpper =
      fun x => (measureLocalization.localizedInterior.piece x).upperCorner := by
  rfl

/--
The downstream single-source strict-buffer constructor.  The two localized-piece
corner identifications are now `rfl`.
-/
def toStrictBufferConstructorData
    (A :
      CompactActiveLocalizedPieceOuterBoxData D selectedPartition targetImages
        measureLocalization) :
    CompactActiveStrictBufferConstructorData D selectedPartition targetImages
      measureLocalization :=
  CompactActiveStrictBufferConstructorData.ofStrictOuterBoxData
    A.toCompactActiveStrictOuterBoxData
    A.selectedPartitionAlignment
    A.localizedPieceAlignment
    (by intro x hx; rfl)
    (by intro x hx; rfl)

/-- Direct strict-buffer alignment generated from localized-piece outer boxes. -/
def toCompactActiveBoxStrictBufferAlignment
    (A :
      CompactActiveLocalizedPieceOuterBoxData D selectedPartition targetImages
        measureLocalization) :
    CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
      measureLocalization :=
  A.toStrictBufferConstructorData.toCompactActiveBoxStrictBufferAlignment

/--
Build localized-piece outer-box data from coordinatewise strict margins.

This is the common output of a coherent chart-box selection: the compact active
closed box is already fixed, and the localized piece records a strictly larger
box around it.
-/
def ofPieceStrictMargins
    (selectedPartitionAlignment :
      CompactActiveSelectedPartitionAlignment D selectedPartition)
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment selectedPartition targetImages
        measureLocalization)
    (compactActive_subset_selected :
      forall x, x ∈ D.finiteActive.active -> x ∈ selectedPartition.active)
    (pieceLower_lt_compactLower :
      forall x, x ∈ selectedPartition.active -> forall j : Fin (n + 1),
        (measureLocalization.localizedInterior.piece x).lowerCorner j <
          D.lower x j)
    (compactUpper_lt_pieceUpper :
      forall x, x ∈ selectedPartition.active -> forall j : Fin (n + 1),
        D.upper x j <
          (measureLocalization.localizedInterior.piece x).upperCorner j) :
    CompactActiveLocalizedPieceOuterBoxData D selectedPartition targetImages
      measureLocalization where
  selectedPartitionAlignment := selectedPartitionAlignment
  localizedPieceAlignment := localizedPieceAlignment
  compactActive_subset_selected := compactActive_subset_selected
  compactBox_subset_pieceInterior := by
    intro x hx
    exact Icc_subset_boxInteriorSupportBox
      (pieceLower_lt_compactLower x hx)
      (compactUpper_lt_pieceUpper x hx)

/--
Build localized-piece outer-box data from an existing strict-buffer alignment,
while keeping the stronger constructor record that remembers the localized
piece chart-label alignment.
-/
def ofStrictBufferAlignment
    (selectedPartitionAlignment :
      CompactActiveSelectedPartitionAlignment D selectedPartition)
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment selectedPartition targetImages
        measureLocalization)
    (compactActive_subset_selected :
      forall x, x ∈ D.finiteActive.active -> x ∈ selectedPartition.active)
    (strictBuffer :
      CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
        measureLocalization) :
    CompactActiveLocalizedPieceOuterBoxData D selectedPartition targetImages
      measureLocalization :=
  ofPieceStrictMargins selectedPartitionAlignment localizedPieceAlignment
    compactActive_subset_selected
    strictBuffer.outer_lower_lt_innerLower
    strictBuffer.innerUpper_lt_outer_upper

end CompactActiveLocalizedPieceOuterBoxData

namespace CompactSupportFiniteActiveSelection

variable {rho : SmoothPartitionOfUnity M I M univ}
variable {K : Set M} {hK : IsCompact K}
variable
    (S : CompactSupportFiniteActiveSelection (I := I) rho K hK omega)
    (smoothness :
      ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega)

/--
Compact-support finite-active selections supply both directions of the active
set equality.  Thus coordinatewise localized-piece strict margins directly
generate the localized-piece outer-box package.
-/
def toLocalizedPieceOuterBoxDataOfPieceStrictMargins
    {targetImages :
      BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega
        (S.selectedBoxPartitionOfUnity smoothness) targetImages}
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization)
    (pieceLower_lt_compactLower :
      forall x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active ->
        forall j : Fin (n + 1),
          (measureLocalization.localizedInterior.piece x).lowerCorner j <
            S.compactActiveBoxData.lower x j)
    (compactUpper_lt_pieceUpper :
      forall x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active ->
        forall j : Fin (n + 1),
          S.compactActiveBoxData.upper x j <
            (measureLocalization.localizedInterior.piece x).upperCorner j) :
    CompactActiveLocalizedPieceOuterBoxData S.compactActiveBoxData
      (S.selectedBoxPartitionOfUnity smoothness) targetImages
      measureLocalization :=
  CompactActiveLocalizedPieceOuterBoxData.ofPieceStrictMargins
    (S.toCompactActiveSelectedPartitionAlignment smoothness)
    localizedPieceAlignment
    (by intro x hx; simpa using hx)
    pieceLower_lt_compactLower
    compactUpper_lt_pieceUpper

/--
Finite-active compact-support route directly to the single-source strict-buffer
constructor, with localized-piece corners as the outer boxes.
-/
def toStrictBufferConstructorDataOfLocalizedPieceStrictMargins
    {targetImages :
      BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega
        (S.selectedBoxPartitionOfUnity smoothness) targetImages}
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization)
    (pieceLower_lt_compactLower :
      forall x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active ->
        forall j : Fin (n + 1),
          (measureLocalization.localizedInterior.piece x).lowerCorner j <
            S.compactActiveBoxData.lower x j)
    (compactUpper_lt_pieceUpper :
      forall x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active ->
        forall j : Fin (n + 1),
          S.compactActiveBoxData.upper x j <
            (measureLocalization.localizedInterior.piece x).upperCorner j) :
    CompactActiveStrictBufferConstructorData S.compactActiveBoxData
      (S.selectedBoxPartitionOfUnity smoothness) targetImages
      measureLocalization :=
  (S.toLocalizedPieceOuterBoxDataOfPieceStrictMargins smoothness
    localizedPieceAlignment pieceLower_lt_compactLower
    compactUpper_lt_pieceUpper).toStrictBufferConstructorData

/--
Finite-active compact-support route directly to the strict-buffer alignment,
with localized-piece corners as the outer boxes.
-/
def toCompactActiveBoxStrictBufferAlignmentOfLocalizedPieceStrictMargins
    {targetImages :
      BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega
        (S.selectedBoxPartitionOfUnity smoothness) targetImages}
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization)
    (pieceLower_lt_compactLower :
      forall x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active ->
        forall j : Fin (n + 1),
          (measureLocalization.localizedInterior.piece x).lowerCorner j <
            S.compactActiveBoxData.lower x j)
    (compactUpper_lt_pieceUpper :
      forall x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active ->
        forall j : Fin (n + 1),
          S.compactActiveBoxData.upper x j <
            (measureLocalization.localizedInterior.piece x).upperCorner j) :
    CompactActiveBoxStrictBufferAlignment S.compactActiveBoxData
      (S.selectedBoxPartitionOfUnity smoothness) targetImages
      measureLocalization :=
  (S.toLocalizedPieceOuterBoxDataOfPieceStrictMargins smoothness
    localizedPieceAlignment pieceLower_lt_compactLower
    compactUpper_lt_pieceUpper).toCompactActiveBoxStrictBufferAlignment

end CompactSupportFiniteActiveSelection

namespace NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources

variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]
variable
    (S :
      NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu)

/--
Endpoint localized-piece outer-box data from strict margins against the compact
active boxes.  The outer boxes are the endpoint M8 localized-piece corners, so
there are no separate outer-corner equality inputs.
-/
def endpointLocalizedPieceOuterBoxDataOfPieceStrictMargins
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment
        S.endpointAutoBase.toBaseInput.selectedPartition
        S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization)
    (pieceLower_lt_compactLower :
      forall x,
        x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner j <
            S.selection.compactActiveBoxData.lower x j)
    (compactUpper_lt_pieceUpper :
      forall x,
        x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          S.selection.compactActiveBoxData.upper x j <
            (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner j) :
    CompactActiveLocalizedPieceOuterBoxData S.selection.compactActiveBoxData
      S.endpointAutoBase.toBaseInput.selectedPartition
      S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
      S.endpointMeasureLocalization :=
  CompactActiveLocalizedPieceOuterBoxData.ofPieceStrictMargins
    (by
      change
        CompactActiveSelectedPartitionAlignment S.selection.compactActiveBoxData
          (S.selection.selectedBoxPartitionOfUnity S.smoothness)
      exact S.selection.toCompactActiveSelectedPartitionAlignment S.smoothness)
    localizedPieceAlignment
    (by
      intro x hx
      simpa
        [NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources.endpointAutoBase]
        using hx)
    pieceLower_lt_compactLower
    compactUpper_lt_pieceUpper

/--
Endpoint strict-buffer constructor generated with localized-piece corners as
the outer boxes.
-/
def endpointStrictBufferConstructorDataOfLocalizedPieceStrictMargins
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment
        S.endpointAutoBase.toBaseInput.selectedPartition
        S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization)
    (pieceLower_lt_compactLower :
      forall x,
        x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner j <
            S.selection.compactActiveBoxData.lower x j)
    (compactUpper_lt_pieceUpper :
      forall x,
        x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          S.selection.compactActiveBoxData.upper x j <
            (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner j) :
    CompactActiveStrictBufferConstructorData S.selection.compactActiveBoxData
      S.endpointAutoBase.toBaseInput.selectedPartition
      S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
      S.endpointMeasureLocalization :=
  (S.endpointLocalizedPieceOuterBoxDataOfPieceStrictMargins
    localizedPieceAlignment pieceLower_lt_compactLower
    compactUpper_lt_pieceUpper).toStrictBufferConstructorData

/--
Endpoint Stokes from M8 chart alignment and localized-piece strict margins.

This is the theorem-facing endpoint route produced by this file: callers no
longer provide separately named outer boxes or equality proofs identifying
those boxes with localized-piece corners.
-/
theorem stokes_ofM8ChartAlignmentAndLocalizedPieceStrictMargins
    (chartAlignment : LocalizedInteriorM8ChartAlignment S.localized)
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment
        S.endpointAutoBase.toBaseInput.selectedPartition
        S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization)
    (pieceLower_lt_compactLower :
      forall x,
        x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner j <
            S.selection.compactActiveBoxData.lower x j)
    (compactUpper_lt_pieceUpper :
      forall x,
        x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          S.selection.compactActiveBoxData.upper x j <
            (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner j) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.stokes_ofM8ChartAlignmentAndStrictBufferConstructorData chartAlignment
    (S.endpointStrictBufferConstructorDataOfLocalizedPieceStrictMargins
      localizedPieceAlignment pieceLower_lt_compactLower
      compactUpper_lt_pieceUpper)

end NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources

namespace NaturalCompactSupportEndpointExtDerivBaseSources

variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]
variable
    (S :
      NaturalCompactSupportEndpointExtDerivBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu)

/-- Ext-deriv endpoint route through localized-piece strict margins. -/
theorem stokes_ofM8ChartAlignmentAndLocalizedPieceStrictMargins
    (chartAlignment : LocalizedInteriorM8ChartAlignment S.localized)
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment
        S.compactSupportEndpointSource.endpointAutoBase.toBaseInput.selectedPartition
        S.compactSupportEndpointSource.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization)
    (pieceLower_lt_compactLower :
      forall x,
        x ∈ S.compactSupportEndpointSource.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner j <
            S.selection.compactActiveBoxData.lower x j)
    (compactUpper_lt_pieceUpper :
      forall x,
        x ∈ S.compactSupportEndpointSource.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          S.selection.compactActiveBoxData.upper x j <
            (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner j) :
    S.endpointMeasureLocalization.bulkMeasureIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  S.compactSupportEndpointSource
    |>.stokes_ofM8ChartAlignmentAndLocalizedPieceStrictMargins chartAlignment
      localizedPieceAlignment pieceLower_lt_compactLower
      compactUpper_lt_pieceUpper

end NaturalCompactSupportEndpointExtDerivBaseSources

end CompactActiveStrictOuterBoxFromLocalizedPiecesAuto

end Stokes

end
