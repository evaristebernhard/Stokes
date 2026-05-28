import Stokes.Global.CompactSupportSelectedBoxEndToEnd

/-!
# Constructor data for compact-active strict buffers

This file moves the compact-active strict-buffer route one step closer to the
actual chart-box construction.

`CompactActiveBoxStrictBufferAlignment` is the downstream input consumed by the
artificial-face and natural compact-support builders.  Its fields are expressed
in terms of the selected partition and M8 localized pieces.  The declarations
below let callers instead keep one strict inner/outer box source: the inner
closed boxes are the compact active boxes, and the outer strict boxes are later
identified with the localized M8 outer boxes.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactActiveStrictBufferConstructorAuto

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}
variable {D : CompactActiveBoxData I omega}

/--
Named strict outer boxes around the compact active closed boxes.

This is often the natural output of a chart-box selection algorithm: the compact
active box has already been selected, and the remaining geometric choice is a
larger open box around it.  From this record we can reconstruct an
`ActiveStrictInnerOuterBoxSelections` whose inner boxes are definitionally
`D.lower`/`D.upper`.
-/
structure CompactActiveStrictOuterBoxData
    (D : CompactActiveBoxData I omega) where
  outerLower : M → Fin (n + 1) → Real
  outerUpper : M → Fin (n + 1) → Real
  compactBox_subset_outerInterior :
    ∀ x, x ∈ D.finiteActive.active →
      Set.Icc (D.lower x) (D.upper x) ⊆
        boxInteriorSupportBox (outerLower x) (outerUpper x)

namespace CompactActiveStrictOuterBoxData

variable (O : CompactActiveStrictOuterBoxData D)

/--
Turn a named strict outer box around the compact active boxes into the
strict-inner/outer selection API.
-/
def toActiveStrictInnerOuterBoxSelections :
    ActiveStrictInnerOuterBoxSelections D.finiteActive.active D.coordSupport where
  innerLower := D.lower
  innerUpper := D.upper
  outerLower := O.outerLower
  outerUpper := O.outerUpper
  inner_le_upper := by
    intro i hi
    exact D.le hi
  outer_le_upper := by
    intro i hi j
    have hle : D.lower i ≤ D.upper i := D.le hi
    have hmem :
        D.lower i ∈ Set.Icc (D.lower i) (D.upper i) := by
      exact ⟨le_rfl, hle⟩
    have hbox := O.compactBox_subset_outerInterior i hi hmem j
    exact le_of_lt (lt_trans hbox.1 hbox.2)
  coordSupport_subset_innerIcc := by
    intro i hi
    exact D.coordSupport_subset_Icc hi
  innerIcc_subset_outerInterior := by
    intro i hi
    exact O.compactBox_subset_outerInterior i hi

@[simp]
theorem toActiveStrictInnerOuterBoxSelections_innerLower :
    O.toActiveStrictInnerOuterBoxSelections.innerLower = D.lower := by
  rfl

@[simp]
theorem toActiveStrictInnerOuterBoxSelections_innerUpper :
    O.toActiveStrictInnerOuterBoxSelections.innerUpper = D.upper := by
  rfl

@[simp]
theorem toActiveStrictInnerOuterBoxSelections_outerLower :
    O.toActiveStrictInnerOuterBoxSelections.outerLower = O.outerLower := by
  rfl

@[simp]
theorem toActiveStrictInnerOuterBoxSelections_outerUpper :
    O.toActiveStrictInnerOuterBoxSelections.outerUpper = O.outerUpper := by
  rfl

end CompactActiveStrictOuterBoxData

/--
Single-source strict inner/outer constructor data for compact-active strict
buffers.

The `strictBoxes` field is the single box source.  The two inner equalities say
that this source uses the compact active boxes as inner boxes.  The two outer
equalities identify the same source with the localized M8 outer boxes.  The
selected-partition and localized-piece alignment fields are the existing
bookkeeping bridges.
-/
structure CompactActiveStrictBufferConstructorData
    (D : CompactActiveBoxData I omega)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages) where
  strictBoxes :
    ActiveStrictInnerOuterBoxSelections D.finiteActive.active D.coordSupport
  selectedPartitionAlignment :
    CompactActiveSelectedPartitionAlignment D selectedPartition
  localizedPieceAlignment :
    LocalizedInteriorPieceAlignment selectedPartition targetImages
      measureLocalization
  innerLower_eq_compactLower :
    ∀ x, x ∈ D.finiteActive.active →
      strictBoxes.innerLower x = D.lower x
  innerUpper_eq_compactUpper :
    ∀ x, x ∈ D.finiteActive.active →
      strictBoxes.innerUpper x = D.upper x
  outerLower_eq_pieceLower :
    ∀ x, x ∈ selectedPartition.active →
      strictBoxes.outerLower x =
        (measureLocalization.localizedInterior.piece x).lowerCorner
  outerUpper_eq_pieceUpper :
    ∀ x, x ∈ selectedPartition.active →
      strictBoxes.outerUpper x =
        (measureLocalization.localizedInterior.piece x).upperCorner

namespace CompactActiveStrictBufferConstructorData

/-- Selected active labels are active for the strict box source. -/
theorem selected_active_mem_strictSource
    (A :
      CompactActiveStrictBufferConstructorData D selectedPartition targetImages
        measureLocalization) :
    ∀ x, x ∈ selectedPartition.active → x ∈ D.finiteActive.active :=
  (A.selectedPartitionAlignment).active_subset

/--
The localized pieces are the compact-active localized representatives, after
rewriting the selected partition through the compact-active alignment.
-/
theorem piece_transitionPullback_eq_compactPartition :
    (A :
      CompactActiveStrictBufferConstructorData D selectedPartition targetImages
        measureLocalization) →
    ∀ x, x ∈ selectedPartition.active →
      ManifoldForm.transitionPullbackInChart I
          (measureLocalization.localizedInterior.piece x).sourceChart
          (measureLocalization.localizedInterior.piece x).targetChart
          (measureLocalization.localizedInterior.piece x).localizedForm =
        ManifoldForm.transitionPullbackInChart I x x
          (ManifoldForm.localizedForm I (D.finiteActive.partition x) omega) := by
  intro A x hx
  simpa [(A.selectedPartitionAlignment).partition_eq] using
    (A.localizedPieceAlignment).piece_transitionPullback_eq x hx

/-- Lower strict margin against the compact active lower corner. -/
theorem outer_lower_lt_compactLower :
    (A :
      CompactActiveStrictBufferConstructorData D selectedPartition targetImages
        measureLocalization) →
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      (measureLocalization.localizedInterior.piece x).lowerCorner j <
        D.lower x j := by
  intro A x hx j
  have hxD : x ∈ D.finiteActive.active :=
    A.selected_active_mem_strictSource x hx
  have h := A.strictBoxes.outerLower_lt_innerLower hxD j
  rw [A.outerLower_eq_pieceLower x hx,
    A.innerLower_eq_compactLower x hxD] at h
  exact h

/-- Upper strict margin against the compact active upper corner. -/
theorem compactUpper_lt_outer_upper :
    (A :
      CompactActiveStrictBufferConstructorData D selectedPartition targetImages
        measureLocalization) →
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      D.upper x j <
        (measureLocalization.localizedInterior.piece x).upperCorner j := by
  intro A x hx j
  have hxD : x ∈ D.finiteActive.active :=
    A.selected_active_mem_strictSource x hx
  have h := A.strictBoxes.innerUpper_lt_outerUpper hxD j
  rw [A.innerUpper_eq_compactUpper x hxD,
    A.outerUpper_eq_pieceUpper x hx] at h
  exact h

/--
Selected-box strict margins generated by the same strict inner/outer source.
-/
def toSelectedBoxStrictMarginData :
    (A :
      CompactActiveStrictBufferConstructorData D selectedPartition targetImages
        measureLocalization) →
    SelectedBoxStrictMarginData selectedPartition targetImages
      measureLocalization := by
  intro A
  exact
    { outer_lower_lt_selectedLower := by
        intro x hx j
        simpa [(A.selectedPartitionAlignment).lower_eq] using
          A.outer_lower_lt_compactLower x hx j
      selectedUpper_lt_outer_upper := by
        intro x hx j
        simpa [(A.selectedPartitionAlignment).upper_eq] using
          A.compactUpper_lt_outer_upper x hx j }

/--
Main constructor: a single strict inner/outer box source yields the downstream
compact-active strict-buffer alignment.
-/
def toCompactActiveBoxStrictBufferAlignment
    (A :
      CompactActiveStrictBufferConstructorData D selectedPartition targetImages
        measureLocalization) :
    CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
      measureLocalization where
  active_subset := A.selected_active_mem_strictSource
  piece_transitionPullback_eq :=
    A.piece_transitionPullback_eq_compactPartition
  outer_lower_lt_innerLower :=
    A.outer_lower_lt_compactLower
  innerUpper_lt_outer_upper :=
    A.compactUpper_lt_outer_upper

/-- The produced strict-buffer alignment reuses the same active-subset proof. -/
@[simp]
theorem toCompactActiveBoxStrictBufferAlignment_active_subset
    (A :
      CompactActiveStrictBufferConstructorData D selectedPartition targetImages
        measureLocalization) :
    A.toCompactActiveBoxStrictBufferAlignment.active_subset =
      (A.selectedPartitionAlignment).active_subset := by
  rfl

/-- The produced selected margin data reuses the lower compact margin. -/
@[simp]
theorem toSelectedBoxStrictMarginData_outer_lower
    (A :
      CompactActiveStrictBufferConstructorData D selectedPartition targetImages
        measureLocalization) :
    A.toSelectedBoxStrictMarginData.outer_lower_lt_selectedLower =
      fun x hx j =>
        show
          (measureLocalization.localizedInterior.piece x).lowerCorner j <
            selectedPartition.lower x j from
        by
          simpa [(A.selectedPartitionAlignment).lower_eq] using
            A.outer_lower_lt_compactLower x hx j := by
  rfl

/--
Build constructor data from an existing active strict-inner/outer source and
explicit identifications.
-/
def ofActiveStrictInnerOuter
    (strictBoxes :
      ActiveStrictInnerOuterBoxSelections D.finiteActive.active D.coordSupport)
    (selectedPartitionAlignment :
      CompactActiveSelectedPartitionAlignment D selectedPartition)
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment selectedPartition targetImages
        measureLocalization)
    (innerLower_eq_compactLower :
      ∀ x, x ∈ D.finiteActive.active →
        strictBoxes.innerLower x = D.lower x)
    (innerUpper_eq_compactUpper :
      ∀ x, x ∈ D.finiteActive.active →
        strictBoxes.innerUpper x = D.upper x)
    (outerLower_eq_pieceLower :
      ∀ x, x ∈ selectedPartition.active →
        strictBoxes.outerLower x =
          (measureLocalization.localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_pieceUpper :
      ∀ x, x ∈ selectedPartition.active →
        strictBoxes.outerUpper x =
          (measureLocalization.localizedInterior.piece x).upperCorner) :
    CompactActiveStrictBufferConstructorData D selectedPartition targetImages
      measureLocalization where
  strictBoxes := strictBoxes
  selectedPartitionAlignment := selectedPartitionAlignment
  localizedPieceAlignment := localizedPieceAlignment
  innerLower_eq_compactLower := innerLower_eq_compactLower
  innerUpper_eq_compactUpper := innerUpper_eq_compactUpper
  outerLower_eq_pieceLower := outerLower_eq_pieceLower
  outerUpper_eq_pieceUpper := outerUpper_eq_pieceUpper

/--
Build constructor data from named strict outer boxes around the compact active
closed boxes.  The inner-box identifications become definitional.
-/
def ofStrictOuterBoxData
    (outerBoxData : CompactActiveStrictOuterBoxData D)
    (selectedPartitionAlignment :
      CompactActiveSelectedPartitionAlignment D selectedPartition)
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment selectedPartition targetImages
        measureLocalization)
    (outerLower_eq_pieceLower :
      ∀ x, x ∈ selectedPartition.active →
        outerBoxData.outerLower x =
          (measureLocalization.localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_pieceUpper :
      ∀ x, x ∈ selectedPartition.active →
        outerBoxData.outerUpper x =
          (measureLocalization.localizedInterior.piece x).upperCorner) :
    CompactActiveStrictBufferConstructorData D selectedPartition targetImages
      measureLocalization :=
  ofActiveStrictInnerOuter
    outerBoxData.toActiveStrictInnerOuterBoxSelections
    selectedPartitionAlignment localizedPieceAlignment
    (by intro x hx; rfl)
    (by intro x hx; rfl)
    outerLower_eq_pieceLower
    outerUpper_eq_pieceUpper

end CompactActiveStrictBufferConstructorData

namespace CompactSupportFiniteActiveSelection

variable {rho : SmoothPartitionOfUnity M I M univ}
variable {K : Set M} {hK : IsCompact K}
variable
    (S : CompactSupportFiniteActiveSelection (I := I) rho K hK omega)
    (smoothness :
      ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega)

/--
Compact-support finite-active selections supply the selected-partition
alignment automatically; callers only provide the single strict box source and
its identifications with compact active and localized outer boxes.
-/
def toStrictBufferConstructorDataOfActiveStrictInnerOuter
    {targetImages :
      BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega
        (S.selectedBoxPartitionOfUnity smoothness) targetImages}
    (strictBoxes :
      ActiveStrictInnerOuterBoxSelections
        S.compactActiveBoxData.finiteActive.active
        S.compactActiveBoxData.coordSupport)
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization)
    (innerLower_eq_compactLower :
      ∀ x, x ∈ S.compactActiveBoxData.finiteActive.active →
        strictBoxes.innerLower x = S.compactActiveBoxData.lower x)
    (innerUpper_eq_compactUpper :
      ∀ x, x ∈ S.compactActiveBoxData.finiteActive.active →
        strictBoxes.innerUpper x = S.compactActiveBoxData.upper x)
    (outerLower_eq_pieceLower :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        strictBoxes.outerLower x =
          (measureLocalization.localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_pieceUpper :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        strictBoxes.outerUpper x =
          (measureLocalization.localizedInterior.piece x).upperCorner) :
    CompactActiveStrictBufferConstructorData S.compactActiveBoxData
      (S.selectedBoxPartitionOfUnity smoothness) targetImages
      measureLocalization :=
  CompactActiveStrictBufferConstructorData.ofActiveStrictInnerOuter
    strictBoxes
    (S.toCompactActiveSelectedPartitionAlignment smoothness)
    localizedPieceAlignment
    innerLower_eq_compactLower innerUpper_eq_compactUpper
    outerLower_eq_pieceLower outerUpper_eq_pieceUpper

/--
Compact-support finite-active constructor from named strict outer boxes.  This
is the shortest route when the chart-box construction chooses an outer box
around the already selected compact active box.
-/
def toStrictBufferConstructorDataOfStrictOuterBoxData
    {targetImages :
      BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega
        (S.selectedBoxPartitionOfUnity smoothness) targetImages}
    (outerBoxData :
      CompactActiveStrictOuterBoxData S.compactActiveBoxData)
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization)
    (outerLower_eq_pieceLower :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        outerBoxData.outerLower x =
          (measureLocalization.localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_pieceUpper :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        outerBoxData.outerUpper x =
          (measureLocalization.localizedInterior.piece x).upperCorner) :
    CompactActiveStrictBufferConstructorData S.compactActiveBoxData
      (S.selectedBoxPartitionOfUnity smoothness) targetImages
      measureLocalization :=
  CompactActiveStrictBufferConstructorData.ofStrictOuterBoxData
    outerBoxData
    (S.toCompactActiveSelectedPartitionAlignment smoothness)
    localizedPieceAlignment
    outerLower_eq_pieceLower outerUpper_eq_pieceUpper

/--
Direct compact-active strict-buffer alignment from a compact-support finite
active selection and named strict outer boxes.
-/
def toCompactActiveBoxStrictBufferAlignmentOfStrictOuterBoxData
    {targetImages :
      BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega
        (S.selectedBoxPartitionOfUnity smoothness) targetImages}
    (outerBoxData :
      CompactActiveStrictOuterBoxData S.compactActiveBoxData)
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization)
    (outerLower_eq_pieceLower :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        outerBoxData.outerLower x =
          (measureLocalization.localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_pieceUpper :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        outerBoxData.outerUpper x =
          (measureLocalization.localizedInterior.piece x).upperCorner) :
    CompactActiveBoxStrictBufferAlignment S.compactActiveBoxData
      (S.selectedBoxPartitionOfUnity smoothness) targetImages
      measureLocalization :=
  (S.toStrictBufferConstructorDataOfStrictOuterBoxData smoothness
    outerBoxData localizedPieceAlignment outerLower_eq_pieceLower
    outerUpper_eq_pieceUpper).toCompactActiveBoxStrictBufferAlignment

end CompactSupportFiniteActiveSelection

end CompactActiveStrictBufferConstructorAuto

end Stokes

end
