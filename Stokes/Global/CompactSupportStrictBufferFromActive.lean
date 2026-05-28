import Stokes.Global.CompactSupportStrictBuffer
import Stokes.Global.PartitionCompactSupport
import Stokes.Global.CompactSupportFiniteActiveSelection
import Stokes.Global.LocalizedInteriorConstructors
import Stokes.Global.M8MeasureConstructors

/-!
# Strict buffers from active compact-support boxes

This file connects the active compact-support box layer to the strict-buffer
input consumed by the artificial-face route.

The automatic part is the support transport: active compact coordinate support
gives a closed inner box for each localized chart representative.  The genuinely
geometric part is kept explicit as an alignment record: the selected partition,
the M8 measure-localized pieces, and the outer boxes must be the same choices,
with a strict margin around the inner closed box.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportStrictBufferFromActive

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

/--
Alignment needed to turn compact active boxes into strict inner-box buffers for
the M8-localized interior pieces.

`D` supplies the inner closed boxes.  The fields say that every selected active
chart is active for `D`, that the M8 localized chart representative is the same
localized representative controlled by `D`, and that the inner closed box sits
strictly inside the outer box stored in the M8 localized piece.
-/
structure CompactActiveBoxStrictBufferAlignment
    (D : CompactActiveBoxData I omega)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages) where
  /-- Selected active chart labels are active for the compact active-box data. -/
  active_subset :
    ∀ x, x ∈ selectedPartition.active → x ∈ D.finiteActive.active
  /--
  The M8 localized representative is the localized selected partition term
  controlled by the compact active-box package.
  -/
  piece_transitionPullback_eq :
    ∀ x, x ∈ selectedPartition.active →
      ManifoldForm.transitionPullbackInChart I
          (measureLocalization.localizedInterior.piece x).sourceChart
          (measureLocalization.localizedInterior.piece x).targetChart
          (measureLocalization.localizedInterior.piece x).localizedForm =
        ManifoldForm.transitionPullbackInChart I x x
          (ManifoldForm.localizedForm I (D.finiteActive.partition x) omega)
  /-- The M8 outer lower corner is strictly below the inner lower corner. -/
  outer_lower_lt_innerLower :
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      (measureLocalization.localizedInterior.piece x).lowerCorner j <
        D.lower x j
  /-- The inner upper corner is strictly below the M8 outer upper corner. -/
  innerUpper_lt_outer_upper :
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      D.upper x j <
        (measureLocalization.localizedInterior.piece x).upperCorner j

namespace CompactActiveBoxStrictBufferAlignment

variable {D : CompactActiveBoxData I omega}

/--
The active compact-support boxes provide the closed inner-box support field
needed by `LocalizedInteriorFormInnerBoxBuffer`.
-/
theorem localized_tsupport_subset_innerIcc
    (A :
      CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
        measureLocalization) :
    ∀ x, x ∈ selectedPartition.active →
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (measureLocalization.localizedInterior.piece x).sourceChart
            (measureLocalization.localizedInterior.piece x).targetChart
            (measureLocalization.localizedInterior.piece x).localizedForm) ⊆
        Set.Icc (D.lower x) (D.upper x) := by
  intro x hx
  have hxD : x ∈ D.finiteActive.active := A.active_subset x hx
  have hsupport :
      tsupport
          (ManifoldForm.transitionPullbackInChart I x x
            (ManifoldForm.localizedForm I (D.finiteActive.partition x) omega)) ⊆
        Set.Icc (D.lower x) (D.upper x) :=
    D.localized_tsupport_subset_box hxD
  change
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (measureLocalization.localizedInterior.piece x).sourceChart
          (measureLocalization.localizedInterior.piece x).targetChart
          (measureLocalization.localizedInterior.piece x).localizedForm) ⊆
      Set.Icc (D.lower x) (D.upper x)
  rw [A.piece_transitionPullback_eq x hx]
  exact hsupport

/--
Build the strict inner-box buffer from compact active boxes plus the explicit
M8/selected-partition alignment data.
-/
def toLocalizedInteriorFormInnerBoxBuffer
    (A :
      CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
        measureLocalization) :
    LocalizedInteriorFormInnerBoxBuffer I omega selectedPartition targetImages
      measureLocalization where
  innerLower := D.lower
  innerUpper := D.upper
  localized_tsupport_subset_innerIcc :=
    A.localized_tsupport_subset_innerIcc
  lower_lt_innerLower := A.outer_lower_lt_innerLower
  innerUpper_lt_upper := A.innerUpper_lt_outer_upper

/-- Direct compact-support box buffer produced from compact active boxes. -/
def toCompactSupportBoxBuffer
    (A :
      CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
        measureLocalization) :
    CompactSupportBoxBuffer I omega selectedPartition targetImages
      measureLocalization :=
  A.toLocalizedInteriorFormInnerBoxBuffer.toCompactSupportBoxBuffer

@[simp]
theorem toLocalizedInteriorFormInnerBoxBuffer_innerLower
    (A :
      CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
        measureLocalization) :
    A.toLocalizedInteriorFormInnerBoxBuffer.innerLower = D.lower :=
  rfl

@[simp]
theorem toLocalizedInteriorFormInnerBoxBuffer_innerUpper
    (A :
      CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
        measureLocalization) :
    A.toLocalizedInteriorFormInnerBoxBuffer.innerUpper = D.upper :=
  rfl

end CompactActiveBoxStrictBufferAlignment

/--
Alignment needed when the input is still the pre-box
`ActiveChartCompactSupportData`.

The inner closed boxes are the automatically selected boxes `D.box`.  This is a
slightly earlier route than `CompactActiveBoxStrictBufferAlignment`: it uses the
finite-active package `P` and the compact-coordinate support data directly.
-/
structure ActiveChartCompactSupportStrictBufferAlignment
    (P : FiniteActiveOnCompact (M := M) I)
    (D : ActiveChartCompactSupportData P omega)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages) where
  /-- Selected active chart labels are active for `P`. -/
  active_subset :
    ∀ x, x ∈ selectedPartition.active → x ∈ P.active
  /--
  The M8 localized representative is the localized representative controlled
  by the active compact-support data.
  -/
  piece_transitionPullback_eq :
    ∀ x, x ∈ selectedPartition.active →
      ManifoldForm.transitionPullbackInChart I
          (measureLocalization.localizedInterior.piece x).sourceChart
          (measureLocalization.localizedInterior.piece x).targetChart
          (measureLocalization.localizedInterior.piece x).localizedForm =
        ManifoldForm.transitionPullbackInChart I x x
          (ManifoldForm.localizedForm I (P.partition x) omega)
  /-- The M8 outer lower corner is strictly below the selected inner lower box. -/
  outer_lower_lt_innerLower :
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      (measureLocalization.localizedInterior.piece x).lowerCorner j <
        (D.box x).a j
  /-- The selected inner upper box is strictly below the M8 outer upper corner. -/
  innerUpper_lt_outer_upper :
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      (D.box x).b j <
        (measureLocalization.localizedInterior.piece x).upperCorner j

namespace ActiveChartCompactSupportStrictBufferAlignment

variable {P : FiniteActiveOnCompact (M := M) I}
variable {D : ActiveChartCompactSupportData P omega}

/--
The active compact-coordinate supports give closed inner-box support for the
M8 localized pieces, once the localized representative alignment is supplied.
-/
theorem localized_tsupport_subset_innerIcc
    (A :
      ActiveChartCompactSupportStrictBufferAlignment P D selectedPartition
        targetImages measureLocalization) :
    ∀ x, x ∈ selectedPartition.active →
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (measureLocalization.localizedInterior.piece x).sourceChart
            (measureLocalization.localizedInterior.piece x).targetChart
            (measureLocalization.localizedInterior.piece x).localizedForm) ⊆
        Set.Icc (D.box x).a (D.box x).b := by
  intro x hx
  have hxP : x ∈ P.active := A.active_subset x hx
  have hcoord :
      tsupport
          (ManifoldForm.transitionPullbackInChart I x x
            (ManifoldForm.localizedForm I (P.partition x) omega)) ⊆
        D.coordSupport x :=
    P.localized_transitionPullback_tsupport_subset_coordSupport_of_base
      omega D.tsupport_subset_coordSupport (i := x) hxP
  have hbox : D.coordSupport x ⊆ Set.Icc (D.box x).a (D.box x).b := by
    intro y hy
    exact (D.box x).subset_Icc (by
      simpa [D.box_K_eq_coordSupport hxP] using hy)
  have hsupport :
      tsupport
          (ManifoldForm.transitionPullbackInChart I x x
            (ManifoldForm.localizedForm I (P.partition x) omega)) ⊆
        Set.Icc (D.box x).a (D.box x).b :=
    hcoord.trans hbox
  change
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (measureLocalization.localizedInterior.piece x).sourceChart
          (measureLocalization.localizedInterior.piece x).targetChart
          (measureLocalization.localizedInterior.piece x).localizedForm) ⊆
      Set.Icc (D.box x).a (D.box x).b
  rw [A.piece_transitionPullback_eq x hx]
  exact hsupport

/--
Build the strict inner-box buffer directly from active compact-coordinate
support data plus explicit M8/selected-partition alignment.
-/
def toLocalizedInteriorFormInnerBoxBuffer
    (A :
      ActiveChartCompactSupportStrictBufferAlignment P D selectedPartition
        targetImages measureLocalization) :
    LocalizedInteriorFormInnerBoxBuffer I omega selectedPartition targetImages
      measureLocalization where
  innerLower := fun x => (D.box x).a
  innerUpper := fun x => (D.box x).b
  localized_tsupport_subset_innerIcc :=
    A.localized_tsupport_subset_innerIcc
  lower_lt_innerLower := A.outer_lower_lt_innerLower
  innerUpper_lt_upper := A.innerUpper_lt_outer_upper

/-- Direct compact-support box buffer from pre-box active compact-support data. -/
def toCompactSupportBoxBuffer
    (A :
      ActiveChartCompactSupportStrictBufferAlignment P D selectedPartition
        targetImages measureLocalization) :
    CompactSupportBoxBuffer I omega selectedPartition targetImages
      measureLocalization :=
  A.toLocalizedInteriorFormInnerBoxBuffer.toCompactSupportBoxBuffer

@[simp]
theorem toLocalizedInteriorFormInnerBoxBuffer_innerLower
    (A :
      ActiveChartCompactSupportStrictBufferAlignment P D selectedPartition
        targetImages measureLocalization) :
    A.toLocalizedInteriorFormInnerBoxBuffer.innerLower =
      fun x => (D.box x).a :=
  rfl

@[simp]
theorem toLocalizedInteriorFormInnerBoxBuffer_innerUpper
    (A :
      ActiveChartCompactSupportStrictBufferAlignment P D selectedPartition
        targetImages measureLocalization) :
    A.toLocalizedInteriorFormInnerBoxBuffer.innerUpper =
      fun x => (D.box x).b :=
  rfl

end ActiveChartCompactSupportStrictBufferAlignment

end CompactSupportStrictBufferFromActive

end Stokes

end
