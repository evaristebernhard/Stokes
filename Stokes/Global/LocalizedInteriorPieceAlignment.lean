import Stokes.Global.LocalizedInteriorConstructors
import Stokes.Global.M8MeasureConstructors

/-!
# Alignment for localized interior pieces

This file isolates the remaining chart-label alignment needed by the strict
buffer route.

The coefficient part is already a theorem: `LocalizedInteriorM8Fields` and
`M8MeasureLocalizationData` record that the localized interior coefficient
family is the selected partition family.  What is not automatic for an
arbitrary `LocalizedInteriorPiece` is that its source and target charts are the
indexing chart `x`.  The small record below exposes exactly those two fields
and derives the `piece_transitionPullback_eq` shape used downstream.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section LocalizedInteriorPieceAlignment

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

namespace LocalizedInteriorM8Fields

variable {P : SelectedBoxPartitionOfUnity I omega}

/--
The localized form stored in an M8-facing interior field is the selected
partition localized form.  This is the part that follows from the existing
constructor equality on coefficient families.
-/
theorem piece_localizedForm_eq_selected
    (D : LocalizedInteriorM8Fields I omega P) (x : M) :
    (D.localizedInterior.piece x).localizedForm =
      ManifoldForm.localizedForm I (P.partition x) omega := by
  dsimp [LocalizedInteriorPiece.localizedForm]
  rw [congrFun D.localized_coefficient x]

/--
If the explicit localized piece charts are the chart label `x`, then the full
transition-pullback alignment follows.
-/
theorem piece_transitionPullback_eq_selected_of_chart_eq
    (D : LocalizedInteriorM8Fields I omega P)
    {x : M}
    (hsource :
      (D.localizedInterior.piece x).sourceChart = x)
    (htarget :
      (D.localizedInterior.piece x).targetChart = x) :
    ManifoldForm.transitionPullbackInChart I
        (D.localizedInterior.piece x).sourceChart
        (D.localizedInterior.piece x).targetChart
        (D.localizedInterior.piece x).localizedForm =
      ManifoldForm.transitionPullbackInChart I x x
        (ManifoldForm.localizedForm I (P.partition x) omega) := by
  rw [hsource, htarget, D.piece_localizedForm_eq_selected x]

end LocalizedInteriorM8Fields

namespace M8MeasureLocalizationData

/--
The localized form stored in `M8MeasureLocalizationData.localizedInterior` is
the selected partition localized form.  This is already implied by the
`localized_coefficient` field.
-/
theorem localizedInterior_piece_localizedForm_eq_selected
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (x : M) :
    (D.localizedInterior.piece x).localizedForm =
      ManifoldForm.localizedForm I (selectedPartition.partition x) omega := by
  dsimp [LocalizedInteriorPiece.localizedForm]
  rw [congrFun D.localized_coefficient x]

/--
The full `piece_transitionPullback_eq` shape follows from the existing
coefficient alignment plus explicit source/target chart alignment.
-/
theorem piece_transitionPullback_eq_selected_of_chart_eq
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    {x : M}
    (hsource :
      (D.localizedInterior.piece x).sourceChart = x)
    (htarget :
      (D.localizedInterior.piece x).targetChart = x) :
    ManifoldForm.transitionPullbackInChart I
        (D.localizedInterior.piece x).sourceChart
        (D.localizedInterior.piece x).targetChart
        (D.localizedInterior.piece x).localizedForm =
      ManifoldForm.transitionPullbackInChart I x x
        (ManifoldForm.localizedForm I (selectedPartition.partition x) omega) := by
  rw [hsource, htarget, D.localizedInterior_piece_localizedForm_eq_selected x]

end M8MeasureLocalizationData

/--
Minimal alignment package for turning an arbitrary M8 localized interior
family into the `x`/`x` chart shape expected by compact-support strict buffers.

The coefficient/localized-form equality is not repeated here; it is already a
field of `M8MeasureLocalizationData`.
-/
structure LocalizedInteriorPieceAlignment
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages) where
  /-- The localized source chart for an active selected label is that label. -/
  sourceChart_eq :
    ∀ x, x ∈ selectedPartition.active →
      (measureLocalization.localizedInterior.piece x).sourceChart = x
  /-- The localized target chart for an active selected label is that label. -/
  targetChart_eq :
    ∀ x, x ∈ selectedPartition.active →
      (measureLocalization.localizedInterior.piece x).targetChart = x

namespace LocalizedInteriorPieceAlignment

variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/--
The exact `piece_transitionPullback_eq` field used by the strict-buffer
alignment records.
-/
theorem piece_transitionPullback_eq
    (A :
      LocalizedInteriorPieceAlignment selectedPartition targetImages
        measureLocalization) :
    ∀ x, x ∈ selectedPartition.active →
      ManifoldForm.transitionPullbackInChart I
          (measureLocalization.localizedInterior.piece x).sourceChart
          (measureLocalization.localizedInterior.piece x).targetChart
          (measureLocalization.localizedInterior.piece x).localizedForm =
        ManifoldForm.transitionPullbackInChart I x x
          (ManifoldForm.localizedForm I (selectedPartition.partition x) omega) := by
  intro x hx
  exact
    measureLocalization.piece_transitionPullback_eq_selected_of_chart_eq
      (A.sourceChart_eq x hx) (A.targetChart_eq x hx)

end LocalizedInteriorPieceAlignment

end LocalizedInteriorPieceAlignment

end Stokes

end
