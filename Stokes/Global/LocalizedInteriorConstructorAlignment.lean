import Stokes.Global.LocalizedInteriorPieceAlignment
import Stokes.Global.CompactSupportPartitionToLocalized
import Stokes.Global.CompactSupportToM8Measure
import Stokes.Global.M8MeasureConstructors

/-!
# Constructor alignment for localized interior pieces

The localized-interior constructors deliberately accept arbitrary
`LocalizedInteriorPiece` values.  They therefore do not imply, by themselves,
that the explicit source and target chart labels stored in each piece are the
indexing chart.  This file packages the minimal extra chart-label equalities
and projects them through the selected-partition and measure constructors.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section LocalizedInteriorConstructorAlignment

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

/--
Minimal chart-label alignment for a selected-partition localized-interior
package.  The localized-form/coefficient equality is already part of
`LocalizedInteriorM8Fields`; this record only adds the source/target chart
equalities that are not forced by the constructors.
-/
structure LocalizedInteriorM8ChartAlignment
    {P : SelectedBoxPartitionOfUnity I omega}
    (localized : LocalizedInteriorM8Fields I omega P) where
  sourceChart_eq :
    forall x, x ∈ P.active ->
      (localized.localizedInterior.piece x).sourceChart = x
  targetChart_eq :
    forall x, x ∈ P.active ->
      (localized.localizedInterior.piece x).targetChart = x

namespace LocalizedInteriorM8ChartAlignment

variable {P : SelectedBoxPartitionOfUnity I omega}
variable {localized : LocalizedInteriorM8Fields I omega P}

/-- The chart-label fields give the transition-pullback shape used downstream. -/
theorem piece_transitionPullback_eq_selected
    (A : LocalizedInteriorM8ChartAlignment localized) :
    forall x, x ∈ P.active ->
      ManifoldForm.transitionPullbackInChart I
          (localized.localizedInterior.piece x).sourceChart
          (localized.localizedInterior.piece x).targetChart
          (localized.localizedInterior.piece x).localizedForm =
        ManifoldForm.transitionPullbackInChart I x x
          (ManifoldForm.localizedForm I (P.partition x) omega) := by
  intro x hx
  exact localized.piece_transitionPullback_eq_selected_of_chart_eq
    (A.sourceChart_eq x hx) (A.targetChart_eq x hx)

/--
Transport chart-label alignment across a measure-localization package whose
localized interior family is known to be this selected one.
-/
def toPieceAlignment
    {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization : M8MeasureLocalizationData I omega P targetImages}
    (A : LocalizedInteriorM8ChartAlignment localized)
    (hlocalized :
      measureLocalization.localizedInterior = localized.localizedInterior) :
    LocalizedInteriorPieceAlignment P targetImages measureLocalization where
  sourceChart_eq := by
    intro x hx
    rw [hlocalized]
    exact A.sourceChart_eq x hx
  targetChart_eq := by
    intro x hx
    rw [hlocalized]
    exact A.targetChart_eq x hx

/-- The transported alignment exposes the downstream transition-pullback field. -/
theorem measure_piece_transitionPullback_eq
    {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization : M8MeasureLocalizationData I omega P targetImages}
    (A : LocalizedInteriorM8ChartAlignment localized)
    (hlocalized :
      measureLocalization.localizedInterior = localized.localizedInterior) :
    forall x, x ∈ P.active ->
      ManifoldForm.transitionPullbackInChart I
          (measureLocalization.localizedInterior.piece x).sourceChart
          (measureLocalization.localizedInterior.piece x).targetChart
          (measureLocalization.localizedInterior.piece x).localizedForm =
        ManifoldForm.transitionPullbackInChart I x x
          (ManifoldForm.localizedForm I (P.partition x) omega) :=
  (A.toPieceAlignment hlocalized).piece_transitionPullback_eq

end LocalizedInteriorM8ChartAlignment

namespace SelectedBoxPartitionOfUnity

variable {P : SelectedBoxPartitionOfUnity I omega}
variable
    {piece :
      forall i : M,
        LocalizedInteriorPiece I omega
          (fun j x => P.partition j x) i}

/-- Raw selected-partition constructor with explicit chart-label alignment. -/
def toLocalizedInteriorM8ChartAlignment
    (P : SelectedBoxPartitionOfUnity I omega)
    (piece :
      forall i : M,
        LocalizedInteriorPiece I omega
          (fun j x => P.partition j x) i)
    (sourceChart_eq :
      forall x, x ∈ P.active -> (piece x).sourceChart = x)
    (targetChart_eq :
      forall x, x ∈ P.active -> (piece x).targetChart = x) :
    LocalizedInteriorM8ChartAlignment (P.toLocalizedInteriorM8Fields piece) where
  sourceChart_eq := by
    intro x hx
    exact sourceChart_eq x hx
  targetChart_eq := by
    intro x hx
    exact targetChart_eq x hx

/-- The raw selected-partition constructor gives the transition-pullback alignment. -/
theorem toLocalizedInteriorM8Fields_piece_transitionPullback_eq
    (P : SelectedBoxPartitionOfUnity I omega)
    (piece :
      forall i : M,
        LocalizedInteriorPiece I omega
          (fun j x => P.partition j x) i)
    (sourceChart_eq :
      forall x, x ∈ P.active -> (piece x).sourceChart = x)
    (targetChart_eq :
      forall x, x ∈ P.active -> (piece x).targetChart = x) :
    forall x, x ∈ P.active ->
      ManifoldForm.transitionPullbackInChart I
          ((P.toLocalizedInteriorM8Fields piece).localizedInterior.piece x).sourceChart
          ((P.toLocalizedInteriorM8Fields piece).localizedInterior.piece x).targetChart
          ((P.toLocalizedInteriorM8Fields piece).localizedInterior.piece x).localizedForm =
        ManifoldForm.transitionPullbackInChart I x x
          (ManifoldForm.localizedForm I (P.partition x) omega) :=
  LocalizedInteriorM8ChartAlignment.piece_transitionPullback_eq_selected
    (P.toLocalizedInteriorM8ChartAlignment piece sourceChart_eq targetChart_eq)

end SelectedBoxPartitionOfUnity

/--
Selected-partition localized input plus the minimal chart-label fields missing
from `SelectedPartitionLocalizedInteriorInput`.
-/
structure SelectedPartitionLocalizedInteriorChartInput
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (P : SelectedBoxPartitionOfUnity I omega) where
  localizedInput : SelectedPartitionLocalizedInteriorInput I omega P
  sourceChart_eq :
    forall x, x ∈ P.active -> (localizedInput.piece x).sourceChart = x
  targetChart_eq :
    forall x, x ∈ P.active -> (localizedInput.piece x).targetChart = x

namespace SelectedPartitionLocalizedInteriorChartInput

variable {P : SelectedBoxPartitionOfUnity I omega}

/-- Forget the chart-label fields and keep the original localized input. -/
def toSelectedPartitionLocalizedInteriorInput
    (D : SelectedPartitionLocalizedInteriorChartInput I omega P) :
    SelectedPartitionLocalizedInteriorInput I omega P :=
  D.localizedInput

/-- M8 localized-interior fields produced by the underlying constructor. -/
def toLocalizedInteriorM8Fields
    (D : SelectedPartitionLocalizedInteriorChartInput I omega P) :
    LocalizedInteriorM8Fields I omega P :=
  D.localizedInput.toLocalizedInteriorM8Fields

/-- Chart-label alignment for the constructor-produced M8 localized fields. -/
def toLocalizedInteriorM8ChartAlignment
    (D : SelectedPartitionLocalizedInteriorChartInput I omega P) :
    LocalizedInteriorM8ChartAlignment D.toLocalizedInteriorM8Fields where
  sourceChart_eq := by
    intro x hx
    exact D.sourceChart_eq x hx
  targetChart_eq := by
    intro x hx
    exact D.targetChart_eq x hx

@[simp]
theorem toLocalizedInteriorM8Fields_localizedInterior
    (D : SelectedPartitionLocalizedInteriorChartInput I omega P) :
    D.toLocalizedInteriorM8Fields.localizedInterior =
      D.localizedInput.toLocalizedInteriorPieces :=
  rfl

/-- Transition-pullback alignment for the selected localized constructor. -/
theorem piece_transitionPullback_eq_selected
    (D : SelectedPartitionLocalizedInteriorChartInput I omega P) :
    forall x, x ∈ P.active ->
      ManifoldForm.transitionPullbackInChart I
          (D.toLocalizedInteriorM8Fields.localizedInterior.piece x).sourceChart
          (D.toLocalizedInteriorM8Fields.localizedInterior.piece x).targetChart
          (D.toLocalizedInteriorM8Fields.localizedInterior.piece x).localizedForm =
        ManifoldForm.transitionPullbackInChart I x x
          (ManifoldForm.localizedForm I (P.partition x) omega) :=
  D.toLocalizedInteriorM8ChartAlignment.piece_transitionPullback_eq_selected

/-- Build the existing `LocalizedInteriorPieceAlignment` after measure localization. -/
def toPieceAlignment
    {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization : M8MeasureLocalizationData I omega P targetImages}
    (D : SelectedPartitionLocalizedInteriorChartInput I omega P)
    (hlocalized :
      measureLocalization.localizedInterior =
        D.toLocalizedInteriorM8Fields.localizedInterior) :
    LocalizedInteriorPieceAlignment P targetImages measureLocalization :=
  D.toLocalizedInteriorM8ChartAlignment.toPieceAlignment hlocalized

end SelectedPartitionLocalizedInteriorChartInput

/--
Compact-support localized input plus the minimal chart-label fields missing from
`CompactSupportPartitionLocalizedInput`.
-/
structure CompactSupportPartitionLocalizedChartInput
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (D : CompactActiveExtendedBoxData I omega) where
  localizedInput : CompactSupportPartitionLocalizedInput I omega D
  sourceChart_eq :
    forall x, x ∈ D.toSelectedBoxPartitionOfUnity.active ->
      (localizedInput.piece x).sourceChart = x
  targetChart_eq :
    forall x, x ∈ D.toSelectedBoxPartitionOfUnity.active ->
      (localizedInput.piece x).targetChart = x

namespace CompactSupportPartitionLocalizedChartInput

variable {D : CompactActiveExtendedBoxData I omega}

/-- Forget the chart-label fields and keep the original compact-support input. -/
def toCompactSupportPartitionLocalizedInput
    (L : CompactSupportPartitionLocalizedChartInput I omega D) :
    CompactSupportPartitionLocalizedInput I omega D :=
  L.localizedInput

/-- M8 localized-interior fields produced by the compact-support constructor. -/
def toLocalizedInteriorM8Fields
    (L : CompactSupportPartitionLocalizedChartInput I omega D) :
    LocalizedInteriorM8Fields I omega D.toSelectedBoxPartitionOfUnity :=
  L.localizedInput.toLocalizedInteriorM8Fields

/-- Chart-label alignment for compact-support constructor-produced M8 fields. -/
def toLocalizedInteriorM8ChartAlignment
    (L : CompactSupportPartitionLocalizedChartInput I omega D) :
    LocalizedInteriorM8ChartAlignment L.toLocalizedInteriorM8Fields where
  sourceChart_eq := by
    intro x hx
    exact L.sourceChart_eq x hx
  targetChart_eq := by
    intro x hx
    exact L.targetChart_eq x hx

@[simp]
theorem toLocalizedInteriorM8Fields_localizedInterior
    (L : CompactSupportPartitionLocalizedChartInput I omega D) :
    L.toLocalizedInteriorM8Fields.localizedInterior =
      L.localizedInput.toLocalizedInteriorPieces :=
  rfl

/-- Transition-pullback alignment for the compact-support localized constructor. -/
theorem piece_transitionPullback_eq_selected
    (L : CompactSupportPartitionLocalizedChartInput I omega D) :
    forall x, x ∈ D.toSelectedBoxPartitionOfUnity.active ->
      ManifoldForm.transitionPullbackInChart I
          (L.toLocalizedInteriorM8Fields.localizedInterior.piece x).sourceChart
          (L.toLocalizedInteriorM8Fields.localizedInterior.piece x).targetChart
          (L.toLocalizedInteriorM8Fields.localizedInterior.piece x).localizedForm =
        ManifoldForm.transitionPullbackInChart I x x
          (ManifoldForm.localizedForm I
            (D.toSelectedBoxPartitionOfUnity.partition x) omega) :=
  L.toLocalizedInteriorM8ChartAlignment.piece_transitionPullback_eq_selected

/-- Build the existing `LocalizedInteriorPieceAlignment` after measure localization. -/
def toPieceAlignment
    {targetImages :
      BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega D.toSelectedBoxPartitionOfUnity
        targetImages}
    (L : CompactSupportPartitionLocalizedChartInput I omega D)
    (hlocalized :
      measureLocalization.localizedInterior =
        L.toLocalizedInteriorM8Fields.localizedInterior) :
    LocalizedInteriorPieceAlignment D.toSelectedBoxPartitionOfUnity
      targetImages measureLocalization :=
  L.toLocalizedInteriorM8ChartAlignment.toPieceAlignment hlocalized

end CompactSupportPartitionLocalizedChartInput

namespace CompactSupportToM8MeasureData

variable
    (D :
      CompactSupportToM8MeasureData
        (α := α) I omega selectedPartition targetImages μ)

/-- Chart-label alignment for the localized fields carried by a measure package. -/
def toLocalizedInteriorPieceAlignment
    (A : LocalizedInteriorM8ChartAlignment D.localized) :
    LocalizedInteriorPieceAlignment selectedPartition targetImages
      D.toM8MeasureLocalizationData :=
  A.toPieceAlignment rfl

/-- Transition-pullback alignment projected from a compact-support measure package. -/
theorem piece_transitionPullback_eq_selected
    (A : LocalizedInteriorM8ChartAlignment D.localized) :
    forall x, x ∈ selectedPartition.active ->
      ManifoldForm.transitionPullbackInChart I
          (D.toM8MeasureLocalizationData.localizedInterior.piece x).sourceChart
          (D.toM8MeasureLocalizationData.localizedInterior.piece x).targetChart
          (D.toM8MeasureLocalizationData.localizedInterior.piece x).localizedForm =
        ManifoldForm.transitionPullbackInChart I x x
          (ManifoldForm.localizedForm I
            (selectedPartition.partition x) omega) :=
  (D.toLocalizedInteriorPieceAlignment A).piece_transitionPullback_eq

/-- Constructor-specific chart-label projection for `ofBoundaryMeasureIntegral`. -/
def ofBoundaryMeasureIntegral_toLocalizedInteriorPieceAlignment
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (A : LocalizedInteriorM8ChartAlignment localized)
    (targetImages_active :
      targetImages.activeCharts = selectedPartition.active)
    (globalBulkIntegral : Real)
    (bulk :
      CompactSupportBulkMeasureData (α := α) (μ := μ)
        localized.localizedInterior targetImages globalBulkIntegral)
    (boundaryPartitionTerm : M -> BoundaryPiece -> Real)
    (boundary :
      BoundaryCompactMeasureFields μ selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm) :
    LocalizedInteriorPieceAlignment selectedPartition targetImages
      ((ofBoundaryMeasureIntegral (α := α) (μ := μ)
        (I := I) (omega := omega)
        (selectedPartition := selectedPartition)
        (targetImages := targetImages)
        localized targetImages_active globalBulkIntegral bulk
        boundaryPartitionTerm boundary).toM8MeasureLocalizationData) :=
  A.toPieceAlignment rfl

end CompactSupportToM8MeasureData

namespace M8BulkMeasureConstructorData

variable
    (D :
      M8BulkMeasureConstructorData
        (I := I) (omega := omega)
        (selectedPartition := selectedPartition)
        (targetImages := targetImages))

/-- View M8 bulk constructor data as selected localized-interior M8 fields. -/
def toLocalizedInteriorM8Fields :
    LocalizedInteriorM8Fields I omega selectedPartition where
  localizedInterior := D.localizedInterior
  localized_active := D.localized_active
  localized_coefficient := D.localized_coefficient

@[simp]
theorem toLocalizedInteriorM8Fields_localizedInterior :
    D.toLocalizedInteriorM8Fields.localizedInterior = D.localizedInterior :=
  rfl

end M8BulkMeasureConstructorData

/--
Minimal chart-label alignment for the localized interior family stored in
`M8BulkMeasureConstructorData`.
-/
structure M8BulkMeasureConstructorChartAlignment
    (D :
      M8BulkMeasureConstructorData
        (I := I) (omega := omega)
        (selectedPartition := selectedPartition)
        (targetImages := targetImages)) where
  sourceChart_eq :
    forall x, x ∈ selectedPartition.active ->
      (D.localizedInterior.piece x).sourceChart = x
  targetChart_eq :
    forall x, x ∈ selectedPartition.active ->
      (D.localizedInterior.piece x).targetChart = x

namespace M8BulkMeasureConstructorChartAlignment

variable
    {D :
      M8BulkMeasureConstructorData
        (I := I) (omega := omega)
        (selectedPartition := selectedPartition)
        (targetImages := targetImages)}

/-- Convert bulk-constructor chart fields to selected localized-interior fields. -/
def toLocalizedInteriorM8ChartAlignment
    (A : M8BulkMeasureConstructorChartAlignment D) :
    LocalizedInteriorM8ChartAlignment D.toLocalizedInteriorM8Fields where
  sourceChart_eq := by
    intro x hx
    exact A.sourceChart_eq x hx
  targetChart_eq := by
    intro x hx
    exact A.targetChart_eq x hx

/-- Chart-label alignment for `M8MeasureLocalizationData.ofBulkAndBoundaryFields`. -/
def toPieceAlignmentOfBulkAndBoundaryFields
    (A : M8BulkMeasureConstructorChartAlignment D)
    (boundaryPartitionTerm : M -> BoundaryPiece -> Real)
    (globalBoundaryIntegral : Real)
    (boundary :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    LocalizedInteriorPieceAlignment selectedPartition targetImages
      (M8MeasureLocalizationData.ofBulkAndBoundaryFields
        (I := I) (omega := omega)
        (selectedPartition := selectedPartition)
        (targetImages := targetImages)
        D boundaryPartitionTerm globalBoundaryIntegral boundary) :=
  A.toLocalizedInteriorM8ChartAlignment.toPieceAlignment rfl

/-- Transition-pullback alignment for `ofBulkAndBoundaryFields`. -/
theorem ofBulkAndBoundaryFields_piece_transitionPullback_eq
    (A : M8BulkMeasureConstructorChartAlignment D)
    (boundaryPartitionTerm : M -> BoundaryPiece -> Real)
    (globalBoundaryIntegral : Real)
    (boundary :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    let measureLocalization :=
      M8MeasureLocalizationData.ofBulkAndBoundaryFields
        (I := I) (omega := omega)
        (selectedPartition := selectedPartition)
        (targetImages := targetImages)
        D boundaryPartitionTerm globalBoundaryIntegral boundary
    forall x, x ∈ selectedPartition.active ->
      ManifoldForm.transitionPullbackInChart I
          (measureLocalization.localizedInterior.piece x).sourceChart
          (measureLocalization.localizedInterior.piece x).targetChart
          (measureLocalization.localizedInterior.piece x).localizedForm =
        ManifoldForm.transitionPullbackInChart I x x
          (ManifoldForm.localizedForm I
            (selectedPartition.partition x) omega) :=
  (A.toPieceAlignmentOfBulkAndBoundaryFields boundaryPartitionTerm
    globalBoundaryIntegral boundary).piece_transitionPullback_eq

end M8BulkMeasureConstructorChartAlignment

end LocalizedInteriorConstructorAlignment

end Stokes

end
