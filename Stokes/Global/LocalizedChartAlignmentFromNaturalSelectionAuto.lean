import Stokes.Global.NaturalStrictAlignmentFromFiniteSelectionAuto

/-!
# Localized chart alignment from natural finite-active selections

This file removes one layer of endpoint plumbing around
`LocalizedInteriorM8ChartAlignment`.

A natural finite-active chart-box selection fixes the selected partition.  The
remaining localized-interior family is still genuine local Stokes data, but in
the common constructor route it is known to be the selected localized family
up to a recorded equality.  From that equality, plus the source/target chart
labels stored on the localized pieces, we can generate the chart-alignment
record consumed by the strict endpoint route.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section LocalizedChartAlignmentFromNaturalSelectionAuto

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {alpha : Type a} [TopologicalSpace alpha] [MeasurableSpace alpha]
variable [OpensMeasurableSpace alpha] [T2Space alpha]
variable {mu : Measure alpha} [IsFiniteMeasureOnCompacts mu]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {rho : SmoothPartitionOfUnity M I M univ}
variable [IsManifold I 1 M]

namespace LocalizedInteriorM8ChartAlignment

variable {P : SelectedBoxPartitionOfUnity I omega}
variable {localized localized' : LocalizedInteriorM8Fields I omega P}

/--
Transport chart-label alignment across equality of the localized-interior
families.  This is the reusable cast needed when a bulk/measure constructor
stores the same localized pieces behind a different record wrapper.
-/
def ofLocalizedInteriorEq
    (hlocalized :
      localized.localizedInterior = localized'.localizedInterior)
    (A : LocalizedInteriorM8ChartAlignment localized') :
    LocalizedInteriorM8ChartAlignment localized where
  sourceChart_eq := by
    intro x hx
    rw [hlocalized]
    exact A.sourceChart_eq x hx
  targetChart_eq := by
    intro x hx
    rw [hlocalized]
    exact A.targetChart_eq x hx

@[simp]
theorem ofLocalizedInteriorEq_sourceChart_eq
    (hlocalized :
      localized.localizedInterior = localized'.localizedInterior)
    (A : LocalizedInteriorM8ChartAlignment localized') :
    (ofLocalizedInteriorEq hlocalized A).sourceChart_eq =
      fun x hx => by
        rw [hlocalized]
        exact A.sourceChart_eq x hx := by
  rfl

end LocalizedInteriorM8ChartAlignment

namespace NaturalFiniteActiveChartBoxSelectionData

variable
    (D : NaturalFiniteActiveChartBoxSelectionData I omega rho)

/-- The compact-active extended boxes fixed by the natural finite selection. -/
abbrev compactActiveExtendedBoxData :
    CompactActiveExtendedBoxData I omega :=
  D.selection.compactActiveExtendedBoxData D.smoothness

/--
Specialized constructor route: the localized pieces are built directly from
the selected partition attached to `D`, and their source/target chart labels
are the selected labels on active indices.
-/
def localizedChartAlignmentOfPieces
    (piece :
      forall i : M,
        LocalizedInteriorPiece I omega
          (fun j x => D.selectedPartition.partition j x) i)
    (sourceChart_eq :
      forall x, x ∈ D.selectedPartition.active -> (piece x).sourceChart = x)
    (targetChart_eq :
      forall x, x ∈ D.selectedPartition.active -> (piece x).targetChart = x) :
    LocalizedInteriorM8ChartAlignment
      (D.selectedPartition.toLocalizedInteriorM8Fields piece) :=
  D.selectedPartition.toLocalizedInteriorM8ChartAlignment
    piece sourceChart_eq targetChart_eq

/--
Generate chart alignment for an arbitrary localized M8 field once it is known
to carry the same localized pieces as the selected-partition constructor.
-/
def localizedChartAlignmentOfLocalizedInteriorEq
    {localized : LocalizedInteriorM8Fields I omega D.selectedPartition}
    (piece :
      forall i : M,
        LocalizedInteriorPiece I omega
          (fun j x => D.selectedPartition.partition j x) i)
    (hlocalized :
      localized.localizedInterior =
        (D.selectedPartition.toLocalizedInteriorM8Fields piece).localizedInterior)
    (sourceChart_eq :
      forall x, x ∈ D.selectedPartition.active -> (piece x).sourceChart = x)
    (targetChart_eq :
      forall x, x ∈ D.selectedPartition.active -> (piece x).targetChart = x) :
    LocalizedInteriorM8ChartAlignment localized :=
  LocalizedInteriorM8ChartAlignment.ofLocalizedInteriorEq hlocalized
    (D.localizedChartAlignmentOfPieces piece sourceChart_eq targetChart_eq)

/--
Variant for the existing selected-partition chart-input wrapper from
`LocalizedInteriorConstructorAlignment`.
-/
def localizedChartAlignmentOfSelectedPartitionChartInput
    {localized : LocalizedInteriorM8Fields I omega D.selectedPartition}
    (L : SelectedPartitionLocalizedInteriorChartInput I omega D.selectedPartition)
    (hlocalized :
      localized.localizedInterior = L.toLocalizedInteriorM8Fields.localizedInterior) :
    LocalizedInteriorM8ChartAlignment localized :=
  LocalizedInteriorM8ChartAlignment.ofLocalizedInteriorEq hlocalized
    L.toLocalizedInteriorM8ChartAlignment

/--
Variant for compact-active localized inputs over the compact boxes selected by
`D`.  This is useful when the localized pieces are constructed from selected
chart boxes first and only later moved into the bulk package.
-/
def localizedChartAlignmentOfCompactSupportChartInput
    {localized : LocalizedInteriorM8Fields I omega D.selectedPartition}
    (L :
      CompactSupportPartitionLocalizedChartInput I omega
        D.compactActiveExtendedBoxData)
    (hlocalized :
      localized.localizedInterior = L.toLocalizedInteriorM8Fields.localizedInterior) :
    LocalizedInteriorM8ChartAlignment localized :=
  LocalizedInteriorM8ChartAlignment.ofLocalizedInteriorEq hlocalized
    L.toLocalizedInteriorM8ChartAlignment

end NaturalFiniteActiveChartBoxSelectionData

/--
Localized-piece equality data specialized to a natural finite-active selection.
This is the non-endpoint-facing package callers can produce from their actual
localized M8 pieces.
-/
structure NaturalFiniteActiveLocalizedPieceEqData
    (D : NaturalFiniteActiveChartBoxSelectionData I omega rho)
    (localized : LocalizedInteriorM8Fields I omega D.selectedPartition) where
  piece :
    forall i : M,
      LocalizedInteriorPiece I omega
        (fun j x => D.selectedPartition.partition j x) i
  localizedInterior_eq :
    localized.localizedInterior =
      (D.selectedPartition.toLocalizedInteriorM8Fields piece).localizedInterior
  sourceChart_eq :
    forall x, x ∈ D.selectedPartition.active -> (piece x).sourceChart = x
  targetChart_eq :
    forall x, x ∈ D.selectedPartition.active -> (piece x).targetChart = x

namespace NaturalFiniteActiveLocalizedPieceEqData

variable {D : NaturalFiniteActiveChartBoxSelectionData I omega rho}
variable {localized : LocalizedInteriorM8Fields I omega D.selectedPartition}
variable
    (A : NaturalFiniteActiveLocalizedPieceEqData D localized)

/-- The constructor-side localized M8 fields named by the equality package. -/
abbrev constructorLocalized :
    LocalizedInteriorM8Fields I omega D.selectedPartition :=
  D.selectedPartition.toLocalizedInteriorM8Fields A.piece

/-- Alignment for the constructor-side localized M8 fields. -/
def constructorChartAlignment :
    LocalizedInteriorM8ChartAlignment A.constructorLocalized :=
  D.localizedChartAlignmentOfPieces
    A.piece A.sourceChart_eq A.targetChart_eq

/-- Alignment transported to the actual localized M8 fields. -/
def toLocalizedInteriorM8ChartAlignment :
    LocalizedInteriorM8ChartAlignment localized :=
  D.localizedChartAlignmentOfLocalizedInteriorEq
    A.piece A.localizedInterior_eq A.sourceChart_eq A.targetChart_eq

/-- The transition-pullback shape required downstream. -/
theorem piece_transitionPullback_eq_selected
    (A : NaturalFiniteActiveLocalizedPieceEqData D localized) :
    forall x, x ∈ D.selectedPartition.active ->
      ManifoldForm.transitionPullbackInChart I
          (localized.localizedInterior.piece x).sourceChart
          (localized.localizedInterior.piece x).targetChart
          (localized.localizedInterior.piece x).localizedForm =
        ManifoldForm.transitionPullbackInChart I x x
          (ManifoldForm.localizedForm I
            (D.selectedPartition.partition x) omega) :=
  LocalizedInteriorM8ChartAlignment.piece_transitionPullback_eq_selected
    (NaturalFiniteActiveLocalizedPieceEqData.toLocalizedInteriorM8ChartAlignment A)

/-- Constructor from the existing selected-partition chart-input wrapper. -/
def ofSelectedPartitionChartInput
    (L : SelectedPartitionLocalizedInteriorChartInput I omega D.selectedPartition)
    (hlocalized :
      localized.localizedInterior = L.toLocalizedInteriorM8Fields.localizedInterior) :
    NaturalFiniteActiveLocalizedPieceEqData D localized where
  piece := L.localizedInput.piece
  localizedInterior_eq := by
    simpa [SelectedPartitionLocalizedInteriorChartInput.toLocalizedInteriorM8Fields,
      SelectedPartitionLocalizedInteriorInput.toLocalizedInteriorM8Fields]
      using hlocalized
  sourceChart_eq := L.sourceChart_eq
  targetChart_eq := L.targetChart_eq

/-- Constructor from compact-active chart input over the boxes selected by `D`. -/
def ofCompactSupportChartInput
    (L :
      CompactSupportPartitionLocalizedChartInput I omega
        D.compactActiveExtendedBoxData)
    (hlocalized :
      localized.localizedInterior = L.toLocalizedInteriorM8Fields.localizedInterior) :
    NaturalFiniteActiveLocalizedPieceEqData D localized where
  piece := L.localizedInput.piece
  localizedInterior_eq := by
    simpa [CompactSupportPartitionLocalizedChartInput.toLocalizedInteriorM8Fields,
      CompactSupportPartitionLocalizedInput.toLocalizedInteriorM8Fields,
      CompactSupportPartitionLocalizedInput.toSelectedPartitionInput]
      using hlocalized
  sourceChart_eq := L.sourceChart_eq
  targetChart_eq := L.targetChart_eq

end NaturalFiniteActiveLocalizedPieceEqData

namespace NaturalFiniteActiveChartBoxSelectionData

variable
    (D : NaturalFiniteActiveChartBoxSelectionData I omega rho)
variable
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (targetImageInput :
      M8TargetImageInput I omega D.selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := alpha) (μ := mu)
        D.selectedPartition targetImageInput.targetImages globalBulkIntegral)
    (boundaryTarget :
      CanonicalBoundaryTargetCompactSupportInput
        (α := alpha) targetImageInput mu)

/--
Strict-alignment data where the localized chart alignment is generated from
piece equality data instead of being supplied as a raw endpoint field.
-/
def toStrictAlignmentDataOfLocalizedPieces
    (localizedPieces :
      NaturalFiniteActiveLocalizedPieceEqData D bulk.localized)
    (strictMargins :
      SelectedBoxStrictMarginData D.selectedPartition
        targetImageInput.targetImages
        (boundaryTarget.toMeasureBuilderData bulk).toM8MeasureLocalizationData) :
    NaturalFiniteActiveStrictAlignmentData
      (alpha := alpha) I omega BoundaryPiece rho mu :=
  D.toStrictAlignmentData
    orientedBoundaryAtlas targetImageInput bulk boundaryTarget
    localizedPieces.toLocalizedInteriorM8ChartAlignment strictMargins

/--
Strict-builder alignment generated from localized-piece equality data and the
existing selected-box strict margins.
-/
def toNaturalMeasureStrictBuilderAlignmentOfLocalizedPieces
    (localizedPieces :
      NaturalFiniteActiveLocalizedPieceEqData D bulk.localized)
    (strictMargins :
      SelectedBoxStrictMarginData D.selectedPartition
        targetImageInput.targetImages
        (boundaryTarget.toMeasureBuilderData bulk).toM8MeasureLocalizationData) :
    NaturalMeasureStrictBuilderAlignment targetImageInput
      (boundaryTarget.toMeasureBuilderData bulk) D.compactActiveBoxData :=
  D.toNaturalMeasureStrictBuilderAlignment
    orientedBoundaryAtlas targetImageInput bulk boundaryTarget
    localizedPieces.toLocalizedInteriorM8ChartAlignment strictMargins

/--
End-to-end input generated from localized-piece equality data and selected-box
strict margins.
-/
def toNaturalCompactSupportEndToEndInputOfLocalizedPieces
    (localizedPieces :
      NaturalFiniteActiveLocalizedPieceEqData D bulk.localized)
    (strictMargins :
      SelectedBoxStrictMarginData D.selectedPartition
        targetImageInput.targetImages
        (boundaryTarget.toMeasureBuilderData bulk).toM8MeasureLocalizationData) :
    NaturalCompactSupportEndToEndInput
      (α := alpha) I omega BoundaryPiece mu :=
  D.toNaturalCompactSupportEndToEndInput
    orientedBoundaryAtlas targetImageInput bulk boundaryTarget
    localizedPieces.toLocalizedInteriorM8ChartAlignment strictMargins

/--
Canonical Stokes from natural finite-active chart boxes, localized-piece
equality data, and selected-box strict margins.
-/
theorem canonical_stokes_ofLocalizedPieces
    (localizedPieces :
      NaturalFiniteActiveLocalizedPieceEqData D bulk.localized)
    (strictMargins :
      SelectedBoxStrictMarginData D.selectedPartition
        targetImageInput.targetImages
        (boundaryTarget.toMeasureBuilderData bulk).toM8MeasureLocalizationData) :
    ((D.toNaturalCompactSupportEndToEndInputOfLocalizedPieces
        orientedBoundaryAtlas targetImageInput bulk boundaryTarget
        localizedPieces strictMargins)
        |>.toNaturalCompactSupportStokesInput
        |>.canonicalIntegralInterface
        |>.stokesStatement) :=
  (D.toStrictAlignmentDataOfLocalizedPieces
    orientedBoundaryAtlas targetImageInput bulk boundaryTarget
    localizedPieces strictMargins)
    |>.canonical_stokes

end NaturalFiniteActiveChartBoxSelectionData

end LocalizedChartAlignmentFromNaturalSelectionAuto

end Stokes

end
