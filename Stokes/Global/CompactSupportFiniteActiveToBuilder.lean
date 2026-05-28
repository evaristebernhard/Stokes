import Stokes.Global.CompactSupportFiniteActiveSelection
import Stokes.Global.CompactSupportPartitionToLocalized
import Stokes.Global.M8InputBuilder

/-!
# Compact-support finite-active selections to M8 builders

This file connects the compact-support finite-active chart-box selection layer
to the M8 input builder layer.

The construction remains a bookkeeping adapter.  It turns a
`CompactSupportFiniteActiveSelection` plus smoothness data into the selected
partition used by `M8InputBuilderData`, then packages the independently proved
localized-interior, measure-localization, target-image, and artificial-face
inputs around that selected partition.
-/

noncomputable section

open Set
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportFiniteActiveToBuilder

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

namespace CompactSupportFiniteActiveSelection

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {ρ : SmoothPartitionOfUnity M I M univ}
variable {K : Set M} {hK : IsCompact K}

/--
Localized-interior input canonically indexed by the selected partition coming
from a compact-support finite-active selection.
-/
def toCompactSupportPartitionLocalizedInput
    (S : CompactSupportFiniteActiveSelection (I := I) ρ K hK omega)
    (smoothness : ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega)
    (piece :
      forall i : M,
        LocalizedInteriorPiece I omega
          (fun j x => (S.selectedBoxPartitionOfUnity smoothness).partition j x) i) :
    CompactSupportPartitionLocalizedInput I omega
      (S.compactActiveExtendedBoxData smoothness) where
  piece := piece

@[simp]
theorem toCompactSupportPartitionLocalizedInput_piece
    (S : CompactSupportFiniteActiveSelection (I := I) ρ K hK omega)
    (smoothness : ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega)
    (piece :
      forall i : M,
        LocalizedInteriorPiece I omega
          (fun j x => (S.selectedBoxPartitionOfUnity smoothness).partition j x) i) :
    (S.toCompactSupportPartitionLocalizedInput smoothness piece).piece = piece :=
  rfl

@[simp]
theorem toCompactSupportPartitionLocalizedInput_toLocalizedInteriorM8Fields
    (S : CompactSupportFiniteActiveSelection (I := I) ρ K hK omega)
    (smoothness : ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega)
    (piece :
      forall i : M,
        LocalizedInteriorPiece I omega
          (fun j x => (S.selectedBoxPartitionOfUnity smoothness).partition j x) i) :
    (S.toCompactSupportPartitionLocalizedInput smoothness piece).toLocalizedInteriorM8Fields =
      (S.selectedBoxPartitionOfUnity smoothness).toLocalizedInteriorM8Fields piece :=
  rfl

end CompactSupportFiniteActiveSelection

/--
Natural M8-builder input starting from a compact-support finite-active
selection.

The fields `selection` and `smoothness` determine the selected partition and
selected boxes.  All genuinely analytic or geometric statements downstream of
that selection remain explicit fields: local pieces, measure localization,
target images, and artificial-face cancellation.
-/
structure CompactSupportFiniteActiveBuilderData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (K : Set M) (hK : IsCompact K) where
  /-- Compactly supported smooth input form. -/
  formData : CompactlySupportedSmoothFormData I omega
  /-- The compact control set is the support set recorded by `formData`. -/
  supportSet_eq : K = formData.supportSet
  /-- Finite active chart selection and compact coordinate boxes. -/
  selection : CompactSupportFiniteActiveSelection (I := I) ρ K hK omega
  /-- Smoothness neighborhoods upgrading selected boxes to extended boxes. -/
  smoothness :
    ActiveCompactBoxSmoothness selection.finiteActive selection.supportData.box omega
  /-- Explicit oriented boundary-chart atlas data. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Boundary target-image data over the selected partition. -/
  targetImageInput :
    M8TargetImageInput I omega
      (selection.selectedBoxPartitionOfUnity smoothness)
      orientedBoundaryAtlas BoundaryPiece
  /-- Localized interior fields over the compact-support selected boxes. -/
  localizedInput :
    CompactSupportPartitionLocalizedInput I omega
      (selection.compactActiveExtendedBoxData smoothness)
  /-- Measure-localization fields indexed by the target-image family. -/
  measureLocalization :
    M8MeasureLocalizationData I omega
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages
  /-- The measure package uses the localized interior family recorded above. -/
  measure_localizedInterior :
    measureLocalization.localizedInterior =
      localizedInput.toLocalizedInteriorM8Fields.localizedInterior
  /-- The target-image assembly boundary term is the measure boundary term. -/
  measureLocalization_boundaryTerm :
    targetImageInput.assembly.boundaryPartitionTerm =
      measureLocalization.boundaryPartitionTerm
  /-- Artificial-face cancellation fields indexed by the same M8 data. -/
  artificial :
    M8ArtificialFaceFields I omega BoundaryPiece
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages measureLocalization

namespace CompactSupportFiniteActiveBuilderData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {ρ : SmoothPartitionOfUnity M I M univ}
variable {K : Set M} {hK : IsCompact K}

/-- Compact active extended-box data determined by the finite-active selection. -/
abbrev compactActiveExtendedBoxData
    (D :
      CompactSupportFiniteActiveBuilderData I omega BoundaryPiece ρ K hK) :
    CompactActiveExtendedBoxData I omega :=
  D.selection.compactActiveExtendedBoxData D.smoothness

/-- Selected partition determined by the finite-active selection. -/
abbrev selectedPartition
    (D :
      CompactSupportFiniteActiveBuilderData I omega BoundaryPiece ρ K hK) :
    SelectedBoxPartitionOfUnity I omega :=
  D.selection.selectedBoxPartitionOfUnity D.smoothness

/-- Localized-interior M8 fields determined by the localized input. -/
abbrev localizedInterior
    (D :
      CompactSupportFiniteActiveBuilderData I omega BoundaryPiece ρ K hK) :
    LocalizedInteriorM8Fields I omega D.selectedPartition :=
  D.localizedInput.toLocalizedInteriorM8Fields

/-- Target-image family determined by the target-image input. -/
abbrev targetImages
    (D :
      CompactSupportFiniteActiveBuilderData I omega BoundaryPiece ρ K hK) :
    BoundaryPieceFamilyInput I omega M BoundaryPiece :=
  D.targetImageInput.targetImages

/-- Support-set compatibility in the exact shape expected by `M8InputBuilderData`. -/
theorem selectedPartition_supportSet
    (D :
      CompactSupportFiniteActiveBuilderData I omega BoundaryPiece ρ K hK) :
    D.selectedPartition.K = D.formData.supportSet := by
  simpa [selectedPartition] using D.supportSet_eq

/-- Convert finite-active compact-support builder data to the general M8 builder. -/
def toM8InputBuilderData
    (D :
      CompactSupportFiniteActiveBuilderData I omega BoundaryPiece ρ K hK) :
    M8InputBuilderData I omega BoundaryPiece where
  formData := D.formData
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  selectedPartition := D.selectedPartition
  selectedPartition_supportSet := D.selectedPartition_supportSet
  targetImageInput := D.targetImageInput
  localizedInterior := D.localizedInterior
  measureLocalization := D.measureLocalization
  measure_localizedInterior := D.measure_localizedInterior
  measureLocalization_boundaryTerm := D.measureLocalization_boundaryTerm
  artificial := D.artificial

@[simp]
theorem toM8InputBuilderData_formData
    (D :
      CompactSupportFiniteActiveBuilderData I omega BoundaryPiece ρ K hK) :
    D.toM8InputBuilderData.formData = D.formData :=
  rfl

@[simp]
theorem toM8InputBuilderData_selectedPartition
    (D :
      CompactSupportFiniteActiveBuilderData I omega BoundaryPiece ρ K hK) :
    D.toM8InputBuilderData.selectedPartition = D.selectedPartition :=
  rfl

@[simp]
theorem toM8InputBuilderData_targetImages
    (D :
      CompactSupportFiniteActiveBuilderData I omega BoundaryPiece ρ K hK) :
    D.toM8InputBuilderData.targetImages = D.targetImages :=
  rfl

@[simp]
theorem toM8InputBuilderData_localizedInterior
    (D :
      CompactSupportFiniteActiveBuilderData I omega BoundaryPiece ρ K hK) :
    D.toM8InputBuilderData.localizedInterior = D.localizedInterior :=
  rfl

@[simp]
theorem toM8InputBuilderData_measureLocalization
    (D :
      CompactSupportFiniteActiveBuilderData I omega BoundaryPiece ρ K hK) :
    D.toM8InputBuilderData.measureLocalization = D.measureLocalization :=
  rfl

/-- M8 Stokes exposed from the compact-support finite-active builder input. -/
theorem stokes
    [IsManifold I 1 M]
    (D :
      CompactSupportFiniteActiveBuilderData I omega BoundaryPiece ρ K hK) :
    D.measureLocalization.bulkMeasureIntegral =
      D.measureLocalization.boundaryMeasureIntegral :=
  D.toM8InputBuilderData.stokes

/-- Represented-integral M8 Stokes from the compact-support finite-active builder. -/
theorem represented_stokes
    [IsManifold I 1 M]
    (D :
      CompactSupportFiniteActiveBuilderData I omega BoundaryPiece ρ K hK) :
    D.measureLocalization.globalBulkIntegral =
      D.measureLocalization.globalBoundaryIntegral :=
  D.toM8InputBuilderData.represented_stokes

end CompactSupportFiniteActiveBuilderData

end CompactSupportFiniteActiveToBuilder

end Stokes

end
