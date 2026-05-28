import Stokes.Global.NaturalCompactSupportBulkAuto

/-!
# Automatic measure-local box term constructors

This module records the shortest current constructor path to
`MeasureLocalBoxTermAPI`: choose the measure-local scalar terms to be the
already-recorded project-local box terms.  With that canonical choice, the
box-term API is definitionally available.

The second half exposes a compact-support bulk-auto input that uses this
canonical choice, so callers no longer have to provide `measureTerms` and
`measureBox` as separate fields.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section MeasureLocalBoxTermAuto

universe u w ιu cb pb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type ιu}
variable {BoundaryChart : Type cb} {BoundaryPiece : Type pb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable
    (interior : LocalizedInteriorPieces (ι := ι) I ω)
    (boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece)

/-- The finite project-local box sum used by the canonical measure-term choice. -/
def projectLocalBoxMeasureSum : Real :=
  (Finset.sum interior.active fun i => interior.bulkTerm i) +
    BoundaryPieceFamilyInput.boundaryBulkSum boundary

namespace BulkMeasureLocalizationTermFields

/--
Canonical measure-local terms: each scalar measure term is defined to be the
corresponding project-local box term.
-/
def ofProjectLocalBoxTerms :
    BulkMeasureLocalizationTermFields interior boundary where
  globalBulkIntegral := projectLocalBoxMeasureSum interior boundary
  bulkMeasureIntegral := projectLocalBoxMeasureSum interior boundary
  interiorMeasureTerm := fun i => interior.bulkTerm i
  boundaryMeasureTerm := fun x q =>
    BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q
  globalBulkIntegral_eq_bulkMeasureIntegral := rfl
  bulkMeasureIntegral_eq_measureSum := by
    simp [projectLocalBoxMeasureSum, BoundaryPieceFamilyInput.boundaryBulkSum]

@[simp]
theorem ofProjectLocalBoxTerms_globalBulkIntegral :
    (ofProjectLocalBoxTerms interior boundary).globalBulkIntegral =
      projectLocalBoxMeasureSum interior boundary :=
  rfl

@[simp]
theorem ofProjectLocalBoxTerms_bulkMeasureIntegral :
    (ofProjectLocalBoxTerms interior boundary).bulkMeasureIntegral =
      projectLocalBoxMeasureSum interior boundary :=
  rfl

@[simp]
theorem ofProjectLocalBoxTerms_interiorMeasureTerm
    (i : ι) :
    (ofProjectLocalBoxTerms interior boundary).interiorMeasureTerm i =
      interior.bulkTerm i :=
  rfl

@[simp]
theorem ofProjectLocalBoxTerms_boundaryMeasureTerm
    (x : BoundaryChart) (q : BoundaryPiece) :
    (ofProjectLocalBoxTerms interior boundary).boundaryMeasureTerm x q =
      BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q :=
  rfl

/-- The canonical project-local measure terms provide `MeasureLocalBoxTermAPI`. -/
def projectLocalBoxTermAPI :
    MeasureLocalBoxTermAPI (ofProjectLocalBoxTerms interior boundary) where
  interiorMeasureTerm_eq_boxTerm := by
    intro i _hi
    rfl
  boundaryMeasureTerm_eq_boxTerm := by
    intro x _hx q _hq
    rfl

@[simp]
theorem projectLocalBoxTermAPI_interior_eq
    {i : ι} (hi : i ∈ interior.active) :
    (projectLocalBoxTermAPI interior boundary).interior_eq hi =
      (rfl :
        (ofProjectLocalBoxTerms interior boundary).interiorMeasureTerm i =
          interior.bulkTerm i) := by
  rfl

@[simp]
theorem projectLocalBoxTermAPI_boundary_eq
    {x : BoundaryChart} (hx : x ∈ boundary.activeCharts)
    {q : BoundaryPiece} (hq : q ∈ boundary.boundaryPieces x) :
    (projectLocalBoxTermAPI interior boundary).boundary_eq hx hq =
      (rfl :
        (ofProjectLocalBoxTerms interior boundary).boundaryMeasureTerm x q =
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q) := by
  rfl

end BulkMeasureLocalizationTermFields

end MeasureLocalBoxTermAuto

section NaturalCompactSupportBulkProjectLocalAuto

universe u w b ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {ρ : SmoothPartitionOfUnity M I M univ}
variable {μ : Measure (Fin (n + 1) → Real)}
variable [IsFiniteMeasureOnCompacts μ]

/--
Bulk-auto compact-support input with canonical project-local measure terms.

Compared with `NaturalCompactSupportBulkAutoCollapsedInput`, this removes the
manual `measureTerms` and `measureBox` fields.  The exterior-derivative a.e.
package is indexed by the canonical measure terms constructed from the
localized interior family and target-image boundary family.
-/
structure NaturalCompactSupportBulkProjectLocalAutoCollapsedInput
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (μ : Measure (Fin (n + 1) → Real))
    [IsFiniteMeasureOnCompacts μ]
    [IsManifold I 1 M] where
  /-- Compactly supported smooth input form. -/
  formData : CompactlySupportedSmoothFormData I omega
  /-- Compact-support finite active chart selection over `formData.supportSet`. -/
  selection :
    CompactSupportFiniteActiveSelection
      (I := I) ρ formData.supportSet formData.isCompact_supportSet omega
  /-- Smoothness data upgrading selected compact boxes to extended boxes. -/
  smoothness :
    ActiveCompactBoxSmoothness selection.finiteActive
      selection.supportData.box omega
  /-- Project-local oriented boundary chart atlas data. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Boundary target-image input over the selected partition. -/
  targetImageInput :
    M8TargetImageInput I omega
      (selection.selectedBoxPartitionOfUnity smoothness)
      orientedBoundaryAtlas BoundaryPiece
  /-- Localized interior package used by the canonical bulk route. -/
  localized :
    LocalizedInteriorM8Fields I omega
      (selection.selectedBoxPartitionOfUnity smoothness)
  /-- Exterior-derivative a.e. reconstruction for the selected pieces. -/
  extDerivAE :
    BulkIntegrandAEFromPartitionData
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages localized
      (BulkMeasureLocalizationTermFields.ofProjectLocalBoxTerms
        localized.localizedInterior targetImageInput.targetImages)
  /-- Local non-integral facts for canonical selected bulk pieces. -/
  bulkLocalFacts :
    SelectedPartitionBulkCanonicalLocalFacts
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages localized
  /-- The selected bulk measure is the volume measure. -/
  measure_eq_volume : μ = volume
  /-- Boundary finite-sum/support and target-COV measure input. -/
  boundarySupportCOV :
    BoundaryPieceSupportFiniteSumTargetCOVInput
      (α := Fin (n + 1) → Real) targetImageInput μ
  /-- The selected localized pieces use the selected chart label as source/target. -/
  localizedChartAlignment :
    LocalizedInteriorM8ChartAlignment localized
  /-- Strict outer margins around the selected boxes for the produced measure data. -/
  strictMargins :
    SelectedBoxStrictMarginData
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages
      ((boundarySupportCOV.toCanonicalBoundaryTargetCompactSupportInput)
        |>.toMeasureBuilderData
          ((selectedPartitionBulkExtDerivInputOfVolumeMeasureLocalBoxTermAPI
              (ExtInteriorPiece := ExtInteriorPiece)
              (ExtBoundaryPiece := ExtBoundaryPiece)
              (selection.selectedBoxPartitionOfUnity smoothness)
              targetImageInput.targetImages localized bulkLocalFacts
              (BulkMeasureLocalizationTermFields.ofProjectLocalBoxTerms
                localized.localizedInterior targetImageInput.targetImages)
              extDerivAE measure_eq_volume
              (BulkMeasureLocalizationTermFields.projectLocalBoxTermAPI
                localized.localizedInterior targetImageInput.targetImages))
            |>.toBulkMeasureFromPartitionData)
        |>.toM8MeasureLocalizationData)

namespace NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

variable [IsManifold I 1 M]
variable
    (D :
      NaturalCompactSupportBulkProjectLocalAutoCollapsedInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece ρ μ)

/-- The selected partition determined by the canonical support selection. -/
abbrev selectedPartition : SelectedBoxPartitionOfUnity I omega :=
  D.selection.selectedBoxPartitionOfUnity D.smoothness

/-- Canonical measure-local terms induced by project-local box terms. -/
def measureTerms :
    BulkMeasureLocalizationTermFields
      D.localized.localizedInterior D.targetImageInput.targetImages :=
  BulkMeasureLocalizationTermFields.ofProjectLocalBoxTerms
    D.localized.localizedInterior D.targetImageInput.targetImages

/-- The automatically available measure-local/project-local box API. -/
def measureBox :
    MeasureLocalBoxTermAPI D.measureTerms :=
  BulkMeasureLocalizationTermFields.projectLocalBoxTermAPI
    D.localized.localizedInterior D.targetImageInput.targetImages

@[simp]
theorem measureTerms_globalBulkIntegral :
    D.measureTerms.globalBulkIntegral =
      projectLocalBoxMeasureSum
        D.localized.localizedInterior D.targetImageInput.targetImages :=
  rfl

@[simp]
theorem measureBox_interior_eq
    {i : M} (hi : i ∈ D.localized.localizedInterior.active) :
    D.measureBox.interior_eq hi =
      (rfl :
        D.measureTerms.interiorMeasureTerm i =
          D.localized.localizedInterior.bulkTerm i) := by
  rfl

@[simp]
theorem measureBox_boundary_eq
    {x : M} (hx : x ∈ D.targetImageInput.targetImages.activeCharts)
    {q : BoundaryPiece} (hq : q ∈ D.targetImageInput.targetImages.boundaryPieces x) :
    D.measureBox.boundary_eq hx hq =
      (rfl :
        D.measureTerms.boundaryMeasureTerm x q =
          BoundaryPieceFamilyInput.boundaryBulkTerm
            D.targetImageInput.targetImages x q) := by
  rfl

/-- Forget the canonical measure-term choice into the existing bulk-auto input. -/
def toBulkAutoCollapsedInput :
    NaturalCompactSupportBulkAutoCollapsedInput
      ExtInteriorPiece ExtBoundaryPiece
      I omega BoundaryPiece ρ μ where
  formData := D.formData
  selection := D.selection
  smoothness := D.smoothness
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  targetImageInput := D.targetImageInput
  localized := D.localized
  measureTerms := D.measureTerms
  extDerivAE := D.extDerivAE
  bulkLocalFacts := D.bulkLocalFacts
  measure_eq_volume := D.measure_eq_volume
  measureBox := D.measureBox
  boundarySupportCOV := D.boundarySupportCOV
  localizedChartAlignment := D.localizedChartAlignment
  strictMargins := by
    simpa [measureTerms, measureBox] using D.strictMargins

@[simp]
theorem toBulkAutoCollapsedInput_measureTerms :
    D.toBulkAutoCollapsedInput.measureTerms = D.measureTerms :=
  rfl

@[simp]
theorem toBulkAutoCollapsedInput_measureBox :
    D.toBulkAutoCollapsedInput.measureBox = D.measureBox :=
  rfl

/--
Bulk-auto compact-support route using canonical project-local measure terms.
-/
theorem canonical_stokes :
    D.toBulkAutoCollapsedInput
      |>.toNaturalCompactSupportStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement :=
  D.toBulkAutoCollapsedInput.canonical_stokes

end NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

/--
Top-level wrapper from project-local-term bulk-auto input to the current
compact-support Stokes endpoint.
-/
theorem naturalCompactSupportStokes_canonical_of_bulkProjectLocalAutoCollapsed
    [IsManifold I 1 M]
    (D :
      NaturalCompactSupportBulkProjectLocalAutoCollapsedInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece ρ μ) :
    D.toBulkAutoCollapsedInput
      |>.toNaturalCompactSupportStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement :=
  D.canonical_stokes

end NaturalCompactSupportBulkProjectLocalAuto

end Stokes

end
