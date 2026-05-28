import Stokes.Global.NaturalCompactSupportInputCollapse
import Stokes.Global.BulkBoundaryIccHalfSpaceTransfer

/-!
# Natural compact-support input with automatic bulk integral identities

`NaturalCompactSupportLocalFactsCollapsedInput` still asked callers to provide
three bulk integral-identification fields.  The current bulk measure API can
construct those fields in the volume-measure case from:

* canonical local facts;
* the support-based `Icc` to `halfSpaceSupportBox` transfer;
* the existing `MeasureLocalBoxTermAPI`.

This module packages that shorter theorem-facing input.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

open SelectedBoundaryIccToHalfSpaceIntegralTransfer

section NaturalCompactSupportBulkAuto

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
Bulk ext-derivative input from volume measure, canonical local facts, and
measure-local box/project-local identification.
-/
def selectedPartitionBulkExtDerivInputOfVolumeMeasureLocalBoxTermAPI
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundary : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (localized : LocalizedInteriorM8Fields I omega P)
    (localFacts :
      SelectedPartitionBulkCanonicalLocalFacts P boundary localized)
    (measureTerms :
      BulkMeasureLocalizationTermFields localized.localizedInterior boundary)
    (extDerivAE :
      BulkIntegrandAEFromPartitionData
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        P boundary localized measureTerms)
    (hμ : μ = volume)
    (boxAPI : MeasureLocalBoxTermAPI measureTerms) :
    SelectedPartitionBulkMeasureExtDerivInput
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      P boundary μ :=
  (toLocalSetIntegralIdentitiesOfMeasureEqVolumeFromSupport
      (P := P) (boundary := boundary) (localized := localized)
      (localFacts := localFacts) (μ := μ) hμ)
    |>.toSelectedPartitionBulkMeasureExtDerivInputOfMeasureLocalBoxTermAPI
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      measureTerms extDerivAE boxAPI

/--
Collapsed compact-support input in which the bulk integral-identification
fields are generated from volume measure and measure-local box data.

Compared with `NaturalCompactSupportLocalFactsCollapsedInput`, this removes:

* `globalBulkIntegral_eq_integral`;
* `interiorBulkTerm_eq_integral`;
* `boundaryBulkTerm_eq_integral`.
-/
structure NaturalCompactSupportBulkAutoCollapsedInput
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
  /-- Scalar measure terms for the localized interior and boundary pieces. -/
  measureTerms :
    BulkMeasureLocalizationTermFields localized.localizedInterior
      targetImageInput.targetImages
  /-- Exterior-derivative a.e. reconstruction for the selected pieces. -/
  extDerivAE :
    BulkIntegrandAEFromPartitionData
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages localized measureTerms
  /-- Local non-integral facts for canonical selected bulk pieces. -/
  bulkLocalFacts :
    SelectedPartitionBulkCanonicalLocalFacts
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages localized
  /-- The selected bulk measure is the volume measure. -/
  measure_eq_volume : μ = volume
  /-- Measure-local box terms agree with the project-local box terms. -/
  measureBox : MeasureLocalBoxTermAPI measureTerms
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
              measureTerms extDerivAE measure_eq_volume measureBox)
            |>.toBulkMeasureFromPartitionData)
        |>.toM8MeasureLocalizationData)

namespace NaturalCompactSupportBulkAutoCollapsedInput

variable [IsManifold I 1 M]
variable
    (D :
      NaturalCompactSupportBulkAutoCollapsedInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece ρ μ)

/-- The canonical support set carried by the compactly supported form data. -/
abbrev supportSet : Set M :=
  D.formData.supportSet

/-- Compactness of the canonical support set. -/
abbrev isCompact_supportSet : IsCompact D.supportSet :=
  D.formData.isCompact_supportSet

/-- The selected partition determined by the canonical support selection. -/
abbrev selectedPartition : SelectedBoxPartitionOfUnity I omega :=
  D.selection.selectedBoxPartitionOfUnity D.smoothness

/-- The automatically constructed local set-integral identities for bulk pieces. -/
def bulkLocalSetIntegralIdentities :
    SelectedPartitionBulkLocalSetIntegralIdentities
      (P := D.selectedPartition)
      (boundary := D.targetImageInput.targetImages)
      D.localized μ :=
  toLocalSetIntegralIdentitiesOfMeasureEqVolumeFromSupport
      (P := D.selectedPartition)
      (boundary := D.targetImageInput.targetImages)
      (localized := D.localized)
      (localFacts := D.bulkLocalFacts)
      (μ := μ)
      D.measure_eq_volume

@[simp]
theorem bulkLocalSetIntegralIdentities_localFacts :
    D.bulkLocalSetIntegralIdentities.localFacts = D.bulkLocalFacts := by
  rfl

/--
The selected bulk ext-derivative input, with global and local integral
identities derived from the bulk measure-local box API.
-/
def bulkExtDerivInput :
    SelectedPartitionBulkMeasureExtDerivInput
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      D.selectedPartition D.targetImageInput.targetImages μ :=
  D.bulkLocalSetIntegralIdentities
    |>.toSelectedPartitionBulkMeasureExtDerivInputOfMeasureLocalBoxTermAPI
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      D.measureTerms D.extDerivAE D.measureBox

@[simp]
theorem bulkExtDerivInput_localized :
    D.bulkExtDerivInput.localized = D.localized := by
  rfl

@[simp]
theorem bulkExtDerivInput_measureTerms :
    D.bulkExtDerivInput.measureTerms = D.measureTerms := by
  rfl

/-- The automatically derived global bulk integral identity. -/
theorem globalBulkIntegral_eq_integral :
    D.measureTerms.globalBulkIntegral =
      ∫ y,
        selectedPartitionBulkScalarIntegrand
          D.selectedPartition D.targetImageInput.targetImages D.localized y ∂μ :=
  D.bulkLocalSetIntegralIdentities
    |>.globalBulkIntegral_eq_integral_of_measureLocalBoxTermAPI D.measureBox

/-- The automatically derived interior local set-integral identity. -/
theorem interiorBulkTerm_eq_integral
    (i : M) (hi : i ∈ D.selectedPartition.active) :
    D.localized.localizedInterior.bulkTerm i =
      ∫ y in D.bulkLocalFacts.interiorBox i,
        selectedPartitionInteriorBulkScalarTerm D.localized i y ∂μ :=
  D.bulkLocalSetIntegralIdentities.interiorBulkTerm_eq_integral i hi

/-- The automatically derived boundary local set-integral identity. -/
theorem boundaryBulkTerm_eq_integral
    (x : M) (hx : x ∈ D.selectedPartition.active)
    (q : BoundaryPiece) (hq : q ∈ D.targetImageInput.targetImages.boundaryPieces x) :
    BoundaryPieceFamilyInput.boundaryBulkTerm
        D.targetImageInput.targetImages x q =
      ∫ y in D.bulkLocalFacts.boundaryBox x q,
        selectedPartitionBoundaryBulkScalarTerm
          D.targetImageInput.targetImages x q y ∂μ :=
  D.bulkLocalSetIntegralIdentities.boundaryBulkTerm_eq_integral x hx q hq

/-- The boundary COV input produced by support-finite selected pieces. -/
def boundaryCOVInput :
    BoundaryMeasureFromTargetCOVInput
      (α := Fin (n + 1) → Real) D.targetImageInput μ :=
  D.boundarySupportCOV.toBoundaryMeasureFromTargetCOVInput

@[simp]
theorem boundaryCOVInput_boundaryIntegrand :
    D.boundaryCOVInput.boundaryIntegrand =
      D.boundarySupportCOV.pieces.boundaryIntegrand := by
  rfl

/-- Construct the collapsed canonical-piece input directly from bulk-auto data. -/
def toCanonicalPiecesCollapsedInput :
    NaturalCompactSupportCanonicalPiecesCollapsedInput
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      I omega BoundaryPiece ρ μ where
  formData := D.formData
  selection := D.selection
  smoothness := D.smoothness
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  targetImageInput := D.targetImageInput
  bulkExtDeriv := D.bulkExtDerivInput
  boundaryCOV := D.boundaryCOVInput
  localizedChartAlignment := by
    simpa [bulkExtDerivInput] using D.localizedChartAlignment
  strictMargins := by
    simpa [bulkExtDerivInput, boundaryCOVInput] using D.strictMargins

/-- The endpoint input produced by automatic bulk integral identities. -/
def toNaturalCompactSupportStokesInput :
    NaturalCompactSupportStokesInput
      (α := Fin (n + 1) → Real) I omega BoundaryPiece μ :=
  D.toCanonicalPiecesCollapsedInput.toNaturalCompactSupportStokesInput

@[simp]
theorem toNaturalCompactSupportStokesInput_selectedPartition :
    D.toNaturalCompactSupportStokesInput.selectedPartition =
      D.selectedPartition := by
  rfl

/--
Bulk-auto compact-support route to the canonical compact-support Stokes
statement.
-/
theorem canonical_stokes :
    D.toNaturalCompactSupportStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement :=
  D.toCanonicalPiecesCollapsedInput.canonical_stokes

end NaturalCompactSupportBulkAutoCollapsedInput

/--
Top-level wrapper from bulk-auto collapsed input to the current compact-support
Stokes endpoint.
-/
theorem naturalCompactSupportStokes_canonical_of_bulkAutoCollapsed
    [IsManifold I 1 M]
    (D :
      NaturalCompactSupportBulkAutoCollapsedInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece ρ μ) :
    D.toNaturalCompactSupportStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement :=
  D.canonical_stokes

end NaturalCompactSupportBulkAuto

end Stokes

end
