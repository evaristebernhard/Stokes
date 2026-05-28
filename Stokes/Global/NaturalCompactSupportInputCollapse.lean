import Stokes.Global.CanonicalPiecesFromLocalFacts

/-!
# Natural compact-support endpoint input collapse

This module records the current shortest natural entry points for
`naturalCompactSupportStokes_canonical`.

The constructors below remove the remaining bookkeeping around the compact
support set: callers no longer choose an external `K` with a separate proof
`K = formData.supportSet`.  The selected chart package is indexed directly by
`formData.supportSet` and `formData.isCompact_supportSet`, so the support-set
compatibility field is definitionally `rfl`.

The local-facts wrapper also keeps the canonical-piece fields collapsed: the
bulk measure input is constructed from selected local bulk facts, and the
boundary target measure input is constructed from the support-finite COV
package.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportInputCollapse

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
Canonical-piece input with the compact support set chosen canonically from
`formData`.

Compared with `NaturalCompactSupportCanonicalPiecesInput`, this record removes
the separate `K`, `hK`, and `supportSet_eq` fields.  The remaining fields are
the current genuine inputs to the canonical-piece route.
-/
structure NaturalCompactSupportCanonicalPiecesCollapsedInput
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
  /-- Canonical bulk measure input from partition exterior derivatives. -/
  bulkExtDeriv :
    SelectedPartitionBulkMeasureExtDerivInput
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages μ
  /-- Boundary compact-support input produced by target-image COV. -/
  boundaryCOV :
    BoundaryMeasureFromTargetCOVInput
      (α := Fin (n + 1) → Real) targetImageInput μ
  /-- The selected localized pieces use the selected chart label as source/target. -/
  localizedChartAlignment :
    LocalizedInteriorM8ChartAlignment
      bulkExtDeriv.toBulkMeasureFromPartitionData.localized
  /-- Strict outer margins around the selected boxes for the produced measure data. -/
  strictMargins :
    SelectedBoxStrictMarginData
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages
      ((boundaryCOV.toCanonicalBoundaryTargetCompactSupportInput)
        |>.toMeasureBuilderData bulkExtDeriv.toBulkMeasureFromPartitionData
        |>.toM8MeasureLocalizationData)

namespace NaturalCompactSupportCanonicalPiecesCollapsedInput

variable [IsManifold I 1 M]
variable
    (D :
      NaturalCompactSupportCanonicalPiecesCollapsedInput
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
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

/--
Forget the support-set collapse and expose the existing canonical-piece input.
-/
def toNaturalCompactSupportCanonicalPiecesInput :
    NaturalCompactSupportCanonicalPiecesInput
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      I omega BoundaryPiece ρ D.supportSet D.isCompact_supportSet μ where
  formData := D.formData
  supportSet_eq := rfl
  selection := D.selection
  smoothness := D.smoothness
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  targetImageInput := D.targetImageInput
  bulkExtDeriv := D.bulkExtDeriv
  boundaryCOV := D.boundaryCOV
  localizedChartAlignment := D.localizedChartAlignment
  strictMargins := D.strictMargins

@[simp]
theorem toNaturalCompactSupportCanonicalPiecesInput_formData :
    D.toNaturalCompactSupportCanonicalPiecesInput.formData = D.formData := by
  rfl

@[simp]
theorem toNaturalCompactSupportCanonicalPiecesInput_selection :
    D.toNaturalCompactSupportCanonicalPiecesInput.selection = D.selection := by
  rfl

@[simp]
theorem toNaturalCompactSupportCanonicalPiecesInput_bulkExtDeriv :
    D.toNaturalCompactSupportCanonicalPiecesInput.bulkExtDeriv =
      D.bulkExtDeriv := by
  rfl

@[simp]
theorem toNaturalCompactSupportCanonicalPiecesInput_boundaryCOV :
    D.toNaturalCompactSupportCanonicalPiecesInput.boundaryCOV =
      D.boundaryCOV := by
  rfl

/-- The end-to-end input produced by the collapsed canonical-piece input. -/
def toNaturalCompactSupportEndToEndInput :
    NaturalCompactSupportEndToEndInput
      (α := Fin (n + 1) → Real) I omega BoundaryPiece μ :=
  D.toNaturalCompactSupportCanonicalPiecesInput
    |>.toNaturalCompactSupportEndToEndInput

/-- The endpoint input consumed directly by `naturalCompactSupportStokes_canonical`. -/
def toNaturalCompactSupportStokesInput :
    NaturalCompactSupportStokesInput
      (α := Fin (n + 1) → Real) I omega BoundaryPiece μ :=
  D.toNaturalCompactSupportEndToEndInput
    |>.toNaturalCompactSupportStokesInput

@[simp]
theorem toNaturalCompactSupportStokesInput_formData :
    D.toNaturalCompactSupportStokesInput.formData = D.formData := by
  rfl

@[simp]
theorem toNaturalCompactSupportStokesInput_selectedPartition :
    D.toNaturalCompactSupportStokesInput.selectedPartition =
      D.selectedPartition := by
  rfl

/--
Collapsed canonical-piece route to the canonical compact-support Stokes
statement.
-/
theorem canonical_stokes :
    D.toNaturalCompactSupportStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement :=
  D.toNaturalCompactSupportCanonicalPiecesInput.canonical_stokes

end NaturalCompactSupportCanonicalPiecesCollapsedInput

/--
Top-level wrapper from collapsed canonical-piece input to the current endpoint.
-/
theorem naturalCompactSupportStokes_canonical_of_collapsedCanonicalPieces
    [IsManifold I 1 M]
    (D :
      NaturalCompactSupportCanonicalPiecesCollapsedInput
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        I omega BoundaryPiece ρ μ) :
    D.toNaturalCompactSupportStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement :=
  D.canonical_stokes

/--
Local-facts input with the compact support set chosen canonically from
`formData`.

Compared with `NaturalCompactSupportLocalFactsInput`, this record removes
`K`, `hK`, and `supportSet_eq`.  It also exposes the same local-facts split:
canonical bulk measure data and boundary COV data are constructed below rather
than supplied as independent fields.
-/
structure NaturalCompactSupportLocalFactsCollapsedInput
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
  /-- The represented bulk integral is the integral of the canonical scalar sum. -/
  globalBulkIntegral_eq_integral :
    measureTerms.globalBulkIntegral =
      ∫ y,
        selectedPartitionBulkScalarIntegrand
          (selection.selectedBoxPartitionOfUnity smoothness)
          targetImageInput.targetImages localized y ∂μ
  /-- Interior local set integrals are the recorded localized bulk terms. -/
  interiorBulkTerm_eq_integral :
    ∀ i, i ∈ (selection.selectedBoxPartitionOfUnity smoothness).active →
      localized.localizedInterior.bulkTerm i =
        ∫ y in bulkLocalFacts.interiorBox i,
          selectedPartitionInteriorBulkScalarTerm localized i y ∂μ
  /-- Boundary local set integrals are the recorded boundary bulk terms. -/
  boundaryBulkTerm_eq_integral :
    ∀ x, x ∈ (selection.selectedBoxPartitionOfUnity smoothness).active →
      ∀ q, q ∈ targetImageInput.targetImages.boundaryPieces x →
        BoundaryPieceFamilyInput.boundaryBulkTerm
            targetImageInput.targetImages x q =
          ∫ y in bulkLocalFacts.boundaryBox x q,
            selectedPartitionBoundaryBulkScalarTerm
              targetImageInput.targetImages x q y ∂μ
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
          (bulkLocalFacts.toSelectedPartitionBulkMeasureExtDerivInput
            (ExtInteriorPiece := ExtInteriorPiece)
            (ExtBoundaryPiece := ExtBoundaryPiece)
            measureTerms extDerivAE globalBulkIntegral_eq_integral
            interiorBulkTerm_eq_integral boundaryBulkTerm_eq_integral
            |>.toBulkMeasureFromPartitionData)
        |>.toM8MeasureLocalizationData)

namespace NaturalCompactSupportLocalFactsCollapsedInput

variable [IsManifold I 1 M]
variable
    (D :
      NaturalCompactSupportLocalFactsCollapsedInput
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
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

/-- The selected bulk ext-derivative input produced from local facts. -/
def bulkExtDerivInput :
    SelectedPartitionBulkMeasureExtDerivInput
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      D.selectedPartition D.targetImageInput.targetImages μ :=
  D.bulkLocalFacts.toSelectedPartitionBulkMeasureExtDerivInput
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    D.measureTerms D.extDerivAE D.globalBulkIntegral_eq_integral
    D.interiorBulkTerm_eq_integral D.boundaryBulkTerm_eq_integral

@[simp]
theorem bulkExtDerivInput_localized :
    D.bulkExtDerivInput.localized = D.localized := by
  rfl

@[simp]
theorem bulkExtDerivInput_measureTerms :
    D.bulkExtDerivInput.measureTerms = D.measureTerms := by
  rfl

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

/--
Forget the support-set collapse and expose the existing local-facts input.
-/
def toNaturalCompactSupportLocalFactsInput :
    NaturalCompactSupportLocalFactsInput
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      I omega BoundaryPiece ρ D.supportSet D.isCompact_supportSet μ where
  formData := D.formData
  supportSet_eq := rfl
  selection := D.selection
  smoothness := D.smoothness
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  targetImageInput := D.targetImageInput
  localized := D.localized
  measureTerms := D.measureTerms
  extDerivAE := D.extDerivAE
  bulkLocalFacts := D.bulkLocalFacts
  globalBulkIntegral_eq_integral := D.globalBulkIntegral_eq_integral
  interiorBulkTerm_eq_integral := D.interiorBulkTerm_eq_integral
  boundaryBulkTerm_eq_integral := D.boundaryBulkTerm_eq_integral
  boundarySupportCOV := D.boundarySupportCOV
  localizedChartAlignment := D.localizedChartAlignment
  strictMargins := D.strictMargins

@[simp]
theorem toNaturalCompactSupportLocalFactsInput_formData :
    D.toNaturalCompactSupportLocalFactsInput.formData = D.formData := by
  rfl

@[simp]
theorem toNaturalCompactSupportLocalFactsInput_selection :
    D.toNaturalCompactSupportLocalFactsInput.selection = D.selection := by
  rfl

/--
Construct the collapsed canonical-piece input from collapsed local facts.
-/
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

@[simp]
theorem toCanonicalPiecesCollapsedInput_bulkExtDeriv :
    D.toCanonicalPiecesCollapsedInput.bulkExtDeriv =
      D.bulkExtDerivInput := by
  rfl

@[simp]
theorem toCanonicalPiecesCollapsedInput_boundaryCOV :
    D.toCanonicalPiecesCollapsedInput.boundaryCOV =
      D.boundaryCOVInput := by
  rfl

/-- The endpoint input produced by collapsed local facts. -/
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
Collapsed local-facts route to the canonical compact-support Stokes statement.
-/
theorem canonical_stokes :
    D.toNaturalCompactSupportStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement :=
  D.toCanonicalPiecesCollapsedInput.canonical_stokes

end NaturalCompactSupportLocalFactsCollapsedInput

/--
Top-level wrapper from collapsed local facts to the current endpoint.
-/
theorem naturalCompactSupportStokes_canonical_of_collapsedLocalFacts
    [IsManifold I 1 M]
    (D :
      NaturalCompactSupportLocalFactsCollapsedInput
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        I omega BoundaryPiece ρ μ) :
    D.toNaturalCompactSupportStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement :=
  D.canonical_stokes

end NaturalCompactSupportInputCollapse

end Stokes

end
