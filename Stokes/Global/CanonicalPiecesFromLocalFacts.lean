import Stokes.Global.MeasureBuilderFromCanonicalPieces
import Stokes.Global.BulkMeasureCanonicalLocalFacts
import Stokes.Global.BoundaryPieceSupportFiniteSum

/-!
# Canonical Stokes input from local bulk and boundary facts

This module composes the latest field-reduction layers:

* `SelectedPartitionBulkCanonicalLocalFacts` supplies box measurability,
  compact-support projections, and zero-off-box facts for canonical bulk local
  terms;
* `BoundaryPieceSupportFiniteSumTargetCOVInput` supplies the boundary target COV
  input with the a.e. reconstruction derived from support containment.

The remaining hard inputs are now the actual integral identities for the bulk
local/global terms, plus the geometric/source-boundary facts needed to construct
the boundary support-finite-sum package.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section CanonicalPiecesFromLocalFacts

universe u w b ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {ρ : SmoothPartitionOfUnity M I M univ}
variable {K : Set M} {hK : IsCompact K}
variable {μ : Measure (Fin (n + 1) → Real)}
variable [IsFiniteMeasureOnCompacts μ]

/--
Input for compact-support Stokes after local bulk facts and support-finite
boundary reconstruction have been separated from the remaining integral
identities.
-/
structure NaturalCompactSupportLocalFactsInput
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (K : Set M) (hK : IsCompact K)
    (μ : Measure (Fin (n + 1) → Real))
    [IsFiniteMeasureOnCompacts μ]
    [IsManifold I 1 M] where
  /-- Compactly supported smooth input form. -/
  formData : CompactlySupportedSmoothFormData I omega
  /-- The selected compact set is the support set recorded by `formData`. -/
  supportSet_eq : K = formData.supportSet
  /-- Compact-support finite active chart selection. -/
  selection : CompactSupportFiniteActiveSelection (I := I) ρ K hK omega
  /-- Smoothness data upgrading selected compact boxes to extended boxes. -/
  smoothness :
    ActiveCompactBoxSmoothness selection.finiteActive selection.supportData.box omega
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

namespace NaturalCompactSupportLocalFactsInput

variable [IsManifold I 1 M]
variable
    (D :
      NaturalCompactSupportLocalFactsInput
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        I omega BoundaryPiece ρ K hK μ)

/-- The selected partition determined by the compact-support selection. -/
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

/-- Convert the local-facts input to canonical-piece input. -/
def toNaturalCompactSupportCanonicalPiecesInput :
    NaturalCompactSupportCanonicalPiecesInput
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      I omega BoundaryPiece ρ K hK μ where
  formData := D.formData
  supportSet_eq := D.supportSet_eq
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
theorem toNaturalCompactSupportCanonicalPiecesInput_bulkExtDeriv :
    D.toNaturalCompactSupportCanonicalPiecesInput.bulkExtDeriv =
      D.bulkExtDerivInput := by
  rfl

@[simp]
theorem toNaturalCompactSupportCanonicalPiecesInput_boundaryCOV :
    D.toNaturalCompactSupportCanonicalPiecesInput.boundaryCOV =
      D.boundaryCOVInput := by
  rfl

/-- Current compact-support Stokes endpoint from local bulk and boundary facts. -/
theorem canonical_stokes :
    D.toNaturalCompactSupportCanonicalPiecesInput
      |>.toNaturalCompactSupportEndToEndInput
      |>.toNaturalCompactSupportStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement :=
  D.toNaturalCompactSupportCanonicalPiecesInput.canonical_stokes

end NaturalCompactSupportLocalFactsInput

/--
Top-level wrapper from local bulk facts and support-finite boundary data to the
current compact-support Stokes endpoint.
-/
theorem naturalCompactSupportStokes_canonical_of_localFacts
    [IsManifold I 1 M]
    (D :
      NaturalCompactSupportLocalFactsInput
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        I omega BoundaryPiece ρ K hK μ) :
    D.toNaturalCompactSupportCanonicalPiecesInput
      |>.toNaturalCompactSupportEndToEndInput
      |>.toNaturalCompactSupportStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement :=
  D.canonical_stokes

end CanonicalPiecesFromLocalFacts

end Stokes

end
