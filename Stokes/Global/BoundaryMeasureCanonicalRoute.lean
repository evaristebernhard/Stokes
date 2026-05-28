import Stokes.Global.BoundaryMeasurePartitionToM8
import Stokes.Global.BoundaryMeasureProjectLocal
import Stokes.Global.BoundaryMeasureTargetAssembly
import Stokes.Global.NaturalBoundaryMeasureBuilder

/-!
# Canonical boundary measure route

This file collects the boundary-measure handoff used by the natural compact
support route.  It is deliberately thin: all genuine analytic facts remain
fields of either `BoundaryCompactMeasureFields`, target-image compact-support
input, or existing localization records.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryMeasureCanonicalRoute

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {α : Type a} [MeasurableSpace α]
variable {μ : Measure α}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

namespace NaturalBoundaryMeasureBuilderData

variable
    (D :
      NaturalBoundaryMeasureBuilderData
        (α := α) I omega selectedPartition targetImages μ)

/-- Canonical boundary partition term exposed by the natural boundary route. -/
def canonicalBoundaryPartitionTerm : M → BoundaryPiece → Real :=
  D.boundaryPartitionTerm

/-- Canonical compact/set-integral boundary fields for the selected route. -/
def canonicalBoundaryCompactFields :
    BoundaryCompactMeasureFields μ selectedPartition.active
      targetImages.boundaryPieces D.canonicalBoundaryPartitionTerm :=
  D.compactFields

/-- Canonical analytic boundary localization data. -/
def canonicalBoundaryLocalizationData :
    BoundaryMeasureLocalizationData μ selectedPartition.active
      targetImages.boundaryPieces D.canonicalBoundaryPartitionTerm :=
  D.toBoundaryMeasureLocalizationData

/-- Canonical fieldized boundary localization package. -/
def canonicalBoundaryLocalizationFields :
    BoundaryMeasureLocalizationFields selectedPartition.active
      targetImages.boundaryPieces D.canonicalBoundaryPartitionTerm
      D.globalBoundaryIntegral :=
  D.toBoundaryMeasureLocalizationFields

/-- Canonical boundary-only M8 package produced by natural compact data. -/
def canonicalBoundaryM8MeasureData :
    M8BoundaryMeasureData I omega selectedPartition targetImages :=
  D.toM8BoundaryMeasureData

/-- Replace the boundary part of an M8 measure package by the canonical route. -/
def canonicalBoundaryReplaceM8
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    M8MeasureLocalizationData I omega selectedPartition targetImages :=
  D.replaceBoundary E

@[simp]
theorem canonicalBoundaryPartitionTerm_eq :
    D.canonicalBoundaryPartitionTerm = D.boundaryPartitionTerm :=
  rfl

@[simp]
theorem canonicalBoundaryCompactFields_boundaryMeasureIntegral :
    D.canonicalBoundaryCompactFields.boundaryMeasureIntegral =
      D.compactFields.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem canonicalBoundaryLocalizationData_boundaryMeasureIntegral :
    D.canonicalBoundaryLocalizationData.boundaryMeasureIntegral =
      D.compactFields.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem canonicalBoundaryLocalizationFields_boundaryMeasureIntegral :
    D.canonicalBoundaryLocalizationFields.boundaryMeasureIntegral =
      D.compactFields.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem canonicalBoundaryM8MeasureData_boundaryPartitionTerm :
    D.canonicalBoundaryM8MeasureData.boundaryPartitionTerm =
      D.canonicalBoundaryPartitionTerm :=
  rfl

@[simp]
theorem canonicalBoundaryM8MeasureData_globalBoundaryIntegral :
    D.canonicalBoundaryM8MeasureData.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

@[simp]
theorem canonicalBoundaryM8MeasureData_boundaryMeasureIntegral :
    D.canonicalBoundaryM8MeasureData.boundaryMeasureIntegral =
      D.compactFields.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem canonicalBoundaryReplaceM8_boundaryPartitionTerm
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    (D.canonicalBoundaryReplaceM8 E).boundaryPartitionTerm =
      D.canonicalBoundaryPartitionTerm :=
  rfl

@[simp]
theorem canonicalBoundaryReplaceM8_boundaryMeasureIntegral
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    (D.canonicalBoundaryReplaceM8 E).boundaryMeasureIntegral =
      D.compactFields.boundaryMeasureIntegral :=
  rfl

/-- Active boundary-piece set measurability projected from compact fields. -/
theorem canonicalBoundaryPieceSet_measurable
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ targetImages.boundaryPieces x) :
    MeasurableSet (D.compactFields.boundaryPieceSet x q) :=
  D.compactFields.boundaryPieceSet_measurable x hx q hq

/-- Active boundary-piece `IntegrableOn` projected from compact fields. -/
theorem canonicalBoundaryPieceIntegrableOn
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ targetImages.boundaryPieces x) :
    IntegrableOn (D.compactFields.boundaryPieceIntegrand x q)
      (D.compactFields.boundaryPieceSet x q) μ :=
  D.compactFields.boundaryPieceIntegrableOn x hx q hq

/-- Active indicator-piece integrability in the localization-data shape. -/
theorem canonicalBoundaryPieceIndicator_integrable
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ targetImages.boundaryPieces x) :
    Integrable (D.canonicalBoundaryLocalizationData.pieceFunction x q) μ :=
  D.canonicalBoundaryLocalizationData.boundaryPieceIntegrable x hx q hq

/-- Active partition terms are the corresponding boundary set integrals. -/
theorem canonicalBoundaryPartitionTerm_eq_setIntegral
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ targetImages.boundaryPieces x) :
    D.canonicalBoundaryPartitionTerm x q =
      ∫ y in D.compactFields.boundaryPieceSet x q,
        D.compactFields.boundaryPieceIntegrand x q y ∂μ :=
  D.compactFields.boundaryPartitionTerm_eq_setIntegral x hx q hq

/-- The canonical boundary integrand is AE the selected indicator sum. -/
theorem canonicalBoundaryIntegrand_ae_eq_indicatorSum :
    D.compactFields.boundaryIntegrand =ᵐ[μ]
      boundaryMeasureIndicatorSum selectedPartition.active
        targetImages.boundaryPieces D.compactFields.boundaryPieceSet
        D.compactFields.boundaryPieceIntegrand :=
  D.compactFields.boundaryIntegrand_ae_eq_indicatorSum

/-- Boundary measure localization in the finite selected-piece sum shape. -/
theorem canonicalBoundaryMeasureIntegral_eq_partitionSum :
    D.compactFields.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces D.canonicalBoundaryPartitionTerm :=
  D.compactFields.boundaryMeasureIntegral_eq_partitionSum

/-- The canonical M8 package carries the same finite selected-piece sum field. -/
theorem canonicalBoundaryM8MeasureData_boundaryMeasureIntegral_eq_partitionSum :
    D.canonicalBoundaryM8MeasureData.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces D.canonicalBoundaryPartitionTerm :=
  D.canonicalBoundaryM8MeasureData.boundaryMeasureIntegral_eq_partitionSum

end NaturalBoundaryMeasureBuilderData

section TargetImageCompactSupportRoute

variable [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
variable [IsFiniteMeasureOnCompacts μ]
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/--
Explicit compact-support inputs needed to turn a selected target-image assembly
into boundary measure localization data.

No change-of-variables or measure identity is inferred here; callers must
provide the boundary integral identity, piece set measurability, compact
support data, set-integral terms, and AE reconstruction.
-/
structure CanonicalBoundaryTargetCompactSupportInput
    (D :
      M8TargetImageInput I omega selectedPartition
        orientedBoundaryAtlas BoundaryPiece)
    (μ : Measure α) where
  /-- Boundary-side integrand represented by the measure integral. -/
  boundaryIntegrand : α → Real
  /-- Selected boundary-piece support set. -/
  boundaryPieceSet : M → BoundaryPiece → Set α
  /-- Selected boundary-piece scalar integrand. -/
  boundaryPieceIntegrand : M → BoundaryPiece → α → Real
  /-- Genuine boundary measure integral. -/
  boundaryMeasureIntegral : Real
  /-- The boundary measure integral is the integral of `boundaryIntegrand`. -/
  boundaryMeasureIntegral_eq_integral :
    boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ
  /-- Active boundary support sets are measurable. -/
  boundaryPieceSet_measurable :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ D.targetImages.boundaryPieces x →
        MeasurableSet (boundaryPieceSet x q)
  /-- Active boundary-piece integrands have compact-support integrability. -/
  boundaryPieceCompact :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ D.targetImages.boundaryPieces x →
        CompactSupportIntegrabilityData (boundaryPieceIntegrand x q)
  /-- Active partition terms are the corresponding set integrals. -/
  boundaryPartitionTerm_eq_setIntegral :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ D.targetImages.boundaryPieces x →
        D.assembly.boundaryPartitionTerm x q =
          ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ
  /-- AE reconstruction by selected boundary indicator pieces. -/
  boundaryIntegrand_ae_eq_indicatorSum :
    boundaryIntegrand =ᵐ[μ]
      boundaryMeasureIndicatorSum selectedPartition.active
        D.targetImages.boundaryPieces boundaryPieceSet boundaryPieceIntegrand
  /-- The represented global boundary integral. -/
  globalBoundaryIntegral : Real
  /-- The represented global boundary integral is the measure integral. -/
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :
    globalBoundaryIntegral = boundaryMeasureIntegral

namespace CanonicalBoundaryTargetCompactSupportInput

variable
    {D :
      M8TargetImageInput I omega selectedPartition
        orientedBoundaryAtlas BoundaryPiece}
    (B : CanonicalBoundaryTargetCompactSupportInput (α := α) D μ)

/-- Boundary compact/set-integral fields built from target-image compact data. -/
def canonicalBoundaryCompactFields :
    BoundaryCompactMeasureFields μ selectedPartition.active
      D.targetImages.boundaryPieces D.assembly.boundaryPartitionTerm :=
  D.toSelectedBoundaryMeasurePartitionData.compactFieldsOfCompactSupport
    (μ := μ) B.boundaryIntegrand B.boundaryPieceSet
    B.boundaryPieceIntegrand B.boundaryMeasureIntegral
    B.boundaryMeasureIntegral_eq_integral B.boundaryPieceSet_measurable
    B.boundaryPieceCompact B.boundaryPartitionTerm_eq_setIntegral
    B.boundaryIntegrand_ae_eq_indicatorSum

/-- Boundary measure localization built from target-image compact data. -/
def canonicalBoundaryLocalizationData :
    BoundaryMeasureLocalizationData μ selectedPartition.active
      D.targetImages.boundaryPieces D.assembly.boundaryPartitionTerm :=
  B.canonicalBoundaryCompactFields.toBoundaryMeasureLocalizationData

/-- Fieldized boundary measure localization built from target-image compact data. -/
def canonicalBoundaryLocalizationFields :
    BoundaryMeasureLocalizationFields selectedPartition.active
      D.targetImages.boundaryPieces D.assembly.boundaryPartitionTerm
      B.globalBoundaryIntegral :=
  B.canonicalBoundaryLocalizationData.toBoundaryMeasureLocalizationFields
    B.globalBoundaryIntegral B.globalBoundaryIntegral_eq_boundaryMeasureIntegral

/-- Boundary-only M8 package built from target-image compact data. -/
def canonicalBoundaryM8MeasureData :
    M8BoundaryMeasureData I omega selectedPartition D.targetImages :=
  M8BoundaryMeasureData.ofBoundaryMeasureLocalizationFields
    (I := I) (omega := omega) (selectedPartition := selectedPartition)
    (targetImages := D.targetImages)
    B.canonicalBoundaryLocalizationFields

@[simp]
theorem canonicalBoundaryCompactFields_boundaryMeasureIntegral :
    B.canonicalBoundaryCompactFields.boundaryMeasureIntegral =
      B.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem canonicalBoundaryLocalizationData_boundaryMeasureIntegral :
    B.canonicalBoundaryLocalizationData.boundaryMeasureIntegral =
      B.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem canonicalBoundaryLocalizationFields_boundaryMeasureIntegral :
    B.canonicalBoundaryLocalizationFields.boundaryMeasureIntegral =
      B.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem canonicalBoundaryM8MeasureData_boundaryPartitionTerm :
    B.canonicalBoundaryM8MeasureData.boundaryPartitionTerm =
      D.assembly.boundaryPartitionTerm :=
  rfl

@[simp]
theorem canonicalBoundaryM8MeasureData_globalBoundaryIntegral :
    B.canonicalBoundaryM8MeasureData.globalBoundaryIntegral =
      B.globalBoundaryIntegral :=
  rfl

@[simp]
theorem canonicalBoundaryM8MeasureData_boundaryMeasureIntegral :
    B.canonicalBoundaryM8MeasureData.boundaryMeasureIntegral =
      B.boundaryMeasureIntegral :=
  rfl

/-- Target-image compact route supplies active indicator-piece integrability. -/
theorem canonicalBoundaryPieceIndicator_integrable
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    Integrable (B.canonicalBoundaryLocalizationData.pieceFunction x q) μ :=
  B.canonicalBoundaryLocalizationData.boundaryPieceIntegrable x hx q hq

/-- Target-image compact route supplies AE boundary localization. -/
theorem canonicalBoundaryIntegrand_ae_eq_indicatorSum :
    B.boundaryIntegrand =ᵐ[μ]
      boundaryMeasureIndicatorSum selectedPartition.active
        D.targetImages.boundaryPieces B.boundaryPieceSet
        B.boundaryPieceIntegrand :=
  B.canonicalBoundaryCompactFields.boundaryIntegrand_ae_eq_indicatorSum

/-- Target-image compact route supplies the finite selected-piece sum. -/
theorem canonicalBoundaryMeasureIntegral_eq_partitionSum :
    B.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        D.targetImages.boundaryPieces D.assembly.boundaryPartitionTerm :=
  B.canonicalBoundaryLocalizationData.boundaryMeasureIntegral_eq_partitionSum

/-- Target-image compact route supplies the M8 boundary finite-sum field. -/
theorem canonicalBoundaryM8MeasureData_boundaryMeasureIntegral_eq_partitionSum :
    B.canonicalBoundaryM8MeasureData.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        D.targetImages.boundaryPieces D.assembly.boundaryPartitionTerm :=
  B.canonicalBoundaryM8MeasureData.boundaryMeasureIntegral_eq_partitionSum

end CanonicalBoundaryTargetCompactSupportInput

end TargetImageCompactSupportRoute

end BoundaryMeasureCanonicalRoute

end Stokes

end
