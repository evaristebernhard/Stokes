import Stokes.Global.NaturalCompactSupportBuilder

/-!
# Canonical bulk-measure route for natural compact-support inputs

This file is a zero-semantics adapter.  It records the shortest currently
available route from a `NaturalCompactSupportStokesInput` or
`NaturalCompactSupportBuilderData` to the bulk-measure pieces of the M8
statement.

The important point is negative as much as positive: no new analytic
localization theorem is proved here.  The compact-support measure package
already contains the bulk integrability, a.e. localization, and finite-sum
fields.  This module only exposes those fields under collision-resistant
`canonicalBulk...` names.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkMeasureCanonicalRoute

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]

namespace NaturalCompactSupportStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/-- The compact-support bulk package carried by the natural input. -/
def canonicalBulkCompactSupportData
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    CompactSupportBulkMeasureData
      (α := α) (μ := μ)
      D.measure.localized.localizedInterior
      D.targetImageInput.targetImages
      D.measure.globalBulkIntegral :=
  D.measure.bulk

/-- Pure measure-localization fields obtained from the compact-support bulk package. -/
def canonicalBulkMeasureLocalizationFields
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    BulkIntegralPartitionInput.BulkMeasureLocalizationFields
      (α := α) μ
      D.measure.localized.localizedInterior
      D.targetImageInput.targetImages
      D.measure.globalBulkIntegral :=
  D.canonicalBulkCompactSupportData.toBulkMeasureLocalizationFields

/-- The M8 bulk fields obtained by forgetting the boundary fields of the M8 measure package. -/
def canonicalBulkM8Fields
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    M8BulkMeasureFields I omega D.selectedPartition
      D.targetImageInput.targetImages where
  localizedInterior := D.measure.toM8MeasureLocalizationData.localizedInterior
  localized_active := D.measure.toM8MeasureLocalizationData.localized_active
  localized_coefficient :=
    D.measure.toM8MeasureLocalizationData.localized_coefficient
  globalBulkIntegral := D.measure.toM8MeasureLocalizationData.globalBulkIntegral
  bulkMeasureIntegral := D.measure.toM8MeasureLocalizationData.bulkMeasureIntegral
  globalBulkIntegral_eq_bulkMeasureIntegral :=
    D.measure.toM8MeasureLocalizationData.globalBulkIntegral_eq_bulkMeasureIntegral
  bulkMeasureIntegral_eq_localBulkSum :=
    D.measure.toM8MeasureLocalizationData.bulkMeasureIntegral_eq_localBulkSum

/--
Bundle of the bulk projections that are already available from a natural
compact-support input.

The fields here are intentionally projections, not new hypotheses.  If a caller
starts only from geometric compact-support/chart data, it must still construct
`D.measure`; this record only describes what becomes available after that
measure package exists.
-/
structure CanonicalBulkRouteEvidence
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) where
  /-- Compact-support bulk data in the natural measure package. -/
  compactSupport :
    CompactSupportBulkMeasureData
      (α := α) (μ := μ)
      D.measure.localized.localizedInterior
      D.targetImageInput.targetImages
      D.measure.globalBulkIntegral
  /-- Pure measure localization fields derived from compact support. -/
  localization :
    BulkIntegralPartitionInput.BulkMeasureLocalizationFields
      (α := α) μ
      D.measure.localized.localizedInterior
      D.targetImageInput.targetImages
      D.measure.globalBulkIntegral
  /-- M8 bulk fields obtained from the full M8 measure-localization package. -/
  m8Bulk :
    M8BulkMeasureFields I omega D.selectedPartition
      D.targetImageInput.targetImages
  /-- The M8 bulk integral is the compact-support represented bulk integral. -/
  m8BulkIntegral_eq_global :
    m8Bulk.bulkMeasureIntegral = D.measure.globalBulkIntegral
  /-- The a.e. indicator localization used by the pure measure theorem. -/
  aeIndicator :
    compactSupport.F =ᵐ[μ]
      bulkMeasureIndicatorSum
        D.measure.localized.localizedInterior.active
        D.targetImageInput.targetImages.activeCharts
        D.targetImageInput.targetImages.boundaryPieces
        compactSupport.interiorBox
        compactSupport.boundaryBox
        compactSupport.interiorLocalTerm
        compactSupport.boundaryLocalTerm

/-- Canonical bulk-route evidence, built only by projecting existing fields. -/
def canonicalBulkRouteEvidence
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    CanonicalBulkRouteEvidence D where
  compactSupport := D.canonicalBulkCompactSupportData
  localization := D.canonicalBulkMeasureLocalizationFields
  m8Bulk := D.canonicalBulkM8Fields
  m8BulkIntegral_eq_global := rfl
  aeIndicator := D.canonicalBulkCompactSupportData.F_ae_eq_indicatorSum

@[simp]
theorem canonicalBulkCompactSupportData_eq_measure_bulk
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.canonicalBulkCompactSupportData = D.measure.bulk :=
  rfl

@[simp]
theorem canonicalBulkMeasureLocalizationFields_F
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.canonicalBulkMeasureLocalizationFields.F =
      D.measure.bulk.F :=
  rfl

@[simp]
theorem canonicalBulkM8Fields_localizedInterior
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.canonicalBulkM8Fields.localizedInterior =
      D.measure.toM8MeasureLocalizationData.localizedInterior :=
  rfl

@[simp]
theorem canonicalBulkM8Fields_globalBulkIntegral
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.canonicalBulkM8Fields.globalBulkIntegral =
      D.measure.toM8MeasureLocalizationData.globalBulkIntegral :=
  rfl

@[simp]
theorem canonicalBulkM8Fields_bulkMeasureIntegral
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.canonicalBulkM8Fields.bulkMeasureIntegral =
      D.measure.toM8MeasureLocalizationData.bulkMeasureIntegral :=
  rfl

@[simp]
theorem canonicalBulkM8Fields_bulkMeasureIntegral_eq_global
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.canonicalBulkM8Fields.bulkMeasureIntegral =
      D.measure.globalBulkIntegral :=
  rfl

@[simp]
theorem canonicalBulkRouteEvidence_compactSupport
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    (D.canonicalBulkRouteEvidence).compactSupport =
      D.canonicalBulkCompactSupportData :=
  rfl

@[simp]
theorem canonicalBulkRouteEvidence_localization
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    (D.canonicalBulkRouteEvidence).localization =
      D.canonicalBulkMeasureLocalizationFields :=
  rfl

@[simp]
theorem canonicalBulkRouteEvidence_m8Bulk
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    (D.canonicalBulkRouteEvidence).m8Bulk =
      D.canonicalBulkM8Fields :=
  rfl

/-- Interior compact-support integrability projected from the canonical route. -/
def canonicalBulkInteriorCompactSupport
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ)
    (i : M) (hi : i ∈ D.measure.localized.localizedInterior.active) :
    CompactSupportIntegrabilityData
      (D.measure.bulk.interiorLocalTerm i) :=
  D.canonicalBulkCompactSupportData.interiorCompactSupport i hi

/-- Boundary compact-support integrability projected from the canonical route. -/
def canonicalBulkBoundaryCompactSupport
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ)
    (x : M) (hx : x ∈ D.targetImageInput.targetImages.activeCharts)
    (q : BoundaryPiece)
    (hq : q ∈ D.targetImageInput.targetImages.boundaryPieces x) :
    CompactSupportIntegrabilityData
      (D.measure.bulk.boundaryLocalTerm x q) :=
  D.canonicalBulkCompactSupportData.boundaryCompactSupport x hx q hq

/-- Interior `IntegrableOn` field used by the pure bulk measure theorem. -/
theorem canonicalBulkInteriorIntegrableOn
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ)
    (i : M) (hi : i ∈ D.measure.localized.localizedInterior.active) :
    IntegrableOn
      (D.measure.bulk.interiorLocalTerm i)
      (D.measure.bulk.interiorBox i) μ :=
  D.canonicalBulkMeasureLocalizationFields.interiorIntegrableOn i hi

/-- Boundary `IntegrableOn` field used by the pure bulk measure theorem. -/
theorem canonicalBulkBoundaryIntegrableOn
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ)
    (x : M) (hx : x ∈ D.targetImageInput.targetImages.activeCharts)
    (q : BoundaryPiece)
    (hq : q ∈ D.targetImageInput.targetImages.boundaryPieces x) :
    IntegrableOn
      (D.measure.bulk.boundaryLocalTerm x q)
      (D.measure.bulk.boundaryBox x q) μ :=
  D.canonicalBulkMeasureLocalizationFields.boundaryIntegrableOn x hx q hq

/-- A.e. indicator localization projected from the compact-support route. -/
theorem canonicalBulkAEIndicatorLocalization
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.measure.bulk.F =ᵐ[μ]
      bulkMeasureIndicatorSum
        D.measure.localized.localizedInterior.active
        D.targetImageInput.targetImages.activeCharts
        D.targetImageInput.targetImages.boundaryPieces
        D.measure.bulk.interiorBox
        D.measure.bulk.boundaryBox
        D.measure.bulk.interiorLocalTerm
        D.measure.bulk.boundaryLocalTerm :=
  D.canonicalBulkCompactSupportData.F_ae_eq_indicatorSum

/-- M8 finite local-bulk-sum equality exposed under a canonical bulk name. -/
theorem canonicalBulkM8Localizes
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.canonicalBulkM8Fields.bulkMeasureIntegral =
      (Finset.sum D.selectedPartition.active fun x =>
        Finset.sum ({()} : Finset Unit) fun _q =>
          D.canonicalBulkM8Fields.localizedInterior.bulkTerm x) +
        Finset.sum D.selectedPartition.active fun x =>
          Finset.sum (D.targetImageInput.targetImages.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm
              D.targetImageInput.targetImages x q :=
  D.canonicalBulkM8Fields.bulkMeasureIntegral_eq_localBulkSum

end NaturalCompactSupportStokesInput

namespace NaturalCompactSupportBuilderData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/-- Canonical compact-support bulk package projected from builder data. -/
def canonicalBulkCompactSupportData
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    CompactSupportBulkMeasureData
      (α := α) (μ := μ)
      D.measure.localized.localizedInterior
      D.targetImageInput.targetImages
      D.measure.globalBulkIntegral :=
  D.toNaturalCompactSupportStokesInput.canonicalBulkCompactSupportData

/-- Canonical pure bulk measure-localization fields projected from builder data. -/
def canonicalBulkMeasureLocalizationFields
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    BulkIntegralPartitionInput.BulkMeasureLocalizationFields
      (α := α) μ
      D.measure.localized.localizedInterior
      D.targetImageInput.targetImages
      D.measure.globalBulkIntegral :=
  D.toNaturalCompactSupportStokesInput.canonicalBulkMeasureLocalizationFields

/-- Canonical M8 bulk fields projected from builder data. -/
def canonicalBulkM8Fields
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    M8BulkMeasureFields I omega D.selectedPartition
      D.targetImageInput.targetImages :=
  D.toNaturalCompactSupportStokesInput.canonicalBulkM8Fields

@[simp]
theorem canonicalBulkCompactSupportData_eq_measure_bulk
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    D.canonicalBulkCompactSupportData = D.measure.bulk :=
  rfl

@[simp]
theorem canonicalBulkM8Fields_bulkMeasureIntegral
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    D.canonicalBulkM8Fields.bulkMeasureIntegral =
      D.measure.toM8MeasureLocalizationData.bulkMeasureIntegral :=
  rfl

@[simp]
theorem canonicalBulkM8Fields_bulkMeasureIntegral_eq_global
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    D.canonicalBulkM8Fields.bulkMeasureIntegral =
      D.measure.globalBulkIntegral :=
  rfl

/-- Builder-facing a.e. indicator localization under the canonical bulk name. -/
theorem canonicalBulkAEIndicatorLocalization
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    D.measure.bulk.F =ᵐ[μ]
      bulkMeasureIndicatorSum
        D.measure.localized.localizedInterior.active
        D.targetImageInput.targetImages.activeCharts
        D.targetImageInput.targetImages.boundaryPieces
        D.measure.bulk.interiorBox
        D.measure.bulk.boundaryBox
        D.measure.bulk.interiorLocalTerm
        D.measure.bulk.boundaryLocalTerm :=
  D.toNaturalCompactSupportStokesInput.canonicalBulkAEIndicatorLocalization

end NaturalCompactSupportBuilderData

end BulkMeasureCanonicalRoute

end Stokes

end
