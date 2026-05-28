import Stokes.Global.BoundaryMeasureFromPartition
import Stokes.Global.BoundaryMeasureToM8

/-!
# Boundary partition measure data for M8

This file is a boundary-only M8 entry point for the measure side of the proof
wave.  It combines the selected boundary partition package, compact/set
integral boundary measure fields, and the M8 boundary-measure adapter.

The analytic inputs remain explicit: a boundary integrand, selected support
sets, piece integrands, set-integral term identities, active-piece
integrability (or compact-support data), and the a.e. indicator reconstruction
of the boundary integrand.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryMeasurePartitionToM8

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

/--
Boundary partition data sufficient to build the M8 boundary-measure package.

The partition data may be produced before rewriting into the selected M8
indices.  The two alignment fields identify its active charts and boundary
pieces with the selected partition and target-image family.
-/
structure BoundaryMeasurePartitionToM8Data
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (μ : Measure α)
    (globalBoundaryIntegral : Real) where
  /-- Boundary partition data carrying the active charts, pieces, and terms. -/
  boundaryPartition : BoundaryMeasurePartitionData M BoundaryPiece
  /-- The partition active charts are the selected M8 active charts. -/
  boundary_active :
    boundaryPartition.activeCharts = selectedPartition.active
  /-- The partition boundary pieces are the selected target-image pieces. -/
  boundary_pieces :
    boundaryPartition.boundaryPieces = targetImages.boundaryPieces
  /-- Boundary-side integrand represented by the measure integral. -/
  boundaryIntegrand : α → Real
  /-- Support set for one selected boundary piece. -/
  boundaryPieceSet : M → BoundaryPiece → Set α
  /-- Scalar integrand for one selected boundary piece. -/
  boundaryPieceIntegrand : M → BoundaryPiece → α → Real
  /-- Genuine boundary measure integral. -/
  boundaryMeasureIntegral : Real
  /-- The represented global boundary integral agrees with the measure integral. -/
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :
    globalBoundaryIntegral = boundaryMeasureIntegral
  /-- The boundary measure integral is the integral of the global integrand. -/
  boundaryMeasureIntegral_eq_integral :
    boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ
  /-- Active boundary support sets are measurable. -/
  boundaryPieceSet_measurable :
    ∀ x, x ∈ boundaryPartition.activeCharts →
      ∀ q, q ∈ boundaryPartition.boundaryPieces x →
        MeasurableSet (boundaryPieceSet x q)
  /-- Active boundary-piece integrands are integrable on their support sets. -/
  boundaryPieceIntegrableOn :
    ∀ x, x ∈ boundaryPartition.activeCharts →
      ∀ q, q ∈ boundaryPartition.boundaryPieces x →
        IntegrableOn (boundaryPieceIntegrand x q) (boundaryPieceSet x q) μ
  /-- Active boundary partition terms are the corresponding set integrals. -/
  boundaryPartitionTerm_eq_setIntegral :
    ∀ x, x ∈ boundaryPartition.activeCharts →
      ∀ q, q ∈ boundaryPartition.boundaryPieces x →
        boundaryPartition.boundaryPartitionTerm x q =
          ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ
  /-- A.e. reconstruction of the boundary integrand by selected indicators. -/
  boundaryIntegrand_ae_eq_indicatorSum :
    boundaryIntegrand =ᵐ[μ]
      boundaryMeasureIndicatorSum boundaryPartition.activeCharts
        boundaryPartition.boundaryPieces boundaryPieceSet
        boundaryPieceIntegrand

namespace BoundaryMeasurePartitionToM8Data

variable {globalBoundaryIntegral : Real}
variable
    (D :
      BoundaryMeasurePartitionToM8Data
        (α := α) I omega selectedPartition targetImages μ
        globalBoundaryIntegral)

/-- Boundary compact/set-integral fields in the native partition shape. -/
def toBoundaryCompactMeasureFields :
    BoundaryCompactMeasureFields μ D.boundaryPartition.activeCharts
      D.boundaryPartition.boundaryPieces
      D.boundaryPartition.boundaryPartitionTerm :=
  D.boundaryPartition.compactFieldsOfIntegrableOn
    (μ := μ) D.boundaryIntegrand D.boundaryPieceSet
    D.boundaryPieceIntegrand D.boundaryMeasureIntegral
    D.boundaryMeasureIntegral_eq_integral D.boundaryPieceSet_measurable
    D.boundaryPieceIntegrableOn D.boundaryPartitionTerm_eq_setIntegral
    D.boundaryIntegrand_ae_eq_indicatorSum

/-- Boundary compact/set-integral fields rewritten to the selected M8 shape. -/
def toSelectedBoundaryCompactMeasureFields :
    BoundaryCompactMeasureFields μ selectedPartition.active
      targetImages.boundaryPieces
      D.boundaryPartition.boundaryPartitionTerm :=
  BoundaryCompactMeasureFields.ofSetIntegral
    (μ := μ) (activeCharts := selectedPartition.active)
    (boundaryPieces := targetImages.boundaryPieces)
    (boundaryPartitionTerm := D.boundaryPartition.boundaryPartitionTerm)
    D.boundaryIntegrand D.boundaryPieceSet D.boundaryPieceIntegrand
    D.boundaryMeasureIntegral D.boundaryMeasureIntegral_eq_integral
    (fun x hx q hq =>
      D.boundaryPieceSet_measurable x
        (by simpa [D.boundary_active] using hx) q
        (by simpa [D.boundary_pieces] using hq))
    (fun x hx q hq =>
      D.boundaryPieceIntegrableOn x
        (by simpa [D.boundary_active] using hx) q
        (by simpa [D.boundary_pieces] using hq))
    (fun x hx q hq =>
      D.boundaryPartitionTerm_eq_setIntegral x
        (by simpa [D.boundary_active] using hx) q
        (by simpa [D.boundary_pieces] using hq))
    (by
      simpa [D.boundary_active, D.boundary_pieces] using
        D.boundaryIntegrand_ae_eq_indicatorSum)

/-- Analytic boundary localization data rewritten to the selected M8 shape. -/
def toBoundaryMeasureLocalizationData :
    BoundaryMeasureLocalizationData μ selectedPartition.active
      targetImages.boundaryPieces
      D.boundaryPartition.boundaryPartitionTerm :=
  D.toSelectedBoundaryCompactMeasureFields.toBoundaryMeasureLocalizationData

/-- Fieldized boundary measure localization used by M8 adapters. -/
def toBoundaryMeasureLocalizationFields :
    BoundaryMeasureLocalizationFields selectedPartition.active
      targetImages.boundaryPieces
      D.boundaryPartition.boundaryPartitionTerm globalBoundaryIntegral :=
  D.toBoundaryMeasureLocalizationData.toBoundaryMeasureLocalizationFields
    globalBoundaryIntegral
    (by
      simpa [toBoundaryMeasureLocalizationData,
        toSelectedBoundaryCompactMeasureFields,
        BoundaryCompactMeasureFields.toBoundaryMeasureLocalizationData] using
        D.globalBoundaryIntegral_eq_boundaryMeasureIntegral)

/-- M8 boundary-only package induced by the boundary partition measure data. -/
def toM8BoundaryMeasureData :
    M8BoundaryMeasureData I omega selectedPartition targetImages :=
  M8BoundaryMeasureData.ofBoundaryMeasureLocalizationFields
    (I := I) (omega := omega) (selectedPartition := selectedPartition)
    (targetImages := targetImages)
    D.toBoundaryMeasureLocalizationFields

/--
Replace only the boundary half of an existing M8 measure-localization package.
-/
def replaceBoundary
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    M8MeasureLocalizationData I omega selectedPartition targetImages :=
  E.withBoundaryMeasureData D.toM8BoundaryMeasureData

@[simp]
theorem toBoundaryCompactMeasureFields_boundaryMeasureIntegral :
    D.toBoundaryCompactMeasureFields.boundaryMeasureIntegral =
      D.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem toSelectedBoundaryCompactMeasureFields_boundaryMeasureIntegral :
    D.toSelectedBoundaryCompactMeasureFields.boundaryMeasureIntegral =
      D.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem toBoundaryMeasureLocalizationData_boundaryMeasureIntegral :
    D.toBoundaryMeasureLocalizationData.boundaryMeasureIntegral =
      D.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem toBoundaryMeasureLocalizationFields_boundaryMeasureIntegral :
    D.toBoundaryMeasureLocalizationFields.boundaryMeasureIntegral =
      D.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem toM8BoundaryMeasureData_boundaryPartitionTerm :
    D.toM8BoundaryMeasureData.boundaryPartitionTerm =
      D.boundaryPartition.boundaryPartitionTerm :=
  rfl

@[simp]
theorem toM8BoundaryMeasureData_globalBoundaryIntegral :
    D.toM8BoundaryMeasureData.globalBoundaryIntegral =
      globalBoundaryIntegral :=
  rfl

@[simp]
theorem toM8BoundaryMeasureData_boundaryMeasureIntegral :
    D.toM8BoundaryMeasureData.boundaryMeasureIntegral =
      D.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem replaceBoundary_boundaryPartitionTerm
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    (D.replaceBoundary E).boundaryPartitionTerm =
      D.boundaryPartition.boundaryPartitionTerm :=
  rfl

@[simp]
theorem replaceBoundary_globalBoundaryIntegral
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    (D.replaceBoundary E).globalBoundaryIntegral =
      globalBoundaryIntegral :=
  rfl

@[simp]
theorem replaceBoundary_boundaryMeasureIntegral
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    (D.replaceBoundary E).boundaryMeasureIntegral =
      D.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem replaceBoundary_globalBulkIntegral
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    (D.replaceBoundary E).globalBulkIntegral =
      E.globalBulkIntegral :=
  rfl

@[simp]
theorem replaceBoundary_bulkMeasureIntegral
    (E : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    (D.replaceBoundary E).bulkMeasureIntegral =
      E.bulkMeasureIntegral :=
  rfl

/-- Boundary finite-sum projection supplied by the partition measure data. -/
theorem boundaryMeasureIntegral_eq_partitionSum :
    D.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces
        D.boundaryPartition.boundaryPartitionTerm := by
  simpa using
    D.toBoundaryMeasureLocalizationData.boundaryMeasureIntegral_eq_partitionSum

/--
M8 boundary finite-sum projection in terms of the produced boundary package.
-/
theorem toM8BoundaryMeasureData_boundaryMeasureIntegral_eq_partitionSum :
    D.toM8BoundaryMeasureData.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces
        D.boundaryPartition.boundaryPartitionTerm := by
  simpa using D.boundaryMeasureIntegral_eq_partitionSum

/--
Build the boundary-to-M8 package from compact-support integrability data for
each active unlocalized boundary-piece integrand.
-/
def ofCompactSupport
    [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
    [IsFiniteMeasureOnCompacts μ]
    (boundaryPartition : BoundaryMeasurePartitionData M BoundaryPiece)
    (boundary_active :
      boundaryPartition.activeCharts = selectedPartition.active)
    (boundary_pieces :
      boundaryPartition.boundaryPieces = targetImages.boundaryPieces)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : M → BoundaryPiece → Set α)
    (boundaryPieceIntegrand : M → BoundaryPiece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hglobal :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ boundaryPartition.activeCharts →
        ∀ q, q ∈ boundaryPartition.boundaryPieces x →
          MeasurableSet (boundaryPieceSet x q))
    (hcompact :
      ∀ x, x ∈ boundaryPartition.activeCharts →
        ∀ q, q ∈ boundaryPartition.boundaryPieces x →
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (hterm :
      ∀ x, x ∈ boundaryPartition.activeCharts →
        ∀ q, q ∈ boundaryPartition.boundaryPieces x →
          boundaryPartition.boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum boundaryPartition.activeCharts
          boundaryPartition.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand) :
    BoundaryMeasurePartitionToM8Data
      (α := α) I omega selectedPartition targetImages μ
      globalBoundaryIntegral where
  boundaryPartition := boundaryPartition
  boundary_active := boundary_active
  boundary_pieces := boundary_pieces
  boundaryIntegrand := boundaryIntegrand
  boundaryPieceSet := boundaryPieceSet
  boundaryPieceIntegrand := boundaryPieceIntegrand
  boundaryMeasureIntegral := boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := hglobal
  boundaryMeasureIntegral_eq_integral := hmeasure
  boundaryPieceSet_measurable := hset
  boundaryPieceIntegrableOn := fun x hx q hq =>
    (hcompact x hx q hq).integrableOn (boundaryPieceSet x q)
  boundaryPartitionTerm_eq_setIntegral := hterm
  boundaryIntegrand_ae_eq_indicatorSum := hboundary

end BoundaryMeasurePartitionToM8Data

namespace BoundaryMeasurePartitionData

variable {globalBoundaryIntegral : Real}
variable (P : BoundaryMeasurePartitionData M BoundaryPiece)

/--
Direct M8 boundary entry from explicit active-piece `IntegrableOn`
hypotheses.
-/
def toM8BoundaryMeasureDataOfIntegrableOn
    (hactive : P.activeCharts = selectedPartition.active)
    (hpieces : P.boundaryPieces = targetImages.boundaryPieces)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : M → BoundaryPiece → Set α)
    (boundaryPieceIntegrand : M → BoundaryPiece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hglobal :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          MeasurableSet (boundaryPieceSet x q))
    (hintegrable :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          IntegrableOn (boundaryPieceIntegrand x q) (boundaryPieceSet x q) μ)
    (hterm :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          P.boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum P.activeCharts P.boundaryPieces
          boundaryPieceSet boundaryPieceIntegrand) :
    M8BoundaryMeasureData I omega selectedPartition targetImages :=
  (BoundaryMeasurePartitionToM8Data.mk
    (boundaryPartition := P)
    (boundary_active := hactive)
    (boundary_pieces := hpieces)
    (boundaryIntegrand := boundaryIntegrand)
    (boundaryPieceSet := boundaryPieceSet)
    (boundaryPieceIntegrand := boundaryPieceIntegrand)
    (boundaryMeasureIntegral := boundaryMeasureIntegral)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral := hglobal)
    (boundaryMeasureIntegral_eq_integral := hmeasure)
    (boundaryPieceSet_measurable := hset)
    (boundaryPieceIntegrableOn := hintegrable)
    (boundaryPartitionTerm_eq_setIntegral := hterm)
    (boundaryIntegrand_ae_eq_indicatorSum := hboundary)).toM8BoundaryMeasureData

/--
Direct M8 boundary entry from compact-support integrability data for each
active unlocalized piece.
-/
def toM8BoundaryMeasureDataOfCompactSupport
    [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
    [IsFiniteMeasureOnCompacts μ]
    (hactive : P.activeCharts = selectedPartition.active)
    (hpieces : P.boundaryPieces = targetImages.boundaryPieces)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : M → BoundaryPiece → Set α)
    (boundaryPieceIntegrand : M → BoundaryPiece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hglobal :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          MeasurableSet (boundaryPieceSet x q))
    (hcompact :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (hterm :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          P.boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum P.activeCharts P.boundaryPieces
          boundaryPieceSet boundaryPieceIntegrand) :
    M8BoundaryMeasureData I omega selectedPartition targetImages :=
  (BoundaryMeasurePartitionToM8Data.ofCompactSupport
    (α := α) (μ := μ) (I := I) (omega := omega)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (globalBoundaryIntegral := globalBoundaryIntegral)
    P hactive hpieces boundaryIntegrand boundaryPieceSet
    boundaryPieceIntegrand boundaryMeasureIntegral hglobal hmeasure hset
    hcompact hterm hboundary).toM8BoundaryMeasureData

end BoundaryMeasurePartitionData

end BoundaryMeasurePartitionToM8

end Stokes

end
