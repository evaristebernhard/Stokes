import Stokes.Global.BoundaryCompactMeasure

/-!
# Boundary measure localization from partition data

This file adds a thin boundary-only entry point from finite boundary partition
data to the existing measure-localization packages.

The mathematical input is still explicit: boundary-piece support sets,
piece integrands, compact-support or integrability hypotheses, and the a.e.
indicator reconstruction of the boundary integrand.  The output is the stable
`BoundaryCompactMeasureFields` / `BoundaryMeasureLocalizationData` API.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryMeasureFromPartition

universe a c p

variable {α : Type a} [MeasurableSpace α]
variable {Chart : Type c} {Piece : Type p}
variable {μ : Measure α}

/--
Finite boundary partition data, stripped down to the part used by the measure
localization layer.
-/
structure BoundaryMeasurePartitionData (Chart : Type c) (Piece : Type p) where
  /-- Active chart labels in the selected boundary decomposition. -/
  activeCharts : Finset Chart
  /-- Boundary pieces assigned to each active chart. -/
  boundaryPieces : Chart → Finset Piece
  /-- The finite partition term attached to one boundary piece. -/
  boundaryPartitionTerm : Chart → Piece → Real

namespace BoundaryMeasurePartitionData

variable (P : BoundaryMeasurePartitionData Chart Piece)

/-- The selected finite boundary-partition sum recorded by `P`. -/
def boundaryPartitionSum : Real :=
  selectedBoundaryPieceSum P.activeCharts P.boundaryPieces
    P.boundaryPartitionTerm

/--
Construct compact/set-integral boundary measure fields from explicit active
piece `IntegrableOn` hypotheses.
-/
def compactFieldsOfIntegrableOn
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x → MeasurableSet (boundaryPieceSet x q))
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
    BoundaryCompactMeasureFields μ P.activeCharts P.boundaryPieces
      P.boundaryPartitionTerm :=
  BoundaryCompactMeasureFields.ofSetIntegral
    (μ := μ) (activeCharts := P.activeCharts)
    (boundaryPieces := P.boundaryPieces)
    (boundaryPartitionTerm := P.boundaryPartitionTerm)
    boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hintegrable hterm hboundary

/--
Construct analytic boundary localization data from explicit active
`IntegrableOn` hypotheses.
-/
def localizationDataOfIntegrableOn
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x → MeasurableSet (boundaryPieceSet x q))
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
    BoundaryMeasureLocalizationData μ P.activeCharts P.boundaryPieces
      P.boundaryPartitionTerm :=
  (P.compactFieldsOfIntegrableOn
    (μ := μ) boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hintegrable hterm hboundary)
    |>.toBoundaryMeasureLocalizationData

/--
Direct constructor for `BoundaryMeasureLocalizationData` when the caller has
already proved indicator-level integrability and indicator integral terms.
-/
def localizationDataOfIndicatorIntegrable
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum P.activeCharts P.boundaryPieces
          boundaryPieceSet boundaryPieceIntegrand)
    (hpieceIntegrable :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          Integrable
            (boundaryMeasurePieceIndicator boundaryPieceSet
              boundaryPieceIntegrand x q) μ)
    (hterm :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          P.boundaryPartitionTerm x q =
            ∫ y,
              boundaryMeasurePieceIndicator boundaryPieceSet
                boundaryPieceIntegrand x q y ∂μ) :
    BoundaryMeasureLocalizationData μ P.activeCharts P.boundaryPieces
      P.boundaryPartitionTerm :=
  BoundaryMeasureLocalizationData.ofMeasureIntegralEqIndicatorSum
    (μ := μ) (activeCharts := P.activeCharts)
    (boundaryPieces := P.boundaryPieces)
    (boundaryPartitionTerm := P.boundaryPartitionTerm)
    boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hboundary hpieceIntegrable hterm

section CompactSupport

variable [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
variable [IsFiniteMeasureOnCompacts μ]

/--
Construct compact/set-integral boundary measure fields when every active piece
integrand comes with compact-support integrability data.
-/
def compactFieldsOfCompactSupport
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x → MeasurableSet (boundaryPieceSet x q))
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
    BoundaryCompactMeasureFields μ P.activeCharts P.boundaryPieces
      P.boundaryPartitionTerm :=
  BoundaryCompactMeasureFields.ofCompactSupport
    (μ := μ) (activeCharts := P.activeCharts)
    (boundaryPieces := P.boundaryPieces)
    (boundaryPartitionTerm := P.boundaryPartitionTerm)
    boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hcompact hterm hboundary

/--
Construct analytic boundary localization data from compact-support
integrability on each active boundary piece.
-/
def localizationDataOfCompactSupport
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x → MeasurableSet (boundaryPieceSet x q))
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
    BoundaryMeasureLocalizationData μ P.activeCharts P.boundaryPieces
      P.boundaryPartitionTerm :=
  (P.compactFieldsOfCompactSupport
    (μ := μ) boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hcompact hterm hboundary)
    |>.toBoundaryMeasureLocalizationData

end CompactSupport

end BoundaryMeasurePartitionData

end BoundaryMeasureFromPartition

end Stokes

end
