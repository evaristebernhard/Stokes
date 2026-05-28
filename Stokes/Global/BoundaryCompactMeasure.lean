import Stokes.Global.BoundaryMeasureLocalization
import Stokes.Global.BoundaryIntegrabilityCompactSupport
import Stokes.Global.CompactSupportIntegrability
import Stokes.Global.MeasureBoxAPI

/-!
# Boundary compact-support measure localization

This file is the boundary-side analogue of the bulk measure-localization
constructor layer.  It packages the common handoff from compactly supported or
lower-face-localized boundary integrands to `BoundaryMeasureLocalizationData`.

The core theorem is still the existing finite indicator localization theorem
from `BoundaryMeasureLocalization`; this module only reduces the number of
fields downstream code has to fill by hand.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryCompactMeasure

universe a c p

variable {α : Type a} [MeasurableSpace α]
variable {Chart : Type c} {Piece : Type p}
variable {μ : Measure α}
variable {activeCharts : Finset Chart}
variable {boundaryPieces : Chart → Finset Piece}
variable {boundaryPartitionTerm : Chart → Piece → Real}

/--
Measure-level boundary localization fields phrased with set integrals.

Compared with `BoundaryMeasureLocalizationData`, this package asks for
`IntegrableOn` on the selected boundary-piece support sets and for partition
terms as set integrals.  The conversion below inserts indicators and supplies
the exact existing `BoundaryMeasureLocalizationData` shape.
-/
structure BoundaryCompactMeasureFields
    (μ : Measure α)
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart → Finset Piece)
    (boundaryPartitionTerm : Chart → Piece → Real) where
  /-- Boundary-side integrand whose integral is represented. -/
  boundaryIntegrand : α → Real
  /-- Localization set for one active boundary piece. -/
  boundaryPieceSet : Chart → Piece → Set α
  /-- Unlocalized scalar integrand for one boundary piece. -/
  boundaryPieceIntegrand : Chart → Piece → α → Real
  /-- The represented boundary measure integral. -/
  boundaryMeasureIntegral : Real
  /-- The represented integral is the integral of the global boundary integrand. -/
  boundaryMeasureIntegral_eq_integral :
    boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ
  /-- Active localization sets are measurable. -/
  boundaryPieceSet_measurable :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x → MeasurableSet (boundaryPieceSet x q)
  /-- Active unlocalized piece integrands are integrable on their support sets. -/
  boundaryPieceIntegrableOn :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x →
        IntegrableOn (boundaryPieceIntegrand x q) (boundaryPieceSet x q) μ
  /-- Active partition terms are the corresponding set integrals. -/
  boundaryPartitionTerm_eq_setIntegral :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x →
        boundaryPartitionTerm x q =
          ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ
  /-- A.e. reconstruction by the finite indicator-localized boundary sum. -/
  boundaryIntegrand_ae_eq_indicatorSum :
    boundaryIntegrand =ᵐ[μ]
      boundaryMeasureIndicatorSum activeCharts boundaryPieces
        boundaryPieceSet boundaryPieceIntegrand

namespace BoundaryCompactMeasureFields

/-- Stable constructor from explicit set-integral localization fields. -/
def ofSetIntegral
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x → MeasurableSet (boundaryPieceSet x q))
    (hintegrable :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          IntegrableOn (boundaryPieceIntegrand x q) (boundaryPieceSet x q) μ)
    (hterm :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum activeCharts boundaryPieces
          boundaryPieceSet boundaryPieceIntegrand) :
    BoundaryCompactMeasureFields μ activeCharts boundaryPieces
      boundaryPartitionTerm where
  boundaryIntegrand := boundaryIntegrand
  boundaryPieceSet := boundaryPieceSet
  boundaryPieceIntegrand := boundaryPieceIntegrand
  boundaryMeasureIntegral := boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_integral := hmeasure
  boundaryPieceSet_measurable := hset
  boundaryPieceIntegrableOn := hintegrable
  boundaryPartitionTerm_eq_setIntegral := hterm
  boundaryIntegrand_ae_eq_indicatorSum := hboundary

/-- Indicator-localized function attached to one recorded boundary piece. -/
def pieceIndicator
    (D :
      BoundaryCompactMeasureFields μ activeCharts boundaryPieces
        boundaryPartitionTerm)
    (x : Chart) (q : Piece) : α → Real :=
  boundaryMeasurePieceIndicator D.boundaryPieceSet D.boundaryPieceIntegrand x q

/-- The recorded `IntegrableOn` field makes the active indicator integrable. -/
theorem pieceIndicator_integrable
    (D :
      BoundaryCompactMeasureFields μ activeCharts boundaryPieces
        boundaryPartitionTerm)
    {x : Chart} (hx : x ∈ activeCharts)
    {q : Piece} (hq : q ∈ boundaryPieces x) :
    Integrable (D.pieceIndicator x q) μ := by
  simpa [pieceIndicator, boundaryMeasurePieceIndicator] using
    (D.boundaryPieceIntegrableOn x hx q hq).integrable_indicator
      (D.boundaryPieceSet_measurable x hx q hq)

/-- Rewrite an active set-integral partition term as an indicator integral. -/
theorem boundaryPartitionTerm_eq_indicatorIntegral
    (D :
      BoundaryCompactMeasureFields μ activeCharts boundaryPieces
        boundaryPartitionTerm)
    {x : Chart} (hx : x ∈ activeCharts)
    {q : Piece} (hq : q ∈ boundaryPieces x) :
    boundaryPartitionTerm x q =
      ∫ y, D.pieceIndicator x q y ∂μ := by
  calc
    boundaryPartitionTerm x q =
        ∫ y in D.boundaryPieceSet x q,
          D.boundaryPieceIntegrand x q y ∂μ :=
      D.boundaryPartitionTerm_eq_setIntegral x hx q hq
    _ = ∫ y, D.pieceIndicator x q y ∂μ := by
      simpa [pieceIndicator, boundaryMeasurePieceIndicator] using
        (integral_indicator
          (μ := μ) (f := D.boundaryPieceIntegrand x q)
          (D.boundaryPieceSet_measurable x hx q hq)).symm

/--
Convert compact/set-integral boundary fields to the existing
`BoundaryMeasureLocalizationData` API.
-/
def toBoundaryMeasureLocalizationData
    (D :
      BoundaryCompactMeasureFields μ activeCharts boundaryPieces
        boundaryPartitionTerm) :
    BoundaryMeasureLocalizationData μ activeCharts boundaryPieces
      boundaryPartitionTerm :=
  BoundaryMeasureLocalizationData.ofMeasureIntegralEqIndicatorSum
    D.boundaryIntegrand D.boundaryPieceSet D.boundaryPieceIntegrand
    D.boundaryMeasureIntegral D.boundaryMeasureIntegral_eq_integral
    D.boundaryIntegrand_ae_eq_indicatorSum
    (fun x hx q hq => D.pieceIndicator_integrable (x := x) hx (q := q) hq)
    (fun x hx q hq =>
      D.boundaryPartitionTerm_eq_indicatorIntegral (x := x) hx (q := q) hq)

@[simp]
theorem toBoundaryMeasureLocalizationData_boundaryMeasureIntegral
    (D :
      BoundaryCompactMeasureFields μ activeCharts boundaryPieces
        boundaryPartitionTerm) :
    D.toBoundaryMeasureLocalizationData.boundaryMeasureIntegral =
      D.boundaryMeasureIntegral :=
  rfl

/-- Boundary measure localization equality supplied by compact measure fields. -/
theorem boundaryMeasureIntegral_eq_partitionSum
    (D :
      BoundaryCompactMeasureFields μ activeCharts boundaryPieces
        boundaryPartitionTerm) :
    D.boundaryMeasureIntegral =
      selectedBoundaryPieceSum activeCharts boundaryPieces
        boundaryPartitionTerm :=
  D.toBoundaryMeasureLocalizationData.boundaryMeasureIntegral_eq_partitionSum

/-- Convert directly to boundary partition reconstruction data. -/
def toBoundaryIntegralPartitionReconstructionData
    (D :
      BoundaryCompactMeasureFields μ activeCharts boundaryPieces
        boundaryPartitionTerm)
    (globalBoundaryIntegral : Real)
    (hmeasure : globalBoundaryIntegral = D.boundaryMeasureIntegral) :
    BoundaryIntegralPartitionReconstructionData activeCharts boundaryPieces
      boundaryPartitionTerm globalBoundaryIntegral :=
  D.toBoundaryMeasureLocalizationData
    |>.toBoundaryIntegralPartitionReconstructionData
      globalBoundaryIntegral hmeasure

@[simp]
theorem toBoundaryIntegralPartitionReconstructionData_boundaryMeasureIntegral
    (D :
      BoundaryCompactMeasureFields μ activeCharts boundaryPieces
        boundaryPartitionTerm)
    (globalBoundaryIntegral : Real)
    (hmeasure : globalBoundaryIntegral = D.boundaryMeasureIntegral) :
    (D.toBoundaryIntegralPartitionReconstructionData
      globalBoundaryIntegral hmeasure).boundaryMeasureIntegral =
      D.boundaryMeasureIntegral :=
  rfl

/-- Final finite-sum reconstruction supplied by compact measure fields. -/
theorem globalBoundaryIntegral_eq_partitionSum
    (D :
      BoundaryCompactMeasureFields μ activeCharts boundaryPieces
        boundaryPartitionTerm)
    {globalBoundaryIntegral : Real}
    (hmeasure : globalBoundaryIntegral = D.boundaryMeasureIntegral) :
    globalBoundaryIntegral =
      selectedBoundaryPieceSum activeCharts boundaryPieces
        boundaryPartitionTerm :=
  hmeasure.trans D.boundaryMeasureIntegral_eq_partitionSum

section CompactSupportConstructor

variable [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
variable [IsFiniteMeasureOnCompacts μ]

/--
Constructor that discharges active piece integrability from compact-support
data for the unlocalized piece integrands.
-/
def ofCompactSupport
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x → MeasurableSet (boundaryPieceSet x q))
    (hcompact :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (hterm :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum activeCharts boundaryPieces
          boundaryPieceSet boundaryPieceIntegrand) :
    BoundaryCompactMeasureFields μ activeCharts boundaryPieces
      boundaryPartitionTerm :=
  ofSetIntegral boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset
    (fun x hx q hq => (hcompact x hx q hq).integrableOn (boundaryPieceSet x q))
    hterm hboundary

end CompactSupportConstructor

section LowerZeroFaceConstructor

variable {n : Nat}
variable {boundaryPartitionTerm : Chart → Piece → Real}

/--
Lower-zero-face constructor from already established face-domain
`IntegrableOn` hypotheses.
-/
def ofLowerZeroFaceIntegrable
    (boundaryIntegrand : (Fin n → Real) → Real)
    (lowerCorner upperCorner : Chart → Piece → Fin (n + 1) → Real)
    (boundaryPieceIntegrand : Chart → Piece → (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hintegrable :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          IntegrableOn (boundaryPieceIntegrand x q)
            (lowerZeroFaceDomain (lowerCorner x q) (upperCorner x q)))
    (hterm :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in lowerZeroFaceDomain (lowerCorner x q) (upperCorner x q),
              boundaryPieceIntegrand x q y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum activeCharts boundaryPieces
          (fun x q => lowerZeroFaceDomain (lowerCorner x q) (upperCorner x q))
          boundaryPieceIntegrand) :
    BoundaryCompactMeasureFields (α := Fin n → Real)
      (μ := volume) activeCharts boundaryPieces boundaryPartitionTerm :=
  ofSetIntegral (μ := (volume : Measure (Fin n → Real))) boundaryIntegrand
    (fun x q => lowerZeroFaceDomain (lowerCorner x q) (upperCorner x q))
    boundaryPieceIntegrand boundaryMeasureIntegral hmeasure
    (fun x _ q _ => measurableSet_lowerZeroFaceDomain (lowerCorner x q) (upperCorner x q))
    hintegrable hterm hboundary

/--
Lower-zero-face constructor that derives active piece integrability from
continuous compactly supported scalar boundary integrands.
-/
def ofLowerZeroFaceCompactSupport
    (boundaryIntegrand : (Fin n → Real) → Real)
    (lowerCorner upperCorner : Chart → Piece → Fin (n + 1) → Real)
    (boundaryPieceIntegrand : Chart → Piece → (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hcontinuous :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          Continuous (boundaryPieceIntegrand x q))
    (hcompact :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          HasCompactSupport (boundaryPieceIntegrand x q))
    (hterm :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in lowerZeroFaceDomain (lowerCorner x q) (upperCorner x q),
              boundaryPieceIntegrand x q y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum activeCharts boundaryPieces
          (fun x q => lowerZeroFaceDomain (lowerCorner x q) (upperCorner x q))
          boundaryPieceIntegrand) :
    BoundaryCompactMeasureFields (α := Fin n → Real)
      (μ := volume) activeCharts boundaryPieces boundaryPartitionTerm :=
  ofLowerZeroFaceIntegrable (boundaryPartitionTerm := boundaryPartitionTerm)
    boundaryIntegrand lowerCorner upperCorner
    boundaryPieceIntegrand boundaryMeasureIntegral hmeasure
    (fun x hx q hq =>
      integrableOn_lowerZeroFaceDomain_of_continuous_hasCompactSupport
        (a := lowerCorner x q) (b := upperCorner x q)
        (hf := hcontinuous x hx q hq) (hcf := hcompact x hx q hq))
    hterm hboundary

end LowerZeroFaceConstructor

end BoundaryCompactMeasureFields

end BoundaryCompactMeasure

end Stokes

end
