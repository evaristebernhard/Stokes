import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Stokes.Global.BoundaryIntegralPartitionReconstruction

/-!
# Boundary measure localization

This file isolates the measure-theoretic finite-sum step on the boundary side.
The eventual manifold boundary measure is not fixed in this workspace yet, so
the main package is fieldized over an arbitrary measure.  Its analytic content
is the standard Bochner-integral statement: if the boundary integrand is
almost everywhere the finite sum of indicator-localized boundary-piece
integrands, and each selected piece integrates to the recorded boundary
partition term, then the boundary measure integral is the selected finite sum.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section PureMeasure

universe a c p

variable {α : Type a} [MeasurableSpace α]
variable {Chart : Type c} {Piece : Type p}

/-- Indicator-localized boundary piece integrand. -/
def boundaryMeasurePieceIndicator
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (x : Chart) (q : Piece) : α → Real :=
  (boundaryPieceSet x q).indicator (boundaryPieceIntegrand x q)

/-- Finite sum of arbitrary boundary-piece integrands. -/
def boundaryMeasurePieceSum
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart → Finset Piece)
    (boundaryPieceFunction : Chart → Piece → α → Real) : α → Real :=
  fun y =>
    Finset.sum activeCharts fun x =>
      Finset.sum (boundaryPieces x) fun q => boundaryPieceFunction x q y

/-- Finite sum of indicator-localized boundary-piece integrands. -/
def boundaryMeasureIndicatorSum
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart → Finset Piece)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real) : α → Real :=
  boundaryMeasurePieceSum activeCharts boundaryPieces
    (boundaryMeasurePieceIndicator boundaryPieceSet boundaryPieceIntegrand)

/--
Pure finite-sum localization for a boundary measure integral.

This is the reusable measure lemma behind the fieldized boundary localization
package below.
-/
theorem boundaryMeasureIntegral_eq_selectedBoundaryPieceSum_of_ae_eq
    (μ : Measure α)
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart → Finset Piece)
    (boundaryIntegrand : α → Real)
    (boundaryPieceFunction : Chart → Piece → α → Real)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasurePieceSum activeCharts boundaryPieces boundaryPieceFunction)
    (hpieceIntegrable :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          Integrable (boundaryPieceFunction x q) μ)
    (hterm :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          ∫ y, boundaryPieceFunction x q y ∂μ = boundaryPartitionTerm x q) :
    (∫ y, boundaryIntegrand y ∂μ) =
      selectedBoundaryPieceSum activeCharts boundaryPieces boundaryPartitionTerm := by
  calc
    (∫ y, boundaryIntegrand y ∂μ) =
        ∫ y, boundaryMeasurePieceSum activeCharts boundaryPieces
          boundaryPieceFunction y ∂μ :=
      integral_congr_ae hboundary
    _ =
        Finset.sum activeCharts fun x =>
          ∫ y, (Finset.sum (boundaryPieces x) fun q =>
            boundaryPieceFunction x q y) ∂μ := by
      exact integral_finset_sum activeCharts (fun x hx =>
        integrable_finset_sum (boundaryPieces x) (hpieceIntegrable x hx))
    _ =
        Finset.sum activeCharts fun x =>
          Finset.sum (boundaryPieces x) fun q =>
            ∫ y, boundaryPieceFunction x q y ∂μ := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      exact integral_finset_sum (boundaryPieces x) (hpieceIntegrable x hx)
    _ =
        Finset.sum activeCharts fun x =>
          Finset.sum (boundaryPieces x) fun q =>
            boundaryPartitionTerm x q := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      refine Finset.sum_congr rfl ?_
      intro q hq
      exact hterm x hx q hq
    _ = selectedBoundaryPieceSum activeCharts boundaryPieces
        boundaryPartitionTerm := by
      rfl

/--
Indicator-specialized finite-sum localization for a boundary measure integral.
-/
theorem boundaryMeasureIntegral_eq_selectedBoundaryPieceSum_of_ae_indicator_eq
    (μ : Measure α)
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart → Finset Piece)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum activeCharts boundaryPieces
          boundaryPieceSet boundaryPieceIntegrand)
    (hpieceIntegrable :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          Integrable
            (boundaryMeasurePieceIndicator boundaryPieceSet
              boundaryPieceIntegrand x q) μ)
    (hterm :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          (∫ y,
            boundaryMeasurePieceIndicator boundaryPieceSet
              boundaryPieceIntegrand x q y ∂μ) =
            boundaryPartitionTerm x q) :
    (∫ y, boundaryIntegrand y ∂μ) =
      selectedBoundaryPieceSum activeCharts boundaryPieces boundaryPartitionTerm :=
  boundaryMeasureIntegral_eq_selectedBoundaryPieceSum_of_ae_eq μ activeCharts
    boundaryPieces boundaryIntegrand
    (boundaryMeasurePieceIndicator boundaryPieceSet boundaryPieceIntegrand)
    boundaryPartitionTerm hboundary hpieceIntegrable hterm

end PureMeasure

section LocalizationData

universe a c p

variable {α : Type a} [MeasurableSpace α]
variable {Chart : Type c} {Piece : Type p}

/--
Fieldized boundary-measure localization data.

The measure `μ` is the eventual boundary measure placeholder.  The fields record
that the represented boundary integrand is AE equal to a finite sum of
indicator-localized piece integrands, and that each selected piece integrates
to the corresponding boundary partition term.
-/
structure BoundaryMeasureLocalizationData
    (μ : Measure α)
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart → Finset Piece)
    (boundaryPartitionTerm : Chart → Piece → Real) where
  /-- Boundary-side integrand whose integral is the represented measure integral. -/
  boundaryIntegrand : α → Real
  /-- Measurable-support placeholder for one localized boundary piece. -/
  boundaryPieceSet : Chart → Piece → Set α
  /-- Unlocalized integrand attached to one boundary piece. -/
  boundaryPieceIntegrand : Chart → Piece → α → Real
  /-- The represented boundary measure integral. -/
  boundaryMeasureIntegral : Real
  /-- The represented measure integral is the integral of `boundaryIntegrand`. -/
  boundaryMeasureIntegral_eq_integral :
    boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ
  /-- AE partition/indicator reconstruction of the boundary integrand. -/
  boundaryIntegrand_ae_eq_indicatorSum :
    boundaryIntegrand =ᵐ[μ]
      boundaryMeasureIndicatorSum activeCharts boundaryPieces
        boundaryPieceSet boundaryPieceIntegrand
  /-- Integrability of every active indicator-localized boundary piece. -/
  boundaryPieceIntegrable :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x →
        Integrable
          (boundaryMeasurePieceIndicator boundaryPieceSet
            boundaryPieceIntegrand x q) μ
  /-- Each active localized piece integrates to its selected partition term. -/
  boundaryPartitionTerm_eq_integral :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x →
        boundaryPartitionTerm x q =
          ∫ y,
            boundaryMeasurePieceIndicator boundaryPieceSet
              boundaryPieceIntegrand x q y ∂μ

namespace BoundaryMeasureLocalizationData

variable {μ : Measure α}
variable {activeCharts : Finset Chart}
variable {boundaryPieces : Chart → Finset Piece}
variable {boundaryPartitionTerm : Chart → Piece → Real}

/--
Stable constructor for the analytic boundary-measure localization package.

Downstream global statements should prefer this named constructor over filling
the structure fields directly, so that the measure/integrand bookkeeping can
change locally in this file.
-/
def ofMeasureIntegralEqIndicatorSum
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum activeCharts boundaryPieces
          boundaryPieceSet boundaryPieceIntegrand)
    (hpieceIntegrable :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          Integrable
            (boundaryMeasurePieceIndicator boundaryPieceSet
              boundaryPieceIntegrand x q) μ)
    (hterm :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y,
              boundaryMeasurePieceIndicator boundaryPieceSet
                boundaryPieceIntegrand x q y ∂μ) :
    BoundaryMeasureLocalizationData μ activeCharts boundaryPieces
      boundaryPartitionTerm where
  boundaryIntegrand := boundaryIntegrand
  boundaryPieceSet := boundaryPieceSet
  boundaryPieceIntegrand := boundaryPieceIntegrand
  boundaryMeasureIntegral := boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_integral := hmeasure
  boundaryIntegrand_ae_eq_indicatorSum := hboundary
  boundaryPieceIntegrable := hpieceIntegrable
  boundaryPartitionTerm_eq_integral := hterm

/-- The indicator-localized function attached to one boundary piece. -/
def pieceFunction
    (D :
      BoundaryMeasureLocalizationData μ activeCharts boundaryPieces
        boundaryPartitionTerm)
    (x : Chart) (q : Piece) : α → Real :=
  boundaryMeasurePieceIndicator D.boundaryPieceSet D.boundaryPieceIntegrand x q

/-- Integral of one active localized piece, rewritten as its selected term. -/
theorem piece_integral_eq_boundaryPartitionTerm
    (D :
      BoundaryMeasureLocalizationData μ activeCharts boundaryPieces
        boundaryPartitionTerm)
    {x : Chart} (hx : x ∈ activeCharts)
    {q : Piece} (hq : q ∈ boundaryPieces x) :
    (∫ y, D.pieceFunction x q y ∂μ) = boundaryPartitionTerm x q :=
  (D.boundaryPartitionTerm_eq_integral x hx q hq).symm

/--
The boundary measure integral localizes to the selected boundary-piece finite
sum.
-/
theorem boundaryMeasureIntegral_eq_selectedBoundaryPieceSum
    (D :
      BoundaryMeasureLocalizationData μ activeCharts boundaryPieces
        boundaryPartitionTerm) :
    D.boundaryMeasureIntegral =
      selectedBoundaryPieceSum activeCharts boundaryPieces
        boundaryPartitionTerm := by
  calc
    D.boundaryMeasureIntegral = ∫ y, D.boundaryIntegrand y ∂μ :=
      D.boundaryMeasureIntegral_eq_integral
    _ = selectedBoundaryPieceSum activeCharts boundaryPieces
        boundaryPartitionTerm :=
      boundaryMeasureIntegral_eq_selectedBoundaryPieceSum_of_ae_indicator_eq μ
        activeCharts boundaryPieces D.boundaryIntegrand D.boundaryPieceSet
        D.boundaryPieceIntegrand boundaryPartitionTerm
        D.boundaryIntegrand_ae_eq_indicatorSum D.boundaryPieceIntegrable
        (fun x hx q hq => D.piece_integral_eq_boundaryPartitionTerm hx hq)

/--
The boundary measure localization equality in the exact field shape required
by `BoundaryIntegralPartitionReconstructionData`.
-/
theorem boundaryMeasureIntegral_eq_partitionSum
    (D :
      BoundaryMeasureLocalizationData μ activeCharts boundaryPieces
        boundaryPartitionTerm) :
    D.boundaryMeasureIntegral =
      selectedBoundaryPieceSum activeCharts boundaryPieces
        boundaryPartitionTerm :=
  D.boundaryMeasureIntegral_eq_selectedBoundaryPieceSum

/-- Expanded nested finite-sum form of boundary measure localization. -/
theorem boundaryMeasureIntegral_eq_selectedBoundaryPieceSum_expanded
    (D :
      BoundaryMeasureLocalizationData μ activeCharts boundaryPieces
        boundaryPartitionTerm) :
    D.boundaryMeasureIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun q =>
          boundaryPartitionTerm x q := by
  simpa [selectedBoundaryPieceSum] using
    D.boundaryMeasureIntegral_eq_selectedBoundaryPieceSum

/--
Convert boundary-measure localization into the existing boundary partition
reconstruction package, once the represented manifold boundary integral is
identified with the measure integral.
-/
def toBoundaryIntegralPartitionReconstructionData
    (D :
      BoundaryMeasureLocalizationData μ activeCharts boundaryPieces
        boundaryPartitionTerm)
    (manifoldBoundaryIntegral : Real)
    (hmeasure : manifoldBoundaryIntegral = D.boundaryMeasureIntegral) :
    BoundaryIntegralPartitionReconstructionData activeCharts boundaryPieces
      boundaryPartitionTerm manifoldBoundaryIntegral :=
  BoundaryIntegralPartitionReconstructionData.ofBoundaryMeasureEq
    D.boundaryMeasureIntegral hmeasure
    D.boundaryMeasureIntegral_eq_partitionSum

@[simp]
theorem toBoundaryIntegralPartitionReconstructionData_boundaryMeasureIntegral
    (D :
      BoundaryMeasureLocalizationData μ activeCharts boundaryPieces
        boundaryPartitionTerm)
    (manifoldBoundaryIntegral : Real)
    (hmeasure : manifoldBoundaryIntegral = D.boundaryMeasureIntegral) :
    (D.toBoundaryIntegralPartitionReconstructionData
        manifoldBoundaryIntegral hmeasure).boundaryMeasureIntegral =
      D.boundaryMeasureIntegral :=
  rfl

/--
Projection theorem for the finite-sum reconstruction supplied by the partition
package produced from boundary-measure localization.
-/
theorem toBoundaryIntegralPartitionReconstructionData_boundaryMeasureIntegral_eq_partitionSum
    (D :
      BoundaryMeasureLocalizationData μ activeCharts boundaryPieces
        boundaryPartitionTerm)
    (manifoldBoundaryIntegral : Real)
    (hmeasure : manifoldBoundaryIntegral = D.boundaryMeasureIntegral) :
    (D.toBoundaryIntegralPartitionReconstructionData
        manifoldBoundaryIntegral hmeasure).boundaryMeasureIntegral =
      selectedBoundaryPieceSum activeCharts boundaryPieces
        boundaryPartitionTerm :=
  (D.toBoundaryIntegralPartitionReconstructionData
    manifoldBoundaryIntegral hmeasure).boundaryMeasureIntegral_eq_partitionSum

/--
Projection theorem in the final manifold-boundary-integral shape.  This is the
statement later M8 constructors usually need, without exposing the intermediate
record fields.
-/
theorem toBoundaryIntegralPartitionReconstructionData_manifoldBoundaryIntegral_eq_partitionSum
    (D :
      BoundaryMeasureLocalizationData μ activeCharts boundaryPieces
        boundaryPartitionTerm)
    (manifoldBoundaryIntegral : Real)
    (hmeasure : manifoldBoundaryIntegral = D.boundaryMeasureIntegral) :
    manifoldBoundaryIntegral =
      selectedBoundaryPieceSum activeCharts boundaryPieces
        boundaryPartitionTerm :=
  (D.toBoundaryIntegralPartitionReconstructionData
    manifoldBoundaryIntegral hmeasure).manifoldBoundaryIntegral_eq_partitionSum

/--
Forget the intermediate measure integral after localization, retaining the core
boundary finite-sum reconstruction package.
-/
def toBoundaryIntegralReconstructionData
    (D :
      BoundaryMeasureLocalizationData μ activeCharts boundaryPieces
        boundaryPartitionTerm)
    (manifoldBoundaryIntegral : Real)
    (hmeasure : manifoldBoundaryIntegral = D.boundaryMeasureIntegral) :
    BoundaryIntegralReconstructionData activeCharts boundaryPieces
      boundaryPartitionTerm manifoldBoundaryIntegral :=
  (D.toBoundaryIntegralPartitionReconstructionData
    manifoldBoundaryIntegral hmeasure).toBoundaryIntegralReconstructionData

/-- The core boundary reconstruction package obtained from localization. -/
theorem toBoundaryIntegralReconstructionData_manifoldBoundaryIntegral_eq_selectedBoundarySum
    (D :
      BoundaryMeasureLocalizationData μ activeCharts boundaryPieces
        boundaryPartitionTerm)
    (manifoldBoundaryIntegral : Real)
    (hmeasure : manifoldBoundaryIntegral = D.boundaryMeasureIntegral) :
    manifoldBoundaryIntegral =
      selectedBoundaryPieceSum activeCharts boundaryPieces
        boundaryPartitionTerm :=
  (D.toBoundaryIntegralReconstructionData
    manifoldBoundaryIntegral hmeasure).manifoldBoundaryIntegral_eq_selectedBoundarySum

/--
Direct finite-sum localization for a manifold boundary integral once it is
identified with the fieldized boundary measure integral.
-/
theorem manifoldBoundaryIntegral_eq_selectedBoundaryPieceSum
    (D :
      BoundaryMeasureLocalizationData μ activeCharts boundaryPieces
        boundaryPartitionTerm)
    {manifoldBoundaryIntegral : Real}
    (hmeasure : manifoldBoundaryIntegral = D.boundaryMeasureIntegral) :
    manifoldBoundaryIntegral =
      selectedBoundaryPieceSum activeCharts boundaryPieces
        boundaryPartitionTerm :=
  hmeasure.trans D.boundaryMeasureIntegral_eq_selectedBoundaryPieceSum

end BoundaryMeasureLocalizationData

end LocalizationData

end Stokes

end
