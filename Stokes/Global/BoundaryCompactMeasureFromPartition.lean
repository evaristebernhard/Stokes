import Stokes.Global.BoundaryMeasureFromPartition

/-!
# Boundary compact measure fields from partition-term alignment

This file is the boundary-side handoff from a geometric finite partition term
to the compact-support measure package.

The common situation is that the analytic set-integral reconstruction is first
proved for a local geometric term, while the global Stokes package is phrased
using a selected `boundaryPartitionTerm`.  A pointwise equality on active
boundary pieces is enough to transport the whole compact measure package and
its finite-sum reconstruction.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryCompactMeasureFromPartition

universe a c p

variable {Alpha : Type a} [MeasurableSpace Alpha]
variable {Chart : Type c} {Piece : Type p}
variable {mu : Measure Alpha}
variable {activeCharts : Finset Chart}
variable {boundaryPieces : Chart -> Finset Piece}
variable {oldTerm newTerm : Chart -> Piece -> Real}

/--
Pointwise equality on the selected active boundary pieces transports the
selected finite boundary-piece sum.
-/
theorem selectedBoundaryPieceSum_congr
    (hterm :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          oldTerm x q = newTerm x q) :
    selectedBoundaryPieceSum activeCharts boundaryPieces oldTerm =
      selectedBoundaryPieceSum activeCharts boundaryPieces newTerm := by
  refine Finset.sum_congr rfl ?_
  intro x hx
  refine Finset.sum_congr rfl ?_
  intro q hq
  exact hterm x hx q hq

namespace BoundaryCompactMeasureFields

/--
Transport compact boundary measure fields across a pointwise equality of the
recorded boundary partition terms on the active pieces.
-/
def congrBoundaryPartitionTerm
    (D :
      BoundaryCompactMeasureFields mu activeCharts boundaryPieces oldTerm)
    (hterm :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          oldTerm x q = newTerm x q) :
    BoundaryCompactMeasureFields mu activeCharts boundaryPieces newTerm where
  boundaryIntegrand := D.boundaryIntegrand
  boundaryPieceSet := D.boundaryPieceSet
  boundaryPieceIntegrand := D.boundaryPieceIntegrand
  boundaryMeasureIntegral := D.boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_integral :=
    D.boundaryMeasureIntegral_eq_integral
  boundaryPieceSet_measurable := D.boundaryPieceSet_measurable
  boundaryPieceIntegrableOn := D.boundaryPieceIntegrableOn
  boundaryPartitionTerm_eq_setIntegral := by
    intro x hx q hq
    exact (hterm x hx q hq).symm.trans
      (D.boundaryPartitionTerm_eq_setIntegral x hx q hq)
  boundaryIntegrand_ae_eq_indicatorSum :=
    D.boundaryIntegrand_ae_eq_indicatorSum

/--
The boundary measure integral localizes to a transported selected boundary
partition sum.
-/
theorem boundaryMeasureIntegral_eq_partitionSum_of_boundaryPartitionTerm_eq
    (D :
      BoundaryCompactMeasureFields mu activeCharts boundaryPieces oldTerm)
    (hterm :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          oldTerm x q = newTerm x q) :
    D.boundaryMeasureIntegral =
      selectedBoundaryPieceSum activeCharts boundaryPieces newTerm :=
  D.boundaryMeasureIntegral_eq_partitionSum.trans
    (selectedBoundaryPieceSum_congr (activeCharts := activeCharts)
      (boundaryPieces := boundaryPieces) (oldTerm := oldTerm)
      (newTerm := newTerm) hterm)

/--
Compact measure fields give boundary integral partition reconstruction after a
pointwise alignment of their geometric term with the selected partition term.
-/
def toBoundaryIntegralPartitionReconstructionData_of_boundaryPartitionTerm_eq
    (D :
      BoundaryCompactMeasureFields mu activeCharts boundaryPieces oldTerm)
    (manifoldBoundaryIntegral : Real)
    (hmeasure : manifoldBoundaryIntegral = D.boundaryMeasureIntegral)
    (hterm :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          oldTerm x q = newTerm x q) :
    BoundaryIntegralPartitionReconstructionData activeCharts boundaryPieces
      newTerm manifoldBoundaryIntegral :=
  BoundaryIntegralPartitionReconstructionData.ofBoundaryMeasureEq
    D.boundaryMeasureIntegral hmeasure
    (D.boundaryMeasureIntegral_eq_partitionSum_of_boundaryPartitionTerm_eq
      hterm)

/--
Final finite-sum reconstruction in the field shape supplied by compact measure
fields, with the selected partition term identified pointwise afterwards.
-/
theorem manifoldBoundaryIntegral_eq_partitionSum_of_boundaryPartitionTerm_eq
    (D :
      BoundaryCompactMeasureFields mu activeCharts boundaryPieces oldTerm)
    {manifoldBoundaryIntegral : Real}
    (hmeasure : manifoldBoundaryIntegral = D.boundaryMeasureIntegral)
    (hterm :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          oldTerm x q = newTerm x q) :
    manifoldBoundaryIntegral =
      selectedBoundaryPieceSum activeCharts boundaryPieces newTerm :=
  hmeasure.trans
    (D.boundaryMeasureIntegral_eq_partitionSum_of_boundaryPartitionTerm_eq
      hterm)

/--
Expanded nested-sum reconstruction in the field shape commonly consumed by
global boundary constructors.
-/
theorem manifoldBoundaryIntegral_eq_partitionSum_expanded_of_boundaryPartitionTerm_eq
    (D :
      BoundaryCompactMeasureFields mu activeCharts boundaryPieces oldTerm)
    {manifoldBoundaryIntegral : Real}
    (hmeasure : manifoldBoundaryIntegral = D.boundaryMeasureIntegral)
    (hterm :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          oldTerm x q = newTerm x q) :
    manifoldBoundaryIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun q => newTerm x q := by
  simpa [selectedBoundaryPieceSum] using
    D.manifoldBoundaryIntegral_eq_partitionSum_of_boundaryPartitionTerm_eq
      (newTerm := newTerm) hmeasure hterm

/--
Constructor from set-integral reconstruction of a geometric boundary term plus
pointwise alignment with the selected boundary partition term.
-/
def ofSetIntegralBoundaryTermEq
    (boundaryIntegrand : Alpha -> Real)
    (boundaryPieceSet : Chart -> Piece -> Set Alpha)
    (boundaryPieceIntegrand : Chart -> Piece -> Alpha -> Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂mu)
    (hset :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          MeasurableSet (boundaryPieceSet x q))
    (hintegrable :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          IntegrableOn (boundaryPieceIntegrand x q)
            (boundaryPieceSet x q) mu)
    (holdTerm :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          oldTerm x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (hterm :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          oldTerm x q = newTerm x q)
    (hboundary :
      boundaryIntegrand =ᵐ[mu]
        boundaryMeasureIndicatorSum activeCharts boundaryPieces
          boundaryPieceSet boundaryPieceIntegrand) :
    BoundaryCompactMeasureFields mu activeCharts boundaryPieces newTerm :=
  (BoundaryCompactMeasureFields.ofSetIntegral
    (μ := mu) (activeCharts := activeCharts)
    (boundaryPieces := boundaryPieces)
    (boundaryPartitionTerm := oldTerm)
    boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hintegrable holdTerm hboundary)
    |>.congrBoundaryPartitionTerm hterm

section CompactSupport

variable [TopologicalSpace Alpha] [OpensMeasurableSpace Alpha]
variable [T2Space Alpha] [IsFiniteMeasureOnCompacts mu]

/--
Compact-support version of `ofSetIntegralBoundaryTermEq`: active piece
integrability is discharged by compact-support integrability data.
-/
def ofCompactSupportBoundaryTermEq
    (boundaryIntegrand : Alpha -> Real)
    (boundaryPieceSet : Chart -> Piece -> Set Alpha)
    (boundaryPieceIntegrand : Chart -> Piece -> Alpha -> Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂mu)
    (hset :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          MeasurableSet (boundaryPieceSet x q))
    (hcompact :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (holdTerm :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          oldTerm x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (hterm :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          oldTerm x q = newTerm x q)
    (hboundary :
      boundaryIntegrand =ᵐ[mu]
        boundaryMeasureIndicatorSum activeCharts boundaryPieces
          boundaryPieceSet boundaryPieceIntegrand) :
    BoundaryCompactMeasureFields mu activeCharts boundaryPieces newTerm :=
  (BoundaryCompactMeasureFields.ofCompactSupport
    (μ := mu) (activeCharts := activeCharts)
    (boundaryPieces := boundaryPieces)
    (boundaryPartitionTerm := oldTerm)
    boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hcompact holdTerm hboundary)
    |>.congrBoundaryPartitionTerm hterm

end CompactSupport

end BoundaryCompactMeasureFields

namespace BoundaryMeasurePartitionData

variable (P : BoundaryMeasurePartitionData Chart Piece)

/--
A partition data package inherits compact boundary measure fields from a
geometric term once that term is pointwise identified with
`P.boundaryPartitionTerm` on active pieces.
-/
def compactFieldsOfIntegrableOnBoundaryTermEq
    (boundaryIntegrand : Alpha -> Real)
    (boundaryPieceSet : Chart -> Piece -> Set Alpha)
    (boundaryPieceIntegrand : Chart -> Piece -> Alpha -> Real)
    (boundaryMeasureIntegral : Real)
    (oldTerm : Chart -> Piece -> Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂mu)
    (hset :
      forall x, x ∈ P.activeCharts ->
        forall q, q ∈ P.boundaryPieces x ->
          MeasurableSet (boundaryPieceSet x q))
    (hintegrable :
      forall x, x ∈ P.activeCharts ->
        forall q, q ∈ P.boundaryPieces x ->
          IntegrableOn (boundaryPieceIntegrand x q)
            (boundaryPieceSet x q) mu)
    (holdTerm :
      forall x, x ∈ P.activeCharts ->
        forall q, q ∈ P.boundaryPieces x ->
          oldTerm x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (hterm :
      forall x, x ∈ P.activeCharts ->
        forall q, q ∈ P.boundaryPieces x ->
          oldTerm x q = P.boundaryPartitionTerm x q)
    (hboundary :
      boundaryIntegrand =ᵐ[mu]
        boundaryMeasureIndicatorSum P.activeCharts P.boundaryPieces
          boundaryPieceSet boundaryPieceIntegrand) :
    BoundaryCompactMeasureFields mu P.activeCharts P.boundaryPieces
      P.boundaryPartitionTerm :=
  BoundaryCompactMeasureFields.ofSetIntegralBoundaryTermEq
    (mu := mu) (activeCharts := P.activeCharts)
    (boundaryPieces := P.boundaryPieces) (oldTerm := oldTerm)
    (newTerm := P.boundaryPartitionTerm)
    boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hintegrable holdTerm hterm hboundary

end BoundaryMeasurePartitionData

end BoundaryCompactMeasureFromPartition

end Stokes

end
