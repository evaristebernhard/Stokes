import Stokes.Global.BoundaryScalarPartitionIdentity
import Stokes.Global.BoundaryPartitionReconstructionFromSupport

/-!
# Cover-indexed boundary reconstruction

This file exposes the boundary indicator reconstruction in the cover-indexed
shape

`G_omega = sum i, indicator (boundarySet i) (G_i)`,

without routing callers through the older selected-partition chart/piece
indices.  Internally, the connection to the existing boundary measure package
uses a one-point piece fiber, so the public hypotheses stay cover-indexed while
`BoundaryCompactMeasureFields` and reconstruction data remain reusable.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedBoundaryReconstruction

universe c a

variable {Cover : Type c}
variable {alpha : Type a} [MeasurableSpace alpha]
variable {mu : Measure alpha}

/-- The one-piece boundary fiber used to view cover-indexed boundary data as
the existing chart/piece-indexed boundary measure data. -/
def coverIndexedBoundaryPieces {Cover : Type c} : Cover -> Finset Unit :=
  fun _ => {()}

/-- Cover-indexed boundary support sets as one-piece boundary support sets. -/
def coverIndexedBoundaryPieceSet
    (boundarySet : Cover -> Set alpha) :
    Cover -> Unit -> Set alpha :=
  fun i _ => boundarySet i

/-- Cover-indexed boundary scalar representatives as one-piece representatives. -/
def coverIndexedBoundaryPieceIntegrand
    (G : Cover -> alpha -> Real) :
    Cover -> Unit -> alpha -> Real :=
  fun i _ => G i

/-- Cover-indexed boundary terms as one-piece boundary partition terms. -/
def coverIndexedBoundaryPartitionTerm
    (boundaryTerm : Cover -> Real) :
    Cover -> Unit -> Real :=
  fun i _ => boundaryTerm i

/-- Pointwise cover-indexed boundary reconstruction from a finite scalar sum and
zero-off support control. -/
theorem coverIndexed_boundaryIntegrand_eq_indicator_sum
    (activeCover : Finset Cover)
    (G_omega : alpha -> Real)
    (boundarySet : Cover -> Set alpha)
    (G : Cover -> alpha -> Real)
    (hrespect :
      forall y,
        G_omega y = Finset.sum activeCover fun i => G i y)
    (hzero :
      forall i, i ∈ activeCover ->
        forall y, y ∉ boundarySet i -> G i y = 0) :
    G_omega =
      fun y => Finset.sum activeCover fun i =>
        (boundarySet i).indicator (G i) y := by
  funext y
  calc
    G_omega y = Finset.sum activeCover fun i => G i y := hrespect y
    _ =
        Finset.sum activeCover fun i =>
          (boundarySet i).indicator (G i) y := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hy : y ∈ boundarySet i
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy, hzero i hi y hy]

/-- A.e. cover-indexed boundary reconstruction from a finite scalar sum and
zero-off support control. -/
theorem coverIndexed_boundaryIntegrand_ae_eq_indicator_sum
    (activeCover : Finset Cover)
    (G_omega : alpha -> Real)
    (boundarySet : Cover -> Set alpha)
    (G : Cover -> alpha -> Real)
    (hrespect :
      forall y,
        G_omega y = Finset.sum activeCover fun i => G i y)
    (hzero :
      forall i, i ∈ activeCover ->
        forall y, y ∉ boundarySet i -> G i y = 0) :
    G_omega =ᵐ[mu]
      fun y => Finset.sum activeCover fun i =>
        (boundarySet i).indicator (G i) y :=
  ae_of_all mu fun y =>
    congrFun
      (coverIndexed_boundaryIntegrand_eq_indicator_sum
        activeCover G_omega boundarySet G hrespect hzero) y

/-- Signed cover-indexed boundary reconstruction.  The sign is folded into the
piece representatives, while zero-off support may still be proved for the
unsigned representatives. -/
theorem coverIndexed_signed_boundaryIntegrand_ae_eq_indicator_sum
    (boundarySign : Real)
    (activeCover : Finset Cover)
    (G_omega : alpha -> Real)
    (boundarySet : Cover -> Set alpha)
    (G : Cover -> alpha -> Real)
    (hrespect :
      forall y,
        G_omega y =
          Finset.sum activeCover fun i => boundarySign * G i y)
    (hzero :
      forall i, i ∈ activeCover ->
        forall y, y ∉ boundarySet i -> G i y = 0) :
    G_omega =ᵐ[mu]
      fun y => Finset.sum activeCover fun i =>
        (boundarySet i).indicator
          (fun z => boundarySign * G i z) y := by
  exact
    coverIndexed_boundaryIntegrand_ae_eq_indicator_sum
      (mu := mu) activeCover G_omega boundarySet
      (fun i z => boundarySign * G i z) hrespect
      (fun i hi y hy => by simp [hzero i hi y hy])

/-- Outward-first signed cover-indexed boundary reconstruction. -/
theorem outwardFirst_coverIndexed_boundaryIntegrand_ae_eq_indicator_sum
    (n : Nat)
    (activeCover : Finset Cover)
    (G_omega : alpha -> Real)
    (boundarySet : Cover -> Set alpha)
    (G : Cover -> alpha -> Real)
    (hrespect :
      forall y,
        G_omega y =
          Finset.sum activeCover fun i =>
            outwardFirstBoundaryOrientationSign n * G i y)
    (hzero :
      forall i, i ∈ activeCover ->
        forall y, y ∉ boundarySet i -> G i y = 0) :
    G_omega =ᵐ[mu]
      fun y => Finset.sum activeCover fun i =>
        (boundarySet i).indicator
          (fun z => outwardFirstBoundaryOrientationSign n * G i z) y :=
  coverIndexed_signed_boundaryIntegrand_ae_eq_indicator_sum
    (mu := mu) (outwardFirstBoundaryOrientationSign n)
    activeCover G_omega boundarySet G hrespect hzero

/-- Cover-indexed compact/set-integral boundary measure fields from finite
scalar reconstruction plus zero-off support control. -/
def coverIndexed_boundaryMeasureFields_of_support_reconstruction
    (activeCover : Finset Cover)
    (G_omega : alpha -> Real)
    (boundarySet : Cover -> Set alpha)
    (G : Cover -> alpha -> Real)
    (boundaryTerm : Cover -> Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, G_omega y ∂mu)
    (hset :
      forall i, i ∈ activeCover -> MeasurableSet (boundarySet i))
    (hintegrable :
      forall i, i ∈ activeCover ->
        IntegrableOn (G i) (boundarySet i) mu)
    (hterm :
      forall i, i ∈ activeCover ->
        boundaryTerm i = ∫ y in boundarySet i, G i y ∂mu)
    (hrespect :
      forall y,
        G_omega y = Finset.sum activeCover fun i => G i y)
    (hzero :
      forall i, i ∈ activeCover ->
        forall y, y ∉ boundarySet i -> G i y = 0) :
    BoundaryCompactMeasureFields mu activeCover
      (coverIndexedBoundaryPieces (Cover := Cover))
      (coverIndexedBoundaryPartitionTerm boundaryTerm) :=
  BoundaryCompactMeasureFields.ofSetIntegral
    (μ := mu) (activeCharts := activeCover)
    (boundaryPieces := coverIndexedBoundaryPieces (Cover := Cover))
    (boundaryPartitionTerm := coverIndexedBoundaryPartitionTerm boundaryTerm)
    G_omega
    (coverIndexedBoundaryPieceSet boundarySet)
    (coverIndexedBoundaryPieceIntegrand G)
    boundaryMeasureIntegral hmeasure
    (by
      intro i hi q hq
      simpa [coverIndexedBoundaryPieceSet] using hset i hi)
    (by
      intro i hi q hq
      simpa [coverIndexedBoundaryPieceSet,
        coverIndexedBoundaryPieceIntegrand] using hintegrable i hi)
    (by
      intro i hi q hq
      simpa [coverIndexedBoundaryPieceSet,
        coverIndexedBoundaryPieceIntegrand,
        coverIndexedBoundaryPartitionTerm] using hterm i hi)
    (by
      exact
        (coverIndexed_boundaryIntegrand_ae_eq_indicator_sum
          (mu := mu) activeCover G_omega boundarySet G hrespect hzero).mono
          (fun y hy => by
            simpa [boundaryMeasureIndicatorSum, boundaryMeasurePieceSum,
              boundaryMeasurePieceIndicator,
              coverIndexedBoundaryPieces, coverIndexedBoundaryPieceSet,
              coverIndexedBoundaryPieceIntegrand] using hy))

/-- Cover-indexed boundary integral reconstruction data obtained from the
compact measure fields above. -/
def coverIndexed_boundaryReconstructionData_of_support_reconstruction
    (activeCover : Finset Cover)
    (G_omega : alpha -> Real)
    (boundarySet : Cover -> Set alpha)
    (G : Cover -> alpha -> Real)
    (boundaryTerm : Cover -> Real)
    (globalBoundaryIntegral boundaryMeasureIntegral : Real)
    (hglobal : globalBoundaryIntegral = boundaryMeasureIntegral)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, G_omega y ∂mu)
    (hset :
      forall i, i ∈ activeCover -> MeasurableSet (boundarySet i))
    (hintegrable :
      forall i, i ∈ activeCover ->
        IntegrableOn (G i) (boundarySet i) mu)
    (hterm :
      forall i, i ∈ activeCover ->
        boundaryTerm i = ∫ y in boundarySet i, G i y ∂mu)
    (hrespect :
      forall y,
        G_omega y = Finset.sum activeCover fun i => G i y)
    (hzero :
      forall i, i ∈ activeCover ->
        forall y, y ∉ boundarySet i -> G i y = 0) :
    BoundaryIntegralPartitionReconstructionData activeCover
      (coverIndexedBoundaryPieces (Cover := Cover))
      (coverIndexedBoundaryPartitionTerm boundaryTerm)
      globalBoundaryIntegral :=
  (coverIndexed_boundaryMeasureFields_of_support_reconstruction
    (mu := mu) activeCover G_omega boundarySet G boundaryTerm
    boundaryMeasureIntegral hmeasure hset hintegrable hterm hrespect hzero)
    |>.toBoundaryIntegralPartitionReconstructionData
      globalBoundaryIntegral
      (by
        simpa [coverIndexed_boundaryMeasureFields_of_support_reconstruction]
          using hglobal)

/-- Outward-first signed cover-indexed compact/set-integral boundary fields. -/
def outwardFirst_coverIndexed_boundaryMeasureFields_of_support_reconstruction
    (n : Nat)
    (activeCover : Finset Cover)
    (G_omega : alpha -> Real)
    (boundarySet : Cover -> Set alpha)
    (G : Cover -> alpha -> Real)
    (boundaryTerm : Cover -> Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, G_omega y ∂mu)
    (hset :
      forall i, i ∈ activeCover -> MeasurableSet (boundarySet i))
    (hintegrable :
      forall i, i ∈ activeCover ->
        IntegrableOn
          (fun y => outwardFirstBoundaryOrientationSign n * G i y)
          (boundarySet i) mu)
    (hterm :
      forall i, i ∈ activeCover ->
        boundaryTerm i =
          ∫ y in boundarySet i,
            outwardFirstBoundaryOrientationSign n * G i y ∂mu)
    (hrespect :
      forall y,
        G_omega y =
          Finset.sum activeCover fun i =>
            outwardFirstBoundaryOrientationSign n * G i y)
    (hzero :
      forall i, i ∈ activeCover ->
        forall y, y ∉ boundarySet i -> G i y = 0) :
    BoundaryCompactMeasureFields mu activeCover
      (coverIndexedBoundaryPieces (Cover := Cover))
      (coverIndexedBoundaryPartitionTerm boundaryTerm) :=
  coverIndexed_boundaryMeasureFields_of_support_reconstruction
    (mu := mu) activeCover G_omega boundarySet
    (fun i y => outwardFirstBoundaryOrientationSign n * G i y)
    boundaryTerm boundaryMeasureIntegral hmeasure hset hintegrable hterm
    hrespect
    (fun i hi y hy => by simp [hzero i hi y hy])

end CoverIndexedBoundaryReconstruction

end Stokes

end
