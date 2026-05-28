import Stokes.Global.CoverIndexedBoundaryReconstruction
import Stokes.Global.CoverIndexedMeasureFields

/-!
# Cover-indexed boundary measure constructors

This file packages the resolved boundary-measure side of the cover-indexed
compact-support route.  The hard geometric data is assumed to have already
been resolved: boundary chart choices, orientation/sign conventions, target
image data, and the scalar boundary representatives.

The constructors here remove one layer of manual wiring from
`SupportControlledCoverIndexedMeasureInput`: once the local boundary terms are
known to be the corresponding set integrals, and the global boundary scalar is
known either as an indicator sum or as an unlocalized finite sum with support
control, the `CoverIndexedSetIntegralFields` boundary package is produced
directly.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

universe u a

section BoundaryMeasureConstructor

variable {ι : Type u}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]

/--
Boundary set-integral fields from a resolved indicator-sum reconstruction.

This is the thinnest constructor: all compact-support/integrability hypotheses
are kept in their natural compact/continuous/`tsupport` form, and the resolved
boundary chart/orientation machinery supplies the a.e. indicator
reconstruction.
-/
def coverIndexed_boundarySetIntegralFields_of_indicator_reconstruction
    (active : Finset ι)
    (localBoundary : ι → Real)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : ι → Set α)
    (boundaryPieceIntegrand : ι → α → Real)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (boundaryPiece_isCompact :
      ∀ i, i ∈ active → IsCompact (boundaryPieceSet i))
    (boundaryPiece_continuousOn :
      ∀ i, i ∈ active →
        ContinuousOn (boundaryPieceIntegrand i) (boundaryPieceSet i))
    (boundaryPiece_tsupport_subset :
      ∀ i, i ∈ active →
        tsupport (boundaryPieceIntegrand i) ⊆ boundaryPieceSet i)
    (localBoundary_eq_setIntegral :
      ∀ i, i ∈ active →
        localBoundary i =
          ∫ y in boundaryPieceSet i, boundaryPieceIntegrand i y ∂μ)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[μ]
        fun y => Finset.sum active fun i =>
          (boundaryPieceSet i).indicator (boundaryPieceIntegrand i) y) :
    CoverIndexedSetIntegralFields
      (α := α) active μ localBoundary :=
  CoverIndexedSetIntegralFields.ofTSupportSubsetCompactBoxIndicator
    (μ := μ) active localBoundary boundaryIntegrand boundaryPieceSet
    boundaryPieceIntegrand globalBoundaryIntegral
    globalBoundaryIntegral_eq_integral boundaryPiece_isCompact
    boundaryPiece_continuousOn boundaryPiece_tsupport_subset
    localBoundary_eq_setIntegral boundaryIntegrand_ae_eq_indicatorSum

/--
Boundary set-integral fields from an unlocalized a.e. finite-sum
reconstruction.

Support control turns the unlocalized sum
`∑ i, boundaryPieceIntegrand i y` into the indicator sum expected by the
measure package.
-/
def coverIndexed_boundarySetIntegralFields_of_ae_piece_sum
    (active : Finset ι)
    (localBoundary : ι → Real)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : ι → Set α)
    (boundaryPieceIntegrand : ι → α → Real)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (boundaryPiece_isCompact :
      ∀ i, i ∈ active → IsCompact (boundaryPieceSet i))
    (boundaryPiece_continuousOn :
      ∀ i, i ∈ active →
        ContinuousOn (boundaryPieceIntegrand i) (boundaryPieceSet i))
    (boundaryPiece_tsupport_subset :
      ∀ i, i ∈ active →
        tsupport (boundaryPieceIntegrand i) ⊆ boundaryPieceSet i)
    (localBoundary_eq_setIntegral :
      ∀ i, i ∈ active →
        localBoundary i =
          ∫ y in boundaryPieceSet i, boundaryPieceIntegrand i y ∂μ)
    (boundaryIntegrand_ae_eq_pieceSum :
      boundaryIntegrand =ᵐ[μ]
        fun y => Finset.sum active fun i =>
          boundaryPieceIntegrand i y) :
    CoverIndexedSetIntegralFields
      (α := α) active μ localBoundary :=
  CoverIndexedSetIntegralFields.ofTSupportSubsetCompactBoxPieceSum
    (μ := μ) active localBoundary boundaryIntegrand boundaryPieceSet
    boundaryPieceIntegrand globalBoundaryIntegral
    globalBoundaryIntegral_eq_integral boundaryPiece_isCompact
    boundaryPiece_continuousOn boundaryPiece_tsupport_subset
    localBoundary_eq_setIntegral boundaryIntegrand_ae_eq_pieceSum

/--
Boundary set-integral fields from a pointwise finite-sum identity.

This is often the most convenient endpoint for resolved chart data: prove the
scalar representative identity pointwise, and let the constructor convert it
to the a.e. measure reconstruction.
-/
def coverIndexed_boundarySetIntegralFields_of_pointwise_piece_sum
    (active : Finset ι)
    (localBoundary : ι → Real)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : ι → Set α)
    (boundaryPieceIntegrand : ι → α → Real)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (boundaryPiece_isCompact :
      ∀ i, i ∈ active → IsCompact (boundaryPieceSet i))
    (boundaryPiece_continuousOn :
      ∀ i, i ∈ active →
        ContinuousOn (boundaryPieceIntegrand i) (boundaryPieceSet i))
    (boundaryPiece_tsupport_subset :
      ∀ i, i ∈ active →
        tsupport (boundaryPieceIntegrand i) ⊆ boundaryPieceSet i)
    (localBoundary_eq_setIntegral :
      ∀ i, i ∈ active →
        localBoundary i =
          ∫ y in boundaryPieceSet i, boundaryPieceIntegrand i y ∂μ)
    (boundaryIntegrand_eq_pieceSum :
      ∀ y,
        boundaryIntegrand y =
          Finset.sum active fun i => boundaryPieceIntegrand i y) :
    CoverIndexedSetIntegralFields
      (α := α) active μ localBoundary :=
  coverIndexed_boundarySetIntegralFields_of_ae_piece_sum
    (μ := μ) active localBoundary boundaryIntegrand boundaryPieceSet
    boundaryPieceIntegrand globalBoundaryIntegral
    globalBoundaryIntegral_eq_integral boundaryPiece_isCompact
    boundaryPiece_continuousOn boundaryPiece_tsupport_subset
    localBoundary_eq_setIntegral
    (ae_of_all μ boundaryIntegrand_eq_pieceSum)

/--
Boundary set-integral fields from a pointwise finite-sum identity plus
zero-off support control.

Unlike `coverIndexed_boundarySetIntegralFields_of_pointwise_piece_sum`, this
constructor uses the cover-indexed boundary reconstruction lemma explicitly.
It is useful when zero-off-boundary-box facts are easier to prove than a
`tsupport`-to-indicator rewrite at the call site.
-/
def coverIndexed_boundarySetIntegralFields_of_pointwise_sum_zero
    (active : Finset ι)
    (localBoundary : ι → Real)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : ι → Set α)
    (boundaryPieceIntegrand : ι → α → Real)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (boundaryPiece_isCompact :
      ∀ i, i ∈ active → IsCompact (boundaryPieceSet i))
    (boundaryPiece_continuousOn :
      ∀ i, i ∈ active →
        ContinuousOn (boundaryPieceIntegrand i) (boundaryPieceSet i))
    (boundaryPiece_tsupport_subset :
      ∀ i, i ∈ active →
        tsupport (boundaryPieceIntegrand i) ⊆ boundaryPieceSet i)
    (localBoundary_eq_setIntegral :
      ∀ i, i ∈ active →
        localBoundary i =
          ∫ y in boundaryPieceSet i, boundaryPieceIntegrand i y ∂μ)
    (boundaryIntegrand_eq_pieceSum :
      ∀ y,
        boundaryIntegrand y =
          Finset.sum active fun i => boundaryPieceIntegrand i y)
    (boundaryPiece_zero_off :
      ∀ i, i ∈ active →
        ∀ y, y ∉ boundaryPieceSet i → boundaryPieceIntegrand i y = 0) :
    CoverIndexedSetIntegralFields
      (α := α) active μ localBoundary :=
  coverIndexed_boundarySetIntegralFields_of_indicator_reconstruction
    (μ := μ) active localBoundary boundaryIntegrand boundaryPieceSet
    boundaryPieceIntegrand globalBoundaryIntegral
    globalBoundaryIntegral_eq_integral boundaryPiece_isCompact
    boundaryPiece_continuousOn boundaryPiece_tsupport_subset
    localBoundary_eq_setIntegral
    (coverIndexed_boundaryIntegrand_ae_eq_indicator_sum
      (mu := μ) active boundaryIntegrand boundaryPieceSet
      boundaryPieceIntegrand boundaryIntegrand_eq_pieceSum
      boundaryPiece_zero_off)

/--
Outward-first signed boundary constructor from resolved unsigned boundary
pieces.

The local set integrals and compact-support fields are stated for the signed
piece representatives, while the finite-sum identity and zero-off support are
allowed to use the unsigned representatives.  This matches the usual boundary
chart pipeline: orientation contributes a single scalar sign after the
unsigned scalar representatives have been identified.
-/
def outwardFirst_coverIndexed_boundarySetIntegralFields_of_pointwise_sum_zero
    (n : Nat)
    (active : Finset ι)
    (localBoundary : ι → Real)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : ι → Set α)
    (unsignedBoundaryPieceIntegrand : ι → α → Real)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (signedBoundaryPiece_isCompact :
      ∀ i, i ∈ active → IsCompact (boundaryPieceSet i))
    (signedBoundaryPiece_continuousOn :
      ∀ i, i ∈ active →
        ContinuousOn
          (fun y =>
            outwardFirstBoundaryOrientationSign n *
              unsignedBoundaryPieceIntegrand i y)
          (boundaryPieceSet i))
    (signedBoundaryPiece_tsupport_subset :
      ∀ i, i ∈ active →
        tsupport
            (fun y =>
              outwardFirstBoundaryOrientationSign n *
                unsignedBoundaryPieceIntegrand i y) ⊆
          boundaryPieceSet i)
    (localBoundary_eq_setIntegral :
      ∀ i, i ∈ active →
        localBoundary i =
          ∫ y in boundaryPieceSet i,
            outwardFirstBoundaryOrientationSign n *
              unsignedBoundaryPieceIntegrand i y ∂μ)
    (boundaryIntegrand_eq_signedPieceSum :
      ∀ y,
        boundaryIntegrand y =
          Finset.sum active fun i =>
            outwardFirstBoundaryOrientationSign n *
              unsignedBoundaryPieceIntegrand i y)
    (unsignedBoundaryPiece_zero_off :
      ∀ i, i ∈ active →
        ∀ y, y ∉ boundaryPieceSet i →
          unsignedBoundaryPieceIntegrand i y = 0) :
    CoverIndexedSetIntegralFields
      (α := α) active μ localBoundary :=
  coverIndexed_boundarySetIntegralFields_of_indicator_reconstruction
    (μ := μ) active localBoundary boundaryIntegrand boundaryPieceSet
    (fun i y =>
      outwardFirstBoundaryOrientationSign n *
        unsignedBoundaryPieceIntegrand i y)
    globalBoundaryIntegral globalBoundaryIntegral_eq_integral
    signedBoundaryPiece_isCompact signedBoundaryPiece_continuousOn
    signedBoundaryPiece_tsupport_subset localBoundary_eq_setIntegral
    (outwardFirst_coverIndexed_boundaryIntegrand_ae_eq_indicator_sum
      (mu := μ) n active boundaryIntegrand boundaryPieceSet
      unsignedBoundaryPieceIntegrand
      boundaryIntegrand_eq_signedPieceSum
      unsignedBoundaryPiece_zero_off)

namespace CoverIndexedSetIntegralFields

/--
View a boundary `CoverIndexedSetIntegralFields` package as the boundary side
of a `CoverIndexedMeasureFields` package once the bulk side and local Stokes
equalities are already available.
-/
def withBulkAsCoverIndexedMeasureFields
    {αBulk : Type a} [TopologicalSpace αBulk] [MeasurableSpace αBulk]
    [OpensMeasurableSpace αBulk] [T2Space αBulk]
    {μBulk : Measure αBulk} [IsFiniteMeasureOnCompacts μBulk]
    {μBoundary : Measure α} [IsFiniteMeasureOnCompacts μBoundary]
    {active : Finset ι}
    {localBulk localBoundary : ι → Real}
    (boundary :
      CoverIndexedSetIntegralFields
        (α := α) active μBoundary localBoundary)
    (bulk :
      CoverIndexedSetIntegralFields
        (α := αBulk) active μBulk localBulk)
    (localBulk_eq_localBoundary :
      ∀ i, i ∈ active → localBulk i = localBoundary i) :
    CoverIndexedMeasureFields active μBulk μBoundary where
  localBulk := localBulk
  localBoundary := localBoundary
  bulk := bulk
  boundary := boundary
  localBulk_eq_localBoundary := localBulk_eq_localBoundary

end CoverIndexedSetIntegralFields

end BoundaryMeasureConstructor

end Stokes

end
