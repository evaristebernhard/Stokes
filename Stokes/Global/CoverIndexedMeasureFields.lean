import Stokes.Global.LocalIntegrabilityFromCompactSupport
import Stokes.Global.CoverIndexedCompactSupportCore

/-!
# Cover-indexed measure and integrability fields

This module is the measure-side handoff for the cover-indexed compact-support
route.  It keeps the genuine representation hypotheses explicit:

* the global scalar integrand represents the measure integral;
* every active cover piece has a compact carrier, continuity on that carrier,
  and topological support in that carrier;
* every recorded local real term is the corresponding set integral;
* the global scalar integrand is reconstructed a.e. from the finite indicator
  sum of the localized pieces.

From these fields we derive the active `IntegrableOn` facts and the finite
sum reconstruction expected by `CoverIndexedStokesSums`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace Stokes

universe u a b

section OneMeasureSpace

variable {ι : Type u}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]

/--
Cover-indexed set-integral data over one measure space.

The compactness, continuity, and `tsupport` fields are the compact-support
inputs.  The set-integral and a.e. indicator reconstruction fields are the
minimal representation hypotheses needed for finite-sum measure
reconstruction.
-/
structure CoverIndexedSetIntegralFields
    (active : Finset ι) (μ : Measure α) [IsFiniteMeasureOnCompacts μ]
    (localTerm : ι -> Real) where
  /-- Global scalar integrand represented by `measureIntegral`. -/
  integrand : α -> Real
  /-- Localized support set for one cover piece. -/
  pieceSet : ι -> Set α
  /-- Unlocalized scalar integrand for one cover piece. -/
  pieceIntegrand : ι -> α -> Real
  /-- The represented measure integral. -/
  measureIntegral : Real
  /-- The represented integral is the integral of `integrand`. -/
  measureIntegral_eq_integral :
    measureIntegral = ∫ y, integrand y ∂μ
  /-- Active cover-piece support sets are compact. -/
  piece_isCompact :
    forall i, i ∈ active -> IsCompact (pieceSet i)
  /-- Active piece integrands are continuous on their compact carriers. -/
  piece_continuousOn :
    forall i, i ∈ active -> ContinuousOn (pieceIntegrand i) (pieceSet i)
  /-- Active piece integrands have topological support in their carriers. -/
  piece_tsupport_subset :
    forall i, i ∈ active -> tsupport (pieceIntegrand i) ⊆ pieceSet i
  /-- Active local real terms are the corresponding set integrals. -/
  localTerm_eq_setIntegral :
    forall i, i ∈ active ->
      localTerm i = ∫ y in pieceSet i, pieceIntegrand i y ∂μ
  /-- A.e. reconstruction of the global integrand by localized indicator pieces. -/
  integrand_ae_eq_indicatorSum :
    integrand =ᵐ[μ]
      fun y => Finset.sum active fun i =>
        (pieceSet i).indicator (pieceIntegrand i) y

namespace CoverIndexedSetIntegralFields

variable {active : Finset ι}
variable {localTerm : ι -> Real}

/-- Active cover-piece carriers are measurable, by compactness. -/
theorem pieceSet_measurable
    (D : CoverIndexedSetIntegralFields (α := α) active μ localTerm)
    (i : ι) (hi : i ∈ active) :
    MeasurableSet (D.pieceSet i) :=
  (D.piece_isCompact i hi).measurableSet

/--
Compact-support integrability data for an active cover piece, obtained from
`tsupport` containment in the compact carrier and continuity on that carrier.
-/
def pieceCompactSupport
    (D : CoverIndexedSetIntegralFields (α := α) active μ localTerm)
    (i : ι) (hi : i ∈ active) :
    CompactSupportIntegrabilityData (D.pieceIntegrand i) :=
  CompactSupportIntegrabilityData.ofTSupportSubsetCompactBox
    (f := D.pieceIntegrand i) (D.pieceSet i)
    (D.piece_isCompact i hi) (D.piece_continuousOn i hi)
    (D.piece_tsupport_subset i hi)

/-- Active cover-piece integrability on its localization set. -/
theorem pieceIntegrableOn
    (D : CoverIndexedSetIntegralFields (α := α) active μ localTerm)
    (i : ι) (hi : i ∈ active) :
    IntegrableOn (D.pieceIntegrand i) (D.pieceSet i) μ :=
  (D.pieceCompactSupport i hi).integrableOn (D.pieceSet i)

/-- Active cover-piece algebraic support is contained in its localization set. -/
theorem piece_support_subset
    (D : CoverIndexedSetIntegralFields (α := α) active μ localTerm)
    (i : ι) (hi : i ∈ active) :
    Function.support (D.pieceIntegrand i) ⊆ D.pieceSet i :=
  (subset_tsupport (D.pieceIntegrand i)).trans
    (D.piece_tsupport_subset i hi)

/-- The measure integral is reconstructed as the finite sum of local terms. -/
theorem measureIntegral_eq_localTermSum
    (D : CoverIndexedSetIntegralFields (α := α) active μ localTerm) :
    D.measureIntegral = Finset.sum active localTerm := by
  calc
    D.measureIntegral = ∫ y, D.integrand y ∂μ :=
      D.measureIntegral_eq_integral
    _ =
        Finset.sum active fun i =>
          ∫ y in D.pieceSet i, D.pieceIntegrand i y ∂μ := by
      exact integral_eq_finset_sum_setIntegral_of_ae_eq_sum_indicator
        (μ := μ) active D.pieceSet D.pieceIntegrand D.integrand
        D.pieceSet_measurable D.pieceIntegrableOn
        D.integrand_ae_eq_indicatorSum
    _ = Finset.sum active localTerm := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact (D.localTerm_eq_setIntegral i hi).symm

/--
Constructor from compact carriers and an indicator-level a.e.
reconstruction.
-/
def ofTSupportSubsetCompactBoxIndicator
    (active : Finset ι) (localTerm : ι -> Real)
    (integrand : α -> Real)
    (pieceSet : ι -> Set α)
    (pieceIntegrand : ι -> α -> Real)
    (measureIntegral : Real)
    (measureIntegral_eq_integral :
      measureIntegral = ∫ y, integrand y ∂μ)
    (piece_isCompact :
      forall i, i ∈ active -> IsCompact (pieceSet i))
    (piece_continuousOn :
      forall i, i ∈ active -> ContinuousOn (pieceIntegrand i) (pieceSet i))
    (piece_tsupport_subset :
      forall i, i ∈ active -> tsupport (pieceIntegrand i) ⊆ pieceSet i)
    (localTerm_eq_setIntegral :
      forall i, i ∈ active ->
        localTerm i = ∫ y in pieceSet i, pieceIntegrand i y ∂μ)
    (integrand_ae_eq_indicatorSum :
      integrand =ᵐ[μ]
        fun y => Finset.sum active fun i =>
          (pieceSet i).indicator (pieceIntegrand i) y) :
    CoverIndexedSetIntegralFields (α := α) active μ localTerm where
  integrand := integrand
  pieceSet := pieceSet
  pieceIntegrand := pieceIntegrand
  measureIntegral := measureIntegral
  measureIntegral_eq_integral := measureIntegral_eq_integral
  piece_isCompact := piece_isCompact
  piece_continuousOn := piece_continuousOn
  piece_tsupport_subset := piece_tsupport_subset
  localTerm_eq_setIntegral := localTerm_eq_setIntegral
  integrand_ae_eq_indicatorSum := integrand_ae_eq_indicatorSum

/--
Constructor from compact carriers and an unlocalized finite-sum a.e.
reconstruction.  The indicator reconstruction is inserted from the support
control derived from `tsupport`.
-/
def ofTSupportSubsetCompactBoxPieceSum
    (active : Finset ι) (localTerm : ι -> Real)
    (integrand : α -> Real)
    (pieceSet : ι -> Set α)
    (pieceIntegrand : ι -> α -> Real)
    (measureIntegral : Real)
    (measureIntegral_eq_integral :
      measureIntegral = ∫ y, integrand y ∂μ)
    (piece_isCompact :
      forall i, i ∈ active -> IsCompact (pieceSet i))
    (piece_continuousOn :
      forall i, i ∈ active -> ContinuousOn (pieceIntegrand i) (pieceSet i))
    (piece_tsupport_subset :
      forall i, i ∈ active -> tsupport (pieceIntegrand i) ⊆ pieceSet i)
    (localTerm_eq_setIntegral :
      forall i, i ∈ active ->
        localTerm i = ∫ y in pieceSet i, pieceIntegrand i y ∂μ)
    (integrand_ae_eq_pieceSum :
      integrand =ᵐ[μ]
        fun y => Finset.sum active fun i => pieceIntegrand i y) :
    CoverIndexedSetIntegralFields (α := α) active μ localTerm :=
  ofTSupportSubsetCompactBoxIndicator
    (μ := μ) active localTerm integrand pieceSet pieceIntegrand
    measureIntegral measureIntegral_eq_integral piece_isCompact
    piece_continuousOn piece_tsupport_subset localTerm_eq_setIntegral
    (integrand_ae_eq_pieceSum.trans
      (Filter.Eventually.of_forall fun y => by
        have hfun :
            (fun y => Finset.sum active fun i => pieceIntegrand i y) =
              fun y => Finset.sum active fun i =>
                (pieceSet i).indicator (pieceIntegrand i) y := by
          simpa using
            (finset_sum_eq_finset_sum_indicator_of_support_subset
              active pieceSet pieceIntegrand
              (fun i hi =>
                (subset_tsupport (pieceIntegrand i)).trans
                  (piece_tsupport_subset i hi)))
        exact congrFun hfun y))

end CoverIndexedSetIntegralFields

end OneMeasureSpace

section Combined

variable {ι : Type u}
variable {αBulk : Type a} [TopologicalSpace αBulk]
variable [MeasurableSpace αBulk] [OpensMeasurableSpace αBulk]
variable [T2Space αBulk]
variable {μBulk : Measure αBulk} [IsFiniteMeasureOnCompacts μBulk]
variable {αBoundary : Type b} [TopologicalSpace αBoundary]
variable [MeasurableSpace αBoundary] [OpensMeasurableSpace αBoundary]
variable [T2Space αBoundary]
variable {μBoundary : Measure αBoundary}
variable [IsFiniteMeasureOnCompacts μBoundary]

/--
Cover-indexed bulk/boundary measure fields.

The two measure spaces may differ.  This is useful for the compact-support
route where bulk terms can live on an ambient coordinate chart and boundary
terms on a lower-dimensional boundary chart.  The package produces the finite
cover-indexed core input once the local Stokes equality is supplied on active
pieces.
-/
structure CoverIndexedMeasureFields
    (active : Finset ι)
    (μBulk : Measure αBulk) [IsFiniteMeasureOnCompacts μBulk]
    (μBoundary : Measure αBoundary)
    [IsFiniteMeasureOnCompacts μBoundary] where
  /-- Local bulk real term attached to one cover piece. -/
  localBulk : ι -> Real
  /-- Local true-boundary real term attached to one cover piece. -/
  localBoundary : ι -> Real
  /-- Bulk measure reconstruction fields. -/
  bulk :
    CoverIndexedSetIntegralFields (α := αBulk) active μBulk localBulk
  /-- Boundary measure reconstruction fields. -/
  boundary :
    CoverIndexedSetIntegralFields
      (α := αBoundary) active μBoundary localBoundary
  /-- Local Stokes equality on active cover pieces. -/
  localBulk_eq_localBoundary :
    forall i, i ∈ active -> localBulk i = localBoundary i

namespace CoverIndexedMeasureFields

variable {active : Finset ι}

/-- The represented global bulk measure integral. -/
abbrev globalBulk
    (D : CoverIndexedMeasureFields active μBulk μBoundary) : Real :=
  D.bulk.measureIntegral

/-- The represented global boundary measure integral. -/
abbrev globalBoundary
    (D : CoverIndexedMeasureFields active μBulk μBoundary) : Real :=
  D.boundary.measureIntegral

/-- Active bulk carrier measurability, derived from compactness. -/
theorem bulk_pieceSet_measurable
    (D : CoverIndexedMeasureFields active μBulk μBoundary)
    (i : ι) (hi : i ∈ active) :
    MeasurableSet (D.bulk.pieceSet i) :=
  D.bulk.pieceSet_measurable i hi

/-- Active boundary carrier measurability, derived from compactness. -/
theorem boundary_pieceSet_measurable
    (D : CoverIndexedMeasureFields active μBulk μBoundary)
    (i : ι) (hi : i ∈ active) :
    MeasurableSet (D.boundary.pieceSet i) :=
  D.boundary.pieceSet_measurable i hi

/-- Compact-support data for an active bulk cover piece. -/
def bulk_pieceCompactSupport
    (D : CoverIndexedMeasureFields active μBulk μBoundary)
    (i : ι) (hi : i ∈ active) :
    CompactSupportIntegrabilityData (D.bulk.pieceIntegrand i) :=
  D.bulk.pieceCompactSupport i hi

/-- Compact-support data for an active boundary cover piece. -/
def boundary_pieceCompactSupport
    (D : CoverIndexedMeasureFields active μBulk μBoundary)
    (i : ι) (hi : i ∈ active) :
    CompactSupportIntegrabilityData (D.boundary.pieceIntegrand i) :=
  D.boundary.pieceCompactSupport i hi

/-- Active bulk `IntegrableOn` field. -/
theorem bulk_pieceIntegrableOn
    (D : CoverIndexedMeasureFields active μBulk μBoundary)
    (i : ι) (hi : i ∈ active) :
    IntegrableOn (D.bulk.pieceIntegrand i) (D.bulk.pieceSet i) μBulk :=
  D.bulk.pieceIntegrableOn i hi

/-- Active boundary `IntegrableOn` field. -/
theorem boundary_pieceIntegrableOn
    (D : CoverIndexedMeasureFields active μBulk μBoundary)
    (i : ι) (hi : i ∈ active) :
    IntegrableOn
      (D.boundary.pieceIntegrand i) (D.boundary.pieceSet i) μBoundary :=
  D.boundary.pieceIntegrableOn i hi

/-- Bulk measure reconstruction as a finite cover sum. -/
theorem globalBulk_eq_localBulkSum
    (D : CoverIndexedMeasureFields active μBulk μBoundary) :
    D.globalBulk = Finset.sum active D.localBulk :=
  D.bulk.measureIntegral_eq_localTermSum

/-- Boundary measure reconstruction as a finite cover sum. -/
theorem localBoundarySum_eq_globalBoundary
    (D : CoverIndexedMeasureFields active μBulk μBoundary) :
    Finset.sum active D.localBoundary = D.globalBoundary :=
  D.boundary.measureIntegral_eq_localTermSum.symm

/-- Forget the measure fields and expose the core cover-indexed algebra input. -/
def toCoverIndexedStokesSums
    (D : CoverIndexedMeasureFields active μBulk μBoundary) :
    CoverIndexedStokesSums ι where
  active := active
  globalBulk := D.globalBulk
  globalBoundary := D.globalBoundary
  localBulk := D.localBulk
  localBoundary := D.localBoundary
  globalBulk_eq_localBulkSum := D.globalBulk_eq_localBulkSum
  localBoundarySum_eq_globalBoundary := D.localBoundarySum_eq_globalBoundary
  localBulk_eq_localBoundary := D.localBulk_eq_localBoundary

/-- Cover-indexed compact-support Stokes from the measure-field package. -/
theorem stokes
    (D : CoverIndexedMeasureFields active μBulk μBoundary) :
    D.globalBulk = D.globalBoundary :=
  D.toCoverIndexedStokesSums.stokes

end CoverIndexedMeasureFields

end Combined

end Stokes

end
