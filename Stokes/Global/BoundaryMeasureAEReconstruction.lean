import Stokes.Global.BoundaryMeasurePartitionLocalizationWrappers
import Stokes.Global.IndicatorSupportLocalization

/-!
# Boundary-measure a.e. reconstruction from canonical pieces

This file supplies a non-axiomatic source for the boundary-side finite
indicator reconstruction field used by `BoundaryCompactMeasureFields` and the
canonical target-image route.

The useful hypothesis is support-theoretic rather than measure-theoretic: the
chosen boundary integrand is the finite sum of the chosen boundary-piece
integrands, and every selected piece integrand is algebraically supported in
its selected piece set.  From this we derive the exact indicator-sum equality,
hence the a.e. reconstruction consumed downstream.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryMeasureAEReconstruction

universe u w c p a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {Piece : Type p}
variable {α : Type a} [MeasurableSpace α]
variable {μ : Measure α}

omit [MeasurableSpace α] in
/--
The unlocalized selected boundary-piece sum equals the indicator-localized sum
when every active piece integrand is supported in its selected piece set.
-/
theorem boundaryMeasurePieceSum_eq_indicatorSum_of_support_subset
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart → Finset Piece)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (hsupp :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          Function.support (boundaryPieceIntegrand x q) ⊆
            boundaryPieceSet x q) :
    boundaryMeasurePieceSum activeCharts boundaryPieces
        boundaryPieceIntegrand =
      boundaryMeasureIndicatorSum activeCharts boundaryPieces
        boundaryPieceSet boundaryPieceIntegrand := by
  funext y
  simp only [boundaryMeasurePieceSum, boundaryMeasureIndicatorSum]
  refine Finset.sum_congr rfl ?_
  intro x hx
  simpa [boundaryMeasurePieceIndicator] using congrFun
    (finset_sum_eq_indicator_sum_of_support_subset
      (active := boundaryPieces x)
      (K := fun q => boundaryPieceSet x q)
      (f := boundaryPieceIntegrand x)
      (fun q hq => hsupp x hx q hq)) y

/--
A.e. version of
`boundaryMeasurePieceSum_eq_indicatorSum_of_support_subset`.
-/
theorem boundaryMeasurePieceSum_ae_eq_indicatorSum_of_support_subset
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart → Finset Piece)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (hsupp :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          Function.support (boundaryPieceIntegrand x q) ⊆
            boundaryPieceSet x q) :
    boundaryMeasurePieceSum activeCharts boundaryPieces
        boundaryPieceIntegrand =ᵐ[μ]
      boundaryMeasureIndicatorSum activeCharts boundaryPieces
        boundaryPieceSet boundaryPieceIntegrand :=
  ae_of_all μ fun y =>
    congrFun
      (boundaryMeasurePieceSum_eq_indicatorSum_of_support_subset
        activeCharts boundaryPieces boundaryPieceSet boundaryPieceIntegrand
        hsupp) y

/--
Support-based input for the selected boundary indicator reconstruction.

This is intentionally smaller than `BoundaryCompactMeasureFields`: it only
records the finite-piece identity and support containment needed to derive the
a.e. indicator reconstruction.  Measurability, integrability, and integral-term
identities stay separate downstream hypotheses.
-/
structure BoundaryMeasureAEReconstructionInput
    (P : BoundaryMeasurePartitionData Chart Piece) where
  /-- Boundary-side integrand represented by the selected finite pieces. -/
  boundaryIntegrand : α → Real
  /-- Selected boundary-piece support set. -/
  boundaryPieceSet : Chart → Piece → Set α
  /-- Unlocalized selected boundary-piece scalar integrand. -/
  boundaryPieceIntegrand : Chart → Piece → α → Real
  /-- The global boundary integrand is the unlocalized selected piece sum. -/
  boundaryIntegrand_eq_pieceSum :
    boundaryIntegrand =
      boundaryMeasurePieceSum P.activeCharts P.boundaryPieces
        boundaryPieceIntegrand
  /-- Active selected piece integrands are supported in their piece sets. -/
  boundaryPiece_support_subset :
    ∀ x, x ∈ P.activeCharts →
      ∀ q, q ∈ P.boundaryPieces x →
        Function.support (boundaryPieceIntegrand x q) ⊆
          boundaryPieceSet x q

namespace BoundaryMeasureAEReconstructionInput

variable {P : BoundaryMeasurePartitionData Chart Piece}
variable (R : BoundaryMeasureAEReconstructionInput (α := α) P)

omit [MeasurableSpace α] in
/-- The exact finite indicator reconstruction supplied by support containment. -/
theorem boundaryIntegrand_eq_selectedTargetIndicatorSum :
    R.boundaryIntegrand =
      boundaryMeasureIndicatorSum P.activeCharts P.boundaryPieces
        R.boundaryPieceSet R.boundaryPieceIntegrand := by
  calc
    R.boundaryIntegrand =
        boundaryMeasurePieceSum P.activeCharts P.boundaryPieces
          R.boundaryPieceIntegrand :=
      R.boundaryIntegrand_eq_pieceSum
    _ =
        boundaryMeasureIndicatorSum P.activeCharts P.boundaryPieces
          R.boundaryPieceSet R.boundaryPieceIntegrand :=
      boundaryMeasurePieceSum_eq_indicatorSum_of_support_subset
        P.activeCharts P.boundaryPieces R.boundaryPieceSet
        R.boundaryPieceIntegrand R.boundaryPiece_support_subset

/-- The selected target indicator reconstruction in the downstream a.e. shape. -/
theorem boundaryIntegrand_ae_eq_selectedTargetIndicatorSum :
    R.boundaryIntegrand =ᵐ[μ]
      boundaryMeasureIndicatorSum P.activeCharts P.boundaryPieces
        R.boundaryPieceSet R.boundaryPieceIntegrand :=
  ae_of_all μ fun y =>
    congrFun R.boundaryIntegrand_eq_selectedTargetIndicatorSum y

/--
Build compact/set-integral boundary fields from support-based reconstruction
plus the remaining analytic measure inputs.
-/
def toBoundaryCompactMeasureFieldsOfIntegrableOn
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, R.boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          MeasurableSet (R.boundaryPieceSet x q))
    (hintegrable :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          IntegrableOn (R.boundaryPieceIntegrand x q)
            (R.boundaryPieceSet x q) μ)
    (hterm :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          P.boundaryPartitionTerm x q =
            ∫ y in R.boundaryPieceSet x q,
              R.boundaryPieceIntegrand x q y ∂μ) :
    BoundaryCompactMeasureFields μ P.activeCharts P.boundaryPieces
      P.boundaryPartitionTerm :=
  P.compactFieldsOfIntegrableOn (μ := μ) R.boundaryIntegrand
    R.boundaryPieceSet R.boundaryPieceIntegrand boundaryMeasureIntegral
    hmeasure hset hintegrable hterm
    R.boundaryIntegrand_ae_eq_selectedTargetIndicatorSum

/--
Build analytic boundary-measure localization data from support-based
reconstruction plus explicit active-piece `IntegrableOn` inputs.
-/
def toBoundaryMeasureLocalizationDataOfIntegrableOn
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, R.boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          MeasurableSet (R.boundaryPieceSet x q))
    (hintegrable :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          IntegrableOn (R.boundaryPieceIntegrand x q)
            (R.boundaryPieceSet x q) μ)
    (hterm :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          P.boundaryPartitionTerm x q =
            ∫ y in R.boundaryPieceSet x q,
              R.boundaryPieceIntegrand x q y ∂μ) :
    BoundaryMeasureLocalizationData μ P.activeCharts P.boundaryPieces
      P.boundaryPartitionTerm :=
  (R.toBoundaryCompactMeasureFieldsOfIntegrableOn
    (μ := μ) boundaryMeasureIntegral hmeasure hset hintegrable hterm)
    |>.toBoundaryMeasureLocalizationData

section CompactSupport

variable [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
variable [IsFiniteMeasureOnCompacts μ]

/--
Build compact/set-integral boundary fields when the selected piece integrands
come with compact-support integrability data.
-/
def toBoundaryCompactMeasureFieldsOfCompactSupport
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, R.boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          MeasurableSet (R.boundaryPieceSet x q))
    (hcompact :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          CompactSupportIntegrabilityData (R.boundaryPieceIntegrand x q))
    (hterm :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          P.boundaryPartitionTerm x q =
            ∫ y in R.boundaryPieceSet x q,
              R.boundaryPieceIntegrand x q y ∂μ) :
    BoundaryCompactMeasureFields μ P.activeCharts P.boundaryPieces
      P.boundaryPartitionTerm :=
  P.compactFieldsOfCompactSupport (μ := μ) R.boundaryIntegrand
    R.boundaryPieceSet R.boundaryPieceIntegrand boundaryMeasureIntegral
    hmeasure hset hcompact hterm
    R.boundaryIntegrand_ae_eq_selectedTargetIndicatorSum

/--
Build analytic boundary-measure localization data from support-based
reconstruction and compact-support integrability.
-/
def toBoundaryMeasureLocalizationDataOfCompactSupport
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, R.boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          MeasurableSet (R.boundaryPieceSet x q))
    (hcompact :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          CompactSupportIntegrabilityData (R.boundaryPieceIntegrand x q))
    (hterm :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.boundaryPieces x →
          P.boundaryPartitionTerm x q =
            ∫ y in R.boundaryPieceSet x q,
              R.boundaryPieceIntegrand x q y ∂μ) :
    BoundaryMeasureLocalizationData μ P.activeCharts P.boundaryPieces
      P.boundaryPartitionTerm :=
  (R.toBoundaryCompactMeasureFieldsOfCompactSupport
    (μ := μ) boundaryMeasureIntegral hmeasure hset hcompact hterm)
    |>.toBoundaryMeasureLocalizationData

end CompactSupport

end BoundaryMeasureAEReconstructionInput

section CanonicalTargetRoute

variable [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
variable [IsFiniteMeasureOnCompacts μ]
variable {BoundaryPiece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
variable
    {D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}

namespace BoundaryMeasureAEReconstructionInput

variable
    (R :
      BoundaryMeasureAEReconstructionInput (α := α)
        D.toSelectedBoundaryMeasurePartitionData)

/--
Turn support-based selected target-piece reconstruction into the canonical
boundary target compact-support input.  The genuine measure identity,
compact-support integrability, and set-integral terms remain explicit
hypotheses.
-/
def toCanonicalBoundaryTargetCompactSupportInput
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, R.boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.targetImages.boundaryPieces x →
          MeasurableSet (R.boundaryPieceSet x q))
    (hcompact :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData (R.boundaryPieceIntegrand x q))
    (hterm :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.targetImages.boundaryPieces x →
          D.assembly.boundaryPartitionTerm x q =
            ∫ y in R.boundaryPieceSet x q,
              R.boundaryPieceIntegrand x q y ∂μ)
    (globalBoundaryIntegral : Real)
    (hglobal : globalBoundaryIntegral = boundaryMeasureIntegral) :
    CanonicalBoundaryTargetCompactSupportInput (α := α) D μ where
  boundaryIntegrand := R.boundaryIntegrand
  boundaryPieceSet := R.boundaryPieceSet
  boundaryPieceIntegrand := R.boundaryPieceIntegrand
  boundaryMeasureIntegral := boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_integral := hmeasure
  boundaryPieceSet_measurable := hset
  boundaryPieceCompact := hcompact
  boundaryPartitionTerm_eq_setIntegral := hterm
  boundaryIntegrand_ae_eq_indicatorSum := by
    simpa using
      (R.boundaryIntegrand_ae_eq_selectedTargetIndicatorSum (μ := μ))
  globalBoundaryIntegral := globalBoundaryIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := hglobal

end BoundaryMeasureAEReconstructionInput

end CanonicalTargetRoute

end BoundaryMeasureAEReconstruction

end Stokes

end
