import Stokes.Global.BoundaryMeasureAEReconstruction
import Stokes.Global.NaturalCompactSupportMeasureConstructor

/-!
# Boundary partition reconstruction from support

This file is a boundary-side support-control entry point for finite partition
reconstruction.  The measure constructors downstream already know how to
integrate an indicator-localized finite sum.  Here we derive that indicator
sum from the more geometric input shape:

* the boundary scalar integrand is the finite unlocalized sum of the selected
  boundary-piece scalar integrands;
* each selected scalar piece vanishes off its boundary support set.

The result is a direct handoff to `BoundaryCompactMeasureFields` and to the
selected compact-support M8 measure constructor.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryPartitionReconstructionFromSupport

universe c p a

variable {Chart : Type c} {Piece : Type p}
variable {alpha : Type a} [MeasurableSpace alpha]
variable {mu : Measure alpha}

omit [MeasurableSpace alpha] in
/-- Zero off a selected boundary set gives the support-containment hypothesis
used by the indicator finite-sum lemmas. -/
theorem boundaryScalarPiece_support_subset_of_eq_zero_off
    {s : Set alpha} {f : alpha -> Real}
    (hzero : forall y, y ∉ s -> f y = 0) :
    Function.support f ⊆ s := by
  intro y hy
  by_contra hmem
  exact hy (hzero y hmem)

omit [MeasurableSpace alpha] in
/-- Insert boundary indicators in a finite scalar piece sum from zero-off
support control on every selected active piece. -/
theorem boundaryMeasurePieceSum_eq_indicatorSum_of_eq_zero_off
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart -> Finset Piece)
    (boundaryPieceSet : Chart -> Piece -> Set alpha)
    (boundaryPieceIntegrand : Chart -> Piece -> alpha -> Real)
    (hzero :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          forall y, y ∉ boundaryPieceSet x q ->
            boundaryPieceIntegrand x q y = 0) :
    boundaryMeasurePieceSum activeCharts boundaryPieces
        boundaryPieceIntegrand =
      boundaryMeasureIndicatorSum activeCharts boundaryPieces
        boundaryPieceSet boundaryPieceIntegrand := by
  exact
    boundaryMeasurePieceSum_eq_indicatorSum_of_support_subset
      activeCharts boundaryPieces boundaryPieceSet boundaryPieceIntegrand
      (fun x hx q hq =>
        boundaryScalarPiece_support_subset_of_eq_zero_off
          (hzero x hx q hq))

/-- A.e. version of indicator insertion from zero-off support control. -/
theorem boundaryMeasurePieceSum_ae_eq_indicatorSum_of_eq_zero_off
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart -> Finset Piece)
    (boundaryPieceSet : Chart -> Piece -> Set alpha)
    (boundaryPieceIntegrand : Chart -> Piece -> alpha -> Real)
    (hzero :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          forall y, y ∉ boundaryPieceSet x q ->
            boundaryPieceIntegrand x q y = 0) :
    boundaryMeasurePieceSum activeCharts boundaryPieces
        boundaryPieceIntegrand =ᵐ[mu]
      boundaryMeasureIndicatorSum activeCharts boundaryPieces
        boundaryPieceSet boundaryPieceIntegrand :=
  ae_of_all mu fun y =>
    congrFun
      (boundaryMeasurePieceSum_eq_indicatorSum_of_eq_zero_off
        activeCharts boundaryPieces boundaryPieceSet boundaryPieceIntegrand
        hzero) y

omit [MeasurableSpace alpha] in
/-- Pointwise scalar boundary reconstruction from an unlocalized finite-sum
identity and active support containment. -/
theorem boundaryScalarIntegrand_eq_indicatorSum_of_pieceSum_eq_of_support_subset
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart -> Finset Piece)
    (boundaryIntegrand : alpha -> Real)
    (boundaryPieceSet : Chart -> Piece -> Set alpha)
    (boundaryPieceIntegrand : Chart -> Piece -> alpha -> Real)
    (hpiece :
      boundaryIntegrand =
        boundaryMeasurePieceSum activeCharts boundaryPieces
          boundaryPieceIntegrand)
    (hsupp :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          Function.support (boundaryPieceIntegrand x q) ⊆
            boundaryPieceSet x q) :
    boundaryIntegrand =
      boundaryMeasureIndicatorSum activeCharts boundaryPieces
        boundaryPieceSet boundaryPieceIntegrand := by
  exact hpiece.trans
    (boundaryMeasurePieceSum_eq_indicatorSum_of_support_subset
      activeCharts boundaryPieces boundaryPieceSet boundaryPieceIntegrand
      hsupp)

/-- A.e. scalar boundary reconstruction from an unlocalized finite-sum identity
and active support containment. -/
theorem boundaryScalarIntegrand_ae_eq_indicatorSum_of_pieceSum_eq_of_support_subset
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart -> Finset Piece)
    (boundaryIntegrand : alpha -> Real)
    (boundaryPieceSet : Chart -> Piece -> Set alpha)
    (boundaryPieceIntegrand : Chart -> Piece -> alpha -> Real)
    (hpiece :
      boundaryIntegrand =
        boundaryMeasurePieceSum activeCharts boundaryPieces
          boundaryPieceIntegrand)
    (hsupp :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          Function.support (boundaryPieceIntegrand x q) ⊆
            boundaryPieceSet x q) :
    boundaryIntegrand =ᵐ[mu]
      boundaryMeasureIndicatorSum activeCharts boundaryPieces
        boundaryPieceSet boundaryPieceIntegrand :=
  ae_of_all mu fun y =>
    congrFun
      (boundaryScalarIntegrand_eq_indicatorSum_of_pieceSum_eq_of_support_subset
        activeCharts boundaryPieces boundaryIntegrand boundaryPieceSet
        boundaryPieceIntegrand hpiece hsupp) y

omit [MeasurableSpace alpha] in
/-- Pointwise scalar boundary reconstruction from an unlocalized finite-sum
identity and zero-off support control. -/
theorem boundaryScalarIntegrand_eq_indicatorSum_of_pieceSum_eq_of_eq_zero_off
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart -> Finset Piece)
    (boundaryIntegrand : alpha -> Real)
    (boundaryPieceSet : Chart -> Piece -> Set alpha)
    (boundaryPieceIntegrand : Chart -> Piece -> alpha -> Real)
    (hpiece :
      boundaryIntegrand =
        boundaryMeasurePieceSum activeCharts boundaryPieces
          boundaryPieceIntegrand)
    (hzero :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          forall y, y ∉ boundaryPieceSet x q ->
            boundaryPieceIntegrand x q y = 0) :
    boundaryIntegrand =
      boundaryMeasureIndicatorSum activeCharts boundaryPieces
        boundaryPieceSet boundaryPieceIntegrand := by
  exact hpiece.trans
    (boundaryMeasurePieceSum_eq_indicatorSum_of_eq_zero_off
      activeCharts boundaryPieces boundaryPieceSet boundaryPieceIntegrand
      hzero)

/-- A.e. scalar boundary reconstruction from an unlocalized finite-sum identity
and zero-off support control. -/
theorem boundaryScalarIntegrand_ae_eq_indicatorSum_of_pieceSum_eq_of_eq_zero_off
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart -> Finset Piece)
    (boundaryIntegrand : alpha -> Real)
    (boundaryPieceSet : Chart -> Piece -> Set alpha)
    (boundaryPieceIntegrand : Chart -> Piece -> alpha -> Real)
    (hpiece :
      boundaryIntegrand =
        boundaryMeasurePieceSum activeCharts boundaryPieces
          boundaryPieceIntegrand)
    (hzero :
      forall x, x ∈ activeCharts ->
        forall q, q ∈ boundaryPieces x ->
          forall y, y ∉ boundaryPieceSet x q ->
            boundaryPieceIntegrand x q y = 0) :
    boundaryIntegrand =ᵐ[mu]
      boundaryMeasureIndicatorSum activeCharts boundaryPieces
        boundaryPieceSet boundaryPieceIntegrand :=
  ae_of_all mu fun y =>
    congrFun
      (boundaryScalarIntegrand_eq_indicatorSum_of_pieceSum_eq_of_eq_zero_off
        activeCharts boundaryPieces boundaryIntegrand boundaryPieceSet
        boundaryPieceIntegrand hpiece hzero) y

namespace BoundaryMeasurePartitionData

variable (P : BoundaryMeasurePartitionData Chart Piece)

/-- Compact/set-integral boundary measure fields from finite scalar
reconstruction plus support containment. -/
def compactFieldsOfIntegrableOnFromSupportSubset
    (boundaryIntegrand : alpha -> Real)
    (boundaryPieceSet : Chart -> Piece -> Set alpha)
    (boundaryPieceIntegrand : Chart -> Piece -> alpha -> Real)
    (boundaryMeasureIntegral : Real)
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
    (hterm :
      forall x, x ∈ P.activeCharts ->
        forall q, q ∈ P.boundaryPieces x ->
          P.boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (hpiece :
      boundaryIntegrand =
        boundaryMeasurePieceSum P.activeCharts P.boundaryPieces
          boundaryPieceIntegrand)
    (hsupp :
      forall x, x ∈ P.activeCharts ->
        forall q, q ∈ P.boundaryPieces x ->
          Function.support (boundaryPieceIntegrand x q) ⊆
            boundaryPieceSet x q) :
    BoundaryCompactMeasureFields mu P.activeCharts P.boundaryPieces
      P.boundaryPartitionTerm :=
  P.compactFieldsOfIntegrableOn (μ := mu)
    boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hintegrable hterm
    (boundaryScalarIntegrand_ae_eq_indicatorSum_of_pieceSum_eq_of_support_subset
      (mu := mu) P.activeCharts P.boundaryPieces boundaryIntegrand
      boundaryPieceSet boundaryPieceIntegrand hpiece hsupp)

/-- Compact/set-integral boundary measure fields from finite scalar
reconstruction plus zero-off support control. -/
def compactFieldsOfIntegrableOnFromSupport
    (boundaryIntegrand : alpha -> Real)
    (boundaryPieceSet : Chart -> Piece -> Set alpha)
    (boundaryPieceIntegrand : Chart -> Piece -> alpha -> Real)
    (boundaryMeasureIntegral : Real)
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
    (hterm :
      forall x, x ∈ P.activeCharts ->
        forall q, q ∈ P.boundaryPieces x ->
          P.boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (hpiece :
      boundaryIntegrand =
        boundaryMeasurePieceSum P.activeCharts P.boundaryPieces
          boundaryPieceIntegrand)
    (hzero :
      forall x, x ∈ P.activeCharts ->
        forall q, q ∈ P.boundaryPieces x ->
          forall y, y ∉ boundaryPieceSet x q ->
            boundaryPieceIntegrand x q y = 0) :
    BoundaryCompactMeasureFields mu P.activeCharts P.boundaryPieces
      P.boundaryPartitionTerm :=
  P.compactFieldsOfIntegrableOnFromSupportSubset (mu := mu)
    boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hintegrable hterm hpiece
    (fun x hx q hq =>
      boundaryScalarPiece_support_subset_of_eq_zero_off
        (hzero x hx q hq))

/-- Boundary integral partition reconstruction from finite scalar
reconstruction plus zero-off support control. -/
def boundaryIntegralPartitionReconstructionDataOfIntegrableOnFromSupport
    (boundaryIntegrand : alpha -> Real)
    (boundaryPieceSet : Chart -> Piece -> Set alpha)
    (boundaryPieceIntegrand : Chart -> Piece -> alpha -> Real)
    (globalBoundaryIntegral boundaryMeasureIntegral : Real)
    (hglobal : globalBoundaryIntegral = boundaryMeasureIntegral)
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
    (hterm :
      forall x, x ∈ P.activeCharts ->
        forall q, q ∈ P.boundaryPieces x ->
          P.boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (hpiece :
      boundaryIntegrand =
        boundaryMeasurePieceSum P.activeCharts P.boundaryPieces
          boundaryPieceIntegrand)
    (hzero :
      forall x, x ∈ P.activeCharts ->
        forall q, q ∈ P.boundaryPieces x ->
          forall y, y ∉ boundaryPieceSet x q ->
            boundaryPieceIntegrand x q y = 0) :
    BoundaryIntegralPartitionReconstructionData P.activeCharts
      P.boundaryPieces P.boundaryPartitionTerm globalBoundaryIntegral :=
    (P.compactFieldsOfIntegrableOnFromSupport (mu := mu)
    boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hintegrable hterm hpiece hzero)
    |>.toBoundaryIntegralPartitionReconstructionData
      globalBoundaryIntegral (by simpa using hglobal)

/-- The finite partition sum obtained from
`boundaryIntegralPartitionReconstructionDataOfIntegrableOnFromSupport`. -/
theorem globalBoundaryIntegral_eq_partitionSum_of_integrableOnFromSupport
    (boundaryIntegrand : alpha -> Real)
    (boundaryPieceSet : Chart -> Piece -> Set alpha)
    (boundaryPieceIntegrand : Chart -> Piece -> alpha -> Real)
    (globalBoundaryIntegral boundaryMeasureIntegral : Real)
    (hglobal : globalBoundaryIntegral = boundaryMeasureIntegral)
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
    (hterm :
      forall x, x ∈ P.activeCharts ->
        forall q, q ∈ P.boundaryPieces x ->
          P.boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (hpiece :
      boundaryIntegrand =
        boundaryMeasurePieceSum P.activeCharts P.boundaryPieces
          boundaryPieceIntegrand)
    (hzero :
      forall x, x ∈ P.activeCharts ->
        forall q, q ∈ P.boundaryPieces x ->
          forall y, y ∉ boundaryPieceSet x q ->
            boundaryPieceIntegrand x q y = 0) :
    globalBoundaryIntegral = P.boundaryPartitionSum := by
  simpa [BoundaryMeasurePartitionData.boundaryPartitionSum] using
    (P.boundaryIntegralPartitionReconstructionDataOfIntegrableOnFromSupport
      (mu := mu) boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
      globalBoundaryIntegral boundaryMeasureIntegral hglobal hmeasure hset
      hintegrable hterm hpiece hzero).manifoldBoundaryIntegral_eq_partitionSum

section CompactSupport

variable [TopologicalSpace alpha] [OpensMeasurableSpace alpha]
variable [T2Space alpha] [IsFiniteMeasureOnCompacts mu]

/-- Compact-support boundary measure fields from finite scalar reconstruction
plus zero-off support control. -/
def compactFieldsOfCompactSupportFromSupport
    (boundaryIntegrand : alpha -> Real)
    (boundaryPieceSet : Chart -> Piece -> Set alpha)
    (boundaryPieceIntegrand : Chart -> Piece -> alpha -> Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂mu)
    (hset :
      forall x, x ∈ P.activeCharts ->
        forall q, q ∈ P.boundaryPieces x ->
          MeasurableSet (boundaryPieceSet x q))
    (hcompact :
      forall x, x ∈ P.activeCharts ->
        forall q, q ∈ P.boundaryPieces x ->
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (hterm :
      forall x, x ∈ P.activeCharts ->
        forall q, q ∈ P.boundaryPieces x ->
          P.boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (hpiece :
      boundaryIntegrand =
        boundaryMeasurePieceSum P.activeCharts P.boundaryPieces
          boundaryPieceIntegrand)
    (hzero :
      forall x, x ∈ P.activeCharts ->
        forall q, q ∈ P.boundaryPieces x ->
          forall y, y ∉ boundaryPieceSet x q ->
            boundaryPieceIntegrand x q y = 0) :
    BoundaryCompactMeasureFields mu P.activeCharts P.boundaryPieces
      P.boundaryPartitionTerm :=
  P.compactFieldsOfCompactSupport (μ := mu)
    boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hcompact hterm
    (boundaryScalarIntegrand_ae_eq_indicatorSum_of_pieceSum_eq_of_eq_zero_off
      (mu := mu) P.activeCharts P.boundaryPieces boundaryIntegrand
      boundaryPieceSet boundaryPieceIntegrand hpiece hzero)

end CompactSupport

end BoundaryMeasurePartitionData

end BoundaryPartitionReconstructionFromSupport

section SelectedBoundaryM8FromSupport

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {alpha : Type a} [TopologicalSpace alpha] [MeasurableSpace alpha]
variable [OpensMeasurableSpace alpha] [T2Space alpha]
variable {mu : Measure alpha} [IsFiniteMeasureOnCompacts mu]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

/-- Selected compact-support M8 measure data from a boundary finite-piece sum
and zero-off support control.

This is the boundary reconstruction theorem in the shape consumed by the
existing selected compact-support measure constructor: the boundary integrand
is the literal finite piece sum, and the a.e. indicator reconstruction is
derived here from support control. -/
def compactSupportToM8MeasureDataOfBoundarySupportReconstruction
    {globalBulkIntegral globalBoundaryIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData (α := alpha) (μ := mu)
        selectedPartition targetImages globalBulkIntegral)
    (boundaryPartitionTerm : M -> BoundaryPiece -> Real)
    (boundaryPieceSet : M -> BoundaryPiece -> Set alpha)
    (boundaryPieceIntegrand : M -> BoundaryPiece -> alpha -> Real)
    (boundaryMeasureIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral =
        ∫ y,
          boundaryMeasurePieceSum selectedPartition.active
            targetImages.boundaryPieces boundaryPieceIntegrand y ∂mu)
    (boundaryPieceSet_measurable :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceCompactSupport :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (boundaryPartitionTerm_eq_setIntegral :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (boundaryPiece_eq_zero_off :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          forall y, y ∉ boundaryPieceSet x q ->
            boundaryPieceIntegrand x q y = 0) :
    CompactSupportToM8MeasureData
      (α := alpha) I omega selectedPartition targetImages mu :=
  compactSupportToM8MeasureDataOfReconstruction
    (α := alpha) (μ := mu) (I := I) (omega := omega)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    bulk boundaryPartitionTerm
    (boundaryMeasurePieceSum selectedPartition.active
      targetImages.boundaryPieces boundaryPieceIntegrand)
    boundaryPieceSet boundaryPieceIntegrand boundaryMeasureIntegral
    globalBoundaryIntegral_eq_boundaryMeasureIntegral
    boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
    boundaryPieceCompactSupport boundaryPartitionTerm_eq_setIntegral
    (boundaryMeasurePieceSum_ae_eq_indicatorSum_of_eq_zero_off
      (mu := mu) selectedPartition.active targetImages.boundaryPieces
      boundaryPieceSet boundaryPieceIntegrand boundaryPiece_eq_zero_off)

/-- The selected compact-support M8 package built from support reconstruction
supplies the expected finite boundary partition sum. -/
theorem boundarySupportReconstruction_boundaryMeasureIntegral_eq_partitionSum
    {globalBulkIntegral globalBoundaryIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData (α := alpha) (μ := mu)
        selectedPartition targetImages globalBulkIntegral)
    (boundaryPartitionTerm : M -> BoundaryPiece -> Real)
    (boundaryPieceSet : M -> BoundaryPiece -> Set alpha)
    (boundaryPieceIntegrand : M -> BoundaryPiece -> alpha -> Real)
    (boundaryMeasureIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral =
        ∫ y,
          boundaryMeasurePieceSum selectedPartition.active
            targetImages.boundaryPieces boundaryPieceIntegrand y ∂mu)
    (boundaryPieceSet_measurable :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceCompactSupport :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (boundaryPartitionTerm_eq_setIntegral :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (boundaryPiece_eq_zero_off :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          forall y, y ∉ boundaryPieceSet x q ->
            boundaryPieceIntegrand x q y = 0) :
    (compactSupportToM8MeasureDataOfBoundarySupportReconstruction
      (alpha := alpha) (mu := mu)
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      bulk boundaryPartitionTerm boundaryPieceSet boundaryPieceIntegrand
      boundaryMeasureIntegral globalBoundaryIntegral_eq_boundaryMeasureIntegral
      boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
      boundaryPieceCompactSupport boundaryPartitionTerm_eq_setIntegral
      boundaryPiece_eq_zero_off).boundary.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm := by
  simpa [compactSupportToM8MeasureDataOfBoundarySupportReconstruction] using
    (compactSupportToM8MeasureDataOfReconstruction_boundaryMeasureIntegral_eq_partitionSum
      (α := alpha) (μ := mu) (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      bulk boundaryPartitionTerm
      (boundaryMeasurePieceSum selectedPartition.active
        targetImages.boundaryPieces boundaryPieceIntegrand)
      boundaryPieceSet boundaryPieceIntegrand boundaryMeasureIntegral
      globalBoundaryIntegral_eq_boundaryMeasureIntegral
      boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
      boundaryPieceCompactSupport boundaryPartitionTerm_eq_setIntegral
      (boundaryMeasurePieceSum_ae_eq_indicatorSum_of_eq_zero_off
        (mu := mu) selectedPartition.active targetImages.boundaryPieces
        boundaryPieceSet boundaryPieceIntegrand boundaryPiece_eq_zero_off))

end SelectedBoundaryM8FromSupport

end Stokes

end
