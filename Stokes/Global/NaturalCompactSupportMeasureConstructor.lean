import Stokes.Global.CompactSupportMeasureToM8Builder

/-!
# Natural compact-support measure constructor

This file gives a leaf constructor for the `measure` field of
`NaturalCompactSupportStokesInput`.

The inputs are the two real measure-reconstruction packages:

* selected-partition compact-support bulk reconstruction;
* boundary compact-support indicator/set-integral reconstruction.

The constructor fixes the selected active set and target boundary pieces
definitionally, then reuses the existing compact-support-to-M8 builder.  Thus
callers do not fill raw M8 measure fields or arbitrary active/piece alignment
records by hand.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportMeasureConstructor

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

/--
The boundary partition shape forced by the selected compact-support M8 data.

This is deliberately definitionally aligned with `selectedPartition.active` and
`targetImages.boundaryPieces`; the remaining hypotheses below are analytic
facts about the boundary measure, not bookkeeping equalities.
-/
def selectedBoundaryMeasurePartitionData
    (boundaryPartitionTerm : M → BoundaryPiece → Real) :
    BoundaryMeasurePartitionData M BoundaryPiece where
  activeCharts := selectedPartition.active
  boundaryPieces := targetImages.boundaryPieces
  boundaryPartitionTerm := boundaryPartitionTerm

@[simp]
theorem selectedBoundaryMeasurePartitionData_activeCharts
    (boundaryPartitionTerm : M → BoundaryPiece → Real) :
    (selectedBoundaryMeasurePartitionData
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      boundaryPartitionTerm).activeCharts =
      selectedPartition.active :=
  rfl

@[simp]
theorem selectedBoundaryMeasurePartitionData_boundaryPieces
    (boundaryPartitionTerm : M → BoundaryPiece → Real) :
    (selectedBoundaryMeasurePartitionData
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      boundaryPartitionTerm).boundaryPieces =
      targetImages.boundaryPieces :=
  rfl

@[simp]
theorem selectedBoundaryMeasurePartitionData_boundaryPartitionTerm
    (boundaryPartitionTerm : M → BoundaryPiece → Real) :
    (selectedBoundaryMeasurePartitionData
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      boundaryPartitionTerm).boundaryPartitionTerm =
      boundaryPartitionTerm :=
  rfl

/--
Builder data for compact-support measure localization from genuine bulk and
boundary reconstruction facts.

The boundary side is supplied by the standard analytic facts: represented
boundary integral, measurable piece sets, compact-support integrability of
piece integrands, set-integral identities, and a.e. indicator reconstruction.
-/
def compactSupportMeasureBuilderDataOfReconstruction
    {globalBulkIntegral globalBoundaryIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    (boundaryPartitionTerm : M → BoundaryPiece → Real)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : M → BoundaryPiece → Set α)
    (boundaryPieceIntegrand : M → BoundaryPiece → α → Real)
    (boundaryMeasureIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (boundaryPieceSet_measurable :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceCompactSupport :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (boundaryPartitionTerm_eq_setIntegral :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum selectedPartition.active
          targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand) :
    CompactSupportMeasureToM8BuilderData
      (α := α) I omega selectedPartition targetImages μ
      globalBulkIntegral globalBoundaryIntegral where
  bulk := bulk
  boundaryPartition :=
    selectedBoundaryMeasurePartitionData
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      boundaryPartitionTerm
  boundary_active := rfl
  boundary_pieces := rfl
  boundaryIntegrand := boundaryIntegrand
  boundaryPieceSet := boundaryPieceSet
  boundaryPieceIntegrand := boundaryPieceIntegrand
  boundaryMeasureIntegral := boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    globalBoundaryIntegral_eq_boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_integral :=
    boundaryMeasureIntegral_eq_integral
  boundaryPieceSet_measurable := boundaryPieceSet_measurable
  boundaryPieceCompactSupport := boundaryPieceCompactSupport
  boundaryPartitionTerm_eq_setIntegral :=
    boundaryPartitionTerm_eq_setIntegral
  boundaryIntegrand_ae_eq_indicatorSum :=
    boundaryIntegrand_ae_eq_indicatorSum

/--
Clean constructor for the compact-support M8 measure package.

This is the theorem-facing constructor for the `measure` field of
`NaturalCompactSupportStokesInput`: the caller supplies compact-support bulk
localization plus boundary a.e./integrability/set-integral reconstruction, and
gets the resolved `CompactSupportToM8MeasureData`.
-/
def compactSupportToM8MeasureDataOfReconstruction
    {globalBulkIntegral globalBoundaryIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    (boundaryPartitionTerm : M → BoundaryPiece → Real)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : M → BoundaryPiece → Set α)
    (boundaryPieceIntegrand : M → BoundaryPiece → α → Real)
    (boundaryMeasureIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (boundaryPieceSet_measurable :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceCompactSupport :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (boundaryPartitionTerm_eq_setIntegral :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum selectedPartition.active
          targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand) :
    CompactSupportToM8MeasureData
      (α := α) I omega selectedPartition targetImages μ :=
  (compactSupportMeasureBuilderDataOfReconstruction
    (α := α) (μ := μ)
    (I := I) (omega := omega)
    (selectedPartition := selectedPartition)
    (targetImages := targetImages)
    bulk boundaryPartitionTerm boundaryIntegrand boundaryPieceSet
    boundaryPieceIntegrand boundaryMeasureIntegral
    globalBoundaryIntegral_eq_boundaryMeasureIntegral
    boundaryMeasureIntegral_eq_integral
    boundaryPieceSet_measurable boundaryPieceCompactSupport
    boundaryPartitionTerm_eq_setIntegral
    boundaryIntegrand_ae_eq_indicatorSum).toCompactSupportToM8MeasureData

@[simp]
theorem compactSupportToM8MeasureDataOfReconstruction_globalBulkIntegral
    {globalBulkIntegral globalBoundaryIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    (boundaryPartitionTerm : M → BoundaryPiece → Real)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : M → BoundaryPiece → Set α)
    (boundaryPieceIntegrand : M → BoundaryPiece → α → Real)
    (boundaryMeasureIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (boundaryPieceSet_measurable :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceCompactSupport :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (boundaryPartitionTerm_eq_setIntegral :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum selectedPartition.active
          targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand) :
    (compactSupportToM8MeasureDataOfReconstruction
      (α := α) (μ := μ)
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      bulk boundaryPartitionTerm boundaryIntegrand boundaryPieceSet
      boundaryPieceIntegrand boundaryMeasureIntegral
      globalBoundaryIntegral_eq_boundaryMeasureIntegral
      boundaryMeasureIntegral_eq_integral
      boundaryPieceSet_measurable boundaryPieceCompactSupport
      boundaryPartitionTerm_eq_setIntegral
      boundaryIntegrand_ae_eq_indicatorSum).globalBulkIntegral =
      globalBulkIntegral :=
  rfl

@[simp]
theorem compactSupportToM8MeasureDataOfReconstruction_boundaryPartitionTerm
    {globalBulkIntegral globalBoundaryIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    (boundaryPartitionTerm : M → BoundaryPiece → Real)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : M → BoundaryPiece → Set α)
    (boundaryPieceIntegrand : M → BoundaryPiece → α → Real)
    (boundaryMeasureIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (boundaryPieceSet_measurable :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceCompactSupport :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (boundaryPartitionTerm_eq_setIntegral :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum selectedPartition.active
          targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand) :
    (compactSupportToM8MeasureDataOfReconstruction
      (α := α) (μ := μ)
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      bulk boundaryPartitionTerm boundaryIntegrand boundaryPieceSet
      boundaryPieceIntegrand boundaryMeasureIntegral
      globalBoundaryIntegral_eq_boundaryMeasureIntegral
      boundaryMeasureIntegral_eq_integral
      boundaryPieceSet_measurable boundaryPieceCompactSupport
      boundaryPartitionTerm_eq_setIntegral
      boundaryIntegrand_ae_eq_indicatorSum).boundaryPartitionTerm =
      boundaryPartitionTerm :=
  rfl

@[simp]
theorem compactSupportToM8MeasureDataOfReconstruction_globalBoundaryIntegral
    {globalBulkIntegral globalBoundaryIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    (boundaryPartitionTerm : M → BoundaryPiece → Real)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : M → BoundaryPiece → Set α)
    (boundaryPieceIntegrand : M → BoundaryPiece → α → Real)
    (boundaryMeasureIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (boundaryPieceSet_measurable :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceCompactSupport :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (boundaryPartitionTerm_eq_setIntegral :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum selectedPartition.active
          targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand) :
    (compactSupportToM8MeasureDataOfReconstruction
      (α := α) (μ := μ)
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      bulk boundaryPartitionTerm boundaryIntegrand boundaryPieceSet
      boundaryPieceIntegrand boundaryMeasureIntegral
      globalBoundaryIntegral_eq_boundaryMeasureIntegral
      boundaryMeasureIntegral_eq_integral
      boundaryPieceSet_measurable boundaryPieceCompactSupport
      boundaryPartitionTerm_eq_setIntegral
      boundaryIntegrand_ae_eq_indicatorSum).globalBoundaryIntegral =
      globalBoundaryIntegral :=
  rfl

@[simp]
theorem compactSupportToM8MeasureDataOfReconstruction_boundaryMeasureIntegral
    {globalBulkIntegral globalBoundaryIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    (boundaryPartitionTerm : M → BoundaryPiece → Real)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : M → BoundaryPiece → Set α)
    (boundaryPieceIntegrand : M → BoundaryPiece → α → Real)
    (boundaryMeasureIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (boundaryPieceSet_measurable :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceCompactSupport :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (boundaryPartitionTerm_eq_setIntegral :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum selectedPartition.active
          targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand) :
    (compactSupportToM8MeasureDataOfReconstruction
      (α := α) (μ := μ)
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      bulk boundaryPartitionTerm boundaryIntegrand boundaryPieceSet
      boundaryPieceIntegrand boundaryMeasureIntegral
      globalBoundaryIntegral_eq_boundaryMeasureIntegral
      boundaryMeasureIntegral_eq_integral
      boundaryPieceSet_measurable boundaryPieceCompactSupport
      boundaryPartitionTerm_eq_setIntegral
      boundaryIntegrand_ae_eq_indicatorSum).boundary.boundaryMeasureIntegral =
      boundaryMeasureIntegral := by
  rfl

/--
The constructed measure package supplies the bulk finite-sum reconstruction in
the selected M8 shape.
-/
theorem compactSupportToM8MeasureDataOfReconstruction_bulkMeasureIntegral_eq_localBulkSum
    {globalBulkIntegral globalBoundaryIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    (boundaryPartitionTerm : M → BoundaryPiece → Real)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : M → BoundaryPiece → Set α)
    (boundaryPieceIntegrand : M → BoundaryPiece → α → Real)
    (boundaryMeasureIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (boundaryPieceSet_measurable :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceCompactSupport :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (boundaryPartitionTerm_eq_setIntegral :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum selectedPartition.active
          targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand) :
    (compactSupportToM8MeasureDataOfReconstruction
      (α := α) (μ := μ)
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      bulk boundaryPartitionTerm boundaryIntegrand boundaryPieceSet
      boundaryPieceIntegrand boundaryMeasureIntegral
      globalBoundaryIntegral_eq_boundaryMeasureIntegral
      boundaryMeasureIntegral_eq_integral
      boundaryPieceSet_measurable boundaryPieceCompactSupport
      boundaryPartitionTerm_eq_setIntegral
      boundaryIntegrand_ae_eq_indicatorSum).globalBulkIntegral =
      (Finset.sum selectedPartition.active fun x =>
        Finset.sum ({()} : Finset Unit) fun _q =>
          bulk.localized.localizedInterior.bulkTerm x) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (targetImages.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm targetImages x q := by
  simpa using
    (compactSupportToM8MeasureDataOfReconstruction
      (α := α) (μ := μ)
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      bulk boundaryPartitionTerm boundaryIntegrand boundaryPieceSet
      boundaryPieceIntegrand boundaryMeasureIntegral
      globalBoundaryIntegral_eq_boundaryMeasureIntegral
      boundaryMeasureIntegral_eq_integral
      boundaryPieceSet_measurable boundaryPieceCompactSupport
      boundaryPartitionTerm_eq_setIntegral
      boundaryIntegrand_ae_eq_indicatorSum).bulkMeasureIntegral_eq_localBulkSum

/--
The constructed measure package supplies the boundary finite-sum
reconstruction over the selected target boundary pieces.
-/
theorem compactSupportToM8MeasureDataOfReconstruction_boundaryMeasureIntegral_eq_partitionSum
    {globalBulkIntegral globalBoundaryIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    (boundaryPartitionTerm : M → BoundaryPiece → Real)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : M → BoundaryPiece → Set α)
    (boundaryPieceIntegrand : M → BoundaryPiece → α → Real)
    (boundaryMeasureIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (boundaryPieceSet_measurable :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceCompactSupport :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (boundaryPartitionTerm_eq_setIntegral :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum selectedPartition.active
          targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand) :
    (compactSupportToM8MeasureDataOfReconstruction
      (α := α) (μ := μ)
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      bulk boundaryPartitionTerm boundaryIntegrand boundaryPieceSet
      boundaryPieceIntegrand boundaryMeasureIntegral
      globalBoundaryIntegral_eq_boundaryMeasureIntegral
      boundaryMeasureIntegral_eq_integral
      boundaryPieceSet_measurable boundaryPieceCompactSupport
      boundaryPartitionTerm_eq_setIntegral
      boundaryIntegrand_ae_eq_indicatorSum).boundary.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm := by
  simpa using
    (compactSupportToM8MeasureDataOfReconstruction
      (α := α) (μ := μ)
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      bulk boundaryPartitionTerm boundaryIntegrand boundaryPieceSet
      boundaryPieceIntegrand boundaryMeasureIntegral
      globalBoundaryIntegral_eq_boundaryMeasureIntegral
      boundaryMeasureIntegral_eq_integral
      boundaryPieceSet_measurable boundaryPieceCompactSupport
      boundaryPartitionTerm_eq_setIntegral
      boundaryIntegrand_ae_eq_indicatorSum).boundary.boundaryMeasureIntegral_eq_partitionSum

end NaturalCompactSupportMeasureConstructor

end Stokes

end
