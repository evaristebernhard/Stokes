import Stokes.Global.BulkDerivativeIndicatorFromPartition
import Stokes.Global.SupportControlledSelectedPartition

/-!
# Cover-indexed bulk reconstruction

This file records the cover-indexed version of the bulk indicator
reconstruction step.  The intended input is a finite cover-indexed scalar
partition identity

`F =ᵐ[μ] fun y => ∑ i ∈ active, f i y`

together with support control of each cover-indexed summand in its assigned
box.  The output is the indicator-localized reconstruction consumed by the
bulk measure-localization fields.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedFiniteSum

universe i a

variable {ι : Type i}
variable {α : Type a}

/-- The unlocalized finite sum of cover-indexed bulk scalar terms. -/
def coverIndexedBulkUnlocalizedSum
    (active : Finset ι) (f : ι → α → Real) : α → Real :=
  fun y => Finset.sum active fun i => f i y

/-- The finite sum of cover-indexed bulk scalar terms localized to their boxes. -/
def coverIndexedBulkIndicatorSum
    (active : Finset ι) (box : ι → Set α) (f : ι → α → Real) :
    α → Real :=
  fun y => Finset.sum active fun i => (box i).indicator (f i) y

variable [TopologicalSpace α]

/-- Pointwise cover-indexed indicator insertion from topological support control. -/
theorem coverIndexed_bulkUnlocalizedSum_eq_indicator_sum_of_tsupport_subset
    (active : Finset ι) (box : ι → Set α) (f : ι → α → Real)
    (hsupp :
      ∀ i, i ∈ active → tsupport (f i) ⊆ box i) :
    coverIndexedBulkUnlocalizedSum active f =
      coverIndexedBulkIndicatorSum active box f := by
  have hsupport :
      ∀ i, i ∈ active → Function.support (f i) ⊆ box i := by
    intro i hi
    exact support_subset_of_tsupport_subset_box (f := f i) (hsupp i hi)
  funext y
  simpa [coverIndexedBulkUnlocalizedSum, coverIndexedBulkIndicatorSum,
    Finset.sum_apply] using
      congrFun
        (finset_sum_eq_indicator_sum_of_support_subset active box f hsupport) y

variable [MeasurableSpace α] {μ : Measure α}

/--
If the cover-indexed unlocalized finite sum reconstructs `F` a.e. and every
active summand has topological support in its assigned box, then `F` is a.e.
the corresponding cover-indexed indicator sum.
-/
theorem coverIndexed_bulkIntegrand_ae_eq_indicator_sum_of_tsupport_subset
    (active : Finset ι) (F : α → Real)
    (box : ι → Set α) (f : ι → α → Real)
    (hF : F =ᵐ[μ] fun y => Finset.sum active fun i => f i y)
    (hsupp :
      ∀ i, i ∈ active → tsupport (f i) ⊆ box i) :
    F =ᵐ[μ] coverIndexedBulkIndicatorSum active box f := by
  have hsum :
      (fun y => Finset.sum active fun i => f i y) =ᵐ[μ]
        coverIndexedBulkIndicatorSum active box f :=
    Filter.Eventually.of_forall fun y =>
      congrFun
        (coverIndexed_bulkUnlocalizedSum_eq_indicator_sum_of_tsupport_subset
          active box f hsupp) y
  exact hF.trans hsum

omit [TopologicalSpace α] in
/--
Off-box-zero variant of the cover-indexed indicator reconstruction.

This is useful when local box support is available as a vanishing statement
rather than as topological support containment.
-/
theorem coverIndexed_bulkIntegrand_ae_eq_indicator_sum_of_eq_zero_off
    (active : Finset ι) (F : α → Real)
    (box : ι → Set α) (f : ι → α → Real)
    (hF : F =ᵐ[μ] fun y => Finset.sum active fun i => f i y)
    (hzero :
      ∀ i, i ∈ active → ∀ y, y ∉ box i → f i y = 0) :
    F =ᵐ[μ] coverIndexedBulkIndicatorSum active box f := by
  have hsum :
      (fun y => Finset.sum active fun i => f i y) =ᵐ[μ]
        coverIndexedBulkIndicatorSum active box f := by
    have hsupport :
        ∀ i, i ∈ active → Function.support (f i) ⊆ box i := by
      intro i hi
      exact support_subset_of_eq_zero_off (hzero i hi)
    exact Filter.Eventually.of_forall fun y =>
      by
        simpa [coverIndexedBulkIndicatorSum, Finset.sum_apply] using
          congrFun
            (finset_sum_eq_indicator_sum_of_support_subset
              active box f hsupport) y
  exact hF.trans hsum

/-- Finite-type wrapper: the active cover is the full finite index type. -/
theorem finiteType_coverIndexed_bulkIntegrand_ae_eq_indicator_sum_of_tsupport_subset
    [Fintype ι] (F : α → Real)
    (box : ι → Set α) (f : ι → α → Real)
    (hF : F =ᵐ[μ] fun y => ∑ i : ι, f i y)
    (hsupp : ∀ i, tsupport (f i) ⊆ box i) :
    F =ᵐ[μ]
      coverIndexedBulkIndicatorSum (Finset.univ : Finset ι) box f := by
  classical
  exact
    coverIndexed_bulkIntegrand_ae_eq_indicator_sum_of_tsupport_subset
      (μ := μ) (active := Finset.univ) F box f
      (by simpa using hF)
      (fun i _hi => hsupp i)

end CoverIndexedFiniteSum

section CoverIndexedMeasureFields

universe u w i c p a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type i}
variable {BoundaryChart : Type c} {BoundaryPiece : Type p}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {interior : LocalizedInteriorPieces (ι := ι) I ω}
variable {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
variable {globalBulkIntegral : Real}

/--
Construct the existing bulk measure-localization fields from a flat
cover-indexed indicator reconstruction.

The cover-indexed family is used as the interior-indexed side of the existing
bulk measure package.  The boundary side is required to have no active charts,
so its term and box functions are bookkeeping only.
-/
def coverIndexed_bulkMeasureFields_of_indicator_reconstruction
    (hboundary_inactive : boundary.activeCharts = ∅)
    (F : α → Real)
    (localTerm : ι → α → Real)
    (box : ι → Set α)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (hglobal : globalBulkIntegral = ∫ y, F y ∂μ)
    (hBoxMeasurable :
      ∀ i, i ∈ interior.active → MeasurableSet (box i))
    (hIntegrable :
      ∀ i, i ∈ interior.active → IntegrableOn (localTerm i) (box i) μ)
    (hBulkTerm :
      ∀ i, i ∈ interior.active →
        interior.bulkTerm i = ∫ y in box i, localTerm i y ∂μ)
    (hF :
      F =ᵐ[μ] coverIndexedBulkIndicatorSum interior.active box localTerm) :
    BulkIntegralPartitionInput.BulkMeasureLocalizationFields
      (α := α) μ interior boundary globalBulkIntegral := by
  have hFbulk :
      F =ᵐ[μ]
        bulkMeasureIndicatorSum interior.active boundary.activeCharts
          boundary.boundaryPieces box boundaryBox localTerm boundaryLocalTerm := by
    refine hF.trans (Filter.Eventually.of_forall ?_)
    intro y
    simp [coverIndexedBulkIndicatorSum, bulkMeasureIndicatorSum,
      bulkMeasureInteriorIndicatorSum, bulkMeasureBoundaryIndicatorSum,
      hboundary_inactive]
  refine
    BulkIntegralPartitionInput.BulkMeasureLocalizationFields.ofDerivativePartitionAEIndicator
        (μ := μ) (interior := interior) (boundary := boundary)
        (globalBulkIntegral := globalBulkIntegral)
        F localTerm boundaryLocalTerm box boundaryBox hglobal
        hBoxMeasurable ?_ hIntegrable ?_ hBulkTerm ?_ ?_
  · intro x hx q _hq
    have hxEmpty : x ∈ (∅ : Finset BoundaryChart) := by
      rwa [hboundary_inactive] at hx
    exact False.elim (Finset.notMem_empty x hxEmpty)
  · intro x hx q _hq
    have hxEmpty : x ∈ (∅ : Finset BoundaryChart) := by
      rwa [hboundary_inactive] at hx
    exact False.elim (Finset.notMem_empty x hxEmpty)
  · intro x hx q _hq
    have hxEmpty : x ∈ (∅ : Finset BoundaryChart) := by
      rwa [hboundary_inactive] at hx
    exact False.elim (Finset.notMem_empty x hxEmpty)
  · exact hFbulk

/--
Cover-indexed constructor for `BulkIntegralPartitionInput`, obtained by
forgetting the intermediate measure-localization field package.
-/
def coverIndexed_bulkIntegralPartitionInput_of_indicator_reconstruction
    (hboundary_inactive : boundary.activeCharts = ∅)
    (F : α → Real)
    (localTerm : ι → α → Real)
    (box : ι → Set α)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (hglobal : globalBulkIntegral = ∫ y, F y ∂μ)
    (hBoxMeasurable :
      ∀ i, i ∈ interior.active → MeasurableSet (box i))
    (hIntegrable :
      ∀ i, i ∈ interior.active → IntegrableOn (localTerm i) (box i) μ)
    (hBulkTerm :
      ∀ i, i ∈ interior.active →
        interior.bulkTerm i = ∫ y in box i, localTerm i y ∂μ)
    (hF :
      F =ᵐ[μ] coverIndexedBulkIndicatorSum interior.active box localTerm) :
    BulkIntegralPartitionInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece) :=
  (coverIndexed_bulkMeasureFields_of_indicator_reconstruction
    (μ := μ) (interior := interior) (boundary := boundary)
    (globalBulkIntegral := globalBulkIntegral)
    hboundary_inactive F localTerm box boundaryLocalTerm boundaryBox hglobal
    hBoxMeasurable hIntegrable hBulkTerm hF).toBulkIntegralPartitionInput

end CoverIndexedMeasureFields

section CoverIndexWrappers

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {μ : Measure (Fin (n + 1) → Real)}

/--
Wrapper for a selected chart-box cover: the cover-indexed active set is
`Finset.univ : Finset C.CoverIndex`, and the boxes are the assigned coordinate
boxes of the cover selection.
-/
theorem coverIndex_bulkIntegrand_ae_eq_indicator_sum_of_tsupport_subset
    (C : CompactSupportChartCoverSelection I K)
    (F : (Fin (n + 1) → Real) → Real)
    (f : C.CoverIndex → (Fin (n + 1) → Real) → Real)
    (hF : F =ᵐ[μ] fun y => ∑ j : C.CoverIndex, f j y)
    (hsupp :
      ∀ j, tsupport (f j) ⊆ C.assignedCoordinateBox j) :
    F =ᵐ[μ]
      coverIndexedBulkIndicatorSum
        (Finset.univ : Finset C.CoverIndex)
        C.assignedCoordinateBox f := by
  classical
  exact
    finiteType_coverIndexed_bulkIntegrand_ae_eq_indicator_sum_of_tsupport_subset
      (μ := μ) F C.assignedCoordinateBox f hF hsupp

namespace SupportControlledSelectedPartition

variable {C : CompactSupportChartCoverSelection I K}

/--
Support-controlled-partition wrapper exposing the same reconstruction over the
mixed cover index type carried by `C`.
-/
theorem coverIndexed_bulkIntegrand_ae_eq_indicator_sum_of_tsupport_subset
    (P : SupportControlledSelectedPartition C)
    (F : (Fin (n + 1) → Real) → Real)
    (f : C.CoverIndex → (Fin (n + 1) → Real) → Real)
    (hF : F =ᵐ[μ] fun y => ∑ j : C.CoverIndex, f j y)
    (hsupp :
      ∀ j, tsupport (f j) ⊆ C.assignedCoordinateBox j) :
    F =ᵐ[μ]
      coverIndexedBulkIndicatorSum
        (Finset.univ : Finset C.CoverIndex)
        C.assignedCoordinateBox f := by
  classical
  let _controlledPartition := P
  exact coverIndex_bulkIntegrand_ae_eq_indicator_sum_of_tsupport_subset
    (μ := μ) C F f hF hsupp

end SupportControlledSelectedPartition

end CoverIndexWrappers

end Stokes

end
