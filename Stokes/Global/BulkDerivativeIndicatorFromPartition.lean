import Stokes.Global.PartitionExtDerivSumIdentity
import Stokes.Global.BulkMeasureFromDerivativePartition

/-!
# Bulk derivative indicator reconstruction from partition finite sums

This file supplies the L5-to-L6 support step for the bulk side.  The partition
exterior-derivative layer naturally produces an a.e. finite-sum reconstruction
of a scalar bulk integrand.  The measure-localization layer wants the same
finite sum with every local scalar term restricted by the indicator of its
selected box.

The key input here is topological support containment: if `tsupport f` lies in
the selected box, then `f` agrees pointwise, hence a.e., with its
indicator-localized version.  Finite sums and the selected-partition constructor
are then just bookkeeping around that fact.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section TopologicalSupportIndicator

universe u v

variable {α : Type u} [TopologicalSpace α]
variable {β : Type v} [Zero β]
variable {box : Set α} {f : α → β}

/-- Algebraic support is contained in any set containing the topological support. -/
theorem support_subset_of_tsupport_subset_box
    (hsupp : tsupport f ⊆ box) :
    Function.support f ⊆ box :=
  (subset_tsupport f).trans hsupp

/-- A function whose topological support lies in `box` vanishes pointwise off `box`. -/
theorem eq_zero_of_notMem_of_tsupport_subset_box
    (hsupp : tsupport f ⊆ box) {x : α} (hx : x ∉ box) :
    f x = 0 := by
  exact Function.notMem_support.mp fun hx_support =>
    hx (support_subset_of_tsupport_subset_box (f := f) hsupp hx_support)

/-- Pointwise indicator reconstruction from topological support containment. -/
theorem eq_indicator_of_tsupport_subset_box
    (hsupp : tsupport f ⊆ box) :
    f = box.indicator f :=
  eq_indicator_of_support_subset
    (s := box) (f := f)
    (support_subset_of_tsupport_subset_box (f := f) hsupp)

variable [MeasurableSpace α] {μ : Measure α}

/-- A.e. indicator reconstruction from topological support containment. -/
theorem ae_eq_indicator_of_tsupport_subset_box
    (hsupp : tsupport f ⊆ box) :
    f =ᵐ[μ] box.indicator f :=
  ae_eq_indicator_of_support_subset
    (μ := μ) (s := box) (f := f)
    (support_subset_of_tsupport_subset_box (f := f) hsupp)

end TopologicalSupportIndicator

section BulkFiniteSum

universe a i c p

variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable {ι : Type i} {BoundaryChart : Type c} {BoundaryPiece : Type p}
variable {μ : Measure α}

omit [MeasurableSpace α] in
/--
If every local bulk scalar term has topological support in its selected box,
the unlocalized split bulk sum is pointwise the corresponding indicator sum.
-/
theorem bulkMeasureUnlocalizedSum_eq_indicatorSum_of_tsupport_subset
    (activeInterior : Finset ι)
    (activeBoundaryCharts : Finset BoundaryChart)
    (boundaryPieces : BoundaryChart → Finset BoundaryPiece)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real)
    (hInteriorTSupport :
      ∀ i, i ∈ activeInterior →
        tsupport (interiorLocalTerm i) ⊆ interiorBox i)
    (hBoundaryTSupport :
      ∀ x, x ∈ activeBoundaryCharts →
        ∀ q, q ∈ boundaryPieces x →
          tsupport (boundaryLocalTerm x q) ⊆ boundaryBox x q) :
    bulkMeasureUnlocalizedSum activeInterior activeBoundaryCharts
        boundaryPieces interiorLocalTerm boundaryLocalTerm =
      bulkMeasureIndicatorSum activeInterior activeBoundaryCharts
        boundaryPieces interiorBox boundaryBox interiorLocalTerm
        boundaryLocalTerm :=
  bulkMeasureUnlocalizedSum_eq_indicatorSum_of_support_subset
    activeInterior activeBoundaryCharts boundaryPieces interiorBox
    boundaryBox interiorLocalTerm boundaryLocalTerm
    (fun i hi =>
      support_subset_of_tsupport_subset_box
        (f := interiorLocalTerm i) (hInteriorTSupport i hi))
    (fun x hx q hq =>
      support_subset_of_tsupport_subset_box
        (f := boundaryLocalTerm x q) (hBoundaryTSupport x hx q hq))

/-- A.e. version of `bulkMeasureUnlocalizedSum_eq_indicatorSum_of_tsupport_subset`. -/
theorem bulkMeasureUnlocalizedSum_ae_eq_indicatorSum_of_tsupport_subset
    (activeInterior : Finset ι)
    (activeBoundaryCharts : Finset BoundaryChart)
    (boundaryPieces : BoundaryChart → Finset BoundaryPiece)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real)
    (hInteriorTSupport :
      ∀ i, i ∈ activeInterior →
        tsupport (interiorLocalTerm i) ⊆ interiorBox i)
    (hBoundaryTSupport :
      ∀ x, x ∈ activeBoundaryCharts →
        ∀ q, q ∈ boundaryPieces x →
          tsupport (boundaryLocalTerm x q) ⊆ boundaryBox x q) :
    bulkMeasureUnlocalizedSum activeInterior activeBoundaryCharts
        boundaryPieces interiorLocalTerm boundaryLocalTerm =ᵐ[μ]
      bulkMeasureIndicatorSum activeInterior activeBoundaryCharts
        boundaryPieces interiorBox boundaryBox interiorLocalTerm
        boundaryLocalTerm :=
  Filter.Eventually.of_forall fun y =>
    congrFun
      (bulkMeasureUnlocalizedSum_eq_indicatorSum_of_tsupport_subset
        activeInterior activeBoundaryCharts boundaryPieces interiorBox
        boundaryBox interiorLocalTerm boundaryLocalTerm hInteriorTSupport
        hBoundaryTSupport) y

/--
Turn the L5 finite-sum a.e. reconstruction into the L6 indicator-on-box shape,
using topological support containment for every localized scalar term.
-/
theorem bulkIntegrand_ae_eq_indicator_sum_of_localized_tsupport_subset
    (activeInterior : Finset ι)
    (activeBoundaryCharts : Finset BoundaryChart)
    (boundaryPieces : BoundaryChart → Finset BoundaryPiece)
    (F : α → Real)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real)
    (hFinite :
      F =ᵐ[μ] fun y =>
        (Finset.sum activeInterior fun i => interiorLocalTerm i y) +
          Finset.sum activeBoundaryCharts fun x =>
            Finset.sum (boundaryPieces x) fun q =>
              boundaryLocalTerm x q y)
    (hInteriorTSupport :
      ∀ i, i ∈ activeInterior →
        tsupport (interiorLocalTerm i) ⊆ interiorBox i)
    (hBoundaryTSupport :
      ∀ x, x ∈ activeBoundaryCharts →
        ∀ q, q ∈ boundaryPieces x →
          tsupport (boundaryLocalTerm x q) ⊆ boundaryBox x q) :
    F =ᵐ[μ]
      bulkMeasureIndicatorSum activeInterior activeBoundaryCharts
        boundaryPieces interiorBox boundaryBox interiorLocalTerm
        boundaryLocalTerm := by
  have hUnlocalized :
      F =ᵐ[μ]
        bulkMeasureUnlocalizedSum activeInterior activeBoundaryCharts
          boundaryPieces interiorLocalTerm boundaryLocalTerm := by
    simpa [bulkMeasureUnlocalizedSum] using hFinite
  exact hUnlocalized.trans
    (bulkMeasureUnlocalizedSum_ae_eq_indicatorSum_of_tsupport_subset
      (μ := μ) activeInterior activeBoundaryCharts boundaryPieces
      interiorBox boundaryBox interiorLocalTerm boundaryLocalTerm
      hInteriorTSupport hBoundaryTSupport)

/--
Variant whose L5 input is already expressed with `bulkMeasureUnlocalizedSum`.
-/
theorem bulkIntegrand_ae_eq_indicator_sum_of_unlocalized_tsupport_subset
    (activeInterior : Finset ι)
    (activeBoundaryCharts : Finset BoundaryChart)
    (boundaryPieces : BoundaryChart → Finset BoundaryPiece)
    (F : α → Real)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real)
    (hFinite :
      F =ᵐ[μ]
        bulkMeasureUnlocalizedSum activeInterior activeBoundaryCharts
          boundaryPieces interiorLocalTerm boundaryLocalTerm)
    (hInteriorTSupport :
      ∀ i, i ∈ activeInterior →
        tsupport (interiorLocalTerm i) ⊆ interiorBox i)
    (hBoundaryTSupport :
      ∀ x, x ∈ activeBoundaryCharts →
        ∀ q, q ∈ boundaryPieces x →
          tsupport (boundaryLocalTerm x q) ⊆ boundaryBox x q) :
    F =ᵐ[μ]
      bulkMeasureIndicatorSum activeInterior activeBoundaryCharts
        boundaryPieces interiorBox boundaryBox interiorLocalTerm
        boundaryLocalTerm :=
  hFinite.trans
    (bulkMeasureUnlocalizedSum_ae_eq_indicatorSum_of_tsupport_subset
      (μ := μ) activeInterior activeBoundaryCharts boundaryPieces
      interiorBox boundaryBox interiorLocalTerm boundaryLocalTerm
      hInteriorTSupport hBoundaryTSupport)

end BulkFiniteSum

section SelectedPartition

universe u w p a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable {μ : Measure α}
variable {BoundaryPiece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {P : SelectedBoxPartitionOfUnity I ω}
variable {boundary : BoundaryPieceFamilyInput I ω M BoundaryPiece}

/--
Selected-partition `hF` builder for
`selectedBulkIntegralPartitionInputOfDerivativePartitionAEIndicator`.

The input is the L5 finite-sum a.e. shape over `P.active`, plus topological
support containment of every selected scalar term in its selected box.
-/
theorem selectedBulkIntegralPartitionInputOfDerivativePartitionAEIndicator_hF_of_tsupport_subset
    (F : α → Real)
    (interiorLocalTerm : M → α → Real)
    (boundaryLocalTerm : M → BoundaryPiece → α → Real)
    (interiorBox : M → Set α)
    (boundaryBox : M → BoundaryPiece → Set α)
    (hFinite :
      F =ᵐ[μ] fun y =>
        (Finset.sum P.active fun i => interiorLocalTerm i y) +
          Finset.sum P.active fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              boundaryLocalTerm x q y)
    (hInteriorTSupport :
      ∀ i, i ∈ P.active →
        tsupport (interiorLocalTerm i) ⊆ interiorBox i)
    (hBoundaryTSupport :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x →
          tsupport (boundaryLocalTerm x q) ⊆ boundaryBox x q) :
    F =ᵐ[μ]
      bulkMeasureIndicatorSum P.active P.active boundary.boundaryPieces
        interiorBox boundaryBox interiorLocalTerm boundaryLocalTerm :=
  bulkIntegrand_ae_eq_indicator_sum_of_localized_tsupport_subset
    (μ := μ) P.active P.active boundary.boundaryPieces F interiorBox
    boundaryBox interiorLocalTerm boundaryLocalTerm hFinite
    hInteriorTSupport hBoundaryTSupport

/--
Selected-partition constructor that consumes the L5 finite-sum a.e. shape and
topological support containment, then feeds the resulting indicator
reconstruction to the existing L6 measure constructor.
-/
def selectedBulkIntegralPartitionInputOfDerivativePartitionFiniteSumTSupport
    [OpensMeasurableSpace α] [T2Space α] [IsFiniteMeasureOnCompacts μ]
    {localized : LocalizedInteriorM8Fields I ω P}
    {globalBulkIntegral : Real}
    (hboundary_active : boundary.activeCharts = P.active)
    (F : α → Real)
    (interiorLocalTerm : M → α → Real)
    (boundaryLocalTerm : M → BoundaryPiece → α → Real)
    (interiorBox : M → Set α)
    (boundaryBox : M → BoundaryPiece → Set α)
    (hglobal : globalBulkIntegral = ∫ y, F y ∂μ)
    (hInteriorMeasurable :
      ∀ i, i ∈ P.active → MeasurableSet (interiorBox i))
    (hBoundaryMeasurable :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x → MeasurableSet (boundaryBox x q))
    (hInteriorIntegrable :
      ∀ i, i ∈ P.active →
        IntegrableOn (interiorLocalTerm i) (interiorBox i) μ)
    (hBoundaryIntegrable :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x →
          IntegrableOn (boundaryLocalTerm x q) (boundaryBox x q) μ)
    (hInteriorBulkTerm :
      ∀ i, i ∈ P.active →
        localized.localizedInterior.bulkTerm i =
          ∫ y in interiorBox i, interiorLocalTerm i y ∂μ)
    (hBoundaryBulkTerm :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x →
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ)
    (hFinite :
      F =ᵐ[μ] fun y =>
        (Finset.sum P.active fun i => interiorLocalTerm i y) +
          Finset.sum P.active fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              boundaryLocalTerm x q y)
    (hInteriorTSupport :
      ∀ i, i ∈ P.active →
        tsupport (interiorLocalTerm i) ⊆ interiorBox i)
    (hBoundaryTSupport :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x →
          tsupport (boundaryLocalTerm x q) ⊆ boundaryBox x q) :
    BulkIntegralPartitionInput
      (ι := M) (I := I) (ω := ω)
      (BoundaryChart := M) (BoundaryPiece := BoundaryPiece) :=
  selectedBulkIntegralPartitionInputOfDerivativePartitionAEIndicator
    (μ := μ) (P := P) (boundary := boundary) (localized := localized)
    (globalBulkIntegral := globalBulkIntegral)
    hboundary_active F interiorLocalTerm boundaryLocalTerm interiorBox
    boundaryBox hglobal hInteriorMeasurable hBoundaryMeasurable
    hInteriorIntegrable hBoundaryIntegrable hInteriorBulkTerm
    hBoundaryBulkTerm
    (selectedBulkIntegralPartitionInputOfDerivativePartitionAEIndicator_hF_of_tsupport_subset
      (μ := μ) (P := P) (boundary := boundary) F interiorLocalTerm
      boundaryLocalTerm interiorBox boundaryBox hFinite hInteriorTSupport
      hBoundaryTSupport)

end SelectedPartition

end Stokes

end
