import Stokes.Global.BulkMeasureLocalizationFields
import Stokes.Global.CompactSupportIntegrability
import Stokes.Global.IndicatorSupportLocalization

/-!
# Compact-support bulk measure localization

This file is the compact-support entry point for the pure bulk measure
localization package.

The genuinely analytic inputs are still explicit: callers must provide the
represented global integral, the local set-integral identities, compact-support
data for each local integrand, and the a.e. reconstruction of the global
integrand as the unlocalized finite sum.  The constructor here supplies the
two fields that should not be hand-written downstream:

* `IntegrableOn` on every selected localization box, from compact support;
* the indicator-localized a.e. reconstruction, from support containment.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section PureBulkIndicatorSupport

universe a i c p

variable {α : Type a}
variable {ι : Type i} {BoundaryChart : Type c} {BoundaryPiece : Type p}

/-- The unlocalized finite sum of all bulk local integrands. -/
def bulkMeasureUnlocalizedSum
    (activeInterior : Finset ι)
    (activeBoundaryCharts : Finset BoundaryChart)
    (boundaryPieces : BoundaryChart → Finset BoundaryPiece)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real) :
    α → Real :=
  fun y =>
    (Finset.sum activeInterior fun i => interiorLocalTerm i y) +
      Finset.sum activeBoundaryCharts fun x =>
        Finset.sum (boundaryPieces x) fun q =>
          boundaryLocalTerm x q y

/--
If every selected local term is supported in its selected localization set, the
unlocalized split finite sum is exactly the corresponding indicator-localized
sum.
-/
theorem bulkMeasureUnlocalizedSum_eq_indicatorSum_of_support_subset
    (activeInterior : Finset ι)
    (activeBoundaryCharts : Finset BoundaryChart)
    (boundaryPieces : BoundaryChart → Finset BoundaryPiece)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real)
    (hInteriorSupport :
      ∀ i, i ∈ activeInterior →
        Function.support (interiorLocalTerm i) ⊆ interiorBox i)
    (hBoundarySupport :
      ∀ x, x ∈ activeBoundaryCharts →
        ∀ q, q ∈ boundaryPieces x →
          Function.support (boundaryLocalTerm x q) ⊆ boundaryBox x q) :
    bulkMeasureUnlocalizedSum activeInterior activeBoundaryCharts
        boundaryPieces interiorLocalTerm boundaryLocalTerm =
      bulkMeasureIndicatorSum activeInterior activeBoundaryCharts
        boundaryPieces interiorBox boundaryBox interiorLocalTerm
        boundaryLocalTerm := by
  funext y
  have hInterior :
      (Finset.sum activeInterior fun i => interiorLocalTerm i y) =
        Finset.sum activeInterior fun i =>
          (interiorBox i).indicator (interiorLocalTerm i) y := by
    have hFun :
        (Finset.sum activeInterior interiorLocalTerm) =
          Finset.sum activeInterior fun i =>
            (interiorBox i).indicator (interiorLocalTerm i) :=
      finset_sum_eq_indicator_sum_of_support_subset
        activeInterior interiorBox interiorLocalTerm hInteriorSupport
    simpa [Finset.sum_apply] using congrFun hFun y
  have hBoundary :
      (Finset.sum activeBoundaryCharts fun x =>
        Finset.sum (boundaryPieces x) fun q =>
          boundaryLocalTerm x q y) =
        Finset.sum activeBoundaryCharts fun x =>
          Finset.sum (boundaryPieces x) fun q =>
            (boundaryBox x q).indicator (boundaryLocalTerm x q) y := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hFun :
        (Finset.sum (boundaryPieces x) (boundaryLocalTerm x)) =
          Finset.sum (boundaryPieces x) fun q =>
            (boundaryBox x q).indicator (boundaryLocalTerm x q) :=
      finset_sum_eq_indicator_sum_of_support_subset
        (boundaryPieces x) (boundaryBox x) (boundaryLocalTerm x)
        (fun q hq => hBoundarySupport x hx q hq)
    simpa [Finset.sum_apply] using congrFun hFun y
  simp [bulkMeasureUnlocalizedSum, bulkMeasureIndicatorSum,
    bulkMeasureInteriorIndicatorSum, bulkMeasureBoundaryIndicatorSum,
    hInterior, hBoundary]

/-- A.e. version of `bulkMeasureUnlocalizedSum_eq_indicatorSum_of_support_subset`. -/
theorem bulkMeasureUnlocalizedSum_ae_eq_indicatorSum_of_support_subset
    [MeasurableSpace α] {μ : Measure α}
    (activeInterior : Finset ι)
    (activeBoundaryCharts : Finset BoundaryChart)
    (boundaryPieces : BoundaryChart → Finset BoundaryPiece)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real)
    (hInteriorSupport :
      ∀ i, i ∈ activeInterior →
        Function.support (interiorLocalTerm i) ⊆ interiorBox i)
    (hBoundarySupport :
      ∀ x, x ∈ activeBoundaryCharts →
        ∀ q, q ∈ boundaryPieces x →
          Function.support (boundaryLocalTerm x q) ⊆ boundaryBox x q) :
    bulkMeasureUnlocalizedSum activeInterior activeBoundaryCharts
        boundaryPieces interiorLocalTerm boundaryLocalTerm =ᵐ[μ]
      bulkMeasureIndicatorSum activeInterior activeBoundaryCharts
        boundaryPieces interiorBox boundaryBox interiorLocalTerm
        boundaryLocalTerm :=
  Filter.Eventually.of_forall fun y =>
    congrFun
      (bulkMeasureUnlocalizedSum_eq_indicatorSum_of_support_subset
        activeInterior activeBoundaryCharts boundaryPieces interiorBox
        boundaryBox interiorLocalTerm boundaryLocalTerm hInteriorSupport
        hBoundarySupport) y

end PureBulkIndicatorSupport

section CompactSupportConstructor

universe u w i c p a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type i}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {BoundaryChart : Type c} {BoundaryPiece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/--
Compact-support input for the bulk measure localization theorem.

This package turns compact support and support-in-box data into the
`IntegrableOn` and indicator-a.e. fields of
`BulkIntegralPartitionInput.BulkMeasureLocalizationFields`.
-/
structure CompactSupportBulkMeasureData
    (interior : LocalizedInteriorPieces (ι := ι) I ω)
    (boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece)
    (globalBulkIntegral : Real) where
  /-- Global bulk integrand represented by `globalBulkIntegral`. -/
  F : α → Real
  /-- Interior local bulk integrand terms. -/
  interiorLocalTerm : ι → α → Real
  /-- Boundary-chart local bulk integrand terms. -/
  boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real
  /-- Localization box for each interior term. -/
  interiorBox : ι → Set α
  /-- Localization box for each boundary-chart term. -/
  boundaryBox : BoundaryChart → BoundaryPiece → Set α
  /-- The represented global bulk integral is the integral of `F`. -/
  globalBulkIntegral_eq_integral :
    globalBulkIntegral = ∫ y, F y ∂μ
  /-- Measurability of every active interior localization box. -/
  interiorBox_measurable :
    ∀ i, i ∈ interior.active → MeasurableSet (interiorBox i)
  /-- Measurability of every active boundary-piece localization box. -/
  boundaryBox_measurable :
    ∀ x, x ∈ boundary.activeCharts →
      ∀ q, q ∈ boundary.boundaryPieces x → MeasurableSet (boundaryBox x q)
  /-- Compact-support data for every active interior local term. -/
  interiorCompactSupport :
    ∀ i, i ∈ interior.active →
      CompactSupportIntegrabilityData (interiorLocalTerm i)
  /-- Compact-support data for every active boundary local term. -/
  boundaryCompactSupport :
    ∀ x, x ∈ boundary.activeCharts →
      ∀ q, q ∈ boundary.boundaryPieces x →
        CompactSupportIntegrabilityData (boundaryLocalTerm x q)
  /-- Every active interior local term is supported in its localization box. -/
  interior_support_subset_box :
    ∀ i, i ∈ interior.active →
      Function.support (interiorLocalTerm i) ⊆ interiorBox i
  /-- Every active boundary local term is supported in its localization box. -/
  boundary_support_subset_box :
    ∀ x, x ∈ boundary.activeCharts →
      ∀ q, q ∈ boundary.boundaryPieces x →
        Function.support (boundaryLocalTerm x q) ⊆ boundaryBox x q
  /-- Each active interior set integral is the recorded project-local bulk term. -/
  interiorBulkTerm_eq_integral :
    ∀ i, i ∈ interior.active →
      interior.bulkTerm i = ∫ y in interiorBox i, interiorLocalTerm i y ∂μ
  /-- Each active boundary set integral is the recorded project-local bulk term. -/
  boundaryBulkTerm_eq_integral :
    ∀ x, x ∈ boundary.activeCharts →
      ∀ q, q ∈ boundary.boundaryPieces x →
        BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
          ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ
  /--
  A.e. reconstruction of the global integrand as the unlocalized finite sum.
  Indicator insertion is supplied by `toBulkMeasureLocalizationFields`.
  -/
  F_ae_eq_unlocalizedSum :
    F =ᵐ[μ]
      bulkMeasureUnlocalizedSum interior.active boundary.activeCharts
        boundary.boundaryPieces interiorLocalTerm boundaryLocalTerm

namespace CompactSupportBulkMeasureData

variable {interior : LocalizedInteriorPieces (ι := ι) I ω}
variable {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
variable {globalBulkIntegral : Real}

/-- Compact-support data gives the interior `IntegrableOn` fields. -/
theorem interiorIntegrableOn
    (D :
      CompactSupportBulkMeasureData (α := α) (μ := μ) interior boundary
        globalBulkIntegral)
    (i : ι) (hi : i ∈ interior.active) :
    IntegrableOn (D.interiorLocalTerm i) (D.interiorBox i) μ :=
  (D.interiorCompactSupport i hi).integrableOn (D.interiorBox i)

/-- Compact-support data gives the boundary `IntegrableOn` fields. -/
theorem boundaryIntegrableOn
    (D :
      CompactSupportBulkMeasureData (α := α) (μ := μ) interior boundary
        globalBulkIntegral)
    (x : BoundaryChart) (hx : x ∈ boundary.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ boundary.boundaryPieces x) :
    IntegrableOn (D.boundaryLocalTerm x q) (D.boundaryBox x q) μ :=
  (D.boundaryCompactSupport x hx q hq).integrableOn (D.boundaryBox x q)

omit [OpensMeasurableSpace α] [T2Space α] [IsFiniteMeasureOnCompacts μ] in
/--
Support containment in the selected boxes upgrades the unlocalized a.e.
reconstruction to the indicator-localized one required by the measure package.
-/
theorem F_ae_eq_indicatorSum
    (D :
      CompactSupportBulkMeasureData (α := α) (μ := μ) interior boundary
        globalBulkIntegral) :
    D.F =ᵐ[μ]
      bulkMeasureIndicatorSum interior.active boundary.activeCharts
        boundary.boundaryPieces D.interiorBox D.boundaryBox
        D.interiorLocalTerm D.boundaryLocalTerm :=
  D.F_ae_eq_unlocalizedSum.trans
    (bulkMeasureUnlocalizedSum_ae_eq_indicatorSum_of_support_subset
      (μ := μ) interior.active boundary.activeCharts
      boundary.boundaryPieces D.interiorBox D.boundaryBox
      D.interiorLocalTerm D.boundaryLocalTerm
      D.interior_support_subset_box D.boundary_support_subset_box)

/--
Constructor for `BulkIntegralPartitionInput.BulkMeasureLocalizationFields`
from compact support plus support-localization data.
-/
def toBulkMeasureLocalizationFields
    (D :
      CompactSupportBulkMeasureData (α := α) (μ := μ) interior boundary
        globalBulkIntegral) :
    BulkIntegralPartitionInput.BulkMeasureLocalizationFields
      (α := α) μ interior boundary globalBulkIntegral where
  F := D.F
  interiorLocalTerm := D.interiorLocalTerm
  boundaryLocalTerm := D.boundaryLocalTerm
  interiorBox := D.interiorBox
  boundaryBox := D.boundaryBox
  globalBulkIntegral_eq_integral := D.globalBulkIntegral_eq_integral
  interiorBox_measurable := D.interiorBox_measurable
  boundaryBox_measurable := D.boundaryBox_measurable
  interiorIntegrableOn := D.interiorIntegrableOn
  boundaryIntegrableOn := D.boundaryIntegrableOn
  interiorBulkTerm_eq_integral := D.interiorBulkTerm_eq_integral
  boundaryBulkTerm_eq_integral := D.boundaryBulkTerm_eq_integral
  F_ae_eq_indicatorSum := D.F_ae_eq_indicatorSum

/-- The compact-support constructor supplies bulk localization. -/
theorem bulkIntegralLocalizes
    (D :
      CompactSupportBulkMeasureData (α := α) (μ := μ) interior boundary
        globalBulkIntegral) :
    globalBulkIntegral =
      (Finset.sum interior.active fun i => interior.bulkTerm i) +
        BoundaryPieceFamilyInput.boundaryBulkSum boundary :=
  D.toBulkMeasureLocalizationFields.bulkIntegralLocalizes

/-- The compact-support constructor can be consumed as a partition input. -/
def toBulkIntegralPartitionInput
    (D :
      CompactSupportBulkMeasureData (α := α) (μ := μ) interior boundary
        globalBulkIntegral) :
    BulkIntegralPartitionInput (ι := ι)
      (I := I) (ω := ω) (BoundaryChart := BoundaryChart)
      (BoundaryPiece := BoundaryPiece) :=
  D.toBulkMeasureLocalizationFields.toBulkIntegralPartitionInput

@[simp]
theorem toBulkMeasureLocalizationFields_F
    (D :
      CompactSupportBulkMeasureData (α := α) (μ := μ) interior boundary
        globalBulkIntegral) :
    D.toBulkMeasureLocalizationFields.F = D.F :=
  rfl

@[simp]
theorem toBulkMeasureLocalizationFields_F_ae_eq_indicatorSum
    (D :
      CompactSupportBulkMeasureData (α := α) (μ := μ) interior boundary
        globalBulkIntegral) :
    D.toBulkMeasureLocalizationFields.F_ae_eq_indicatorSum =
      D.F_ae_eq_indicatorSum :=
  rfl

@[simp]
theorem toBulkIntegralPartitionInput_globalBulkIntegral
    (D :
      CompactSupportBulkMeasureData (α := α) (μ := μ) interior boundary
        globalBulkIntegral) :
    D.toBulkIntegralPartitionInput.globalBulkIntegral = globalBulkIntegral :=
  rfl

end CompactSupportBulkMeasureData

namespace BulkIntegralPartitionInput

namespace BulkMeasureLocalizationFields

variable {interior : LocalizedInteriorPieces (ι := ι) I ω}
variable {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
variable {globalBulkIntegral : Real}

/--
Clean constructor spelling for downstream code that wants the final measure
field package directly.
-/
def ofCompactSupport
    (D :
      CompactSupportBulkMeasureData (α := α) (μ := μ) interior boundary
        globalBulkIntegral) :
    BulkMeasureLocalizationFields (α := α) μ interior boundary
      globalBulkIntegral :=
  D.toBulkMeasureLocalizationFields

@[simp]
theorem ofCompactSupport_F
    (D :
      CompactSupportBulkMeasureData (α := α) (μ := μ) interior boundary
        globalBulkIntegral) :
    (ofCompactSupport D).F = D.F :=
  rfl

end BulkMeasureLocalizationFields

end BulkIntegralPartitionInput

end CompactSupportConstructor

end Stokes

end
