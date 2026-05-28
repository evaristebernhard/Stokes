import Stokes.Global.BulkMeasureFromPartition

/-!
# Bulk compact-support integrability to measure localization

This file connects the compact-support integrability wrappers to the bulk
measure-localization constructors.

The genuinely geometric and analytic alignments remain explicit: callers still
provide the scalar local terms, their localization boxes, support-in-box
statements, set-integral identifications, and global finite-sum reconstruction.
The constructors here only remove the repetitive step of turning compact
support/continuity data for every local term into the
`CompactSupportBulkMeasureData` and `BulkMeasureFromPartitionData` fields.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkCompactSupportIntegrabilityToMeasure

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
Compact-support/continuity data for the scalar local bulk terms.

This is the local-term integrability constructor input.  It is deliberately
independent of localization boxes: support-in-box and integral-identification
fields are supplied later by `toCompactSupportBulkMeasureData` or
`toBulkMeasureFromPartitionData`.
-/
structure BulkLocalTermCompactSupportData
    (interior : LocalizedInteriorPieces (ι := ι) I ω)
    (boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real) where
  /-- Compact support carrier for each active interior scalar term. -/
  interiorSupportSet : ι → Set α
  /-- Compact support carrier for each active boundary scalar term. -/
  boundarySupportSet : BoundaryChart → BoundaryPiece → Set α
  /-- Active interior support carriers are compact. -/
  interior_isCompact :
    ∀ i, i ∈ interior.active → IsCompact (interiorSupportSet i)
  /-- Active boundary support carriers are compact. -/
  boundary_isCompact :
    ∀ x, x ∈ boundary.activeCharts →
      ∀ q, q ∈ boundary.boundaryPieces x →
        IsCompact (boundarySupportSet x q)
  /-- Active interior scalar terms are continuous on their support carriers. -/
  interior_continuousOn :
    ∀ i, i ∈ interior.active →
      ContinuousOn (interiorLocalTerm i) (interiorSupportSet i)
  /-- Active boundary scalar terms are continuous on their support carriers. -/
  boundary_continuousOn :
    ∀ x, x ∈ boundary.activeCharts →
      ∀ q, q ∈ boundary.boundaryPieces x →
        ContinuousOn (boundaryLocalTerm x q) (boundarySupportSet x q)
  /-- Active interior scalar terms have algebraic support in the carrier. -/
  interior_support_subset :
    ∀ i, i ∈ interior.active →
      Function.support (interiorLocalTerm i) ⊆ interiorSupportSet i
  /-- Active boundary scalar terms have algebraic support in the carrier. -/
  boundary_support_subset :
    ∀ x, x ∈ boundary.activeCharts →
      ∀ q, q ∈ boundary.boundaryPieces x →
        Function.support (boundaryLocalTerm x q) ⊆ boundarySupportSet x q

namespace BulkLocalTermCompactSupportData

variable {interior : LocalizedInteriorPieces (ι := ι) I ω}
variable {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
variable {interiorLocalTerm : ι → α → Real}
variable {boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real}

/-- Interior compact-support wrapper supplied by the local-term data. -/
def interiorCompactSupport
    (D :
      BulkLocalTermCompactSupportData (α := α) interior boundary
        interiorLocalTerm boundaryLocalTerm)
    (i : ι) (hi : i ∈ interior.active) :
    CompactSupportIntegrabilityData (interiorLocalTerm i) :=
  CompactSupportIntegrabilityData.of (D.interiorSupportSet i)
    (D.interior_isCompact i hi) (D.interior_continuousOn i hi)
    (D.interior_support_subset i hi)

/-- Boundary compact-support wrapper supplied by the local-term data. -/
def boundaryCompactSupport
    (D :
      BulkLocalTermCompactSupportData (α := α) interior boundary
        interiorLocalTerm boundaryLocalTerm)
    (x : BoundaryChart) (hx : x ∈ boundary.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ boundary.boundaryPieces x) :
    CompactSupportIntegrabilityData (boundaryLocalTerm x q) :=
  CompactSupportIntegrabilityData.of (D.boundarySupportSet x q)
    (D.boundary_isCompact x hx q hq) (D.boundary_continuousOn x hx q hq)
    (D.boundary_support_subset x hx q hq)

/-- Local compact support gives integrability of an interior scalar term on any box. -/
theorem interiorIntegrableOn
    (D :
      BulkLocalTermCompactSupportData (α := α) interior boundary
        interiorLocalTerm boundaryLocalTerm)
    (interiorBox : ι → Set α)
    (i : ι) (hi : i ∈ interior.active) :
    IntegrableOn (interiorLocalTerm i) (interiorBox i) μ :=
  (D.interiorCompactSupport i hi).integrableOn (interiorBox i)

/-- Local compact support gives integrability of a boundary scalar term on any box. -/
theorem boundaryIntegrableOn
    (D :
      BulkLocalTermCompactSupportData (α := α) interior boundary
        interiorLocalTerm boundaryLocalTerm)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (x : BoundaryChart) (hx : x ∈ boundary.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ boundary.boundaryPieces x) :
    IntegrableOn (boundaryLocalTerm x q) (boundaryBox x q) μ :=
  (D.boundaryCompactSupport x hx q hq).integrableOn (boundaryBox x q)

/--
Build `CompactSupportBulkMeasureData` from local compact-support data.

All non-integrability alignments remain explicit fields.
-/
def toCompactSupportBulkMeasureData
    (D :
      BulkLocalTermCompactSupportData (α := α) interior boundary
        interiorLocalTerm boundaryLocalTerm)
    (globalBulkIntegral : Real)
    (F : α → Real)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral = ∫ y, F y ∂μ)
    (interiorBox_measurable :
      ∀ i, i ∈ interior.active → MeasurableSet (interiorBox i))
    (boundaryBox_measurable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          MeasurableSet (boundaryBox x q))
    (interior_support_subset_box :
      ∀ i, i ∈ interior.active →
        Function.support (interiorLocalTerm i) ⊆ interiorBox i)
    (boundary_support_subset_box :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          Function.support (boundaryLocalTerm x q) ⊆ boundaryBox x q)
    (interiorBulkTerm_eq_integral :
      ∀ i, i ∈ interior.active →
        interior.bulkTerm i = ∫ y in interiorBox i, interiorLocalTerm i y ∂μ)
    (boundaryBulkTerm_eq_integral :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ)
    (F_ae_eq_unlocalizedSum :
      F =ᵐ[μ]
        bulkMeasureUnlocalizedSum interior.active boundary.activeCharts
          boundary.boundaryPieces interiorLocalTerm boundaryLocalTerm) :
    CompactSupportBulkMeasureData (α := α) (μ := μ) interior boundary
      globalBulkIntegral where
  F := F
  interiorLocalTerm := interiorLocalTerm
  boundaryLocalTerm := boundaryLocalTerm
  interiorBox := interiorBox
  boundaryBox := boundaryBox
  globalBulkIntegral_eq_integral := globalBulkIntegral_eq_integral
  interiorBox_measurable := interiorBox_measurable
  boundaryBox_measurable := boundaryBox_measurable
  interiorCompactSupport := D.interiorCompactSupport
  boundaryCompactSupport := D.boundaryCompactSupport
  interior_support_subset_box := interior_support_subset_box
  boundary_support_subset_box := boundary_support_subset_box
  interiorBulkTerm_eq_integral := interiorBulkTerm_eq_integral
  boundaryBulkTerm_eq_integral := boundaryBulkTerm_eq_integral
  F_ae_eq_unlocalizedSum := F_ae_eq_unlocalizedSum

/-- Directly expose the pure bulk measure-localization fields. -/
def toBulkMeasureLocalizationFields
    (D :
      BulkLocalTermCompactSupportData (α := α) interior boundary
        interiorLocalTerm boundaryLocalTerm)
    (globalBulkIntegral : Real)
    (F : α → Real)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral = ∫ y, F y ∂μ)
    (interiorBox_measurable :
      ∀ i, i ∈ interior.active → MeasurableSet (interiorBox i))
    (boundaryBox_measurable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          MeasurableSet (boundaryBox x q))
    (interior_support_subset_box :
      ∀ i, i ∈ interior.active →
        Function.support (interiorLocalTerm i) ⊆ interiorBox i)
    (boundary_support_subset_box :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          Function.support (boundaryLocalTerm x q) ⊆ boundaryBox x q)
    (interiorBulkTerm_eq_integral :
      ∀ i, i ∈ interior.active →
        interior.bulkTerm i = ∫ y in interiorBox i, interiorLocalTerm i y ∂μ)
    (boundaryBulkTerm_eq_integral :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ)
    (F_ae_eq_unlocalizedSum :
      F =ᵐ[μ]
        bulkMeasureUnlocalizedSum interior.active boundary.activeCharts
          boundary.boundaryPieces interiorLocalTerm boundaryLocalTerm) :
    BulkIntegralPartitionInput.BulkMeasureLocalizationFields
      (α := α) μ interior boundary globalBulkIntegral :=
  (D.toCompactSupportBulkMeasureData globalBulkIntegral F interiorBox
    boundaryBox globalBulkIntegral_eq_integral interiorBox_measurable
    boundaryBox_measurable interior_support_subset_box
    boundary_support_subset_box interiorBulkTerm_eq_integral
    boundaryBulkTerm_eq_integral F_ae_eq_unlocalizedSum)
      |>.toBulkMeasureLocalizationFields

end BulkLocalTermCompactSupportData

section SelectedPartition

variable {P : SelectedBoxPartitionOfUnity I ω}
variable {boundary : BoundaryPieceFamilyInput I ω M BoundaryPiece}
variable {globalBulkIntegral : Real}
variable {localized : LocalizedInteriorM8Fields I ω P}
variable {interiorLocalTerm : M → α → Real}
variable {boundaryLocalTerm : M → BoundaryPiece → α → Real}

namespace BulkLocalTermCompactSupportData

/--
Build the selected-partition-facing bulk measure package from local
compact-support data.

The active-set equalities and all term/support/integral alignments are still
explicit.  This constructor only supplies the compact-support integrability
families used by `BulkMeasureFromPartitionData`.
-/
def toBulkMeasureFromPartitionData
    (D :
      BulkLocalTermCompactSupportData (α := α)
        localized.localizedInterior boundary interiorLocalTerm
        boundaryLocalTerm)
    (boundary_active : boundary.activeCharts = P.active)
    (F : α → Real)
    (interiorBox : M → Set α)
    (boundaryBox : M → BoundaryPiece → Set α)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral = ∫ y, F y ∂μ)
    (interiorBox_measurable :
      ∀ i, i ∈ P.active → MeasurableSet (interiorBox i))
    (boundaryBox_measurable :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x →
          MeasurableSet (boundaryBox x q))
    (interior_eq_zero_off_box :
      ∀ i, i ∈ P.active →
        ∀ y, y ∉ interiorBox i → interiorLocalTerm i y = 0)
    (boundary_eq_zero_off_box :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x →
          ∀ y, y ∉ boundaryBox x q → boundaryLocalTerm x q y = 0)
    (interiorBulkTerm_eq_integral :
      ∀ i, i ∈ P.active →
        localized.localizedInterior.bulkTerm i =
          ∫ y in interiorBox i, interiorLocalTerm i y ∂μ)
    (boundaryBulkTerm_eq_integral :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x →
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ)
    (F_eq_partitionUnlocalizedSum :
      ∀ y,
        F y =
          bulkMeasureUnlocalizedSum P.active P.active
            boundary.boundaryPieces interiorLocalTerm boundaryLocalTerm y) :
    BulkMeasureFromPartitionData (α := α) (μ := μ) P boundary
      globalBulkIntegral where
  localized := localized
  boundary_active := boundary_active
  F := F
  interiorLocalTerm := interiorLocalTerm
  boundaryLocalTerm := boundaryLocalTerm
  interiorBox := interiorBox
  boundaryBox := boundaryBox
  globalBulkIntegral_eq_integral := globalBulkIntegral_eq_integral
  interiorBox_measurable := interiorBox_measurable
  boundaryBox_measurable := boundaryBox_measurable
  interiorCompactSupport := by
    intro i hi
    exact D.interiorCompactSupport i
      (by simpa [localized.localized_active] using hi)
  boundaryCompactSupport := by
    intro x hx q hq
    exact D.boundaryCompactSupport x
      (by simpa [boundary_active] using hx) q hq
  interior_eq_zero_off_box := interior_eq_zero_off_box
  boundary_eq_zero_off_box := boundary_eq_zero_off_box
  interiorBulkTerm_eq_integral := interiorBulkTerm_eq_integral
  boundaryBulkTerm_eq_integral := boundaryBulkTerm_eq_integral
  F_eq_partitionUnlocalizedSum := F_eq_partitionUnlocalizedSum

/-- Selected-partition constructor followed by the compact-support bulk package. -/
def toSelectedCompactSupportBulkMeasureData
    (D :
      BulkLocalTermCompactSupportData (α := α)
        localized.localizedInterior boundary interiorLocalTerm
        boundaryLocalTerm)
    (boundary_active : boundary.activeCharts = P.active)
    (F : α → Real)
    (interiorBox : M → Set α)
    (boundaryBox : M → BoundaryPiece → Set α)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral = ∫ y, F y ∂μ)
    (interiorBox_measurable :
      ∀ i, i ∈ P.active → MeasurableSet (interiorBox i))
    (boundaryBox_measurable :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x →
          MeasurableSet (boundaryBox x q))
    (interior_eq_zero_off_box :
      ∀ i, i ∈ P.active →
        ∀ y, y ∉ interiorBox i → interiorLocalTerm i y = 0)
    (boundary_eq_zero_off_box :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x →
          ∀ y, y ∉ boundaryBox x q → boundaryLocalTerm x q y = 0)
    (interiorBulkTerm_eq_integral :
      ∀ i, i ∈ P.active →
        localized.localizedInterior.bulkTerm i =
          ∫ y in interiorBox i, interiorLocalTerm i y ∂μ)
    (boundaryBulkTerm_eq_integral :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x →
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ)
    (F_eq_partitionUnlocalizedSum :
      ∀ y,
        F y =
          bulkMeasureUnlocalizedSum P.active P.active
            boundary.boundaryPieces interiorLocalTerm boundaryLocalTerm y) :
    CompactSupportBulkMeasureData (α := α) (μ := μ)
      localized.localizedInterior boundary globalBulkIntegral :=
  (D.toBulkMeasureFromPartitionData
    (P := P) (localized := localized)
    (boundary := boundary) (globalBulkIntegral := globalBulkIntegral)
    boundary_active F interiorBox boundaryBox globalBulkIntegral_eq_integral
    interiorBox_measurable boundaryBox_measurable interior_eq_zero_off_box
    boundary_eq_zero_off_box interiorBulkTerm_eq_integral
    boundaryBulkTerm_eq_integral F_eq_partitionUnlocalizedSum)
      |>.toCompactSupportBulkMeasureData

end BulkLocalTermCompactSupportData

end SelectedPartition

end BulkCompactSupportIntegrabilityToMeasure

end Stokes

end
