import Stokes.Global.CompactSupportBulkMeasure
import Stokes.Global.LocalizedInteriorConstructors

/-!
# Bulk measure localization from a selected partition

This file adds a selected-partition-facing entry point for the compact-support
bulk measure package.

`CompactSupportBulkMeasureData` is intentionally measure-theoretic, but its
callers in the global Stokes pipeline usually start from a selected finite
partition.  In that setting it is more natural to record:

* the localized interior family aligned with the selected partition;
* the boundary family aligned with the same active chart set;
* pointwise reconstruction of the scalar bulk integrand as the finite local
  sum;
* vanishing of each local scalar term outside its selected box.

The constructor below turns those inputs into the existing
`CompactSupportBulkMeasureData`, supplying the a.e. reconstruction and support
containment fields automatically.  The genuinely analytic data, such as set
integral identities and compact-support integrability, remains explicit.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section PureSupport

universe a v

variable {α : Type a} {β : Type v} [Zero β]

/--
Pointwise vanishing outside a set gives algebraic support containment.

This is the small shape callers usually have after choosing a chart box:
instead of directly proving `Function.support f ⊆ s`, they prove that the
local scalar representative is zero off the selected box.
-/
theorem support_subset_of_eq_zero_off {s : Set α} {f : α → β}
    (hzero : ∀ y, y ∉ s → f y = 0) :
    Function.support f ⊆ s := by
  intro y hy
  by_contra hys
  exact hy (hzero y hys)

end PureSupport

section SelectedPartitionBulkMeasure

universe u w p a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {BoundaryPiece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/--
Selected-partition-facing input for compact-support bulk localization.

The support and a.e. fields expected by `CompactSupportBulkMeasureData` are
replaced by more geometric hypotheses:

* each active local term vanishes outside its selected box;
* the represented scalar bulk integrand is pointwise the unlocalized finite
  sum over the selected partition.
-/
structure BulkMeasureFromPartitionData
    (P : SelectedBoxPartitionOfUnity I ω)
    (boundary : BoundaryPieceFamilyInput I ω M BoundaryPiece)
    (globalBulkIntegral : Real) where
  /-- Localized interior pieces aligned with the selected partition. -/
  localized : LocalizedInteriorM8Fields I ω P
  /-- Boundary bulk pieces use the same active chart set as the partition. -/
  boundary_active : boundary.activeCharts = P.active
  /-- Global scalar bulk integrand represented by `globalBulkIntegral`. -/
  F : α → Real
  /-- Interior local scalar bulk integrands. -/
  interiorLocalTerm : M → α → Real
  /-- Boundary local scalar bulk integrands. -/
  boundaryLocalTerm : M → BoundaryPiece → α → Real
  /-- Localization box for each selected interior term. -/
  interiorBox : M → Set α
  /-- Localization box for each selected boundary term. -/
  boundaryBox : M → BoundaryPiece → Set α
  /-- The represented global bulk integral is the integral of `F`. -/
  globalBulkIntegral_eq_integral :
    globalBulkIntegral = ∫ y, F y ∂μ
  /-- Measurability of every selected interior localization box. -/
  interiorBox_measurable :
    ∀ i, i ∈ P.active → MeasurableSet (interiorBox i)
  /-- Measurability of every selected boundary-piece localization box. -/
  boundaryBox_measurable :
    ∀ x, x ∈ P.active →
      ∀ q, q ∈ boundary.boundaryPieces x → MeasurableSet (boundaryBox x q)
  /-- Compact-support data for every selected interior local term. -/
  interiorCompactSupport :
    ∀ i, i ∈ P.active →
      CompactSupportIntegrabilityData (interiorLocalTerm i)
  /-- Compact-support data for every selected boundary local term. -/
  boundaryCompactSupport :
    ∀ x, x ∈ P.active →
      ∀ q, q ∈ boundary.boundaryPieces x →
        CompactSupportIntegrabilityData (boundaryLocalTerm x q)
  /-- Each selected interior local term vanishes outside its selected box. -/
  interior_eq_zero_off_box :
    ∀ i, i ∈ P.active →
      ∀ y, y ∉ interiorBox i → interiorLocalTerm i y = 0
  /-- Each selected boundary local term vanishes outside its selected box. -/
  boundary_eq_zero_off_box :
    ∀ x, x ∈ P.active →
      ∀ q, q ∈ boundary.boundaryPieces x →
        ∀ y, y ∉ boundaryBox x q → boundaryLocalTerm x q y = 0
  /-- Each selected interior set integral is the recorded local bulk term. -/
  interiorBulkTerm_eq_integral :
    ∀ i, i ∈ P.active →
      localized.localizedInterior.bulkTerm i =
        ∫ y in interiorBox i, interiorLocalTerm i y ∂μ
  /-- Each selected boundary set integral is the recorded local bulk term. -/
  boundaryBulkTerm_eq_integral :
    ∀ x, x ∈ P.active →
      ∀ q, q ∈ boundary.boundaryPieces x →
        BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
          ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ
  /--
  Pointwise reconstruction of the scalar bulk integrand as the selected
  unlocalized finite sum.  The a.e. field is derived from this.
  -/
  F_eq_partitionUnlocalizedSum :
    ∀ y,
      F y =
        bulkMeasureUnlocalizedSum P.active P.active
          boundary.boundaryPieces interiorLocalTerm boundaryLocalTerm y

namespace BulkMeasureFromPartitionData

variable {P : SelectedBoxPartitionOfUnity I ω}
variable {boundary : BoundaryPieceFamilyInput I ω M BoundaryPiece}
variable {globalBulkIntegral : Real}

omit [OpensMeasurableSpace α] [T2Space α] [IsFiniteMeasureOnCompacts μ] in
/-- Selected interior vanishing gives the support containment field. -/
theorem interior_support_subset_box
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ) P boundary
        globalBulkIntegral)
    (i : M) (hi : i ∈ P.active) :
    Function.support (D.interiorLocalTerm i) ⊆ D.interiorBox i :=
  support_subset_of_eq_zero_off (D.interior_eq_zero_off_box i hi)

omit [OpensMeasurableSpace α] [T2Space α] [IsFiniteMeasureOnCompacts μ] in
/-- Selected boundary vanishing gives the support containment field. -/
theorem boundary_support_subset_box
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ) P boundary
        globalBulkIntegral)
    (x : M) (hx : x ∈ P.active)
    (q : BoundaryPiece) (hq : q ∈ boundary.boundaryPieces x) :
    Function.support (D.boundaryLocalTerm x q) ⊆ D.boundaryBox x q :=
  support_subset_of_eq_zero_off (D.boundary_eq_zero_off_box x hx q hq)

omit [OpensMeasurableSpace α] [T2Space α] [IsFiniteMeasureOnCompacts μ] in
/--
The selected-partition pointwise reconstruction, rewritten as the a.e.
unlocalized reconstruction expected by `CompactSupportBulkMeasureData`.
-/
theorem F_ae_eq_unlocalizedSum
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ) P boundary
        globalBulkIntegral) :
    D.F =ᵐ[μ]
      bulkMeasureUnlocalizedSum D.localized.localizedInterior.active
        boundary.activeCharts boundary.boundaryPieces
        D.interiorLocalTerm D.boundaryLocalTerm :=
  Filter.Eventually.of_forall fun y => by
    simpa [D.localized.localized_active, D.boundary_active] using
      D.F_eq_partitionUnlocalizedSum y

/--
Forget the selected-partition-facing wrapper and expose the compact-support
bulk localization package.
-/
def toCompactSupportBulkMeasureData
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ) P boundary
        globalBulkIntegral) :
    CompactSupportBulkMeasureData (α := α) (μ := μ)
      D.localized.localizedInterior boundary globalBulkIntegral where
  F := D.F
  interiorLocalTerm := D.interiorLocalTerm
  boundaryLocalTerm := D.boundaryLocalTerm
  interiorBox := D.interiorBox
  boundaryBox := D.boundaryBox
  globalBulkIntegral_eq_integral := D.globalBulkIntegral_eq_integral
  interiorBox_measurable := by
    intro i hi
    exact D.interiorBox_measurable i
      (by simpa [D.localized.localized_active] using hi)
  boundaryBox_measurable := by
    intro x hx q hq
    exact D.boundaryBox_measurable x
      (by simpa [D.boundary_active] using hx) q hq
  interiorCompactSupport := by
    intro i hi
    exact D.interiorCompactSupport i
      (by simpa [D.localized.localized_active] using hi)
  boundaryCompactSupport := by
    intro x hx q hq
    exact D.boundaryCompactSupport x
      (by simpa [D.boundary_active] using hx) q hq
  interior_support_subset_box := by
    intro i hi
    exact D.interior_support_subset_box i
      (by simpa [D.localized.localized_active] using hi)
  boundary_support_subset_box := by
    intro x hx q hq
    exact D.boundary_support_subset_box x
      (by simpa [D.boundary_active] using hx) q hq
  interiorBulkTerm_eq_integral := by
    intro i hi
    exact D.interiorBulkTerm_eq_integral i
      (by simpa [D.localized.localized_active] using hi)
  boundaryBulkTerm_eq_integral := by
    intro x hx q hq
    exact D.boundaryBulkTerm_eq_integral x
      (by simpa [D.boundary_active] using hx) q hq
  F_ae_eq_unlocalizedSum := D.F_ae_eq_unlocalizedSum

/-- Direct constructor for the pure bulk measure-localization fields. -/
def toBulkMeasureLocalizationFields
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ) P boundary
        globalBulkIntegral) :
    BulkIntegralPartitionInput.BulkMeasureLocalizationFields
      (α := α) μ D.localized.localizedInterior boundary globalBulkIntegral :=
  D.toCompactSupportBulkMeasureData.toBulkMeasureLocalizationFields

/-- The selected-partition-facing package supplies bulk localization. -/
theorem bulkIntegralLocalizes
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ) P boundary
        globalBulkIntegral) :
    globalBulkIntegral =
      (Finset.sum D.localized.localizedInterior.active fun i =>
        D.localized.localizedInterior.bulkTerm i) +
        BoundaryPieceFamilyInput.boundaryBulkSum boundary :=
  D.toCompactSupportBulkMeasureData.bulkIntegralLocalizes

/--
Bulk localization rewritten over the selected partition active set.

This is often the shape consumed by M8 adapters after the boundary family has
also been aligned with the selected partition.
-/
theorem bulkIntegralLocalizes_selected
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ) P boundary
        globalBulkIntegral) :
    globalBulkIntegral =
      (Finset.sum P.active fun i =>
        D.localized.localizedInterior.bulkTerm i) +
        Finset.sum P.active fun x =>
          Finset.sum (boundary.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q := by
  simpa [D.localized.localized_active, D.boundary_active,
    BoundaryPieceFamilyInput.boundaryBulkSum] using D.bulkIntegralLocalizes

omit [OpensMeasurableSpace α] [T2Space α] [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem toCompactSupportBulkMeasureData_F
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ) P boundary
        globalBulkIntegral) :
    D.toCompactSupportBulkMeasureData.F = D.F :=
  rfl

@[simp]
theorem toBulkMeasureLocalizationFields_F
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ) P boundary
        globalBulkIntegral) :
    D.toBulkMeasureLocalizationFields.F = D.F :=
  rfl

@[simp]
theorem toBulkMeasureLocalizationFields_globalBulkIntegral
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ) P boundary
        globalBulkIntegral) :
    D.toBulkMeasureLocalizationFields.toBulkIntegralPartitionInput.globalBulkIntegral =
      globalBulkIntegral :=
  rfl

end BulkMeasureFromPartitionData

namespace SelectedBoxPartitionOfUnity

variable {P : SelectedBoxPartitionOfUnity I ω}
variable {boundary : BoundaryPieceFamilyInput I ω M BoundaryPiece}
variable {globalBulkIntegral : Real}

/--
Selected-partition constructor spelling for `BulkMeasureFromPartitionData`.

This is intentionally just a stable name around the structure constructor; it
lets downstream code avoid depending on field order.
-/
def bulkMeasureFromPartitionData
    (localized : LocalizedInteriorM8Fields I ω P)
    (boundary_active : boundary.activeCharts = P.active)
    (F : α → Real)
    (interiorLocalTerm : M → α → Real)
    (boundaryLocalTerm : M → BoundaryPiece → α → Real)
    (interiorBox : M → Set α)
    (boundaryBox : M → BoundaryPiece → Set α)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral = ∫ y, F y ∂μ)
    (interiorBox_measurable :
      ∀ i, i ∈ P.active → MeasurableSet (interiorBox i))
    (boundaryBox_measurable :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x → MeasurableSet (boundaryBox x q))
    (interiorCompactSupport :
      ∀ i, i ∈ P.active →
        CompactSupportIntegrabilityData (interiorLocalTerm i))
    (boundaryCompactSupport :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x →
          CompactSupportIntegrabilityData (boundaryLocalTerm x q))
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
  interiorCompactSupport := interiorCompactSupport
  boundaryCompactSupport := boundaryCompactSupport
  interior_eq_zero_off_box := interior_eq_zero_off_box
  boundary_eq_zero_off_box := boundary_eq_zero_off_box
  interiorBulkTerm_eq_integral := interiorBulkTerm_eq_integral
  boundaryBulkTerm_eq_integral := boundaryBulkTerm_eq_integral
  F_eq_partitionUnlocalizedSum := F_eq_partitionUnlocalizedSum

/--
Specialization where the global scalar bulk integrand is literally the finite
unlocalized selected-partition sum, so no reconstruction equality is needed.
-/
def bulkMeasureFromLiteralPartitionSum
    (localized : LocalizedInteriorM8Fields I ω P)
    (boundary_active : boundary.activeCharts = P.active)
    (interiorLocalTerm : M → α → Real)
    (boundaryLocalTerm : M → BoundaryPiece → α → Real)
    (interiorBox : M → Set α)
    (boundaryBox : M → BoundaryPiece → Set α)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral =
        ∫ y,
          bulkMeasureUnlocalizedSum P.active P.active
            boundary.boundaryPieces interiorLocalTerm boundaryLocalTerm y ∂μ)
    (interiorBox_measurable :
      ∀ i, i ∈ P.active → MeasurableSet (interiorBox i))
    (boundaryBox_measurable :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x → MeasurableSet (boundaryBox x q))
    (interiorCompactSupport :
      ∀ i, i ∈ P.active →
        CompactSupportIntegrabilityData (interiorLocalTerm i))
    (boundaryCompactSupport :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x →
          CompactSupportIntegrabilityData (boundaryLocalTerm x q))
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
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ) :
    BulkMeasureFromPartitionData (α := α) (μ := μ) P boundary
      globalBulkIntegral :=
  bulkMeasureFromPartitionData
    (P := P) (boundary := boundary) (globalBulkIntegral := globalBulkIntegral)
    localized boundary_active
    (bulkMeasureUnlocalizedSum P.active P.active boundary.boundaryPieces
      interiorLocalTerm boundaryLocalTerm)
    interiorLocalTerm boundaryLocalTerm interiorBox boundaryBox
    globalBulkIntegral_eq_integral interiorBox_measurable
    boundaryBox_measurable interiorCompactSupport boundaryCompactSupport
    interior_eq_zero_off_box boundary_eq_zero_off_box
    interiorBulkTerm_eq_integral boundaryBulkTerm_eq_integral
    (fun _ => rfl)

end SelectedBoxPartitionOfUnity

end SelectedPartitionBulkMeasure

end Stokes

end
