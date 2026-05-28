import Stokes.Global.CompactSupportBulkMeasureFromIndicators
import Stokes.Global.NaturalCompactSupportMeasureConstructor

/-!
# Bulk measure localization from derivative partition identities

This file is the L6 bridge for the compact-support Stokes route.  The
mathematical input is the derivative-partition reconstruction one expects from
the partition-of-unity proof:

* a represented scalar bulk integrand `F`;
* local scalar bulk integrands on the selected interior and boundary boxes;
* an a.e. equality saying that `F` is the finite sum of those
  indicator-localized local derivative terms.

The output is the existing `BulkIntegralPartitionInput`, hence the
`bulkIntegralLocalizes` equality consumed by the global/M8 assembly.  The
theorems below deliberately do not introduce a new global ext-derivative
definition; they take the exact a.e. indicator reconstruction hypothesis and
feed the already-proved measure constructor.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkMeasureFromDerivativePartition

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

namespace BulkIntegralPartitionInput

namespace BulkMeasureLocalizationFields

variable {interior : LocalizedInteriorPieces (ι := ι) I ω}
variable {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
variable {globalBulkIntegral : Real}

/--
Build the bulk measure-localization fields directly from an a.e.
indicator-localized derivative partition identity.

This is the exact L5-to-L6 handoff: once the exterior-derivative partition
argument has produced `F =ᵐ[μ] bulkMeasureIndicatorSum ...`, the remaining
hypotheses are the usual measurability, integrability, and local set-integral
identifications.
-/
def ofDerivativePartitionAEIndicator
    (F : α → Real)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (hglobal : globalBulkIntegral = ∫ y, F y ∂μ)
    (hInteriorMeasurable :
      ∀ i, i ∈ interior.active → MeasurableSet (interiorBox i))
    (hBoundaryMeasurable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x → MeasurableSet (boundaryBox x q))
    (hInteriorIntegrable :
      ∀ i, i ∈ interior.active →
        IntegrableOn (interiorLocalTerm i) (interiorBox i) μ)
    (hBoundaryIntegrable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          IntegrableOn (boundaryLocalTerm x q) (boundaryBox x q) μ)
    (hInteriorBulkTerm :
      ∀ i, i ∈ interior.active →
        interior.bulkTerm i = ∫ y in interiorBox i, interiorLocalTerm i y ∂μ)
    (hBoundaryBulkTerm :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ)
    (hF :
      F =ᵐ[μ]
        bulkMeasureIndicatorSum interior.active boundary.activeCharts
          boundary.boundaryPieces interiorBox boundaryBox interiorLocalTerm
          boundaryLocalTerm) :
    BulkMeasureLocalizationFields (α := α) μ interior boundary
      globalBulkIntegral where
  F := F
  interiorLocalTerm := interiorLocalTerm
  boundaryLocalTerm := boundaryLocalTerm
  interiorBox := interiorBox
  boundaryBox := boundaryBox
  globalBulkIntegral_eq_integral := hglobal
  interiorBox_measurable := hInteriorMeasurable
  boundaryBox_measurable := hBoundaryMeasurable
  interiorIntegrableOn := hInteriorIntegrable
  boundaryIntegrableOn := hBoundaryIntegrable
  interiorBulkTerm_eq_integral := hInteriorBulkTerm
  boundaryBulkTerm_eq_integral := hBoundaryBulkTerm
  F_ae_eq_indicatorSum := hF

omit [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
  [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem ofDerivativePartitionAEIndicator_F
    (F : α → Real)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (hglobal : globalBulkIntegral = ∫ y, F y ∂μ)
    (hInteriorMeasurable :
      ∀ i, i ∈ interior.active → MeasurableSet (interiorBox i))
    (hBoundaryMeasurable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x → MeasurableSet (boundaryBox x q))
    (hInteriorIntegrable :
      ∀ i, i ∈ interior.active →
        IntegrableOn (interiorLocalTerm i) (interiorBox i) μ)
    (hBoundaryIntegrable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          IntegrableOn (boundaryLocalTerm x q) (boundaryBox x q) μ)
    (hInteriorBulkTerm :
      ∀ i, i ∈ interior.active →
        interior.bulkTerm i = ∫ y in interiorBox i, interiorLocalTerm i y ∂μ)
    (hBoundaryBulkTerm :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ)
    (hF :
      F =ᵐ[μ]
        bulkMeasureIndicatorSum interior.active boundary.activeCharts
          boundary.boundaryPieces interiorBox boundaryBox interiorLocalTerm
          boundaryLocalTerm) :
    (ofDerivativePartitionAEIndicator
      (μ := μ) (interior := interior) (boundary := boundary)
      (globalBulkIntegral := globalBulkIntegral)
      F interiorLocalTerm boundaryLocalTerm interiorBox boundaryBox
      hglobal hInteriorMeasurable hBoundaryMeasurable
      hInteriorIntegrable hBoundaryIntegrable hInteriorBulkTerm
      hBoundaryBulkTerm hF).F = F :=
  rfl

omit [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
  [IsFiniteMeasureOnCompacts μ] in
/--
The derivative-partition a.e. reconstruction directly supplies the bulk
localization equality.
-/
theorem bulkIntegralLocalizes_of_derivativePartitionAEIndicator
    (F : α → Real)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (hglobal : globalBulkIntegral = ∫ y, F y ∂μ)
    (hInteriorMeasurable :
      ∀ i, i ∈ interior.active → MeasurableSet (interiorBox i))
    (hBoundaryMeasurable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x → MeasurableSet (boundaryBox x q))
    (hInteriorIntegrable :
      ∀ i, i ∈ interior.active →
        IntegrableOn (interiorLocalTerm i) (interiorBox i) μ)
    (hBoundaryIntegrable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          IntegrableOn (boundaryLocalTerm x q) (boundaryBox x q) μ)
    (hInteriorBulkTerm :
      ∀ i, i ∈ interior.active →
        interior.bulkTerm i = ∫ y in interiorBox i, interiorLocalTerm i y ∂μ)
    (hBoundaryBulkTerm :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ)
    (hF :
      F =ᵐ[μ]
        bulkMeasureIndicatorSum interior.active boundary.activeCharts
          boundary.boundaryPieces interiorBox boundaryBox interiorLocalTerm
          boundaryLocalTerm) :
    globalBulkIntegral =
      (Finset.sum interior.active fun i => interior.bulkTerm i) +
        BoundaryPieceFamilyInput.boundaryBulkSum boundary :=
  (ofDerivativePartitionAEIndicator
    (μ := μ) (interior := interior) (boundary := boundary)
    (globalBulkIntegral := globalBulkIntegral)
    F interiorLocalTerm boundaryLocalTerm interiorBox boundaryBox
    hglobal hInteriorMeasurable hBoundaryMeasurable
    hInteriorIntegrable hBoundaryIntegrable hInteriorBulkTerm
    hBoundaryBulkTerm hF).bulkIntegralLocalizes

/--
Construct the existing `BulkIntegralPartitionInput` from the same
derivative-partition a.e. indicator reconstruction.
-/
def toBulkIntegralPartitionInputOfDerivativePartitionAEIndicator
    (F : α → Real)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (hglobal : globalBulkIntegral = ∫ y, F y ∂μ)
    (hInteriorMeasurable :
      ∀ i, i ∈ interior.active → MeasurableSet (interiorBox i))
    (hBoundaryMeasurable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x → MeasurableSet (boundaryBox x q))
    (hInteriorIntegrable :
      ∀ i, i ∈ interior.active →
        IntegrableOn (interiorLocalTerm i) (interiorBox i) μ)
    (hBoundaryIntegrable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          IntegrableOn (boundaryLocalTerm x q) (boundaryBox x q) μ)
    (hInteriorBulkTerm :
      ∀ i, i ∈ interior.active →
        interior.bulkTerm i = ∫ y in interiorBox i, interiorLocalTerm i y ∂μ)
    (hBoundaryBulkTerm :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ)
    (hF :
      F =ᵐ[μ]
        bulkMeasureIndicatorSum interior.active boundary.activeCharts
          boundary.boundaryPieces interiorBox boundaryBox interiorLocalTerm
          boundaryLocalTerm) :
    BulkIntegralPartitionInput (ι := ι)
      (I := I) (ω := ω) (BoundaryChart := BoundaryChart)
      (BoundaryPiece := BoundaryPiece) :=
  (ofDerivativePartitionAEIndicator
    (μ := μ) (interior := interior) (boundary := boundary)
    (globalBulkIntegral := globalBulkIntegral)
    F interiorLocalTerm boundaryLocalTerm interiorBox boundaryBox
    hglobal hInteriorMeasurable hBoundaryMeasurable
    hInteriorIntegrable hBoundaryIntegrable hInteriorBulkTerm
    hBoundaryBulkTerm hF).toBulkIntegralPartitionInput

omit [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
  [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem toBulkIntegralPartitionInputOfDerivativePartitionAEIndicator_globalBulkIntegral
    (F : α → Real)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (hglobal : globalBulkIntegral = ∫ y, F y ∂μ)
    (hInteriorMeasurable :
      ∀ i, i ∈ interior.active → MeasurableSet (interiorBox i))
    (hBoundaryMeasurable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x → MeasurableSet (boundaryBox x q))
    (hInteriorIntegrable :
      ∀ i, i ∈ interior.active →
        IntegrableOn (interiorLocalTerm i) (interiorBox i) μ)
    (hBoundaryIntegrable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          IntegrableOn (boundaryLocalTerm x q) (boundaryBox x q) μ)
    (hInteriorBulkTerm :
      ∀ i, i ∈ interior.active →
        interior.bulkTerm i = ∫ y in interiorBox i, interiorLocalTerm i y ∂μ)
    (hBoundaryBulkTerm :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ)
    (hF :
      F =ᵐ[μ]
        bulkMeasureIndicatorSum interior.active boundary.activeCharts
          boundary.boundaryPieces interiorBox boundaryBox interiorLocalTerm
          boundaryLocalTerm) :
    (toBulkIntegralPartitionInputOfDerivativePartitionAEIndicator
      (μ := μ) (interior := interior) (boundary := boundary)
      (globalBulkIntegral := globalBulkIntegral)
      F interiorLocalTerm boundaryLocalTerm interiorBox boundaryBox
      hglobal hInteriorMeasurable hBoundaryMeasurable
      hInteriorIntegrable hBoundaryIntegrable hInteriorBulkTerm
      hBoundaryBulkTerm hF).globalBulkIntegral =
        globalBulkIntegral :=
  rfl

end BulkMeasureLocalizationFields

end BulkIntegralPartitionInput

section SelectedPartitionShape

variable {P : SelectedBoxPartitionOfUnity I ω}
variable {BoundaryPiece : Type p}
variable {boundary : BoundaryPieceFamilyInput I ω M BoundaryPiece}
variable {localized : LocalizedInteriorM8Fields I ω P}
variable {globalBulkIntegral : Real}

/--
Selected-partition version of the derivative-partition bulk measure fields.

The L5 statement usually uses `P.active` on both the interior and boundary
index sets.  This constructor rewrites that selected shape to the native
`LocalizedInteriorPieces`/`BoundaryPieceFamilyInput` shape.
-/
def selectedBulkMeasureFieldsOfDerivativePartitionAEIndicator
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
    (hF :
      F =ᵐ[μ]
        bulkMeasureIndicatorSum P.active P.active boundary.boundaryPieces
          interiorBox boundaryBox interiorLocalTerm boundaryLocalTerm) :
    BulkIntegralPartitionInput.BulkMeasureLocalizationFields
      (α := α) μ localized.localizedInterior boundary globalBulkIntegral where
  F := F
  interiorLocalTerm := interiorLocalTerm
  boundaryLocalTerm := boundaryLocalTerm
  interiorBox := interiorBox
  boundaryBox := boundaryBox
  globalBulkIntegral_eq_integral := hglobal
  interiorBox_measurable := by
    intro i hi
    exact hInteriorMeasurable i
      (by simpa [localized.localized_active] using hi)
  boundaryBox_measurable := by
    intro x hx q hq
    exact hBoundaryMeasurable x
      (by simpa [hboundary_active] using hx) q hq
  interiorIntegrableOn := by
    intro i hi
    exact hInteriorIntegrable i
      (by simpa [localized.localized_active] using hi)
  boundaryIntegrableOn := by
    intro x hx q hq
    exact hBoundaryIntegrable x
      (by simpa [hboundary_active] using hx) q hq
  interiorBulkTerm_eq_integral := by
    intro i hi
    exact hInteriorBulkTerm i
      (by simpa [localized.localized_active] using hi)
  boundaryBulkTerm_eq_integral := by
    intro x hx q hq
    exact hBoundaryBulkTerm x
      (by simpa [hboundary_active] using hx) q hq
  F_ae_eq_indicatorSum := by
    simpa [localized.localized_active, hboundary_active] using hF

omit [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
  [IsFiniteMeasureOnCompacts μ] in
/--
The selected derivative-partition reconstruction yields the exact selected
bulk localization equality needed by the compact-support M8 measure builder.
-/
theorem selected_bulkIntegralLocalizes_of_derivativePartitionAEIndicator
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
    (hF :
      F =ᵐ[μ]
        bulkMeasureIndicatorSum P.active P.active boundary.boundaryPieces
          interiorBox boundaryBox interiorLocalTerm boundaryLocalTerm) :
    globalBulkIntegral =
      (Finset.sum P.active fun i => localized.localizedInterior.bulkTerm i) +
        Finset.sum P.active fun x =>
          Finset.sum (boundary.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q := by
  have h :=
    (selectedBulkMeasureFieldsOfDerivativePartitionAEIndicator
      (μ := μ) (P := P) (boundary := boundary) (localized := localized)
      (globalBulkIntegral := globalBulkIntegral)
      hboundary_active F interiorLocalTerm boundaryLocalTerm interiorBox
      boundaryBox hglobal hInteriorMeasurable hBoundaryMeasurable
      hInteriorIntegrable hBoundaryIntegrable hInteriorBulkTerm
      hBoundaryBulkTerm hF).bulkIntegralLocalizes
  simpa [localized.localized_active, hboundary_active,
    BoundaryPieceFamilyInput.boundaryBulkSum] using h

/--
Selected-partition constructor for the existing `BulkIntegralPartitionInput`.
-/
def selectedBulkIntegralPartitionInputOfDerivativePartitionAEIndicator
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
    (hF :
      F =ᵐ[μ]
        bulkMeasureIndicatorSum P.active P.active boundary.boundaryPieces
          interiorBox boundaryBox interiorLocalTerm boundaryLocalTerm) :
    BulkIntegralPartitionInput
      (ι := M) (I := I) (ω := ω)
      (BoundaryChart := M) (BoundaryPiece := BoundaryPiece) :=
  (selectedBulkMeasureFieldsOfDerivativePartitionAEIndicator
    (μ := μ) (P := P) (boundary := boundary) (localized := localized)
    (globalBulkIntegral := globalBulkIntegral)
    hboundary_active F interiorLocalTerm boundaryLocalTerm interiorBox
    boundaryBox hglobal hInteriorMeasurable hBoundaryMeasurable
    hInteriorIntegrable hBoundaryIntegrable hInteriorBulkTerm
    hBoundaryBulkTerm hF).toBulkIntegralPartitionInput

omit [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
  [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem selectedBulkIntegralPartitionInputOfDerivativePartitionAEIndicator_globalBulkIntegral
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
    (hF :
      F =ᵐ[μ]
        bulkMeasureIndicatorSum P.active P.active boundary.boundaryPieces
          interiorBox boundaryBox interiorLocalTerm boundaryLocalTerm) :
    (selectedBulkIntegralPartitionInputOfDerivativePartitionAEIndicator
      (μ := μ) (P := P) (boundary := boundary) (localized := localized)
      (globalBulkIntegral := globalBulkIntegral)
      hboundary_active F interiorLocalTerm boundaryLocalTerm interiorBox
      boundaryBox hglobal hInteriorMeasurable hBoundaryMeasurable
      hInteriorIntegrable hBoundaryIntegrable hInteriorBulkTerm
      hBoundaryBulkTerm hF).globalBulkIntegral =
        globalBulkIntegral :=
  rfl

end SelectedPartitionShape

end BulkMeasureFromDerivativePartition

end Stokes

end
