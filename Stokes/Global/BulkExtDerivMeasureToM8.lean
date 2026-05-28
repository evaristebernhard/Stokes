import Stokes.Global.ExtDerivToBulkMeasure
import Stokes.Global.BulkMeasureFromPartition
import Stokes.Global.BulkMeasureToM8

/-!
# Exterior-derivative bulk measure data for M8

This file is a narrow adapter for the bulk side of M8.  It combines the three
stable ingredients currently used by the proof wave:

* `ExtDerivToBulkMeasure`, which packages chartwise a.e. exterior-derivative
  alignment and local measure-term comparisons;
* `BulkMeasureFromPartition`, which packages the selected-partition measure
  reconstruction with all analytic support/integrability assumptions explicit;
* `BulkMeasureToM8`, which converts bulk reconstruction fields to
  `M8BulkMeasureFields`.

No new analytic fact is proved here.  The constructors only repackage explicit
inputs into the M8-facing bulk field shape.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkExtDerivMeasureToM8

universe u w b a ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {globalBulkIntegral : Real}

namespace BulkMeasureFromPartitionData

/--
Selected-partition bulk measure data directly supplies the M8 bulk fields.

This uses the pure selected-partition measure theorem as the source of the M8
finite-sum reconstruction.  The analytic hypotheses remain in
`BulkMeasureFromPartitionData`.
-/
def toM8BulkMeasureFields
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral) :
    M8BulkMeasureFields I omega selectedPartition targetImages :=
  D.toBulkMeasureLocalizationFields.toM8BulkMeasureFields
    D.localized.localized_active
    D.localized.localized_coefficient
    D.boundary_active

@[simp]
theorem toM8BulkMeasureFields_localizedInterior
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral) :
    D.toM8BulkMeasureFields.localizedInterior =
      D.localized.localizedInterior :=
  rfl

@[simp]
theorem toM8BulkMeasureFields_globalBulkIntegral
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral) :
    D.toM8BulkMeasureFields.globalBulkIntegral =
      globalBulkIntegral :=
  rfl

@[simp]
theorem toM8BulkMeasureFields_bulkMeasureIntegral
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral) :
    D.toM8BulkMeasureFields.bulkMeasureIntegral =
      globalBulkIntegral :=
  rfl

end BulkMeasureFromPartitionData

/--
Bulk data for M8 with the exterior-derivative a.e. alignment kept next to the
selected-partition measure reconstruction.

The `selectedMeasure` field is the source used to produce the M8 finite-sum
bulk fields.  The `measureTerms` and `integrandAE` fields retain the
ext-derivative/local-measure-term alignment that later analytic constructors
can consume.
-/
structure BulkExtDerivMeasureToM8Data
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (μ : Measure α)
    (globalBulkIntegral : Real) where
  /-- Selected-partition measure reconstruction, with analytic assumptions explicit. -/
  selectedMeasure :
    BulkMeasureFromPartitionData (α := α) (μ := μ)
      selectedPartition targetImages globalBulkIntegral
  /-- Measure-local scalar terms aligned with the selected interior/boundary data. -/
  measureTerms :
    BulkMeasureLocalizationTermFields
      selectedMeasure.localized.localizedInterior targetImages
  /-- Exterior-derivative a.e. replacement and local measure-term comparisons. -/
  integrandAE : BulkIntegrandAELocalFields measureTerms

namespace BulkExtDerivMeasureToM8Data

variable
    (D :
      BulkExtDerivMeasureToM8Data (α := α)
        selectedPartition targetImages μ globalBulkIntegral)

/-- M8 bulk fields obtained from the selected-partition measure package. -/
def toM8BulkMeasureFields :
    M8BulkMeasureFields I omega selectedPartition targetImages :=
  D.selectedMeasure.toM8BulkMeasureFields

@[simp]
theorem toM8BulkMeasureFields_localizedInterior :
    D.toM8BulkMeasureFields.localizedInterior =
      D.selectedMeasure.localized.localizedInterior :=
  rfl

@[simp]
theorem toM8BulkMeasureFields_globalBulkIntegral :
    D.toM8BulkMeasureFields.globalBulkIntegral =
      globalBulkIntegral :=
  rfl

@[simp]
theorem toM8BulkMeasureFields_bulkMeasureIntegral :
    D.toM8BulkMeasureFields.bulkMeasureIntegral =
      globalBulkIntegral :=
  rfl

/--
Constructor-level bulk fields from the ext-derivative alignment, once the
remaining integrability and box-identification assumptions are supplied.
-/
def toConstructorFields
    (integrability : CompactSupportIntegrability D.integrandAE)
    (measureBoxAPI : MeasureBoxAPI D.integrandAE) :
    BulkMeasureLocalizationConstructorFields
      (ι := M) (I := I) (ω := omega)
      (BoundaryChart := M) (BoundaryPiece := BoundaryPiece) where
  interior := D.selectedMeasure.localized.localizedInterior
  boundary := targetImages
  measureTerms := D.measureTerms
  integrandAE := D.integrandAE
  integrability := integrability
  measureBoxAPI := measureBoxAPI

/--
M8 bulk fields through the constructor route, preserving the explicit bulk
measure integral carried by `measureTerms`.
-/
def toM8BulkMeasureFields_fromConstructor
    (integrability : CompactSupportIntegrability D.integrandAE)
    (measureBoxAPI : MeasureBoxAPI D.integrandAE) :
    M8BulkMeasureFields I omega selectedPartition targetImages :=
  (D.toConstructorFields integrability measureBoxAPI).toM8BulkMeasureFields
    D.selectedMeasure.localized.localized_active
    D.selectedMeasure.localized.localized_coefficient
    D.selectedMeasure.boundary_active

omit [OpensMeasurableSpace α] [T2Space α] [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem toConstructorFields_measureTerms
    (integrability : CompactSupportIntegrability D.integrandAE)
    (measureBoxAPI : MeasureBoxAPI D.integrandAE) :
    (D.toConstructorFields integrability measureBoxAPI).measureTerms =
      D.measureTerms :=
  rfl

omit [OpensMeasurableSpace α] [T2Space α] [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem toM8BulkMeasureFields_fromConstructor_globalBulkIntegral
    (integrability : CompactSupportIntegrability D.integrandAE)
    (measureBoxAPI : MeasureBoxAPI D.integrandAE) :
    (D.toM8BulkMeasureFields_fromConstructor
        integrability measureBoxAPI).globalBulkIntegral =
      D.measureTerms.globalBulkIntegral :=
  rfl

omit [OpensMeasurableSpace α] [T2Space α] [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem toM8BulkMeasureFields_fromConstructor_bulkMeasureIntegral
    (integrability : CompactSupportIntegrability D.integrandAE)
    (measureBoxAPI : MeasureBoxAPI D.integrandAE) :
    (D.toM8BulkMeasureFields_fromConstructor
        integrability measureBoxAPI).bulkMeasureIntegral =
      D.measureTerms.bulkMeasureIntegral :=
  rfl

variable {D}

/--
Build the bundled M8 bulk data from support-local exterior-derivative
reconstruction.

The measure-support hypothesis and the local measure/integrand-term equalities
are exactly the analytic inputs required by `ExtDerivToBulkMeasure`.
-/
def ofExtDerivOnSupportData
    (selectedMeasure :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    (measureTerms :
      BulkMeasureLocalizationTermFields
        selectedMeasure.localized.localizedInterior targetImages)
    (extDeriv :
      ExtDerivOnSupportData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1),
        y ∈ extDeriv.chartSupport x0 x1)
    (hactive :
      extDeriv.activeCharts =
        selectedMeasure.localized.localizedInterior.active.disjSum
          targetImages.activeCharts)
    (interiorIntegrandTerm : M → Real)
    (boundaryIntegrandTerm : M → BoundaryPiece → Real)
    (hinterior :
      ∀ i, i ∈ selectedMeasure.localized.localizedInterior.active →
        measureTerms.interiorMeasureTerm i = interiorIntegrandTerm i)
    (hboundary :
      ∀ x, x ∈ targetImages.activeCharts →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          measureTerms.boundaryMeasureTerm x q =
            boundaryIntegrandTerm x q) :
    BulkExtDerivMeasureToM8Data (α := α)
      selectedPartition targetImages μ globalBulkIntegral where
  selectedMeasure := selectedMeasure
  measureTerms := measureTerms
  integrandAE :=
    BulkIntegrandAELocalFields.ofExtDerivOnSupportData
      (measureTerms := measureTerms)
      extDeriv measure hmeasureSupport hactive
      interiorIntegrandTerm boundaryIntegrandTerm
      hinterior hboundary

/--
Build the bundled M8 bulk data from eventual-equality exterior-derivative
reconstruction.
-/
def ofExtDerivEventuallyEqData
    (selectedMeasure :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    (measureTerms :
      BulkMeasureLocalizationTermFields
        selectedMeasure.localized.localizedInterior targetImages)
    (extDeriv :
      ExtDerivEventuallyEqData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1),
        y ∈ extDeriv.chartSupport x0 x1)
    (hactive :
      extDeriv.activeCharts =
        selectedMeasure.localized.localizedInterior.active.disjSum
          targetImages.activeCharts)
    (interiorIntegrandTerm : M → Real)
    (boundaryIntegrandTerm : M → BoundaryPiece → Real)
    (hinterior :
      ∀ i, i ∈ selectedMeasure.localized.localizedInterior.active →
        measureTerms.interiorMeasureTerm i = interiorIntegrandTerm i)
    (hboundary :
      ∀ x, x ∈ targetImages.activeCharts →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          measureTerms.boundaryMeasureTerm x q =
            boundaryIntegrandTerm x q) :
    BulkExtDerivMeasureToM8Data (α := α)
      selectedPartition targetImages μ globalBulkIntegral where
  selectedMeasure := selectedMeasure
  measureTerms := measureTerms
  integrandAE :=
    BulkIntegrandAELocalFields.ofExtDerivEventuallyEqData
      (measureTerms := measureTerms)
      extDeriv measure hmeasureSupport hactive
      interiorIntegrandTerm boundaryIntegrandTerm
      hinterior hboundary

omit [OpensMeasurableSpace α] [T2Space α] [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem ofExtDerivOnSupportData_selectedMeasure
    (selectedMeasure :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    (measureTerms :
      BulkMeasureLocalizationTermFields
        selectedMeasure.localized.localizedInterior targetImages)
    (extDeriv :
      ExtDerivOnSupportData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1),
        y ∈ extDeriv.chartSupport x0 x1)
    (hactive :
      extDeriv.activeCharts =
        selectedMeasure.localized.localizedInterior.active.disjSum
          targetImages.activeCharts)
    (interiorIntegrandTerm : M → Real)
    (boundaryIntegrandTerm : M → BoundaryPiece → Real)
    (hinterior :
      ∀ i, i ∈ selectedMeasure.localized.localizedInterior.active →
        measureTerms.interiorMeasureTerm i = interiorIntegrandTerm i)
    (hboundary :
      ∀ x, x ∈ targetImages.activeCharts →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          measureTerms.boundaryMeasureTerm x q =
            boundaryIntegrandTerm x q) :
    (ofExtDerivOnSupportData (α := α) (μ := μ)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      selectedMeasure measureTerms extDeriv measure hmeasureSupport hactive
      interiorIntegrandTerm boundaryIntegrandTerm hinterior
      hboundary).selectedMeasure = selectedMeasure :=
  rfl

omit [OpensMeasurableSpace α] [T2Space α] [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem ofExtDerivEventuallyEqData_selectedMeasure
    (selectedMeasure :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral)
    (measureTerms :
      BulkMeasureLocalizationTermFields
        selectedMeasure.localized.localizedInterior targetImages)
    (extDeriv :
      ExtDerivEventuallyEqData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1),
        y ∈ extDeriv.chartSupport x0 x1)
    (hactive :
      extDeriv.activeCharts =
        selectedMeasure.localized.localizedInterior.active.disjSum
          targetImages.activeCharts)
    (interiorIntegrandTerm : M → Real)
    (boundaryIntegrandTerm : M → BoundaryPiece → Real)
    (hinterior :
      ∀ i, i ∈ selectedMeasure.localized.localizedInterior.active →
        measureTerms.interiorMeasureTerm i = interiorIntegrandTerm i)
    (hboundary :
      ∀ x, x ∈ targetImages.activeCharts →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          measureTerms.boundaryMeasureTerm x q =
            boundaryIntegrandTerm x q) :
    (ofExtDerivEventuallyEqData (α := α) (μ := μ)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      selectedMeasure measureTerms extDeriv measure hmeasureSupport hactive
      interiorIntegrandTerm boundaryIntegrandTerm hinterior
      hboundary).selectedMeasure = selectedMeasure :=
  rfl

end BulkExtDerivMeasureToM8Data

end BulkExtDerivMeasureToM8

end Stokes

end
