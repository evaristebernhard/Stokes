import Stokes.Global.ExtDerivToBulkMeasure
import Stokes.Global.BulkMeasureFromPartition
import Stokes.Global.BulkMeasureToM8

/-!
# Natural bulk-measure builder

This file collects the current bulk-measure route into M8-facing constructors.

The analytic facts are still inputs.  In particular, the exterior-derivative
support hypothesis for the chosen chartwise measures, the measure-local scalar
terms, compact-support/integrability data, and box-term identifications are not
proved here.  The goal of this layer is only to keep the natural selected
partition, exterior-derivative a.e. replacement, compact-support bulk package,
and M8 bulk field adapter aligned.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalBulkMeasureBuilder

universe u w b a ei eb

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

namespace CompactSupportBulkMeasureData

variable {localizedInterior : LocalizedInteriorPieces (ι := M) I omega}
variable {globalBulkIntegral : Real}

/--
Adapt compact-support bulk localization directly to the M8 bulk field package.

The selected-partition and target-image alignments remain explicit because this
constructor does not choose the partition or boundary target family.
-/
def toM8BulkMeasureFields
    (D :
      CompactSupportBulkMeasureData (α := α) (μ := μ)
        localizedInterior targetImages globalBulkIntegral)
    (hlocalized :
      localizedInterior.active = selectedPartition.active)
    (hcoefficient :
      localizedInterior.coefficient =
        fun i x => selectedPartition.partition i x)
    (htarget :
      targetImages.activeCharts = selectedPartition.active) :
    M8BulkMeasureFields I omega selectedPartition targetImages :=
  D.toBulkMeasureLocalizationFields.toM8BulkMeasureFields
    hlocalized hcoefficient htarget

@[simp]
theorem toM8BulkMeasureFields_globalBulkIntegral
    (D :
      CompactSupportBulkMeasureData (α := α) (μ := μ)
        localizedInterior targetImages globalBulkIntegral)
    (hlocalized :
      localizedInterior.active = selectedPartition.active)
    (hcoefficient :
      localizedInterior.coefficient =
        fun i x => selectedPartition.partition i x)
    (htarget :
      targetImages.activeCharts = selectedPartition.active) :
    (D.toM8BulkMeasureFields
      (selectedPartition := selectedPartition)
      hlocalized hcoefficient htarget).globalBulkIntegral =
      globalBulkIntegral :=
  rfl

@[simp]
theorem toM8BulkMeasureFields_bulkMeasureIntegral
    (D :
      CompactSupportBulkMeasureData (α := α) (μ := μ)
        localizedInterior targetImages globalBulkIntegral)
    (hlocalized :
      localizedInterior.active = selectedPartition.active)
    (hcoefficient :
      localizedInterior.coefficient =
        fun i x => selectedPartition.partition i x)
    (htarget :
      targetImages.activeCharts = selectedPartition.active) :
    (D.toM8BulkMeasureFields
      (selectedPartition := selectedPartition)
      hlocalized hcoefficient htarget).bulkMeasureIntegral =
      globalBulkIntegral :=
  rfl

end CompactSupportBulkMeasureData

namespace BulkMeasureFromPartitionData

variable {globalBulkIntegral : Real}

/--
Selected-partition bulk measure data, after compact-support localization, gives
the M8 bulk fields without restating the finite local-bulk-sum equality.
-/
def toM8BulkMeasureFields
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral) :
    M8BulkMeasureFields I omega selectedPartition targetImages :=
  D.toBulkMeasureLocalizationFields.toM8BulkMeasureFields
    D.localized.localized_active D.localized.localized_coefficient
    D.boundary_active

@[simp]
theorem toM8BulkMeasureFields_globalBulkIntegral
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral) :
    D.toM8BulkMeasureFields.globalBulkIntegral = globalBulkIntegral :=
  rfl

@[simp]
theorem toM8BulkMeasureFields_bulkMeasureIntegral
    (D :
      BulkMeasureFromPartitionData (α := α) (μ := μ)
        selectedPartition targetImages globalBulkIntegral) :
    D.toM8BulkMeasureFields.bulkMeasureIntegral = globalBulkIntegral :=
  rfl

end BulkMeasureFromPartitionData

/--
Ext-derivative-facing natural builder for the M8 bulk measure fields.

This record chooses the natural selected-partition and target-image indexing,
then uses `BulkIntegrandAELocalFields.ofExtDerivOnSupportData` to construct the
a.e. replacement package.  The real analytic inputs remain explicit fields:
`hmeasureSupport`, the measure-local terms and their local integral
identifications, compact-support integrability, and the box API.
-/
structure NaturalBulkMeasureBuilderData
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (ExtInteriorPiece : Type ei) (ExtBoundaryPiece : Type eb) where
  /-- Selected-partition localized interior fields. -/
  localized : LocalizedInteriorM8Fields I omega selectedPartition
  /-- The target-image boundary family uses the selected active set. -/
  targetImages_active :
    targetImages.activeCharts = selectedPartition.active
  /-- Measure-local finite-sum terms. -/
  measureTerms :
    BulkMeasureLocalizationTermFields localized.localizedInterior targetImages
  /-- Exterior-derivative reconstruction on a controlled chartwise support. -/
  extDeriv :
    ExtDerivOnSupportData I omega (M ⊕ M) ExtInteriorPiece
      ExtBoundaryPiece
  /-- The chart-pair measures used for bulk-integrand a.e. replacement. -/
  measure : M → M → Measure (Fin (n + 1) → Real)
  /-- The selected chartwise measures are a.e. supported where `extDeriv` applies. -/
  hmeasureSupport :
    ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1),
      y ∈ extDeriv.chartSupport x0 x1
  /-- The exterior-derivative package uses the combined active labels. -/
  extDeriv_active :
    extDeriv.activeCharts =
      localized.localizedInterior.active.disjSum targetImages.activeCharts
  /-- Integrand-local term for each active selected interior chart. -/
  interiorIntegrandTerm : M → Real
  /-- Integrand-local term for each active target-image boundary piece. -/
  boundaryIntegrandTerm : M → BoundaryPiece → Real
  /-- Interior measure-local terms equal the corresponding integrand-local terms. -/
  interiorMeasureTerm_eq_integrandTerm :
    ∀ i, i ∈ localized.localizedInterior.active →
      measureTerms.interiorMeasureTerm i = interiorIntegrandTerm i
  /-- Boundary measure-local terms equal the corresponding integrand-local terms. -/
  boundaryMeasureTerm_eq_integrandTerm :
    ∀ x, x ∈ targetImages.activeCharts →
      ∀ q, q ∈ targetImages.boundaryPieces x →
        measureTerms.boundaryMeasureTerm x q =
          boundaryIntegrandTerm x q
  /-- Compact-support integrability for the constructed a.e. replacement package. -/
  integrability :
    CompactSupportIntegrability
      (BulkIntegrandAELocalFields.ofExtDerivOnSupportData
        (I := I) (ω := omega) (measureTerms := measureTerms)
        extDeriv measure hmeasureSupport extDeriv_active
        interiorIntegrandTerm boundaryIntegrandTerm
        interiorMeasureTerm_eq_integrandTerm
        boundaryMeasureTerm_eq_integrandTerm)
  /-- Box-term identifications for the constructed a.e. replacement package. -/
  measureBoxAPI :
    MeasureBoxAPI
      (BulkIntegrandAELocalFields.ofExtDerivOnSupportData
        (I := I) (ω := omega) (measureTerms := measureTerms)
        extDeriv measure hmeasureSupport extDeriv_active
        interiorIntegrandTerm boundaryIntegrandTerm
        interiorMeasureTerm_eq_integrandTerm
        boundaryMeasureTerm_eq_integrandTerm)

namespace NaturalBulkMeasureBuilderData

variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}

/-- The a.e. local replacement package produced from the explicit ext-deriv data. -/
def integrandAE
    (D :
      NaturalBulkMeasureBuilderData I omega selectedPartition targetImages
        ExtInteriorPiece ExtBoundaryPiece) :
    BulkIntegrandAELocalFields D.measureTerms :=
  BulkIntegrandAELocalFields.ofExtDerivOnSupportData
    (I := I) (ω := omega) (measureTerms := D.measureTerms)
    D.extDeriv D.measure D.hmeasureSupport D.extDeriv_active
    D.interiorIntegrandTerm D.boundaryIntegrandTerm
    D.interiorMeasureTerm_eq_integrandTerm
    D.boundaryMeasureTerm_eq_integrandTerm

/-- Repackage the natural builder as the existing bulk localization constructor fields. -/
def toConstructorFields
    (D :
      NaturalBulkMeasureBuilderData I omega selectedPartition targetImages
        ExtInteriorPiece ExtBoundaryPiece) :
    BulkMeasureLocalizationConstructorFields
      (ι := M) (I := I) (ω := omega)
      (BoundaryChart := M) (BoundaryPiece := BoundaryPiece) where
  interior := D.localized.localizedInterior
  boundary := targetImages
  measureTerms := D.measureTerms
  integrandAE := D.integrandAE
  integrability := by
    simpa [integrandAE] using D.integrability
  measureBoxAPI := by
    simpa [integrandAE] using D.measureBoxAPI

/-- The natural builder supplies the M8 bulk measure-localization fields. -/
def toM8BulkMeasureFields
    (D :
      NaturalBulkMeasureBuilderData I omega selectedPartition targetImages
        ExtInteriorPiece ExtBoundaryPiece) :
    M8BulkMeasureFields I omega selectedPartition targetImages :=
  D.toConstructorFields.toM8BulkMeasureFields
    D.localized.localized_active D.localized.localized_coefficient
    D.targetImages_active

@[simp]
theorem integrandAE_aeData
    (D :
      NaturalBulkMeasureBuilderData I omega selectedPartition targetImages
        ExtInteriorPiece ExtBoundaryPiece) :
    D.integrandAE.aeData =
      BulkIntegrandAEData.ofExtDerivOnSupportData
        (I := I) (ω := omega) D.extDeriv D.measure
        D.hmeasureSupport :=
  rfl

@[simp]
theorem toConstructorFields_interior
    (D :
      NaturalBulkMeasureBuilderData I omega selectedPartition targetImages
        ExtInteriorPiece ExtBoundaryPiece) :
    D.toConstructorFields.interior = D.localized.localizedInterior :=
  rfl

@[simp]
theorem toConstructorFields_boundary
    (D :
      NaturalBulkMeasureBuilderData I omega selectedPartition targetImages
        ExtInteriorPiece ExtBoundaryPiece) :
    D.toConstructorFields.boundary = targetImages :=
  rfl

@[simp]
theorem toConstructorFields_measureTerms
    (D :
      NaturalBulkMeasureBuilderData I omega selectedPartition targetImages
        ExtInteriorPiece ExtBoundaryPiece) :
    D.toConstructorFields.measureTerms = D.measureTerms :=
  rfl

@[simp]
theorem toM8BulkMeasureFields_globalBulkIntegral
    (D :
      NaturalBulkMeasureBuilderData I omega selectedPartition targetImages
        ExtInteriorPiece ExtBoundaryPiece) :
    D.toM8BulkMeasureFields.globalBulkIntegral =
      D.measureTerms.globalBulkIntegral :=
  rfl

@[simp]
theorem toM8BulkMeasureFields_bulkMeasureIntegral
    (D :
      NaturalBulkMeasureBuilderData I omega selectedPartition targetImages
        ExtInteriorPiece ExtBoundaryPiece) :
    D.toM8BulkMeasureFields.bulkMeasureIntegral =
      D.measureTerms.bulkMeasureIntegral :=
  rfl

/--
Direct constructor spelling for M8 bulk fields from explicit
exterior-derivative-on-support data.
-/
def m8BulkMeasureFieldsOfExtDerivOnSupportData
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (targetImages_active :
      targetImages.activeCharts = selectedPartition.active)
    (measureTerms :
      BulkMeasureLocalizationTermFields localized.localizedInterior targetImages)
    (extDeriv :
      ExtDerivOnSupportData I omega (M ⊕ M) ExtInteriorPiece
        ExtBoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1),
        y ∈ extDeriv.chartSupport x0 x1)
    (extDeriv_active :
      extDeriv.activeCharts =
        localized.localizedInterior.active.disjSum targetImages.activeCharts)
    (interiorIntegrandTerm : M → Real)
    (boundaryIntegrandTerm : M → BoundaryPiece → Real)
    (interiorMeasureTerm_eq_integrandTerm :
      ∀ i, i ∈ localized.localizedInterior.active →
        measureTerms.interiorMeasureTerm i = interiorIntegrandTerm i)
    (boundaryMeasureTerm_eq_integrandTerm :
      ∀ x, x ∈ targetImages.activeCharts →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          measureTerms.boundaryMeasureTerm x q =
            boundaryIntegrandTerm x q)
    (integrability :
      CompactSupportIntegrability
        (BulkIntegrandAELocalFields.ofExtDerivOnSupportData
          (I := I) (ω := omega) (measureTerms := measureTerms)
          extDeriv measure hmeasureSupport extDeriv_active
          interiorIntegrandTerm boundaryIntegrandTerm
          interiorMeasureTerm_eq_integrandTerm
          boundaryMeasureTerm_eq_integrandTerm))
    (measureBoxAPI :
      MeasureBoxAPI
        (BulkIntegrandAELocalFields.ofExtDerivOnSupportData
          (I := I) (ω := omega) (measureTerms := measureTerms)
          extDeriv measure hmeasureSupport extDeriv_active
          interiorIntegrandTerm boundaryIntegrandTerm
          interiorMeasureTerm_eq_integrandTerm
          boundaryMeasureTerm_eq_integrandTerm)) :
    M8BulkMeasureFields I omega selectedPartition targetImages :=
  (NaturalBulkMeasureBuilderData.mk
    localized targetImages_active measureTerms extDeriv measure
    hmeasureSupport extDeriv_active interiorIntegrandTerm
    boundaryIntegrandTerm interiorMeasureTerm_eq_integrandTerm
    boundaryMeasureTerm_eq_integrandTerm integrability measureBoxAPI)
    |>.toM8BulkMeasureFields

@[simp]
theorem m8BulkMeasureFieldsOfExtDerivOnSupportData_globalBulkIntegral
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (targetImages_active :
      targetImages.activeCharts = selectedPartition.active)
    (measureTerms :
      BulkMeasureLocalizationTermFields localized.localizedInterior targetImages)
    (extDeriv :
      ExtDerivOnSupportData I omega (M ⊕ M) ExtInteriorPiece
        ExtBoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1),
        y ∈ extDeriv.chartSupport x0 x1)
    (extDeriv_active :
      extDeriv.activeCharts =
        localized.localizedInterior.active.disjSum targetImages.activeCharts)
    (interiorIntegrandTerm : M → Real)
    (boundaryIntegrandTerm : M → BoundaryPiece → Real)
    (interiorMeasureTerm_eq_integrandTerm :
      ∀ i, i ∈ localized.localizedInterior.active →
        measureTerms.interiorMeasureTerm i = interiorIntegrandTerm i)
    (boundaryMeasureTerm_eq_integrandTerm :
      ∀ x, x ∈ targetImages.activeCharts →
        ∀ q, q ∈ targetImages.boundaryPieces x →
          measureTerms.boundaryMeasureTerm x q =
            boundaryIntegrandTerm x q)
    (integrability :
      CompactSupportIntegrability
        (BulkIntegrandAELocalFields.ofExtDerivOnSupportData
          (I := I) (ω := omega) (measureTerms := measureTerms)
          extDeriv measure hmeasureSupport extDeriv_active
          interiorIntegrandTerm boundaryIntegrandTerm
          interiorMeasureTerm_eq_integrandTerm
          boundaryMeasureTerm_eq_integrandTerm))
    (measureBoxAPI :
      MeasureBoxAPI
        (BulkIntegrandAELocalFields.ofExtDerivOnSupportData
          (I := I) (ω := omega) (measureTerms := measureTerms)
          extDeriv measure hmeasureSupport extDeriv_active
          interiorIntegrandTerm boundaryIntegrandTerm
          interiorMeasureTerm_eq_integrandTerm
          boundaryMeasureTerm_eq_integrandTerm)) :
    (m8BulkMeasureFieldsOfExtDerivOnSupportData
        (I := I) (omega := omega) (selectedPartition := selectedPartition)
        (targetImages := targetImages)
        localized targetImages_active measureTerms extDeriv measure
        hmeasureSupport extDeriv_active interiorIntegrandTerm
        boundaryIntegrandTerm interiorMeasureTerm_eq_integrandTerm
        boundaryMeasureTerm_eq_integrandTerm integrability measureBoxAPI).globalBulkIntegral =
      measureTerms.globalBulkIntegral :=
  rfl

end NaturalBulkMeasureBuilderData

end NaturalBulkMeasureBuilder

end Stokes

end
