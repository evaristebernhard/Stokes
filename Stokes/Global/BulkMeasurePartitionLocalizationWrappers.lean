import Stokes.Global.BulkMeasureSelectedBoxAlignment

/-!
# Bulk measure localization wrappers for selected partitions

This file is a zero-semantics projection layer around the bulk-measure
localization packages.  It exposes the already-proved measure localization
facts in the shape used by selected chart partitions, so downstream builders
can `simp` through active-set alignments instead of reopening the compact
support and measure field packages by hand.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkMeasurePartitionLocalizationWrappers

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

namespace BulkMeasureFromPartitionData

variable {globalBulkIntegral : Real}
variable
    (D :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition targetImages
        globalBulkIntegral)

omit [OpensMeasurableSpace α] [T2Space α] [IsFiniteMeasureOnCompacts μ] in
/-- Selected active-set form of the unlocalized-to-indicator reconstruction. -/
theorem selected_unlocalizedSum_ae_eq_indicatorSum :
    bulkMeasureUnlocalizedSum selectedPartition.active selectedPartition.active
        targetImages.boundaryPieces D.interiorLocalTerm D.boundaryLocalTerm
        =ᵐ[μ]
      bulkMeasureIndicatorSum selectedPartition.active selectedPartition.active
        targetImages.boundaryPieces D.interiorBox D.boundaryBox
        D.interiorLocalTerm D.boundaryLocalTerm :=
  bulkMeasureUnlocalizedSum_ae_eq_indicatorSum_of_support_subset
    (μ := μ) selectedPartition.active selectedPartition.active
    targetImages.boundaryPieces D.interiorBox D.boundaryBox
    D.interiorLocalTerm D.boundaryLocalTerm
    (fun i hi => D.interior_support_subset_box i hi)
    (fun x hx q hq => D.boundary_support_subset_box x hx q hq)

omit [OpensMeasurableSpace α] [T2Space α] [IsFiniteMeasureOnCompacts μ] in
/-- Selected active-set form of the global a.e. indicator reconstruction. -/
theorem selected_F_ae_eq_indicatorSum :
    D.F =ᵐ[μ]
      bulkMeasureIndicatorSum selectedPartition.active selectedPartition.active
        targetImages.boundaryPieces D.interiorBox D.boundaryBox
        D.interiorLocalTerm D.boundaryLocalTerm := by
  simpa [D.localized.localized_active, D.boundary_active] using
    D.toCompactSupportBulkMeasureData.F_ae_eq_indicatorSum

/-- Active selected interior terms are integrable on their selected boxes. -/
theorem selected_interiorIntegrableOn
    (i : M) (hi : i ∈ selectedPartition.active) :
    IntegrableOn (D.interiorLocalTerm i) (D.interiorBox i) μ :=
  (D.interiorCompactSupport i hi).integrableOn (D.interiorBox i)

/-- Active selected boundary terms are integrable on their selected boxes. -/
theorem selected_boundaryIntegrableOn
    (x : M) (hx : x ∈ selectedPartition.active)
    (q : BoundaryPiece) (hq : q ∈ targetImages.boundaryPieces x) :
    IntegrableOn (D.boundaryLocalTerm x q) (D.boundaryBox x q) μ :=
  (D.boundaryCompactSupport x hx q hq).integrableOn (D.boundaryBox x q)

/-- Indicator version of selected interior integrability. -/
theorem selected_interiorIndicatorIntegrable
    (i : M) (hi : i ∈ selectedPartition.active) :
    Integrable ((D.interiorBox i).indicator (D.interiorLocalTerm i)) μ :=
  (D.selected_interiorIntegrableOn i hi).integrable_indicator
    (D.interiorBox_measurable i hi)

/-- Indicator version of selected boundary integrability. -/
theorem selected_boundaryIndicatorIntegrable
    (x : M) (hx : x ∈ selectedPartition.active)
    (q : BoundaryPiece) (hq : q ∈ targetImages.boundaryPieces x) :
    Integrable
      ((D.boundaryBox x q).indicator (D.boundaryLocalTerm x q)) μ :=
  (D.selected_boundaryIntegrableOn x hx q hq).integrable_indicator
    (D.boundaryBox_measurable x hx q hq)

/-- The selected interior indicator sum is integrable. -/
theorem selected_interiorIndicatorSumIntegrable :
    Integrable
      (bulkMeasureInteriorIndicatorSum selectedPartition.active
        D.interiorBox D.interiorLocalTerm) μ := by
  simpa [bulkMeasureInteriorIndicatorSum] using
    integrable_finset_sum selectedPartition.active fun i hi =>
      D.selected_interiorIndicatorIntegrable i hi

/-- The selected boundary indicator sum is integrable. -/
theorem selected_boundaryIndicatorSumIntegrable :
    Integrable
      (bulkMeasureBoundaryIndicatorSum selectedPartition.active
        targetImages.boundaryPieces D.boundaryBox D.boundaryLocalTerm) μ := by
  simpa [bulkMeasureBoundaryIndicatorSum] using
    integrable_finset_sum selectedPartition.active fun x hx =>
      integrable_finset_sum (targetImages.boundaryPieces x) fun q hq =>
        D.selected_boundaryIndicatorIntegrable x hx q hq

/-- The full selected bulk indicator sum is integrable. -/
theorem selected_indicatorSumIntegrable :
    Integrable
      (bulkMeasureIndicatorSum selectedPartition.active selectedPartition.active
        targetImages.boundaryPieces D.interiorBox D.boundaryBox
        D.interiorLocalTerm D.boundaryLocalTerm) μ := by
  simpa [bulkMeasureIndicatorSum] using
    D.selected_interiorIndicatorSumIntegrable.add
      D.selected_boundaryIndicatorSumIntegrable

omit [OpensMeasurableSpace α] [T2Space α] [IsFiniteMeasureOnCompacts μ] in
/-- Selected interior indicator integrals are the recorded localized bulk terms. -/
theorem selected_interiorIndicatorIntegral_eq_bulkTerm
    (i : M) (hi : i ∈ selectedPartition.active) :
    (∫ y, (D.interiorBox i).indicator (D.interiorLocalTerm i) y ∂μ) =
      D.localized.localizedInterior.bulkTerm i := by
  calc
    (∫ y, (D.interiorBox i).indicator (D.interiorLocalTerm i) y ∂μ) =
        ∫ y in D.interiorBox i, D.interiorLocalTerm i y ∂μ := by
      rw [integral_indicator (D.interiorBox_measurable i hi)]
    _ = D.localized.localizedInterior.bulkTerm i :=
      (D.interiorBulkTerm_eq_integral i hi).symm

omit [OpensMeasurableSpace α] [T2Space α] [IsFiniteMeasureOnCompacts μ] in
/-- Selected boundary indicator integrals are the recorded boundary bulk terms. -/
theorem selected_boundaryIndicatorIntegral_eq_bulkTerm
    (x : M) (hx : x ∈ selectedPartition.active)
    (q : BoundaryPiece) (hq : q ∈ targetImages.boundaryPieces x) :
    (∫ y, (D.boundaryBox x q).indicator (D.boundaryLocalTerm x q) y ∂μ) =
      BoundaryPieceFamilyInput.boundaryBulkTerm targetImages x q := by
  calc
    (∫ y, (D.boundaryBox x q).indicator (D.boundaryLocalTerm x q) y ∂μ) =
        ∫ y in D.boundaryBox x q, D.boundaryLocalTerm x q y ∂μ := by
      rw [integral_indicator (D.boundaryBox_measurable x hx q hq)]
    _ = BoundaryPieceFamilyInput.boundaryBulkTerm targetImages x q :=
      (D.boundaryBulkTerm_eq_integral x hx q hq).symm

/--
Measure localization theorem rewritten over the selected active set and the
selected boundary target family.
-/
theorem selected_integral_eq_local_setIntegral_sum :
    (∫ y, D.F y ∂μ) =
      (Finset.sum selectedPartition.active fun i =>
        ∫ y in D.interiorBox i, D.interiorLocalTerm i y ∂μ) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (targetImages.boundaryPieces x) fun q =>
            ∫ y in D.boundaryBox x q, D.boundaryLocalTerm x q y ∂μ := by
  simpa [D.localized.localized_active, D.boundary_active] using
    D.toBulkMeasureLocalizationFields.integral_eq_local_setIntegral_sum

/-- Selected active-set finite set-integral reconstruction of the represented bulk integral. -/
theorem selected_globalBulkIntegral_eq_local_setIntegral_sum :
    globalBulkIntegral =
      (Finset.sum selectedPartition.active fun i =>
        ∫ y in D.interiorBox i, D.interiorLocalTerm i y ∂μ) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (targetImages.boundaryPieces x) fun q =>
            ∫ y in D.boundaryBox x q, D.boundaryLocalTerm x q y ∂μ := by
  calc
    globalBulkIntegral = ∫ y, D.F y ∂μ :=
      D.globalBulkIntegral_eq_integral
    _ =
        (Finset.sum selectedPartition.active fun i =>
          ∫ y in D.interiorBox i, D.interiorLocalTerm i y ∂μ) +
          Finset.sum selectedPartition.active fun x =>
            Finset.sum (targetImages.boundaryPieces x) fun q =>
              ∫ y in D.boundaryBox x q, D.boundaryLocalTerm x q y ∂μ :=
      D.selected_integral_eq_local_setIntegral_sum

@[simp]
theorem toBulkMeasureLocalizationFields_interiorBox :
    D.toBulkMeasureLocalizationFields.interiorBox = D.interiorBox :=
  rfl

@[simp]
theorem toBulkMeasureLocalizationFields_boundaryBox :
    D.toBulkMeasureLocalizationFields.boundaryBox = D.boundaryBox :=
  rfl

@[simp]
theorem toBulkMeasureLocalizationFields_interiorLocalTerm :
    D.toBulkMeasureLocalizationFields.interiorLocalTerm =
      D.interiorLocalTerm :=
  rfl

@[simp]
theorem toBulkMeasureLocalizationFields_boundaryLocalTerm :
    D.toBulkMeasureLocalizationFields.boundaryLocalTerm =
      D.boundaryLocalTerm :=
  rfl

end BulkMeasureFromPartitionData

namespace BulkIntegralPartitionInput

variable
    (D : BulkIntegralPartitionInput
      (ι := M) (I := I) (ω := omega)
      (BoundaryChart := M) (BoundaryPiece := BoundaryPiece))

/-- Rewrite a bulk partition input over a selected active set. -/
theorem globalBulkIntegral_eq_selected_bulk_sum
    (hInterior : D.interior.active = selectedPartition.active)
    (hBoundary : D.boundary.activeCharts = selectedPartition.active) :
    D.globalBulkIntegral =
      (Finset.sum selectedPartition.active fun i => D.interior.bulkTerm i) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (D.boundary.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm D.boundary x q := by
  simpa [hInterior, hBoundary, BoundaryPieceFamilyInput.boundaryBulkSum] using
    D.bulkIntegralLocalizes

/-- The generated reconstruction data has the same selected active-set sum. -/
theorem toBulkIntegralReconstructionData_globalBulkIntegral_eq_selected_bulk_sum
    (hInterior : D.interior.active = selectedPartition.active)
    (hBoundary : D.boundary.activeCharts = selectedPartition.active) :
    D.toBulkIntegralReconstructionData.globalBulkIntegral =
      (Finset.sum selectedPartition.active fun i => D.interior.bulkTerm i) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (D.boundary.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm D.boundary x q := by
  simpa using
    D.globalBulkIntegral_eq_selected_bulk_sum
      (selectedPartition := selectedPartition) hInterior hBoundary

end BulkIntegralPartitionInput

namespace BulkIntegralPartitionInput.BulkMeasureLocalizationFields

variable {interior : LocalizedInteriorPieces (ι := M) I omega}
variable {boundary : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {globalBulkIntegral : Real}
variable
    (D :
      BulkIntegralPartitionInput.BulkMeasureLocalizationFields
        (α := α) μ interior boundary globalBulkIntegral)

omit [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
  [IsFiniteMeasureOnCompacts μ] in
/-- Pure measure-localization equality rewritten over a selected active set. -/
theorem integral_eq_selected_local_setIntegral_sum
    (hInterior : interior.active = selectedPartition.active)
    (hBoundary : boundary.activeCharts = selectedPartition.active) :
    (∫ y, D.F y ∂μ) =
      (Finset.sum selectedPartition.active fun i =>
        ∫ y in D.interiorBox i, D.interiorLocalTerm i y ∂μ) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (boundary.boundaryPieces x) fun q =>
            ∫ y in D.boundaryBox x q, D.boundaryLocalTerm x q y ∂μ := by
  simpa [hInterior, hBoundary] using D.integral_eq_local_setIntegral_sum

omit [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
  [IsFiniteMeasureOnCompacts μ] in
/-- The partition input produced by measure fields localizes over the selected active set. -/
theorem toBulkIntegralPartitionInput_globalBulkIntegral_eq_selected_bulk_sum
    (hInterior : interior.active = selectedPartition.active)
    (hBoundary : boundary.activeCharts = selectedPartition.active) :
    D.toBulkIntegralPartitionInput.globalBulkIntegral =
      (Finset.sum selectedPartition.active fun i => interior.bulkTerm i) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (boundary.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q := by
  simpa using
    D.toBulkIntegralPartitionInput.globalBulkIntegral_eq_selected_bulk_sum
      (selectedPartition := selectedPartition) hInterior hBoundary

end BulkIntegralPartitionInput.BulkMeasureLocalizationFields

end BulkMeasurePartitionLocalizationWrappers

end Stokes

end
