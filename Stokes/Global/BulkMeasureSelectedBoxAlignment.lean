import Stokes.Global.BulkMeasureCanonicalRoute
import Stokes.Global.CompactSupportMeasureToM8Builder
import Stokes.Global.NaturalStrictBufferBuilder

/-!
# Bulk measure alignment with selected boxes

This file is a projection layer for the bulk-measure side of the global Stokes
pipeline.  The selected-box alignment data is already present in
`BulkMeasureFromPartitionData`, `CompactSupportToM8MeasureData`, and the
measure-side builder.  The declarations below expose that data under stable
names so later constructors do not have to manually thread
`measure.toM8MeasureLocalizationData.localizedInterior = ...`.

No new analytic localization result is proved here.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkMeasureSelectedBoxAlignment

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

namespace CompactSupportToM8MeasureData

variable
    (D :
      CompactSupportToM8MeasureData
        (α := α) I omega selectedPartition targetImages μ)

/-- The M8 measure package uses the localized pieces carried by `D.localized`. -/
@[simp]
theorem toM8_selectedBox_localizedInterior :
    D.toM8MeasureLocalizationData.localizedInterior =
      D.localized.localizedInterior :=
  rfl

/-- The M8 measure package is active exactly on the selected partition. -/
theorem toM8_selectedBox_active :
    D.toM8MeasureLocalizationData.localizedInterior.active =
      selectedPartition.active :=
  D.toM8MeasureLocalizationData.localized_active

/-- The M8 measure package uses the selected partition coefficients. -/
theorem toM8_selectedBox_coefficient :
    D.toM8MeasureLocalizationData.localizedInterior.coefficient =
      fun i x => selectedPartition.partition i x :=
  D.toM8MeasureLocalizationData.localized_coefficient

/-- Pointwise coefficient projection in selected-box form. -/
theorem toM8_selectedBox_coefficient_apply (i : M) :
    D.toM8MeasureLocalizationData.localizedInterior.coefficient i =
      fun x => selectedPartition.partition i x :=
  congrFun D.toM8_selectedBox_coefficient i

/-- Local bulk terms in the M8 package are the localized bulk terms of `D`. -/
@[simp]
theorem toM8_selectedBox_bulkTerm (i : M) :
    D.toM8MeasureLocalizationData.localizedInterior.bulkTerm i =
      D.localized.localizedInterior.bulkTerm i :=
  rfl

/-- Artificial boundary terms in the M8 package are the localized terms of `D`. -/
@[simp]
theorem toM8_selectedBox_artificialBoundaryTerm (i : M) :
    D.toM8MeasureLocalizationData.localizedInterior.artificialBoundaryTerm i =
      D.localized.localizedInterior.artificialBoundaryTerm i :=
  rfl

end CompactSupportToM8MeasureData

namespace BulkMeasureFromPartitionData

variable {globalBulkIntegral : Real}
variable
    (D :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition targetImages
        globalBulkIntegral)

/--
The selected-partition bulk package, rewritten directly as M8 bulk fields.

This is only a projection wrapper around the existing compact-support bulk
measure route.
-/
def toSelectedBoxM8BulkFields :
    M8BulkMeasureFields I omega selectedPartition targetImages :=
  D.toBulkMeasureLocalizationFields.toM8BulkMeasureFields
    D.localized.localized_active D.localized.localized_coefficient
    D.boundary_active

@[simp]
theorem toSelectedBoxM8BulkFields_localizedInterior :
    D.toSelectedBoxM8BulkFields.localizedInterior =
      D.localized.localizedInterior :=
  rfl

/-- The selected bulk wrapper is active exactly on the selected partition. -/
theorem toSelectedBoxM8BulkFields_active :
    D.toSelectedBoxM8BulkFields.localizedInterior.active =
      selectedPartition.active :=
  D.toSelectedBoxM8BulkFields.localized_active

/-- The selected bulk wrapper uses the selected partition coefficients. -/
theorem toSelectedBoxM8BulkFields_coefficient :
    D.toSelectedBoxM8BulkFields.localizedInterior.coefficient =
      fun i x => selectedPartition.partition i x :=
  D.toSelectedBoxM8BulkFields.localized_coefficient

@[simp]
theorem toSelectedBoxM8BulkFields_globalBulkIntegral :
    D.toSelectedBoxM8BulkFields.globalBulkIntegral =
      globalBulkIntegral :=
  rfl

@[simp]
theorem toSelectedBoxM8BulkFields_bulkMeasureIntegral :
    D.toSelectedBoxM8BulkFields.bulkMeasureIntegral =
      globalBulkIntegral :=
  rfl

@[simp]
theorem toSelectedBoxM8BulkFields_bulkTerm (i : M) :
    D.toSelectedBoxM8BulkFields.localizedInterior.bulkTerm i =
      D.localized.localizedInterior.bulkTerm i :=
  rfl

/--
The selected bulk wrapper exposes the M8 finite local-bulk-sum field over
`selectedPartition.active`.
-/
theorem toSelectedBoxM8BulkFields_bulkMeasureIntegral_eq_selectedSum :
    D.toSelectedBoxM8BulkFields.bulkMeasureIntegral =
      (Finset.sum selectedPartition.active fun x =>
        Finset.sum ({()} : Finset Unit) fun _q =>
          D.localized.localizedInterior.bulkTerm x) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (targetImages.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm targetImages x q :=
  D.toSelectedBoxM8BulkFields.bulkMeasureIntegral_eq_localBulkSum

end BulkMeasureFromPartitionData

namespace CompactSupportMeasureToM8BuilderData

variable {globalBulkIntegral globalBoundaryIntegral : Real}
variable
    (D :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImages μ
        globalBulkIntegral globalBoundaryIntegral)

/-- The compact-support measure package produced by the builder keeps the bulk-localized pieces. -/
@[simp]
theorem toCompactSupportToM8MeasureData_localized :
    D.toCompactSupportToM8MeasureData.localized = D.bulk.localized :=
  rfl

/-- The builder's M8 measure package uses the selected bulk localized interior family. -/
@[simp]
theorem toM8_selectedBox_localizedInterior :
    D.toM8MeasureLocalizationData.localizedInterior =
      D.bulk.localized.localizedInterior :=
  rfl

/-- The builder's M8 measure package is active exactly on the selected partition. -/
theorem toM8_selectedBox_active :
    D.toM8MeasureLocalizationData.localizedInterior.active =
      selectedPartition.active :=
  D.toM8MeasureLocalizationData.localized_active

/-- The builder's M8 measure package uses the selected partition coefficients. -/
theorem toM8_selectedBox_coefficient :
    D.toM8MeasureLocalizationData.localizedInterior.coefficient =
      fun i x => selectedPartition.partition i x :=
  D.toM8MeasureLocalizationData.localized_coefficient

@[simp]
theorem toM8_selectedBox_bulkTerm (i : M) :
    D.toM8MeasureLocalizationData.localizedInterior.bulkTerm i =
      D.bulk.localized.localizedInterior.bulkTerm i :=
  rfl

/-- The builder's selected bulk wrapper. -/
def toSelectedBoxM8BulkFields :
    M8BulkMeasureFields I omega selectedPartition targetImages :=
  D.bulk.toSelectedBoxM8BulkFields

@[simp]
theorem toSelectedBoxM8BulkFields_localizedInterior :
    D.toSelectedBoxM8BulkFields.localizedInterior =
      D.bulk.localized.localizedInterior :=
  rfl

@[simp]
theorem toSelectedBoxM8BulkFields_bulkMeasureIntegral :
    D.toSelectedBoxM8BulkFields.bulkMeasureIntegral =
      globalBulkIntegral :=
  rfl

/--
The equality needed by natural strict-buffer builders, projected from the
measure-side builder.
-/
theorem measure_localizedInterior_eq_bulk :
    D.toCompactSupportToM8MeasureData.toM8MeasureLocalizationData.localizedInterior =
      D.bulk.localized.localizedInterior :=
  rfl

end CompactSupportMeasureToM8BuilderData

/--
Small reusable package for the selected-box localized-interior equality needed
when a compact-support measure package is fed into the natural builders.
-/
structure BulkMeasureSelectedBoxAlignment
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega selectedPartition targetImages μ) where
  /-- The localized interior fields used by downstream natural builders. -/
  localizedInterior : LocalizedInteriorM8Fields I omega selectedPartition
  /-- The measure package's M8 localized interior is the selected one. -/
  measure_localizedInterior :
    measure.toM8MeasureLocalizationData.localizedInterior =
      localizedInterior.localizedInterior

namespace BulkMeasureSelectedBoxAlignment

variable
    {measure :
      CompactSupportToM8MeasureData
        (α := α) I omega selectedPartition targetImages μ}

/-- Every compact-support measure package carries its own selected-box alignment. -/
def ofMeasure
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega selectedPartition targetImages μ) :
    BulkMeasureSelectedBoxAlignment measure where
  localizedInterior := measure.localized
  measure_localizedInterior := rfl

@[simp]
theorem ofMeasure_localizedInterior
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega selectedPartition targetImages μ) :
    (ofMeasure measure).localizedInterior = measure.localized :=
  rfl

/-- Project the active-set alignment from the chosen localized-interior fields. -/
theorem active
    (A : BulkMeasureSelectedBoxAlignment measure) :
    A.localizedInterior.localizedInterior.active = selectedPartition.active :=
  A.localizedInterior.localized_active

/-- Project the coefficient alignment from the chosen localized-interior fields. -/
theorem coefficient
    (A : BulkMeasureSelectedBoxAlignment measure) :
    A.localizedInterior.localizedInterior.coefficient =
      fun i x => selectedPartition.partition i x :=
  A.localizedInterior.localized_coefficient

end BulkMeasureSelectedBoxAlignment

namespace CompactSupportMeasureToM8BuilderData

variable {globalBulkIntegral globalBoundaryIntegral : Real}
variable
    (D :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImages μ
        globalBulkIntegral globalBoundaryIntegral)

/-- Selected-box alignment package induced by the measure-side builder. -/
def toBulkMeasureSelectedBoxAlignment :
    BulkMeasureSelectedBoxAlignment D.toCompactSupportToM8MeasureData where
  localizedInterior := D.bulk.localized
  measure_localizedInterior := rfl

@[simp]
theorem toBulkMeasureSelectedBoxAlignment_localizedInterior :
    D.toBulkMeasureSelectedBoxAlignment.localizedInterior =
      D.bulk.localized :=
  rfl

@[simp]
theorem toBulkMeasureSelectedBoxAlignment_measure_localizedInterior :
    D.toBulkMeasureSelectedBoxAlignment.measure_localizedInterior =
      D.measure_localizedInterior_eq_bulk :=
  rfl

end CompactSupportMeasureToM8BuilderData

namespace NaturalCompactSupportBuilderData

variable
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
variable {globalBulkIntegral globalBoundaryIntegral : Real}

/--
Natural builder entry point from the measure-side builder and a form strict
buffer.  The localized-interior equality is supplied automatically by the bulk
alignment projections above.
-/
def ofMeasureBuilderWithFormInnerBoxBuffer
    (measureBuilder :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImageInput.targetImages μ
        globalBulkIntegral globalBoundaryIntegral)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measureBuilder.toCompactSupportToM8MeasureData.boundaryPartitionTerm)
    (buffer :
      LocalizedInteriorFormInnerBoxBuffer I omega selectedPartition
        targetImageInput.targetImages measureBuilder.toM8MeasureLocalizationData) :
    NaturalCompactSupportBuilderData I omega BoundaryPiece μ :=
  ofPackagesWithFormInnerBoxBuffer
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    formData orientedBoundaryAtlas selectedPartition
    selectedPartition_supportSet targetImageInput measureBuilder.bulk.localized
    measureBuilder.toCompactSupportToM8MeasureData
    measureBuilder.measure_localizedInterior_eq_bulk
    target_boundaryPartitionTerm buffer

@[simp]
theorem ofMeasureBuilderWithFormInnerBoxBuffer_measure
    (measureBuilder :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImageInput.targetImages μ
        globalBulkIntegral globalBoundaryIntegral)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measureBuilder.toCompactSupportToM8MeasureData.boundaryPartitionTerm)
    (buffer :
      LocalizedInteriorFormInnerBoxBuffer I omega selectedPartition
        targetImageInput.targetImages measureBuilder.toM8MeasureLocalizationData) :
    (ofMeasureBuilderWithFormInnerBoxBuffer
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      formData orientedBoundaryAtlas selectedPartition
      selectedPartition_supportSet targetImageInput measureBuilder
      target_boundaryPartitionTerm buffer).measure =
        measureBuilder.toCompactSupportToM8MeasureData :=
  rfl

/--
Natural builder entry point from the measure-side builder and a coefficient
strict buffer.
-/
def ofMeasureBuilderWithCoefficientInnerBoxBuffer
    (measureBuilder :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImageInput.targetImages μ
        globalBulkIntegral globalBoundaryIntegral)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measureBuilder.toCompactSupportToM8MeasureData.boundaryPartitionTerm)
    (buffer :
      LocalizedInteriorCoefficientInnerBoxBuffer I omega selectedPartition
        targetImageInput.targetImages measureBuilder.toM8MeasureLocalizationData) :
    NaturalCompactSupportBuilderData I omega BoundaryPiece μ :=
  ofPackagesWithCoefficientInnerBoxBuffer
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    formData orientedBoundaryAtlas selectedPartition
    selectedPartition_supportSet targetImageInput measureBuilder.bulk.localized
    measureBuilder.toCompactSupportToM8MeasureData
    measureBuilder.measure_localizedInterior_eq_bulk
    target_boundaryPartitionTerm buffer

@[simp]
theorem ofMeasureBuilderWithCoefficientInnerBoxBuffer_measure
    (measureBuilder :
      CompactSupportMeasureToM8BuilderData
        (α := α) I omega selectedPartition targetImageInput.targetImages μ
        globalBulkIntegral globalBoundaryIntegral)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measureBuilder.toCompactSupportToM8MeasureData.boundaryPartitionTerm)
    (buffer :
      LocalizedInteriorCoefficientInnerBoxBuffer I omega selectedPartition
        targetImageInput.targetImages measureBuilder.toM8MeasureLocalizationData) :
    (ofMeasureBuilderWithCoefficientInnerBoxBuffer
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      formData orientedBoundaryAtlas selectedPartition
      selectedPartition_supportSet targetImageInput measureBuilder
      target_boundaryPartitionTerm buffer).measure =
        measureBuilder.toCompactSupportToM8MeasureData :=
  rfl

end NaturalCompactSupportBuilderData

end BulkMeasureSelectedBoxAlignment

end Stokes

end
