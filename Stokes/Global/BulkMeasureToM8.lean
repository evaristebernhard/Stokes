import Stokes.Global.M8Statement
import Stokes.Global.BulkMeasureLocalizationFields

/-!
# Bulk measure localization adapters for M8

This file is an M8-facing adapter layer.  It does not change the M8 statement;
instead it packages the bulk fields of `M8MeasureLocalizationData` and provides
constructors from the current bulk measure-localization APIs.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section BulkMeasureToM8

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

/--
The bulk half of `M8MeasureLocalizationData`.

The boundary measure fields are intentionally absent.  This lets the bulk
measure-localization workers fill the four M8 bulk fields without depending on
the boundary COV/measure reconstruction path.
-/
structure M8BulkMeasureFields
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece) where
  /-- Localized partition-of-unity interior pieces. -/
  localizedInterior : LocalizedInteriorPieces (ι := M) I omega
  /-- The localized active set is the selected partition active set. -/
  localized_active :
    localizedInterior.active = selectedPartition.active
  /-- The localized coefficients are the selected partition coefficients. -/
  localized_coefficient :
    localizedInterior.coefficient =
      fun i x => selectedPartition.partition i x
  /-- The represented global bulk integral. -/
  globalBulkIntegral : Real
  /-- The genuine bulk measure integral represented by the localization data. -/
  bulkMeasureIntegral : Real
  /-- The represented bulk integral agrees with the bulk measure integral. -/
  globalBulkIntegral_eq_bulkMeasureIntegral :
    globalBulkIntegral = bulkMeasureIntegral
  /-- The bulk measure integral is reconstructed from localized local terms. -/
  bulkMeasureIntegral_eq_localBulkSum :
    bulkMeasureIntegral =
      (Finset.sum selectedPartition.active fun x =>
        Finset.sum ({()} : Finset Unit) fun _q =>
          localizedInterior.bulkTerm x) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (targetImages.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm targetImages x q

namespace M8BulkMeasureFields

@[simp]
theorem localBulkSum_singleton
    (B : M8BulkMeasureFields I omega selectedPartition targetImages) :
    ((Finset.sum selectedPartition.active fun x =>
        Finset.sum ({()} : Finset Unit) fun _q =>
          B.localizedInterior.bulkTerm x) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (targetImages.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm targetImages x q) =
      (Finset.sum selectedPartition.active fun x =>
          B.localizedInterior.bulkTerm x) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (targetImages.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm targetImages x q := by
  simp

/--
Complete `M8MeasureLocalizationData` by adding the boundary measure fields to
an already constructed M8 bulk package.
-/
def toM8MeasureLocalizationData
    (B : M8BulkMeasureFields I omega selectedPartition targetImages)
    (boundaryPartitionTerm : M → BoundaryPiece → Real)
    (globalBoundaryIntegral boundaryMeasureIntegral : Real)
    (hboundaryMeasure :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (hboundaryPartition :
      boundaryMeasureIntegral =
        selectedBoundaryPieceSum selectedPartition.active
          targetImages.boundaryPieces boundaryPartitionTerm) :
    M8MeasureLocalizationData I omega selectedPartition targetImages where
  localizedInterior := B.localizedInterior
  localized_active := B.localized_active
  localized_coefficient := B.localized_coefficient
  globalBulkIntegral := B.globalBulkIntegral
  bulkMeasureIntegral := B.bulkMeasureIntegral
  globalBulkIntegral_eq_bulkMeasureIntegral :=
    B.globalBulkIntegral_eq_bulkMeasureIntegral
  bulkMeasureIntegral_eq_localBulkSum :=
    B.bulkMeasureIntegral_eq_localBulkSum
  boundaryPartitionTerm := boundaryPartitionTerm
  globalBoundaryIntegral := globalBoundaryIntegral
  boundaryMeasureIntegral := boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := hboundaryMeasure
  boundaryMeasureIntegral_eq_partitionSum := hboundaryPartition

@[simp]
theorem toM8MeasureLocalizationData_globalBulkIntegral
    (B : M8BulkMeasureFields I omega selectedPartition targetImages)
    (boundaryPartitionTerm : M → BoundaryPiece → Real)
    (globalBoundaryIntegral boundaryMeasureIntegral : Real)
    (hboundaryMeasure :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (hboundaryPartition :
      boundaryMeasureIntegral =
        selectedBoundaryPieceSum selectedPartition.active
          targetImages.boundaryPieces boundaryPartitionTerm) :
    (B.toM8MeasureLocalizationData boundaryPartitionTerm
        globalBoundaryIntegral boundaryMeasureIntegral hboundaryMeasure
        hboundaryPartition).globalBulkIntegral =
      B.globalBulkIntegral :=
  rfl

@[simp]
theorem toM8MeasureLocalizationData_bulkMeasureIntegral
    (B : M8BulkMeasureFields I omega selectedPartition targetImages)
    (boundaryPartitionTerm : M → BoundaryPiece → Real)
    (globalBoundaryIntegral boundaryMeasureIntegral : Real)
    (hboundaryMeasure :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (hboundaryPartition :
      boundaryMeasureIntegral =
        selectedBoundaryPieceSum selectedPartition.active
          targetImages.boundaryPieces boundaryPartitionTerm) :
    (B.toM8MeasureLocalizationData boundaryPartitionTerm
        globalBoundaryIntegral boundaryMeasureIntegral hboundaryMeasure
        hboundaryPartition).bulkMeasureIntegral =
      B.bulkMeasureIntegral :=
  rfl

end M8BulkMeasureFields

namespace BulkIntegralPartitionInput

variable {α : Type a} [MeasurableSpace α]
variable {μ : MeasureTheory.Measure α}
variable {localizedInterior : LocalizedInteriorPieces (ι := M) I omega}
variable {globalBulkIntegral : Real}

/--
Adapt the pure `BulkIntegralPartitionInput.BulkMeasureLocalizationFields`
package to the M8 bulk field shape.

This route has no separate intermediate bulk measure integral, so the adapter
uses the represented global bulk integral itself as the M8 bulk measure
integral.
-/
def BulkMeasureLocalizationFields.toM8BulkMeasureFields
    (D :
      BulkMeasureLocalizationFields (α := α) μ localizedInterior
        targetImages globalBulkIntegral)
    (hlocalized :
      localizedInterior.active = selectedPartition.active)
    (hcoefficient :
      localizedInterior.coefficient =
        fun i x => selectedPartition.partition i x)
    (htarget :
      targetImages.activeCharts = selectedPartition.active) :
    M8BulkMeasureFields I omega selectedPartition targetImages where
  localizedInterior := localizedInterior
  localized_active := hlocalized
  localized_coefficient := hcoefficient
  globalBulkIntegral := globalBulkIntegral
  bulkMeasureIntegral := globalBulkIntegral
  globalBulkIntegral_eq_bulkMeasureIntegral := rfl
  bulkMeasureIntegral_eq_localBulkSum := by
    simpa [BoundaryPieceFamilyInput.boundaryBulkSum, hlocalized, htarget]
      using D.bulkIntegralLocalizes

@[simp]
theorem BulkMeasureLocalizationFields.toM8BulkMeasureFields_globalBulkIntegral
    (D :
      BulkMeasureLocalizationFields (α := α) μ localizedInterior
        targetImages globalBulkIntegral)
    (hlocalized :
      localizedInterior.active = selectedPartition.active)
    (hcoefficient :
      localizedInterior.coefficient =
        fun i x => selectedPartition.partition i x)
    (htarget :
      targetImages.activeCharts = selectedPartition.active) :
    (D.toM8BulkMeasureFields hlocalized hcoefficient htarget).globalBulkIntegral =
      globalBulkIntegral :=
  rfl

@[simp]
theorem BulkMeasureLocalizationFields.toM8BulkMeasureFields_bulkMeasureIntegral
    (D :
      BulkMeasureLocalizationFields (α := α) μ localizedInterior
        targetImages globalBulkIntegral)
    (hlocalized :
      localizedInterior.active = selectedPartition.active)
    (hcoefficient :
      localizedInterior.coefficient =
        fun i x => selectedPartition.partition i x)
    (htarget :
      targetImages.activeCharts = selectedPartition.active) :
    (D.toM8BulkMeasureFields hlocalized hcoefficient htarget).bulkMeasureIntegral =
      globalBulkIntegral :=
  rfl

end BulkIntegralPartitionInput

namespace BulkMeasureLocalizationConstructorFields

/--
Adapt the bundled constructor fields to the M8 bulk field shape.

This preserves the constructor's genuine `bulkMeasureIntegral`, unlike the
pure partition-measure route above.
-/
def toM8BulkMeasureFields
    (D : BulkMeasureLocalizationConstructorFields
      (ι := M) (I := I) (ω := omega)
      (BoundaryChart := M) (BoundaryPiece := BoundaryPiece))
    (hlocalized :
      D.interior.active = selectedPartition.active)
    (hcoefficient :
      D.interior.coefficient =
        fun i x => selectedPartition.partition i x)
    (htarget :
      D.boundary.activeCharts = selectedPartition.active) :
    M8BulkMeasureFields I omega selectedPartition D.boundary where
  localizedInterior := D.interior
  localized_active := hlocalized
  localized_coefficient := hcoefficient
  globalBulkIntegral := D.measureTerms.globalBulkIntegral
  bulkMeasureIntegral := D.measureTerms.bulkMeasureIntegral
  globalBulkIntegral_eq_bulkMeasureIntegral :=
    D.measureTerms.globalBulkIntegral_eq_bulkMeasureIntegral
  bulkMeasureIntegral_eq_localBulkSum := by
    calc
      D.measureTerms.bulkMeasureIntegral =
          D.measureTerms.globalBulkIntegral :=
        D.measureTerms.globalBulkIntegral_eq_bulkMeasureIntegral.symm
      _ =
          (Finset.sum selectedPartition.active fun x =>
            Finset.sum ({()} : Finset Unit) fun _q =>
              D.interior.bulkTerm x) +
            Finset.sum selectedPartition.active fun x =>
              Finset.sum (D.boundary.boundaryPieces x) fun q =>
                BoundaryPieceFamilyInput.boundaryBulkTerm D.boundary x q := by
        simpa [BoundaryPieceFamilyInput.boundaryBulkSum, hlocalized, htarget]
          using D.bulkIntegralLocalizes

@[simp]
theorem toM8BulkMeasureFields_globalBulkIntegral
    (D : BulkMeasureLocalizationConstructorFields
      (ι := M) (I := I) (ω := omega)
      (BoundaryChart := M) (BoundaryPiece := BoundaryPiece))
    (hlocalized :
      D.interior.active = selectedPartition.active)
    (hcoefficient :
      D.interior.coefficient =
        fun i x => selectedPartition.partition i x)
    (htarget :
      D.boundary.activeCharts = selectedPartition.active) :
    (D.toM8BulkMeasureFields hlocalized hcoefficient htarget).globalBulkIntegral =
      D.measureTerms.globalBulkIntegral :=
  rfl

@[simp]
theorem toM8BulkMeasureFields_bulkMeasureIntegral
    (D : BulkMeasureLocalizationConstructorFields
      (ι := M) (I := I) (ω := omega)
      (BoundaryChart := M) (BoundaryPiece := BoundaryPiece))
    (hlocalized :
      D.interior.active = selectedPartition.active)
    (hcoefficient :
      D.interior.coefficient =
        fun i x => selectedPartition.partition i x)
    (htarget :
      D.boundary.activeCharts = selectedPartition.active) :
    (D.toM8BulkMeasureFields hlocalized hcoefficient htarget).bulkMeasureIntegral =
      D.measureTerms.bulkMeasureIntegral :=
  rfl

end BulkMeasureLocalizationConstructorFields

end BulkMeasureToM8

end Stokes

end
