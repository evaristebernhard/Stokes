import Stokes.Global.BulkMeasureFromPartition
import Stokes.Global.CompactSupportToM8Measure

/-!
# Compact-support bulk measure localization from indicator reconstruction

This downstream file connects the compact-support bulk-measure packages to the
measure-indicator reconstruction theorem in
`BulkIntegralPartitionReconstruction`.

The point is small but important for the compact-support Stokes assembly: once
the actual scalar bulk integrand is reconstructed a.e. from indicator-localized
chart-box terms, the required bulk localization field is obtained directly from
`BulkIntegralPartitionInput.bulkIntegralLocalizes_of_measure_indicator_reconstruction`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportBulkMeasureFromIndicators

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

namespace CompactSupportBulkMeasureData

variable {interior : LocalizedInteriorPieces (ι := M) I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {globalBulkIntegral : Real}

/--
Consume compact-support bulk measure data through the indicator-reconstruction
constructor.  This is definitionally the same bulk partition package as the
usual compact-support route, but its `bulkIntegralLocalizes` field is supplied
by the newer measure-indicator theorem.
-/
def toBulkIntegralPartitionInputFromIndicators
    (D :
      CompactSupportBulkMeasureData
        (α := α) (μ := μ) interior targetImages globalBulkIntegral) :
    BulkIntegralPartitionInput
      (ι := M) (I := I) (ω := omega)
      (BoundaryChart := M) (BoundaryPiece := BoundaryPiece) :=
  BulkIntegralPartitionInput.ofMeasureIndicatorReconstruction
    (μ := μ) interior targetImages globalBulkIntegral
    D.F D.interiorLocalTerm D.boundaryLocalTerm D.interiorBox D.boundaryBox
    D.globalBulkIntegral_eq_integral D.interiorBox_measurable
    D.boundaryBox_measurable
    (fun i hi => D.interiorIntegrableOn i hi)
    (fun x hx q hq => D.boundaryIntegrableOn x hx q hq)
    D.interiorBulkTerm_eq_integral D.boundaryBulkTerm_eq_integral
    D.F_ae_eq_indicatorSum

@[simp]
theorem toBulkIntegralPartitionInputFromIndicators_globalBulkIntegral
    (D :
      CompactSupportBulkMeasureData
        (α := α) (μ := μ) interior targetImages globalBulkIntegral) :
    D.toBulkIntegralPartitionInputFromIndicators.globalBulkIntegral =
      globalBulkIntegral :=
  rfl

/--
The compact-support bulk localization field, derived directly from the
measure-indicator reconstruction theorem.
-/
theorem bulkIntegralLocalizes_fromIndicators
    (D :
      CompactSupportBulkMeasureData
        (α := α) (μ := μ) interior targetImages globalBulkIntegral) :
    globalBulkIntegral =
      (Finset.sum interior.active fun i => interior.bulkTerm i) +
        BoundaryPieceFamilyInput.boundaryBulkSum targetImages :=
  BulkIntegralPartitionInput.bulkIntegralLocalizes_of_measure_indicator_reconstruction
    (μ := μ) interior targetImages globalBulkIntegral
    D.F D.interiorLocalTerm D.boundaryLocalTerm D.interiorBox D.boundaryBox
    D.globalBulkIntegral_eq_integral D.interiorBox_measurable
    D.boundaryBox_measurable
    (fun i hi => D.interiorIntegrableOn i hi)
    (fun x hx q hq => D.boundaryIntegrableOn x hx q hq)
    D.interiorBulkTerm_eq_integral D.boundaryBulkTerm_eq_integral
    D.F_ae_eq_indicatorSum

end CompactSupportBulkMeasureData

namespace BulkMeasureFromPartitionData

variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {globalBulkIntegral : Real}

/--
Selected-partition bulk measure data consumed through the compact-support
indicator route.
-/
def toBulkIntegralPartitionInputFromIndicators
    (D :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition targetImages
        globalBulkIntegral) :
    BulkIntegralPartitionInput
      (ι := M) (I := I) (ω := omega)
      (BoundaryChart := M) (BoundaryPiece := BoundaryPiece) :=
  D.toCompactSupportBulkMeasureData.toBulkIntegralPartitionInputFromIndicators

@[simp]
theorem toBulkIntegralPartitionInputFromIndicators_globalBulkIntegral
    (D :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition targetImages
        globalBulkIntegral) :
    D.toBulkIntegralPartitionInputFromIndicators.globalBulkIntegral =
      globalBulkIntegral :=
  rfl

/--
Selected active-set form of bulk localization, derived via the
measure-indicator reconstruction theorem.
-/
theorem bulkIntegralLocalizes_selected_fromIndicators
    (D :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition targetImages
        globalBulkIntegral) :
    globalBulkIntegral =
      (Finset.sum selectedPartition.active fun i =>
        D.localized.localizedInterior.bulkTerm i) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (targetImages.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm targetImages x q := by
  let C := D.toCompactSupportBulkMeasureData
  have h :
      globalBulkIntegral =
        (Finset.sum D.localized.localizedInterior.active fun i =>
          D.localized.localizedInterior.bulkTerm i) +
          BoundaryPieceFamilyInput.boundaryBulkSum targetImages :=
    BulkIntegralPartitionInput.bulkIntegralLocalizes_of_measure_indicator_reconstruction
      (μ := μ) D.localized.localizedInterior targetImages globalBulkIntegral
      C.F C.interiorLocalTerm C.boundaryLocalTerm C.interiorBox C.boundaryBox
      C.globalBulkIntegral_eq_integral C.interiorBox_measurable
      C.boundaryBox_measurable
      (fun i hi => C.interiorIntegrableOn i hi)
      (fun x hx q hq => C.boundaryIntegrableOn x hx q hq)
      C.interiorBulkTerm_eq_integral C.boundaryBulkTerm_eq_integral
      C.F_ae_eq_indicatorSum
  simpa [D.localized.localized_active, D.boundary_active,
    BoundaryPieceFamilyInput.boundaryBulkSum] using h

end BulkMeasureFromPartitionData

namespace CompactSupportToM8MeasureData

variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

variable
    (D :
      CompactSupportToM8MeasureData
        (α := α) I omega selectedPartition targetImages μ)

/--
The M8 bulk finite-sum field, with the bulk side supplied through the
measure-indicator reconstruction theorem.
-/
theorem bulkMeasureIntegral_eq_localBulkSum_fromIndicators :
    D.globalBulkIntegral =
      (Finset.sum selectedPartition.active fun x =>
        Finset.sum ({()} : Finset Unit) fun _q =>
          D.localized.localizedInterior.bulkTerm x) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (targetImages.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm targetImages x q := by
  simpa [D.localized.localized_active, D.targetImages_active,
    BoundaryPieceFamilyInput.boundaryBulkSum] using
    D.bulk.bulkIntegralLocalizes_fromIndicators

end CompactSupportToM8MeasureData

end CompactSupportBulkMeasureFromIndicators

end Stokes

end
