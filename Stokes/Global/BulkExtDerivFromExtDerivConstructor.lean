import Stokes.Global.BulkExtDerivProjectLocalConstructors
import Stokes.Global.ExtDerivPartitionConstructor

/-!
# Bulk exterior-derivative a.e. input from reconstruction constructors

This module reduces the remaining project-local bulk a.e. input surface by
constructing `BulkIntegrandAEProjectLocalAutoInput` directly from existing
exterior-derivative reconstruction packages.

The constructors here do not change the endpoint records.  They remove
bookkeeping hypotheses that are already present in the source packages:

* `PartitionExtDerivConstructorData` already contains the reconstruction
  fields, the localized/eventual package, and their active/support alignment;
* `ExtDerivOnSupportData` already contains the reconstruction fields, so the
  selected-partition support facts can build the localized/eventual package
  without asking callers to pass a separate `PartitionReconstructionData`.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkExtDerivFromExtDerivConstructor

universe u w cb pb ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryChart : Type cb} {BoundaryPiece : Type pb}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {P : SelectedBoxPartitionOfUnity I omega}
variable {boundary : BoundaryPieceFamilyInput I omega BoundaryChart BoundaryPiece}
variable {localized : LocalizedInteriorM8Fields I omega P}

namespace BulkIntegrandAEProjectLocalAutoInput

/--
Construct the project-local automatic bulk a.e. input from the partition
exterior-derivative constructor package.

The reconstruction package and the active-set equality between
`localizedEventually` and that reconstruction are derived from
`D.extDerivOnSupport` and `D.activeCharts_eq`.  Since
`PartitionExtDerivConstructorData` stores a global chart-support cover, the
a.e. measure-support field is also automatic for any chartwise measure.
-/
def ofPartitionExtDerivConstructorData
    (D :
      PartitionExtDerivConstructorData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hactive :
      D.extDerivOnSupport.activeCharts =
        selectedPartitionBulkActive P boundary)
    (hcoefficient :
      D.extDerivOnSupport.coefficient =
        selectedPartitionBulkCoefficient
          (BoundaryChart := BoundaryChart) P)
    (measure : M → M → Measure (Fin (n + 1) → Real)) :
    BulkIntegrandAEProjectLocalAutoInput
      (BoundaryChart := BoundaryChart)
      ExtInteriorPiece ExtBoundaryPiece P boundary localized where
  localizedEventually := D.localizedEventually
  reconstruction := D.toPartitionReconstructionData
  localizedEventually_active := by
    calc
      D.localizedEventually.activeCharts = D.extDerivOnSupport.activeCharts :=
        D.activeCharts_eq
      _ = selectedPartitionBulkActive P boundary := hactive
  localizedEventually_coefficient := by
    calc
      D.localizedEventually.coefficient = D.extDerivOnSupport.coefficient :=
        D.coefficient_eq
      _ =
          selectedPartitionBulkCoefficient
            (BoundaryChart := BoundaryChart) P := hcoefficient
  localizedEventually_active_eq_reconstruction := by
    simpa [PartitionExtDerivConstructorData.toPartitionReconstructionData]
      using D.activeCharts_eq
  measure := measure
  hmeasureSupport := by
    intro x0 x1
    exact Filter.Eventually.of_forall fun y => by
      simpa [D.chartSupport_eq] using D.chartSupport_cover x0 x1 y

@[simp]
theorem ofPartitionExtDerivConstructorData_localizedEventually
    (D :
      PartitionExtDerivConstructorData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hactive :
      D.extDerivOnSupport.activeCharts =
        selectedPartitionBulkActive P boundary)
    (hcoefficient :
      D.extDerivOnSupport.coefficient =
        selectedPartitionBulkCoefficient
          (BoundaryChart := BoundaryChart) P)
    (measure : M → M → Measure (Fin (n + 1) → Real)) :
    (ofPartitionExtDerivConstructorData
      (P := P) (boundary := boundary) (localized := localized)
      D hactive hcoefficient measure).localizedEventually =
      D.localizedEventually := by
  rfl

@[simp]
theorem ofPartitionExtDerivConstructorData_reconstruction
    (D :
      PartitionExtDerivConstructorData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hactive :
      D.extDerivOnSupport.activeCharts =
        selectedPartitionBulkActive P boundary)
    (hcoefficient :
      D.extDerivOnSupport.coefficient =
        selectedPartitionBulkCoefficient
          (BoundaryChart := BoundaryChart) P)
    (measure : M → M → Measure (Fin (n + 1) → Real)) :
    (ofPartitionExtDerivConstructorData
      (P := P) (boundary := boundary) (localized := localized)
      D hactive hcoefficient measure).reconstruction =
      D.toPartitionReconstructionData := by
  rfl

@[simp]
theorem ofPartitionExtDerivConstructorData_measure
    (D :
      PartitionExtDerivConstructorData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hactive :
      D.extDerivOnSupport.activeCharts =
        selectedPartitionBulkActive P boundary)
    (hcoefficient :
      D.extDerivOnSupport.coefficient =
        selectedPartitionBulkCoefficient
          (BoundaryChart := BoundaryChart) P)
    (measure : M → M → Measure (Fin (n + 1) → Real)) :
    (ofPartitionExtDerivConstructorData
      (P := P) (boundary := boundary) (localized := localized)
      D hactive hcoefficient measure).measure =
      measure := by
  rfl

/--
Construct the project-local automatic bulk a.e. input from support-local
exterior-derivative reconstruction data and selected-partition support
containment.

This route uses `D.toPartitionReconstructionData` for the reconstruction fields
and builds the localized/eventual equality package from the selected partition
itself.  The chart support of that package is `univ`, so the measure-support
field is automatic.
-/
def ofExtDerivOnSupportDataSelectedPartition
    (D :
      ExtDerivOnSupportData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hactive :
      selectedPartitionBulkActive P boundary = D.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (homegaSupport : ManifoldForm.support I omega ⊆ P.K) :
    BulkIntegrandAEProjectLocalAutoInput
      (BoundaryChart := BoundaryChart)
      ExtInteriorPiece ExtBoundaryPiece P boundary localized :=
  ofLocalizedFormEventuallyEqData
    (P := P) (boundary := boundary) (localized := localized)
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    (P.toBulkLocalizedFormEventuallyEqData
      (BoundaryChart := BoundaryChart) boundary homegaSupport)
    D.toPartitionReconstructionData rfl rfl (by simpa using hactive) measure

@[simp]
theorem ofExtDerivOnSupportDataSelectedPartition_reconstruction
    (D :
      ExtDerivOnSupportData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hactive :
      selectedPartitionBulkActive P boundary = D.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (homegaSupport : ManifoldForm.support I omega ⊆ P.K) :
    (ofExtDerivOnSupportDataSelectedPartition
      (P := P) (boundary := boundary) (localized := localized)
      D hactive measure homegaSupport).reconstruction =
      D.toPartitionReconstructionData := by
  rfl

@[simp]
theorem ofExtDerivOnSupportDataSelectedPartition_measure
    (D :
      ExtDerivOnSupportData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hactive :
      selectedPartitionBulkActive P boundary = D.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (homegaSupport : ManifoldForm.support I omega ⊆ P.K) :
    (ofExtDerivOnSupportDataSelectedPartition
      (P := P) (boundary := boundary) (localized := localized)
      D hactive measure homegaSupport).measure =
      measure := by
  rfl

end BulkIntegrandAEProjectLocalAutoInput

end BulkExtDerivFromExtDerivConstructor

end Stokes

end
