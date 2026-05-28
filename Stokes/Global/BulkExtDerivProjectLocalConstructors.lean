import Stokes.Global.BulkExtDerivProjectLocalAuto
import Stokes.Global.PartitionLocalizedEventually

/-!
# Source constructors for project-local automatic bulk exterior-derivative input

This module packages the remaining genuine inputs for
`BulkIntegrandAEProjectLocalAutoInput` without changing the core endpoint files.

The main source route starts from `LocalizedFormEventuallyEqData`.  That package
already proves that the localized finite sum reconstructs the original form
globally, after using the stored support containment.  We therefore may use the
whole model space as the chart support; the measure-support field is then
formal, while the analytic reconstruction content remains in the source data.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkExtDerivProjectLocalConstructors

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

namespace LocalizedFormEventuallyEqData

/--
Promote global localized-form eventual reconstruction to the partition-local
eventual-equality package with unrestricted chart support.

The unrestricted support is intentional: the source data has already proved
global equality of the localized form sum with the original form, so every
chartwise representative is eventually equal at every model point.
-/
def toPartitionLocalizedEventuallyFieldsOnUniv
    {Chart : Type*}
    (D : LocalizedFormEventuallyEqData I omega Chart) :
    PartitionLocalizedEventuallyFields I omega Chart where
  activeCharts := D.activeCharts
  coefficient := D.coefficient
  supportSet := D.supportSet
  chartSupport := fun _ _ => univ
  support_preimage_subset_chartSupport := by
    intro _x0 _x1 _y _hy
    simp
  localizedFormSum_eq_self_on := D.localizedFormSum_eq_self_on
  chartwiseEventuallyEq_on := by
    intro x0 x1 y _hy
    exact D.transitionPullbackInChart_eventuallyEq_self x0 x1 y

@[simp]
theorem toPartitionLocalizedEventuallyFieldsOnUniv_activeCharts
    {Chart : Type*}
    (D : LocalizedFormEventuallyEqData I omega Chart) :
    D.toPartitionLocalizedEventuallyFieldsOnUniv.activeCharts =
      D.activeCharts := by
  rfl

@[simp]
theorem toPartitionLocalizedEventuallyFieldsOnUniv_coefficient
    {Chart : Type*}
    (D : LocalizedFormEventuallyEqData I omega Chart) :
    D.toPartitionLocalizedEventuallyFieldsOnUniv.coefficient =
      D.coefficient := by
  rfl

@[simp]
theorem toPartitionLocalizedEventuallyFieldsOnUniv_chartSupport
    {Chart : Type*}
    (D : LocalizedFormEventuallyEqData I omega Chart) :
    D.toPartitionLocalizedEventuallyFieldsOnUniv.chartSupport =
      fun _ _ => univ := by
  rfl

end LocalizedFormEventuallyEqData

namespace SelectedBoxPartitionOfUnity

/-- The combined interior/boundary-label localized form sum is the selected
interior localized form sum, since boundary labels carry coefficient zero. -/
theorem localizedFormSum_selectedPartitionBulkActive_eq
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundary : BoundaryPieceFamilyInput I omega BoundaryChart BoundaryPiece) :
    localizedFormSum I (selectedPartitionBulkActive P boundary)
        (selectedPartitionBulkCoefficient (BoundaryChart := BoundaryChart) P)
        omega =
      localizedFormSum I P.active (fun i y => P.partition i y) omega := by
  have hzero :
      ManifoldForm.localizedForm I (fun _ : M => (0 : Real)) omega = 0 := by
    funext x
    simp [ManifoldForm.localizedForm]
  rw [localizedFormSum, localizedFormSum]
  simp [selectedPartitionBulkActive, selectedPartitionBulkCoefficient, hzero]

/--
Selected partition reconstruction data for the combined bulk labels.

This is a source constructor for the `localizedEventually` field used by the
project-local automatic bulk a.e. input.  The genuine hypothesis is the usual
support containment for the original form.
-/
def toBulkLocalizedFormEventuallyEqData
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundary : BoundaryPieceFamilyInput I omega BoundaryChart BoundaryPiece)
    (homegaSupport : ManifoldForm.support I omega ⊆ P.K) :
    LocalizedFormEventuallyEqData I omega (M ⊕ BoundaryChart) where
  activeCharts := selectedPartitionBulkActive P boundary
  coefficient := selectedPartitionBulkCoefficient
    (BoundaryChart := BoundaryChart) P
  supportSet := P.K
  localizedFormSum_eq_self_on := by
    intro x hx
    rw [P.localizedFormSum_selectedPartitionBulkActive_eq boundary]
    exact P.localizedFormSum_eqOn x hx
  form_support_subset_supportSet := homegaSupport

@[simp]
theorem toBulkLocalizedFormEventuallyEqData_activeCharts
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundary : BoundaryPieceFamilyInput I omega BoundaryChart BoundaryPiece)
    (homegaSupport : ManifoldForm.support I omega ⊆ P.K) :
    (P.toBulkLocalizedFormEventuallyEqData
      (BoundaryChart := BoundaryChart) boundary homegaSupport).activeCharts =
      selectedPartitionBulkActive P boundary := by
  rfl

@[simp]
theorem toBulkLocalizedFormEventuallyEqData_coefficient
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundary : BoundaryPieceFamilyInput I omega BoundaryChart BoundaryPiece)
    (homegaSupport : ManifoldForm.support I omega ⊆ P.K) :
    (P.toBulkLocalizedFormEventuallyEqData
      (BoundaryChart := BoundaryChart) boundary homegaSupport).coefficient =
      selectedPartitionBulkCoefficient
        (BoundaryChart := BoundaryChart) P := by
  rfl

end SelectedBoxPartitionOfUnity

namespace BulkIntegrandAEProjectLocalAutoInput

/--
Constructor from global localized-form eventual reconstruction data.

The source `LocalizedFormEventuallyEqData` supplies the analytic equality of
the localized finite sum and the original form.  We turn it into a
`PartitionLocalizedEventuallyFields` package with chart support `univ`, so the
measure-support field is automatic for any chosen chartwise measure.
-/
def ofLocalizedFormEventuallyEqData
    (D : LocalizedFormEventuallyEqData I omega (M ⊕ BoundaryChart))
    (R :
      PartitionReconstructionData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hactive : D.activeCharts = selectedPartitionBulkActive P boundary)
    (hcoefficient :
      D.coefficient =
        selectedPartitionBulkCoefficient
          (BoundaryChart := BoundaryChart) P)
    (hactive_reconstruction : D.activeCharts = R.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real)) :
    BulkIntegrandAEProjectLocalAutoInput
      (BoundaryChart := BoundaryChart)
      ExtInteriorPiece ExtBoundaryPiece P boundary localized where
  localizedEventually := D.toPartitionLocalizedEventuallyFieldsOnUniv
  reconstruction := R
  localizedEventually_active := by
    simpa using hactive
  localizedEventually_coefficient := by
    simpa using hcoefficient
  localizedEventually_active_eq_reconstruction := by
    simpa using hactive_reconstruction
  measure := measure
  hmeasureSupport := by
    intro _x0 _x1
    exact Filter.Eventually.of_forall fun _y => by simp

@[simp]
theorem ofLocalizedFormEventuallyEqData_localizedEventually
    (D : LocalizedFormEventuallyEqData I omega (M ⊕ BoundaryChart))
    (R :
      PartitionReconstructionData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hactive : D.activeCharts = selectedPartitionBulkActive P boundary)
    (hcoefficient :
      D.coefficient =
        selectedPartitionBulkCoefficient
          (BoundaryChart := BoundaryChart) P)
    (hactive_reconstruction : D.activeCharts = R.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real)) :
    (ofLocalizedFormEventuallyEqData
      (P := P) (boundary := boundary) (localized := localized)
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      D R hactive hcoefficient hactive_reconstruction measure).localizedEventually =
      D.toPartitionLocalizedEventuallyFieldsOnUniv := by
  rfl

@[simp]
theorem ofLocalizedFormEventuallyEqData_reconstruction
    (D : LocalizedFormEventuallyEqData I omega (M ⊕ BoundaryChart))
    (R :
      PartitionReconstructionData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hactive : D.activeCharts = selectedPartitionBulkActive P boundary)
    (hcoefficient :
      D.coefficient =
        selectedPartitionBulkCoefficient
          (BoundaryChart := BoundaryChart) P)
    (hactive_reconstruction : D.activeCharts = R.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real)) :
    (ofLocalizedFormEventuallyEqData
      (P := P) (boundary := boundary) (localized := localized)
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      D R hactive hcoefficient hactive_reconstruction measure).reconstruction =
      R := by
  rfl

@[simp]
theorem ofLocalizedFormEventuallyEqData_measure
    (D : LocalizedFormEventuallyEqData I omega (M ⊕ BoundaryChart))
    (R :
      PartitionReconstructionData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hactive : D.activeCharts = selectedPartitionBulkActive P boundary)
    (hcoefficient :
      D.coefficient =
        selectedPartitionBulkCoefficient
          (BoundaryChart := BoundaryChart) P)
    (hactive_reconstruction : D.activeCharts = R.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real)) :
    (ofLocalizedFormEventuallyEqData
      (P := P) (boundary := boundary) (localized := localized)
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      D R hactive hcoefficient hactive_reconstruction measure).measure =
      measure := by
  rfl

/--
Constructor specialized to the canonical selected partition and boundary-label
bulk coefficient.  The remaining real inputs are the reconstruction package,
the active-set alignment for that reconstruction, the measure, and the form
support containment used to prove localized-form reconstruction globally.
-/
def ofSelectedPartitionReconstruction
    (R :
      PartitionReconstructionData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hactive_reconstruction :
      selectedPartitionBulkActive P boundary = R.activeCharts)
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
    R rfl rfl hactive_reconstruction measure

@[simp]
theorem ofSelectedPartitionReconstruction_reconstruction
    (R :
      PartitionReconstructionData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hactive_reconstruction :
      selectedPartitionBulkActive P boundary = R.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (homegaSupport : ManifoldForm.support I omega ⊆ P.K) :
    (ofSelectedPartitionReconstruction
      (P := P) (boundary := boundary) (localized := localized)
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      R hactive_reconstruction measure homegaSupport).reconstruction =
      R := by
  rfl

@[simp]
theorem ofSelectedPartitionReconstruction_measure
    (R :
      PartitionReconstructionData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hactive_reconstruction :
      selectedPartitionBulkActive P boundary = R.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (homegaSupport : ManifoldForm.support I omega ⊆ P.K) :
    (ofSelectedPartitionReconstruction
      (P := P) (boundary := boundary) (localized := localized)
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      R hactive_reconstruction measure homegaSupport).measure =
      measure := by
  rfl

end BulkIntegrandAEProjectLocalAutoInput

end BulkExtDerivProjectLocalConstructors

end Stokes

end
