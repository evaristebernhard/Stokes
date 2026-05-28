import Stokes.Global.ExtDerivEventually
import Stokes.Global.PartitionLocalizedEventually
import Stokes.Global.ExtDerivPartitionConstructor
import Stokes.Global.BulkIntegralPartitionReconstruction

/-!
# A.e. equality input for bulk integrands

This file supplies the measure-theoretic handoff needed by the bulk-integral
localization layer.  The current global API has not yet introduced a canonical
manifold bulk-integrand definition, so we package the chartwise scalar
top-degree integrand used by the existing project-local bulk integrals:

`y ↦ extDeriv (transitionPullbackInChart ... ω) y (standardTopFrame n)`.

The constructors below turn the already established partition-local eventual
equality and exterior-derivative reconstruction packages into the corresponding
a.e. equality of scalar bulk integrands.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkIntegrand

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
The scalar chartwise top-degree bulk integrand used by the local Stokes
wrappers.

This is intentionally a project-facing definition: once the final manifold
integrand API exists, `BulkIntegrandAEData` can be re-targeted to that
definition without changing the downstream a.e.-equality handoff.
-/
def bulkIntegrand {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) :
    (Fin (n + 1) → Real) → Real :=
  fun y =>
    extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y
      (standardTopFrame n)

/-- Apply an equality of exterior derivatives to the standard top frame. -/
theorem bulkIntegrand_apply_eq_of_extDeriv_eq {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω₁ ω₂ : ManifoldForm I M n} {x0 x1 : M} {y : Fin (n + 1) → Real}
    (hext :
      extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω₁) y =
        extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω₂) y) :
    bulkIntegrand I x0 x1 ω₁ y = bulkIntegrand I x0 x1 ω₂ y := by
  simpa [bulkIntegrand] using
    congrArg (fun η => η (standardTopFrame n)) hext

/--
Pointwise exterior-derivative equality gives a.e. equality of the scalar bulk
integrands for any chartwise measure.
-/
theorem bulkIntegrand_ae_eq_of_forall_extDeriv_eq {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω₁ ω₂ : ManifoldForm I M n}
    (μ : Measure (Fin (n + 1) → Real)) {x0 x1 : M}
    (hext :
      ∀ y,
        extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω₁) y =
          extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω₂) y) :
    bulkIntegrand I x0 x1 ω₁ =ᵐ[μ] bulkIntegrand I x0 x1 ω₂ :=
  Filter.Eventually.of_forall fun y =>
    bulkIntegrand_apply_eq_of_extDeriv_eq (I := I) (x0 := x0) (x1 := x1)
      (ω₁ := ω₁) (ω₂ := ω₂) (y := y) (hext y)

end BulkIntegrand

section BulkIntegrandAEPackage

universe u w c i b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
A.e. equality data for the chartwise scalar bulk integrand.

The measure is chart-pair dependent so worker layers can instantiate it with
box-restricted volume, chart-image measures, or any later canonical integration
measure.  The single analytic field is the a.e. equality needed to replace the
partition-localized bulk integrand by the original one.
-/
structure BulkIntegrandAEData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n) (Chart : Type c) where
  /-- Finite partition/chart labels used in the localized finite sum. -/
  activeCharts : Finset Chart
  /-- Scalar partition coefficients used to form the localized finite sum. -/
  coefficient : Chart → M → Real
  /-- The chartwise measure with respect to which bulk integrands are compared. -/
  measure : M → M → Measure (Fin (n + 1) → Real)
  /-- A.e. equality of the localized and global scalar bulk integrands. -/
  bulkIntegrand_ae_eq_global :
    ∀ x0 x1,
      bulkIntegrand I x0 x1
          (localizedFormSum I activeCharts coefficient ω) =ᵐ[measure x0 x1]
        bulkIntegrand I x0 x1 ω

namespace BulkIntegrandAEData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}

/-- Named accessor for the stored a.e. bulk-integrand equality. -/
theorem ae_eq_global
    (D : BulkIntegrandAEData I ω Chart) (x0 x1 : M) :
    bulkIntegrand I x0 x1
        (localizedFormSum I D.activeCharts D.coefficient ω) =ᵐ[D.measure x0 x1]
      bulkIntegrand I x0 x1 ω :=
  D.bulkIntegrand_ae_eq_global x0 x1

/-- Build a.e. bulk-integrand data from pointwise chartwise `extDeriv` equality. -/
def ofExtDerivEq
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hext :
      ∀ x0 x1 y,
        extDeriv
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (localizedFormSum I active coefficient ω)) y =
          extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y) :
    BulkIntegrandAEData I ω Chart where
  activeCharts := active
  coefficient := coefficient
  measure := measure
  bulkIntegrand_ae_eq_global := fun x0 x1 =>
    bulkIntegrand_ae_eq_of_forall_extDeriv_eq (I := I)
      (ω₁ := localizedFormSum I active coefficient ω) (ω₂ := ω)
      (μ := measure x0 x1) (x0 := x0) (x1 := x1)
      (hext x0 x1)

/--
Build a.e. bulk-integrand data from on-support exterior-derivative
reconstruction, assuming the controlled support holds a.e. for the requested
chartwise measures.
-/
def ofExtDerivOnSupportData
    (D : ExtDerivOnSupportData I ω Chart InteriorPiece BoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1), y ∈ D.chartSupport x0 x1) :
    BulkIntegrandAEData I ω Chart where
  activeCharts := D.activeCharts
  coefficient := D.coefficient
  measure := measure
  bulkIntegrand_ae_eq_global := by
    intro x0 x1
    exact (hmeasureSupport x0 x1).mono fun y hy =>
      bulkIntegrand_apply_eq_of_extDeriv_eq (I := I) (x0 := x0) (x1 := x1)
        (ω₁ := localizedFormSum I D.activeCharts D.coefficient ω) (ω₂ := ω)
        (y := y) (D.extDeriv_localizedFormSum_eq_global_on hy)

/--
Projection theorem for data built from on-support exterior-derivative
reconstruction.
-/
theorem ofExtDerivOnSupportData_ae_eq_global
    (D : ExtDerivOnSupportData I ω Chart InteriorPiece BoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1), y ∈ D.chartSupport x0 x1)
    (x0 x1 : M) :
    bulkIntegrand I x0 x1
        (localizedFormSum I D.activeCharts D.coefficient ω) =ᵐ[measure x0 x1]
      bulkIntegrand I x0 x1 ω :=
  (ofExtDerivOnSupportData (I := I) (ω := ω) D measure hmeasureSupport)
    |>.ae_eq_global x0 x1

/--
Build a.e. bulk-integrand data from on-support reconstruction when the support
covers every model-space point.
-/
def ofExtDerivOnSupportData_cover
    (D : ExtDerivOnSupportData I ω Chart InteriorPiece BoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hcover : ∀ x0 x1 y, y ∈ D.chartSupport x0 x1) :
    BulkIntegrandAEData I ω Chart :=
  ofExtDerivOnSupportData D measure fun x0 x1 =>
    Filter.Eventually.of_forall fun y => hcover x0 x1 y

/--
Build a.e. bulk-integrand data from the eventual-equality package, with
chart-support membership holding a.e. for the requested measures.
-/
def ofExtDerivEventuallyEqData
    (D : ExtDerivEventuallyEqData I ω Chart InteriorPiece BoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1), y ∈ D.chartSupport x0 x1) :
    BulkIntegrandAEData I ω Chart :=
  ofExtDerivOnSupportData D.toExtDerivOnSupportData measure hmeasureSupport

/--
Projection theorem for data built from the eventual-equality exterior-derivative
package.
-/
theorem ofExtDerivEventuallyEqData_ae_eq_global
    (D : ExtDerivEventuallyEqData I ω Chart InteriorPiece BoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1), y ∈ D.chartSupport x0 x1)
    (x0 x1 : M) :
    bulkIntegrand I x0 x1
        (localizedFormSum I D.activeCharts D.coefficient ω) =ᵐ[measure x0 x1]
      bulkIntegrand I x0 x1 ω :=
  (ofExtDerivEventuallyEqData (I := I) (ω := ω) D measure hmeasureSupport)
    |>.ae_eq_global x0 x1

/--
Build a.e. bulk-integrand data from the global exterior-derivative
reconstruction package.
-/
def ofExtDerivPartitionReconstructionData
    (D : ExtDerivPartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real)) :
    BulkIntegrandAEData I ω Chart :=
  ofExtDerivEq D.activeCharts D.coefficient measure
    D.chartwiseExtDeriv_eq_global

/--
Projection theorem for data built from global exterior-derivative
reconstruction.
-/
theorem ofExtDerivPartitionReconstructionData_ae_eq_global
    (D : ExtDerivPartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (x0 x1 : M) :
    bulkIntegrand I x0 x1
        (localizedFormSum I D.activeCharts D.coefficient ω) =ᵐ[measure x0 x1]
      bulkIntegrand I x0 x1 ω :=
  (ofExtDerivPartitionReconstructionData (I := I) (ω := ω) D measure)
    |>.ae_eq_global x0 x1

/--
Build a.e. bulk-integrand data from the compact-support partition constructor.
-/
def ofPartitionExtDerivConstructorData
    (D : PartitionExtDerivConstructorData I ω Chart InteriorPiece BoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real)) :
    BulkIntegrandAEData I ω Chart :=
  ofExtDerivPartitionReconstructionData
    D.toExtDerivPartitionReconstructionData measure

/--
Projection theorem for data built from the compact-support partition
constructor.
-/
theorem ofPartitionExtDerivConstructorData_ae_eq_global
    (D : PartitionExtDerivConstructorData I ω Chart InteriorPiece BoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (x0 x1 : M) :
    bulkIntegrand I x0 x1
        (localizedFormSum I D.extDerivOnSupport.activeCharts
          D.extDerivOnSupport.coefficient ω) =ᵐ[measure x0 x1]
      bulkIntegrand I x0 x1 ω :=
  (ofPartitionExtDerivConstructorData (I := I) (ω := ω) D measure)
    |>.ae_eq_global x0 x1

/--
Build a.e. bulk-integrand data directly from partition-local eventual equality
and a reconstruction package.
-/
def ofPartitionLocalizedEventuallyFields
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (L : PartitionLocalizedEventuallyFields I ω Chart)
    (hactive : L.activeCharts = R.activeCharts)
    (hcover : ∀ x0 x1 y, y ∈ L.chartSupport x0 x1)
    (measure : M → M → Measure (Fin (n + 1) → Real)) :
    BulkIntegrandAEData I ω Chart :=
  ofPartitionExtDerivConstructorData
    (PartitionExtDerivConstructorData.ofPartitionReconstructionData
      R L hactive hcover)
    measure

/--
Projection theorem for data built directly from partition-local eventual
equality and a reconstruction package.
-/
theorem ofPartitionLocalizedEventuallyFields_ae_eq_global
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (L : PartitionLocalizedEventuallyFields I ω Chart)
    (hactive : L.activeCharts = R.activeCharts)
    (hcover : ∀ x0 x1 y, y ∈ L.chartSupport x0 x1)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (x0 x1 : M) :
    bulkIntegrand I x0 x1
        (localizedFormSum I R.activeCharts L.coefficient ω) =ᵐ[measure x0 x1]
      bulkIntegrand I x0 x1 ω :=
  (ofPartitionLocalizedEventuallyFields (I := I) (ω := ω)
      R L hactive hcover measure)
    |>.ae_eq_global x0 x1

/--
Build a.e. bulk-integrand data from the global localized-form eventual-equality
package in `PartitionLocalizedEventually`.
-/
def ofLocalizedFormEventuallyEqData
    (D : LocalizedFormEventuallyEqData I ω Chart)
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (hactive : R.activeCharts = D.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real)) :
    BulkIntegrandAEData I ω Chart :=
  ofExtDerivPartitionReconstructionData
    (D.toExtDerivPartitionReconstructionData R hactive)
    measure

/--
Projection theorem for data built from the partition-localized eventual
equality package.
-/
theorem ofLocalizedFormEventuallyEqData_ae_eq_global
    (D : LocalizedFormEventuallyEqData I ω Chart)
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (hactive : R.activeCharts = D.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (x0 x1 : M) :
    bulkIntegrand I x0 x1
        (localizedFormSum I R.activeCharts D.coefficient ω) =ᵐ[measure x0 x1]
      bulkIntegrand I x0 x1 ω :=
  (ofLocalizedFormEventuallyEqData (I := I) (ω := ω) D R hactive measure)
    |>.ae_eq_global x0 x1

@[simp]
theorem ofExtDerivEq_activeCharts
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hext :
      ∀ x0 x1 y,
        extDeriv
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (localizedFormSum I active coefficient ω)) y =
          extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y) :
    (ofExtDerivEq (I := I) (ω := ω) active coefficient measure hext).activeCharts =
      active :=
  rfl

@[simp]
theorem ofExtDerivEq_coefficient
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hext :
      ∀ x0 x1 y,
        extDeriv
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (localizedFormSum I active coefficient ω)) y =
          extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y) :
    (ofExtDerivEq (I := I) (ω := ω) active coefficient measure hext).coefficient =
      coefficient :=
  rfl

@[simp]
theorem ofExtDerivPartitionReconstructionData_activeCharts
    (D : ExtDerivPartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real)) :
    (ofExtDerivPartitionReconstructionData D measure).activeCharts =
      D.activeCharts :=
  rfl

@[simp]
theorem ofExtDerivPartitionReconstructionData_coefficient
    (D : ExtDerivPartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real)) :
    (ofExtDerivPartitionReconstructionData D measure).coefficient =
      D.coefficient :=
  rfl

end BulkIntegrandAEData

end BulkIntegrandAEPackage

end Stokes

end
