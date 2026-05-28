import Stokes.Global.ExtDerivOnSupport

/-!
# Partition/exterior-derivative reconstruction constructor

This file is a thin handoff layer for the compact-support partition route.
It keeps the existing `ExtDerivOnSupportData` package as the source of the
actual exterior-derivative reconstruction field, while also recording the
partition-local eventual equality and support-cover data that explain why this
is the right package for a selected partition.

There is no dependency on a separate `PartitionLocalizedEventually` module:
the local-equality inputs are recorded here as an independent field package.
-/

noncomputable section

open Set Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section PartitionLocalizedEventuallyFields

universe u v w c

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}
variable {ω : ManifoldForm I M k}
variable {Chart : Type c}

/--
Partition-local reconstruction and local equality data.

The `localizedFormSum_eq_self_on` field is the manifold-side reconstruction
usually obtained from `PartitionSumOne`.  The `chartwiseEventuallyEq_on` field
is the model-space local equality that can identify exterior derivatives at a
point.  The chart support is kept explicit so it can be aligned with
`ExtDerivOnSupportData`.
-/
structure PartitionLocalizedEventuallyFields
    (I : ModelWithCorners Real E H) (ω : ManifoldForm I M k)
    (Chart : Type c) where
  /-- Finite partition/chart labels used in the localized sum. -/
  activeCharts : Finset Chart
  /-- Scalar partition coefficients for the localized forms. -/
  coefficient : Chart → M → Real
  /-- Manifold support set where the localized sum reconstructs `ω`. -/
  supportSet : Set M
  /-- Chartwise model support on which the local equality is known. -/
  chartSupport : M → M → Set E
  /-- Coordinate preimages of the manifold support lie in the chart support. -/
  support_preimage_subset_chartSupport :
    ∀ x0 x1 y, (extChartAt I x0).symm y ∈ supportSet →
      y ∈ chartSupport x0 x1
  /-- Pointwise reconstruction of the localized finite sum on `supportSet`. -/
  localizedFormSum_eq_self_on :
    ∀ x ∈ supportSet, localizedFormSum I activeCharts coefficient ω x = ω x
  /--
  Local equality of chart representatives on the chartwise support.

  This is intentionally stronger and more directly usable for `extDeriv` than
  the manifold-side pointwise equality.
  -/
  chartwiseEventuallyEq_on :
    ∀ x0 x1 y, y ∈ chartSupport x0 x1 →
      ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I activeCharts coefficient ω) =ᶠ[𝓝 y]
        ManifoldForm.transitionPullbackInChart I x0 x1 ω

namespace PartitionLocalizedEventuallyFields

/-- Constructor from a coefficient-sum-one theorem and chartwise eventual equality. -/
def ofCoeffSumEqOneOn
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (supportSet : Set M) (chartSupport : M → M → Set E)
    (hsupport :
      ∀ x0 x1 y, (extChartAt I x0).symm y ∈ supportSet →
        y ∈ chartSupport x0 x1)
    (hsum :
      ∀ x ∈ supportSet, (Finset.sum active fun i => coefficient i x) = 1)
    (heventually :
      ∀ x0 x1 y, y ∈ chartSupport x0 x1 →
        ManifoldForm.transitionPullbackInChart I x0 x1
            (localizedFormSum I active coefficient ω) =ᶠ[𝓝 y]
          ManifoldForm.transitionPullbackInChart I x0 x1 ω) :
    PartitionLocalizedEventuallyFields I ω Chart where
  activeCharts := active
  coefficient := coefficient
  supportSet := supportSet
  chartSupport := chartSupport
  support_preimage_subset_chartSupport := hsupport
  localizedFormSum_eq_self_on :=
    localizedFormSum_eqOn_of_coeff_sum_eq_one_on active coefficient ω hsum
  chartwiseEventuallyEq_on := heventually

/-- Constructor from an already proved localized-form reconstruction theorem. -/
def ofEqOn
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (supportSet : Set M) (chartSupport : M → M → Set E)
    (hsupport :
      ∀ x0 x1 y, (extChartAt I x0).symm y ∈ supportSet →
        y ∈ chartSupport x0 x1)
    (hlocalized :
      ∀ x ∈ supportSet, localizedFormSum I active coefficient ω x = ω x)
    (heventually :
      ∀ x0 x1 y, y ∈ chartSupport x0 x1 →
        ManifoldForm.transitionPullbackInChart I x0 x1
            (localizedFormSum I active coefficient ω) =ᶠ[𝓝 y]
          ManifoldForm.transitionPullbackInChart I x0 x1 ω) :
    PartitionLocalizedEventuallyFields I ω Chart where
  activeCharts := active
  coefficient := coefficient
  supportSet := supportSet
  chartSupport := chartSupport
  support_preimage_subset_chartSupport := hsupport
  localizedFormSum_eq_self_on := hlocalized
  chartwiseEventuallyEq_on := heventually

/-- Exterior-derivative equality obtained from the stored chartwise eventual equality. -/
theorem extDeriv_localizedFormSum_eq_global_on
    (L : PartitionLocalizedEventuallyFields I ω Chart)
    {x0 x1 : M} {y : E} (hy : y ∈ L.chartSupport x0 x1) :
    extDeriv
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I L.activeCharts L.coefficient ω)) y =
      extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y :=
  (L.chartwiseEventuallyEq_on x0 x1 y hy).extDeriv_eq

/-- Build on-support exterior-derivative data from reconstruction and local equality data. -/
def toExtDerivOnSupportData
    {InteriorPiece : Type*} {BoundaryPiece : Type*}
    (L : PartitionLocalizedEventuallyFields I ω Chart)
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (hactive : L.activeCharts = R.activeCharts) :
    ExtDerivOnSupportData I ω Chart InteriorPiece BoundaryPiece where
  activeCharts := R.activeCharts
  coefficient := L.coefficient
  chartSupport := L.chartSupport
  interiorPieces := R.interiorPieces
  boundaryPieces := R.boundaryPieces
  interiorBulkTerm := R.interiorBulkTerm
  boundaryBulkTerm := R.boundaryBulkTerm
  boundaryPartitionTerm := R.boundaryPartitionTerm
  globalBulkIntegral := R.globalBulkIntegral
  globalBoundaryIntegral := R.globalBoundaryIntegral
  chartwiseExtDeriv_eq_global_on := by
    intro x0 x1 y hy
    have h := L.extDeriv_localizedFormSum_eq_global_on (x0 := x0) (x1 := x1) hy
    simpa [hactive] using h
  globalBulkIntegral_eq_localBulkSum := R.globalBulkIntegral_eq_localBulkSum
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    R.globalBoundaryIntegral_eq_boundaryPartitionSum

@[simp]
theorem ofCoeffSumEqOneOn_activeCharts
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (supportSet : Set M) (chartSupport : M → M → Set E)
    (hsupport :
      ∀ x0 x1 y, (extChartAt I x0).symm y ∈ supportSet →
        y ∈ chartSupport x0 x1)
    (hsum :
      ∀ x ∈ supportSet, (Finset.sum active fun i => coefficient i x) = 1)
    (heventually :
      ∀ x0 x1 y, y ∈ chartSupport x0 x1 →
        ManifoldForm.transitionPullbackInChart I x0 x1
            (localizedFormSum I active coefficient ω) =ᶠ[𝓝 y]
          ManifoldForm.transitionPullbackInChart I x0 x1 ω) :
    (ofCoeffSumEqOneOn (I := I) (ω := ω) active coefficient supportSet chartSupport
        hsupport hsum heventually).activeCharts = active :=
  rfl

@[simp]
theorem ofEqOn_activeCharts
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (supportSet : Set M) (chartSupport : M → M → Set E)
    (hsupport :
      ∀ x0 x1 y, (extChartAt I x0).symm y ∈ supportSet →
        y ∈ chartSupport x0 x1)
    (hlocalized :
      ∀ x ∈ supportSet, localizedFormSum I active coefficient ω x = ω x)
    (heventually :
      ∀ x0 x1 y, y ∈ chartSupport x0 x1 →
        ManifoldForm.transitionPullbackInChart I x0 x1
            (localizedFormSum I active coefficient ω) =ᶠ[𝓝 y]
          ManifoldForm.transitionPullbackInChart I x0 x1 ω) :
    (ofEqOn (I := I) (ω := ω) active coefficient supportSet chartSupport
        hsupport hlocalized heventually).activeCharts = active :=
  rfl

end PartitionLocalizedEventuallyFields

end PartitionLocalizedEventuallyFields

section PartitionExtDerivConstructor

universe u v w c i b

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}
variable {ω : ManifoldForm I M k}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}

/--
Constructor data aligning partition-local equality, support coverage, and the
existing exterior-derivative-on-support reconstruction package.

The wrappers below deliberately return the existing reconstruction records;
this structure only records the alignment facts needed to treat the
partition-local package as the source of those records.
-/
structure PartitionExtDerivConstructorData
    (I : ModelWithCorners Real E H) (ω : ManifoldForm I M k)
    (Chart : Type c) (InteriorPiece : Type i) (BoundaryPiece : Type b) where
  /-- Existing exterior-derivative reconstruction package on chart supports. -/
  extDerivOnSupport :
    ExtDerivOnSupportData I ω Chart InteriorPiece BoundaryPiece
  /-- Partition-local reconstruction and chartwise eventual equality data. -/
  localizedEventually : PartitionLocalizedEventuallyFields I ω Chart
  /-- The localized package uses the same active set as the reconstruction package. -/
  activeCharts_eq :
    localizedEventually.activeCharts = extDerivOnSupport.activeCharts
  /-- The localized package uses the same coefficient family. -/
  coefficient_eq :
    localizedEventually.coefficient = extDerivOnSupport.coefficient
  /-- The localized package uses the same chartwise support sets. -/
  chartSupport_eq :
    localizedEventually.chartSupport = extDerivOnSupport.chartSupport
  /-- The chartwise supports cover every model-space point needed for promotion. -/
  chartSupport_cover :
    ∀ x0 x1 y, y ∈ extDerivOnSupport.chartSupport x0 x1

namespace PartitionExtDerivConstructorData

/-- Forget the partition/eventual-equality bookkeeping. -/
def toPartitionReconstructionData
    (D : PartitionExtDerivConstructorData I ω Chart InteriorPiece BoundaryPiece) :
    PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece :=
  D.extDerivOnSupport.toPartitionReconstructionData

/--
Promote to the global chartwise exterior-derivative reconstruction package,
using the stored chart-support cover.
-/
def toExtDerivPartitionReconstructionData
    (D : PartitionExtDerivConstructorData I ω Chart InteriorPiece BoundaryPiece) :
    ExtDerivPartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece :=
  D.extDerivOnSupport.toExtDerivPartitionReconstructionData
    D.chartSupport_cover

/--
Constructor from a `PartitionReconstructionData` package and local eventual
equality data.  This is the clean-room replacement for a missing
`PartitionLocalizedEventually` dependency.
-/
def ofPartitionReconstructionData
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (L : PartitionLocalizedEventuallyFields I ω Chart)
    (hactive : L.activeCharts = R.activeCharts)
    (hcover : ∀ x0 x1 y, y ∈ L.chartSupport x0 x1) :
    PartitionExtDerivConstructorData I ω Chart InteriorPiece BoundaryPiece where
  extDerivOnSupport := L.toExtDerivOnSupportData R hactive
  localizedEventually := L
  activeCharts_eq := by
    simpa [PartitionLocalizedEventuallyFields.toExtDerivOnSupportData] using hactive
  coefficient_eq := rfl
  chartSupport_eq := rfl
  chartSupport_cover := by
    intro x0 x1 y
    exact hcover x0 x1 y

/-- Localized-form reconstruction restated using the aligned reconstruction fields. -/
theorem localizedFormSum_eq_self_on
    (D : PartitionExtDerivConstructorData I ω Chart InteriorPiece BoundaryPiece) :
    ∀ x ∈ D.localizedEventually.supportSet,
      localizedFormSum I D.extDerivOnSupport.activeCharts
        D.extDerivOnSupport.coefficient ω x = ω x := by
  intro x hx
  have h := D.localizedEventually.localizedFormSum_eq_self_on x hx
  simpa [D.activeCharts_eq, D.coefficient_eq] using h

/-- Chartwise eventual equality restated using the aligned reconstruction fields. -/
theorem chartwiseEventuallyEq_on
    (D : PartitionExtDerivConstructorData I ω Chart InteriorPiece BoundaryPiece)
    {x0 x1 : M} {y : E} (hy : y ∈ D.extDerivOnSupport.chartSupport x0 x1) :
    ManifoldForm.transitionPullbackInChart I x0 x1
        (localizedFormSum I D.extDerivOnSupport.activeCharts
          D.extDerivOnSupport.coefficient ω) =ᶠ[𝓝 y]
      ManifoldForm.transitionPullbackInChart I x0 x1 ω := by
  have hlocal : y ∈ D.localizedEventually.chartSupport x0 x1 := by
    simpa [D.chartSupport_eq] using hy
  have h := D.localizedEventually.chartwiseEventuallyEq_on x0 x1 y hlocal
  simpa [D.activeCharts_eq, D.coefficient_eq] using h

/-- Exterior-derivative equality obtained from the aligned eventual-equality package. -/
theorem extDeriv_localizedFormSum_eq_global_on
    (D : PartitionExtDerivConstructorData I ω Chart InteriorPiece BoundaryPiece)
    {x0 x1 : M} {y : E} (hy : y ∈ D.extDerivOnSupport.chartSupport x0 x1) :
    extDeriv
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I D.extDerivOnSupport.activeCharts
            D.extDerivOnSupport.coefficient ω)) y =
      extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y :=
  (D.chartwiseEventuallyEq_on hy).extDeriv_eq

@[simp]
theorem toPartitionReconstructionData_activeCharts
    (D : PartitionExtDerivConstructorData I ω Chart InteriorPiece BoundaryPiece) :
    D.toPartitionReconstructionData.activeCharts =
      D.extDerivOnSupport.activeCharts :=
  rfl

@[simp]
theorem toPartitionReconstructionData_globalBulkIntegral
    (D : PartitionExtDerivConstructorData I ω Chart InteriorPiece BoundaryPiece) :
    D.toPartitionReconstructionData.globalBulkIntegral =
      D.extDerivOnSupport.globalBulkIntegral :=
  rfl

@[simp]
theorem toPartitionReconstructionData_globalBoundaryIntegral
    (D : PartitionExtDerivConstructorData I ω Chart InteriorPiece BoundaryPiece) :
    D.toPartitionReconstructionData.globalBoundaryIntegral =
      D.extDerivOnSupport.globalBoundaryIntegral :=
  rfl

@[simp]
theorem toExtDerivPartitionReconstructionData_activeCharts
    (D : PartitionExtDerivConstructorData I ω Chart InteriorPiece BoundaryPiece) :
    D.toExtDerivPartitionReconstructionData.activeCharts =
      D.extDerivOnSupport.activeCharts :=
  rfl

@[simp]
theorem toExtDerivPartitionReconstructionData_coefficient
    (D : PartitionExtDerivConstructorData I ω Chart InteriorPiece BoundaryPiece) :
    D.toExtDerivPartitionReconstructionData.coefficient =
      D.extDerivOnSupport.coefficient :=
  rfl

@[simp]
theorem toExtDerivPartitionReconstructionData_globalBulkIntegral
    (D : PartitionExtDerivConstructorData I ω Chart InteriorPiece BoundaryPiece) :
    D.toExtDerivPartitionReconstructionData.globalBulkIntegral =
      D.extDerivOnSupport.globalBulkIntegral :=
  rfl

@[simp]
theorem toExtDerivPartitionReconstructionData_globalBoundaryIntegral
    (D : PartitionExtDerivConstructorData I ω Chart InteriorPiece BoundaryPiece) :
    D.toExtDerivPartitionReconstructionData.globalBoundaryIntegral =
      D.extDerivOnSupport.globalBoundaryIntegral :=
  rfl

end PartitionExtDerivConstructorData

end PartitionExtDerivConstructor

end Stokes

end
