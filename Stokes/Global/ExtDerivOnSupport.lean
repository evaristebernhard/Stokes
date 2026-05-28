import Stokes.Global.ExtDerivReconstruction
import Stokes.Global.LocalizedSupport
import Stokes.Global.PartitionSumOne

/-!
# Exterior-derivative reconstruction on controlled supports

This file records the support-local version of the exterior-derivative
reconstruction layer.  The finite-sum lemmas below are honest algebraic
bridges for `extDeriv` and the project-local `localizedFormSum`; the remaining
support-local reconstruction statement is kept as explicit data so later
compact-support and chart-domain arguments can fill it without changing the
global Stokes bookkeeping layer.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section ExtDerivFiniteSums

universe u v w c

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}

/-- Exterior derivative commutes with a finite sum of differentiable model forms. -/
theorem extDeriv_finset_sum {ι : Type c} (active : Finset ι)
    (ω : ι → ModelForm E k) (y : E)
    (hω : ∀ i ∈ active, DifferentiableAt Real (ω i) y) :
    extDeriv (Finset.sum active fun i => ω i) y =
      Finset.sum active fun i => extDeriv (ω i) y := by
  classical
  revert hω
  refine Finset.induction_on active ?empty ?insert
  · intro _hω
    have hzero : extDeriv (0 : ModelForm E k) y = 0 := by
      rw [extDeriv]
      rw [fderiv_zero]
      ext v
      simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
    simpa using hzero
  · intro i active hi ih hω
    have hωi : DifferentiableAt Real (ω i) y := hω i (by simp [hi])
    have hωactive :
        DifferentiableAt Real (Finset.sum active fun j => ω j) y :=
      DifferentiableAt.sum fun j hj => hω j (Finset.mem_insert_of_mem hj)
    have ih' :
        extDeriv (Finset.sum active fun j => ω j) y =
          Finset.sum active fun j => extDeriv (ω j) y :=
      ih fun j hj => hω j (Finset.mem_insert_of_mem hj)
    calc
      extDeriv (Finset.sum (insert i active) fun j => ω j) y =
          extDeriv (ω i + Finset.sum active fun j => ω j) y := by
        simp [hi]
      _ = extDeriv (ω i) y +
          extDeriv (Finset.sum active fun j => ω j) y :=
        extDeriv_add hωi hωactive
      _ = extDeriv (ω i) y +
          Finset.sum active fun j => extDeriv (ω j) y := by
        rw [ih']
      _ = Finset.sum (insert i active) fun j => extDeriv (ω j) y := by
        simp [hi]

namespace ManifoldForm

/--
Writing a finite localized manifold-form sum in transition coordinates is the
same finite sum of the transition-coordinate representatives.
-/
theorem transitionPullbackInChart_localizedFormSum {Chart : Type c}
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M k) (x0 x1 : M) :
    transitionPullbackInChart I x0 x1
        (localizedFormSum I active coefficient ω) =
      Finset.sum active fun i =>
        transitionPullbackInChart I x0 x1
          (localizedForm I (coefficient i) ω) := by
  classical
  funext y
  ext v
  simp only [localizedFormSum, transitionPullbackInChart, inChart,
    Finset.sum_apply, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]

end ManifoldForm

/--
Exterior derivative of the transition representative of a finite localized sum
is the finite sum of exterior derivatives of the localized representatives,
provided each active localized representative is differentiable at the point.
-/
theorem extDeriv_transitionPullbackInChart_localizedFormSum {Chart : Type c}
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M k) (x0 x1 : M) (y : E)
    (hω :
      ∀ i ∈ active,
        DifferentiableAt Real
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω)) y) :
    extDeriv
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I active coefficient ω)) y =
      Finset.sum active fun i =>
        extDeriv
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω)) y := by
  rw [ManifoldForm.transitionPullbackInChart_localizedFormSum]
  exact extDeriv_finset_sum active
    (fun i =>
      ManifoldForm.transitionPullbackInChart I x0 x1
        (ManifoldForm.localizedForm I (coefficient i) ω)) y hω

end ExtDerivFiniteSums

section ExtDerivOnSupportPackage

universe u v w c i b

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Exterior-derivative reconstruction data on chartwise controlled supports.

The support field is chartwise because `extDeriv` is applied to model-space
chart representatives.  A later compact-support proof can choose
`chartSupport x0 x1` to be the coordinate preimage of the compact support (or a
chart-domain neighborhood of it) and fill `chartwiseExtDeriv_eq_global_on`.
-/
structure ExtDerivOnSupportData {k : Nat}
    (I : ModelWithCorners Real E H) (ω : ManifoldForm I M k)
    (Chart : Type c) (InteriorPiece : Type i) (BoundaryPiece : Type b) where
  /-- Finite chart labels active in the chosen partition/cover. -/
  activeCharts : Finset Chart
  /-- Scalar partition coefficients used to form the localized finite sum. -/
  coefficient : Chart → M → Real
  /-- Coordinate support on which the exterior-derivative reconstruction is known. -/
  chartSupport : M → M → Set E
  /-- Localized interior pieces assigned to an active chart. -/
  interiorPieces : Chart → Finset InteriorPiece
  /-- Localized boundary-chart pieces assigned to an active chart. -/
  boundaryPieces : Chart → Finset BoundaryPiece
  /-- Bulk contribution of an interior local piece. -/
  interiorBulkTerm : Chart → InteriorPiece → Real
  /-- Bulk contribution of a boundary-chart local piece. -/
  boundaryBulkTerm : Chart → BoundaryPiece → Real
  /-- Boundary contribution after chart changes and partition reconstruction. -/
  boundaryPartitionTerm : Chart → BoundaryPiece → Real
  /-- The global bulk integral represented by this reconstruction package. -/
  globalBulkIntegral : Real
  /-- The global boundary integral represented by this reconstruction package. -/
  globalBoundaryIntegral : Real
  /-- Chartwise exterior-derivative reconstruction on the controlled support. -/
  chartwiseExtDeriv_eq_global_on :
    ∀ x0 x1 y, y ∈ chartSupport x0 x1 →
      extDeriv
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (localizedFormSum I activeCharts coefficient ω)) y =
        extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y
  /-- Reconstruction of the global bulk integral from finitely many local pieces. -/
  globalBulkIntegral_eq_localBulkSum :
    globalBulkIntegral =
      (Finset.sum activeCharts fun x =>
          Finset.sum (interiorPieces x) fun q => interiorBulkTerm x q) +
        Finset.sum activeCharts fun x =>
          Finset.sum (boundaryPieces x) fun q => boundaryBulkTerm x q
  /-- Reconstruction of the global boundary integral from the boundary partition. -/
  globalBoundaryIntegral_eq_boundaryPartitionSum :
    globalBoundaryIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun q => boundaryPartitionTerm x q

namespace ExtDerivOnSupportData

variable {k : Nat} {I : ModelWithCorners Real E H}
variable {ω : ManifoldForm I M k}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}

/-- Named accessor for the on-support exterior-derivative reconstruction field. -/
theorem extDeriv_localizedFormSum_eq_global_on
    (D : ExtDerivOnSupportData I ω Chart InteriorPiece BoundaryPiece)
    {x0 x1 : M} {y : E} (hy : y ∈ D.chartSupport x0 x1) :
    extDeriv
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I D.activeCharts D.coefficient ω)) y =
      extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y :=
  D.chartwiseExtDeriv_eq_global_on x0 x1 y hy

/-- Forget the support-local exterior-derivative field. -/
def toPartitionReconstructionData
    (D : ExtDerivOnSupportData I ω Chart InteriorPiece BoundaryPiece) :
    PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece where
  activeCharts := D.activeCharts
  interiorPieces := D.interiorPieces
  boundaryPieces := D.boundaryPieces
  interiorBulkTerm := D.interiorBulkTerm
  boundaryBulkTerm := D.boundaryBulkTerm
  boundaryPartitionTerm := D.boundaryPartitionTerm
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum := D.globalBulkIntegral_eq_localBulkSum
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    D.globalBoundaryIntegral_eq_boundaryPartitionSum

/--
Promote on-support reconstruction data to the existing global
exterior-derivative reconstruction package when the controlled chart supports
cover all model-space points relevant to the package.
-/
def toExtDerivPartitionReconstructionData
    (D : ExtDerivOnSupportData I ω Chart InteriorPiece BoundaryPiece)
    (hcover : ∀ x0 x1 y, y ∈ D.chartSupport x0 x1) :
    ExtDerivPartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece where
  activeCharts := D.activeCharts
  coefficient := D.coefficient
  interiorPieces := D.interiorPieces
  boundaryPieces := D.boundaryPieces
  interiorBulkTerm := D.interiorBulkTerm
  boundaryBulkTerm := D.boundaryBulkTerm
  boundaryPartitionTerm := D.boundaryPartitionTerm
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral
  chartwiseExtDeriv_eq_global := fun x0 x1 y =>
    D.chartwiseExtDeriv_eq_global_on x0 x1 y (hcover x0 x1 y)
  globalBulkIntegral_eq_localBulkSum := D.globalBulkIntegral_eq_localBulkSum
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    D.globalBoundaryIntegral_eq_boundaryPartitionSum

/-- Build on-support exterior-derivative data from an existing reconstruction package. -/
def ofPartitionReconstructionData
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (coefficient : Chart → M → Real)
    (chartSupport : M → M → Set E)
    (hext :
      ∀ x0 x1 y, y ∈ chartSupport x0 x1 →
        extDeriv
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (localizedFormSum I R.activeCharts coefficient ω)) y =
          extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y) :
    ExtDerivOnSupportData I ω Chart InteriorPiece BoundaryPiece where
  activeCharts := R.activeCharts
  coefficient := coefficient
  chartSupport := chartSupport
  interiorPieces := R.interiorPieces
  boundaryPieces := R.boundaryPieces
  interiorBulkTerm := R.interiorBulkTerm
  boundaryBulkTerm := R.boundaryBulkTerm
  boundaryPartitionTerm := R.boundaryPartitionTerm
  globalBulkIntegral := R.globalBulkIntegral
  globalBoundaryIntegral := R.globalBoundaryIntegral
  chartwiseExtDeriv_eq_global_on := hext
  globalBulkIntegral_eq_localBulkSum := R.globalBulkIntegral_eq_localBulkSum
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    R.globalBoundaryIntegral_eq_boundaryPartitionSum

@[simp]
theorem toPartitionReconstructionData_activeCharts
    (D : ExtDerivOnSupportData I ω Chart InteriorPiece BoundaryPiece) :
    D.toPartitionReconstructionData.activeCharts = D.activeCharts :=
  rfl

@[simp]
theorem toPartitionReconstructionData_globalBulkIntegral
    (D : ExtDerivOnSupportData I ω Chart InteriorPiece BoundaryPiece) :
    D.toPartitionReconstructionData.globalBulkIntegral = D.globalBulkIntegral :=
  rfl

@[simp]
theorem toPartitionReconstructionData_globalBoundaryIntegral
    (D : ExtDerivOnSupportData I ω Chart InteriorPiece BoundaryPiece) :
    D.toPartitionReconstructionData.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

section CompactSupport

/-- Coordinate preimage of a manifold support set, written for chart representatives. -/
def chartPreimageSupport (I : ModelWithCorners Real E H) (K : Set M)
    (x0 _x1 : M) : Set E :=
  {y | (extChartAt I x0).symm y ∈ K}

/--
Compact-support constructor: use the coordinate preimage of a compact manifold
support set as the chartwise support in `ExtDerivOnSupportData`.
-/
def ofCompactSupport
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (coefficient : Chart → M → Real)
    (K : Set M) (_hK : IsCompact K)
    (hext :
      ∀ x0 x1 y, (extChartAt I x0).symm y ∈ K →
        extDeriv
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (localizedFormSum I R.activeCharts coefficient ω)) y =
          extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y) :
    ExtDerivOnSupportData I ω Chart InteriorPiece BoundaryPiece :=
  ofPartitionReconstructionData R coefficient (chartPreimageSupport I K)
    (by
      intro x0 x1 y hy
      exact hext x0 x1 y hy)

@[simp]
theorem ofCompactSupport_chartSupport
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (coefficient : Chart → M → Real)
    (K : Set M) (hK : IsCompact K)
    (hext :
      ∀ x0 x1 y, (extChartAt I x0).symm y ∈ K →
        extDeriv
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (localizedFormSum I R.activeCharts coefficient ω)) y =
          extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y)
    (x0 x1 : M) :
    (ofCompactSupport R coefficient K hK hext).chartSupport x0 x1 =
      chartPreimageSupport I K x0 x1 :=
  rfl

end CompactSupport

end ExtDerivOnSupportData

end ExtDerivOnSupportPackage

end Stokes

end
