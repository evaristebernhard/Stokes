import Stokes.Global.ExtDerivOnSupport

/-!
# Exterior derivatives of eventually equal chart representatives

This file packages the local nature of `extDeriv` in the shape used by the
global Stokes reconstruction layer.  The analytic input is local equality of
model-space chart representatives, expressed either as `EventuallyEq` at the
point or as equality on a set that is a neighborhood of the point.
-/

noncomputable section

open Set Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section ModelForms

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {k : Nat} {ω₁ ω₂ : ModelForm E k} {y : E}

/-- Eventually equal model forms have equal exterior derivatives at the point. -/
theorem extDeriv_eq_of_eventuallyEq
    (hω : ω₁ =ᶠ[𝓝 y] ω₂) :
    extDeriv ω₁ y = extDeriv ω₂ y :=
  hω.extDeriv_eq

/--
Equality on a neighborhood of the point is enough to identify exterior
derivatives at the point.
-/
theorem extDeriv_eq_of_eqOn_mem_nhds {s : Set E}
    (hs : s ∈ 𝓝 y) (hω : EqOn ω₁ ω₂ s) :
    extDeriv ω₁ y = extDeriv ω₂ y :=
  extDeriv_eq_of_eventuallyEq (eventually_of_mem hs hω)

/--
Differentiability hypotheses are often available in chart applications; the
local equality, not the global behavior, is what determines `extDeriv` at the
point.
-/
theorem extDeriv_eq_of_eventuallyEq_differentiableAt
    (hω : ω₁ =ᶠ[𝓝 y] ω₂)
    (_hω₁ : DifferentiableAt Real ω₁ y)
    (_hω₂ : DifferentiableAt Real ω₂ y) :
    extDeriv ω₁ y = extDeriv ω₂ y :=
  extDeriv_eq_of_eventuallyEq hω

/--
Differentiability-friendly neighborhood version of
`extDeriv_eq_of_eqOn_mem_nhds`.
-/
theorem extDeriv_eq_of_eqOn_mem_nhds_differentiableAt {s : Set E}
    (hs : s ∈ 𝓝 y) (hω : EqOn ω₁ ω₂ s)
    (_hω₁ : DifferentiableAt Real ω₁ y)
    (_hω₂ : DifferentiableAt Real ω₂ y) :
    extDeriv ω₁ y = extDeriv ω₂ y :=
  extDeriv_eq_of_eqOn_mem_nhds hs hω

end ModelForms

section ChartRepresentatives

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}
variable {ω₁ ω₂ : ManifoldForm I M k} {x0 x1 : M} {y : E}

/--
If two manifold forms have eventually equal transition representatives in a
fixed pair of charts, their chartwise exterior derivatives agree at the point.
-/
theorem extDeriv_transitionPullbackInChart_eq_of_eventuallyEq
    (hω :
      ManifoldForm.transitionPullbackInChart I x0 x1 ω₁ =ᶠ[𝓝 y]
        ManifoldForm.transitionPullbackInChart I x0 x1 ω₂) :
    extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω₁) y =
      extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω₂) y :=
  extDeriv_eq_of_eventuallyEq hω

/--
Neighborhood form of
`extDeriv_transitionPullbackInChart_eq_of_eventuallyEq`.
-/
theorem extDeriv_transitionPullbackInChart_eq_of_eqOn_mem_nhds {s : Set E}
    (hs : s ∈ 𝓝 y)
    (hω :
      EqOn
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω₁)
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω₂) s) :
    extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω₁) y =
      extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω₂) y :=
  extDeriv_eq_of_eqOn_mem_nhds hs hω

/--
Differentiability-friendly chart-representative version.  The proof only uses
the local equality, but this statement matches the hypotheses usually produced
by smoothness packages.
-/
theorem extDeriv_transitionPullbackInChart_eq_of_eventuallyEq_differentiableAt
    (hω :
      ManifoldForm.transitionPullbackInChart I x0 x1 ω₁ =ᶠ[𝓝 y]
        ManifoldForm.transitionPullbackInChart I x0 x1 ω₂)
    (_hω₁ :
      DifferentiableAt Real
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω₁) y)
    (_hω₂ :
      DifferentiableAt Real
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω₂) y) :
    extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω₁) y =
      extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω₂) y :=
  extDeriv_transitionPullbackInChart_eq_of_eventuallyEq hω

end ChartRepresentatives

section ExtDerivEventuallyPackage

universe u v w c i b

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Exterior-derivative reconstruction data whose analytic field is local equality
of chart representatives, rather than direct equality of their exterior
derivatives.

The projection to `ExtDerivOnSupportData` below proves the exterior-derivative
field from `chartwiseEventuallyEq_on`.
-/
structure ExtDerivEventuallyEqData {k : Nat}
    (I : ModelWithCorners Real E H) (ω : ManifoldForm I M k)
    (Chart : Type c) (InteriorPiece : Type i) (BoundaryPiece : Type b) where
  /-- Finite chart labels active in the chosen partition/cover. -/
  activeCharts : Finset Chart
  /-- Scalar partition coefficients used to form the localized finite sum. -/
  coefficient : Chart → M → Real
  /-- Coordinate support on which local representative equality is known. -/
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
  /-- Chartwise local equality of representatives on the controlled support. -/
  chartwiseEventuallyEq_on :
    ∀ x0 x1 y, y ∈ chartSupport x0 x1 →
      ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I activeCharts coefficient ω) =ᶠ[𝓝 y]
        ManifoldForm.transitionPullbackInChart I x0 x1 ω
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

namespace ExtDerivEventuallyEqData

variable {k : Nat} {I : ModelWithCorners Real E H}
variable {ω : ManifoldForm I M k}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}

/--
The exterior-derivative reconstruction field proved from the stored local
eventual equality.
-/
theorem extDeriv_localizedFormSum_eq_global_on
    (D : ExtDerivEventuallyEqData I ω Chart InteriorPiece BoundaryPiece)
    {x0 x1 : M} {y : E} (hy : y ∈ D.chartSupport x0 x1) :
    extDeriv
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I D.activeCharts D.coefficient ω)) y =
      extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y :=
  extDeriv_transitionPullbackInChart_eq_of_eventuallyEq
    (D.chartwiseEventuallyEq_on x0 x1 y hy)

/-- Project local-equality data to the existing on-support `extDeriv` package. -/
def toExtDerivOnSupportData
    (D : ExtDerivEventuallyEqData I ω Chart InteriorPiece BoundaryPiece) :
    ExtDerivOnSupportData I ω Chart InteriorPiece BoundaryPiece where
  activeCharts := D.activeCharts
  coefficient := D.coefficient
  chartSupport := D.chartSupport
  interiorPieces := D.interiorPieces
  boundaryPieces := D.boundaryPieces
  interiorBulkTerm := D.interiorBulkTerm
  boundaryBulkTerm := D.boundaryBulkTerm
  boundaryPartitionTerm := D.boundaryPartitionTerm
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral
  chartwiseExtDeriv_eq_global_on := fun _x0 _x1 _y hy =>
    D.extDeriv_localizedFormSum_eq_global_on hy
  globalBulkIntegral_eq_localBulkSum := D.globalBulkIntegral_eq_localBulkSum
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    D.globalBoundaryIntegral_eq_boundaryPartitionSum

/--
Build local-equality data from an existing reconstruction package and explicit
eventual equality of the relevant chart representatives.
-/
def ofPartitionReconstructionData
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (coefficient : Chart → M → Real)
    (chartSupport : M → M → Set E)
    (heq :
      ∀ x0 x1 y, y ∈ chartSupport x0 x1 →
        ManifoldForm.transitionPullbackInChart I x0 x1
            (localizedFormSum I R.activeCharts coefficient ω) =ᶠ[𝓝 y]
          ManifoldForm.transitionPullbackInChart I x0 x1 ω) :
    ExtDerivEventuallyEqData I ω Chart InteriorPiece BoundaryPiece where
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
  chartwiseEventuallyEq_on := heq
  globalBulkIntegral_eq_localBulkSum := R.globalBulkIntegral_eq_localBulkSum
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    R.globalBoundaryIntegral_eq_boundaryPartitionSum

/--
Constructor from equality on chart-support sets, provided each support set is a
neighborhood of every point of it.
-/
def ofPartitionReconstructionDataEqOn
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (coefficient : Chart → M → Real)
    (chartSupport : M → M → Set E)
    (hnhds : ∀ x0 x1 y, y ∈ chartSupport x0 x1 → chartSupport x0 x1 ∈ 𝓝 y)
    (heq :
      ∀ x0 x1,
        EqOn
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (localizedFormSum I R.activeCharts coefficient ω))
          (ManifoldForm.transitionPullbackInChart I x0 x1 ω)
          (chartSupport x0 x1)) :
    ExtDerivEventuallyEqData I ω Chart InteriorPiece BoundaryPiece :=
  ofPartitionReconstructionData R coefficient chartSupport fun x0 x1 y hy =>
    eventually_of_mem (hnhds x0 x1 y hy) (heq x0 x1)

@[simp]
theorem toExtDerivOnSupportData_activeCharts
    (D : ExtDerivEventuallyEqData I ω Chart InteriorPiece BoundaryPiece) :
    D.toExtDerivOnSupportData.activeCharts = D.activeCharts :=
  rfl

@[simp]
theorem toExtDerivOnSupportData_chartSupport
    (D : ExtDerivEventuallyEqData I ω Chart InteriorPiece BoundaryPiece) :
    D.toExtDerivOnSupportData.chartSupport = D.chartSupport :=
  rfl

@[simp]
theorem toExtDerivOnSupportData_globalBulkIntegral
    (D : ExtDerivEventuallyEqData I ω Chart InteriorPiece BoundaryPiece) :
    D.toExtDerivOnSupportData.globalBulkIntegral = D.globalBulkIntegral :=
  rfl

@[simp]
theorem toExtDerivOnSupportData_globalBoundaryIntegral
    (D : ExtDerivEventuallyEqData I ω Chart InteriorPiece BoundaryPiece) :
    D.toExtDerivOnSupportData.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

end ExtDerivEventuallyEqData

end ExtDerivEventuallyPackage

end Stokes

end
