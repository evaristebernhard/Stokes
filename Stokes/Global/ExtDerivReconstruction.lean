import Stokes.Global.Reconstruction

/-!
# Exterior-derivative reconstruction interface

This module records the exterior-derivative reconstruction obligation needed by
the global Stokes assembly.  The hard analytic statement is kept as explicit
chartwise data: later files can replace that field by a theorem about
`extDeriv` commuting with finite localized sums.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section ExtDerivReconstructionPackage

universe u v w c i b

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Partition reconstruction data augmented by an explicit exterior-derivative
reconstruction field.

The field is chartwise because the current project-local integral API computes
bulk terms through chart representatives.  It is intentionally explicit rather
than asserted globally.
-/
structure ExtDerivPartitionReconstructionData {k : Nat}
    (I : ModelWithCorners Real E H) (omega : ManifoldForm I M k)
    (Chart : Type c) (InteriorPiece : Type i) (BoundaryPiece : Type b) where
  /-- Finite chart labels active in the chosen partition/cover. -/
  activeCharts : Finset Chart
  /-- Scalar partition coefficients used to form the localized finite sum. -/
  coefficient : Chart → M → Real
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
  /-- Chartwise exterior-derivative reconstruction for the localized finite sum. -/
  chartwiseExtDeriv_eq_global :
    ∀ x0 x1 y,
      extDeriv
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (localizedFormSum I activeCharts coefficient omega)) y =
        extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 omega) y
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

namespace ExtDerivPartitionReconstructionData

variable {k : Nat} {I : ModelWithCorners Real E H}
variable {omega : ManifoldForm I M k}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}

/-- Forget the exterior-derivative field and keep the existing reconstruction package. -/
def toPartitionReconstructionData
    (D : ExtDerivPartitionReconstructionData I omega Chart InteriorPiece BoundaryPiece) :
    PartitionReconstructionData I omega Chart InteriorPiece BoundaryPiece where
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

/-- Named accessor for the chartwise exterior-derivative reconstruction field. -/
theorem extDeriv_localizedFormSum_eq_global
    (D : ExtDerivPartitionReconstructionData I omega Chart InteriorPiece BoundaryPiece)
    (x0 x1 : M) (y : E) :
    extDeriv
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I D.activeCharts D.coefficient omega)) y =
      extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 omega) y :=
  D.chartwiseExtDeriv_eq_global x0 x1 y

/-- Build the exterior-derivative package from an existing reconstruction package. -/
def ofPartitionReconstructionData
    (R : PartitionReconstructionData I omega Chart InteriorPiece BoundaryPiece)
    (coefficient : Chart → M → Real)
    (hext :
      ∀ x0 x1 y,
        extDeriv
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (localizedFormSum I R.activeCharts coefficient omega)) y =
          extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 omega) y) :
    ExtDerivPartitionReconstructionData I omega Chart InteriorPiece BoundaryPiece where
  activeCharts := R.activeCharts
  coefficient := coefficient
  interiorPieces := R.interiorPieces
  boundaryPieces := R.boundaryPieces
  interiorBulkTerm := R.interiorBulkTerm
  boundaryBulkTerm := R.boundaryBulkTerm
  boundaryPartitionTerm := R.boundaryPartitionTerm
  globalBulkIntegral := R.globalBulkIntegral
  globalBoundaryIntegral := R.globalBoundaryIntegral
  chartwiseExtDeriv_eq_global := hext
  globalBulkIntegral_eq_localBulkSum := R.globalBulkIntegral_eq_localBulkSum
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    R.globalBoundaryIntegral_eq_boundaryPartitionSum

section GlobalStokesWrapper

variable {n : Nat}
variable {I' : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega' : ManifoldForm I' M n}

/--
Convert exterior-derivative reconstruction data plus the remaining
local/cancellation/chart-change inputs into the final `GlobalStokesData`
package.
-/
def toGlobalStokesData
    (D :
      ExtDerivPartitionReconstructionData I' omega' Chart InteriorPiece BoundaryPiece)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (boundaryBoundaryTerm : Chart → BoundaryPiece → Real)
    (interiorLocalStokes :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.interiorPieces x →
          D.interiorBulkTerm x q = interiorBoundaryTerm x q)
    (boundaryLocalStokes :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          D.boundaryBulkTerm x q = boundaryBoundaryTerm x q)
    (interiorBoundaryCancellation :
      (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.interiorPieces x) fun q => interiorBoundaryTerm x q) = 0)
    (chartChangeCancellation :
      (Finset.sum D.activeCharts fun x =>
          Finset.sum (D.boundaryPieces x) fun q => boundaryBoundaryTerm x q) =
        Finset.sum D.activeCharts fun x =>
          Finset.sum (D.boundaryPieces x) fun q => D.boundaryPartitionTerm x q) :
    GlobalStokesData I' omega' Chart InteriorPiece BoundaryPiece :=
  PartitionReconstructionData.toGlobalStokesData
    D.toPartitionReconstructionData
    interiorBoundaryTerm
    boundaryBoundaryTerm
    interiorLocalStokes
    boundaryLocalStokes
    interiorBoundaryCancellation
    chartChangeCancellation

end GlobalStokesWrapper

end ExtDerivPartitionReconstructionData

end ExtDerivReconstructionPackage

end Stokes

end
