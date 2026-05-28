import Stokes.Global.ReconstructionWrappers
import Stokes.Global.MixedGlobalConstructor

/-!
# Minimized remaining fields for global Stokes packages

This file audits the fields still needed after `PartitionReconstructionData`
has supplied the two global reconstruction equalities.  The remaining data is
exactly the local Stokes, artificial-boundary cancellation, and chart-change
part of the final theorem package.  A single minimized package constructs both
`GlobalStokesData` and `MixedGlobalStokesData`.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section RemainingFieldsMinimized

universe u w c i b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}

namespace PartitionReconstructionData

/--
Minimal package of the fields still needed after partition reconstruction.

These are the six non-reconstruction obligations common to the final
`GlobalStokesData` package and the mixed constructor: two boundary-side term
families, two local Stokes fields, artificial-boundary cancellation, and
boundary chart-change compatibility.
-/
structure GlobalStokesRemainingFieldsMinimized
    (R : PartitionReconstructionData I omega Chart InteriorPiece BoundaryPiece) where
  /-- Artificial boundary-side contribution of an interior local piece. -/
  interiorBoundaryTerm : Chart -> InteriorPiece -> Real
  /-- Boundary-chart contribution before global chart-change identification. -/
  boundaryBoundaryTerm : Chart -> BoundaryPiece -> Real
  /-- Local Stokes on every recorded interior piece. -/
  interiorLocalStokes :
    forall x, x ∈ R.activeCharts ->
      forall q, q ∈ R.interiorPieces x ->
        R.interiorBulkTerm x q = interiorBoundaryTerm x q
  /-- Local Stokes on every recorded boundary-chart piece. -/
  boundaryLocalStokes :
    forall x, x ∈ R.activeCharts ->
      forall q, q ∈ R.boundaryPieces x ->
        R.boundaryBulkTerm x q = boundaryBoundaryTerm x q
  /-- Cancellation of artificial interior-chart boundary faces. -/
  interiorBoundaryCancellation :
    (Finset.sum R.activeCharts fun x =>
      Finset.sum (R.interiorPieces x) fun q => interiorBoundaryTerm x q) = 0
  /-- Boundary chart-change compatibility with the reconstructed partition term. -/
  chartChangeCancellation :
    (Finset.sum R.activeCharts fun x =>
        Finset.sum (R.boundaryPieces x) fun q => boundaryBoundaryTerm x q) =
      Finset.sum R.activeCharts fun x =>
        Finset.sum (R.boundaryPieces x) fun q => R.boundaryPartitionTerm x q

namespace GlobalStokesRemainingFieldsMinimized

variable {R : PartitionReconstructionData I omega Chart InteriorPiece BoundaryPiece}

/-- Convert the minimized package to the existing remaining-field wrapper. -/
def toRemainingFields
    (A : GlobalStokesRemainingFieldsMinimized R) :
    GlobalStokesRemainingFields R where
  interiorBoundaryTerm := A.interiorBoundaryTerm
  boundaryBoundaryTerm := A.boundaryBoundaryTerm
  interiorLocalStokes := A.interiorLocalStokes
  boundaryLocalStokes := A.boundaryLocalStokes
  interiorBoundaryCancellation := A.interiorBoundaryCancellation
  chartChangeCancellation := A.chartChangeCancellation

@[simp]
theorem toRemainingFields_interiorBoundaryTerm
    (A : GlobalStokesRemainingFieldsMinimized R) :
    A.toRemainingFields.interiorBoundaryTerm = A.interiorBoundaryTerm :=
  rfl

@[simp]
theorem toRemainingFields_boundaryBoundaryTerm
    (A : GlobalStokesRemainingFieldsMinimized R) :
    A.toRemainingFields.boundaryBoundaryTerm = A.boundaryBoundaryTerm :=
  rfl

@[simp]
theorem toRemainingFields_interiorLocalStokes
    (A : GlobalStokesRemainingFieldsMinimized R) :
    A.toRemainingFields.interiorLocalStokes = A.interiorLocalStokes :=
  rfl

@[simp]
theorem toRemainingFields_boundaryLocalStokes
    (A : GlobalStokesRemainingFieldsMinimized R) :
    A.toRemainingFields.boundaryLocalStokes = A.boundaryLocalStokes :=
  rfl

/-- Constructor for the final global package from reconstruction plus minimized fields. -/
def toGlobalStokesData
    (A : GlobalStokesRemainingFieldsMinimized R) :
    GlobalStokesData I omega Chart InteriorPiece BoundaryPiece :=
  R.toGlobalStokesDataWith A.toRemainingFields

/-- Constructor for the mixed global package from reconstruction plus minimized fields. -/
def toMixedGlobalStokesData
    (A : GlobalStokesRemainingFieldsMinimized R) :
    MixedGlobalStokesData I omega Chart InteriorPiece BoundaryPiece where
  reconstruction := R
  interiorBoundaryTerm := A.interiorBoundaryTerm
  boundaryBoundaryTerm := A.boundaryBoundaryTerm
  interiorPackage := { localStokes := A.interiorLocalStokes }
  boundaryPackage := { localStokes := A.boundaryLocalStokes }
  interiorBoundaryCancellation := A.interiorBoundaryCancellation
  chartChangeCancellation := A.chartChangeCancellation

@[simp]
theorem toGlobalStokesData_globalBulkIntegral
    (A : GlobalStokesRemainingFieldsMinimized R) :
    A.toGlobalStokesData.globalBulkIntegral = R.globalBulkIntegral :=
  rfl

@[simp]
theorem toGlobalStokesData_globalBoundaryIntegral
    (A : GlobalStokesRemainingFieldsMinimized R) :
    A.toGlobalStokesData.globalBoundaryIntegral = R.globalBoundaryIntegral :=
  rfl

@[simp]
theorem toGlobalStokesData_interiorBoundaryTerm
    (A : GlobalStokesRemainingFieldsMinimized R) :
    A.toGlobalStokesData.interiorBoundaryTerm = A.interiorBoundaryTerm :=
  rfl

@[simp]
theorem toGlobalStokesData_boundaryBoundaryTerm
    (A : GlobalStokesRemainingFieldsMinimized R) :
    A.toGlobalStokesData.boundaryBoundaryTerm = A.boundaryBoundaryTerm :=
  rfl

@[simp]
theorem toMixedGlobalStokesData_reconstruction
    (A : GlobalStokesRemainingFieldsMinimized R) :
    A.toMixedGlobalStokesData.reconstruction = R :=
  rfl

@[simp]
theorem toMixedGlobalStokesData_interiorBoundaryTerm
    (A : GlobalStokesRemainingFieldsMinimized R) :
    A.toMixedGlobalStokesData.interiorBoundaryTerm = A.interiorBoundaryTerm :=
  rfl

@[simp]
theorem toMixedGlobalStokesData_boundaryBoundaryTerm
    (A : GlobalStokesRemainingFieldsMinimized R) :
    A.toMixedGlobalStokesData.boundaryBoundaryTerm = A.boundaryBoundaryTerm :=
  rfl

@[simp]
theorem toMixedGlobalStokesData_interiorLocalStokes
    (A : GlobalStokesRemainingFieldsMinimized R) :
    A.toMixedGlobalStokesData.interiorPackage.localStokes =
      A.interiorLocalStokes :=
  rfl

@[simp]
theorem toMixedGlobalStokesData_boundaryLocalStokes
    (A : GlobalStokesRemainingFieldsMinimized R) :
    A.toMixedGlobalStokesData.boundaryPackage.localStokes =
      A.boundaryLocalStokes :=
  rfl

/--
The mixed constructor and the final constructor agree after converting the
mixed package to `GlobalStokesData`.
-/
theorem toMixedGlobalStokesData_toGlobalStokesData
    (A : GlobalStokesRemainingFieldsMinimized R) :
    A.toMixedGlobalStokesData.toGlobalStokesData = A.toGlobalStokesData :=
  rfl

/-- Global Stokes theorem from reconstruction plus minimized remaining fields. -/
theorem stokes
    (A : GlobalStokesRemainingFieldsMinimized R) :
    R.globalBulkIntegral = R.globalBoundaryIntegral :=
  A.toMixedGlobalStokesData.stokes

end GlobalStokesRemainingFieldsMinimized

end PartitionReconstructionData

namespace GlobalStokesData

/-- Extract the partition-reconstruction fields from a final data package. -/
def partitionReconstructionData
    (D : GlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
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

/-- Project the minimized remaining fields from a final data package. -/
def remainingFieldsMinimized
    (D : GlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    PartitionReconstructionData.GlobalStokesRemainingFieldsMinimized
      D.partitionReconstructionData where
  interiorBoundaryTerm := D.interiorBoundaryTerm
  boundaryBoundaryTerm := D.boundaryBoundaryTerm
  interiorLocalStokes := by
    simpa [partitionReconstructionData] using D.interiorLocalStokes
  boundaryLocalStokes := by
    simpa [partitionReconstructionData] using D.boundaryLocalStokes
  interiorBoundaryCancellation := by
    simpa [partitionReconstructionData] using D.interiorBoundaryCancellation
  chartChangeCancellation := by
    simpa [partitionReconstructionData] using D.chartChangeCancellation

@[simp]
theorem partitionReconstructionData_activeCharts
    (D : GlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    D.partitionReconstructionData.activeCharts = D.activeCharts :=
  rfl

@[simp]
theorem partitionReconstructionData_globalBulkIntegral
    (D : GlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    D.partitionReconstructionData.globalBulkIntegral = D.globalBulkIntegral :=
  rfl

@[simp]
theorem partitionReconstructionData_globalBoundaryIntegral
    (D : GlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    D.partitionReconstructionData.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

@[simp]
theorem remainingFieldsMinimized_interiorBoundaryTerm
    (D : GlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    D.remainingFieldsMinimized.interiorBoundaryTerm =
      D.interiorBoundaryTerm :=
  rfl

@[simp]
theorem remainingFieldsMinimized_boundaryBoundaryTerm
    (D : GlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    D.remainingFieldsMinimized.boundaryBoundaryTerm =
      D.boundaryBoundaryTerm :=
  rfl

end GlobalStokesData

namespace MixedGlobalStokesData

/-- Project the minimized remaining fields from a mixed global data package. -/
def remainingFieldsMinimized
    (D : MixedGlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    PartitionReconstructionData.GlobalStokesRemainingFieldsMinimized
      D.reconstruction where
  interiorBoundaryTerm := D.interiorBoundaryTerm
  boundaryBoundaryTerm := D.boundaryBoundaryTerm
  interiorLocalStokes := D.interiorPackage.localStokes
  boundaryLocalStokes := D.boundaryPackage.localStokes
  interiorBoundaryCancellation := D.interiorBoundaryCancellation
  chartChangeCancellation := D.chartChangeCancellation

@[simp]
theorem remainingFieldsMinimized_interiorBoundaryTerm
    (D : MixedGlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    D.remainingFieldsMinimized.interiorBoundaryTerm =
      D.interiorBoundaryTerm :=
  rfl

@[simp]
theorem remainingFieldsMinimized_boundaryBoundaryTerm
    (D : MixedGlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    D.remainingFieldsMinimized.boundaryBoundaryTerm =
      D.boundaryBoundaryTerm :=
  rfl

@[simp]
theorem remainingFieldsMinimized_interiorLocalStokes
    (D : MixedGlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    D.remainingFieldsMinimized.interiorLocalStokes =
      D.interiorPackage.localStokes :=
  rfl

@[simp]
theorem remainingFieldsMinimized_boundaryLocalStokes
    (D : MixedGlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    D.remainingFieldsMinimized.boundaryLocalStokes =
      D.boundaryPackage.localStokes :=
  rfl

end MixedGlobalStokesData

end RemainingFieldsMinimized

end Stokes

end
