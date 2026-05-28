import Stokes.Global.ProjectLocalConstructor
import Stokes.Global.MixedGlobalConstructor

/-!
# Project-local data as boundary-only mixed global Stokes data

This file records the relationship between the project-local constructor layer
and the mixed/global constructor layer.  A project-local package is a mixed
package with no interior pieces: the mixed interior index is `Empty`, and the
project-local pieces are used as the mixed boundary pieces.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section ProjectLocalToMixed

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace ProjectLocalGlobalStokesData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/--
View project-local global data as mixed reconstruction data with no interior
pieces.
-/
def toBoundaryOnlyPartitionReconstructionData
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    PartitionReconstructionData I ω Chart Empty Piece where
  activeCharts := D.activeCharts
  interiorPieces := fun _ => ∅
  boundaryPieces := D.localPieces
  interiorBulkTerm := fun _ q => Empty.elim q
  boundaryBulkTerm := fun x q =>
    projectLocalBulkIntegral I (D.sourceChart x q) (D.targetChart x q) ω
      (D.lowerCorner x q) (D.upperCorner x q)
  boundaryPartitionTerm := D.boundaryPartitionTerm
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum := by
    simpa using D.globalBulkIntegral_eq_projectLocalSum
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    D.globalBoundaryIntegral_eq_boundaryPartitionSum

/-- Project-local boundary terms in the mixed boundary-local-Stokes slot. -/
def boundaryOnlyBoundaryTerm
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) (x : Chart) (q : Piece) :
    Real :=
  projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
    (D.lowerCorner x q) (D.upperCorner x q)

/--
View project-local global data as mixed global data with no interior pieces.

The adapter is purely structural: the mixed boundary bulk term is the
project-local bulk wrapper, the mixed boundary-boundary term is the
project-local boundary wrapper, and the interior package is vacuous.
-/
def toBoundaryOnlyMixedGlobalStokesData
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    MixedGlobalStokesData I ω Chart Empty Piece where
  reconstruction := D.toBoundaryOnlyPartitionReconstructionData
  interiorBoundaryTerm := fun _ q => Empty.elim q
  boundaryBoundaryTerm := D.boundaryOnlyBoundaryTerm
  interiorPackage := {
    localStokes := by
      intro _ _ q _
      cases q
  }
  boundaryPackage := {
    localStokes := by
      intro x hx q hq
      simpa [boundaryOnlyBoundaryTerm] using D.localProjectStokes x hx q hq
  }
  interiorBoundaryCancellation := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    exact Finset.sum_empty
  chartChangeCancellation := by
    simpa [boundaryOnlyBoundaryTerm] using D.chartChangeCancellation

/-- Direct conversion from project-local global data to final global data. -/
def toBoundaryOnlyGlobalStokesData
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    GlobalStokesData I ω Chart Empty Piece :=
  D.toBoundaryOnlyMixedGlobalStokesData.toGlobalStokesData

@[simp]
theorem toBoundaryOnlyPartitionReconstructionData_globalBulkIntegral
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    D.toBoundaryOnlyPartitionReconstructionData.globalBulkIntegral =
      D.globalBulkIntegral :=
  rfl

@[simp]
theorem toBoundaryOnlyPartitionReconstructionData_globalBoundaryIntegral
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    D.toBoundaryOnlyPartitionReconstructionData.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

@[simp]
theorem toBoundaryOnlyMixedGlobalStokesData_reconstruction
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    D.toBoundaryOnlyMixedGlobalStokesData.reconstruction =
      D.toBoundaryOnlyPartitionReconstructionData :=
  rfl

@[simp]
theorem toBoundaryOnlyMixedGlobalStokesData_globalBulkIntegral
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    D.toBoundaryOnlyMixedGlobalStokesData.reconstruction.globalBulkIntegral =
      D.globalBulkIntegral :=
  rfl

@[simp]
theorem toBoundaryOnlyMixedGlobalStokesData_globalBoundaryIntegral
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    D.toBoundaryOnlyMixedGlobalStokesData.reconstruction.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

/-- Project-local global Stokes, routed through the boundary-only mixed adapter. -/
theorem stokes_via_boundaryOnlyMixed
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    D.globalBulkIntegral = D.globalBoundaryIntegral := by
  simpa using D.toBoundaryOnlyMixedGlobalStokesData.stokes

end ProjectLocalGlobalStokesData

namespace ProjectLocalConstructorData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/--
Convert project-local constructor data into mixed global Stokes data by first
building the project-local global package and then applying the boundary-only
adapter.
-/
def toBoundaryOnlyMixedGlobalStokesData
    (D : ProjectLocalConstructorData I ω Chart Piece) :
    MixedGlobalStokesData I ω Chart Empty Piece :=
  D.toProjectLocalGlobalStokesData.toBoundaryOnlyMixedGlobalStokesData

/-- Direct conversion from project-local constructor data to final global data. -/
def toBoundaryOnlyGlobalStokesData
    (D : ProjectLocalConstructorData I ω Chart Piece) :
    GlobalStokesData I ω Chart Empty Piece :=
  D.toBoundaryOnlyMixedGlobalStokesData.toGlobalStokesData

@[simp]
theorem toBoundaryOnlyMixedGlobalStokesData_globalBulkIntegral
    (D : ProjectLocalConstructorData I ω Chart Piece) :
    D.toBoundaryOnlyMixedGlobalStokesData.reconstruction.globalBulkIntegral =
      D.globalBulkIntegral :=
  rfl

@[simp]
theorem toBoundaryOnlyMixedGlobalStokesData_globalBoundaryIntegral
    (D : ProjectLocalConstructorData I ω Chart Piece) :
    D.toBoundaryOnlyMixedGlobalStokesData.reconstruction.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

/-- Project-local constructor Stokes, routed through the mixed/global adapter. -/
theorem stokes_via_boundaryOnlyMixed
    (D : ProjectLocalConstructorData I ω Chart Piece) :
    D.globalBulkIntegral = D.globalBoundaryIntegral := by
  simpa using D.toBoundaryOnlyMixedGlobalStokesData.stokes

end ProjectLocalConstructorData

/--
Blueprint-facing wrapper: project-local constructor data as boundary-only mixed
global Stokes data.
-/
def projectLocalConstructorToBoundaryOnlyMixedGlobalStokesData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    {Chart : Type c} {Piece : Type p}
    (D : ProjectLocalConstructorData I ω Chart Piece) :
    MixedGlobalStokesData I ω Chart Empty Piece :=
  D.toBoundaryOnlyMixedGlobalStokesData

/--
Blueprint-facing theorem showing that the project-local constructor theorem can
be routed through the mixed/global bookkeeping layer.
-/
theorem projectLocalConstructorGlobalStokes_viaBoundaryOnlyMixed
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    {Chart : Type c} {Piece : Type p}
    (D : ProjectLocalConstructorData I ω Chart Piece) :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  D.stokes_via_boundaryOnlyMixed

end ProjectLocalToMixed

end Stokes

end
