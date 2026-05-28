import Stokes.Global.Assembly
import Stokes.Global.ReconstructionWrappers
import Stokes.Global.MixedGlobalConstructor

/-!
# Global bulk integral reconstruction

This file isolates the bulk-integral reconstruction obligation from the full
partition reconstruction package.  The main data package records only that the
global bulk integral is the finite sum of the chosen local bulk terms.  Boundary
partition reconstruction can then be added separately to recover the existing
`PartitionReconstructionData` and constructor APIs.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section IntegralReconstruction

universe u v w c i b

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Bulk reconstruction data for a global Stokes package.

This is the smallest reusable package for the obligation
`global bulk integral = finite local bulk sum`.  It deliberately does not carry
local Stokes identities, artificial-boundary cancellation, chart-change data, or
boundary integral reconstruction.
-/
structure BulkIntegralReconstructionData {k : Nat}
    (I : ModelWithCorners Real E H) (omega : ManifoldForm I M k)
    (Chart : Type c) (InteriorPiece : Type i) (BoundaryPiece : Type b) where
  /-- Finite chart labels active in the chosen partition/cover. -/
  activeCharts : Finset Chart
  /-- Localized interior pieces assigned to an active chart. -/
  interiorPieces : Chart -> Finset InteriorPiece
  /-- Localized boundary-chart pieces assigned to an active chart. -/
  boundaryPieces : Chart -> Finset BoundaryPiece
  /-- Bulk contribution of an interior local piece. -/
  interiorBulkTerm : Chart -> InteriorPiece -> Real
  /-- Bulk contribution of a boundary-chart local piece. -/
  boundaryBulkTerm : Chart -> BoundaryPiece -> Real
  /-- The global bulk integral represented by this reconstruction package. -/
  globalBulkIntegral : Real
  /-- Reconstruction of the global bulk integral from finitely many local pieces. -/
  globalBulkIntegral_eq_localBulkSum :
    globalBulkIntegral =
      (Finset.sum activeCharts fun x =>
          Finset.sum (interiorPieces x) fun q => interiorBulkTerm x q) +
        Finset.sum activeCharts fun x =>
          Finset.sum (boundaryPieces x) fun q => boundaryBulkTerm x q

namespace BulkIntegralReconstructionData

variable {k : Nat} {I : ModelWithCorners Real E H}
variable {omega : ManifoldForm I M k}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}

/-- Sum of all interior bulk terms in a bulk reconstruction package. -/
def interiorBulkSum
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece) :
    Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.interiorPieces x) fun q => D.interiorBulkTerm x q

/-- Sum of all boundary-chart bulk terms in a bulk reconstruction package. -/
def boundaryBulkSum
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece) :
    Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => D.boundaryBulkTerm x q

/-- Total local bulk side recorded in a bulk reconstruction package. -/
def localBulkSum
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece) :
    Real :=
  interiorBulkSum D + boundaryBulkSum D

/-- Wrapper form of the bulk reconstruction field using package-local sum names. -/
theorem globalBulkIntegral_eq_localBulkSum'
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece) :
    D.globalBulkIntegral = localBulkSum D := by
  rw [localBulkSum, interiorBulkSum, boundaryBulkSum]
  exact D.globalBulkIntegral_eq_localBulkSum

/--
Bulk reconstruction theorem in the exact shape of
`GlobalStokesAssemblyData.globalBulkIntegral_eq_localSum`.
-/
theorem globalBulkIntegral_eq_assemblyLocalSum
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece) :
    D.globalBulkIntegral =
      (Finset.sum D.activeCharts fun x =>
          Finset.sum (D.interiorPieces x) fun q => D.interiorBulkTerm x q) +
        Finset.sum D.activeCharts fun x =>
          Finset.sum (D.boundaryPieces x) fun q => D.boundaryBulkTerm x q :=
  D.globalBulkIntegral_eq_localBulkSum

/--
Bulk reconstruction theorem in the exact shape of
`GlobalStokesData.globalBulkIntegral_eq_localBulkSum`.
-/
theorem globalBulkIntegral_eq_globalStokesDataField
    {n : Nat} {I' : ModelWithCorners Real (Fin (n + 1) -> Real) H}
    {omega' : ManifoldForm I' M n}
    (D :
      BulkIntegralReconstructionData I' omega' Chart InteriorPiece BoundaryPiece) :
    D.globalBulkIntegral =
      (Finset.sum D.activeCharts fun x =>
          Finset.sum (D.interiorPieces x) fun q => D.interiorBulkTerm x q) +
        Finset.sum D.activeCharts fun x =>
          Finset.sum (D.boundaryPieces x) fun q => D.boundaryBulkTerm x q :=
  D.globalBulkIntegral_eq_localBulkSum

/--
Boundary-side fields that complete bulk reconstruction into the existing
`PartitionReconstructionData` package.
-/
structure BoundaryPartitionFields
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece) where
  /-- Boundary contribution after chart changes and partition reconstruction. -/
  boundaryPartitionTerm : Chart -> BoundaryPiece -> Real
  /-- The global boundary integral represented by the completed package. -/
  globalBoundaryIntegral : Real
  /-- Reconstruction of the global boundary integral from the boundary partition. -/
  globalBoundaryIntegral_eq_boundaryPartitionSum :
    globalBoundaryIntegral =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.boundaryPieces x) fun q => boundaryPartitionTerm x q

/--
Complete a bulk reconstruction package with boundary partition fields, obtaining
the existing two-sided partition reconstruction package.
-/
def toPartitionReconstructionData
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D) :
    PartitionReconstructionData I omega Chart InteriorPiece BoundaryPiece where
  activeCharts := D.activeCharts
  interiorPieces := D.interiorPieces
  boundaryPieces := D.boundaryPieces
  interiorBulkTerm := D.interiorBulkTerm
  boundaryBulkTerm := D.boundaryBulkTerm
  boundaryPartitionTerm := B.boundaryPartitionTerm
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := B.globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum := D.globalBulkIntegral_eq_localBulkSum
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    B.globalBoundaryIntegral_eq_boundaryPartitionSum

@[simp]
theorem toPartitionReconstructionData_activeCharts
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D) :
    (D.toPartitionReconstructionData B).activeCharts = D.activeCharts :=
  rfl

@[simp]
theorem toPartitionReconstructionData_globalBulkIntegral
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D) :
    (D.toPartitionReconstructionData B).globalBulkIntegral =
      D.globalBulkIntegral :=
  rfl

@[simp]
theorem toPartitionReconstructionData_globalBoundaryIntegral
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D) :
    (D.toPartitionReconstructionData B).globalBoundaryIntegral =
      B.globalBoundaryIntegral :=
  rfl

@[simp]
theorem toPartitionReconstructionData_boundaryPartitionTerm
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D) :
    (D.toPartitionReconstructionData B).boundaryPartitionTerm =
      B.boundaryPartitionTerm :=
  rfl

/--
The completed partition reconstruction keeps the bulk reconstruction field
supplied by the source bulk package.
-/
theorem toPartitionReconstructionData_globalBulkIntegral_eq_localBulkSum
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D) :
    (D.toPartitionReconstructionData B).globalBulkIntegral =
      PartitionReconstructionData.localBulkSum (D.toPartitionReconstructionData B) := by
  rw [PartitionReconstructionData.localBulkSum,
    PartitionReconstructionData.interiorBulkSum,
    PartitionReconstructionData.boundaryBulkSum]
  exact D.globalBulkIntegral_eq_localBulkSum

/--
The completed partition reconstruction keeps the boundary reconstruction field
supplied by the boundary partition fields.
-/
theorem toPartitionReconstructionData_globalBoundaryIntegral_eq_boundaryPartitionSum
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D) :
    (D.toPartitionReconstructionData B).globalBoundaryIntegral =
      PartitionReconstructionData.boundaryPartitionSum
        (D.toPartitionReconstructionData B) := by
  rw [PartitionReconstructionData.boundaryPartitionSum]
  exact B.globalBoundaryIntegral_eq_boundaryPartitionSum

section GlobalStokesWrapper

variable {n : Nat}
variable {I' : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega' : ManifoldForm I' M n}

/--
Complete bulk reconstruction into the reconstruction-field package used by
`GlobalStokesData`.
-/
def toGlobalStokesReconstructionFields
    (D : BulkIntegralReconstructionData I' omega' Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D) :
    GlobalStokesReconstructionFields I' omega' Chart InteriorPiece BoundaryPiece :=
  GlobalStokesReconstructionFields.ofPartitionReconstructionData
    (D.toPartitionReconstructionData B)

/--
Complete bulk reconstruction and the remaining local/cancellation fields into
the final `GlobalStokesData` package.
-/
def toGlobalStokesDataWith
    (D : BulkIntegralReconstructionData I' omega' Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D)
    (A :
      PartitionReconstructionData.GlobalStokesRemainingFields
        (D.toPartitionReconstructionData B)) :
    GlobalStokesData I' omega' Chart InteriorPiece BoundaryPiece :=
  (D.toPartitionReconstructionData B).toGlobalStokesDataWith A

@[simp]
theorem toGlobalStokesDataWith_globalBulkIntegral
    (D : BulkIntegralReconstructionData I' omega' Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D)
    (A :
      PartitionReconstructionData.GlobalStokesRemainingFields
        (D.toPartitionReconstructionData B)) :
    (D.toGlobalStokesDataWith B A).globalBulkIntegral =
      D.globalBulkIntegral :=
  rfl

@[simp]
theorem toGlobalStokesDataWith_globalBoundaryIntegral
    (D : BulkIntegralReconstructionData I' omega' Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D)
    (A :
      PartitionReconstructionData.GlobalStokesRemainingFields
        (D.toPartitionReconstructionData B)) :
    (D.toGlobalStokesDataWith B A).globalBoundaryIntegral =
      B.globalBoundaryIntegral :=
  rfl

/--
The automatically constructed `GlobalStokesData` has its bulk reconstruction
field filled by the source bulk package.
-/
theorem toGlobalStokesDataWith_globalBulkIntegral_eq_localBulkSum
    (D : BulkIntegralReconstructionData I' omega' Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D)
    (A :
      PartitionReconstructionData.GlobalStokesRemainingFields
        (D.toPartitionReconstructionData B)) :
    (D.toGlobalStokesDataWith B A).globalBulkIntegral =
      GlobalStokesData.localBulkSum (D.toGlobalStokesDataWith B A) := by
  rw [GlobalStokesData.localBulkSum, GlobalStokesData.interiorBulkSum,
    GlobalStokesData.boundaryBulkSum]
  exact D.globalBulkIntegral_eq_localBulkSum

/--
The automatically constructed `GlobalStokesData` has its boundary
reconstruction field filled by the boundary partition fields.
-/
theorem toGlobalStokesDataWith_globalBoundaryIntegral_eq_boundaryPartitionSum
    (D : BulkIntegralReconstructionData I' omega' Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D)
    (A :
      PartitionReconstructionData.GlobalStokesRemainingFields
        (D.toPartitionReconstructionData B)) :
    (D.toGlobalStokesDataWith B A).globalBoundaryIntegral =
      GlobalStokesData.boundaryPartitionSum (D.toGlobalStokesDataWith B A) := by
  rw [GlobalStokesData.boundaryPartitionSum]
  exact B.globalBoundaryIntegral_eq_boundaryPartitionSum

/--
Build the mixed global constructor package from separated bulk reconstruction
and boundary partition reconstruction fields.
-/
def toMixedGlobalStokesData
    (D : BulkIntegralReconstructionData I' omega' Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D)
    (interiorBoundaryTerm : Chart -> InteriorPiece -> Real)
    (boundaryBoundaryTerm : Chart -> BoundaryPiece -> Real)
    (interiorPackage :
      MixedInteriorPackage I' omega' Chart InteriorPiece
        D.activeCharts D.interiorPieces D.interiorBulkTerm interiorBoundaryTerm)
    (boundaryPackage :
      MixedBoundaryPackage I' omega' Chart BoundaryPiece
        D.activeCharts D.boundaryPieces D.boundaryBulkTerm boundaryBoundaryTerm)
    (interiorBoundaryCancellation :
      (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.interiorPieces x) fun q =>
          interiorBoundaryTerm x q) = 0)
    (chartChangeCancellation :
      (Finset.sum D.activeCharts fun x =>
          Finset.sum (D.boundaryPieces x) fun q =>
            boundaryBoundaryTerm x q) =
        Finset.sum D.activeCharts fun x =>
          Finset.sum (D.boundaryPieces x) fun q =>
            B.boundaryPartitionTerm x q) :
    MixedGlobalStokesData I' omega' Chart InteriorPiece BoundaryPiece where
  reconstruction := D.toPartitionReconstructionData B
  interiorBoundaryTerm := interiorBoundaryTerm
  boundaryBoundaryTerm := boundaryBoundaryTerm
  interiorPackage := by
    simpa [toPartitionReconstructionData] using interiorPackage
  boundaryPackage := by
    simpa [toPartitionReconstructionData] using boundaryPackage
  interiorBoundaryCancellation := by
    simpa [toPartitionReconstructionData] using interiorBoundaryCancellation
  chartChangeCancellation := by
    simpa [toPartitionReconstructionData] using chartChangeCancellation

@[simp]
theorem toMixedGlobalStokesData_reconstruction
    (D : BulkIntegralReconstructionData I' omega' Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D)
    (interiorBoundaryTerm : Chart -> InteriorPiece -> Real)
    (boundaryBoundaryTerm : Chart -> BoundaryPiece -> Real)
    (interiorPackage :
      MixedInteriorPackage I' omega' Chart InteriorPiece
        D.activeCharts D.interiorPieces D.interiorBulkTerm interiorBoundaryTerm)
    (boundaryPackage :
      MixedBoundaryPackage I' omega' Chart BoundaryPiece
        D.activeCharts D.boundaryPieces D.boundaryBulkTerm boundaryBoundaryTerm)
    (interiorBoundaryCancellation :
      (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.interiorPieces x) fun q =>
          interiorBoundaryTerm x q) = 0)
    (chartChangeCancellation :
      (Finset.sum D.activeCharts fun x =>
          Finset.sum (D.boundaryPieces x) fun q =>
            boundaryBoundaryTerm x q) =
        Finset.sum D.activeCharts fun x =>
          Finset.sum (D.boundaryPieces x) fun q =>
            B.boundaryPartitionTerm x q) :
    (D.toMixedGlobalStokesData B interiorBoundaryTerm boundaryBoundaryTerm
        interiorPackage boundaryPackage interiorBoundaryCancellation
        chartChangeCancellation).reconstruction =
      D.toPartitionReconstructionData B :=
  rfl

end GlobalStokesWrapper

end BulkIntegralReconstructionData

end IntegralReconstruction

end Stokes

end
