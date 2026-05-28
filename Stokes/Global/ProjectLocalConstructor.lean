import Stokes.Global.BoundaryChartChangePieces

/-!
# Project-local global Stokes constructor

This file provides a thin constructor layer for `ProjectLocalGlobalStokesData`.
It records the project-local chart/box inputs together with the remaining
reconstruction, local-Stokes, chart-change, and boundary-reconstruction fields,
then aligns those fields with the final theorem package.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section ProjectLocalConstructor

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Constructor input for the project-local final Stokes package.

The geometric fields name the finite project-local chart pieces directly.  The
last four fields are exactly the remaining assumptions needed by
`ProjectLocalGlobalStokesData`: bulk reconstruction, local project Stokes,
chart-change cancellation, and boundary reconstruction.
-/
structure ProjectLocalConstructorData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in the project-local decomposition. -/
  activeCharts : Finset Chart
  /-- Project-local pieces assigned to an active chart. -/
  localPieces : Chart → Finset Piece
  /-- Source chart for the project-local wrapper. -/
  sourceChart : Chart → Piece → M
  /-- Target chart for the project-local wrapper. -/
  targetChart : Chart → Piece → M
  /-- Lower corner of the selected coordinate box. -/
  lowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Upper corner of the selected coordinate box. -/
  upperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Boundary term after chart changes and partition reconstruction. -/
  boundaryPartitionTerm : Chart → Piece → Real
  /-- The global bulk integral represented by this constructor package. -/
  globalBulkIntegral : Real
  /-- The global boundary integral represented by this constructor package. -/
  globalBoundaryIntegral : Real
  /-- Reconstruction of the global bulk integral from project-local bulk terms. -/
  globalBulkIntegral_eq_projectLocalSum :
    globalBulkIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q =>
          projectLocalBulkIntegral I (sourceChart x q) (targetChart x q) ω
            (lowerCorner x q) (upperCorner x q)
  /-- Project-local Stokes on every active local piece. -/
  localProjectStokes :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ localPieces x →
        projectLocalBulkIntegral I (sourceChart x q) (targetChart x q) ω
            (lowerCorner x q) (upperCorner x q) =
          projectLocalBoundaryIntegral I (sourceChart x q) (targetChart x q) ω
            (lowerCorner x q) (upperCorner x q)
  /-- Compatibility of project-local boundary terms with the boundary partition. -/
  chartChangeCancellation :
    (Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q =>
          projectLocalBoundaryIntegral I (sourceChart x q) (targetChart x q) ω
            (lowerCorner x q) (upperCorner x q)) =
      Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q => boundaryPartitionTerm x q
  /-- Reconstruction of the global boundary integral from the boundary partition. -/
  globalBoundaryIntegral_eq_boundaryPartitionSum :
    globalBoundaryIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q => boundaryPartitionTerm x q

namespace ProjectLocalConstructorData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Bulk term of one recorded project-local piece. -/
def projectLocalBulkTerm
    (D : ProjectLocalConstructorData I ω Chart Piece) (x : Chart) (q : Piece) :
    Real :=
  projectLocalBulkIntegral I (D.sourceChart x q) (D.targetChart x q) ω
    (D.lowerCorner x q) (D.upperCorner x q)

/-- Boundary term of one recorded project-local piece. -/
def projectLocalBoundaryTerm
    (D : ProjectLocalConstructorData I ω Chart Piece) (x : Chart) (q : Piece) :
    Real :=
  projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
    (D.lowerCorner x q) (D.upperCorner x q)

/-- Sum of all project-local bulk terms. -/
def projectLocalBulkSum
    (D : ProjectLocalConstructorData I ω Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.localPieces x) fun q => projectLocalBulkTerm D x q

/-- Sum of all project-local boundary terms before boundary reconstruction. -/
def projectLocalBoundarySum
    (D : ProjectLocalConstructorData I ω Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.localPieces x) fun q => projectLocalBoundaryTerm D x q

/-- Sum of the selected boundary partition terms. -/
def boundaryPartitionSum
    (D : ProjectLocalConstructorData I ω Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.localPieces x) fun q => D.boundaryPartitionTerm x q

/--
Pointwise boundary chart-change equality fills the constructor package's
finite-sum chart-change field.
-/
theorem chartChangeCancellation_of_pointwise_eq
    (D : ProjectLocalConstructorData I ω Chart Piece)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          projectLocalBoundaryTerm D x q = D.boundaryPartitionTerm x q) :
    projectLocalBoundarySum D = boundaryPartitionSum D := by
  exact chartChangeCancellation_sum_eq_of_forall_eq D.activeCharts D.localPieces
    (projectLocalBoundaryTerm D) D.boundaryPartitionTerm hterm

/--
Instantiate the final `ProjectLocalGlobalStokesData` package from constructor
data.  This definition is only field alignment; all mathematical hypotheses
are already fields of `D`.
-/
def toProjectLocalGlobalStokesData
    (D : ProjectLocalConstructorData I ω Chart Piece) :
    ProjectLocalGlobalStokesData I ω Chart Piece where
  activeCharts := D.activeCharts
  localPieces := D.localPieces
  sourceChart := D.sourceChart
  targetChart := D.targetChart
  lowerCorner := D.lowerCorner
  upperCorner := D.upperCorner
  boundaryPartitionTerm := D.boundaryPartitionTerm
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral
  globalBulkIntegral_eq_projectLocalSum := D.globalBulkIntegral_eq_projectLocalSum
  localProjectStokes := D.localProjectStokes
  chartChangeCancellation := D.chartChangeCancellation
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    D.globalBoundaryIntegral_eq_boundaryPartitionSum

@[simp]
theorem toProjectLocalGlobalStokesData_globalBulkIntegral
    (D : ProjectLocalConstructorData I ω Chart Piece) :
    D.toProjectLocalGlobalStokesData.globalBulkIntegral = D.globalBulkIntegral :=
  rfl

@[simp]
theorem toProjectLocalGlobalStokesData_globalBoundaryIntegral
    (D : ProjectLocalConstructorData I ω Chart Piece) :
    D.toProjectLocalGlobalStokesData.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

/-- Project-local constructor theorem, via the instantiated final package. -/
theorem stokes
    (D : ProjectLocalConstructorData I ω Chart Piece) :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  ProjectLocalGlobalStokesData.stokes D.toProjectLocalGlobalStokesData

end ProjectLocalConstructorData

/-- Blueprint-facing wrapper for project-local constructor data. -/
theorem projectLocalConstructorGlobalStokes
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    {Chart : Type c} {Piece : Type p}
    (D : ProjectLocalConstructorData I ω Chart Piece) :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  D.stokes

end ProjectLocalConstructor

end Stokes

end
