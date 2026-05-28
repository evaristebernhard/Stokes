import Stokes.Global.LocalIntegral

/-!
# Final global Stokes theorem package

This file provides the blueprint-facing final theorem anchor for global Stokes.
It deliberately has no analytic proof obligations: all geometry, integration,
partition-of-unity reconstruction, chart-change compatibility, and cancellation
facts are explicit fields of the data packages below.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section GlobalTheorem

universe u w c i b p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Final-node data for global Stokes on a charted manifold.

The parameters `I` and `ω` record the model-with-corners and the differential
form.  The finite sets and real-valued term functions record the current
algebraic assembly layer.  Later analytic files should replace the explicit
reconstruction, cancellation, and chart-change fields by theorems.
-/
structure GlobalStokesData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (Chart : Type c) (InteriorPiece : Type i) (BoundaryPiece : Type b) where
  /-- Finite chart labels active in the chosen partition/cover. -/
  activeCharts : Finset Chart
  /-- Localized interior pieces assigned to an active chart. -/
  interiorPieces : Chart → Finset InteriorPiece
  /-- Localized boundary-chart pieces assigned to an active chart. -/
  boundaryPieces : Chart → Finset BoundaryPiece
  /-- Bulk contribution of an interior local piece. -/
  interiorBulkTerm : Chart → InteriorPiece → Real
  /-- Artificial boundary-side contribution of an interior local piece. -/
  interiorBoundaryTerm : Chart → InteriorPiece → Real
  /-- Bulk contribution of a boundary-chart local piece. -/
  boundaryBulkTerm : Chart → BoundaryPiece → Real
  /-- Boundary-chart contribution before global chart-change identification. -/
  boundaryBoundaryTerm : Chart → BoundaryPiece → Real
  /-- Boundary contribution after chart changes and partition reconstruction. -/
  boundaryPartitionTerm : Chart → BoundaryPiece → Real
  /-- The global bulk integral represented by this package. -/
  globalBulkIntegral : Real
  /-- The global boundary integral represented by this package. -/
  globalBoundaryIntegral : Real
  /-- Reconstruction of the global bulk integral from finitely many local pieces. -/
  globalBulkIntegral_eq_localBulkSum :
    globalBulkIntegral =
      (Finset.sum activeCharts fun x =>
          Finset.sum (interiorPieces x) fun q => interiorBulkTerm x q) +
        Finset.sum activeCharts fun x =>
          Finset.sum (boundaryPieces x) fun q => boundaryBulkTerm x q
  /-- Local Stokes on every recorded interior piece. -/
  interiorLocalStokes :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ interiorPieces x →
        interiorBulkTerm x q = interiorBoundaryTerm x q
  /-- Local Stokes on every recorded boundary-chart piece. -/
  boundaryLocalStokes :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x →
        boundaryBulkTerm x q = boundaryBoundaryTerm x q
  /-- Cancellation of artificial interior-chart boundary faces. -/
  interiorBoundaryCancellation :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun q => interiorBoundaryTerm x q) = 0
  /--
  Compatibility of boundary chart representatives with the chosen global
  boundary partition terms.
  -/
  chartChangeCancellation :
    (Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun q => boundaryBoundaryTerm x q) =
      Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun q => boundaryPartitionTerm x q
  /-- Reconstruction of the global boundary integral from the boundary partition. -/
  globalBoundaryIntegral_eq_boundaryPartitionSum :
    globalBoundaryIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun q => boundaryPartitionTerm x q

namespace GlobalStokesData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}

/-- Sum of all interior bulk terms in a global package. -/
def interiorBulkSum
    (D : GlobalStokesData I ω Chart InteriorPiece BoundaryPiece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.interiorPieces x) fun q => D.interiorBulkTerm x q

/-- Sum of all boundary-chart bulk terms in a global package. -/
def boundaryBulkSum
    (D : GlobalStokesData I ω Chart InteriorPiece BoundaryPiece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => D.boundaryBulkTerm x q

/-- Total local bulk side recorded in a global package. -/
def localBulkSum
    (D : GlobalStokesData I ω Chart InteriorPiece BoundaryPiece) : Real :=
  interiorBulkSum D + boundaryBulkSum D

/-- Sum of artificial boundary terms from interior chart pieces. -/
def interiorBoundarySum
    (D : GlobalStokesData I ω Chart InteriorPiece BoundaryPiece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.interiorPieces x) fun q => D.interiorBoundaryTerm x q

/-- Sum of boundary-chart terms before global chart-change identification. -/
def boundaryChartSum
    (D : GlobalStokesData I ω Chart InteriorPiece BoundaryPiece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => D.boundaryBoundaryTerm x q

/-- Boundary side after summing local Stokes identities, before cancellation. -/
def localBoundarySideSum
    (D : GlobalStokesData I ω Chart InteriorPiece BoundaryPiece) : Real :=
  interiorBoundarySum D + boundaryChartSum D

/-- Sum of boundary terms after chart changes and partition reconstruction. -/
def boundaryPartitionSum
    (D : GlobalStokesData I ω Chart InteriorPiece BoundaryPiece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => D.boundaryPartitionTerm x q

/-- Finite-sum transport of pointwise local Stokes identities. -/
theorem sum_localPieces
    {Piece : Type p} (active : Finset Chart) (pieces : Chart → Finset Piece)
    (bulk boundary : Chart → Piece → Real)
    (hlocal :
      ∀ x, x ∈ active →
        ∀ q, q ∈ pieces x →
          bulk x q = boundary x q) :
    (Finset.sum active fun x => Finset.sum (pieces x) fun q => bulk x q) =
      Finset.sum active fun x => Finset.sum (pieces x) fun q => boundary x q := by
  refine Finset.sum_congr rfl ?_
  intro x hx
  refine Finset.sum_congr rfl ?_
  intro q hq
  exact hlocal x hx q hq

/-- Interior local Stokes identities summed over all active interior pieces. -/
theorem interiorBulkSum_eq_interiorBoundarySum
    (D : GlobalStokesData I ω Chart InteriorPiece BoundaryPiece) :
    interiorBulkSum D = interiorBoundarySum D := by
  exact sum_localPieces D.activeCharts D.interiorPieces
    D.interiorBulkTerm D.interiorBoundaryTerm D.interiorLocalStokes

/-- Boundary-chart local Stokes identities summed over all active boundary pieces. -/
theorem boundaryBulkSum_eq_boundaryChartSum
    (D : GlobalStokesData I ω Chart InteriorPiece BoundaryPiece) :
    boundaryBulkSum D = boundaryChartSum D := by
  exact sum_localPieces D.activeCharts D.boundaryPieces
    D.boundaryBulkTerm D.boundaryBoundaryTerm D.boundaryLocalStokes

/-- Summing all recorded local Stokes identities gives equality of local sides. -/
theorem localBulkSum_eq_localBoundarySideSum
    (D : GlobalStokesData I ω Chart InteriorPiece BoundaryPiece) :
    localBulkSum D = localBoundarySideSum D := by
  rw [localBulkSum, localBoundarySideSum,
    interiorBulkSum_eq_interiorBoundarySum D,
    boundaryBulkSum_eq_boundaryChartSum D]

/-- After cancelling artificial interior faces, only boundary-chart terms remain. -/
theorem localBoundarySideSum_eq_boundaryChartSum
    (D : GlobalStokesData I ω Chart InteriorPiece BoundaryPiece) :
    localBoundarySideSum D = boundaryChartSum D := by
  rw [localBoundarySideSum, interiorBoundarySum, boundaryChartSum,
    D.interiorBoundaryCancellation, zero_add]

/--
After interior cancellation and chart-change compatibility, the local boundary
side is the reconstructed global boundary partition sum.
-/
theorem localBoundarySideSum_eq_boundaryPartitionSum
    (D : GlobalStokesData I ω Chart InteriorPiece BoundaryPiece) :
    localBoundarySideSum D = boundaryPartitionSum D := by
  calc
    localBoundarySideSum D = boundaryChartSum D :=
      localBoundarySideSum_eq_boundaryChartSum D
    _ = boundaryPartitionSum D := by
      rw [boundaryChartSum, boundaryPartitionSum]
      exact D.chartChangeCancellation

/--
Pure bookkeeping theorem for the final global Stokes package.

All analytic and geometric content is supplied by the fields of `D`.
-/
theorem stokes
    (D : GlobalStokesData I ω Chart InteriorPiece BoundaryPiece) :
    D.globalBulkIntegral = D.globalBoundaryIntegral := by
  calc
    D.globalBulkIntegral = localBulkSum D := by
      rw [localBulkSum, interiorBulkSum, boundaryBulkSum]
      exact D.globalBulkIntegral_eq_localBulkSum
    _ = localBoundarySideSum D := localBulkSum_eq_localBoundarySideSum D
    _ = boundaryPartitionSum D := localBoundarySideSum_eq_boundaryPartitionSum D
    _ = D.globalBoundaryIntegral := by
      rw [boundaryPartitionSum]
      exact D.globalBoundaryIntegral_eq_boundaryPartitionSum.symm

end GlobalStokesData

/-- Blueprint-facing final global Stokes theorem anchor. -/
theorem globalStokes
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}
    (D : GlobalStokesData I ω Chart InteriorPiece BoundaryPiece) :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  GlobalStokesData.stokes D

/--
Project-local specialization whose local terms are the wrappers from
`Stokes.Global.LocalIntegral`.

This is the package to instantiate directly from boundary-chart boxes while the
global integration layer is still being developed.
-/
structure ProjectLocalGlobalStokesData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in the chosen partition/cover. -/
  activeCharts : Finset Chart
  /-- Project-local chart pieces assigned to an active chart. -/
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
  /-- The global bulk integral represented by this package. -/
  globalBulkIntegral : Real
  /-- The global boundary integral represented by this package. -/
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

namespace ProjectLocalGlobalStokesData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Sum of project-local bulk wrapper terms. -/
def projectLocalBulkSum
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.localPieces x) fun q =>
      projectLocalBulkIntegral I (D.sourceChart x q) (D.targetChart x q) ω
        (D.lowerCorner x q) (D.upperCorner x q)

/-- Sum of project-local boundary wrapper terms before global reconstruction. -/
def projectLocalBoundarySum
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.localPieces x) fun q =>
      projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
        (D.lowerCorner x q) (D.upperCorner x q)

/-- Sum of boundary partition terms. -/
def boundaryPartitionSum
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.localPieces x) fun q => D.boundaryPartitionTerm x q

/-- Project-local Stokes identities summed over all active local pieces. -/
theorem projectLocalBulkSum_eq_projectLocalBoundarySum
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    projectLocalBulkSum D = projectLocalBoundarySum D := by
  exact GlobalStokesData.sum_localPieces D.activeCharts D.localPieces
    (fun x q =>
      projectLocalBulkIntegral I (D.sourceChart x q) (D.targetChart x q) ω
        (D.lowerCorner x q) (D.upperCorner x q))
    (fun x q =>
      projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
        (D.lowerCorner x q) (D.upperCorner x q))
    D.localProjectStokes

/-- Project-local global Stokes package theorem. -/
theorem stokes
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    D.globalBulkIntegral = D.globalBoundaryIntegral := by
  calc
    D.globalBulkIntegral = projectLocalBulkSum D := by
      rw [projectLocalBulkSum]
      exact D.globalBulkIntegral_eq_projectLocalSum
    _ = projectLocalBoundarySum D :=
      projectLocalBulkSum_eq_projectLocalBoundarySum D
    _ = boundaryPartitionSum D := by
      rw [projectLocalBoundarySum, boundaryPartitionSum]
      exact D.chartChangeCancellation
    _ = D.globalBoundaryIntegral := by
      rw [boundaryPartitionSum]
      exact D.globalBoundaryIntegral_eq_boundaryPartitionSum.symm

end ProjectLocalGlobalStokesData

/--
Blueprint-facing final theorem anchor for the project-local wrapper package.
-/
theorem projectLocalGlobalStokes
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    {Chart : Type c} {Piece : Type p}
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  ProjectLocalGlobalStokesData.stokes D

end GlobalTheorem

end Stokes

end
