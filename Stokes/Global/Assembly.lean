import Stokes.Global.InteriorChart
import Stokes.BoundaryChart.Convenience

/-!
# Global Stokes assembly skeleton

This module is the algebraic interface between the local chart Stokes theorems
and the future partition-of-unity/global-integral layer.  The analytic and
geometric inputs are recorded as fields: this file only proves that finite sums
of local equalities assemble to a finite-cover equality.
-/

noncomputable section

open scoped BigOperators

namespace Stokes

/--
Data needed to assemble finitely many local Stokes identities.

The two piece types are intentionally abstract.  Later modules can instantiate
them with partition-localized forms supported in selected interior or boundary
chart boxes.  The cancellation and chart-change fields are explicit hypotheses
to be supplied by the global integration layer, not proved here.
-/
structure GlobalStokesAssemblyData
    (Chart InteriorPiece BoundaryPiece : Type*) where
  /-- Finite set of chart labels active in the chosen cover/partition. -/
  activeCharts : Finset Chart
  /-- Interior local pieces assigned to each active chart. -/
  interiorPieces : Chart → Finset InteriorPiece
  /-- Boundary local pieces assigned to each active chart. -/
  boundaryPieces : Chart → Finset BoundaryPiece
  /-- Bulk contribution of an interior local piece. -/
  interiorBulkTerm : Chart → InteriorPiece → Real
  /-- Boundary-side contribution of an interior local piece. -/
  interiorBoundaryTerm : Chart → InteriorPiece → Real
  /-- Bulk contribution of a boundary local piece. -/
  boundaryBulkTerm : Chart → BoundaryPiece → Real
  /-- Outward-first boundary contribution of a boundary local piece. -/
  boundaryBoundaryTerm : Chart → BoundaryPiece → Real
  /-- The global/project-local bulk integral represented by this package. -/
  globalBulkIntegral : Real
  /-- The global/project-local boundary integral represented by this package. -/
  globalBoundaryIntegral : Real
  /-- The bulk integral has been reduced to the finite sum of recorded bulk terms. -/
  globalBulkIntegral_eq_localSum :
    globalBulkIntegral =
      (Finset.sum activeCharts fun x =>
          Finset.sum (interiorPieces x) fun p => interiorBulkTerm x p) +
        Finset.sum activeCharts fun x =>
          Finset.sum (boundaryPieces x) fun p => boundaryBulkTerm x p
  /--
  The boundary integral has been reduced to the finite sum of the genuine
  boundary-chart terms.
  -/
  globalBoundaryIntegral_eq_boundaryLocalSum :
    globalBoundaryIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun p => boundaryBoundaryTerm x p
  /-- Local Stokes identity for every recorded interior piece. -/
  interiorLocalStokes :
    ∀ x, x ∈ activeCharts →
      ∀ p, p ∈ interiorPieces x →
        interiorBulkTerm x p = interiorBoundaryTerm x p
  /-- Local Stokes identity for every recorded boundary piece. -/
  boundaryLocalStokes :
    ∀ x, x ∈ activeCharts →
      ∀ p, p ∈ boundaryPieces x →
        boundaryBulkTerm x p = boundaryBoundaryTerm x p
  /--
  Artificial boundary contributions from interior chart boxes cancel in the
  finite assembly.
  -/
  interiorBoundaryCancellation :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun p => interiorBoundaryTerm x p) = 0
  /--
  Placeholder for the chart-change invariance package used to identify boundary
  chart representatives with the chosen global boundary integral.
  -/
  chartChangeInvariance : Prop
  /-- The chart-change invariance package is an explicit assumption. -/
  chartChangeInvariance_holds : chartChangeInvariance

/-- Sum of the interior bulk terms recorded in an assembly package. -/
def assembledInteriorBulkIntegral
    {Chart InteriorPiece BoundaryPiece : Type*}
    (D : GlobalStokesAssemblyData Chart InteriorPiece BoundaryPiece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.interiorPieces x) fun p => D.interiorBulkTerm x p

/-- Sum of the boundary-chart bulk terms recorded in an assembly package. -/
def assembledBoundaryBulkIntegral
    {Chart InteriorPiece BoundaryPiece : Type*}
    (D : GlobalStokesAssemblyData Chart InteriorPiece BoundaryPiece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun p => D.boundaryBulkTerm x p

/-- Total assembled bulk integral, split into interior and boundary chart pieces. -/
def assembledBulkIntegral
    {Chart InteriorPiece BoundaryPiece : Type*}
    (D : GlobalStokesAssemblyData Chart InteriorPiece BoundaryPiece) : Real :=
  assembledInteriorBulkIntegral D + assembledBoundaryBulkIntegral D

/-- Sum of the interior boundary-side terms recorded in an assembly package. -/
def assembledInteriorBoundaryIntegral
    {Chart InteriorPiece BoundaryPiece : Type*}
    (D : GlobalStokesAssemblyData Chart InteriorPiece BoundaryPiece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.interiorPieces x) fun p => D.interiorBoundaryTerm x p

/-- Sum of the genuine boundary-chart terms recorded in an assembly package. -/
def assembledBoundaryChartIntegral
    {Chart InteriorPiece BoundaryPiece : Type*}
    (D : GlobalStokesAssemblyData Chart InteriorPiece BoundaryPiece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun p => D.boundaryBoundaryTerm x p

/--
Total assembled boundary side before cancelling the artificial interior faces.
-/
def assembledBoundaryIntegral
    {Chart InteriorPiece BoundaryPiece : Type*}
    (D : GlobalStokesAssemblyData Chart InteriorPiece BoundaryPiece) : Real :=
  assembledInteriorBoundaryIntegral D + assembledBoundaryChartIntegral D

/--
Pure finite-sum assembly for a single chart-indexed family of local equalities.
-/
theorem sum_localStokes
    {Chart Piece : Type*} (active : Finset Chart) (pieces : Chart → Finset Piece)
    (bulk boundary : Chart → Piece → Real)
    (hlocal :
      ∀ x, x ∈ active → ∀ p, p ∈ pieces x → bulk x p = boundary x p) :
    (Finset.sum active fun x => Finset.sum (pieces x) fun p => bulk x p) =
      Finset.sum active fun x => Finset.sum (pieces x) fun p => boundary x p := by
  refine Finset.sum_congr rfl ?_
  intro x hx
  refine Finset.sum_congr rfl ?_
  intro p hp
  exact hlocal x hx p hp

/--
Pure finite-sum assembly for the interior and boundary local families together.
-/
theorem sum_interior_boundary_localStokes
    {Chart InteriorPiece BoundaryPiece : Type*}
    (active : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (boundaryPieces : Chart → Finset BoundaryPiece)
    (interiorBulk interiorBoundary : Chart → InteriorPiece → Real)
    (boundaryBulk boundaryBoundary : Chart → BoundaryPiece → Real)
    (hinterior :
      ∀ x, x ∈ active →
        ∀ p, p ∈ interiorPieces x →
          interiorBulk x p = interiorBoundary x p)
    (hboundary :
      ∀ x, x ∈ active →
        ∀ p, p ∈ boundaryPieces x →
          boundaryBulk x p = boundaryBoundary x p) :
    ((Finset.sum active fun x =>
          Finset.sum (interiorPieces x) fun p => interiorBulk x p) +
        Finset.sum active fun x =>
          Finset.sum (boundaryPieces x) fun p => boundaryBulk x p) =
      (Finset.sum active fun x =>
          Finset.sum (interiorPieces x) fun p => interiorBoundary x p) +
        Finset.sum active fun x =>
          Finset.sum (boundaryPieces x) fun p => boundaryBoundary x p := by
  rw [sum_localStokes active interiorPieces interiorBulk interiorBoundary hinterior,
    sum_localStokes active boundaryPieces boundaryBulk boundaryBoundary hboundary]

/--
The recorded interior local Stokes identities assemble to equality of the
interior sums.
-/
theorem assembledInteriorBulkIntegral_eq_boundary
    {Chart InteriorPiece BoundaryPiece : Type*}
    (D : GlobalStokesAssemblyData Chart InteriorPiece BoundaryPiece) :
    assembledInteriorBulkIntegral D = assembledInteriorBoundaryIntegral D := by
  exact sum_localStokes D.activeCharts D.interiorPieces D.interiorBulkTerm
    D.interiorBoundaryTerm D.interiorLocalStokes

/--
The recorded boundary local Stokes identities assemble to equality of the
boundary-chart sums.
-/
theorem assembledBoundaryBulkIntegral_eq_boundary
    {Chart InteriorPiece BoundaryPiece : Type*}
    (D : GlobalStokesAssemblyData Chart InteriorPiece BoundaryPiece) :
    assembledBoundaryBulkIntegral D = assembledBoundaryChartIntegral D := by
  exact sum_localStokes D.activeCharts D.boundaryPieces D.boundaryBulkTerm
    D.boundaryBoundaryTerm D.boundaryLocalStokes

/--
Finite-cover assembly: summing all recorded local Stokes identities gives the
assembled bulk equality before cancelling artificial interior boundary faces.
-/
theorem assembledBulkIntegral_eq_assembledBoundaryIntegral
    {Chart InteriorPiece BoundaryPiece : Type*}
    (D : GlobalStokesAssemblyData Chart InteriorPiece BoundaryPiece) :
    assembledBulkIntegral D = assembledBoundaryIntegral D := by
  rw [assembledBulkIntegral, assembledBoundaryIntegral,
    assembledInteriorBulkIntegral_eq_boundary D,
    assembledBoundaryBulkIntegral_eq_boundary D]

/--
After the interior artificial boundary terms cancel, the assembled boundary side
is exactly the finite sum of genuine boundary-chart terms.
-/
theorem assembledBoundaryIntegral_eq_boundaryChartIntegral
    {Chart InteriorPiece BoundaryPiece : Type*}
    (D : GlobalStokesAssemblyData Chart InteriorPiece BoundaryPiece) :
    assembledBoundaryIntegral D = assembledBoundaryChartIntegral D := by
  rw [assembledBoundaryIntegral, assembledInteriorBoundaryIntegral,
    D.interiorBoundaryCancellation, zero_add]

/--
Algebraic global assembly theorem.  The only proof work here is finite-sum
bookkeeping; the fields of `D` provide the local Stokes equalities, the local
sum reductions, and the artificial-boundary cancellation.
-/
theorem globalStokesAssembly
    {Chart InteriorPiece BoundaryPiece : Type*}
    (D : GlobalStokesAssemblyData Chart InteriorPiece BoundaryPiece) :
    D.globalBulkIntegral = D.globalBoundaryIntegral := by
  calc
    D.globalBulkIntegral = assembledBulkIntegral D := D.globalBulkIntegral_eq_localSum
    _ = assembledBoundaryIntegral D := assembledBulkIntegral_eq_assembledBoundaryIntegral D
    _ = assembledBoundaryChartIntegral D := assembledBoundaryIntegral_eq_boundaryChartIntegral D
    _ = D.globalBoundaryIntegral := D.globalBoundaryIntegral_eq_boundaryLocalSum.symm

/--
Blueprint-facing alias for the finite sum of local chart-supported Stokes
identities.
-/
theorem sum_localChartSupportedStokes
    {Chart InteriorPiece BoundaryPiece : Type*}
    (D : GlobalStokesAssemblyData Chart InteriorPiece BoundaryPiece) :
    assembledBulkIntegral D = assembledBoundaryIntegral D :=
  assembledBulkIntegral_eq_assembledBoundaryIntegral D

end Stokes

end
