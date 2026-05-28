import Stokes.Global.BoundaryPieces
import Stokes.Global.ChartChange

/-!
# Boundary global constructor

This file is a thin constructor layer for the boundary-only global Stokes
package.  It combines oriented boundary pieces, pointwise chart-change family
data, and the still-external boundary reconstruction equality into the final
`GlobalStokesData` shape.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryGlobalConstructor

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Chart-change family data for an oriented boundary-piece package.

This records the pointwise identification between the transported boundary
chart representative already produced by `OrientedBoundaryProjectLocalPieces`
and the chosen boundary-partition term.  The finite-sum cancellation field for
`GlobalStokesData` is derived from this family.
-/
structure OrientedBoundaryChartChangeFamilyData {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    {Chart : Type c} {Piece : Type p}
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece) where
  /-- Pointwise chart-change equality on every active boundary piece. -/
  term_eq :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        OrientedBoundaryProjectLocalPieces.projectLocalBoundaryTerm D x q =
          D.boundaryPartitionTerm x q

namespace OrientedBoundaryChartChangeFamilyData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}
variable {D : OrientedBoundaryProjectLocalPieces I ω Chart Piece}

/-- View oriented boundary chart-change family data as pure finite-sum data. -/
def toChartChangeCancellationData
    (F : OrientedBoundaryChartChangeFamilyData D) :
    ChartChangeCancellationData Chart Piece Real where
  activeCharts := D.activeCharts
  boundaryPieces := D.localPieces
  oldBoundaryTerm := OrientedBoundaryProjectLocalPieces.projectLocalBoundaryTerm D
  newBoundaryTerm := D.boundaryPartitionTerm
  term_eq := F.term_eq

/-- The pointwise oriented boundary chart-change family assembles to finite sums. -/
theorem chartChangeCancellation
    (F : OrientedBoundaryChartChangeFamilyData D) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q =>
          OrientedBoundaryProjectLocalPieces.projectLocalBoundaryTerm D x q) =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q => D.boundaryPartitionTerm x q := by
  simpa [toChartChangeCancellationData] using
    (ChartChangeCancellationData.chartChangeCancellation
      (F.toChartChangeCancellationData))

end OrientedBoundaryChartChangeFamilyData

/--
Constructor data for boundary-only global Stokes.

The boundary reconstruction equality is intentionally a field: the global
partition/integration layer is still responsible for proving it.
-/
structure BoundaryGlobalConstructorData {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    {Chart : Type c} {Piece : Type p}
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece) where
  /-- Pointwise chart-change family for the recorded boundary pieces. -/
  chartChangeFamily : OrientedBoundaryChartChangeFamilyData D
  /-- Reconstruction of the global boundary integral from the partition terms. -/
  globalBoundaryIntegral_eq_boundaryPartitionSum :
    D.globalBoundaryIntegral =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q => D.boundaryPartitionTerm x q

namespace BoundaryGlobalConstructorData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}
variable {D : OrientedBoundaryProjectLocalPieces I ω Chart Piece}

/--
Build `GlobalStokesData` from oriented-atlas boundary pieces, chart-change
family data, and the boundary reconstruction field.
-/
def toGlobalStokesData_of_orientedAtlas
    [IsManifold I 1 M]
    (C : BoundaryGlobalConstructorData D)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.boundarySourceChart x q ∈ A.charts) :
    GlobalStokesData I ω Chart Empty Piece where
  activeCharts := D.activeCharts
  interiorPieces := fun _ => ∅
  boundaryPieces := D.localPieces
  interiorBulkTerm := fun _ q => Empty.elim q
  interiorBoundaryTerm := fun _ q => Empty.elim q
  boundaryBulkTerm := OrientedBoundaryProjectLocalPieces.projectLocalBulkTerm D
  boundaryBoundaryTerm := OrientedBoundaryProjectLocalPieces.projectLocalBoundaryTerm D
  boundaryPartitionTerm := D.boundaryPartitionTerm
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum := by
    simpa [OrientedBoundaryProjectLocalPieces.projectLocalBulkTerm] using
      D.globalBulkIntegral_eq_localBulkSum
  interiorLocalStokes := by
    intro _ _ q _
    cases q
  boundaryLocalStokes :=
    D.localProjectStokes_of_orientedAtlas A hsource hboundarySource
  interiorBoundaryCancellation := by
    simp
  chartChangeCancellation := by
    simpa using C.chartChangeFamily.chartChangeCancellation
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    C.globalBoundaryIntegral_eq_boundaryPartitionSum

/--
Build `GlobalStokesData` from oriented-boundary-manifold pieces, chart-change
family data, and the boundary reconstruction field.
-/
def toGlobalStokesData_of_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (C : BoundaryGlobalConstructorData D) :
    GlobalStokesData I ω Chart Empty Piece where
  activeCharts := D.activeCharts
  interiorPieces := fun _ => ∅
  boundaryPieces := D.localPieces
  interiorBulkTerm := fun _ q => Empty.elim q
  interiorBoundaryTerm := fun _ q => Empty.elim q
  boundaryBulkTerm := OrientedBoundaryProjectLocalPieces.projectLocalBulkTerm D
  boundaryBoundaryTerm := OrientedBoundaryProjectLocalPieces.projectLocalBoundaryTerm D
  boundaryPartitionTerm := D.boundaryPartitionTerm
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum := by
    simpa [OrientedBoundaryProjectLocalPieces.projectLocalBulkTerm] using
      D.globalBulkIntegral_eq_localBulkSum
  interiorLocalStokes := by
    intro _ _ q _
    cases q
  boundaryLocalStokes := D.localProjectStokes_of_orientedManifold
  interiorBoundaryCancellation := by
    simp
  chartChangeCancellation := by
    simpa using C.chartChangeFamily.chartChangeCancellation
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    C.globalBoundaryIntegral_eq_boundaryPartitionSum

end BoundaryGlobalConstructorData

/-- Final boundary-global Stokes wrapper from oriented-atlas constructor data. -/
theorem boundaryGlobalStokes_of_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    {ω : ManifoldForm I M n}
    {Chart : Type c} {Piece : Type p}
    {D : OrientedBoundaryProjectLocalPieces I ω Chart Piece}
    (C : BoundaryGlobalConstructorData D)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.boundarySourceChart x q ∈ A.charts) :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  GlobalStokesData.stokes
    (C.toGlobalStokesData_of_orientedAtlas A hsource hboundarySource)

/-- Final boundary-global Stokes wrapper from oriented-boundary-manifold data. -/
theorem boundaryGlobalStokes_of_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    {ω : ManifoldForm I M n}
    {Chart : Type c} {Piece : Type p}
    {D : OrientedBoundaryProjectLocalPieces I ω Chart Piece}
    (C : BoundaryGlobalConstructorData D) :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  GlobalStokesData.stokes C.toGlobalStokesData_of_orientedManifold

end BoundaryGlobalConstructor

end Stokes

end
