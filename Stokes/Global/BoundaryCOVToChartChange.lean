import Stokes.BoundaryChart.ChangeOfVariablesFamily
import Stokes.Global.BoundaryChartChangePieces
import Stokes.Global.BoundaryPieces

/-!
# Boundary COV families as global chart-change data

This file is an adapter layer between the pure `BoundaryChart` finite-family
change-of-variables package and the global chart-change/cancellation packages.
It does not add analytic content: all proofs are field alignments plus the
already packaged pointwise boundary COV theorem.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryCOVToChartChange

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace BoundaryChartChangeOfVariablesFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/--
View a pure boundary chart change-of-variables family as global algebraic
chart-change cancellation data.

The old and new terms are still the pure boundary-chart representatives from
`BoundaryChart.ChangeOfVariablesFamily`; this is useful before tying the family
to a project-local global package.
-/
def toChartChangeCancellationData [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece) :
    ChartChangeCancellationData Chart Piece Real where
  activeCharts := F.activeCharts
  boundaryPieces := F.localPieces
  oldBoundaryTerm := F.sourceBoundaryTerm
  newBoundaryTerm := F.targetBoundaryTerm
  term_eq := F.pointwise_eq_targetBoundary

/-- The pure COV family, viewed through `ChartChangeCancellationData`, sums. -/
theorem chartChangeCancellation [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece) :
    (Finset.sum F.activeCharts fun x =>
        Finset.sum (F.localPieces x) fun q => F.sourceBoundaryTerm x q) =
      Finset.sum F.activeCharts fun x =>
        Finset.sum (F.localPieces x) fun q => F.targetBoundaryTerm x q := by
  exact F.toChartChangeCancellationData.chartChangeCancellation

/--
Compatibility data aligning a pure boundary COV family with a project-local
global Stokes package.

The source project-local term of `D` is identified with the source side of
`F`; the project-local target chart is the boundary-source chart of `F`; and
the boundary partition term of `D` is the transported target boundary term of
`F` on every active piece.
-/
structure ProjectLocalChartChangeCompatibility
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) where
  /-- The active chart labels agree. -/
  activeCharts_eq : D.activeCharts = F.activeCharts
  /-- The local boundary-piece labels agree pointwise. -/
  localPieces_eq : ∀ x, D.localPieces x = F.localPieces x
  /-- Project-local source charts are the pure-family source charts. -/
  sourceChart_eq : ∀ x q, D.sourceChart x q = F.sourceChart x q
  /-- Project-local target charts are the pure-family boundary source charts. -/
  targetChart_eq : ∀ x q, D.targetChart x q = F.boundarySourceChart x q
  /-- Project-local lower corners are the pure-family source lower corners. -/
  lowerCorner_eq : ∀ x q, D.lowerCorner x q = F.sourceLowerCorner x q
  /-- Project-local upper corners are the pure-family source upper corners. -/
  upperCorner_eq : ∀ x q, D.upperCorner x q = F.sourceUpperCorner x q
  /-- The chosen global boundary partition term is the pure-family target term. -/
  boundaryPartitionTerm_eq :
    ∀ x, x ∈ F.activeCharts →
      ∀ q, q ∈ F.localPieces x →
        D.boundaryPartitionTerm x q = F.targetBoundaryTerm x q

namespace ProjectLocalChartChangeCompatibility

variable {F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece}
variable {D : ProjectLocalGlobalStokesData I ω Chart Piece}

/-- Convert active membership from the global package to the pure family. -/
theorem mem_active
    (C : ProjectLocalChartChangeCompatibility F D)
    {x : Chart} (hx : x ∈ D.activeCharts) :
    x ∈ F.activeCharts := by
  simpa [C.activeCharts_eq] using hx

/-- Convert local-piece membership from the global package to the pure family. -/
theorem mem_localPiece
    (C : ProjectLocalChartChangeCompatibility F D)
    {x : Chart} {q : Piece} (hq : q ∈ D.localPieces x) :
    q ∈ F.localPieces x := by
  simpa [C.localPieces_eq x] using hq

end ProjectLocalChartChangeCompatibility

/--
One selected-target global chart-change piece extracted from a pure COV family
aligned with a project-local global package.
-/
def selectedPieceData
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    {D : ProjectLocalGlobalStokesData I ω Chart Piece}
    (C : ProjectLocalChartChangeCompatibility F D)
    (x : Chart) (hx : x ∈ D.activeCharts)
    (q : Piece) (hq : q ∈ D.localPieces x) :
    BoundaryChartChangeSelectedPieceData I ω (D.sourceChart x q) (D.targetChart x q)
      (D.lowerCorner x q) (D.upperCorner x q) where
  boundaryTargetChart := F.boundaryTargetChart x q
  targetLowerCorner := F.targetLowerCorner x q
  targetUpperCorner := F.targetUpperCorner x q
  changeOfVariables := by
    simpa [C.sourceChart_eq x q, C.targetChart_eq x q,
      C.lowerCorner_eq x q, C.upperCorner_eq x q] using
      F.changeOfVariables x (C.mem_active hx) q (C.mem_localPiece hq)
  targetBox := by
    simpa [C.targetChart_eq x q] using
      F.targetSelectedBox x (C.mem_active hx) q (C.mem_localPiece hq)

/--
Adapt a pure boundary COV family to the selected-target global
`BoundaryChartChangeFamilyData` package.
-/
def toBoundaryChartChangeSelectedFamilyData
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    {D : ProjectLocalGlobalStokesData I ω Chart Piece}
    (C : ProjectLocalChartChangeCompatibility F D) :
    BoundaryChartChangeSelectedFamilyData D where
  pieceData := fun x hx q hq => F.selectedPieceData C x hx q hq
  boundaryPartitionTerm_eq := by
    intro x hx q hq
    simpa [selectedPieceData, targetBoundaryTerm, projectLocalBoundaryIntegral,
      C.targetChart_eq x q] using
      C.boundaryPartitionTerm_eq x (C.mem_active hx) q (C.mem_localPiece hq)

/--
The adapted selected-target family supplies the project-local global
`ChartChangeCancellationData`.
-/
def toProjectLocalChartChangeCancellationData [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    {D : ProjectLocalGlobalStokesData I ω Chart Piece}
    (C : ProjectLocalChartChangeCompatibility F D) :
    ChartChangeCancellationData Chart Piece Real :=
  (F.toBoundaryChartChangeSelectedFamilyData C).toChartChangeCancellationData_selected

/--
Expanded project-local chart-change cancellation obtained from the pure COV
family adapter.
-/
theorem projectLocal_chartChangeCancellation [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    {D : ProjectLocalGlobalStokesData I ω Chart Piece}
    (C : ProjectLocalChartChangeCompatibility F D) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q =>
          projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
            (D.lowerCorner x q) (D.upperCorner x q)) =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q => D.boundaryPartitionTerm x q := by
  exact (F.toProjectLocalChartChangeCancellationData C).chartChangeCancellation

end BoundaryChartChangeOfVariablesFamily

end BoundaryCOVToChartChange

end Stokes

end
