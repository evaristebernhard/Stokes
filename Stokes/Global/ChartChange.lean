import Stokes.Global.Theorem

/-!
# Global chart-change cancellation package

This file isolates the algebraic layer needed by the global Stokes packages:
if every active boundary-chart term is identified with its chosen partition
representative, then the corresponding finite sums are equal.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section Algebra

universe c p v

/--
Pure chart-change cancellation data for a finite chart-indexed family.

The `oldBoundaryTerm` side is the local boundary-chart representative before
chart changes.  The `newBoundaryTerm` side is the representative after chart
changes and boundary-partition reconstruction.
-/
structure ChartChangeCancellationData
    (Chart : Type c) (Piece : Type p) (R : Type v) [AddCommMonoid R] where
  /-- Finite chart labels active in the chosen cover/partition. -/
  activeCharts : Finset Chart
  /-- Boundary pieces assigned to an active chart. -/
  boundaryPieces : Chart → Finset Piece
  /-- Boundary-chart contribution before chart-change identification. -/
  oldBoundaryTerm : Chart → Piece → R
  /-- Boundary contribution after chart changes and reconstruction. -/
  newBoundaryTerm : Chart → Piece → R
  /-- Pointwise chart-change equality on every active boundary piece. -/
  term_eq :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x →
        oldBoundaryTerm x q = newBoundaryTerm x q

variable {Chart : Type c} {Piece : Type p} {R : Type v} [AddCommMonoid R]

/--
Finite-sum transport for chart-change equalities over a chart-indexed family.

This is the algebraic theorem used to fill the `chartChangeCancellation` fields
of the global packages once the analytic chart-change theorem has supplied
pointwise equalities.
-/
theorem chartChangeCancellation_sum_eq_of_forall_eq
    (active : Finset Chart) (pieces : Chart → Finset Piece)
    (oldTerm newTerm : Chart → Piece → R)
    (hterm :
      ∀ x, x ∈ active →
        ∀ q, q ∈ pieces x →
          oldTerm x q = newTerm x q) :
    (Finset.sum active fun x => Finset.sum (pieces x) fun q => oldTerm x q) =
      Finset.sum active fun x => Finset.sum (pieces x) fun q => newTerm x q := by
  refine Finset.sum_congr rfl ?_
  intro x hx
  refine Finset.sum_congr rfl ?_
  intro q hq
  exact hterm x hx q hq

namespace ChartChangeCancellationData

/-- Sum of the boundary-chart representatives before chart changes. -/
def oldBoundarySum
    (D : ChartChangeCancellationData Chart Piece R) : R :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => D.oldBoundaryTerm x q

/-- Sum of the boundary representatives after chart changes. -/
def newBoundarySum
    (D : ChartChangeCancellationData Chart Piece R) : R :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => D.newBoundaryTerm x q

/-- The pointwise chart-change equalities assemble to equality of finite sums. -/
theorem sum_eq
    (D : ChartChangeCancellationData Chart Piece R) :
    oldBoundarySum D = newBoundarySum D := by
  exact chartChangeCancellation_sum_eq_of_forall_eq D.activeCharts D.boundaryPieces
    D.oldBoundaryTerm D.newBoundaryTerm D.term_eq

/--
Expanded form of `sum_eq`, suitable for use where the global packages expect
the chart-change cancellation field directly.
-/
theorem chartChangeCancellation
    (D : ChartChangeCancellationData Chart Piece R) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.boundaryPieces x) fun q => D.oldBoundaryTerm x q) =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.boundaryPieces x) fun q => D.newBoundaryTerm x q := by
  exact D.sum_eq

end ChartChangeCancellationData

end Algebra

section GlobalPackages

universe u w c i p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace GlobalStokesData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type p}

/-- Extract the chart-change algebra package from pointwise boundary equalities. -/
def chartChangeCancellationDataOfPointwiseEq
    (D : GlobalStokesData I ω Chart InteriorPiece BoundaryPiece)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          D.boundaryBoundaryTerm x q = D.boundaryPartitionTerm x q) :
    ChartChangeCancellationData Chart BoundaryPiece Real where
  activeCharts := D.activeCharts
  boundaryPieces := D.boundaryPieces
  oldBoundaryTerm := D.boundaryBoundaryTerm
  newBoundaryTerm := D.boundaryPartitionTerm
  term_eq := hterm

/--
Pointwise chart-change equality fills `GlobalStokesData.chartChangeCancellation`.
-/
theorem chartChangeCancellation_of_pointwise_eq
    (D : GlobalStokesData I ω Chart InteriorPiece BoundaryPiece)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          D.boundaryBoundaryTerm x q = D.boundaryPartitionTerm x q) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.boundaryPieces x) fun q => D.boundaryBoundaryTerm x q) =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.boundaryPieces x) fun q => D.boundaryPartitionTerm x q := by
  exact (chartChangeCancellationDataOfPointwiseEq D hterm).chartChangeCancellation

end GlobalStokesData

namespace ProjectLocalGlobalStokesData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Extract the chart-change algebra package from project-local pointwise equalities. -/
def chartChangeCancellationDataOfPointwiseEq
    (D : ProjectLocalGlobalStokesData I ω Chart Piece)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
              (D.lowerCorner x q) (D.upperCorner x q) =
            D.boundaryPartitionTerm x q) :
    ChartChangeCancellationData Chart Piece Real where
  activeCharts := D.activeCharts
  boundaryPieces := D.localPieces
  oldBoundaryTerm := fun x q =>
    projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
      (D.lowerCorner x q) (D.upperCorner x q)
  newBoundaryTerm := D.boundaryPartitionTerm
  term_eq := hterm

/--
Pointwise chart-change equality fills
`ProjectLocalGlobalStokesData.chartChangeCancellation`.
-/
theorem chartChangeCancellation_of_pointwise_eq
    (D : ProjectLocalGlobalStokesData I ω Chart Piece)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
              (D.lowerCorner x q) (D.upperCorner x q) =
            D.boundaryPartitionTerm x q) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q =>
          projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
            (D.lowerCorner x q) (D.upperCorner x q)) =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q => D.boundaryPartitionTerm x q := by
  exact (chartChangeCancellationDataOfPointwiseEq D hterm).chartChangeCancellation

end ProjectLocalGlobalStokesData

end GlobalPackages

section ProjectLocalWrappers

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Project-local wrapper for the selected-target boundary chart
change-of-variables theorem.
-/
theorem projectLocalBoundaryIntegral_chartChange_selected
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hchange : boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d) :
    projectLocalBoundaryIntegral I x0 x1 ω a b =
      projectLocalBoundaryIntegral I x1 x2 ω c d := by
  simpa [projectLocalBoundaryIntegral] using
    outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables_selected
      x0 x1 x2 ω a b c d hchange hboxTarget

/--
Project-local wrapper for the extended-target boundary chart
change-of-variables theorem.
-/
theorem projectLocalBoundaryIntegral_chartChange_extended
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hchange : boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d)
    (hboxTarget : boundaryChartExtendedBox I x1 x2 ω c d) :
    projectLocalBoundaryIntegral I x0 x1 ω a b =
      projectLocalBoundaryIntegral I x1 x2 ω c d := by
  simpa [projectLocalBoundaryIntegral] using
    outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables_extended
      x0 x1 x2 ω a b c d hchange hboxTarget

/--
Finite-sum project-local chart-change equality from selected-target local
change-of-variables data on every active piece.
-/
theorem projectLocalBoundarySum_chartChange_selected
    {Chart : Type c} {Piece : Type p}
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (active : Finset Chart) (pieces : Chart → Finset Piece)
    (x0 x1 x2 : Chart → Piece → M) (ω : ManifoldForm I M n)
    (a b c d : Chart → Piece → Fin (n + 1) → Real)
    (hchange :
      ∀ x, x ∈ active →
        ∀ q, q ∈ pieces x →
          boundaryChartOrientedChangeOfVariables I (x0 x q) (x1 x q) ω
            (a x q) (b x q) (c x q) (d x q))
    (hboxTarget :
      ∀ x, x ∈ active →
        ∀ q, q ∈ pieces x →
          boundaryChartSelectedBox I (x1 x q) (x2 x q) ω (c x q) (d x q)) :
    (Finset.sum active fun x =>
        Finset.sum (pieces x) fun q =>
          projectLocalBoundaryIntegral I (x0 x q) (x1 x q) ω (a x q) (b x q)) =
      Finset.sum active fun x =>
        Finset.sum (pieces x) fun q =>
          projectLocalBoundaryIntegral I (x1 x q) (x2 x q) ω (c x q) (d x q) := by
  exact chartChangeCancellation_sum_eq_of_forall_eq active pieces
    (fun x q =>
      projectLocalBoundaryIntegral I (x0 x q) (x1 x q) ω (a x q) (b x q))
    (fun x q =>
      projectLocalBoundaryIntegral I (x1 x q) (x2 x q) ω (c x q) (d x q))
    (fun x hx q hq =>
      projectLocalBoundaryIntegral_chartChange_selected
        (x0 x q) (x1 x q) (x2 x q) ω
        (a x q) (b x q) (c x q) (d x q)
        (hchange x hx q hq) (hboxTarget x hx q hq))

/--
Finite-sum project-local chart-change equality from extended-target local
change-of-variables data on every active piece.
-/
theorem projectLocalBoundarySum_chartChange_extended
    {Chart : Type c} {Piece : Type p}
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (active : Finset Chart) (pieces : Chart → Finset Piece)
    (x0 x1 x2 : Chart → Piece → M) (ω : ManifoldForm I M n)
    (a b c d : Chart → Piece → Fin (n + 1) → Real)
    (hchange :
      ∀ x, x ∈ active →
        ∀ q, q ∈ pieces x →
          boundaryChartOrientedChangeOfVariables I (x0 x q) (x1 x q) ω
            (a x q) (b x q) (c x q) (d x q))
    (hboxTarget :
      ∀ x, x ∈ active →
        ∀ q, q ∈ pieces x →
          boundaryChartExtendedBox I (x1 x q) (x2 x q) ω (c x q) (d x q)) :
    (Finset.sum active fun x =>
        Finset.sum (pieces x) fun q =>
          projectLocalBoundaryIntegral I (x0 x q) (x1 x q) ω (a x q) (b x q)) =
      Finset.sum active fun x =>
        Finset.sum (pieces x) fun q =>
          projectLocalBoundaryIntegral I (x1 x q) (x2 x q) ω (c x q) (d x q) := by
  exact chartChangeCancellation_sum_eq_of_forall_eq active pieces
    (fun x q =>
      projectLocalBoundaryIntegral I (x0 x q) (x1 x q) ω (a x q) (b x q))
    (fun x q =>
      projectLocalBoundaryIntegral I (x1 x q) (x2 x q) ω (c x q) (d x q))
    (fun x hx q hq =>
      projectLocalBoundaryIntegral_chartChange_extended
        (x0 x q) (x1 x q) (x2 x q) ω
        (a x q) (b x q) (c x q) (d x q)
        (hchange x hx q hq) (hboxTarget x hx q hq))

end ProjectLocalWrappers

end Stokes

end
