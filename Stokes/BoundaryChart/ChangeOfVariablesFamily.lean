import Stokes.BoundaryChart.ChangeOfVariables

/-!
# Boundary chart change-of-variables families

This file packages Finset-indexed families of boundary chart
change-of-variables data.  It stays in the pure `BoundaryChart` layer: the
finite-sum bookkeeping is phrased directly in terms of boundary chart
integrals, without importing the global assembly packages.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u w c p v

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Finite-sum transport for a chart-indexed family of pointwise equalities.

This is the small algebraic kernel used below after the single-piece boundary
chart change-of-variables theorem has supplied the pointwise equality.
-/
theorem boundaryChartChangeOfVariables_sum_eq_of_forall_eq
    {Chart : Type c} {Piece : Type p} {R : Type v} [AddCommMonoid R]
    (active : Finset Chart) (pieces : Chart → Finset Piece)
    (sourceTerm targetTerm : Chart → Piece → R)
    (hterm :
      ∀ x, x ∈ active →
        ∀ q, q ∈ pieces x →
          sourceTerm x q = targetTerm x q) :
    (Finset.sum active fun x =>
        Finset.sum (pieces x) fun q => sourceTerm x q) =
      Finset.sum active fun x =>
        Finset.sum (pieces x) fun q => targetTerm x q := by
  refine Finset.sum_congr rfl ?_
  intro x hx
  refine Finset.sum_congr rfl ?_
  intro q hq
  exact hterm x hx q hq

/--
A Finset-indexed family of oriented boundary chart change-of-variables data.

For every active pair `(x, q)`, the source boundary chart integral
`sourceChart x q -> boundarySourceChart x q` is transported by the stored
oriented COV package to the target lower-zero face box.  The optional target
auxiliary chart is recorded with a selected box so the in-chart target term can
also be viewed as a target boundary chart integral.
-/
structure BoundaryChartChangeOfVariablesFamily {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in this family. -/
  activeCharts : Finset Chart
  /-- Finite local boundary pieces attached to each chart label. -/
  localPieces : Chart → Finset Piece
  /-- Source chart for the original boundary chart integral. -/
  sourceChart : Chart → Piece → M
  /-- Boundary chart reached from the source chart by COV. -/
  boundarySourceChart : Chart → Piece → M
  /-- Auxiliary target chart used to write the transported boundary integral. -/
  boundaryTargetChart : Chart → Piece → M
  /-- Source lower corner. -/
  sourceLowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Source upper corner. -/
  sourceUpperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Target lower corner. -/
  targetLowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Target upper corner. -/
  targetUpperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Per-piece oriented boundary chart change-of-variables package. -/
  changeOfVariables :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ localPieces x →
        boundaryChartOrientedChangeOfVariables I (sourceChart x q)
          (boundarySourceChart x q) ω
          (sourceLowerCorner x q) (sourceUpperCorner x q)
          (targetLowerCorner x q) (targetUpperCorner x q)
  /-- Selected target box used to rewrite the target in-chart term as a chart term. -/
  targetSelectedBox :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ localPieces x →
        boundaryChartSelectedBox I (boundarySourceChart x q)
          (boundaryTargetChart x q) ω
          (targetLowerCorner x q) (targetUpperCorner x q)

namespace BoundaryChartChangeOfVariablesFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- The source-side outward-first boundary chart term of a family piece. -/
def sourceBoundaryTerm
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (x : Chart) (q : Piece) : Real :=
  outwardFirstBoundaryChartIntegral I (F.sourceChart x q)
    (F.boundarySourceChart x q) ω
    (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)

/-- The COV target term written in the boundary-source chart itself. -/
def targetInChartTerm
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (x : Chart) (q : Piece) : Real :=
  outwardFirstBoundaryInChartIntegral I (F.boundarySourceChart x q) ω
    (F.targetLowerCorner x q) (F.targetUpperCorner x q)

/-- The transported target term written using the stored auxiliary target chart. -/
def targetBoundaryTerm
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (x : Chart) (q : Piece) : Real :=
  outwardFirstBoundaryChartIntegral I (F.boundarySourceChart x q)
    (F.boundaryTargetChart x q) ω
    (F.targetLowerCorner x q) (F.targetUpperCorner x q)

/-- Finite sum of source-side outward-first boundary chart terms. -/
def sourceBoundarySum
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece) : Real :=
  Finset.sum F.activeCharts fun x =>
    Finset.sum (F.localPieces x) fun q => F.sourceBoundaryTerm x q

/-- Finite sum of COV target terms written in the boundary-source chart. -/
def targetInChartSum
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece) : Real :=
  Finset.sum F.activeCharts fun x =>
    Finset.sum (F.localPieces x) fun q => F.targetInChartTerm x q

/-- Finite sum of transported target terms written using auxiliary target charts. -/
def targetBoundarySum
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece) : Real :=
  Finset.sum F.activeCharts fun x =>
    Finset.sum (F.localPieces x) fun q => F.targetBoundaryTerm x q

/--
Pointwise COV equality for every active family piece, with the target term
written in the boundary-source chart.
-/
theorem pointwise_eq_inChart [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece) :
    ∀ x, x ∈ F.activeCharts →
      ∀ q, q ∈ F.localPieces x →
        F.sourceBoundaryTerm x q = F.targetInChartTerm x q := by
  intro x hx q hq
  exact
    outwardFirstBoundaryChartIntegral_eq_inChart_of_orientedChangeOfVariables
      (F.sourceChart x q) (F.boundarySourceChart x q) ω
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x q) (F.targetUpperCorner x q)
      (F.changeOfVariables x hx q hq)

/--
Finite-sum COV equality for a family, with the target side written in the
boundary-source chart.
-/
theorem sum_eq_inChartSum [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece) :
    F.sourceBoundarySum = F.targetInChartSum := by
  exact
    boundaryChartChangeOfVariables_sum_eq_of_forall_eq F.activeCharts
      F.localPieces F.sourceBoundaryTerm F.targetInChartTerm
      F.pointwise_eq_inChart

/--
Pointwise transport of each active source boundary chart term to its stored
target boundary chart representative.
-/
theorem pointwise_eq_targetBoundary [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece) :
    ∀ x, x ∈ F.activeCharts →
      ∀ q, q ∈ F.localPieces x →
        F.sourceBoundaryTerm x q = F.targetBoundaryTerm x q := by
  intro x hx q hq
  exact
    outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables_selected
      (F.sourceChart x q) (F.boundarySourceChart x q) (F.boundaryTargetChart x q) ω
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x q) (F.targetUpperCorner x q)
      (F.changeOfVariables x hx q hq)
      (F.targetSelectedBox x hx q hq)

/--
Finite-sum transport of the source boundary chart sum to the stored target
boundary chart sum.
-/
theorem sum_eq_targetBoundarySum [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece) :
    F.sourceBoundarySum = F.targetBoundarySum := by
  exact
    boundaryChartChangeOfVariables_sum_eq_of_forall_eq F.activeCharts
      F.localPieces F.sourceBoundaryTerm F.targetBoundaryTerm
      F.pointwise_eq_targetBoundary

/--
Finite-sum transport to an externally chosen target term, once that target
agrees pointwise with the family target boundary chart representative.
-/
theorem sum_eq_of_targetBoundaryTerm_eq [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (targetTerm : Chart → Piece → Real)
    (htarget :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.localPieces x →
          F.targetBoundaryTerm x q = targetTerm x q) :
    F.sourceBoundarySum =
      Finset.sum F.activeCharts fun x =>
        Finset.sum (F.localPieces x) fun q => targetTerm x q := by
  exact
    boundaryChartChangeOfVariables_sum_eq_of_forall_eq F.activeCharts
      F.localPieces F.sourceBoundaryTerm targetTerm
      (fun x hx q hq =>
        (F.pointwise_eq_targetBoundary x hx q hq).trans
          (htarget x hx q hq))

end BoundaryChartChangeOfVariablesFamily

end ManifoldBoundary

end Stokes

end
