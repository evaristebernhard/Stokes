import Stokes.Global.CoverIndexedZeroCompactRefinedSmoothness

/-!
# Local finite-sum Stokes for box-refined boundary pieces

This module is the Wave 2 assembly point for the refined compact-support
route.  The half-space local Stokes theorem has already been packaged in
`CoverIndexedZeroCompactRefinedSmoothness`; here we expose the stable theorem
name consumed by the reconstruction layer.

No local analytic proof is repeated here.  The theorem below is exactly the
nested finite-sum statement for the refined boundary boxes, obtained from the
refined smoothness fields and the box-neighborhood hypotheses.
-/

noncomputable section

set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section RefinedLocalStokes

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryBoxRefinedPartition

variable
  {D :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P omega BoundaryPiece}
  {U :
    CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece ->
      Set (Fin (n + 1) -> Real)}

/--
Refined local Stokes summed over all selected boundary charts and all refined
half-space boxes over each chart.

This is the canonical Wave 2 local-sum entrypoint: callers provide the grouped
smoothness fields plus an open neighborhood around every refined box, and the
theorem returns the nested finite-sum equality of local bulk and outward-first
boundary terms.
-/
theorem refinedLocalStokesSum
    [IsManifold I ⊤ M]
    (S : CoverIndexedBoundaryBoxRefinedSmoothnessFields D U)
    (hU :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i -> IsOpen (U i q))
    (hUbox :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
          Icc (D.lower i q) (D.upper i q) ⊆ U i q) :
    (Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBulkTerm i q) =
      Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBoundaryTerm i q :=
  D.boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_refinedSmoothness S hU hUbox

end CoverIndexedBoundaryBoxRefinedPartition

end RefinedLocalStokes

end Stokes

end
