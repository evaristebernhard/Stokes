import Stokes.HalfSpace.BoxInteriorSmoothness
import Stokes.Global.CoverIndexedRelativeLocalStokes

/-!
# Refined boundary local Stokes from open-interior smoothness fields

This file is the global-layer lift from the expected half-space
`HalfSpaceBoxOpenInteriorSmoothnessFields` package to the already available
refined finite-sum theorem from `HalfSpaceBoxInteriorStokesFields`.

The proof is intentionally thin: every refined box is converted to interior
fields, and the existing `boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_interiorFields`
entry point does the finite-sum assembly.
-/

noncomputable section

set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section RefinedOpenInteriorLocalStokes

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
  (D :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P omega BoundaryPiece)

/-- Convert per-refined-box open-interior smoothness packages into the exact
interior fields consumed by the boundary-compatible local Stokes theorem. -/
def interiorFields_of_openInteriorSmoothness
    (hfields :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
          HalfSpaceBoxOpenInteriorSmoothnessFields
            (ManifoldForm.transitionPullbackInChart I
              (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
            (D.lower i q) (D.upper i q)) :
    forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
      forall q, q ∈ D.boundaryPieces i ->
        HalfSpaceBoxInteriorStokesFields
          (ManifoldForm.transitionPullbackInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
          (D.lower i q) (D.upper i q) := by
  intro i hi q hq
  exact HalfSpaceBoxInteriorStokesFields.ofOpenInteriorSmoothness (hfields i hi q hq)

/-- Refined boundary half-space Stokes from per-box open-interior smoothness
fields. -/
theorem boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_openInteriorSmoothness
    (hfields :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
          HalfSpaceBoxOpenInteriorSmoothnessFields
            (ManifoldForm.transitionPullbackInChart I
              (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
            (D.lower i q) (D.upper i q)) :
    (Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBulkTerm i q) =
      Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBoundaryTerm i q := by
  classical
  exact
    D.boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_interiorFields
      (D.interiorFields_of_openInteriorSmoothness hfields)

end CoverIndexedBoundaryBoxRefinedPartition

end RefinedOpenInteriorLocalStokes

end Stokes

end
