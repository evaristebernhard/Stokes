import Stokes.BoundaryChart.LocalStokes

/-!
# Real half-space model wrappers

This file was split out of Stokes.HalfSpace as part of the M6.0
module-structure pass.  The theorem statements and proofs are intended to
remain identical to the monolithic version.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

theorem range_realHalfSpaceModel (n : Nat) [NeZero n] :
    range (𝓡∂ n) = {y : EuclideanSpace Real (Fin n) | 0 ≤ y 0} :=
  range_modelWithCornersEuclideanHalfSpace n

theorem frontier_realHalfSpaceModel (n : Nat) [NeZero n] :
    frontier (range (𝓡∂ n)) = {y : EuclideanSpace Real (Fin n) | 0 = y 0} :=
  frontier_range_modelWithCornersEuclideanHalfSpace n

end Stokes

end
