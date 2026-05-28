import Stokes.Global.Reconstruction

/-!
# Mixed interior and boundary global Stokes constructor

This file is the final bookkeeping adapter for the mixed case: interior chart
pieces and boundary chart pieces are present at the same time.  The specialized
interior and boundary constructors are not required here.  Instead, their
outputs are represented by small abstract packages carrying only the local
Stokes equalities needed by `GlobalStokesData`.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section MixedGlobalConstructor

universe u w c i b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Abstract output of the interior-piece constructor.

Future files can instantiate this package from localized interior chart boxes.
This mixed constructor only needs the active interior pieces, the recorded bulk
and artificial-boundary terms, and the pointwise local Stokes equality.
-/
structure MixedInteriorPackage {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (Chart : Type c) (InteriorPiece : Type i)
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (interiorBulkTerm interiorBoundaryTerm : Chart → InteriorPiece → Real) where
  /-- Local Stokes on every recorded active interior piece. -/
  localStokes :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ interiorPieces x →
        interiorBulkTerm x q = interiorBoundaryTerm x q

/--
Abstract output of the boundary-piece constructor.

Future files can instantiate this package from boundary chart boxes, oriented
image data, or another boundary local theorem.  The mixed constructor only uses
the local bulk-to-boundary equality.
-/
structure MixedBoundaryPackage {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (Chart : Type c) (BoundaryPiece : Type b)
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart → Finset BoundaryPiece)
    (boundaryBulkTerm boundaryBoundaryTerm : Chart → BoundaryPiece → Real) where
  /-- Local Stokes on every recorded active boundary piece. -/
  localStokes :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x →
        boundaryBulkTerm x q = boundaryBoundaryTerm x q

/--
Mixed final-constructor data.

The `reconstruction` field records the global bulk and boundary reconstruction
equalities.  The two local packages provide local Stokes on interior and
boundary pieces.  The final two fields are the artificial-face cancellation and
chart-change compatibility needed by the final `GlobalStokesData` theorem.
-/
structure MixedGlobalStokesData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (Chart : Type c) (InteriorPiece : Type i) (BoundaryPiece : Type b) where
  /-- Bulk and boundary reconstruction package for the mixed local sums. -/
  reconstruction : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece
  /-- Artificial boundary term supplied by the interior local constructor. -/
  interiorBoundaryTerm : Chart → InteriorPiece → Real
  /-- Boundary-chart term supplied by the boundary local constructor. -/
  boundaryBoundaryTerm : Chart → BoundaryPiece → Real
  /-- Local Stokes package for the interior pieces. -/
  interiorPackage :
    MixedInteriorPackage I ω Chart InteriorPiece
      reconstruction.activeCharts reconstruction.interiorPieces
      reconstruction.interiorBulkTerm interiorBoundaryTerm
  /-- Local Stokes package for the boundary pieces. -/
  boundaryPackage :
    MixedBoundaryPackage I ω Chart BoundaryPiece
      reconstruction.activeCharts reconstruction.boundaryPieces
      reconstruction.boundaryBulkTerm boundaryBoundaryTerm
  /-- Cancellation of artificial boundary terms from interior pieces. -/
  interiorBoundaryCancellation :
    (Finset.sum reconstruction.activeCharts fun x =>
      Finset.sum (reconstruction.interiorPieces x) fun q =>
        interiorBoundaryTerm x q) = 0
  /-- Boundary chart-change compatibility with the reconstructed partition term. -/
  chartChangeCancellation :
    (Finset.sum reconstruction.activeCharts fun x =>
        Finset.sum (reconstruction.boundaryPieces x) fun q =>
          boundaryBoundaryTerm x q) =
      Finset.sum reconstruction.activeCharts fun x =>
        Finset.sum (reconstruction.boundaryPieces x) fun q =>
          reconstruction.boundaryPartitionTerm x q

namespace MixedGlobalStokesData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}

/--
Convert mixed constructor data into the final `GlobalStokesData` package.

All analytic content is already present in the component fields of `D`; this
definition only aligns those fields with the final theorem's record shape.
-/
def toGlobalStokesData
    (D : MixedGlobalStokesData I ω Chart InteriorPiece BoundaryPiece) :
    GlobalStokesData I ω Chart InteriorPiece BoundaryPiece :=
  D.reconstruction.toGlobalStokesData
    D.interiorBoundaryTerm
    D.boundaryBoundaryTerm
    D.interiorPackage.localStokes
    D.boundaryPackage.localStokes
    D.interiorBoundaryCancellation
    D.chartChangeCancellation

/-- The converted package has the same recorded global bulk integral. -/
@[simp]
theorem toGlobalStokesData_globalBulkIntegral
    (D : MixedGlobalStokesData I ω Chart InteriorPiece BoundaryPiece) :
    D.toGlobalStokesData.globalBulkIntegral = D.reconstruction.globalBulkIntegral :=
  rfl

/-- The converted package has the same recorded global boundary integral. -/
@[simp]
theorem toGlobalStokesData_globalBoundaryIntegral
    (D : MixedGlobalStokesData I ω Chart InteriorPiece BoundaryPiece) :
    D.toGlobalStokesData.globalBoundaryIntegral =
      D.reconstruction.globalBoundaryIntegral :=
  rfl

/-- Mixed constructor theorem, obtained by converting to `GlobalStokesData`. -/
theorem stokes
    (D : MixedGlobalStokesData I ω Chart InteriorPiece BoundaryPiece) :
    D.reconstruction.globalBulkIntegral =
      D.reconstruction.globalBoundaryIntegral :=
  globalStokes D.toGlobalStokesData

end MixedGlobalStokesData

/-- Blueprint-facing final theorem for mixed interior and boundary packages. -/
theorem mixedGlobalStokes
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}
    (D : MixedGlobalStokesData I ω Chart InteriorPiece BoundaryPiece) :
    D.reconstruction.globalBulkIntegral =
      D.reconstruction.globalBoundaryIntegral :=
  D.stokes

end MixedGlobalConstructor

end Stokes

end
