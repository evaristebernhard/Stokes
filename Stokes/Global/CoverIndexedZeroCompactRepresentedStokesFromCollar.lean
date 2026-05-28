import Stokes.Global.CoverIndexedZeroCompactCollarBoxSelection
import Stokes.Global.CoverIndexedZeroCompactSmoothBoxRefinement
import Stokes.Global.CoverIndexedZeroCompactRefinedPartitionConstructor
import Stokes.Global.CoverIndexedZeroCompactRefinedImageControl
import Stokes.Global.CoverIndexedZeroCompactRefinedSmoothness
import Stokes.Global.CoverIndexedZeroCompactRefinedEndpointAdapter

/-!
# Natural compact-support represented Stokes interface from collar data

This file is the public-facing bundle for the refined compact-support route.
It does not claim that collar data alone constructs every downstream object.
Instead it collects the honest certificates currently needed by the route:

* collar-compatible coordinate carriers, from which a finite half-space cover is
  available;
* a smooth box refinement and the resulting box-refined boundary partition;
* smoothness fields for the local half-space Stokes theorem;
* ambient image-control data for the whole refined half-space boxes; and
* endpoint reconstruction data from refined local terms to represented
  bulk/boundary integrals.

The theorem at the bottom is the compact-support represented Stokes endpoint
available from these data.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section FromCollar

universe uH uM uB uι

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type uB} [DecidableEq BoundaryPiece]
variable {ImageIndex : Type uι} [Fintype ImageIndex]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/--
Natural input package for the compact-support represented Stokes theorem
generated from collar-compatible boundary data.

The package still exposes the honest refined-partition and reconstruction
certificates.  The collar fields guarantee that the finite half-space cover can
be selected, while the later fields record the smooth refined partition,
ambient image control, local Stokes smoothness, and endpoint reconstruction
needed by the represented theorem.
-/
structure CoverIndexedZeroCompactRepresentedStokesFromCollarInput where
  /-- Coordinate carrier for each boundary chart index. -/
  coordCarrier :
    CoverIndexedBoundaryIndex (I := I) C → Set (Fin (n + 1) → Real)
  /-- Ambient collar/preimage region in the same boundary coordinates. -/
  ambient :
    CoverIndexedBoundaryIndex (I := I) C → Set (Fin (n + 1) → Real)
  /-- Compactness of each coordinate carrier. -/
  coordCarrier_isCompact :
    ∀ i : CoverIndexedBoundaryIndex (I := I) C, IsCompact (coordCarrier i)
  /-- The coordinate carriers lie in the closed upper half-space. -/
  coordCarrier_subset_upperHalfSpace :
    ∀ i : CoverIndexedBoundaryIndex (I := I) C,
      coordCarrier i ⊆ upperHalfSpace n
  /--
  Collar/prism containment around every carrier point.  This is the genuine
  geometric input that produces half-space boxes with lower normal corner zero.
  -/
  collar_prisms :
    ∀ i : CoverIndexedBoundaryIndex (I := I) C,
      ∀ x ∈ coordCarrier i, ∃ eps : Real,
        0 < eps ∧ halfSpaceCollarPrism (n := n) x eps ⊆ ambient i
  /-- Smooth refinement of the original boundary partition into box pieces. -/
  smoothRefinement :
    BoundarySmoothBoxRefinement (I := I) (K := K) C P BoundaryPiece
  /-- The actual box-refined boundary partition consumed by local Stokes. -/
  refinedPartition :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P ω BoundaryPiece
  /-- Smoothness neighborhood assigned to each refined boundary box. -/
  smoothnessNeighborhood :
    CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece →
      Set (Fin (n + 1) → Real)
  /-- Smoothness fields for refined coefficients and transition-pullback forms. -/
  smoothnessFields :
    CoverIndexedBoundaryBoxRefinedSmoothnessFields
      (I := I) (K := K) refinedPartition smoothnessNeighborhood
  /-- The smoothness neighborhoods are open. -/
  smoothnessNeighborhood_isOpen :
    ∀ i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
      ∀ q, q ∈ refinedPartition.boundaryPieces i →
        IsOpen (smoothnessNeighborhood i q)
  /-- Each refined closed source box lies in its smoothness neighborhood. -/
  sourceIcc_subset_smoothnessNeighborhood :
    ∀ i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
      ∀ q, q ∈ refinedPartition.boundaryPieces i →
        Icc (refinedPartition.lower i q) (refinedPartition.upper i q) ⊆
          smoothnessNeighborhood i q
  /-- Finite family used to state ambient image control for refined boxes. -/
  imageControlFamily :
    CoverIndexedRefinedBoxImageControlFamily
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      refinedPartition ImageIndex
  /--
  Whole-box ambient chart-transition control.  This is intentionally retained
  as an honest field: tangential boundary-face control is not enough here.
  -/
  imageControl_mapsTo :
    imageControlFamily.ChartTransitionMapsToField (I := I) (K := K) (C := C)
  /-- Reconstruction from refined local terms to represented bulk/boundary integrals. -/
  endpointAdapter :
    refinedPartition.RefinedEndpointAdapter (I := I) (K := K)

namespace CoverIndexedZeroCompactRepresentedStokesFromCollarInput

variable
    (X :
      CoverIndexedZeroCompactRepresentedStokesFromCollarInput
        (I := I) (K := K) (ω := ω) (C := C) (P := P)
        (BoundaryPiece := BoundaryPiece) (ImageIndex := ImageIndex))

/-- The finite half-space box cover supplied by the collar fields of the input. -/
def finiteHalfSpaceCover :
    CoverIndexedFiniteHalfSpaceBoxCover
      (I := I) (K := K) C X.coordCarrier X.ambient
      (fun _ : CoverIndexedBoundaryIndex (I := I) C => Fin (n + 1) → Real) :=
  coverIndexedFiniteHalfSpaceBoxCoverOfCollar
    (I := I) (K := K) (C := C)
    X.coordCarrier X.ambient
    X.coordCarrier_isCompact
    X.coordCarrier_subset_upperHalfSpace
    X.collar_prisms

/-- Active centers selected by the collar finite cover remain in their carriers. -/
theorem finiteHalfSpaceCover_active_subset
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    ∀ x ∈ (X.finiteHalfSpaceCover
        (I := I) (K := K) (C := C)).activePieces i,
      x ∈ X.coordCarrier i := by
  simpa [finiteHalfSpaceCover] using
    (coverIndexedFiniteHalfSpaceBoxCoverOfCollar_active_subset
      (I := I) (K := K) (C := C)
      X.coordCarrier X.ambient
      X.coordCarrier_isCompact
      X.coordCarrier_subset_upperHalfSpace
      X.collar_prisms i)

/-- Represented bulk integral stored in the endpoint adapter. -/
def representedBulkIntegral : Real :=
  X.endpointAdapter.representedBulkIntegral

/-- Represented boundary integral stored in the endpoint adapter. -/
def representedBoundaryIntegral : Real :=
  X.endpointAdapter.representedBoundaryIntegral

/-- Local refined half-space Stokes for all refined boundary boxes. -/
theorem refinedLocalStokes
    [IsManifold I ⊤ M] :
    (Finset.sum
        (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (X.refinedPartition.boundaryPieces i) fun q =>
          X.refinedPartition.localBulkTerm i q) =
      Finset.sum
        (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (X.refinedPartition.boundaryPieces i) fun q =>
          X.refinedPartition.localBoundaryTerm i q :=
  X.refinedPartition.boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_refinedSmoothness
    (I := I) (K := K)
    X.smoothnessFields
    X.smoothnessNeighborhood_isOpen
    X.sourceIcc_subset_smoothnessNeighborhood

/--
Compact-support represented Stokes theorem from collar/refined-box data.

This is still a represented theorem: it proves equality of the represented
bulk and boundary integrals recorded by the endpoint adapter, not yet a fully
manifold-native integral statement.
-/
theorem representedStokes
    [IsManifold I ⊤ M] :
    X.representedBulkIntegral (I := I) (K := K) =
      X.representedBoundaryIntegral (I := I) (K := K) := by
  dsimp [representedBulkIntegral, representedBoundaryIntegral]
  exact
    X.endpointAdapter.representedBulkIntegral_eq_representedBoundaryIntegral_of_localSum
      (I := I) (K := K)
      (X.refinedLocalStokes (I := I) (K := K))

end CoverIndexedZeroCompactRepresentedStokesFromCollarInput

end FromCollar

end Stokes

end
