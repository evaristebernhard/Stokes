import Stokes.Global.CoverIndexedZeroCompactRepresentedStokesBigTheorem
import Stokes.Global.CoverIndexedZeroCompactBoxPartitionRefinement
import Stokes.Global.BoundaryPieces
import Stokes.Global.CoverIndexedBoundaryReconstruction
import Stokes.Global.IntegralReconstruction
import Stokes.Global.LocalIntegralFiniteAdditivity

/-!
# Endpoint adapter for box-refined compact-support boundary pieces

The old compact-support endpoint is indexed by one boundary center and one
box.  The refined route has a finite family of boxes over each boundary center,
so its natural index is a flattened sigma family.

This module provides only the bookkeeping bridge:

* a logical flattened refined boundary-piece type;
* the corresponding finite sigma index set;
* finite-sum reindexing lemmas between nested boundary sums and flattened
  sums; and
* an adapter from refined local terms to the existing represented bulk and
  boundary reconstruction packages.

It deliberately does not assert that the old one-box `BigInput` is sufficient
for the refined route.  Later reconstruction modules should use the adapter
fields below, or the generated `PartitionReconstructionData`, after the refined
partition and local Stokes fields have been constructed.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section RefinedEndpointAdapter

universe uH uM uP uR

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type uP}
variable {R : Type uR}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/--
Logical flattened refined boundary-piece type.

An element is a selected boundary cover index together with one of the finite
refined boxes assigned to that index.
-/
abbrev CoverIndexedRefinedBoundaryPiece
    (D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P omega BoundaryPiece) :
    Type (max uM uP) :=
  Sigma fun i : CoverIndexedBoundaryIndex (I := I) C =>
    {q : BoundaryPiece // q ∈ D.boundaryPieces i}

namespace CoverIndexedRefinedBoundaryPiece

variable
    {D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P omega BoundaryPiece}

/-- Owner boundary-center index of a flattened refined piece. -/
def owner (r : CoverIndexedRefinedBoundaryPiece (I := I) (K := K) D) :
    CoverIndexedBoundaryIndex (I := I) C :=
  r.1

/-- Underlying refined box label of a flattened refined piece. -/
def piece (r : CoverIndexedRefinedBoundaryPiece (I := I) (K := K) D) :
    BoundaryPiece :=
  r.2.1

/-- Membership certificate for the underlying refined box label. -/
theorem piece_mem (r : CoverIndexedRefinedBoundaryPiece (I := I) (K := K) D) :
    piece r ∈ D.boundaryPieces (owner r) :=
  r.2.2

/-- Forget the membership proof and view a logical refined piece as a sigma
index used by `Finset.sigma`. -/
def toSigma (r : CoverIndexedRefinedBoundaryPiece (I := I) (K := K) D) :
    Sigma fun _ : CoverIndexedBoundaryIndex (I := I) C => BoundaryPiece :=
  Sigma.mk (owner r) (piece r)

@[simp]
theorem owner_mk
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (q : {q : BoundaryPiece // q ∈ D.boundaryPieces i}) :
    owner (D := D) (Sigma.mk i q) = i :=
  rfl

@[simp]
theorem piece_mk
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (q : {q : BoundaryPiece // q ∈ D.boundaryPieces i}) :
    piece (D := D) (Sigma.mk i q) = q.1 :=
  rfl

@[simp]
theorem toSigma_mk
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (q : {q : BoundaryPiece // q ∈ D.boundaryPieces i}) :
    toSigma (D := D) (Sigma.mk i q) = Sigma.mk i q.1 :=
  rfl

end CoverIndexedRefinedBoundaryPiece

namespace CoverIndexedBoundaryBoxRefinedPartition

variable
    (D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P omega BoundaryPiece)

/--
Finite flattened sigma index set of all refined boundary boxes.

This is the finitary version of `CoverIndexedRefinedBoundaryPiece`; it is the
right shape for finite sums and reindexing.
-/
def refinedBoundaryIndexSet :
    Finset (Sigma fun _ : CoverIndexedBoundaryIndex (I := I) C => BoundaryPiece) :=
  (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)).sigma
    D.boundaryPieces

@[simp]
theorem mem_refinedBoundaryIndexSet
    {iq : Sigma fun _ : CoverIndexedBoundaryIndex (I := I) C => BoundaryPiece} :
    iq ∈ D.refinedBoundaryIndexSet (I := I) (K := K) ↔
      iq.1 ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ∧
        iq.2 ∈ D.boundaryPieces iq.1 := by
  simp [refinedBoundaryIndexSet]

/-- Convert a sigma index together with membership in the flattened finite set
to the logical flattened refined-piece type. -/
def refinedBoundaryPieceOfSigmaMem
    (iq : Sigma fun _ : CoverIndexedBoundaryIndex (I := I) C => BoundaryPiece)
    (hiq : iq ∈ D.refinedBoundaryIndexSet (I := I) (K := K)) :
    CoverIndexedRefinedBoundaryPiece (I := I) (K := K) D :=
  Sigma.mk iq.1
    ⟨iq.2, (D.mem_refinedBoundaryIndexSet (I := I) (K := K)).1 hiq |>.2⟩

@[simp]
theorem refinedBoundaryPieceOfSigmaMem_owner
    (iq : Sigma fun _ : CoverIndexedBoundaryIndex (I := I) C => BoundaryPiece)
    (hiq : iq ∈ D.refinedBoundaryIndexSet (I := I) (K := K)) :
    CoverIndexedRefinedBoundaryPiece.owner
        (D.refinedBoundaryPieceOfSigmaMem (I := I) (K := K) iq hiq) =
      iq.1 :=
  rfl

@[simp]
theorem refinedBoundaryPieceOfSigmaMem_piece
    (iq : Sigma fun _ : CoverIndexedBoundaryIndex (I := I) C => BoundaryPiece)
    (hiq : iq ∈ D.refinedBoundaryIndexSet (I := I) (K := K)) :
    CoverIndexedRefinedBoundaryPiece.piece
        (D.refinedBoundaryPieceOfSigmaMem (I := I) (K := K) iq hiq) =
      iq.2 :=
  rfl

/-- Nested refined boundary sum over boundary indices and their finite box
families. -/
def refinedBoundaryNestedSum [AddCommMonoid R]
    (term : CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> R) : R :=
  Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C))
    fun i => Finset.sum (D.boundaryPieces i) fun q => term i q

/-- Flattened refined boundary sum over the sigma index set. -/
def refinedBoundaryFlatSum [AddCommMonoid R]
    (term : CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> R) : R :=
  Finset.sum (D.refinedBoundaryIndexSet (I := I) (K := K)) fun iq =>
    term iq.1 iq.2

/-- Sum over the logical flattened refined-piece type, implemented through the
finite sigma index set. -/
def refinedBoundaryPieceSum [AddCommMonoid R]
    (term : CoverIndexedRefinedBoundaryPiece (I := I) (K := K) D -> R) : R :=
  Finset.sum (D.refinedBoundaryIndexSet (I := I) (K := K)).attach fun iq =>
    term (D.refinedBoundaryPieceOfSigmaMem (I := I) (K := K) iq.1 iq.2)

/-- A nested refined boundary sum equals the sum over the flattened sigma
index set. -/
theorem refinedBoundaryNestedSum_eq_flatSum [AddCommMonoid R]
    (term : CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> R) :
    D.refinedBoundaryNestedSum (I := I) (K := K) term =
      D.refinedBoundaryFlatSum (I := I) (K := K) term := by
  simpa [refinedBoundaryNestedSum, refinedBoundaryFlatSum,
    refinedBoundaryIndexSet] using
    (Finset.sum_sigma'
      (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C))
      D.boundaryPieces term)

/-- A nested refined boundary sum equals the sum over the logical flattened
refined-piece type when the term only depends on owner and piece. -/
theorem refinedBoundaryNestedSum_eq_pieceSum [AddCommMonoid R]
    (term : CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> R) :
    D.refinedBoundaryNestedSum (I := I) (K := K) term =
      D.refinedBoundaryPieceSum (I := I) (K := K)
        (fun r => term
          (CoverIndexedRefinedBoundaryPiece.owner r)
          (CoverIndexedRefinedBoundaryPiece.piece r)) := by
  calc
    D.refinedBoundaryNestedSum (I := I) (K := K) term =
        D.refinedBoundaryFlatSum (I := I) (K := K) term :=
      D.refinedBoundaryNestedSum_eq_flatSum (I := I) (K := K) term
    _ = D.refinedBoundaryPieceSum (I := I) (K := K)
        (fun r => term
          (CoverIndexedRefinedBoundaryPiece.owner r)
          (CoverIndexedRefinedBoundaryPiece.piece r)) := by
      simpa [refinedBoundaryFlatSum, refinedBoundaryPieceSum,
        refinedBoundaryPieceOfSigmaMem] using
        (Finset.sum_attach
          (s := D.refinedBoundaryIndexSet (I := I) (K := K))
          (f := fun iq => term iq.1 iq.2)).symm

/-- Specialized flattened-sum identity for refined local bulk terms. -/
theorem refinedLocalBulkNestedSum_eq_flatSum :
    D.refinedBoundaryNestedSum (I := I) (K := K) D.localBulkTerm =
      D.refinedBoundaryFlatSum (I := I) (K := K) D.localBulkTerm :=
  D.refinedBoundaryNestedSum_eq_flatSum (I := I) (K := K) D.localBulkTerm

/-- Specialized flattened-sum identity for refined local boundary terms. -/
theorem refinedLocalBoundaryNestedSum_eq_flatSum :
    D.refinedBoundaryNestedSum (I := I) (K := K) D.localBoundaryTerm =
      D.refinedBoundaryFlatSum (I := I) (K := K) D.localBoundaryTerm :=
  D.refinedBoundaryNestedSum_eq_flatSum (I := I) (K := K) D.localBoundaryTerm

/--
Endpoint adapter for refined compact-support boundary boxes.

It records exactly the three reconstruction fields needed after local refined
Stokes has been proved:

* represented bulk integral equals the refined local bulk sum;
* local boundary representatives change/reconstruct to the chosen boundary
  partition terms; and
* represented boundary integral equals the boundary partition sum.
-/
structure RefinedEndpointAdapter where
  boundaryPartitionTerm :
    CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> Real
  representedBulkIntegral : Real
  representedBoundaryIntegral : Real
  representedBulkIntegral_eq_refinedBulkSum :
    representedBulkIntegral =
      D.refinedBoundaryNestedSum (I := I) (K := K) D.localBulkTerm
  localBoundarySum_eq_boundaryPartitionSum :
    D.refinedBoundaryNestedSum (I := I) (K := K) D.localBoundaryTerm =
      D.refinedBoundaryNestedSum (I := I) (K := K) boundaryPartitionTerm
  representedBoundaryIntegral_eq_boundaryPartitionSum :
    representedBoundaryIntegral =
      D.refinedBoundaryNestedSum (I := I) (K := K) boundaryPartitionTerm

namespace RefinedEndpointAdapter

variable
    {D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P omega BoundaryPiece}
    (A : D.RefinedEndpointAdapter (I := I) (K := K))

/-- The adapter's bulk reconstruction as generic finite-additivity data. -/
def bulkFiniteAdditivityData :
    LocalIntegralFiniteAdditivityData
      (CoverIndexedBoundaryIndex (I := I) C) BoundaryPiece where
  activeCharts := Finset.univ
  localPieces := D.boundaryPieces
  localIntegralTerm := D.localBulkTerm
  globalIntegral := A.representedBulkIntegral
  globalIntegral_eq_localSum := by
    simpa [chartPieceSum, refinedBoundaryNestedSum] using
      A.representedBulkIntegral_eq_refinedBulkSum

/-- The adapter's boundary-partition reconstruction as generic
finite-additivity data. -/
def boundaryFiniteAdditivityData :
    LocalIntegralFiniteAdditivityData
      (CoverIndexedBoundaryIndex (I := I) C) BoundaryPiece where
  activeCharts := Finset.univ
  localPieces := D.boundaryPieces
  localIntegralTerm := A.boundaryPartitionTerm
  globalIntegral := A.representedBoundaryIntegral
  globalIntegral_eq_localSum := by
    simpa [chartPieceSum, refinedBoundaryNestedSum] using
      A.representedBoundaryIntegral_eq_boundaryPartitionSum

/--
Bulk reconstruction data for the existing represented-integral API, with no
interior pieces and with the refined boundary boxes as boundary pieces.
-/
def toBulkIntegralReconstructionData :
    BulkIntegralReconstructionData I omega
      (CoverIndexedBoundaryIndex (I := I) C) Empty BoundaryPiece where
  activeCharts := Finset.univ
  interiorPieces := fun _ => (Finset.empty : Finset Empty)
  boundaryPieces := D.boundaryPieces
  interiorBulkTerm := fun _ q => (Empty.elim q : Real)
  boundaryBulkTerm := D.localBulkTerm
  globalBulkIntegral := A.representedBulkIntegral
  globalBulkIntegral_eq_localBulkSum := by
    let boundarySum :=
      Finset.sum
        (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C))
        (fun i => Finset.sum (D.boundaryPieces i) fun q =>
          D.localBulkTerm i q)
    let emptyInteriorSum :=
      Finset.sum
        (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C))
        (fun _ => Finset.sum (Finset.empty : Finset Empty) fun q =>
          (Empty.elim q : Real))
    have hzero : emptyInteriorSum = (0 : Real) := by
      dsimp [emptyInteriorSum]
      apply Finset.sum_eq_zero
      intro _ _
      exact Finset.sum_empty
    calc
      A.representedBulkIntegral =
          boundarySum := by
        simpa [refinedBoundaryNestedSum] using
          A.representedBulkIntegral_eq_refinedBulkSum
      _ = (0 : Real) + boundarySum := by simp
      _ = emptyInteriorSum + boundarySum := by rw [hzero]

/-- Boundary fields completing the bulk reconstruction package. -/
def toBoundaryPartitionFields :
    BulkIntegralReconstructionData.BoundaryPartitionFields
      (A.toBulkIntegralReconstructionData (I := I) (K := K)) where
  boundaryPartitionTerm := A.boundaryPartitionTerm
  globalBoundaryIntegral := A.representedBoundaryIntegral
  globalBoundaryIntegral_eq_boundaryPartitionSum := by
    simpa [toBulkIntegralReconstructionData, refinedBoundaryNestedSum] using
      A.representedBoundaryIntegral_eq_boundaryPartitionSum

/-- The existing two-sided partition reconstruction package generated by the
refined endpoint adapter. -/
def toPartitionReconstructionData :
    PartitionReconstructionData I omega
      (CoverIndexedBoundaryIndex (I := I) C) Empty BoundaryPiece :=
  (A.toBulkIntegralReconstructionData (I := I) (K := K)).toPartitionReconstructionData
    (A.toBoundaryPartitionFields (I := I) (K := K))

@[simp]
theorem toPartitionReconstructionData_globalBulkIntegral :
    (A.toPartitionReconstructionData (I := I) (K := K)).globalBulkIntegral =
      A.representedBulkIntegral :=
  rfl

@[simp]
theorem toPartitionReconstructionData_globalBoundaryIntegral :
    (A.toPartitionReconstructionData (I := I) (K := K)).globalBoundaryIntegral =
      A.representedBoundaryIntegral :=
  rfl

/-- The generated partition reconstruction has the refined local bulk terms as
its boundary bulk terms. -/
@[simp]
theorem toPartitionReconstructionData_boundaryBulkTerm :
    (A.toPartitionReconstructionData (I := I) (K := K)).boundaryBulkTerm =
      D.localBulkTerm :=
  rfl

/-- The generated partition reconstruction has no interior pieces. -/
@[simp]
theorem toPartitionReconstructionData_interiorPieces :
    (A.toPartitionReconstructionData (I := I) (K := K)).interiorPieces =
      fun _ => (Finset.empty : Finset Empty) :=
  rfl

/-- Local Stokes plus the adapter reconstruction fields prove equality of the
represented refined bulk and boundary integrals. -/
theorem representedBulkIntegral_eq_representedBoundaryIntegral
    (hlocal :
      D.refinedBoundaryNestedSum (I := I) (K := K) D.localBulkTerm =
        D.refinedBoundaryNestedSum (I := I) (K := K) D.localBoundaryTerm) :
    A.representedBulkIntegral = A.representedBoundaryIntegral := by
  calc
    A.representedBulkIntegral =
        D.refinedBoundaryNestedSum (I := I) (K := K) D.localBulkTerm :=
      A.representedBulkIntegral_eq_refinedBulkSum
    _ = D.refinedBoundaryNestedSum (I := I) (K := K) D.localBoundaryTerm :=
      hlocal
    _ = D.refinedBoundaryNestedSum (I := I) (K := K) A.boundaryPartitionTerm :=
      A.localBoundarySum_eq_boundaryPartitionSum
    _ = A.representedBoundaryIntegral :=
      A.representedBoundaryIntegral_eq_boundaryPartitionSum.symm

/-- Same represented equality, consuming the local Stokes theorem in the
currently available refined-partition shape. -/
theorem representedBulkIntegral_eq_representedBoundaryIntegral_of_localSum
    (hlocal :
      (Finset.sum
          (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
          Finset.sum (D.boundaryPieces i) fun q => D.localBulkTerm i q) =
        Finset.sum
          (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
          Finset.sum (D.boundaryPieces i) fun q => D.localBoundaryTerm i q) :
    A.representedBulkIntegral = A.representedBoundaryIntegral := by
  exact
    A.representedBulkIntegral_eq_representedBoundaryIntegral
      (I := I) (K := K)
      (by simpa [refinedBoundaryNestedSum] using hlocal)

end RefinedEndpointAdapter

end CoverIndexedBoundaryBoxRefinedPartition

end RefinedEndpointAdapter

end Stokes

end
