import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Stokes.Global.CoverIndexedZeroCompactBoxPartitionRefinement
import Stokes.Global.CoverIndexedZeroCompactFiniteHalfSpaceCover

/-!
# Refined boundary partitions from finite half-space covers

This file is the support-bridge constructor used after a boundary chart piece
has been refined by a finite family of half-space boxes.  The input side keeps
the natural dependent piece type `Piece i` for each boundary chart.  The output
side flattens those labels to `Σ i, Piece i`, which is the uniform piece type
expected by `CoverIndexedBoundaryBoxRefinedPartition`.

The constructor deliberately delegates the actual support proof to
`CoverIndexedBoundaryBoxRefinedPartition.ofManifoldSupportControl`; it only
performs the finite-cover projections and sigma-index bookkeeping.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section RefinedPartitionConstructor

universe u w p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/-- Flattened labels for a boundary refinement with dependent per-chart pieces. -/
abbrev SigmaBoundaryPiece
    (C : CompactSupportChartCoverSelection I K)
    (Piece : CoverIndexedBoundaryIndex (I := I) C → Type p) : Type (max w p) :=
  Sigma Piece

namespace CoverIndexedFiniteHalfSpaceBoxCover

variable
  {coordCarrier ambient :
    CoverIndexedBoundaryIndex (I := I) C → Set (Fin (n + 1) → Real)}
  {Piece : CoverIndexedBoundaryIndex (I := I) C → Type p}

/-- The flattened finite set of active refined boxes over one boundary chart. -/
def sigmaBoundaryPieces
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    Finset (SigmaBoundaryPiece (I := I) (K := K) C Piece) :=
  ({i} : Finset (CoverIndexedBoundaryIndex (I := I) C)).sigma
    (fun j => D.activePieces j)

@[simp]
theorem mem_sigmaBoundaryPieces
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    {i : CoverIndexedBoundaryIndex (I := I) C}
    {q : SigmaBoundaryPiece (I := I) (K := K) C Piece} :
    q ∈ D.sigmaBoundaryPieces i ↔
      q.1 = i ∧ q.2 ∈ D.activePieces q.1 := by
  simp [sigmaBoundaryPieces]

/-- The active-piece projection of a flattened member. -/
theorem sigmaBoundaryPieces_active
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    {i : CoverIndexedBoundaryIndex (I := I) C}
    {q : SigmaBoundaryPiece (I := I) (K := K) C Piece}
    (hq : q ∈ D.sigmaBoundaryPieces i) :
    q.2 ∈ D.activePieces q.1 :=
  (D.mem_sigmaBoundaryPieces.mp hq).2

/-- A finite-cover closed box lies in its ambient set, in flattened notation. -/
theorem Icc_subset_ambient_of_sigmaBoundaryPieces
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    {i : CoverIndexedBoundaryIndex (I := I) C}
    {q : SigmaBoundaryPiece (I := I) (K := K) C Piece}
    (hq : q ∈ D.sigmaBoundaryPieces i) :
    Icc (D.lowerCorner q.1 q.2) (D.upperCorner q.1 q.2) ⊆
      ambient q.1 :=
  D.Icc_subset_ambient q.1 (D.sigmaBoundaryPieces_active hq)

/-- A finite-cover support box lies in its ambient set, in flattened notation. -/
theorem sourceBox_subset_ambient_of_sigmaBoundaryPieces
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    {i : CoverIndexedBoundaryIndex (I := I) C}
    {q : SigmaBoundaryPiece (I := I) (K := K) C Piece}
    (hq : q ∈ D.sigmaBoundaryPieces i) :
    halfSpaceSupportBox (D.lowerCorner q.1 q.2) (D.upperCorner q.1 q.2) ⊆
      ambient q.1 :=
  D.sourceBox_subset_ambient q.1 (D.sigmaBoundaryPieces_active hq)

end CoverIndexedFiniteHalfSpaceBoxCover

namespace CoverIndexedBoundaryBoxRefinedPartition

variable
  {coordCarrier ambient :
    CoverIndexedBoundaryIndex (I := I) C → Set (Fin (n + 1) → Real)}
  {Piece : CoverIndexedBoundaryIndex (I := I) C → Type p}

/--
Construct a genuine box-refined boundary partition from a finite half-space
cover and refined coefficient/support data.

The input pieces may depend on the boundary chart index.  The output uses the
flattened piece type `Σ i, Piece i`; all local geometric fields are evaluated
at the index stored in that sigma label.  This keeps downstream APIs uniform
without losing the per-chart finite-cover structure.
-/
def ofFiniteHalfSpaceCover
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (sourceChart targetChart :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C, Piece i → M)
    (coefficient :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C, Piece i → M → Real)
    (reconstruct_on_K :
      ∀ i x, x ∈ K →
        (∑ q ∈ D.activePieces i, coefficient i q x) =
          P.partition (Sum.inr i) x)
    (base_tsupport_subset_coordCarrier :
      ∀ i q, q ∈ D.activePieces i →
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (sourceChart i q) (targetChart i q) ω) ⊆
          coordCarrier i)
    (coordCarrier_subset_upperHalfSpace :
      ∀ i, coordCarrier i ⊆ upperHalfSpace n)
    (isCompact_coordCarrier :
      ∀ i, IsCompact (coordCarrier i))
    (Icc_subset_boundaryChartDomain :
      ∀ i q, q ∈ D.activePieces i →
        Icc (D.lowerCorner i q) (D.upperCorner i q) ⊆
          boundaryChartDomain I (sourceChart i q) (targetChart i q))
    (coordCarrier_mapsTo_K :
      ∀ i q, q ∈ D.activePieces i →
        ∀ y ∈ coordCarrier i, (extChartAt I (sourceChart i q)).symm y ∈ K)
    (coordCarrier_subset_sourceTarget :
      ∀ i q, q ∈ D.activePieces i →
        coordCarrier i ⊆ (extChartAt I (sourceChart i q)).target)
    (coordCarrier_subset_overlap :
      ∀ i q, q ∈ D.activePieces i →
        coordCarrier i ⊆
          ManifoldForm.chartOverlap I (sourceChart i q) (targetChart i q))
    (coefficient_tsupport_inter_K_subset_sourceBox :
      ∀ i q, q ∈ D.activePieces i →
        tsupport (coefficient i q) ∩ K ⊆
          boundaryChartBoxNeighborhood I (sourceChart i q)
            (D.lowerCorner i q) (D.upperCorner i q)) :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P ω
      (SigmaBoundaryPiece (I := I) (K := K) C Piece) :=
  CoverIndexedBoundaryBoxRefinedPartition.ofManifoldSupportControl
    (I := I) (K := K) (ω := ω) (C := C) (P := P)
    (BoundaryPiece := SigmaBoundaryPiece (I := I) (K := K) C Piece)
    (boundaryPieces := D.sigmaBoundaryPieces)
    (sourceChart := fun _ q => sourceChart q.1 q.2)
    (targetChart := fun _ q => targetChart q.1 q.2)
    (coefficient := fun _ q => coefficient q.1 q.2)
    (coordSupport := fun _ q => coordCarrier q.1)
    (lower := fun _ q => D.lowerCorner q.1 q.2)
    (upper := fun _ q => D.upperCorner q.1 q.2)
    (reconstruct_on_K := by
      intro i x hxK
      calc
        Finset.sum (D.sigmaBoundaryPieces i)
            (fun q => coefficient q.1 q.2 x)
            =
            Finset.sum
              ({i} : Finset (CoverIndexedBoundaryIndex (I := I) C))
              (fun j =>
                Finset.sum (D.activePieces j)
                  (fun q => coefficient j q x)) := by
              simpa [CoverIndexedFiniteHalfSpaceBoxCover.sigmaBoundaryPieces]
                using
                  (Finset.sum_sigma'
                    ({i} : Finset (CoverIndexedBoundaryIndex (I := I) C))
                    (fun j => D.activePieces j)
                    (fun j q => coefficient j q x)).symm
        _ = Finset.sum (D.activePieces i) (fun q => coefficient i q x) := by
              simp
        _ = P.partition (Sum.inr i) x :=
              reconstruct_on_K i x hxK)
    (base_tsupport_subset_coordSupport := by
      intro i q hq
      exact
        base_tsupport_subset_coordCarrier q.1 q.2
          (D.sigmaBoundaryPieces_active hq))
    (coordSupport_subset_upperHalfSpace := by
      intro i q hq
      exact coordCarrier_subset_upperHalfSpace q.1)
    (isCompact_coordSupport := by
      intro i q hq
      exact isCompact_coordCarrier q.1)
    (lower_zero := by
      intro i q hq
      exact
        (D.cover q.1).lowerCorner_zero q.2
          (by
            simpa [CoverIndexedFiniteHalfSpaceBoxCover.activePieces] using
              D.sigmaBoundaryPieces_active hq))
    (lower_le_upper := by
      intro i q hq
      exact
        (D.cover q.1).lower_le_upper q.2
          (by
            simpa [CoverIndexedFiniteHalfSpaceBoxCover.activePieces] using
              D.sigmaBoundaryPieces_active hq))
    (Icc_subset_boundaryChartDomain := by
      intro i q hq
      exact
        Icc_subset_boundaryChartDomain q.1 q.2
          (D.sigmaBoundaryPieces_active hq))
    (coordSupport_mapsTo_K := by
      intro i q hq
      exact
        coordCarrier_mapsTo_K q.1 q.2
          (D.sigmaBoundaryPieces_active hq))
    (coordSupport_subset_sourceTarget := by
      intro i q hq
      exact
        coordCarrier_subset_sourceTarget q.1 q.2
          (D.sigmaBoundaryPieces_active hq))
    (coordSupport_subset_overlap := by
      intro i q hq
      exact
        coordCarrier_subset_overlap q.1 q.2
          (D.sigmaBoundaryPieces_active hq))
    (coefficient_tsupport_inter_K_subset_sourceBox := by
      intro i q hq
      exact
        coefficient_tsupport_inter_K_subset_sourceBox q.1 q.2
          (D.sigmaBoundaryPieces_active hq))

/--
Variant deriving the boundary-domain containment from the finite-cover ambient
field plus an ambient-to-domain inclusion.  This is often the form produced by
collar and image-control shrink data.
-/
def ofFiniteHalfSpaceCoverOfAmbientDomain
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (sourceChart targetChart :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C, Piece i → M)
    (coefficient :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C, Piece i → M → Real)
    (reconstruct_on_K :
      ∀ i x, x ∈ K →
        (∑ q ∈ D.activePieces i, coefficient i q x) =
          P.partition (Sum.inr i) x)
    (base_tsupport_subset_coordCarrier :
      ∀ i q, q ∈ D.activePieces i →
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (sourceChart i q) (targetChart i q) ω) ⊆
          coordCarrier i)
    (coordCarrier_subset_upperHalfSpace :
      ∀ i, coordCarrier i ⊆ upperHalfSpace n)
    (isCompact_coordCarrier :
      ∀ i, IsCompact (coordCarrier i))
    (ambient_subset_boundaryChartDomain :
      ∀ i q, q ∈ D.activePieces i →
        ambient i ⊆ boundaryChartDomain I (sourceChart i q) (targetChart i q))
    (coordCarrier_mapsTo_K :
      ∀ i q, q ∈ D.activePieces i →
        ∀ y ∈ coordCarrier i, (extChartAt I (sourceChart i q)).symm y ∈ K)
    (coordCarrier_subset_sourceTarget :
      ∀ i q, q ∈ D.activePieces i →
        coordCarrier i ⊆ (extChartAt I (sourceChart i q)).target)
    (coordCarrier_subset_overlap :
      ∀ i q, q ∈ D.activePieces i →
        coordCarrier i ⊆
          ManifoldForm.chartOverlap I (sourceChart i q) (targetChart i q))
    (coefficient_tsupport_inter_K_subset_sourceBox :
      ∀ i q, q ∈ D.activePieces i →
        tsupport (coefficient i q) ∩ K ⊆
          boundaryChartBoxNeighborhood I (sourceChart i q)
            (D.lowerCorner i q) (D.upperCorner i q)) :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P ω
      (SigmaBoundaryPiece (I := I) (K := K) C Piece) :=
  ofFiniteHalfSpaceCover
    (I := I) (K := K) (ω := ω) (C := C) (P := P) D
    sourceChart targetChart coefficient reconstruct_on_K
    base_tsupport_subset_coordCarrier
    coordCarrier_subset_upperHalfSpace
    isCompact_coordCarrier
    (fun i q hq =>
      (D.Icc_subset_ambient i hq).trans
        (ambient_subset_boundaryChartDomain i q hq))
    coordCarrier_mapsTo_K
    coordCarrier_subset_sourceTarget
    coordCarrier_subset_overlap
    coefficient_tsupport_inter_K_subset_sourceBox

end CoverIndexedBoundaryBoxRefinedPartition

end RefinedPartitionConstructor

end Stokes

end
