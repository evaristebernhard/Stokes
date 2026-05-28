import Stokes.Global.CoverIndexedZeroCompactBoxPartitionRefinement
import Stokes.Global.SupportControlledPartition

/-!
# Smooth box refinement of boundary partition pieces

This file isolates the smooth-partition step in the compact-support
represented Stokes route.  For every active boundary chart carrier, a finite
ambient open cover produces a smooth subpartition.  Multiplying the original
boundary partition coefficient by the subpartition coefficients gives the
refined coefficients used by the later box-level local Stokes assembly.

The construction is intentionally generic about the carrier and the ambient
open cover, because the carrier-selection and relative-open-lift modules are
parallel tasks.  Once those modules exist, their outputs should feed directly
into `BoundarySmoothBoxRefinement.ofFiniteOpenCover`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section SmoothBoxRefinement

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b} [DecidableEq BoundaryPiece]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/--
Smooth refinement data for the boundary part of a selected compact-support
partition.

For each boundary index `i`, `activeCarrier i` is the compact carrier on which
the original boundary coefficient must be refined.  The finite set
`boundaryPieces i` indexes smaller box neighborhoods.  The field
`subpartition i` is a mathlib smooth partition of unity on that carrier,
subordinate to the ambient open cover `ambientOpen i`.

The refined scalar coefficient itself is defined below as
`P.partition (Sum.inr i) * subpartition`.
-/
structure BoundarySmoothBoxRefinement
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (BoundaryPiece : Type b) [DecidableEq BoundaryPiece] where
  /-- Compact carrier of the boundary coefficient being refined. -/
  activeCarrier : CoverIndexedBoundaryIndex (I := I) C → Set M
  /-- Finite local box pieces attached to each boundary carrier. -/
  boundaryPieces : CoverIndexedBoundaryIndex (I := I) C → Finset BoundaryPiece
  /-- Source boundary chart for each refined box. -/
  sourceChart :
    CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → M
  /-- Lower half-space-box corner for each refined box. -/
  lower :
    CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → Fin (n + 1) → Real
  /-- Upper half-space-box corner for each refined box. -/
  upper :
    CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → Fin (n + 1) → Real
  /-- Ambient open set used to build the subpartition for a refined box. -/
  ambientOpen :
    CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → Set M
  /-- Smooth subpartition on each active boundary carrier. -/
  subpartition :
    ∀ i : CoverIndexedBoundaryIndex (I := I) C,
      SmoothPartitionOfUnity {q // q ∈ boundaryPieces i} I M
        (activeCarrier i)
  /-- The subpartition is subordinate to the assigned ambient open cover. -/
  subpartition_subordinate :
    ∀ i : CoverIndexedBoundaryIndex (I := I) C,
      (subpartition i).IsSubordinate
        (fun q : {q // q ∈ boundaryPieces i} => ambientOpen i q.1)
  /-- The subpartition sums to one on its active carrier. -/
  subpartition_sum_on_carrier :
    ∀ i x, x ∈ activeCarrier i →
      (∑ q : {q // q ∈ boundaryPieces i}, subpartition i q x) = 1
  /-- Each subpartition coefficient is supported, on the carrier, in its open set. -/
  subpartition_tsupport_inter_carrier_subset_open :
    ∀ i (q : {q // q ∈ boundaryPieces i}),
      tsupport (subpartition i q) ∩ activeCarrier i ⊆ ambientOpen i q.1
  /-- The ambient open set is already chosen inside the desired boundary chart box. -/
  ambientOpen_subset_boundaryChartBox :
    ∀ i q, q ∈ boundaryPieces i →
      ambientOpen i q ⊆
        boundaryChartBoxNeighborhood I (sourceChart i q) (lower i q) (upper i q)
  /--
  The original boundary coefficient has no topological support on `K` outside
  the active carrier.  This is the carrier bridge that makes reconstruction
  hold on all of `K`, not only on `activeCarrier i`.
  -/
  base_tsupport_inter_K_subset_carrier :
    ∀ i,
      tsupport (P.partition (Sum.inr i)) ∩ K ⊆ activeCarrier i

namespace BoundarySmoothBoxRefinement

variable
  (D : BoundarySmoothBoxRefinement
    (I := I) (K := K) C P BoundaryPiece)

/--
The refined coefficient attached to a boundary index and a box piece.

For `q ∉ D.boundaryPieces i` it is defined to be zero, so downstream code can
use the ambient `BoundaryPiece` type while finite sums still range over
`D.boundaryPieces i`.
-/
def coefficient
    (i : CoverIndexedBoundaryIndex (I := I) C) (q : BoundaryPiece) :
    M → Real :=
  fun x =>
    if hq : q ∈ D.boundaryPieces i then
      P.partition (Sum.inr i) x * D.subpartition i ⟨q, hq⟩ x
    else
      0

@[simp]
theorem coefficient_of_mem
    (i : CoverIndexedBoundaryIndex (I := I) C) {q : BoundaryPiece}
    (hq : q ∈ D.boundaryPieces i) (x : M) :
    D.coefficient i q x =
      P.partition (Sum.inr i) x * D.subpartition i ⟨q, hq⟩ x := by
  simp [coefficient, hq]

@[simp]
theorem coefficient_of_not_mem
    (i : CoverIndexedBoundaryIndex (I := I) C) {q : BoundaryPiece}
    (hq : q ∉ D.boundaryPieces i) (x : M) :
    D.coefficient i q x = 0 := by
  simp [coefficient, hq]

/-- Rewrite a finite sum over raw pieces as the corresponding subtype sum. -/
theorem sum_coefficient_eq_subtype_sum
    (i : CoverIndexedBoundaryIndex (I := I) C) (x : M) :
    (∑ q ∈ D.boundaryPieces i, D.coefficient i q x) =
      ∑ q : {q // q ∈ D.boundaryPieces i},
        P.partition (Sum.inr i) x * D.subpartition i q x := by
  classical
  rw [← Finset.sum_attach]
  simp [coefficient]

/--
The refined coefficients reconstruct the original boundary coefficient on the
global compact support set `K`.

On the active carrier this is the partition-of-unity identity.  Outside the
carrier, the original coefficient is zero because its topological support on
`K` is contained in the carrier.
-/
theorem reconstruct_on_K
    (i : CoverIndexedBoundaryIndex (I := I) C) {x : M} (hxK : x ∈ K) :
    (∑ q ∈ D.boundaryPieces i, D.coefficient i q x) =
      P.partition (Sum.inr i) x := by
  classical
  by_cases hxcarrier : x ∈ D.activeCarrier i
  · calc
      (∑ q ∈ D.boundaryPieces i, D.coefficient i q x)
          =
            ∑ q : {q // q ∈ D.boundaryPieces i},
              P.partition (Sum.inr i) x * D.subpartition i q x := by
              exact D.sum_coefficient_eq_subtype_sum i x
      _ = P.partition (Sum.inr i) x *
            (∑ q : {q // q ∈ D.boundaryPieces i},
              D.subpartition i q x) := by
              rw [Finset.mul_sum]
      _ = P.partition (Sum.inr i) x := by
              have hsum_attach :
                  (∑ q ∈ (D.boundaryPieces i).attach,
                    D.subpartition i q x) = 1 := by
                simpa using D.subpartition_sum_on_carrier i x hxcarrier
              simp [hsum_attach]
  · have hbase_zero : P.partition (Sum.inr i) x = 0 := by
      by_contra hne
      have hx_support :
          x ∈ Function.support (P.partition (Sum.inr i)) := by
        simpa [Function.mem_support] using hne
      have hx_tsupport :
          x ∈ tsupport (P.partition (Sum.inr i)) :=
        (subset_tsupport (f := P.partition (Sum.inr i))) hx_support
      exact hxcarrier
        (D.base_tsupport_inter_K_subset_carrier i ⟨hx_tsupport, hxK⟩)
    have hterms :
        ∀ q ∈ D.boundaryPieces i, D.coefficient i q x = 0 := by
      intro q hq
      simp [D.coefficient_of_mem i hq x, hbase_zero]
    have hsum_zero :
        (∑ q ∈ D.boundaryPieces i, D.coefficient i q x) = 0 := by
      exact Finset.sum_eq_zero hterms
    simpa [hbase_zero] using hsum_zero

/--
Subpartition support, transported from the ambient open cover to the boundary
chart box.
-/
theorem subpartition_tsupport_inter_carrier_subset_boundaryChartBox
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (q : {q // q ∈ D.boundaryPieces i}) :
    tsupport (D.subpartition i q) ∩ D.activeCarrier i ⊆
      boundaryChartBoxNeighborhood I (D.sourceChart i q.1)
        (D.lower i q.1) (D.upper i q.1) := by
  exact
    (D.subpartition_tsupport_inter_carrier_subset_open i q).trans
      (D.ambientOpen_subset_boundaryChartBox i q.1 q.2)

/--
The refined coefficient is supported, on `K`, inside the assigned boundary
chart box.

This is the support field expected by the next box-refined-partition
constructor.
-/
theorem coefficient_tsupport_inter_K_subset_boundaryChartBox
    (i : CoverIndexedBoundaryIndex (I := I) C) {q : BoundaryPiece}
    (hq : q ∈ D.boundaryPieces i) :
    tsupport (D.coefficient i q) ∩ K ⊆
      boundaryChartBoxNeighborhood I (D.sourceChart i q)
        (D.lower i q) (D.upper i q) := by
  intro x hx
  have hxcoeff : x ∈ tsupport (D.coefficient i q) := hx.1
  have hxK : x ∈ K := hx.2
  have hcoeff_eq :
      D.coefficient i q =
        (fun x => P.partition (Sum.inr i) x *
          D.subpartition i ⟨q, hq⟩ x) := by
    funext x
    simp [coefficient, hq]
  have hxcoeff_product :
      x ∈ tsupport
        (fun x => P.partition (Sum.inr i) x *
          D.subpartition i ⟨q, hq⟩ x) := by
    simpa [hcoeff_eq] using hxcoeff
  have hxbase :
      x ∈ tsupport (P.partition (Sum.inr i)) := by
    exact
      (tsupport_mul_subset_left
        (f := P.partition (Sum.inr i))
        (g := D.subpartition i ⟨q, hq⟩))
        hxcoeff_product
  have hxcarrier : x ∈ D.activeCarrier i :=
    D.base_tsupport_inter_K_subset_carrier i ⟨hxbase, hxK⟩
  have hxsub :
      x ∈ tsupport (D.subpartition i ⟨q, hq⟩) := by
    exact
      (tsupport_mul_subset_right
        (f := P.partition (Sum.inr i))
        (g := D.subpartition i ⟨q, hq⟩))
        hxcoeff_product
  exact
    D.subpartition_tsupport_inter_carrier_subset_boundaryChartBox i ⟨q, hq⟩
      ⟨hxsub, hxcarrier⟩

/--
Constructor from a finite ambient open cover of each active carrier.

This is the intended handoff from the relative-open-lift and carrier-selection
workers: once they provide compact carriers, finite pieces, open sets, cover
proofs, and containment of those open sets in boundary chart boxes, this
constructor supplies the smooth subpartitions and all reconstruction/support
facts.
-/
def ofFiniteOpenCover
    [FiniteDimensional Real (Fin (n + 1) → Real)]
    [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]
    (activeCarrier :
      CoverIndexedBoundaryIndex (I := I) C → Set M)
    (boundaryPieces :
      CoverIndexedBoundaryIndex (I := I) C → Finset BoundaryPiece)
    (sourceChart :
      CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → M)
    (lower upper :
      CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece →
        Fin (n + 1) → Real)
    (ambientOpen :
      CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → Set M)
    (isCompact_activeCarrier :
      ∀ i, IsCompact (activeCarrier i))
    (ambientOpen_isOpen :
      ∀ i q, q ∈ boundaryPieces i → IsOpen (ambientOpen i q))
    (activeCarrier_subset_iUnion_ambientOpen :
      ∀ i, activeCarrier i ⊆ ⋃ q ∈ boundaryPieces i, ambientOpen i q)
    (ambientOpen_subset_boundaryChartBox :
      ∀ i q, q ∈ boundaryPieces i →
        ambientOpen i q ⊆
          boundaryChartBoxNeighborhood I (sourceChart i q) (lower i q) (upper i q))
    (base_tsupport_inter_K_subset_carrier :
      ∀ i,
        tsupport (P.partition (Sum.inr i)) ∩ K ⊆ activeCarrier i) :
    BoundarySmoothBoxRefinement (I := I) (K := K) C P BoundaryPiece := by
  classical
  let partExists :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C,
        ∃ ρ : SmoothPartitionOfUnity {q // q ∈ boundaryPieces i} I M
            (activeCarrier i),
          ρ.IsSubordinate
              (fun q : {q // q ∈ boundaryPieces i} => ambientOpen i q.1) ∧
            (∀ x ∈ activeCarrier i,
              (∑ q : {q // q ∈ boundaryPieces i}, ρ q x) = 1) ∧
              (∀ q : {q // q ∈ boundaryPieces i},
                tsupport (ρ q) ∩ activeCarrier i ⊆ ambientOpen i q.1) :=
    fun i =>
      exists_supportControlledSmoothPartition_finset_sum
        (I := I) (s := boundaryPieces i) (K := activeCarrier i)
        (hK := isCompact_activeCarrier i) (U := ambientOpen i)
        (hUopen := ambientOpen_isOpen i)
        (hcover := activeCarrier_subset_iUnion_ambientOpen i)
  refine
    { activeCarrier := activeCarrier
      boundaryPieces := boundaryPieces
      sourceChart := sourceChart
      lower := lower
      upper := upper
      ambientOpen := ambientOpen
      subpartition := fun i => Classical.choose (partExists i)
      subpartition_subordinate := ?_
      subpartition_sum_on_carrier := ?_
      subpartition_tsupport_inter_carrier_subset_open := ?_
      ambientOpen_subset_boundaryChartBox := ambientOpen_subset_boundaryChartBox
      base_tsupport_inter_K_subset_carrier :=
        base_tsupport_inter_K_subset_carrier }
  · intro i
    exact (Classical.choose_spec (partExists i)).1
  · intro i x hx
    exact (Classical.choose_spec (partExists i)).2.1 x hx
  · intro i q
    exact (Classical.choose_spec (partExists i)).2.2 q

end BoundarySmoothBoxRefinement

end SmoothBoxRefinement

end Stokes

end
