import Stokes.Global.CoverIndexedZeroCompactSmoothBoxRefinement
import Stokes.Global.CoverIndexedZeroCompactRefinedPartitionConstructor

/-!
# Refined boundary partitions from smooth collar refinements

This file ties together the two constructor layers used in the compact-support
collar route:

* `BoundarySmoothBoxRefinement` provides refined scalar coefficients and proves
  reconstruction/support on the manifold compact set `K`;
* `CoverIndexedBoundaryBoxRefinedPartition.ofFiniteHalfSpaceCover` packages a
  finite half-space cover and coordinate-carrier compatibility into the
  box-refined partition consumed by local Stokes.

The constructors below perform the dependent `Piece i` to `Σ i, Piece i`
bookkeeping once, so final callers do not have to separately provide both a
smooth refinement and a hand-built refined partition.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section FromCollarPartition

universe u w p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable
  {coordCarrier ambient :
    CoverIndexedBoundaryIndex (I := I) C → Set (Fin (n + 1) → Real)}
variable {Piece : CoverIndexedBoundaryIndex (I := I) C → Type p}

namespace BoundarySmoothBoxRefinement

variable [DecidableEq (SigmaBoundaryPiece (I := I) (K := K) C Piece)]

variable
  (S :
    BoundarySmoothBoxRefinement
      (I := I) (K := K) C P
      (SigmaBoundaryPiece (I := I) (K := K) C Piece))
  (F :
    CoverIndexedFiniteHalfSpaceBoxCover
      (I := I) (K := K) C coordCarrier ambient Piece)

/--
The smooth-refinement reconstruction identity, rewritten over the dependent
finite half-space labels of one boundary chart.
-/
theorem reconstruct_on_K_of_sigmaBoundaryPieces
    (boundaryPieces_eq :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C,
        S.boundaryPieces i = F.sigmaBoundaryPieces i)
    (i : CoverIndexedBoundaryIndex (I := I) C) {x : M} (hxK : x ∈ K) :
    (∑ q ∈ F.activePieces i, S.coefficient i ⟨i, q⟩ x) =
      P.partition (Sum.inr i) x := by
  classical
  have hsigma_sum :
      Finset.sum (F.sigmaBoundaryPieces i) (fun q => S.coefficient i q x) =
        Finset.sum (F.activePieces i)
          (fun q => S.coefficient i ⟨i, q⟩ x) := by
    calc
      Finset.sum (F.sigmaBoundaryPieces i) (fun q => S.coefficient i q x)
          =
          Finset.sum
            ({i} : Finset (CoverIndexedBoundaryIndex (I := I) C))
            (fun j =>
              Finset.sum (F.activePieces j)
                (fun q => S.coefficient i ⟨j, q⟩ x)) := by
            simpa [CoverIndexedFiniteHalfSpaceBoxCover.sigmaBoundaryPieces]
              using
                (Finset.sum_sigma'
                  ({i} : Finset (CoverIndexedBoundaryIndex (I := I) C))
                  (fun j => F.activePieces j)
                  (fun j q => S.coefficient i ⟨j, q⟩ x)).symm
      _ =
          Finset.sum (F.activePieces i)
            (fun q => S.coefficient i ⟨i, q⟩ x) := by
            simp
  calc
    (∑ q ∈ F.activePieces i, S.coefficient i ⟨i, q⟩ x)
        =
        Finset.sum (F.sigmaBoundaryPieces i)
          (fun q => S.coefficient i q x) := by
          exact hsigma_sum.symm
    _ = P.partition (Sum.inr i) x := by
          simpa [boundaryPieces_eq i] using
            S.reconstruct_on_K i (x := x) hxK

/--
The smooth-refinement coefficient support field, rewritten for one active
dependent finite-cover label.
-/
theorem coefficient_tsupport_inter_K_subset_finiteHalfSpaceCoverBox
    (boundaryPieces_eq :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C,
        S.boundaryPieces i = F.sigmaBoundaryPieces i)
    (lower_eq :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        S.lower i ⟨i, q⟩ = F.lowerCorner i q)
    (upper_eq :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        S.upper i ⟨i, q⟩ = F.upperCorner i q)
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (q : Piece i) (hq : q ∈ F.activePieces i) :
    tsupport (S.coefficient i ⟨i, q⟩) ∩ K ⊆
      boundaryChartBoxNeighborhood I (S.sourceChart i ⟨i, q⟩)
        (F.lowerCorner i q) (F.upperCorner i q) := by
  classical
  have hsigma :
      (⟨i, q⟩ : SigmaBoundaryPiece (I := I) (K := K) C Piece) ∈
        S.boundaryPieces i := by
    rw [boundaryPieces_eq i]
    exact
      (F.mem_sigmaBoundaryPieces
        (i := i)
        (q := (⟨i, q⟩ :
          SigmaBoundaryPiece (I := I) (K := K) C Piece))).mpr
        ⟨rfl, hq⟩
  simpa [lower_eq i q hq, upper_eq i q hq] using
    S.coefficient_tsupport_inter_K_subset_boundaryChartBox i hsigma

/--
Construct a box-refined boundary partition from a smooth sigma-indexed
refinement and a dependent finite half-space cover.

The honest remaining hypotheses are the compatibility between the smooth
refinement and finite cover (`boundaryPieces_eq`, `lower_eq`, `upper_eq`) and
the coordinate-carrier fields needed by local Stokes.
-/
def toRefinedPartitionOfFiniteHalfSpaceCover
    (targetChart :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C, Piece i → M)
    (boundaryPieces_eq :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C,
        S.boundaryPieces i = F.sigmaBoundaryPieces i)
    (lower_eq :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        S.lower i ⟨i, q⟩ = F.lowerCorner i q)
    (upper_eq :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        S.upper i ⟨i, q⟩ = F.upperCorner i q)
    (base_tsupport_subset_coordCarrier :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (S.sourceChart i ⟨i, q⟩) (targetChart i q) ω) ⊆
          coordCarrier i)
    (coordCarrier_subset_upperHalfSpace :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C,
        coordCarrier i ⊆ upperHalfSpace n)
    (isCompact_coordCarrier :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C,
        IsCompact (coordCarrier i))
    (Icc_subset_boundaryChartDomain :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        Icc (F.lowerCorner i q) (F.upperCorner i q) ⊆
          boundaryChartDomain I (S.sourceChart i ⟨i, q⟩) (targetChart i q))
    (coordCarrier_mapsTo_K :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        ∀ y ∈ coordCarrier i,
          (extChartAt I (S.sourceChart i ⟨i, q⟩)).symm y ∈ K)
    (coordCarrier_subset_sourceTarget :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        coordCarrier i ⊆ (extChartAt I (S.sourceChart i ⟨i, q⟩)).target)
    (coordCarrier_subset_overlap :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        coordCarrier i ⊆
          ManifoldForm.chartOverlap I (S.sourceChart i ⟨i, q⟩) (targetChart i q)) :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P ω
      (SigmaBoundaryPiece (I := I) (K := K) C Piece) :=
  CoverIndexedBoundaryBoxRefinedPartition.ofFiniteHalfSpaceCover
    (I := I) (K := K) (ω := ω) (C := C) (P := P) F
    (fun i q => S.sourceChart i ⟨i, q⟩)
    targetChart
    (fun i q => S.coefficient i ⟨i, q⟩)
    (fun i x hxK =>
      S.reconstruct_on_K_of_sigmaBoundaryPieces F boundaryPieces_eq i
        (x := x) hxK)
    base_tsupport_subset_coordCarrier
    coordCarrier_subset_upperHalfSpace
    isCompact_coordCarrier
    Icc_subset_boundaryChartDomain
    coordCarrier_mapsTo_K
    coordCarrier_subset_sourceTarget
    coordCarrier_subset_overlap
    (fun i q hq =>
      S.coefficient_tsupport_inter_K_subset_finiteHalfSpaceCoverBox F
        boundaryPieces_eq lower_eq upper_eq i q hq)

/--
Variant of `toRefinedPartitionOfFiniteHalfSpaceCover` in which closed-box
domain containment is derived from the finite cover's ambient containment and
an ambient-to-boundary-domain compatibility field.
-/
def toRefinedPartitionOfFiniteHalfSpaceCoverOfAmbientDomain
    (targetChart :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C, Piece i → M)
    (boundaryPieces_eq :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C,
        S.boundaryPieces i = F.sigmaBoundaryPieces i)
    (lower_eq :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        S.lower i ⟨i, q⟩ = F.lowerCorner i q)
    (upper_eq :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        S.upper i ⟨i, q⟩ = F.upperCorner i q)
    (base_tsupport_subset_coordCarrier :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (S.sourceChart i ⟨i, q⟩) (targetChart i q) ω) ⊆
          coordCarrier i)
    (coordCarrier_subset_upperHalfSpace :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C,
        coordCarrier i ⊆ upperHalfSpace n)
    (isCompact_coordCarrier :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C,
        IsCompact (coordCarrier i))
    (ambient_subset_boundaryChartDomain :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        ambient i ⊆
          boundaryChartDomain I (S.sourceChart i ⟨i, q⟩) (targetChart i q))
    (coordCarrier_mapsTo_K :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        ∀ y ∈ coordCarrier i,
          (extChartAt I (S.sourceChart i ⟨i, q⟩)).symm y ∈ K)
    (coordCarrier_subset_sourceTarget :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        coordCarrier i ⊆ (extChartAt I (S.sourceChart i ⟨i, q⟩)).target)
    (coordCarrier_subset_overlap :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        coordCarrier i ⊆
          ManifoldForm.chartOverlap I (S.sourceChart i ⟨i, q⟩) (targetChart i q)) :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P ω
      (SigmaBoundaryPiece (I := I) (K := K) C Piece) :=
  CoverIndexedBoundaryBoxRefinedPartition.ofFiniteHalfSpaceCoverOfAmbientDomain
    (I := I) (K := K) (ω := ω) (C := C) (P := P) F
    (fun i q => S.sourceChart i ⟨i, q⟩)
    targetChart
    (fun i q => S.coefficient i ⟨i, q⟩)
    (fun i x hxK =>
      S.reconstruct_on_K_of_sigmaBoundaryPieces F boundaryPieces_eq i
        (x := x) hxK)
    base_tsupport_subset_coordCarrier
    coordCarrier_subset_upperHalfSpace
    isCompact_coordCarrier
    ambient_subset_boundaryChartDomain
    coordCarrier_mapsTo_K
    coordCarrier_subset_sourceTarget
    coordCarrier_subset_overlap
    (fun i q hq =>
      S.coefficient_tsupport_inter_K_subset_finiteHalfSpaceCoverBox F
        boundaryPieces_eq lower_eq upper_eq i q hq)

end BoundarySmoothBoxRefinement

end FromCollarPartition

end Stokes

end
