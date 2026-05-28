import Stokes.Global.CoverIndexedIntrinsicAmbientOpen
import Stokes.Global.CoverIndexedZeroCompactSmoothBoxRefinement

/-!
# Intrinsic smooth-refinement constructor

This file closes the smooth-refinement generation checkpoint for the intrinsic
compact-support represented route.

The raw route used openness of the assigned boundary chart boxes.  The
intrinsic route instead uses the auxiliary open shrink remembered by
`openSelectedCover`, intersected with the selected finite half-space cover's
coordinate `openPart`.  The open shrink supplies both manifold-side openness
and, through `openCoverSet_subset_assigned`, the upper-half-space fact needed
to place the ambient-open lift inside the refined half-space box.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section IntrinsicSmoothRefinementConstructor

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable [FiniteDimensional Real (Fin (n + 1) -> Real)]
variable [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]

namespace CoverIndexedZeroCompactRepresentedStokesIntrinsicInput

variable
    (X :
      CoverIndexedZeroCompactRepresentedStokesIntrinsicInput
        (I := I) (ω := omega) K)

/--
The intrinsic manifold-side ambient open used for the selected smooth
refinement.

It is the open shrink attached to the boundary chart index, further restricted
to the chart-source/preimage of the selected finite half-space cover's
coordinate `openPart`.
-/
def selectedSmoothRefinementAmbientOpen
    (_i :
      CoverIndexedBoundaryIndex
        (I := I) (X.selectedCover (I := I) (K := K) (ω := omega)))
    (q : X.selectedBoundaryPiece (I := I) (K := K) (ω := omega)) :
    Set M :=
  let C := X.selectedCover (I := I) (K := K) (ω := omega)
  let F := X.selectedBoundaryFiniteCover (I := I) (K := K) (ω := omega)
  (X.openSelectedCover (I := I) (K := K) (ω := omega)).openCoverSet
      (Sum.inr q.1) ∩
    ((extChartAt I (C.boundaryChart q.1.1)).source ∩
      (extChartAt I (C.boundaryChart q.1.1)) ⁻¹'
        F.openPart q.1 q.2)

/-- The selected smooth-refinement ambient lift is open. -/
theorem isOpen_selectedSmoothRefinementAmbientOpen
    (i :
      CoverIndexedBoundaryIndex
        (I := I) (X.selectedCover (I := I) (K := K) (ω := omega)))
    (q : X.selectedBoundaryPiece (I := I) (K := K) (ω := omega))
    (_hq :
      q ∈ (X.selectedBoundaryFiniteCover
        (I := I) (K := K) (ω := omega)).sigmaBoundaryPieces i) :
    IsOpen
      (X.selectedSmoothRefinementAmbientOpen
        (I := I) (K := K) (omega := omega) i q) := by
  classical
  let C := X.selectedCover (I := I) (K := K) (ω := omega)
  let F := X.selectedBoundaryFiniteCover (I := I) (K := K) (ω := omega)
  let O := X.openSelectedCover (I := I) (K := K) (ω := omega)
  have hopenCover : IsOpen (O.openCoverSet (Sum.inr q.1)) :=
    O.openCoverSet_isOpen (Sum.inr q.1)
  have hopenPart : IsOpen (F.openPart q.1 q.2) :=
    F.isOpen_openPart q.1 q.2
  have hchart :
      IsOpen
        ((extChartAt I (C.boundaryChart q.1.1)).source ∩
          (extChartAt I (C.boundaryChart q.1.1)) ⁻¹'
            F.openPart q.1 q.2) :=
    isOpen_extChartAt_preimage' (I := I)
      (x := C.boundaryChart q.1.1) hopenPart
  simpa [selectedSmoothRefinementAmbientOpen, C, F, O] using
    hopenCover.inter hchart

/--
The natural boundary active carrier is covered by the selected
smooth-refinement ambient opens.
-/
theorem boundaryActiveCarrier_subset_iUnion_selectedSmoothRefinementAmbientOpen
    (i :
      CoverIndexedBoundaryIndex
        (I := I) (X.selectedCover (I := I) (K := K) (ω := omega))) :
    (X.selectedPartition
      (I := I) (K := K) (ω := omega)).boundaryActiveCarrier (I := I) i ⊆
      ⋃ q ∈
        (X.selectedBoundaryFiniteCover
          (I := I) (K := K) (ω := omega)).sigmaBoundaryPieces i,
        X.selectedSmoothRefinementAmbientOpen
          (I := I) (K := K) (omega := omega) i q := by
  classical
  let C := X.selectedCover (I := I) (K := K) (ω := omega)
  let P := X.selectedPartition (I := I) (K := K) (ω := omega)
  let F := X.selectedBoundaryFiniteCover (I := I) (K := K) (ω := omega)
  let O := X.openSelectedCover (I := I) (K := K) (ω := omega)
  intro x hx
  have hxopen :
      x ∈ O.openCoverSet (Sum.inr i) := by
    exact
      X.selectedPartition_tsupport_inter_subset_openCoverSet
        (I := I) (K := K) (ω := omega) (Sum.inr i) hx
  have hycoord :
      (extChartAt I (C.boundaryChart i.1)) x ∈
        P.boundaryActiveCoordCarrier (I := I) i := by
    refine ⟨x, ?_, rfl⟩
    simpa [P] using hx
  have hcover :
      (extChartAt I (C.boundaryChart i.1)) x ∈
        ⋃ q : {q // q ∈ F.activePieces i}, F.openPart i q.1 :=
    F.carrier_subset_iUnion_openPart i hycoord
  rcases mem_iUnion.mp hcover with ⟨q, hxpart⟩
  let qflat : X.selectedBoundaryPiece (I := I) (K := K) (ω := omega) :=
    ⟨i, q.1⟩
  have hqflat : qflat ∈ F.sigmaBoundaryPieces i := by
    simp [qflat, CoverIndexedFiniteHalfSpaceBoxCover.sigmaBoundaryPieces]
  refine mem_iUnion_of_mem qflat ?_
  refine mem_iUnion_of_mem hqflat ?_
  have hxsource :
      x ∈ (extChartAt I (C.boundaryChart i.1)).source :=
    P.boundaryActiveCarrier_subset_chart_source (I := I) i hx
  exact
    ⟨by simpa [qflat, O] using hxopen,
      ⟨by simpa [qflat] using hxsource, by simpa [qflat] using hxpart⟩⟩

/--
Each selected smooth-refinement ambient open lies in its selected finite
half-space boundary chart box.
-/
theorem selectedSmoothRefinementAmbientOpen_subset_boundaryChartBox
    (i :
      CoverIndexedBoundaryIndex
        (I := I) (X.selectedCover (I := I) (K := K) (ω := omega)))
    (q : X.selectedBoundaryPiece (I := I) (K := K) (ω := omega))
    (hq :
      q ∈ (X.selectedBoundaryFiniteCover
        (I := I) (K := K) (ω := omega)).sigmaBoundaryPieces i) :
    X.selectedSmoothRefinementAmbientOpen
        (I := I) (K := K) (omega := omega) i q ⊆
      boundaryChartBoxNeighborhood I
        ((X.selectedCover (I := I) (K := K) (ω := omega)).boundaryChart q.1.1)
        ((X.selectedBoundaryFiniteCover
          (I := I) (K := K) (ω := omega)).lowerCorner q.1 q.2)
        ((X.selectedBoundaryFiniteCover
          (I := I) (K := K) (ω := omega)).upperCorner q.1 q.2) := by
  classical
  let C := X.selectedCover (I := I) (K := K) (ω := omega)
  let F := X.selectedBoundaryFiniteCover (I := I) (K := K) (ω := omega)
  let O := X.openSelectedCover (I := I) (K := K) (ω := omega)
  intro x hx
  have hactive : q.2 ∈ F.activePieces q.1 :=
    F.sigmaBoundaryPieces_active hq
  have hxassigned :
      x ∈ C.assignedCoverSet (Sum.inr q.1) :=
    O.openCoverSet_subset_assigned (Sum.inr q.1) hx.1
  have hxsource :
      x ∈ (extChartAt I (C.boundaryChart q.1.1)).source := hx.2.1
  have hxopen :
      (extChartAt I (C.boundaryChart q.1.1)) x ∈ F.openPart q.1 q.2 :=
    hx.2.2
  have hxupper :
      (extChartAt I (C.boundaryChart q.1.1)) x ∈ upperHalfSpace n := by
    have hbox :
        (extChartAt I (C.boundaryChart q.1.1)) x ∈
          halfSpaceSupportBox (C.boundaryLower q.1.1) (C.boundaryUpper q.1.1) := by
      simpa [CompactSupportChartCoverSelection.assignedCoverSet,
        boundaryChartBoxNeighborhood] using hxassigned.2
    have hzero : C.boundaryLower q.1.1 0 = 0 :=
      C.boundary_lower_zero q.1.1 q.1.2
    simpa [upperHalfSpace, hzero] using hbox.1
  have hxbox :
      (extChartAt I (C.boundaryChart q.1.1)) x ∈
        halfSpaceSupportBox (F.lowerCorner q.1 q.2) (F.upperCorner q.1 q.2) := by
    exact
      upperHalfSpace_inter_halfSpaceSupportBoxOpenPart_subset
        (n := n)
        (a := F.lowerCorner q.1 q.2)
        (b := F.upperCorner q.1 q.2)
        (by
          simpa [CoverIndexedFiniteHalfSpaceBoxCover.activePieces,
            CoverIndexedFiniteHalfSpaceBoxCover.lowerCorner] using
            (F.cover q.1).lowerCorner_zero q.2 hactive)
        ⟨hxupper, by simpa [CoverIndexedFiniteHalfSpaceBoxCover.openPart] using hxopen⟩
  exact
    ⟨by simpa [C] using hxsource,
      by simpa [C, F, boundaryChartBoxNeighborhood] using hxbox⟩

/--
The canonical selected smooth box refinement generated by the intrinsic route.
-/
def selectedSmoothRefinement
    [DecidableEq (X.selectedBoundaryPiece (I := I) (K := K) (ω := omega))] :
    BoundarySmoothBoxRefinement
      (I := I) (K := K)
      (X.selectedCover (I := I) (K := K) (ω := omega))
      (X.selectedPartition (I := I) (K := K) (ω := omega))
      (X.selectedBoundaryPiece (I := I) (K := K) (ω := omega)) :=
  BoundarySmoothBoxRefinement.ofFiniteOpenCover
    (I := I) (K := K)
    (C := X.selectedCover (I := I) (K := K) (ω := omega))
    (P := X.selectedPartition (I := I) (K := K) (ω := omega))
    (BoundaryPiece := X.selectedBoundaryPiece (I := I) (K := K) (ω := omega))
    (activeCarrier := fun i =>
      (X.selectedPartition
        (I := I) (K := K) (ω := omega)).boundaryActiveCarrier (I := I) i)
    (boundaryPieces := fun i =>
      (X.selectedBoundaryFiniteCover
        (I := I) (K := K) (ω := omega)).sigmaBoundaryPieces i)
    (sourceChart := fun _ q =>
      (X.selectedCover (I := I) (K := K) (ω := omega)).boundaryChart q.1.1)
    (lower := fun _ q =>
      (X.selectedBoundaryFiniteCover
        (I := I) (K := K) (ω := omega)).lowerCorner q.1 q.2)
    (upper := fun _ q =>
      (X.selectedBoundaryFiniteCover
        (I := I) (K := K) (ω := omega)).upperCorner q.1 q.2)
    (ambientOpen :=
      X.selectedSmoothRefinementAmbientOpen
        (I := I) (K := K) (omega := omega))
    (isCompact_activeCarrier := by
      intro i
      exact
        SupportControlledSelectedPartition.isCompact_boundaryActiveCarrier
          (I := I)
          (P := X.selectedPartition (I := I) (K := K) (ω := omega))
          X.hK i)
    (ambientOpen_isOpen := by
      intro i q hq
      exact
        X.isOpen_selectedSmoothRefinementAmbientOpen
          (I := I) (K := K) (omega := omega) i q hq)
    (activeCarrier_subset_iUnion_ambientOpen := by
      intro i
      exact
        X.boundaryActiveCarrier_subset_iUnion_selectedSmoothRefinementAmbientOpen
          (I := I) (K := K) (omega := omega) i)
    (ambientOpen_subset_boundaryChartBox := by
      intro i q hq
      exact
        X.selectedSmoothRefinementAmbientOpen_subset_boundaryChartBox
          (I := I) (K := K) (omega := omega) i q hq)
    (base_tsupport_inter_K_subset_carrier := by
      intro i
      exact subset_rfl)

@[simp]
theorem selectedSmoothRefinement_boundaryPieces
    [DecidableEq (X.selectedBoundaryPiece (I := I) (K := K) (ω := omega))]
    (i :
      CoverIndexedBoundaryIndex
        (I := I) (X.selectedCover (I := I) (K := K) (ω := omega))) :
    (X.selectedSmoothRefinement
      (I := I) (K := K) (omega := omega)).boundaryPieces i =
      (X.selectedBoundaryFiniteCover
        (I := I) (K := K) (ω := omega)).sigmaBoundaryPieces i := by
  rfl

@[simp]
theorem selectedSmoothRefinement_activeCarrier
    [DecidableEq (X.selectedBoundaryPiece (I := I) (K := K) (ω := omega))]
    (i :
      CoverIndexedBoundaryIndex
        (I := I) (X.selectedCover (I := I) (K := K) (ω := omega))) :
    (X.selectedSmoothRefinement
      (I := I) (K := K) (omega := omega)).activeCarrier i =
      (X.selectedPartition
        (I := I) (K := K) (ω := omega)).boundaryActiveCarrier (I := I) i := by
  rfl

/--
Existence form of the intrinsic selected smooth-refinement checkpoint.

The returned refinement has pieces exactly matching
`X.selectedBoundaryFiniteCover.sigmaBoundaryPieces`; the refinement structure
itself carries the smooth partition of unity, subordination, support, and
reconstruction fields produced by `BoundarySmoothBoxRefinement.ofFiniteOpenCover`.
-/
theorem existsSelectedSmoothRefinement
    [DecidableEq (X.selectedBoundaryPiece (I := I) (K := K) (ω := omega))] :
    ∃ S :
      BoundarySmoothBoxRefinement
        (I := I) (K := K)
        (X.selectedCover (I := I) (K := K) (ω := omega))
        (X.selectedPartition (I := I) (K := K) (ω := omega))
        (X.selectedBoundaryPiece (I := I) (K := K) (ω := omega)),
      (∀ i :
        CoverIndexedBoundaryIndex
          (I := I) (X.selectedCover (I := I) (K := K) (ω := omega)),
        S.boundaryPieces i =
          (X.selectedBoundaryFiniteCover
            (I := I) (K := K) (ω := omega)).sigmaBoundaryPieces i) ∧
        (∀ i :
          CoverIndexedBoundaryIndex
            (I := I) (X.selectedCover (I := I) (K := K) (ω := omega)),
          S.activeCarrier i =
            (X.selectedPartition
              (I := I) (K := K) (ω := omega)).boundaryActiveCarrier (I := I) i) ∧
        (∀ i
          (q : X.selectedBoundaryPiece (I := I) (K := K) (ω := omega)),
          S.sourceChart i q =
            (X.selectedCover
              (I := I) (K := K) (ω := omega)).boundaryChart q.1.1) ∧
        (∀ i
          (q : X.selectedBoundaryPiece (I := I) (K := K) (ω := omega)),
          S.lower i q =
            (X.selectedBoundaryFiniteCover
              (I := I) (K := K) (ω := omega)).lowerCorner q.1 q.2) ∧
        (∀ i
          (q : X.selectedBoundaryPiece (I := I) (K := K) (ω := omega)),
          S.upper i q =
            (X.selectedBoundaryFiniteCover
              (I := I) (K := K) (ω := omega)).upperCorner q.1 q.2) := by
  refine ⟨X.selectedSmoothRefinement (I := I) (K := K) (omega := omega), ?_⟩
  exact ⟨by intro i; rfl,
    by intro i; rfl,
    by intro i q; rfl,
    by intro i q; rfl,
    by intro i q; rfl⟩

end CoverIndexedZeroCompactRepresentedStokesIntrinsicInput

end IntrinsicSmoothRefinementConstructor

end Stokes

end
