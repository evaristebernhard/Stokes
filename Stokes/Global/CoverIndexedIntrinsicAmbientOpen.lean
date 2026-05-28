import Stokes.Global.CoverIndexedZeroCompactRepresentedStokesIntrinsic
import Stokes.Global.CoverIndexedZeroCompactRelativeOpenCover

/-!
# Intrinsic ambient-open lift for canonical selected boundary covers

This file builds the manifold-side ambient open sets for the intrinsic
compact-support represented route directly from the coordinate `openPart`s of
the canonical selected finite half-space cover.

Unlike the older raw route, this construction does **not** intersect with
`C.assignedCoverSet` and therefore does not use any openness hypothesis for
assigned boundary chart boxes.

The unconditional inclusion of this ambient-open lift into a half-space support
box is intentionally not stated: `openPart` is ambient-open and does not carry
the missing normal-coordinate inequality `0 <= y 0`.  The file records the
usable restricted version with an explicit upper-half-space condition, and a
specialization on the natural active carrier where that condition is available.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section IntrinsicAmbientOpen

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable [FiniteDimensional Real (Fin (n + 1) → Real)]
variable [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]

namespace CoverIndexedZeroCompactRepresentedStokesIntrinsicInput

variable
    (X :
      CoverIndexedZeroCompactRepresentedStokesIntrinsicInput
        (I := I) (ω := ω) K)

/--
The intrinsic manifold-side ambient-open lift attached to one selected
finite-cover boundary piece.

It is just the chart source, intersected with the preimage of the coordinate
`openPart`.  No assigned-cover-set openness is used here.
-/
def intrinsicAmbientOpenPartPreimage
    (_i :
      CoverIndexedBoundaryIndex
        (I := I) (X.selectedCover (I := I) (K := K) (ω := ω)))
    (q : X.selectedBoundaryPiece (I := I) (K := K) (ω := ω)) :
    Set M :=
  let C := X.selectedCover (I := I) (K := K) (ω := ω)
  let F := X.selectedBoundaryFiniteCover (I := I) (K := K) (ω := ω)
  (extChartAt I (C.boundaryChart q.1.1)).source ∩
    (extChartAt I (C.boundaryChart q.1.1)) ⁻¹'
      F.openPart q.1 q.2

/--
The intrinsic `openPart` lift is open on the manifold side.

This is the key replacement for the old `assignedCoverSet_isOpen` route.
-/
theorem isOpen_intrinsicAmbientOpenPartPreimage
    (i :
      CoverIndexedBoundaryIndex
        (I := I) (X.selectedCover (I := I) (K := K) (ω := ω)))
    (q : X.selectedBoundaryPiece (I := I) (K := K) (ω := ω))
    (_hq :
      q ∈ (X.selectedBoundaryFiniteCover
        (I := I) (K := K) (ω := ω)).sigmaBoundaryPieces i) :
    IsOpen
      (X.intrinsicAmbientOpenPartPreimage
        (I := I) (K := K) (ω := ω) i q) := by
  classical
  let C := X.selectedCover (I := I) (K := K) (ω := ω)
  let F := X.selectedBoundaryFiniteCover (I := I) (K := K) (ω := ω)
  have hopenPart : IsOpen (F.openPart q.1 q.2) :=
    F.isOpen_openPart q.1 q.2
  simpa [intrinsicAmbientOpenPartPreimage, C, F] using
    isOpen_extChartAt_preimage'
      (I := I) (x := C.boundaryChart q.1.1) hopenPart

/--
The canonical boundary active carrier is covered by the intrinsic ambient-open
lifts of the selected finite half-space cover.
-/
theorem boundaryActiveCarrier_subset_iUnion_intrinsicAmbientOpenPartPreimage
    (i :
      CoverIndexedBoundaryIndex
        (I := I) (X.selectedCover (I := I) (K := K) (ω := ω))) :
    (X.selectedPartition
      (I := I) (K := K) (ω := ω)).boundaryActiveCarrier (I := I) i ⊆
      ⋃ q ∈
        (X.selectedBoundaryFiniteCover
          (I := I) (K := K) (ω := ω)).sigmaBoundaryPieces i,
        X.intrinsicAmbientOpenPartPreimage
          (I := I) (K := K) (ω := ω) i q := by
  classical
  let C := X.selectedCover (I := I) (K := K) (ω := ω)
  let P := X.selectedPartition (I := I) (K := K) (ω := ω)
  let F := X.selectedBoundaryFiniteCover (I := I) (K := K) (ω := ω)
  intro x hx
  have hycoord :
      (extChartAt I (C.boundaryChart i.1)) x ∈
        P.boundaryActiveCoordCarrier (I := I) i := by
    refine ⟨x, ?_, rfl⟩
    simpa [P] using hx
  have hcover :
      (extChartAt I (C.boundaryChart i.1)) x ∈
        ⋃ q : {q // q ∈ F.activePieces i}, F.openPart i q.1 :=
    F.carrier_subset_iUnion_openPart i hycoord
  rcases mem_iUnion.mp hcover with ⟨q, hxopen⟩
  let qflat : X.selectedBoundaryPiece (I := I) (K := K) (ω := ω) :=
    ⟨i, q.1⟩
  have hqflat : qflat ∈ F.sigmaBoundaryPieces i := by
    simp [qflat, CoverIndexedFiniteHalfSpaceBoxCover.sigmaBoundaryPieces]
  refine mem_iUnion_of_mem qflat ?_
  refine mem_iUnion_of_mem hqflat ?_
  have hxsource :
      x ∈ (extChartAt I (C.boundaryChart i.1)).source :=
    P.boundaryActiveCarrier_subset_chart_source (I := I) i hx
  exact ⟨by simpa [qflat] using hxsource, by simpa [qflat] using hxopen⟩

/--
If the lifted coordinate point is known to lie in the coordinate upper
half-space, the intrinsic ambient-open lift lands in the corresponding
half-space boundary chart box.

This is the honest set-theoretic form of the missing normal-coordinate input.
-/
theorem intrinsicAmbientOpenPartPreimage_subset_boundaryChartBox_of_chart_mem_upperHalfSpace
    (i :
      CoverIndexedBoundaryIndex
        (I := I) (X.selectedCover (I := I) (K := K) (ω := ω)))
    (q : X.selectedBoundaryPiece (I := I) (K := K) (ω := ω))
    (hq :
      q ∈ (X.selectedBoundaryFiniteCover
        (I := I) (K := K) (ω := ω)).sigmaBoundaryPieces i)
    (hupper :
      ∀ x ∈ X.intrinsicAmbientOpenPartPreimage
          (I := I) (K := K) (ω := ω) i q,
        (extChartAt I
          ((X.selectedCover (I := I) (K := K) (ω := ω)).boundaryChart q.1.1)) x ∈
          upperHalfSpace n) :
    X.intrinsicAmbientOpenPartPreimage
        (I := I) (K := K) (ω := ω) i q ⊆
      boundaryChartBoxNeighborhood I
        ((X.selectedCover (I := I) (K := K) (ω := ω)).boundaryChart q.1.1)
        ((X.selectedBoundaryFiniteCover
          (I := I) (K := K) (ω := ω)).lowerCorner q.1 q.2)
        ((X.selectedBoundaryFiniteCover
          (I := I) (K := K) (ω := ω)).upperCorner q.1 q.2) := by
  classical
  let C := X.selectedCover (I := I) (K := K) (ω := ω)
  let F := X.selectedBoundaryFiniteCover (I := I) (K := K) (ω := ω)
  intro x hx
  have hactive : q.2 ∈ F.activePieces q.1 :=
    F.sigmaBoundaryPieces_active hq
  have hxsource :
      x ∈ (extChartAt I (C.boundaryChart q.1.1)).source := hx.1
  have hxopen :
      (extChartAt I (C.boundaryChart q.1.1)) x ∈ F.openPart q.1 q.2 := hx.2
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
        ⟨by simpa [C, F] using hupper x hx,
          by simpa [CoverIndexedFiniteHalfSpaceBoxCover.openPart] using hxopen⟩
  exact
    ⟨by simpa [C] using hxsource,
      by simpa [C, F, boundaryChartBoxNeighborhood] using hxbox⟩

/--
On the natural active carrier, the missing upper-half-space condition is
available from the selected boundary chart-box support control.
-/
theorem intrinsicAmbientOpenPartPreimage_inter_activeCarrier_subset_boundaryChartBox
    (i :
      CoverIndexedBoundaryIndex
        (I := I) (X.selectedCover (I := I) (K := K) (ω := ω)))
    (q : X.selectedBoundaryPiece (I := I) (K := K) (ω := ω))
    (hq :
      q ∈ (X.selectedBoundaryFiniteCover
        (I := I) (K := K) (ω := ω)).sigmaBoundaryPieces i)
    (hqi : q.1 = i) :
    X.intrinsicAmbientOpenPartPreimage
        (I := I) (K := K) (ω := ω) i q ∩
        (X.selectedPartition
          (I := I) (K := K) (ω := ω)).boundaryActiveCarrier (I := I) i ⊆
      boundaryChartBoxNeighborhood I
        ((X.selectedCover (I := I) (K := K) (ω := ω)).boundaryChart q.1.1)
        ((X.selectedBoundaryFiniteCover
          (I := I) (K := K) (ω := ω)).lowerCorner q.1 q.2)
        ((X.selectedBoundaryFiniteCover
          (I := I) (K := K) (ω := ω)).upperCorner q.1 q.2) := by
  classical
  let C := X.selectedCover (I := I) (K := K) (ω := ω)
  let P := X.selectedPartition (I := I) (K := K) (ω := ω)
  let F := X.selectedBoundaryFiniteCover (I := I) (K := K) (ω := ω)
  intro x hx
  have hactive : q.2 ∈ F.activePieces q.1 :=
    F.sigmaBoundaryPieces_active hq
  have hxsource :
      x ∈ (extChartAt I (C.boundaryChart q.1.1)).source := hx.1.1
  have hxopen :
      (extChartAt I (C.boundaryChart q.1.1)) x ∈ F.openPart q.1 q.2 := hx.1.2
  have hxupper :
      (extChartAt I (C.boundaryChart q.1.1)) x ∈ upperHalfSpace n := by
    have hxupper_i :
        (extChartAt I (C.boundaryChart i.1)) x ∈ upperHalfSpace n :=
      P.boundaryActiveCarrier_chart_mem_upperHalfSpace (I := I) i hx.2
    simpa [hqi] using hxupper_i
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
Membership in `sigmaBoundaryPieces` already records that a flattened selected
boundary piece belongs to the boundary index it is summed over.
-/
theorem intrinsicAmbientOpenPartPreimage_inter_activeCarrier_subset_boundaryChartBox'
    (i :
      CoverIndexedBoundaryIndex
        (I := I) (X.selectedCover (I := I) (K := K) (ω := ω)))
    (q : X.selectedBoundaryPiece (I := I) (K := K) (ω := ω))
    (hq :
      q ∈ (X.selectedBoundaryFiniteCover
        (I := I) (K := K) (ω := ω)).sigmaBoundaryPieces i) :
    X.intrinsicAmbientOpenPartPreimage
        (I := I) (K := K) (ω := ω) i q ∩
        (X.selectedPartition
          (I := I) (K := K) (ω := ω)).boundaryActiveCarrier (I := I) i ⊆
      boundaryChartBoxNeighborhood I
        ((X.selectedCover (I := I) (K := K) (ω := ω)).boundaryChart q.1.1)
        ((X.selectedBoundaryFiniteCover
          (I := I) (K := K) (ω := ω)).lowerCorner q.1 q.2)
        ((X.selectedBoundaryFiniteCover
          (I := I) (K := K) (ω := ω)).upperCorner q.1 q.2) := by
  exact
    X.intrinsicAmbientOpenPartPreimage_inter_activeCarrier_subset_boundaryChartBox
      (I := I) (K := K) (ω := ω) i q hq
      ((X.selectedBoundaryFiniteCover
        (I := I) (K := K) (ω := ω)).mem_sigmaBoundaryPieces.mp hq).1

end CoverIndexedZeroCompactRepresentedStokesIntrinsicInput

end IntrinsicAmbientOpen

end Stokes

end
