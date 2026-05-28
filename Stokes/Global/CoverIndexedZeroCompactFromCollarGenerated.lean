import Stokes.Global.CoverIndexedZeroCompactRepresentedStokesFromCollar
import Stokes.Global.CoverIndexedZeroCompactBoundaryCarrierRefinement

/-!
# Generated compact-support represented Stokes data from collar carriers

This file starts the clean generated-data layer for the compact-support
represented Stokes route.  The natural boundary carrier is
`P.boundaryActiveCarrier`; its coordinate image is
`P.boundaryActiveCoordCarrier`.  From compact support plus collar-prism data we
generate the finite half-space box cover, and from small manifold-side
ambient-open lift data we generate the smooth box refinement.

The manifold-side open lift is deliberately an explicit small hypothesis:
choosing open neighborhoods whose chart images sit in the selected coordinate
boxes is chart geometry, not a definitional consequence of the collar cover.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section FromCollarGenerated

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/--
Generated collar data for the compact-support represented route.

The compactness and half-space fields for the coordinate carriers are not
stored: they are generated from `P.boundaryActiveCarrier`,
`P.boundaryActiveCoordCarrier`, and compactness of `K`.
-/
structure CoverIndexedZeroCompactFromCollarGenerated
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C) where
  /-- Compact global support set. -/
  hK : IsCompact K
  /-- Coordinate-side ambient region for each natural boundary carrier. -/
  ambient :
    CoverIndexedBoundaryIndex (I := I) C → Set (Fin (n + 1) → Real)
  /--
  Collar/prism containment around every natural boundary active coordinate
  carrier point.
  -/
  collar_prisms :
    ∀ i : CoverIndexedBoundaryIndex (I := I) C,
      ∀ x ∈ P.boundaryActiveCoordCarrier (I := I) i, ∃ eps : Real,
        0 < eps ∧ halfSpaceCollarPrism (n := n) x eps ⊆ ambient i

namespace CoverIndexedZeroCompactFromCollarGenerated

variable
    (D :
      CoverIndexedZeroCompactFromCollarGenerated
        (I := I) (K := K) C P)

/-- The natural manifold-side active carrier for a boundary partition term. -/
def activeCarrier
    (_D :
      CoverIndexedZeroCompactFromCollarGenerated
        (I := I) (K := K) C P) :
    CoverIndexedBoundaryIndex (I := I) C → Set M :=
  P.boundaryActiveCarrier (I := I)

/-- The natural coordinate carrier for a boundary partition term. -/
def coordCarrier
    (_D :
      CoverIndexedZeroCompactFromCollarGenerated
        (I := I) (K := K) C P) :
    CoverIndexedBoundaryIndex (I := I) C → Set (Fin (n + 1) → Real) :=
  P.boundaryActiveCoordCarrier (I := I)

@[simp]
theorem activeCarrier_eq
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    D.activeCarrier (I := I) (K := K) i =
      P.boundaryActiveCarrier (I := I) i := by
  rfl

@[simp]
theorem coordCarrier_eq
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    D.coordCarrier (I := I) (K := K) i =
      P.boundaryActiveCoordCarrier (I := I) i := by
  rfl

/-- The generated active carriers are compact. -/
theorem isCompact_activeCarrier
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    IsCompact (D.activeCarrier (I := I) (K := K) i) := by
  simpa [activeCarrier] using
    SupportControlledSelectedPartition.isCompact_boundaryActiveCarrier
      (I := I) P D.hK i

/-- The generated coordinate carriers are compact. -/
theorem isCompact_coordCarrier
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    IsCompact (D.coordCarrier (I := I) (K := K) i) := by
  simpa [coordCarrier] using
    SupportControlledSelectedPartition.isCompact_boundaryActiveCoordCarrier
      (I := I) P D.hK i

/-- The generated coordinate carriers lie in the closed upper half-space. -/
theorem coordCarrier_subset_upperHalfSpace
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    D.coordCarrier (I := I) (K := K) i ⊆ upperHalfSpace n := by
  simpa [coordCarrier] using
    SupportControlledSelectedPartition.boundaryActiveCoordCarrier_subset_upperHalfSpace
      (I := I) P i

/--
The finite half-space cover generated from the natural coordinate carriers and
the supplied collar-prism containment.
-/
def finiteHalfSpaceCover :
    CoverIndexedFiniteHalfSpaceBoxCover
      (I := I) (K := K) C
      (D.coordCarrier (I := I) (K := K)) D.ambient
      (fun _ : CoverIndexedBoundaryIndex (I := I) C =>
        Fin (n + 1) → Real) :=
  coverIndexedFiniteHalfSpaceBoxCoverOfCollar
    (I := I) (K := K) (C := C)
    (D.coordCarrier (I := I) (K := K)) D.ambient
    (D.isCompact_coordCarrier (I := I) (K := K))
    (D.coordCarrier_subset_upperHalfSpace (I := I) (K := K))
    (by
      intro i x hx
      exact D.collar_prisms i x hx)

/-- Active centers selected by the generated finite half-space cover remain in
the generated coordinate carrier. -/
theorem finiteHalfSpaceCover_active_subset
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    ∀ x ∈
      ((D.finiteHalfSpaceCover
        (I := I) (K := K) (C := C)).cover i).activePieces,
        x ∈ D.coordCarrier (I := I) (K := K) i := by
  simpa [finiteHalfSpaceCover] using
    (coverIndexedFiniteHalfSpaceBoxCoverOfCollar_active_subset
      (I := I) (K := K) (C := C)
      (D.coordCarrier (I := I) (K := K)) D.ambient
      (D.isCompact_coordCarrier (I := I) (K := K))
      (D.coordCarrier_subset_upperHalfSpace (I := I) (K := K))
      (by
        intro i x hx
        exact D.collar_prisms i x hx)
      i)

/-- The uniform refined-boundary piece type generated by the finite
half-space cover. -/
abbrev BoundaryPiece
    (_D :
      CoverIndexedZeroCompactFromCollarGenerated
        (I := I) (K := K) C P) : Type uM :=
  SigmaBoundaryPiece (I := I) (K := K) C
    (fun _ : CoverIndexedBoundaryIndex (I := I) C =>
      Fin (n + 1) → Real)

/-- Classical decidable equality for the generated finite-cover piece type. -/
instance instDecidableEqBoundaryPiece
    (D :
      CoverIndexedZeroCompactFromCollarGenerated
        (I := I) (K := K) C P) :
    DecidableEq (D.BoundaryPiece (I := I) (K := K)) :=
  Classical.decEq _

/-- The finite refined pieces over one boundary index generated by the finite
half-space cover. -/
def boundaryPieces
    (D :
      CoverIndexedZeroCompactFromCollarGenerated
        (I := I) (K := K) C P)
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    Finset (D.BoundaryPiece (I := I) (K := K)) :=
  (D.finiteHalfSpaceCover
    (I := I) (K := K) (C := C)).sigmaBoundaryPieces i

/-- The generated source chart for a finite-cover refined piece. -/
def sourceChart
    (D :
      CoverIndexedZeroCompactFromCollarGenerated
        (I := I) (K := K) C P)
    (_i : CoverIndexedBoundaryIndex (I := I) C)
    (q : D.BoundaryPiece (I := I) (K := K)) : M :=
  C.boundaryChart q.1.1

/-- The generated lower corner for a finite-cover refined piece. -/
def lower
    (D :
      CoverIndexedZeroCompactFromCollarGenerated
        (I := I) (K := K) C P)
    (_i : CoverIndexedBoundaryIndex (I := I) C)
    (q : D.BoundaryPiece (I := I) (K := K)) :
    Fin (n + 1) → Real :=
  (D.finiteHalfSpaceCover
    (I := I) (K := K) (C := C)).lowerCorner q.1 q.2

/-- The generated upper corner for a finite-cover refined piece. -/
def upper
    (D :
      CoverIndexedZeroCompactFromCollarGenerated
        (I := I) (K := K) C P)
    (_i : CoverIndexedBoundaryIndex (I := I) C)
    (q : D.BoundaryPiece (I := I) (K := K)) :
    Fin (n + 1) → Real :=
  (D.finiteHalfSpaceCover
    (I := I) (K := K) (C := C)).upperCorner q.1 q.2

/--
Small honest manifold-side open-cover data needed to turn the generated
finite-coordinate cover into a smooth box refinement.

The field `ambientOpen_subset_boundaryChartBox` is the nontrivial chart lift:
it states that the chosen manifold-side open set is already inside the
boundary chart box attached to the generated finite-cover piece.
-/
structure FiniteCoverAmbientOpenData
    (D :
      CoverIndexedZeroCompactFromCollarGenerated
        (I := I) (K := K) C P) where
  /-- Manifold-side open neighborhood assigned to each generated refined box. -/
  ambientOpen :
    CoverIndexedBoundaryIndex (I := I) C →
      D.BoundaryPiece (I := I) (K := K) → Set M
  /-- The assigned manifold-side neighborhoods are open. -/
  ambientOpen_isOpen :
    ∀ i q, q ∈ D.boundaryPieces (I := I) (K := K) i →
      IsOpen (ambientOpen i q)
  /-- The natural active carrier is covered by the assigned neighborhoods. -/
  activeCarrier_subset_iUnion_ambientOpen :
    ∀ i : CoverIndexedBoundaryIndex (I := I) C,
      D.activeCarrier (I := I) (K := K) i ⊆
        ⋃ q ∈ D.boundaryPieces (I := I) (K := K) i, ambientOpen i q
  /-- Each assigned neighborhood lies in the generated boundary chart box. -/
  ambientOpen_subset_boundaryChartBox :
    ∀ i q, q ∈ D.boundaryPieces (I := I) (K := K) i →
      ambientOpen i q ⊆
        boundaryChartBoxNeighborhood I
          (D.sourceChart (I := I) (K := K) i q)
          (D.lower (I := I) (K := K) i q)
          (D.upper (I := I) (K := K) i q)

/--
The smooth box refinement generated from the natural active carriers, the
generated finite half-space cover, and a small manifold-side ambient-open lift.
-/
def smoothRefinementOfFiniteOpenCover
    [FiniteDimensional Real (Fin (n + 1) → Real)]
    [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]
    (A :
      FiniteCoverAmbientOpenData
        (I := I) (K := K) (C := C) (P := P) D) :
    BoundarySmoothBoxRefinement
      (I := I) (K := K) C P (D.BoundaryPiece (I := I) (K := K)) :=
  BoundarySmoothBoxRefinement.ofFiniteOpenCover
    (I := I) (K := K) (C := C) (P := P)
    (activeCarrier := D.activeCarrier (I := I) (K := K))
    (boundaryPieces := D.boundaryPieces (I := I) (K := K))
    (sourceChart := D.sourceChart (I := I) (K := K))
    (lower := D.lower (I := I) (K := K))
    (upper := D.upper (I := I) (K := K))
    (ambientOpen := A.ambientOpen)
    (isCompact_activeCarrier :=
      D.isCompact_activeCarrier (I := I) (K := K))
    (ambientOpen_isOpen := A.ambientOpen_isOpen)
    (activeCarrier_subset_iUnion_ambientOpen :=
      A.activeCarrier_subset_iUnion_ambientOpen)
    (ambientOpen_subset_boundaryChartBox :=
      A.ambientOpen_subset_boundaryChartBox)
    (base_tsupport_inter_K_subset_carrier := by
      intro i
      exact subset_rfl)

@[simp]
theorem smoothRefinementOfFiniteOpenCover_activeCarrier
    [FiniteDimensional Real (Fin (n + 1) → Real)]
    [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]
    (A :
      FiniteCoverAmbientOpenData
        (I := I) (K := K) (C := C) (P := P) D) :
    (D.smoothRefinementOfFiniteOpenCover
      (I := I) (K := K) A).activeCarrier =
      D.activeCarrier (I := I) (K := K) := by
  rfl

@[simp]
theorem smoothRefinementOfFiniteOpenCover_boundaryPieces
    [FiniteDimensional Real (Fin (n + 1) → Real)]
    [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]
    (A :
      FiniteCoverAmbientOpenData
        (I := I) (K := K) (C := C) (P := P) D) :
    (D.smoothRefinementOfFiniteOpenCover
      (I := I) (K := K) A).boundaryPieces =
      D.boundaryPieces (I := I) (K := K) := by
  rfl

end CoverIndexedZeroCompactFromCollarGenerated

end FromCollarGenerated

end Stokes

end
