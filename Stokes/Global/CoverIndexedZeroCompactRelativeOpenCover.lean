import Stokes.Global.CoverIndexedZeroCompactFiniteHalfSpaceCover
import Stokes.Global.SupportControlledPartition
import Stokes.Global.SupportControlledSelectedPartition

/-!
# Relative open covers from finite half-space box covers

The finite half-space boxes used near a boundary chart are not ambient-open:
they include the true boundary face `x₀ = 0`, but remain strict in every
artificial face direction.  Smooth partitions of unity, however, need an
ambient-open cover.

This file isolates the bridge.  Each half-space support box has an ambient-open
part `halfSpaceSupportBoxOpenPart`.  On the closed coordinate half-space, and
provided the lower normal corner is normalized by `a 0 = 0`, this open part is
exactly the support box.  Therefore a partition subordinate to the open parts
still gives support inside the corresponding half-space support boxes after
intersecting with a carrier contained in `upperHalfSpace n`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section PureRelativeOpen

variable {n : Nat}

/-- A half-space support box is always contained in its ambient-open part. -/
theorem halfSpaceSupportBox_subset_halfSpaceSupportBoxOpenPart
    (a b : Fin (n + 1) → Real) :
    halfSpaceSupportBox a b ⊆ halfSpaceSupportBoxOpenPart (n := n) a b := by
  intro y hy
  exact ⟨hy.2.1, hy.2.2⟩

/-- On the coordinate upper half-space, the ambient-open part of a normalized
half-space box is contained in the actual half-space support box. -/
theorem upperHalfSpace_inter_halfSpaceSupportBoxOpenPart_subset
    {a b : Fin (n + 1) → Real} (ha0 : a 0 = 0) :
    upperHalfSpace n ∩ halfSpaceSupportBoxOpenPart (n := n) a b ⊆
      halfSpaceSupportBox a b := by
  rintro y ⟨hyhalf, hyopen⟩
  refine ⟨?_, hyopen.1, hyopen.2⟩
  simpa [upperHalfSpace, ha0] using hyhalf

/-- With normalized lower normal corner, the support box is the intersection of
the coordinate half-space and its ambient-open part. -/
theorem halfSpaceSupportBox_eq_upperHalfSpace_inter_openPart
    {a b : Fin (n + 1) → Real} (ha0 : a 0 = 0) :
    halfSpaceSupportBox a b =
      upperHalfSpace n ∩ halfSpaceSupportBoxOpenPart (n := n) a b := by
  ext y
  constructor
  · intro hy
    exact
      ⟨by simpa [upperHalfSpace, ha0] using hy.1,
        halfSpaceSupportBox_subset_halfSpaceSupportBoxOpenPart
          (n := n) a b hy⟩
  · intro hy
    exact upperHalfSpace_inter_halfSpaceSupportBoxOpenPart_subset
      (n := n) (a := a) (b := b) ha0 hy

/-- If a carrier lies in the coordinate half-space, then intersecting it with
the ambient-open part of a normalized half-space box lands in the support box. -/
theorem inter_halfSpaceSupportBoxOpenPart_subset_halfSpaceSupportBox_of_subset_upperHalfSpace
    {K : Set (Fin (n + 1) → Real)}
    {a b : Fin (n + 1) → Real}
    (hKhalf : K ⊆ upperHalfSpace n) (ha0 : a 0 = 0) :
    K ∩ halfSpaceSupportBoxOpenPart (n := n) a b ⊆
      halfSpaceSupportBox a b := by
  rintro y ⟨hyK, hyopen⟩
  exact upperHalfSpace_inter_halfSpaceSupportBoxOpenPart_subset
    (n := n) (a := a) (b := b) ha0 ⟨hKhalf hyK, hyopen⟩

/-- Subordination to the ambient-open part becomes support-box control after
intersecting with a carrier contained in the coordinate half-space. -/
theorem inter_subset_halfSpaceSupportBox_of_inter_subset_openPart
    {K S : Set (Fin (n + 1) → Real)}
    {a b : Fin (n + 1) → Real}
    (hKhalf : K ⊆ upperHalfSpace n) (ha0 : a 0 = 0)
    (hSopen :
      S ∩ K ⊆ halfSpaceSupportBoxOpenPart (n := n) a b) :
    S ∩ K ⊆ halfSpaceSupportBox a b := by
  rintro y hy
  exact upperHalfSpace_inter_halfSpaceSupportBoxOpenPart_subset
    (n := n) (a := a) (b := b) ha0
    ⟨hKhalf hy.2, hSopen hy⟩

end PureRelativeOpen

section FiniteCoverRelativeOpen

variable {n : Nat}
variable {K W : Set (Fin (n + 1) → Real)}
variable {Piece : Type*}

namespace FiniteHalfSpaceBoxCover

/-- The ambient-open set attached to one selected finite half-space box. -/
def openPart
    (D : FiniteHalfSpaceBoxCover (n := n) K W Piece) (q : Piece) :
    Set (Fin (n + 1) → Real) :=
  halfSpaceSupportBoxOpenPart (n := n) (D.lowerCorner q) (D.upperCorner q)

/-- The open cover member attached to an active finite-cover label. -/
def activeOpenSet
    (D : FiniteHalfSpaceBoxCover (n := n) K W Piece)
    (q : {q // q ∈ D.activePieces}) :
    Set (Fin (n + 1) → Real) :=
  D.openPart q.1

/-- Each selected ambient-open part is open. -/
theorem isOpen_openPart
    (D : FiniteHalfSpaceBoxCover (n := n) K W Piece) (q : Piece) :
    IsOpen (D.openPart q) := by
  simpa [openPart] using
    isOpen_halfSpaceSupportBoxOpenPart
      (n := n) (D.lowerCorner q) (D.upperCorner q)

/-- Active open-cover members are open. -/
theorem isOpen_activeOpenSet
    (D : FiniteHalfSpaceBoxCover (n := n) K W Piece)
    (q : {q // q ∈ D.activePieces}) :
    IsOpen (D.activeOpenSet q) := by
  simpa [activeOpenSet] using D.isOpen_openPart q.1

/-- A selected half-space support box lies in its ambient-open part. -/
theorem sourceBox_subset_openPart
    (D : FiniteHalfSpaceBoxCover (n := n) K W Piece) (q : Piece) :
    D.sourceBox q ⊆ D.openPart q := by
  simpa [sourceBox, openPart] using
    halfSpaceSupportBox_subset_halfSpaceSupportBoxOpenPart
      (n := n) (D.lowerCorner q) (D.upperCorner q)

/-- On the coordinate half-space, an active ambient-open part lands back in its
selected half-space support box. -/
theorem upperHalfSpace_inter_openPart_subset_sourceBox
    (D : FiniteHalfSpaceBoxCover (n := n) K W Piece)
    {q : Piece} (hq : q ∈ D.activePieces) :
    upperHalfSpace n ∩ D.openPart q ⊆ D.sourceBox q := by
  simpa [sourceBox, openPart] using
    upperHalfSpace_inter_halfSpaceSupportBoxOpenPart_subset
      (n := n) (a := D.lowerCorner q) (b := D.upperCorner q)
      (D.lowerCorner_zero q hq)

/-- Intersecting a half-space-contained carrier with an active open part gives
the selected support box. -/
theorem carrier_inter_openPart_subset_sourceBox
    (D : FiniteHalfSpaceBoxCover (n := n) K W Piece)
    (hKhalf : K ⊆ upperHalfSpace n)
    {q : Piece} (hq : q ∈ D.activePieces) :
    K ∩ D.openPart q ⊆ D.sourceBox q := by
  rintro y ⟨hyK, hyopen⟩
  exact D.upperHalfSpace_inter_openPart_subset_sourceBox hq
    ⟨hKhalf hyK, hyopen⟩

/-- Support control into an active ambient-open part becomes support control
inside the selected half-space support box. -/
theorem inter_subset_sourceBox_of_inter_subset_openPart
    (D : FiniteHalfSpaceBoxCover (n := n) K W Piece)
    (hKhalf : K ⊆ upperHalfSpace n)
    {S : Set (Fin (n + 1) → Real)} {q : Piece}
    (hq : q ∈ D.activePieces)
    (hSopen : S ∩ K ⊆ D.openPart q) :
    S ∩ K ⊆ D.sourceBox q := by
  rintro y hy
  exact D.upperHalfSpace_inter_openPart_subset_sourceBox hq
    ⟨hKhalf hy.2, hSopen hy⟩

/-- `tsupport` specialization of
`inter_subset_sourceBox_of_inter_subset_openPart`, matching the output of
support-controlled partitions of unity. -/
theorem tsupport_inter_carrier_subset_sourceBox_of_subset_openPart
    (D : FiniteHalfSpaceBoxCover (n := n) K W Piece)
    (hKhalf : K ⊆ upperHalfSpace n)
    {E : Type*} [Zero E]
    {f : (Fin (n + 1) → Real) → E} {q : Piece}
    (hq : q ∈ D.activePieces)
    (hfopen : tsupport f ∩ K ⊆ D.openPart q) :
    tsupport f ∩ K ⊆ D.sourceBox q :=
  D.inter_subset_sourceBox_of_inter_subset_openPart hKhalf hq hfopen

/-- The selected ambient-open parts cover the carrier. -/
theorem carrier_subset_iUnion_openPart
    (D : FiniteHalfSpaceBoxCover (n := n) K W Piece) :
    K ⊆ ⋃ q : {q // q ∈ D.activePieces}, D.openPart q.1 := by
  intro x hx
  rcases mem_iUnion.1 (D.carrier_subset_iUnion hx) with ⟨q, hxq⟩
  exact mem_iUnion.2 ⟨q, D.sourceBox_subset_openPart q.1 hxq⟩

/-- Same cover statement written with `activeOpenSet`, the shape consumed most
directly by finite-index partition constructors. -/
theorem carrier_subset_iUnion_activeOpenSet
    (D : FiniteHalfSpaceBoxCover (n := n) K W Piece) :
    K ⊆ ⋃ q : {q // q ∈ D.activePieces}, D.activeOpenSet q := by
  simpa [activeOpenSet] using D.carrier_subset_iUnion_openPart

end FiniteHalfSpaceBoxCover

end FiniteCoverRelativeOpen

section CoverIndexedRelativeOpen

universe uH uM uPiece

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable
    {coordCarrier ambient :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real)}
variable {Piece : {x : M // x ∈ C.boundaryCenters} → Type uPiece}

namespace CoverIndexedFiniteHalfSpaceBoxCover

/-- Coordinate ambient-open part attached to one active refined boundary box. -/
def openPart
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (i : {x : M // x ∈ C.boundaryCenters}) (q : Piece i) :
    Set (Fin (n + 1) → Real) :=
  (D.cover i).openPart q

/-- Active open-cover set for one cover-indexed boundary chart. -/
def activeOpenSet
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (i : {x : M // x ∈ C.boundaryCenters})
    (q : {q // q ∈ D.activePieces i}) :
    Set (Fin (n + 1) → Real) :=
  D.openPart i q.1

/-- Each cover-indexed selected open part is ambient-open. -/
theorem isOpen_openPart
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (i : {x : M // x ∈ C.boundaryCenters}) (q : Piece i) :
    IsOpen (D.openPart i q) := by
  simpa [openPart] using (D.cover i).isOpen_openPart q

/-- Each active cover-indexed open-cover member is ambient-open. -/
theorem isOpen_activeOpenSet
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (i : {x : M // x ∈ C.boundaryCenters})
    (q : {q // q ∈ D.activePieces i}) :
    IsOpen (D.activeOpenSet i q) := by
  simpa [activeOpenSet] using D.isOpen_openPart i q.1

/-- The selected ambient-open parts cover each coordinate carrier. -/
theorem carrier_subset_iUnion_openPart
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    coordCarrier i ⊆ ⋃ q : {q // q ∈ D.activePieces i}, D.openPart i q.1 := by
  simpa [openPart] using (D.cover i).carrier_subset_iUnion_openPart

/-- Same per-index cover statement written with `activeOpenSet`. -/
theorem carrier_subset_iUnion_activeOpenSet
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    coordCarrier i ⊆ ⋃ q : {q // q ∈ D.activePieces i}, D.activeOpenSet i q := by
  simpa [activeOpenSet] using D.carrier_subset_iUnion_openPart i

/-- Per-index open-part support control descends to the corresponding selected
half-space support box, provided the coordinate carrier lies in the upper
half-space. -/
theorem inter_subset_sourceBox_of_inter_subset_openPart
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (hhalf :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        coordCarrier i ⊆ upperHalfSpace n)
    (i : {x : M // x ∈ C.boundaryCenters})
    {S : Set (Fin (n + 1) → Real)} {q : Piece i}
    (hq : q ∈ D.activePieces i)
    (hSopen : S ∩ coordCarrier i ⊆ D.openPart i q) :
    S ∩ coordCarrier i ⊆
      halfSpaceSupportBox (D.lowerCorner i q) (D.upperCorner i q) := by
  simpa [openPart, lowerCorner, upperCorner,
    FiniteHalfSpaceBoxCover.sourceBox] using
    (D.cover i).inter_subset_sourceBox_of_inter_subset_openPart
      (hhalf i) hq hSopen

/-- `tsupport` specialization for cover-indexed smooth partition refinements:
subordination to an active ambient-open part gives the support-box containment
needed by the half-space local Stokes input. -/
theorem tsupport_inter_carrier_subset_halfSpaceSupportBox_of_subset_openPart
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (hhalf :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        coordCarrier i ⊆ upperHalfSpace n)
    (i : {x : M // x ∈ C.boundaryCenters})
    {E : Type*} [Zero E]
    {f : (Fin (n + 1) → Real) → E} {q : Piece i}
    (hq : q ∈ D.activePieces i)
    (hfopen : tsupport f ∩ coordCarrier i ⊆ D.openPart i q) :
    tsupport f ∩ coordCarrier i ⊆
      halfSpaceSupportBox (D.lowerCorner i q) (D.upperCorner i q) :=
  D.inter_subset_sourceBox_of_inter_subset_openPart hhalf i hq hfopen

end CoverIndexedFiniteHalfSpaceBoxCover

end CoverIndexedRelativeOpen

end Stokes

end
