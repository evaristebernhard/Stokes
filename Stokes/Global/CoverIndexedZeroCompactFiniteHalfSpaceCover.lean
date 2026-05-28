import Stokes.Global.CoverIndexedZeroCompactSourceInnerOuterExistence
import Stokes.BoundaryChart.BoundaryOpenBoxSelection

/-!
# Finite half-space box covers for compact zero Stokes

This file packages the genuine compactness step needed before refining a
boundary chart piece into smaller half-space boxes.

The key point is topological: `halfSpaceSupportBox a b` is not generally open
in the ambient coordinate space at boundary points, but when `a 0 = 0` it is a
neighborhood relative to the closed half-space.  Therefore compactness can be
used through `IsCompact.elim_nhdsWithin_subcover`, provided the compact carrier
already lies in the half-space.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section PureHalfSpaceCover

variable {n : Nat}

/-- The ambient-open part of a half-space support box.  Intersecting this set
with the closed upper half-space gives `halfSpaceSupportBox` when the lower
normal coordinate is `0`. -/
def halfSpaceSupportBoxOpenPart
    (a b : Fin (n + 1) → Real) : Set (Fin (n + 1) → Real) :=
  {y | y 0 < b 0 ∧
    ∀ i : Fin n, a i.succ < y i.succ ∧ y i.succ < b i.succ}

/-- The open part of a half-space support box is ambient-open. -/
theorem isOpen_halfSpaceSupportBoxOpenPart
    (a b : Fin (n + 1) → Real) :
    IsOpen (halfSpaceSupportBoxOpenPart (n := n) a b) := by
  unfold halfSpaceSupportBoxOpenPart
  refine
    (isOpen_lt (continuous_apply (0 : Fin (n + 1))) continuous_const).inter ?_
  have htail :
      IsOpen
        {y : Fin (n + 1) → Real |
          ∀ i : Fin n, a i.succ < y i.succ ∧ y i.succ < b i.succ} := by
    simpa [setOf_forall] using
      (isOpen_iInter_of_finite (ι := Fin n) fun i =>
        (show
          IsOpen
            {y : Fin (n + 1) → Real |
              a i.succ < y i.succ ∧ y i.succ < b i.succ} from
          (isOpen_lt
            (show Continuous (fun _ : Fin (n + 1) → Real => a i.succ) from
              continuous_const)
            (continuous_apply i.succ)).inter
            (isOpen_lt
              (continuous_apply i.succ)
              (show Continuous (fun _ : Fin (n + 1) → Real => b i.succ) from
                continuous_const))))
  simpa using htail

/-- A half-space support box is contained in any ambient set containing its
closed box. -/
theorem halfSpaceSupportBox_subset_of_Icc_subset
    {a b : Fin (n + 1) → Real} {W : Set (Fin (n + 1) → Real)}
    (_ha0 : a 0 = 0) (hIcc : Icc a b ⊆ W) :
    halfSpaceSupportBox a b ⊆ W :=
  (halfSpaceSupportBox_subset_Icc a b).trans hIcc

/-- With lower normal corner `0`, a half-space support box is a neighborhood
relative to the coordinate half-space of each of its points. -/
theorem halfSpaceSupportBox_mem_nhdsWithin_upperHalfSpace_of_mem
    {a b : Fin (n + 1) → Real} {x : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hx : x ∈ halfSpaceSupportBox a b) :
    halfSpaceSupportBox a b ∈ 𝓝[upperHalfSpace n] x := by
  refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ?_
  refine ⟨halfSpaceSupportBoxOpenPart (n := n) a b, ?_, ?_⟩
  · exact (isOpen_halfSpaceSupportBoxOpenPart (n := n) a b).mem_nhds
      ⟨hx.2.1, hx.2.2⟩
  · intro y hy
    refine ⟨?_, ?_, ?_⟩
    · simpa [upperHalfSpace, ha0] using hy.2
    · exact hy.1.1
    · exact hy.1.2

/-- If a compact carrier lies in the coordinate half-space, then any selected
half-space support box around a carrier point is a neighborhood relative to the
carrier. -/
theorem halfSpaceSupportBox_mem_nhdsWithin_of_subset_upperHalfSpace
    {K : Set (Fin (n + 1) → Real)}
    {a b : Fin (n + 1) → Real} {x : Fin (n + 1) → Real}
    (hKhalf : K ⊆ upperHalfSpace n)
    (ha0 : a 0 = 0) (hx : x ∈ halfSpaceSupportBox a b) :
    halfSpaceSupportBox a b ∈ 𝓝[K] x :=
  nhdsWithin_mono x hKhalf
    (halfSpaceSupportBox_mem_nhdsWithin_upperHalfSpace_of_mem
      (n := n) ha0 hx)

/-- A finite family of half-space support boxes covering a compact coordinate
carrier, with each closed box contained in a chosen ambient set `W`. -/
structure FiniteHalfSpaceBoxCover
    (K W : Set (Fin (n + 1) → Real)) (Piece : Type*) where
  /-- Finite labels for the selected source boxes. -/
  activePieces : Finset Piece
  /-- Lower corner of each selected half-space box. -/
  lowerCorner : Piece → Fin (n + 1) → Real
  /-- Upper corner of each selected half-space box. -/
  upperCorner : Piece → Fin (n + 1) → Real
  /-- Active lower corners lie on the true boundary hyperplane. -/
  lowerCorner_zero :
    ∀ q, q ∈ activePieces → lowerCorner q 0 = 0
  /-- Active source boxes have ordered corners. -/
  lower_le_upper :
    ∀ q, q ∈ activePieces → lowerCorner q ≤ upperCorner q
  /-- The compact carrier is covered by the active half-space support boxes. -/
  carrier_subset_iUnion :
    K ⊆ ⋃ q : {q // q ∈ activePieces},
      halfSpaceSupportBox (lowerCorner q.1) (upperCorner q.1)
  /-- Each active closed box lies inside the selected ambient set. -/
  Icc_subset_ambient :
    ∀ q, q ∈ activePieces → Icc (lowerCorner q) (upperCorner q) ⊆ W

namespace FiniteHalfSpaceBoxCover

variable {K W : Set (Fin (n + 1) → Real)} {Piece : Type*}

/-- The selected support box for one finite-cover label. -/
def sourceBox (D : FiniteHalfSpaceBoxCover (n := n) K W Piece) (q : Piece) :
    Set (Fin (n + 1) → Real) :=
  halfSpaceSupportBox (D.lowerCorner q) (D.upperCorner q)

/-- The selected closed ambient box for one finite-cover label. -/
def closedBox (D : FiniteHalfSpaceBoxCover (n := n) K W Piece) (q : Piece) :
    Set (Fin (n + 1) → Real) :=
  Icc (D.lowerCorner q) (D.upperCorner q)

/-- Every carrier point lies in some active selected half-space box. -/
theorem exists_active_mem_sourceBox
    (D : FiniteHalfSpaceBoxCover (n := n) K W Piece)
    {x : Fin (n + 1) → Real} (hx : x ∈ K) :
    ∃ q : Piece, q ∈ D.activePieces ∧ x ∈ D.sourceBox q := by
  rcases Set.mem_iUnion.mp (D.carrier_subset_iUnion hx) with ⟨q, hxq⟩
  exact ⟨q.1, q.2, hxq⟩

/-- Active half-space support boxes lie in the ambient set because their closed
boxes do. -/
theorem sourceBox_subset_ambient
    (D : FiniteHalfSpaceBoxCover (n := n) K W Piece)
    {q : Piece} (hq : q ∈ D.activePieces) :
    D.sourceBox q ⊆ W :=
  halfSpaceSupportBox_subset_of_Icc_subset
    (n := n) (D.lowerCorner_zero q hq) (D.Icc_subset_ambient q hq)

/-- The carrier is contained in the ambient set covered by the selected boxes. -/
theorem carrier_subset_ambient
    (D : FiniteHalfSpaceBoxCover (n := n) K W Piece) :
    K ⊆ W := by
  intro x hx
  rcases D.exists_active_mem_sourceBox hx with ⟨q, hq, hxq⟩
  exact D.sourceBox_subset_ambient hq hxq

/-- Constructor from one already selected half-space box. -/
def singleton
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hKbox : K ⊆ halfSpaceSupportBox a b)
    (hIcc : Icc a b ⊆ W) :
    FiniteHalfSpaceBoxCover (n := n) K W PUnit where
  activePieces := {PUnit.unit}
  lowerCorner := fun _ => a
  upperCorner := fun _ => b
  lowerCorner_zero := by
    intro q _hq
    exact ha0
  lower_le_upper := by
    intro q _hq
    exact hle
  carrier_subset_iUnion := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨PUnit.unit, by simp⟩, hKbox hx⟩
  Icc_subset_ambient := by
    intro q hq
    exact hIcc

end FiniteHalfSpaceBoxCover

/-- If each carrier point has a half-space box that is relatively local to the
carrier and whose closed box lies in `W`, compactness selects finitely many of
them.

The pointwise hypothesis is the honest local geometric input.  It is exactly
what later collar/local-openness arguments must prove. -/
theorem exists_finiteHalfSpaceBoxCover_of_pointwise
    {K W : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hKhalf : K ⊆ upperHalfSpace n)
    (hpoint :
      ∀ x ∈ K, ∃ a b : Fin (n + 1) → Real,
        a 0 = 0 ∧ a ≤ b ∧ x ∈ halfSpaceSupportBox a b ∧
          Icc a b ⊆ W) :
    ∃ D : FiniteHalfSpaceBoxCover
        (n := n) K W (Fin (n + 1) → Real),
      ∀ x ∈ D.activePieces, x ∈ K := by
  classical
  choose lower upper hzero hle hxbox hIcc using hpoint
  let lower' : (Fin (n + 1) → Real) → Fin (n + 1) → Real :=
    fun x => if hx : x ∈ K then lower x hx else 0
  let upper' : (Fin (n + 1) → Real) → Fin (n + 1) → Real :=
    fun x => if hx : x ∈ K then upper x hx else 0
  have hzero' : ∀ x ∈ K, lower' x 0 = 0 := by
    intro x hx
    simpa [lower', hx] using hzero x hx
  have hle' : ∀ x ∈ K, lower' x ≤ upper' x := by
    intro x hx
    simpa [lower', upper', hx] using hle x hx
  have hxbox' : ∀ x ∈ K, x ∈ halfSpaceSupportBox (lower' x) (upper' x) := by
    intro x hx
    simpa [lower', upper', hx] using hxbox x hx
  have hIcc' : ∀ x ∈ K, Icc (lower' x) (upper' x) ⊆ W := by
    intro x hx
    simpa [lower', upper', hx] using hIcc x hx
  have hboxWithin :
      ∀ x ∈ K,
        halfSpaceSupportBox (lower' x) (upper' x) ∈ 𝓝[K] x := by
    intro x hx
    exact
      halfSpaceSupportBox_mem_nhdsWithin_of_subset_upperHalfSpace
        (n := n) (K := K) hKhalf (hzero' x hx) (hxbox' x hx)
  obtain ⟨centers, hcentersK, hcover⟩ :=
    hK.elim_nhdsWithin_subcover
      (fun x => halfSpaceSupportBox (lower' x) (upper' x))
      hboxWithin
  let D : FiniteHalfSpaceBoxCover
      (n := n) K W (Fin (n + 1) → Real) :=
    { activePieces := centers
      lowerCorner := lower'
      upperCorner := upper'
      lowerCorner_zero := by
        intro q hq
        exact hzero' q (hcentersK q hq)
      lower_le_upper := by
        intro q hq
        exact hle' q (hcentersK q hq)
      carrier_subset_iUnion := by
        intro x hx
        rcases Set.mem_iUnion.mp (hcover hx) with ⟨q, hxqUnion⟩
        rcases Set.mem_iUnion.mp hxqUnion with ⟨hq, hxq⟩
        exact Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hxq⟩
      Icc_subset_ambient := by
        intro q hq
        exact hIcc' q (hcentersK q hq) }
  exact ⟨D, by simpa [D] using hcentersK⟩

/-- A noncomputable selected finite half-space box cover from pointwise local
box data. -/
def finiteHalfSpaceBoxCoverOfPointwise
    {K W : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hKhalf : K ⊆ upperHalfSpace n)
    (hpoint :
      ∀ x ∈ K, ∃ a b : Fin (n + 1) → Real,
        a 0 = 0 ∧ a ≤ b ∧ x ∈ halfSpaceSupportBox a b ∧
          Icc a b ⊆ W) :
    FiniteHalfSpaceBoxCover
      (n := n) K W (Fin (n + 1) → Real) :=
  Classical.choose
    (exists_finiteHalfSpaceBoxCover_of_pointwise
      (n := n) hK hKhalf hpoint)

/-- The selected finite cover keeps its active centers inside the carrier. -/
theorem finiteHalfSpaceBoxCoverOfPointwise_active_subset
    {K W : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hKhalf : K ⊆ upperHalfSpace n)
    (hpoint :
      ∀ x ∈ K, ∃ a b : Fin (n + 1) → Real,
        a 0 = 0 ∧ a ≤ b ∧ x ∈ halfSpaceSupportBox a b ∧
          Icc a b ⊆ W) :
    ∀ x ∈
      (finiteHalfSpaceBoxCoverOfPointwise
        (n := n) hK hKhalf hpoint).activePieces, x ∈ K :=
  Classical.choose_spec
    (exists_finiteHalfSpaceBoxCover_of_pointwise
      (n := n) hK hKhalf hpoint)

end PureHalfSpaceCover

section CoverIndexedBoundaryFamily

universe uH uM uPiece

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}

/-- Cover-indexed family of finite half-space box covers.

`coordCarrier i` is the compact coordinate carrier for the boundary chart
piece indexed by `i`; `ambient i` is the source-side open/preimage region into
which the closed boxes must fit. -/
structure CoverIndexedFiniteHalfSpaceBoxCover
    (C : CompactSupportChartCoverSelection I K)
    (coordCarrier ambient :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (Piece : {x : M // x ∈ C.boundaryCenters} → Type uPiece) where
  /-- Per-boundary-index finite half-space box covers. -/
  cover :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      FiniteHalfSpaceBoxCover
        (n := n) (coordCarrier i) (ambient i) (Piece i)

namespace CoverIndexedFiniteHalfSpaceBoxCover

variable
    {coordCarrier ambient :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real)}
    {Piece : {x : M // x ∈ C.boundaryCenters} → Type uPiece}

/-- Active pieces for one boundary index. -/
def activePieces
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    Finset (Piece i) :=
  (D.cover i).activePieces

/-- Lower corner of one selected finite-cover box. -/
def lowerCorner
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (i : {x : M // x ∈ C.boundaryCenters}) (q : Piece i) :
    Fin (n + 1) → Real :=
  (D.cover i).lowerCorner q

/-- Upper corner of one selected finite-cover box. -/
def upperCorner
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (i : {x : M // x ∈ C.boundaryCenters}) (q : Piece i) :
    Fin (n + 1) → Real :=
  (D.cover i).upperCorner q

/-- Per-index carrier cover projection. -/
theorem carrier_subset_iUnion
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    coordCarrier i ⊆ ⋃ q : {q // q ∈ D.activePieces i},
      halfSpaceSupportBox (D.lowerCorner i q.1) (D.upperCorner i q.1) := by
  simpa [activePieces, lowerCorner, upperCorner] using
    (D.cover i).carrier_subset_iUnion

/-- Per-index closed-box containment projection. -/
theorem Icc_subset_ambient
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (i : {x : M // x ∈ C.boundaryCenters}) {q : Piece i}
    (hq : q ∈ D.activePieces i) :
    Icc (D.lowerCorner i q) (D.upperCorner i q) ⊆ ambient i := by
  simpa [activePieces, lowerCorner, upperCorner] using
    (D.cover i).Icc_subset_ambient q hq

/-- Per-index support-box containment in the ambient set. -/
theorem sourceBox_subset_ambient
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (i : {x : M // x ∈ C.boundaryCenters}) {q : Piece i}
    (hq : q ∈ D.activePieces i) :
    halfSpaceSupportBox (D.lowerCorner i q) (D.upperCorner i q) ⊆
      ambient i := by
  simpa [activePieces, lowerCorner, upperCorner] using
    (D.cover i).sourceBox_subset_ambient hq

/-- Build the cover-indexed family from already selected per-index covers. -/
def ofCovers
    (cover :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        FiniteHalfSpaceBoxCover
          (n := n) (coordCarrier i) (ambient i) (Piece i)) :
    CoverIndexedFiniteHalfSpaceBoxCover
      (I := I) (K := K) C coordCarrier ambient Piece where
  cover := cover

end CoverIndexedFiniteHalfSpaceBoxCover

/-- Cover-indexed finite half-space covers selected from pointwise local
half-space box data at every boundary index. -/
def coverIndexedFiniteHalfSpaceBoxCoverOfPointwise
    (coordCarrier ambient :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (hcompact :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsCompact (coordCarrier i))
    (hhalf :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        coordCarrier i ⊆ upperHalfSpace n)
    (hpoint :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ∀ x ∈ coordCarrier i,
          ∃ a b : Fin (n + 1) → Real,
            a 0 = 0 ∧ a ≤ b ∧ x ∈ halfSpaceSupportBox a b ∧
              Icc a b ⊆ ambient i) :
    CoverIndexedFiniteHalfSpaceBoxCover
      (I := I) (K := K) C coordCarrier ambient
      (fun _ => Fin (n + 1) → Real) where
  cover := fun i =>
    finiteHalfSpaceBoxCoverOfPointwise
      (n := n) (K := coordCarrier i) (W := ambient i)
      (hcompact i) (hhalf i) (hpoint i)

/-- Active centers selected by the cover-indexed pointwise constructor remain
inside the corresponding coordinate carrier. -/
theorem coverIndexedFiniteHalfSpaceBoxCoverOfPointwise_active_subset
    (coordCarrier ambient :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (hcompact :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsCompact (coordCarrier i))
    (hhalf :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        coordCarrier i ⊆ upperHalfSpace n)
    (hpoint :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ∀ x ∈ coordCarrier i,
          ∃ a b : Fin (n + 1) → Real,
            a 0 = 0 ∧ a ≤ b ∧ x ∈ halfSpaceSupportBox a b ∧
              Icc a b ⊆ ambient i)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ∀ x ∈
      ((coverIndexedFiniteHalfSpaceBoxCoverOfPointwise
        (I := I) (K := K) (C := C)
        coordCarrier ambient hcompact hhalf hpoint).cover i).activePieces,
      x ∈ coordCarrier i := by
  simpa [coverIndexedFiniteHalfSpaceBoxCoverOfPointwise] using
    (finiteHalfSpaceBoxCoverOfPointwise_active_subset
      (n := n) (K := coordCarrier i) (W := ambient i)
      (hcompact i) (hhalf i) (hpoint i))

end CoverIndexedBoundaryFamily

end Stokes

end
