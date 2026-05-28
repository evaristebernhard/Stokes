import Stokes.BoundaryChart.BoundaryOpenBoxSelection
import Stokes.Global.CoverIndexedZeroCompactFiniteHalfSpaceCover
import Stokes.Global.CoverIndexedZeroCompactAmbientThickening

/-!
# Collar box selection for compact zero Stokes

This file supplies the honest pointwise input for finite half-space box covers.

An arbitrary ambient open set around an interior point of the closed half-space
does not contain a half-space box with lower normal corner `0`: such a box also
contains the vertical segment down to the boundary face.  The useful true
hypothesis is a collar/prism containment.  We record that containment explicitly
and feed it to the existing finite-cover constructor.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section PureHalfSpaceCollar

variable {n : Nat}

/-- Lower corner of the closed collar prism based at the boundary face below
`x`, with tangential radius `eps`. -/
def halfSpaceCollarLower
    (x : Fin (n + 1) → Real) (eps : Real) : Fin (n + 1) → Real :=
  Fin.cases (0 : Real) (fun i : Fin n => x i.succ - eps)

/-- Upper corner of the closed collar prism based at the boundary face below
`x`, with tangential and normal buffer `eps`. -/
def halfSpaceCollarUpper
    (x : Fin (n + 1) → Real) (eps : Real) : Fin (n + 1) → Real :=
  Fin.cases (x 0 + eps) (fun i : Fin n => x i.succ + eps)

/-- The closed collar prism below and around `x`: normal coordinate ranges from
`0` to `x 0 + eps`, and tangential coordinates range between
`x_i - eps` and `x_i + eps`. -/
def halfSpaceCollarPrism
    (x : Fin (n + 1) → Real) (eps : Real) : Set (Fin (n + 1) → Real) :=
  Icc (halfSpaceCollarLower (n := n) x eps)
    (halfSpaceCollarUpper (n := n) x eps)

@[simp]
theorem halfSpaceCollarLower_zero
    (x : Fin (n + 1) → Real) (eps : Real) :
    halfSpaceCollarLower (n := n) x eps 0 = 0 := by
  rfl

@[simp]
theorem halfSpaceCollarUpper_zero
    (x : Fin (n + 1) → Real) (eps : Real) :
    halfSpaceCollarUpper (n := n) x eps 0 = x 0 + eps := by
  rfl

@[simp]
theorem halfSpaceCollarLower_succ
    (x : Fin (n + 1) → Real) (eps : Real) (i : Fin n) :
    halfSpaceCollarLower (n := n) x eps i.succ = x i.succ - eps := by
  rfl

@[simp]
theorem halfSpaceCollarUpper_succ
    (x : Fin (n + 1) → Real) (eps : Real) (i : Fin n) :
    halfSpaceCollarUpper (n := n) x eps i.succ = x i.succ + eps := by
  rfl

/-- The collar lower corner is below the upper corner when `x` lies in the
closed upper half-space and the collar radius is positive. -/
theorem halfSpaceCollarLower_le_upper
    {x : Fin (n + 1) → Real} {eps : Real}
    (hxhalf : x ∈ upperHalfSpace n) (heps : 0 < eps) :
    halfSpaceCollarLower (n := n) x eps ≤
      halfSpaceCollarUpper (n := n) x eps := by
  intro j
  refine Fin.cases ?_ ?_ j
  · have hx0 : 0 ≤ x 0 := by
      simpa [upperHalfSpace] using hxhalf
    simp [halfSpaceCollarLower, halfSpaceCollarUpper]
    linarith
  · intro i
    simp [halfSpaceCollarLower, halfSpaceCollarUpper]
    linarith

/-- The center point `x` lies in its half-space support box whenever `x` lies
in the closed upper half-space and the collar radius is positive. -/
theorem mem_halfSpaceSupportBox_halfSpaceCollar
    {x : Fin (n + 1) → Real} {eps : Real}
    (hxhalf : x ∈ upperHalfSpace n) (heps : 0 < eps) :
    x ∈ halfSpaceSupportBox
      (halfSpaceCollarLower (n := n) x eps)
      (halfSpaceCollarUpper (n := n) x eps) := by
  have hx0 : 0 ≤ x 0 := by
    simpa [upperHalfSpace] using hxhalf
  refine ⟨?_, ?_, ?_⟩
  · simpa [halfSpaceCollarLower] using hx0
  · simp [halfSpaceCollarUpper]
    linarith
  · intro i
    constructor <;> simp [halfSpaceCollarLower, halfSpaceCollarUpper] <;>
      linarith

/-- Pointwise collar-prism selection of a half-space support box.

The explicit collar hypothesis is the essential extra geometric input: the
closed prism below `x` has to be contained in the ambient set `W`.  No claim is
made that an arbitrary open neighborhood supplies this prism. -/
theorem exists_halfSpaceSupportBox_subset_of_collar_prism
    {W : Set (Fin (n + 1) → Real)} {x : Fin (n + 1) → Real} {eps : Real}
    (hxhalf : x ∈ upperHalfSpace n) (heps : 0 < eps)
    (hprism : halfSpaceCollarPrism (n := n) x eps ⊆ W) :
    ∃ a b : Fin (n + 1) → Real,
      a 0 = 0 ∧ a ≤ b ∧ x ∈ halfSpaceSupportBox a b ∧ Icc a b ⊆ W := by
  refine ⟨halfSpaceCollarLower (n := n) x eps,
    halfSpaceCollarUpper (n := n) x eps, ?_, ?_, ?_, ?_⟩
  · simp
  · exact halfSpaceCollarLower_le_upper (n := n) hxhalf heps
  · exact mem_halfSpaceSupportBox_halfSpaceCollar (n := n) hxhalf heps
  · simpa [halfSpaceCollarPrism] using hprism

/-- A pointwise family of collar prisms over a compact coordinate carrier
selects a finite half-space box cover. -/
def finiteHalfSpaceBoxCoverOfCollar
    {K W : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hKhalf : K ⊆ upperHalfSpace n)
    (hcollar :
      ∀ x ∈ K, ∃ eps : Real,
        0 < eps ∧ halfSpaceCollarPrism (n := n) x eps ⊆ W) :
    FiniteHalfSpaceBoxCover
      (n := n) K W (Fin (n + 1) → Real) :=
  finiteHalfSpaceBoxCoverOfPointwise
    (n := n) (K := K) (W := W) hK hKhalf
    (by
      intro x hx
      rcases hcollar x hx with ⟨eps, heps, hprism⟩
      exact
        exists_halfSpaceSupportBox_subset_of_collar_prism
          (n := n) (x := x) (W := W) (eps := eps)
          (hKhalf hx) heps hprism)

/-- Active centers selected by the collar finite-cover constructor remain in
the carrier. -/
theorem finiteHalfSpaceBoxCoverOfCollar_active_subset
    {K W : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hKhalf : K ⊆ upperHalfSpace n)
    (hcollar :
      ∀ x ∈ K, ∃ eps : Real,
        0 < eps ∧ halfSpaceCollarPrism (n := n) x eps ⊆ W) :
    ∀ x ∈
      (finiteHalfSpaceBoxCoverOfCollar
        (n := n) hK hKhalf hcollar).activePieces, x ∈ K := by
  simpa [finiteHalfSpaceBoxCoverOfCollar] using
    (finiteHalfSpaceBoxCoverOfPointwise_active_subset
      (n := n) (K := K) (W := W) hK hKhalf
      (by
        intro x hx
        rcases hcollar x hx with ⟨eps, heps, hprism⟩
        exact
          exists_halfSpaceSupportBox_subset_of_collar_prism
            (n := n) (x := x) (W := W) (eps := eps)
            (hKhalf hx) heps hprism))

end PureHalfSpaceCollar

section CoverIndexedBoundaryFamily

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}

/-- Cover-indexed finite half-space covers selected from pointwise collar
prisms in each boundary chart coordinate carrier. -/
def coverIndexedFiniteHalfSpaceBoxCoverOfCollar
    (coordCarrier ambient :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (hcompact :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsCompact (coordCarrier i))
    (hhalf :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        coordCarrier i ⊆ upperHalfSpace n)
    (hcollar :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ∀ x ∈ coordCarrier i, ∃ eps : Real,
          0 < eps ∧ halfSpaceCollarPrism (n := n) x eps ⊆ ambient i) :
    CoverIndexedFiniteHalfSpaceBoxCover
      (I := I) (K := K) C coordCarrier ambient
      (fun _ => Fin (n + 1) → Real) :=
  coverIndexedFiniteHalfSpaceBoxCoverOfPointwise
    (I := I) (K := K) (C := C)
    coordCarrier ambient hcompact hhalf
    (by
      intro i x hx
      rcases hcollar i x hx with ⟨eps, heps, hprism⟩
      exact
        exists_halfSpaceSupportBox_subset_of_collar_prism
          (n := n) (x := x) (W := ambient i) (eps := eps)
          (hhalf i hx) heps hprism)

/-- Active centers selected by the cover-indexed collar constructor remain in
their coordinate carriers. -/
theorem coverIndexedFiniteHalfSpaceBoxCoverOfCollar_active_subset
    (coordCarrier ambient :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (hcompact :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsCompact (coordCarrier i))
    (hhalf :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        coordCarrier i ⊆ upperHalfSpace n)
    (hcollar :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ∀ x ∈ coordCarrier i, ∃ eps : Real,
          0 < eps ∧ halfSpaceCollarPrism (n := n) x eps ⊆ ambient i)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ∀ x ∈
      ((coverIndexedFiniteHalfSpaceBoxCoverOfCollar
        (I := I) (K := K) (C := C)
        coordCarrier ambient hcompact hhalf hcollar).cover i).activePieces,
      x ∈ coordCarrier i := by
  simpa [coverIndexedFiniteHalfSpaceBoxCoverOfCollar] using
    (coverIndexedFiniteHalfSpaceBoxCoverOfPointwise_active_subset
      (I := I) (K := K) (C := C)
      coordCarrier ambient hcompact hhalf
      (by
        intro i x hx
        rcases hcollar i x hx with ⟨eps, heps, hprism⟩
        exact
          exists_halfSpaceSupportBox_subset_of_collar_prism
            (n := n) (x := x) (W := ambient i) (eps := eps)
            (hhalf i hx) heps hprism)
      i)

end CoverIndexedBoundaryFamily

end Stokes

end
