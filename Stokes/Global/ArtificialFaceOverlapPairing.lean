import Stokes.Global.ArtificialFaceGeometry

/-!
# Overlap pairings for artificial faces

This file packages the common artificial-face cancellation pattern used by the
global Stokes assembly: paired artificial faces represent the same geometric
overlap face, but carry opposite orientation signs.  The geometric equality is
recorded as data, while the finite-sum cancellation is discharged by a reusable
involution lemma for signed/unsigned terms.
-/

noncomputable section

open scoped BigOperators

namespace Stokes

section FiniteInvolutionCancellation

variable {α : Type*}

/--
Finite-sum cancellation for terms split as `sign * unsigned`.

The involution preserves the finite index set, paired unsigned terms agree, and
paired signs add to zero.  Fixed points are allowed only when their signed term
has already vanished.
-/
theorem sum_sign_mul_cancel_of_involution
    (s : Finset α) (faceSign unsignedTerm : α → Real) (pair : α → α)
    (hunsigned_eq :
      ∀ a, a ∈ s → unsignedTerm a = unsignedTerm (pair a))
    (hsign_cancel :
      ∀ a, a ∈ s → faceSign a + faceSign (pair a) = 0)
    (hfixed_zero :
      ∀ a, a ∈ s → pair a = a → faceSign a * unsignedTerm a = 0)
    (hpair_mem : ∀ a, a ∈ s → pair a ∈ s)
    (hpair_involutive : ∀ a, a ∈ s → pair (pair a) = a) :
    (Finset.sum s fun a => faceSign a * unsignedTerm a) = 0 :=
  sum_pair_cancel_of_involution s (fun a => faceSign a * unsignedTerm a) pair
    (fun a ha => by
      change faceSign a * unsignedTerm a +
        faceSign (pair a) * unsignedTerm (pair a) = 0
      rw [← hunsigned_eq a ha, ← add_mul, hsign_cancel a ha, zero_mul])
    (fun a ha hnonzero hfix => hnonzero (hfixed_zero a ha hfix))
    hpair_mem hpair_involutive

/--
Finite-sum cancellation for `sign * unsigned` terms, stated with the paired sign
as the negative of the original sign.
-/
theorem sum_sign_mul_cancel_of_opposite_involution
    (s : Finset α) (faceSign unsignedTerm : α → Real) (pair : α → α)
    (hunsigned_eq :
      ∀ a, a ∈ s → unsignedTerm a = unsignedTerm (pair a))
    (hsign_opposite :
      ∀ a, a ∈ s → faceSign (pair a) = -faceSign a)
    (hfixed_zero :
      ∀ a, a ∈ s → pair a = a → faceSign a * unsignedTerm a = 0)
    (hpair_mem : ∀ a, a ∈ s → pair a ∈ s)
    (hpair_involutive : ∀ a, a ∈ s → pair (pair a) = a) :
    (Finset.sum s fun a => faceSign a * unsignedTerm a) = 0 :=
  sum_sign_mul_cancel_of_involution s faceSign unsignedTerm pair hunsigned_eq
    (fun a ha => by simp [hsign_opposite a ha])
    hfixed_zero hpair_mem hpair_involutive

/--
Fixed-point-free variant of `sum_sign_mul_cancel_of_involution`.
-/
theorem sum_sign_mul_cancel_of_fixedPointFree_involution
    (s : Finset α) (faceSign unsignedTerm : α → Real) (pair : α → α)
    (hunsigned_eq :
      ∀ a, a ∈ s → unsignedTerm a = unsignedTerm (pair a))
    (hsign_cancel :
      ∀ a, a ∈ s → faceSign a + faceSign (pair a) = 0)
    (hpair_ne_self : ∀ a, a ∈ s → pair a ≠ a)
    (hpair_mem : ∀ a, a ∈ s → pair a ∈ s)
    (hpair_involutive : ∀ a, a ∈ s → pair (pair a) = a) :
    (Finset.sum s fun a => faceSign a * unsignedTerm a) = 0 :=
  sum_sign_mul_cancel_of_involution s faceSign unsignedTerm pair hunsigned_eq
    hsign_cancel
    (fun a ha hfix => False.elim ((hpair_ne_self a ha) hfix))
    hpair_mem hpair_involutive

/--
Fixed-point-free variant of `sum_sign_mul_cancel_of_opposite_involution`.
-/
theorem sum_sign_mul_cancel_of_fixedPointFree_opposite_involution
    (s : Finset α) (faceSign unsignedTerm : α → Real) (pair : α → α)
    (hunsigned_eq :
      ∀ a, a ∈ s → unsignedTerm a = unsignedTerm (pair a))
    (hsign_opposite :
      ∀ a, a ∈ s → faceSign (pair a) = -faceSign a)
    (hpair_ne_self : ∀ a, a ∈ s → pair a ≠ a)
    (hpair_mem : ∀ a, a ∈ s → pair a ∈ s)
    (hpair_involutive : ∀ a, a ∈ s → pair (pair a) = a) :
    (Finset.sum s fun a => faceSign a * unsignedTerm a) = 0 :=
  sum_sign_mul_cancel_of_opposite_involution s faceSign unsignedTerm pair
    hunsigned_eq hsign_opposite
    (fun a ha hfix => False.elim ((hpair_ne_self a ha) hfix))
    hpair_mem hpair_involutive

end FiniteInvolutionCancellation

section ArtificialFaceOverlapPairing

universe c p f d g

variable {Chart : Type c} {InteriorPiece : Type p} {Face : Type f}
variable {FaceDimension : Type d} {Geometry : Type g}

/--
Artificial-face cancellation from overlap pairings.

This is the artificial-face specialization of
`sum_sign_mul_cancel_of_involution`: the signed face term is `faceSign` times an
unsigned contribution, paired unsigned contributions agree, and paired
orientation signs cancel.
-/
theorem artificialFace_sum_eq_zero_of_overlap_pairing
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (faceIndices : Chart → InteriorPiece → Finset Face)
    (faceSign unsignedFaceTerm : Chart → InteriorPiece → Face → Real)
    (pair :
      ArtificialFaceIndex Chart InteriorPiece Face →
        ArtificialFaceIndex Chart InteriorPiece Face)
    (hunsigned_eq :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        artificialFaceTerm unsignedFaceTerm q =
          artificialFaceTerm unsignedFaceTerm (pair q))
    (hsign_cancel :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        artificialFaceTerm faceSign q +
          artificialFaceTerm faceSign (pair q) = 0)
    (hfixed_zero :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair q = q →
          artificialFaceTerm faceSign q *
            artificialFaceTerm unsignedFaceTerm q = 0)
    (hpair_mem :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices)
    (hpair_involutive :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair (pair q) = q) :
    (Finset.sum activeCharts fun x =>
        Finset.sum (interiorPieces x) fun p =>
          Finset.sum (faceIndices x p) fun f =>
            faceSign x p f * unsignedFaceTerm x p f) = 0 := by
  rw [interiorBoundaryFace_sum_eq_indexSet_sum]
  simpa [artificialFaceTerm] using
    (sum_sign_mul_cancel_of_involution
      (artificialFaceIndexSet activeCharts interiorPieces faceIndices)
      (fun q => artificialFaceTerm faceSign q)
      (fun q => artificialFaceTerm unsignedFaceTerm q)
      pair hunsigned_eq hsign_cancel hfixed_zero hpair_mem hpair_involutive)

/--
Data package for the "same overlap face, opposite orientation" artificial-face
cancellation pattern.

The `overlapFace` field records the underlying common geometric face.  It is not
used algebraically by the finite-sum theorem, but keeping it as a field makes
the later geometric construction explicit and auditable.
-/
structure ArtificialFaceOverlapPairingData
    (Chart : Type c) (InteriorPiece : Type p) (Face : Type f)
    (FaceDimension : Type d) (Geometry : Type g) where
  /-- Finite chart labels whose interior pieces contribute artificial faces. -/
  activeCharts : Finset Chart
  /-- Interior pieces assigned to each chart. -/
  interiorPieces : Chart → Finset InteriorPiece
  /-- Artificial face labels assigned to an interior piece. -/
  faceIndices : Chart → InteriorPiece → Finset Face
  /-- Dimension or coordinate label of a face. -/
  faceDimension : Chart → InteriorPiece → Face → FaceDimension
  /-- The underlying artificial overlap face, forgetting orientation. -/
  overlapFace : Chart → InteriorPiece → Face → Geometry
  /-- Signed orientation factor of a face. -/
  faceSign : Chart → InteriorPiece → Face → Real
  /-- Unsigned integral or magnitude attached to a face. -/
  unsignedFaceTerm : Chart → InteriorPiece → Face → Real
  /-- Pairing of flattened artificial faces. -/
  pair :
    ArtificialFaceIndex Chart InteriorPiece Face →
      ArtificialFaceIndex Chart InteriorPiece Face
  /-- The pairing preserves the active flattened finite index set. -/
  pair_mem :
    ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      pair q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices
  /-- The pairing is an involution on the active flattened finite index set. -/
  pair_involutive :
    ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      pair (pair q) = q
  /-- Paired faces have the same recorded face dimension. -/
  paired_faceDimension_eq :
    ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      faceDimension q.1.1 q.1.2 q.2 =
        faceDimension (pair q).1.1 (pair q).1.2 (pair q).2
  /-- Paired faces represent the same underlying overlap face. -/
  paired_overlapFace_eq :
    ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      overlapFace q.1.1 q.1.2 q.2 =
        overlapFace (pair q).1.1 (pair q).1.2 (pair q).2
  /-- Paired faces have equal unsigned terms. -/
  paired_unsignedFaceTerm_eq :
    ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      artificialFaceTerm unsignedFaceTerm q =
        artificialFaceTerm unsignedFaceTerm (pair q)
  /-- Paired face orientation signs cancel. -/
  paired_orientation_cancel :
    ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      artificialFaceTerm faceSign q + artificialFaceTerm faceSign (pair q) = 0
  /-- Fixed artificial face terms are already zero. -/
  fixed_terms_zero :
    ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      pair q = q →
        artificialFaceTerm faceSign q * artificialFaceTerm unsignedFaceTerm q = 0

namespace ArtificialFaceOverlapPairingData

/-- The active flattened artificial-face index set carried by the package. -/
def indexSet
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry) :
    Finset (ArtificialFaceIndex Chart InteriorPiece Face) :=
  artificialFaceIndexSet D.activeCharts D.interiorPieces D.faceIndices

/-- The paired flattened artificial face. -/
def pairedFace
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) :
    ArtificialFaceIndex Chart InteriorPiece Face :=
  D.pair q

/-- The recorded face dimension of a flattened artificial face. -/
def dimension
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) : FaceDimension :=
  D.faceDimension q.1.1 q.1.2 q.2

/-- The recorded underlying overlap face of a flattened artificial face. -/
def geometry
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) : Geometry :=
  D.overlapFace q.1.1 q.1.2 q.2

/-- The recorded orientation sign of a flattened artificial face. -/
def sign
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) : Real :=
  artificialFaceTerm D.faceSign q

/-- The recorded unsigned face term of a flattened artificial face. -/
def unsignedTerm
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) : Real :=
  artificialFaceTerm D.unsignedFaceTerm q

/-- The signed face-term function induced by the sign/unsigned split. -/
def faceTerm
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry)
    (x : Chart) (p : InteriorPiece) (f : Face) : Real :=
  D.faceSign x p f * D.unsignedFaceTerm x p f

/-- The recorded signed face term of a flattened artificial face. -/
def term
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) : Real :=
  artificialFaceTerm D.faceTerm q

/-- Paired active faces have equal recorded dimensions. -/
theorem paired_dimension_eq
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry)
    {q : ArtificialFaceIndex Chart InteriorPiece Face} (hq : q ∈ D.indexSet) :
    D.dimension q = D.dimension (D.pairedFace q) :=
  D.paired_faceDimension_eq q hq

/-- Paired active faces have the same recorded overlap geometry. -/
theorem paired_geometry_eq
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry)
    {q : ArtificialFaceIndex Chart InteriorPiece Face} (hq : q ∈ D.indexSet) :
    D.geometry q = D.geometry (D.pairedFace q) :=
  D.paired_overlapFace_eq q hq

/-- The signed term decomposes as sign times unsigned term. -/
theorem term_eq_sign_mul_unsigned
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) :
    D.term q = D.sign q * D.unsignedTerm q := by
  rfl

/-- Paired active signed terms sum to zero. -/
theorem paired_terms_cancel
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry) :
    ∀ q, q ∈ D.indexSet → D.term q + D.term (D.pairedFace q) = 0 := by
  intro q hq
  have hunsigned : D.unsignedTerm q = D.unsignedTerm (D.pair q) := by
    simpa [unsignedTerm] using D.paired_unsignedFaceTerm_eq q hq
  have hsign : D.sign q + D.sign (D.pair q) = 0 := by
    simpa [sign] using D.paired_orientation_cancel q hq
  change D.sign q * D.unsignedTerm q +
      D.sign (D.pair q) * D.unsignedTerm (D.pair q) = 0
  rw [← hunsigned, ← add_mul, hsign, zero_mul]

/-- The recorded overlap pairing cancels the total nested face sum. -/
theorem faceSum_cancellation
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.interiorPieces x) fun p =>
          Finset.sum (D.faceIndices x p) fun f => D.faceTerm x p f) = 0 :=
  artificialFace_sum_eq_zero_of_overlap_pairing D.activeCharts D.interiorPieces
    D.faceIndices D.faceSign D.unsignedFaceTerm D.pair
    D.paired_unsignedFaceTerm_eq D.paired_orientation_cancel D.fixed_terms_zero
    D.pair_mem D.pair_involutive

/-- Forget the overlap-specific name and build the geometric face package. -/
def toArtificialFaceGeometryData
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry) :
    ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry
    where
  activeCharts := D.activeCharts
  interiorPieces := D.interiorPieces
  faceIndices := D.faceIndices
  faceDimension := D.faceDimension
  geometricFace := D.overlapFace
  faceSign := D.faceSign
  unsignedFaceTerm := D.unsignedFaceTerm
  faceTerm := D.faceTerm
  pair := D.pair
  pair_mem := D.pair_mem
  pair_involutive := D.pair_involutive
  paired_faceDimension_eq := D.paired_faceDimension_eq
  paired_geometricFace_eq := D.paired_overlapFace_eq
  faceTerm_eq_sign_mul := by
    intro q _hq
    rfl
  paired_unsignedFaceTerm_eq := D.paired_unsignedFaceTerm_eq
  paired_sign_cancel := D.paired_orientation_cancel
  fixed_terms_zero := by
    intro q hq hfix
    exact D.fixed_terms_zero q hq hfix

/-- The active index set is unchanged by forgetting the overlap-specific name. -/
theorem toArtificialFaceGeometryData_indexSet
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry) :
    D.toArtificialFaceGeometryData.indexSet = D.indexSet :=
  rfl

/-- The signed face term is unchanged by forgetting the overlap-specific name. -/
theorem toArtificialFaceGeometryData_term
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) :
    D.toArtificialFaceGeometryData.term q = D.term q :=
  rfl

/-- Forget the overlap fields and keep the algebraic artificial-face pairing. -/
def toArtificialFacePairingData
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry) :
    ArtificialFacePairingData Chart InteriorPiece Face :=
  D.toArtificialFaceGeometryData.toArtificialFacePairingData

/-- Forget overlap data all the way to the artificial-boundary package. -/
def toArtificialBoundaryCancellationData
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry) :
    ArtificialBoundaryCancellationData Chart InteriorPiece :=
  D.toArtificialFacePairingData.toArtificialBoundaryCancellationData

/--
Constructor from an explicit opposite-orientation statement.
-/
def ofOppositeOrientation
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (faceIndices : Chart → InteriorPiece → Finset Face)
    (faceDimension : Chart → InteriorPiece → Face → FaceDimension)
    (overlapFace : Chart → InteriorPiece → Face → Geometry)
    (faceSign unsignedFaceTerm : Chart → InteriorPiece → Face → Real)
    (pair :
      ArtificialFaceIndex Chart InteriorPiece Face →
        ArtificialFaceIndex Chart InteriorPiece Face)
    (pair_mem :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices)
    (pair_involutive :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair (pair q) = q)
    (paired_faceDimension_eq :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        faceDimension q.1.1 q.1.2 q.2 =
          faceDimension (pair q).1.1 (pair q).1.2 (pair q).2)
    (paired_overlapFace_eq :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        overlapFace q.1.1 q.1.2 q.2 =
          overlapFace (pair q).1.1 (pair q).1.2 (pair q).2)
    (paired_unsignedFaceTerm_eq :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        artificialFaceTerm unsignedFaceTerm q =
          artificialFaceTerm unsignedFaceTerm (pair q))
    (paired_orientation_opposite :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        artificialFaceTerm faceSign (pair q) =
          -artificialFaceTerm faceSign q)
    (fixed_terms_zero :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair q = q →
          artificialFaceTerm faceSign q * artificialFaceTerm unsignedFaceTerm q =
            0) :
    ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
      Geometry where
  activeCharts := activeCharts
  interiorPieces := interiorPieces
  faceIndices := faceIndices
  faceDimension := faceDimension
  overlapFace := overlapFace
  faceSign := faceSign
  unsignedFaceTerm := unsignedFaceTerm
  pair := pair
  pair_mem := pair_mem
  pair_involutive := pair_involutive
  paired_faceDimension_eq := paired_faceDimension_eq
  paired_overlapFace_eq := paired_overlapFace_eq
  paired_unsignedFaceTerm_eq := paired_unsignedFaceTerm_eq
  paired_orientation_cancel := by
    intro q hq
    simp [paired_orientation_opposite q hq]
  fixed_terms_zero := fixed_terms_zero

/--
Fixed-point-free constructor from an explicit opposite-orientation statement.
-/
def ofFixedPointFreeOppositeOrientation
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (faceIndices : Chart → InteriorPiece → Finset Face)
    (faceDimension : Chart → InteriorPiece → Face → FaceDimension)
    (overlapFace : Chart → InteriorPiece → Face → Geometry)
    (faceSign unsignedFaceTerm : Chart → InteriorPiece → Face → Real)
    (pair :
      ArtificialFaceIndex Chart InteriorPiece Face →
        ArtificialFaceIndex Chart InteriorPiece Face)
    (pair_mem :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices)
    (pair_involutive :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair (pair q) = q)
    (pair_ne_self :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair q ≠ q)
    (paired_faceDimension_eq :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        faceDimension q.1.1 q.1.2 q.2 =
          faceDimension (pair q).1.1 (pair q).1.2 (pair q).2)
    (paired_overlapFace_eq :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        overlapFace q.1.1 q.1.2 q.2 =
          overlapFace (pair q).1.1 (pair q).1.2 (pair q).2)
    (paired_unsignedFaceTerm_eq :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        artificialFaceTerm unsignedFaceTerm q =
          artificialFaceTerm unsignedFaceTerm (pair q))
    (paired_orientation_opposite :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        artificialFaceTerm faceSign (pair q) =
          -artificialFaceTerm faceSign q) :
    ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
      Geometry :=
  ofOppositeOrientation activeCharts interiorPieces faceIndices faceDimension
    overlapFace faceSign unsignedFaceTerm pair pair_mem pair_involutive
    paired_faceDimension_eq paired_overlapFace_eq paired_unsignedFaceTerm_eq
    paired_orientation_opposite
    (fun q hq hfix => False.elim ((pair_ne_self q hq) hfix))

/--
Coordinate-face constructor: paired coordinate faces are opposite sides of the
same coordinate dimension and represent the same overlap face.
-/
def ofCoordinateOverlapPairing {n : Nat}
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (faceIndices : Chart → InteriorPiece → Finset Face)
    (coordinateFace : Chart → InteriorPiece → Face → ArtificialCoordinateFace n)
    (overlapFace : Chart → InteriorPiece → Face → Geometry)
    (unsignedFaceTerm : Chart → InteriorPiece → Face → Real)
    (pair :
      ArtificialFaceIndex Chart InteriorPiece Face →
        ArtificialFaceIndex Chart InteriorPiece Face)
    (pair_mem :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices)
    (pair_involutive :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair (pair q) = q)
    (paired_coordinateFace_opposite :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        coordinateFace (pair q).1.1 (pair q).1.2 (pair q).2 =
          (coordinateFace q.1.1 q.1.2 q.2).opposite)
    (paired_overlapFace_eq :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        overlapFace q.1.1 q.1.2 q.2 =
          overlapFace (pair q).1.1 (pair q).1.2 (pair q).2)
    (paired_unsignedFaceTerm_eq :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        artificialFaceTerm unsignedFaceTerm q =
          artificialFaceTerm unsignedFaceTerm (pair q))
    (fixed_terms_zero :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair q = q →
          artificialFaceTerm
              (fun x p f => (coordinateFace x p f).sign) q *
            artificialFaceTerm unsignedFaceTerm q = 0) :
    ArtificialFaceOverlapPairingData Chart InteriorPiece Face (Fin (n + 1))
      Geometry where
  activeCharts := activeCharts
  interiorPieces := interiorPieces
  faceIndices := faceIndices
  faceDimension := fun x p f => (coordinateFace x p f).faceDimension
  overlapFace := overlapFace
  faceSign := fun x p f => (coordinateFace x p f).sign
  unsignedFaceTerm := unsignedFaceTerm
  pair := pair
  pair_mem := pair_mem
  pair_involutive := pair_involutive
  paired_faceDimension_eq := by
    intro q hq
    have hcoord := paired_coordinateFace_opposite q hq
    change (coordinateFace q.1.1 q.1.2 q.2).faceDimension =
      (coordinateFace (pair q).1.1 (pair q).1.2 (pair q).2).faceDimension
    rw [hcoord]
    rfl
  paired_overlapFace_eq := paired_overlapFace_eq
  paired_unsignedFaceTerm_eq := paired_unsignedFaceTerm_eq
  paired_orientation_cancel := by
    intro q hq
    have hcoord := paired_coordinateFace_opposite q hq
    change (coordinateFace q.1.1 q.1.2 q.2).sign +
      (coordinateFace (pair q).1.1 (pair q).1.2 (pair q).2).sign = 0
    rw [hcoord]
    exact ArtificialCoordinateFace.sign_add_sign_opposite
      (coordinateFace q.1.1 q.1.2 q.2)
  fixed_terms_zero := fixed_terms_zero

/--
Coordinate-face constructor for fixed-point-free overlap pairings.
-/
def ofCoordinateFixedPointFreeOverlapPairing {n : Nat}
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (faceIndices : Chart → InteriorPiece → Finset Face)
    (coordinateFace : Chart → InteriorPiece → Face → ArtificialCoordinateFace n)
    (overlapFace : Chart → InteriorPiece → Face → Geometry)
    (unsignedFaceTerm : Chart → InteriorPiece → Face → Real)
    (pair :
      ArtificialFaceIndex Chart InteriorPiece Face →
        ArtificialFaceIndex Chart InteriorPiece Face)
    (pair_mem :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices)
    (pair_involutive :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair (pair q) = q)
    (pair_ne_self :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair q ≠ q)
    (paired_coordinateFace_opposite :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        coordinateFace (pair q).1.1 (pair q).1.2 (pair q).2 =
          (coordinateFace q.1.1 q.1.2 q.2).opposite)
    (paired_overlapFace_eq :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        overlapFace q.1.1 q.1.2 q.2 =
          overlapFace (pair q).1.1 (pair q).1.2 (pair q).2)
    (paired_unsignedFaceTerm_eq :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        artificialFaceTerm unsignedFaceTerm q =
          artificialFaceTerm unsignedFaceTerm (pair q)) :
    ArtificialFaceOverlapPairingData Chart InteriorPiece Face (Fin (n + 1))
      Geometry :=
  ofCoordinateOverlapPairing activeCharts interiorPieces faceIndices
    coordinateFace overlapFace unsignedFaceTerm pair pair_mem pair_involutive
    paired_coordinateFace_opposite paired_overlapFace_eq
    paired_unsignedFaceTerm_eq
    (fun q hq hfix => False.elim ((pair_ne_self q hq) hfix))

end ArtificialFaceOverlapPairingData

namespace ArtificialFaceGeometryData

/-- Build the geometric face package by forgetting the overlap-specific name. -/
def ofOverlapPairing
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry) :
    ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry :=
  D.toArtificialFaceGeometryData

end ArtificialFaceGeometryData

namespace ArtificialFacePairingData

/-- Build the algebraic face-pairing package from overlap-pairing data. -/
def ofOverlapPairing
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry) :
    ArtificialFacePairingData Chart InteriorPiece Face :=
  D.toArtificialFacePairingData

end ArtificialFacePairingData

end ArtificialFaceOverlapPairing

end Stokes

end
