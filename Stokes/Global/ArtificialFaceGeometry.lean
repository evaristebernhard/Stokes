import Stokes.Global.ArtificialFacePairing
import Stokes.HalfSpace.Faces

/-!
# Geometric artificial-face data

This file is the geometric wrapper above `ArtificialFacePairingData`.  It keeps
the source face index, a face-dimension label, an underlying geometric face, and
the signed/unsigned term data that explain the cancellation.  The algebraic
projection to `ArtificialFacePairingData` is still the authoritative input for
finite-sum cancellation.
-/

noncomputable section

open scoped BigOperators

namespace Stokes

section ArtificialFaceGeometry

universe c p f d g

variable {Chart : Type c} {InteriorPiece : Type p} {Face : Type f}
variable {FaceDimension : Type d} {Geometry : Type g}

/-- The chart/interior-piece source of a flattened artificial face. -/
abbrev ArtificialFaceSourceIndex (Chart InteriorPiece : Type*) :=
  Σ _ : Chart, InteriorPiece

namespace ArtificialFaceIndex

/-- The source chart/interior-piece index of a flattened artificial face. -/
def sourceIndex (q : ArtificialFaceIndex Chart InteriorPiece Face) :
    ArtificialFaceSourceIndex Chart InteriorPiece :=
  q.1

/-- The source chart of a flattened artificial face. -/
def sourceChart (q : ArtificialFaceIndex Chart InteriorPiece Face) : Chart :=
  q.1.1

/-- The source interior piece of a flattened artificial face. -/
def sourcePiece (q : ArtificialFaceIndex Chart InteriorPiece Face) : InteriorPiece :=
  q.1.2

/-- The local face label of a flattened artificial face. -/
def faceLabel (q : ArtificialFaceIndex Chart InteriorPiece Face) : Face :=
  q.2

@[simp]
theorem sourceIndex_eq (q : ArtificialFaceIndex Chart InteriorPiece Face) :
    sourceIndex q = q.1 :=
  rfl

@[simp]
theorem sourceChart_eq (q : ArtificialFaceIndex Chart InteriorPiece Face) :
    sourceChart q = q.1.1 :=
  rfl

@[simp]
theorem sourcePiece_eq (q : ArtificialFaceIndex Chart InteriorPiece Face) :
    sourcePiece q = q.1.2 :=
  rfl

@[simp]
theorem faceLabel_eq (q : ArtificialFaceIndex Chart InteriorPiece Face) :
    faceLabel q = q.2 :=
  rfl

end ArtificialFaceIndex

/--
A coordinate face of an `(n + 1)`-box, consisting of the coordinate dimension
and the choice of upper or lower side.
-/
structure ArtificialCoordinateFace (n : Nat) where
  /-- The coordinate normal to this face. -/
  faceDimension : Fin (n + 1)
  /-- `true` for the upper face and `false` for the lower face. -/
  isUpper : Bool

namespace ArtificialCoordinateFace

/-- The same coordinate face with the opposite upper/lower side. -/
def opposite {n : Nat} (F : ArtificialCoordinateFace n) : ArtificialCoordinateFace n where
  faceDimension := F.faceDimension
  isUpper := !F.isUpper

/-- The cubical sign attached to this coordinate face. -/
def sign {n : Nat} (F : ArtificialCoordinateFace n) : Real :=
  if F.isUpper then upperFaceSign F.faceDimension else lowerFaceSign F.faceDimension

@[simp]
theorem opposite_faceDimension {n : Nat} (F : ArtificialCoordinateFace n) :
    F.opposite.faceDimension = F.faceDimension :=
  rfl

@[simp]
theorem opposite_isUpper {n : Nat} (F : ArtificialCoordinateFace n) :
    F.opposite.isUpper = !F.isUpper :=
  rfl

@[simp]
theorem sign_mk_upper {n : Nat} (i : Fin (n + 1)) :
    sign ({ faceDimension := i, isUpper := true } : ArtificialCoordinateFace n) =
      upperFaceSign i := by
  simp [sign]

@[simp]
theorem sign_mk_lower {n : Nat} (i : Fin (n + 1)) :
    sign ({ faceDimension := i, isUpper := false } : ArtificialCoordinateFace n) =
      lowerFaceSign i := by
  simp [sign]

/-- Opposite coordinate faces have opposite cubical signs. -/
theorem sign_add_sign_opposite {n : Nat} (F : ArtificialCoordinateFace n) :
    sign F + sign F.opposite = 0 := by
  rcases F with ⟨i, upper⟩
  cases upper <;> simp [sign, opposite, upperFaceSign, lowerFaceSign, add_comm]

/-- Opposite coordinate faces have opposite cubical signs, in the other order. -/
theorem sign_opposite_add_sign {n : Nat} (F : ArtificialCoordinateFace n) :
    sign F.opposite + sign F = 0 := by
  simpa [add_comm] using sign_add_sign_opposite F

end ArtificialCoordinateFace

/--
Geometric data explaining an artificial-face pairing.

The fields `faceDimension` and `geometricFace` record geometry that is not
needed by the finite-sum cancellation theorem itself.  The cancellation proof
uses the signed/unsigned decomposition: paired faces have the same unsigned
term and signs summing to zero, while fixed points are recorded as zero terms.
-/
structure ArtificialFaceGeometryData
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
  /-- Underlying geometric face, forgetting the algebraic sign. -/
  geometricFace : Chart → InteriorPiece → Face → Geometry
  /-- Signed orientation factor of a face. -/
  faceSign : Chart → InteriorPiece → Face → Real
  /-- Unsigned integral or magnitude attached to a face. -/
  unsignedFaceTerm : Chart → InteriorPiece → Face → Real
  /-- Signed contribution of one artificial face. -/
  faceTerm : Chart → InteriorPiece → Face → Real
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
  /-- Paired faces represent the same underlying geometric face. -/
  paired_geometricFace_eq :
    ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      geometricFace q.1.1 q.1.2 q.2 =
        geometricFace (pair q).1.1 (pair q).1.2 (pair q).2
  /-- The signed face term is sign times unsigned face term. -/
  faceTerm_eq_sign_mul :
    ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      artificialFaceTerm faceTerm q =
        artificialFaceTerm faceSign q * artificialFaceTerm unsignedFaceTerm q
  /-- Paired faces have equal unsigned terms. -/
  paired_unsignedFaceTerm_eq :
    ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      artificialFaceTerm unsignedFaceTerm q =
        artificialFaceTerm unsignedFaceTerm (pair q)
  /-- Paired face signs cancel. -/
  paired_sign_cancel :
    ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      artificialFaceTerm faceSign q + artificialFaceTerm faceSign (pair q) = 0
  /-- Fixed artificial face terms are already zero. -/
  fixed_terms_zero :
    ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      pair q = q → artificialFaceTerm faceTerm q = 0

namespace ArtificialFaceGeometryData

/-- The active flattened artificial-face index set carried by the package. -/
def indexSet
    (D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry) :
    Finset (ArtificialFaceIndex Chart InteriorPiece Face) :=
  artificialFaceIndexSet D.activeCharts D.interiorPieces D.faceIndices

/-- The source chart/interior-piece index of a flattened artificial face. -/
def sourceIndex
    (_D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) :
    ArtificialFaceSourceIndex Chart InteriorPiece :=
  ArtificialFaceIndex.sourceIndex q

/-- The paired flattened artificial face. -/
def pairedFace
    (D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) :
    ArtificialFaceIndex Chart InteriorPiece Face :=
  D.pair q

/-- The recorded face dimension of a flattened artificial face. -/
def dimension
    (D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) : FaceDimension :=
  D.faceDimension q.1.1 q.1.2 q.2

/-- The recorded underlying geometric face of a flattened artificial face. -/
def geometry
    (D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) : Geometry :=
  D.geometricFace q.1.1 q.1.2 q.2

/-- The recorded face sign of a flattened artificial face. -/
def sign
    (D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) : Real :=
  artificialFaceTerm D.faceSign q

/-- The recorded unsigned face term of a flattened artificial face. -/
def unsignedTerm
    (D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) : Real :=
  artificialFaceTerm D.unsignedFaceTerm q

/-- The recorded signed face term of a flattened artificial face. -/
def term
    (D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) : Real :=
  artificialFaceTerm D.faceTerm q

/-- Paired active faces have equal recorded dimensions. -/
theorem paired_dimension_eq
    (D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry)
    {q : ArtificialFaceIndex Chart InteriorPiece Face} (hq : q ∈ D.indexSet) :
    D.dimension q = D.dimension (D.pairedFace q) := by
  exact D.paired_faceDimension_eq q hq

/-- Paired active faces have equal recorded underlying geometry. -/
theorem paired_geometry_eq
    (D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry)
    {q : ArtificialFaceIndex Chart InteriorPiece Face} (hq : q ∈ D.indexSet) :
    D.geometry q = D.geometry (D.pairedFace q) := by
  exact D.paired_geometricFace_eq q hq

/-- The signed term decomposes as sign times unsigned term. -/
theorem term_eq_sign_mul_unsigned
    (D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry)
    {q : ArtificialFaceIndex Chart InteriorPiece Face} (hq : q ∈ D.indexSet) :
    D.term q = D.sign q * D.unsignedTerm q := by
  exact D.faceTerm_eq_sign_mul q hq

/-- The signed/unsigned geometric fields imply the algebraic cancellation field. -/
theorem paired_terms_cancel
    (D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry) :
    ∀ q, q ∈ D.indexSet → D.term q + D.term (D.pairedFace q) = 0 := by
  intro q hq
  change artificialFaceTerm D.faceTerm q +
      artificialFaceTerm D.faceTerm (D.pair q) = 0
  rw [D.faceTerm_eq_sign_mul q hq,
    D.faceTerm_eq_sign_mul (D.pair q) (D.pair_mem q hq)]
  rw [D.paired_unsignedFaceTerm_eq q hq, ← add_mul,
    D.paired_sign_cancel q hq, zero_mul]

/-- Forget the geometric fields and keep the algebraic artificial-face pairing. -/
def toArtificialFacePairingData
    (D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry) :
    ArtificialFacePairingData Chart InteriorPiece Face where
  activeCharts := D.activeCharts
  interiorPieces := D.interiorPieces
  faceIndices := D.faceIndices
  faceTerm := D.faceTerm
  pair := D.pair
  pair_mem := D.pair_mem
  pair_involutive := D.pair_involutive
  paired_terms_cancel := ArtificialFaceGeometryData.paired_terms_cancel D
  fixed_terms_zero := D.fixed_terms_zero

/-- The active index set is unchanged by forgetting geometry. -/
theorem toArtificialFacePairingData_indexSet
    (D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry) :
    D.toArtificialFacePairingData.indexSet = D.indexSet :=
  rfl

/-- The active face term is unchanged by forgetting geometry. -/
theorem toArtificialFacePairingData_term
    (D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) :
    D.toArtificialFacePairingData.term q = D.term q :=
  rfl

/-- The recorded geometric pairing cancels the total nested face sum. -/
theorem faceSum_cancellation
    (D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.interiorPieces x) fun p =>
          Finset.sum (D.faceIndices x p) fun f => D.faceTerm x p f) = 0 :=
  D.toArtificialFacePairingData.faceSum_cancellation

/-- Forget geometry all the way to the existing artificial-boundary package. -/
def toArtificialBoundaryCancellationData
    (D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry) :
    ArtificialBoundaryCancellationData Chart InteriorPiece :=
  D.toArtificialFacePairingData.toArtificialBoundaryCancellationData

/--
Constructor for a geometric data package from explicit signed/unsigned pairing
fields.
-/
def ofSignedPairing
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (faceIndices : Chart → InteriorPiece → Finset Face)
    (faceDimension : Chart → InteriorPiece → Face → FaceDimension)
    (geometricFace : Chart → InteriorPiece → Face → Geometry)
    (faceSign unsignedFaceTerm faceTerm : Chart → InteriorPiece → Face → Real)
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
    (paired_geometricFace_eq :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        geometricFace q.1.1 q.1.2 q.2 =
          geometricFace (pair q).1.1 (pair q).1.2 (pair q).2)
    (faceTerm_eq_sign_mul :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        artificialFaceTerm faceTerm q =
          artificialFaceTerm faceSign q * artificialFaceTerm unsignedFaceTerm q)
    (paired_unsignedFaceTerm_eq :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        artificialFaceTerm unsignedFaceTerm q =
          artificialFaceTerm unsignedFaceTerm (pair q))
    (paired_sign_cancel :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        artificialFaceTerm faceSign q + artificialFaceTerm faceSign (pair q) = 0)
    (fixed_terms_zero :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair q = q → artificialFaceTerm faceTerm q = 0) :
    ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry where
  activeCharts := activeCharts
  interiorPieces := interiorPieces
  faceIndices := faceIndices
  faceDimension := faceDimension
  geometricFace := geometricFace
  faceSign := faceSign
  unsignedFaceTerm := unsignedFaceTerm
  faceTerm := faceTerm
  pair := pair
  pair_mem := pair_mem
  pair_involutive := pair_involutive
  paired_faceDimension_eq := paired_faceDimension_eq
  paired_geometricFace_eq := paired_geometricFace_eq
  faceTerm_eq_sign_mul := faceTerm_eq_sign_mul
  paired_unsignedFaceTerm_eq := paired_unsignedFaceTerm_eq
  paired_sign_cancel := paired_sign_cancel
  fixed_terms_zero := fixed_terms_zero

/--
Coordinate-face constructor: signs are the standard cubical signs carried by
`ArtificialCoordinateFace`, and paired coordinate faces are opposite sides of
the same coordinate dimension.
-/
def ofCoordinatePairing {n : Nat}
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (faceIndices : Chart → InteriorPiece → Finset Face)
    (coordinateFace : Chart → InteriorPiece → Face → ArtificialCoordinateFace n)
    (geometricFace : Chart → InteriorPiece → Face → Geometry)
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
    (paired_geometricFace_eq :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        geometricFace q.1.1 q.1.2 q.2 =
          geometricFace (pair q).1.1 (pair q).1.2 (pair q).2)
    (paired_unsignedFaceTerm_eq :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        artificialFaceTerm unsignedFaceTerm q =
          artificialFaceTerm unsignedFaceTerm (pair q))
    (fixed_terms_zero :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair q = q →
          artificialFaceTerm
            (fun x p f => (coordinateFace x p f).sign * unsignedFaceTerm x p f) q = 0) :
    ArtificialFaceGeometryData Chart InteriorPiece Face (Fin (n + 1)) Geometry where
  activeCharts := activeCharts
  interiorPieces := interiorPieces
  faceIndices := faceIndices
  faceDimension := fun x p f => (coordinateFace x p f).faceDimension
  geometricFace := geometricFace
  faceSign := fun x p f => (coordinateFace x p f).sign
  unsignedFaceTerm := unsignedFaceTerm
  faceTerm := fun x p f => (coordinateFace x p f).sign * unsignedFaceTerm x p f
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
  paired_geometricFace_eq := paired_geometricFace_eq
  faceTerm_eq_sign_mul := by
    intro q _hq
    rfl
  paired_unsignedFaceTerm_eq := paired_unsignedFaceTerm_eq
  paired_sign_cancel := by
    intro q hq
    have hcoord := paired_coordinateFace_opposite q hq
    change (coordinateFace q.1.1 q.1.2 q.2).sign +
      (coordinateFace (pair q).1.1 (pair q).1.2 (pair q).2).sign = 0
    rw [hcoord]
    exact ArtificialCoordinateFace.sign_add_sign_opposite
      (coordinateFace q.1.1 q.1.2 q.2)
  fixed_terms_zero := fixed_terms_zero

/--
Coordinate-face constructor for fixed-point-free pairings.  The fixed-term
field is discharged by contradiction.
-/
def ofCoordinateFixedPointFreePairing {n : Nat}
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (faceIndices : Chart → InteriorPiece → Finset Face)
    (coordinateFace : Chart → InteriorPiece → Face → ArtificialCoordinateFace n)
    (geometricFace : Chart → InteriorPiece → Face → Geometry)
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
    (paired_geometricFace_eq :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        geometricFace q.1.1 q.1.2 q.2 =
          geometricFace (pair q).1.1 (pair q).1.2 (pair q).2)
    (paired_unsignedFaceTerm_eq :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        artificialFaceTerm unsignedFaceTerm q =
          artificialFaceTerm unsignedFaceTerm (pair q)) :
    ArtificialFaceGeometryData Chart InteriorPiece Face (Fin (n + 1)) Geometry :=
  ofCoordinatePairing activeCharts interiorPieces faceIndices coordinateFace
    geometricFace unsignedFaceTerm pair pair_mem pair_involutive
    paired_coordinateFace_opposite paired_geometricFace_eq paired_unsignedFaceTerm_eq
    (fun q hq hfix => False.elim ((pair_ne_self q hq) hfix))

end ArtificialFaceGeometryData

namespace ArtificialFacePairingData

/-- Build the algebraic face-pairing package by forgetting geometric fields. -/
def ofGeometry
    (D : ArtificialFaceGeometryData Chart InteriorPiece Face FaceDimension Geometry) :
    ArtificialFacePairingData Chart InteriorPiece Face :=
  D.toArtificialFacePairingData

end ArtificialFacePairingData

end ArtificialFaceGeometry

end Stokes

end
