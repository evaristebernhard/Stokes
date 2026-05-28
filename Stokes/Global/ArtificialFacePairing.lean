import Stokes.Global.Cancellation

/-!
# Artificial face pairings

This file packages the geometric input that artificial faces of interior boxes
come in opposite pairs.  The package refines the existing
`ArtificialBoundaryCancellationData`: instead of recording one boundary term per
interior piece, it records finitely many face terms for each piece, a pairing of
the flattened face index set, and the algebraic facts needed for cancellation.
-/

noncomputable section

open scoped BigOperators

namespace Stokes

section ArtificialFaces

variable {Chart InteriorPiece Face : Type*}

/-- The flattened index type for artificial faces of interior pieces. -/
abbrev ArtificialFaceIndex (Chart InteriorPiece Face : Type*) :=
  Σ _ : (Σ _ : Chart, InteriorPiece), Face

/--
The flattened finite index set of active artificial faces.

An element is an active chart, an interior piece assigned to that chart, and one
of the artificial face labels assigned to that piece.
-/
def artificialFaceIndexSet
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (faceIndices : Chart → InteriorPiece → Finset Face) :
    Finset (ArtificialFaceIndex Chart InteriorPiece Face) :=
  (artificialBoundaryIndexSet activeCharts interiorPieces).sigma
    (fun qp => faceIndices qp.1 qp.2)

/-- Evaluate a face term on the flattened artificial-face index type. -/
def artificialFaceTerm
    (faceTerm : Chart → InteriorPiece → Face → Real)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) : Real :=
  faceTerm q.1.1 q.1.2 q.2

/--
The nested chart/piece/face sum equals the sum over the flattened artificial
face index set.
-/
theorem interiorBoundaryFace_sum_eq_indexSet_sum
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (faceIndices : Chart → InteriorPiece → Finset Face)
    (faceTerm : Chart → InteriorPiece → Face → Real) :
    (Finset.sum activeCharts fun x =>
        Finset.sum (interiorPieces x) fun p =>
          Finset.sum (faceIndices x p) fun f => faceTerm x p f) =
      Finset.sum (artificialFaceIndexSet activeCharts interiorPieces faceIndices)
        fun q => artificialFaceTerm faceTerm q := by
  rw [interiorBoundary_sum_eq_indexSet_sum activeCharts interiorPieces
    (fun x p => Finset.sum (faceIndices x p) fun f => faceTerm x p f)]
  simpa [artificialFaceIndexSet, artificialFaceTerm] using
    (Finset.sum_sigma'
      (artificialBoundaryIndexSet activeCharts interiorPieces)
      (fun qp => faceIndices qp.1 qp.2)
      (fun qp f => faceTerm qp.1 qp.2 f))

/--
Artificial face terms cancel when a set-preserving involution pairs opposite
terms and any fixed terms are already zero.
-/
theorem interiorBoundaryFace_sum_eq_zero_of_pairing
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (faceIndices : Chart → InteriorPiece → Finset Face)
    (faceTerm : Chart → InteriorPiece → Face → Real)
    (pair :
      ArtificialFaceIndex Chart InteriorPiece Face →
        ArtificialFaceIndex Chart InteriorPiece Face)
    (hpaired_terms_cancel :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        artificialFaceTerm faceTerm q + artificialFaceTerm faceTerm (pair q) = 0)
    (hfixed_terms_zero :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair q = q → artificialFaceTerm faceTerm q = 0)
    (hpair_mem :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices)
    (hpair_involutive :
      ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
        pair (pair q) = q) :
    (Finset.sum activeCharts fun x =>
        Finset.sum (interiorPieces x) fun p =>
          Finset.sum (faceIndices x p) fun f => faceTerm x p f) = 0 := by
  rw [interiorBoundaryFace_sum_eq_indexSet_sum]
  exact sum_pair_cancel_of_involution
    (artificialFaceIndexSet activeCharts interiorPieces faceIndices)
    (fun q => artificialFaceTerm faceTerm q) pair hpaired_terms_cancel
    (fun q hq hnonzero hfix => hnonzero (hfixed_terms_zero q hq hfix))
    hpair_mem hpair_involutive

/--
Geometry package for cancellation of artificial faces from interior pieces.

The face labels are local to each interior piece.  The pairing is stated on the
flattened face-index type; `pair_mem` says it preserves the active finite index
set, `pair_involutive` says it is an involution there, `paired_terms_cancel`
records the opposite-orientation sum, and `fixed_terms_zero` allows harmless
zero fixed points.
-/
structure ArtificialFacePairingData (Chart InteriorPiece Face : Type*) where
  /-- Finite chart labels whose interior pieces contribute artificial faces. -/
  activeCharts : Finset Chart
  /-- Interior pieces assigned to each chart. -/
  interiorPieces : Chart → Finset InteriorPiece
  /-- Artificial face labels assigned to an interior piece. -/
  faceIndices : Chart → InteriorPiece → Finset Face
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
  /-- Paired artificial face terms sum to zero. -/
  paired_terms_cancel :
    ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      artificialFaceTerm faceTerm q + artificialFaceTerm faceTerm (pair q) = 0
  /-- Fixed artificial face terms are already zero. -/
  fixed_terms_zero :
    ∀ q, q ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      pair q = q → artificialFaceTerm faceTerm q = 0

namespace ArtificialFacePairingData

/-- The active flattened artificial-face index set carried by the package. -/
def indexSet (D : ArtificialFacePairingData Chart InteriorPiece Face) :
    Finset (ArtificialFaceIndex Chart InteriorPiece Face) :=
  artificialFaceIndexSet D.activeCharts D.interiorPieces D.faceIndices

/-- The flattened artificial-face term carried by the package. -/
def term
    (D : ArtificialFacePairingData Chart InteriorPiece Face)
    (q : ArtificialFaceIndex Chart InteriorPiece Face) : Real :=
  artificialFaceTerm D.faceTerm q

/-- The per-piece artificial boundary term obtained by summing all face terms. -/
def interiorBoundaryTerm
    (D : ArtificialFacePairingData Chart InteriorPiece Face)
    (x : Chart) (p : InteriorPiece) : Real :=
  Finset.sum (D.faceIndices x p) fun f => D.faceTerm x p f

/-- The recorded face pairing cancels the total nested face sum. -/
theorem faceSum_cancellation
    (D : ArtificialFacePairingData Chart InteriorPiece Face) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.interiorPieces x) fun p =>
          Finset.sum (D.faceIndices x p) fun f => D.faceTerm x p f) = 0 :=
  interiorBoundaryFace_sum_eq_zero_of_pairing D.activeCharts D.interiorPieces
    D.faceIndices D.faceTerm D.pair D.paired_terms_cancel
    D.fixed_terms_zero D.pair_mem D.pair_involutive

/--
The face pairing fills the exact cancellation shape expected by global Stokes
when each interior-piece boundary term is the sum of its face terms.
-/
theorem to_interiorBoundaryCancellation
    (D : ArtificialFacePairingData Chart InteriorPiece Face) :
    (Finset.sum D.activeCharts fun x =>
      Finset.sum (D.interiorPieces x) fun p => D.interiorBoundaryTerm x p) = 0 := by
  simpa [interiorBoundaryTerm] using D.faceSum_cancellation

/--
If an existing per-piece boundary term agrees with the recorded face sum on
active pieces, the face pairing fills the global cancellation field for that
term.
-/
theorem interiorBoundaryCancellation_of_boundaryTerm_eq_faceSum
    (D : ArtificialFacePairingData Chart InteriorPiece Face)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ p, p ∈ D.interiorPieces x →
          interiorBoundaryTerm x p = D.interiorBoundaryTerm x p) :
    (Finset.sum D.activeCharts fun x =>
      Finset.sum (D.interiorPieces x) fun p => interiorBoundaryTerm x p) = 0 := by
  calc
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.interiorPieces x) fun p => interiorBoundaryTerm x p) =
        Finset.sum D.activeCharts fun x =>
          Finset.sum (D.interiorPieces x) fun p => D.interiorBoundaryTerm x p := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      refine Finset.sum_congr rfl ?_
      intro p hp
      exact hterm x hx p hp
    _ = 0 := D.to_interiorBoundaryCancellation

/--
Construct the existing artificial-boundary cancellation package by using the
face sums as the per-piece boundary terms.
-/
def toArtificialBoundaryCancellationData
    (D : ArtificialFacePairingData Chart InteriorPiece Face) :
    ArtificialBoundaryCancellationData Chart InteriorPiece where
  activeCharts := D.activeCharts
  interiorPieces := D.interiorPieces
  interiorBoundaryTerm := D.interiorBoundaryTerm
  cancellation := D.to_interiorBoundaryCancellation

/--
Construct the existing artificial-boundary cancellation package for an external
per-piece boundary term that agrees with the recorded face sum on active pieces.
-/
def toArtificialBoundaryCancellationData_of_boundaryTerm
    (D : ArtificialFacePairingData Chart InteriorPiece Face)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ p, p ∈ D.interiorPieces x →
          interiorBoundaryTerm x p = D.interiorBoundaryTerm x p) :
    ArtificialBoundaryCancellationData Chart InteriorPiece where
  activeCharts := D.activeCharts
  interiorPieces := D.interiorPieces
  interiorBoundaryTerm := interiorBoundaryTerm
  cancellation := D.interiorBoundaryCancellation_of_boundaryTerm_eq_faceSum
    interiorBoundaryTerm hterm

end ArtificialFacePairingData

namespace GlobalStokesAssemblyData

variable {BoundaryPiece : Type*}

/--
Face-pairing wrapper with the exact target shape of
`GlobalStokesAssemblyData.interiorBoundaryCancellation`, using face sums as
per-piece terms.
-/
theorem interiorBoundaryCancellation_of_facePairingData
    (D : ArtificialFacePairingData Chart InteriorPiece Face) :
    (Finset.sum D.activeCharts fun x =>
      Finset.sum (D.interiorPieces x) fun p => D.interiorBoundaryTerm x p) = 0 :=
  D.to_interiorBoundaryCancellation

/--
Face-pairing wrapper for an existing per-piece artificial boundary term.
-/
theorem interiorBoundaryCancellation_of_facePairing
    (D : ArtificialFacePairingData Chart InteriorPiece Face)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ p, p ∈ D.interiorPieces x →
          interiorBoundaryTerm x p = D.interiorBoundaryTerm x p) :
    (Finset.sum D.activeCharts fun x =>
      Finset.sum (D.interiorPieces x) fun p => interiorBoundaryTerm x p) = 0 :=
  D.interiorBoundaryCancellation_of_boundaryTerm_eq_faceSum interiorBoundaryTerm hterm

end GlobalStokesAssemblyData

namespace GlobalStokesData

/--
Face-pairing wrapper with the exact target shape of
`GlobalStokesData.interiorBoundaryCancellation`, using face sums as per-piece
terms.
-/
theorem interiorBoundaryCancellation_of_facePairingData
    (D : ArtificialFacePairingData Chart InteriorPiece Face) :
    (Finset.sum D.activeCharts fun x =>
      Finset.sum (D.interiorPieces x) fun p => D.interiorBoundaryTerm x p) = 0 :=
  D.to_interiorBoundaryCancellation

/--
Face-pairing wrapper for an existing per-piece artificial boundary term.
-/
theorem interiorBoundaryCancellation_of_facePairing
    (D : ArtificialFacePairingData Chart InteriorPiece Face)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ p, p ∈ D.interiorPieces x →
          interiorBoundaryTerm x p = D.interiorBoundaryTerm x p) :
    (Finset.sum D.activeCharts fun x =>
      Finset.sum (D.interiorPieces x) fun p => interiorBoundaryTerm x p) = 0 :=
  D.interiorBoundaryCancellation_of_boundaryTerm_eq_faceSum interiorBoundaryTerm hterm

end GlobalStokesData

end ArtificialFaces

end Stokes

end
