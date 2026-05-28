import Stokes.Global.InteriorBoundarySupportZero
import Stokes.Global.ArtificialFaceAdjacency
import Stokes.Global.ArtificialFaceOverlapPairing
import Stokes.Global.SelectedInteriorAssembly

/-!
# Reduced artificial-face resolution fields

This file gives a small common wrapper for the artificial interior-boundary
remainder.  The existing development can resolve those terms in several ways:

* strict interior support makes each artificial boundary term zero;
* selected adjacent faces cancel as opposite coordinate faces;
* overlap-pairing data cancels signed/unsigned artificial face terms.

`ArtificialFaceResolvedData` keeps only the common output: the active
chart/piece family, the per-piece artificial boundary term, and the resulting
finite-sum cancellation.  It then projects back to the existing
`ArtificialBoundaryCancellationData` consumed by the global constructors.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section ArtificialFaceFieldReduction

universe u w c p f d g

variable {Chart : Type c} {InteriorPiece : Type p}

/--
Common reduced package saying that the artificial boundary terms for a selected
interior family have already been resolved.

The resolution may come from pointwise support-zero, from selected-face
adjacency, or from a signed overlap pairing.  This wrapper deliberately forgets
which route was used and keeps exactly the cancellation shape needed by the
global assembly layer.
-/
structure ArtificialFaceResolvedData (Chart : Type c) (InteriorPiece : Type p) where
  /-- Finite chart labels whose interior pieces contribute artificial faces. -/
  activeCharts : Finset Chart
  /-- Interior pieces assigned to each chart. -/
  interiorPieces : Chart → Finset InteriorPiece
  /-- Artificial boundary contribution of an interior piece. -/
  interiorBoundaryTerm : Chart → InteriorPiece → Real
  /-- The resolved artificial boundary terms cancel in the total finite sum. -/
  cancellation :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun q => interiorBoundaryTerm x q) = 0

namespace ArtificialFaceResolvedData

/-- Convert reduced resolved artificial-face data to the existing cancellation package. -/
def toArtificialBoundaryCancellationData
    (D : ArtificialFaceResolvedData Chart InteriorPiece) :
    ArtificialBoundaryCancellationData Chart InteriorPiece where
  activeCharts := D.activeCharts
  interiorPieces := D.interiorPieces
  interiorBoundaryTerm := D.interiorBoundaryTerm
  cancellation := D.cancellation

@[simp]
theorem toArtificialBoundaryCancellationData_activeCharts
    (D : ArtificialFaceResolvedData Chart InteriorPiece) :
    D.toArtificialBoundaryCancellationData.activeCharts = D.activeCharts :=
  rfl

@[simp]
theorem toArtificialBoundaryCancellationData_interiorPieces
    (D : ArtificialFaceResolvedData Chart InteriorPiece) :
    D.toArtificialBoundaryCancellationData.interiorPieces = D.interiorPieces :=
  rfl

@[simp]
theorem toArtificialBoundaryCancellationData_interiorBoundaryTerm
    (D : ArtificialFaceResolvedData Chart InteriorPiece) :
    D.toArtificialBoundaryCancellationData.interiorBoundaryTerm =
      D.interiorBoundaryTerm :=
  rfl

/-- The cancellation equality, exposed with the same shape as the global fields. -/
theorem to_interiorBoundaryCancellation
    (D : ArtificialFaceResolvedData Chart InteriorPiece) :
    (Finset.sum D.activeCharts fun x =>
      Finset.sum (D.interiorPieces x) fun q => D.interiorBoundaryTerm x q) = 0 :=
  D.cancellation

/--
Use resolved artificial-face data to cancel any external per-piece term that
agrees with the recorded term on the active chart/piece indices.
-/
theorem interiorBoundaryCancellation_of_boundaryTerm_eq
    (D : ArtificialFaceResolvedData Chart InteriorPiece)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.interiorPieces x →
          interiorBoundaryTerm x q = D.interiorBoundaryTerm x q) :
    (Finset.sum D.activeCharts fun x =>
      Finset.sum (D.interiorPieces x) fun q => interiorBoundaryTerm x q) = 0 := by
  calc
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.interiorPieces x) fun q => interiorBoundaryTerm x q) =
        Finset.sum D.activeCharts fun x =>
          Finset.sum (D.interiorPieces x) fun q => D.interiorBoundaryTerm x q := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      refine Finset.sum_congr rfl ?_
      intro q hq
      exact hterm x hx q hq
    _ = 0 := D.cancellation

/--
Use resolved artificial-face data in the exact field shape expected by M8 and
the assembly constructors, after rewriting the active set, piece family, and
term family.
-/
theorem interiorBoundaryCancellation_of_fields
    (D : ArtificialFaceResolvedData Chart InteriorPiece)
    {activeCharts : Finset Chart}
    {interiorPieces : Chart → Finset InteriorPiece}
    {interiorBoundaryTerm : Chart → InteriorPiece → Real}
    (hactive : D.activeCharts = activeCharts)
    (hpieces : D.interiorPieces = interiorPieces)
    (hterm : D.interiorBoundaryTerm = interiorBoundaryTerm) :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun q => interiorBoundaryTerm x q) = 0 := by
  simpa [hactive, hpieces, hterm] using D.cancellation

/-- Build reduced resolved data from the existing cancellation package. -/
def ofCancellationData
    (C : ArtificialBoundaryCancellationData Chart InteriorPiece) :
    ArtificialFaceResolvedData Chart InteriorPiece where
  activeCharts := C.activeCharts
  interiorPieces := C.interiorPieces
  interiorBoundaryTerm := C.interiorBoundaryTerm
  cancellation := C.cancellation

@[simp]
theorem ofCancellationData_activeCharts
    (C : ArtificialBoundaryCancellationData Chart InteriorPiece) :
    (ofCancellationData C).activeCharts = C.activeCharts :=
  rfl

@[simp]
theorem ofCancellationData_interiorPieces
    (C : ArtificialBoundaryCancellationData Chart InteriorPiece) :
    (ofCancellationData C).interiorPieces = C.interiorPieces :=
  rfl

@[simp]
theorem ofCancellationData_interiorBoundaryTerm
    (C : ArtificialBoundaryCancellationData Chart InteriorPiece) :
    (ofCancellationData C).interiorBoundaryTerm = C.interiorBoundaryTerm :=
  rfl

/-- Build reduced resolved data from pointwise-zero artificial boundary terms. -/
def of_forall_eq_zero
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (hzero :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ interiorPieces x →
          interiorBoundaryTerm x q = 0) :
    ArtificialFaceResolvedData Chart InteriorPiece :=
  ofCancellationData <|
    ArtificialBoundaryCancellationData.of_forall_eq_zero activeCharts
      interiorPieces interiorBoundaryTerm hzero

/--
Resolve artificial boundary terms by strict support inside each selected
interior coordinate box.
-/
def ofInteriorSupportZero
    {H : Type u} [TopologicalSpace H]
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (localStokesData : Chart → InteriorPiece → InteriorLocalStokesData I ω)
    (hsupp :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ interiorPieces x →
          tsupport
              (ManifoldForm.transitionPullbackInChart I
                (localStokesData x q).sourceChart
                (localStokesData x q).targetChart ω) ⊆
            boxInteriorSupportBox
              (localStokesData x q).lowerCorner
              (localStokesData x q).upperCorner) :
    ArtificialFaceResolvedData Chart InteriorPiece :=
  ofCancellationData <|
    artificialBoundaryCancellationData_of_interiorSupportZero
      activeCharts interiorPieces localStokesData hsupp

/--
Support-zero exit in field-theorem form: strict support inside each selected
interior box cancels the local artificial-boundary terms.
-/
theorem ofInteriorSupportZero_interiorBoundaryCancellation
    {H : Type u} [TopologicalSpace H]
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (localStokesData : Chart → InteriorPiece → InteriorLocalStokesData I ω)
    (hsupp :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ interiorPieces x →
          tsupport
              (ManifoldForm.transitionPullbackInChart I
                (localStokesData x q).sourceChart
                (localStokesData x q).targetChart ω) ⊆
            boxInteriorSupportBox
              (localStokesData x q).lowerCorner
              (localStokesData x q).upperCorner) :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun q =>
        (localStokesData x q).artificialBoundaryTerm) = 0 :=
  (ofInteriorSupportZero activeCharts interiorPieces localStokesData hsupp).cancellation

/--
Support-zero exit for an assembly/M8 term that is known to agree with the
local artificial-boundary term on active pieces.
-/
theorem ofInteriorSupportZero_boundaryTerm_interiorBoundaryCancellation
    {H : Type u} [TopologicalSpace H]
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (localStokesData : Chart → InteriorPiece → InteriorLocalStokesData I ω)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (hsupp :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ interiorPieces x →
          tsupport
              (ManifoldForm.transitionPullbackInChart I
                (localStokesData x q).sourceChart
                (localStokesData x q).targetChart ω) ⊆
            boxInteriorSupportBox
              (localStokesData x q).lowerCorner
              (localStokesData x q).upperCorner)
    (hterm :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ interiorPieces x →
          interiorBoundaryTerm x q =
            (localStokesData x q).artificialBoundaryTerm) :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun q => interiorBoundaryTerm x q) = 0 := by
  calc
    (Finset.sum activeCharts fun x =>
        Finset.sum (interiorPieces x) fun q => interiorBoundaryTerm x q) =
        Finset.sum activeCharts fun x =>
          Finset.sum (interiorPieces x) fun q =>
            (localStokesData x q).artificialBoundaryTerm := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      refine Finset.sum_congr rfl ?_
      intro q hq
      exact hterm x hx q hq
    _ = 0 :=
      ofInteriorSupportZero_interiorBoundaryCancellation activeCharts
        interiorPieces localStokesData hsupp

/-- Resolve artificial boundary terms from an overlap-pairing package. -/
def ofOverlapPairing
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry) :
    ArtificialFaceResolvedData Chart InteriorPiece :=
  ofCancellationData D.toArtificialBoundaryCancellationData

/--
Overlap-pairing exit in field-theorem form, using the face-sum boundary term
recorded by the pairing package.
-/
theorem ofOverlapPairing_interiorBoundaryCancellation
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry) :
    (Finset.sum D.activeCharts fun x =>
      Finset.sum (D.interiorPieces x) fun q =>
        D.toArtificialFacePairingData.interiorBoundaryTerm x q) = 0 :=
  (ofOverlapPairing D).cancellation

/--
Resolve an external artificial boundary term that agrees with the face sums
recorded by an overlap-pairing package on active pieces.
-/
def ofOverlapPairingBoundaryTerm
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.interiorPieces x →
          interiorBoundaryTerm x q =
            D.toArtificialFacePairingData.interiorBoundaryTerm x q) :
    ArtificialFaceResolvedData Chart InteriorPiece :=
  ofCancellationData <|
    D.toArtificialFacePairingData.toArtificialBoundaryCancellationData_of_boundaryTerm
      interiorBoundaryTerm hterm

/--
Overlap-pairing exit for an assembly/M8 term that agrees with the recorded
face-sum boundary term on active pieces.
-/
theorem ofOverlapPairingBoundaryTerm_interiorBoundaryCancellation
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D :
      ArtificialFaceOverlapPairingData Chart InteriorPiece Face FaceDimension
        Geometry)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.interiorPieces x →
          interiorBoundaryTerm x q =
            D.toArtificialFacePairingData.interiorBoundaryTerm x q) :
    (Finset.sum D.activeCharts fun x =>
      Finset.sum (D.interiorPieces x) fun q => interiorBoundaryTerm x q) = 0 :=
  (ofOverlapPairingBoundaryTerm D interiorBoundaryTerm hterm).cancellation

/--
Coordinate-face overlap-pairing constructor for resolved artificial faces.

This is the reduced front door for the common case where signs are the cubical
signs of coordinate faces and paired faces are opposite sides of the same
coordinate direction.
-/
def ofCoordinateOverlapPairing
    {Face : Type f} {Geometry : Type g} {n : Nat}
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (faceIndices : Chart → InteriorPiece → Finset Face)
    (coordinateFace :
      Chart → InteriorPiece → Face → ArtificialCoordinateFace n)
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
    ArtificialFaceResolvedData Chart InteriorPiece :=
  ofOverlapPairing <|
    ArtificialFaceOverlapPairingData.ofCoordinateOverlapPairing activeCharts
      interiorPieces faceIndices coordinateFace overlapFace unsignedFaceTerm pair
      pair_mem pair_involutive paired_coordinateFace_opposite
      paired_overlapFace_eq paired_unsignedFaceTerm_eq fixed_terms_zero

/--
Fixed-point-free coordinate-face overlap-pairing constructor for resolved
artificial faces.
-/
def ofCoordinateFixedPointFreeOverlapPairing
    {Face : Type f} {Geometry : Type g} {n : Nat}
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (faceIndices : Chart → InteriorPiece → Finset Face)
    (coordinateFace :
      Chart → InteriorPiece → Face → ArtificialCoordinateFace n)
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
    ArtificialFaceResolvedData Chart InteriorPiece :=
  ofOverlapPairing <|
    ArtificialFaceOverlapPairingData.ofCoordinateFixedPointFreeOverlapPairing
      activeCharts interiorPieces faceIndices coordinateFace overlapFace
      unsignedFaceTerm pair pair_mem pair_involutive pair_ne_self
      paired_coordinateFace_opposite paired_overlapFace_eq
      paired_unsignedFaceTerm_eq

/-- Resolve selected artificial faces from adjacent selected-face data. -/
def ofAdjacentSelectedFaces
    {H : Type u} [TopologicalSpace H]
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    {Face : Type f} {Geometry : Type g}
    (D : AdjacentSelectedFacesData I ω Chart InteriorPiece Face Geometry) :
    ArtificialFaceResolvedData Chart InteriorPiece :=
  ofCancellationData <|
    D.toSelectedBoxArtificialFaceFamilyData.toArtificialBoundaryCancellationData

/--
Adjacent-selected-faces exit in field-theorem form, using the project-local
boundary term of each selected interior box.
-/
theorem ofAdjacentSelectedFaces_interiorBoundaryCancellation
    {H : Type u} [TopologicalSpace H]
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    {Face : Type f} {Geometry : Type g}
    (D : AdjacentSelectedFacesData I ω Chart InteriorPiece Face Geometry) :
    (Finset.sum D.activeCharts fun x =>
      Finset.sum (D.interiorPieces x) fun q =>
        projectInteriorBoundaryIntegral I (D.sourceChart x q)
          (D.targetChart x q) ω (D.lowerCorner x q)
          (D.upperCorner x q)) = 0 :=
  (ofAdjacentSelectedFaces D).cancellation

/--
Resolve an external artificial boundary term that agrees with the project-local
boundary term recorded by adjacent selected-face data on active pieces.
-/
def ofAdjacentSelectedFacesBoundaryTerm
    {H : Type u} [TopologicalSpace H]
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    {Face : Type f} {Geometry : Type g}
    (D : AdjacentSelectedFacesData I ω Chart InteriorPiece Face Geometry)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.interiorPieces x →
          interiorBoundaryTerm x q =
            projectInteriorBoundaryIntegral I (D.sourceChart x q)
              (D.targetChart x q) ω (D.lowerCorner x q)
              (D.upperCorner x q)) :
    ArtificialFaceResolvedData Chart InteriorPiece :=
  ofCancellationData <|
    D.toSelectedBoxArtificialFaceFamilyData
      |>.toArtificialBoundaryCancellationData_of_boundaryTerm
          interiorBoundaryTerm
          (by
            intro x hx q hq
            exact hterm x hx q hq)

/--
Adjacent-selected-faces exit for an assembly/M8 term that agrees with the
project-local boundary term on active pieces.
-/
theorem ofAdjacentSelectedFacesBoundaryTerm_interiorBoundaryCancellation
    {H : Type u} [TopologicalSpace H]
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    {Face : Type f} {Geometry : Type g}
    (D : AdjacentSelectedFacesData I ω Chart InteriorPiece Face Geometry)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.interiorPieces x →
          interiorBoundaryTerm x q =
            projectInteriorBoundaryIntegral I (D.sourceChart x q)
              (D.targetChart x q) ω (D.lowerCorner x q)
              (D.upperCorner x q)) :
    (Finset.sum D.activeCharts fun x =>
      Finset.sum (D.interiorPieces x) fun q => interiorBoundaryTerm x q) = 0 :=
  (ofAdjacentSelectedFacesBoundaryTerm D interiorBoundaryTerm hterm).cancellation

end ArtificialFaceResolvedData

namespace ArtificialBoundaryCancellationData

/-- Build the existing cancellation package from reduced resolved artificial-face data. -/
def ofResolved
    (D : ArtificialFaceResolvedData Chart InteriorPiece) :
    ArtificialBoundaryCancellationData Chart InteriorPiece :=
  D.toArtificialBoundaryCancellationData

end ArtificialBoundaryCancellationData

namespace GlobalStokesAssemblyData

/--
Resolved artificial-face data fills the assembly cancellation field after the
ambient constructor's active set, piece family, and term family are identified.
-/
theorem interiorBoundaryCancellation_of_resolvedArtificialFaces
    (D : ArtificialFaceResolvedData Chart InteriorPiece)
    {activeCharts : Finset Chart}
    {interiorPieces : Chart → Finset InteriorPiece}
    {interiorBoundaryTerm : Chart → InteriorPiece → Real}
    (hactive : D.activeCharts = activeCharts)
    (hpieces : D.interiorPieces = interiorPieces)
    (hterm : D.interiorBoundaryTerm = interiorBoundaryTerm) :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun q => interiorBoundaryTerm x q) = 0 :=
  D.interiorBoundaryCancellation_of_fields hactive hpieces hterm

end GlobalStokesAssemblyData

namespace GlobalStokesData

/--
Resolved artificial-face data fills the final global cancellation field after
the ambient constructor's active set, piece family, and term family are
identified.
-/
theorem interiorBoundaryCancellation_of_resolvedArtificialFaces
    (D : ArtificialFaceResolvedData Chart InteriorPiece)
    {activeCharts : Finset Chart}
    {interiorPieces : Chart → Finset InteriorPiece}
    {interiorBoundaryTerm : Chart → InteriorPiece → Real}
    (hactive : D.activeCharts = activeCharts)
    (hpieces : D.interiorPieces = interiorPieces)
    (hterm : D.interiorBoundaryTerm = interiorBoundaryTerm) :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun q => interiorBoundaryTerm x q) = 0 :=
  D.interiorBoundaryCancellation_of_fields hactive hpieces hterm

end GlobalStokesData

section SelectedInteriorAssembly

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Face : Type f}

namespace SelectedInteriorAssemblyData

/--
The artificial-face output of a selected interior assembly, in the reduced
resolved-data shape.
-/
def toArtificialFaceResolvedData
    (D : SelectedInteriorAssemblyData I ω Face) :
    ArtificialFaceResolvedData M Unit :=
  ArtificialFaceResolvedData.ofCancellationData
    D.toArtificialBoundaryCancellationData

@[simp]
theorem toArtificialFaceResolvedData_activeCharts
    (D : SelectedInteriorAssemblyData I ω Face) :
    D.toArtificialFaceResolvedData.activeCharts = D.activeCharts := by
  simp [toArtificialFaceResolvedData]

@[simp]
theorem toArtificialFaceResolvedData_interiorPieces
    (D : SelectedInteriorAssemblyData I ω Face) :
    D.toArtificialFaceResolvedData.interiorPieces = D.interiorPieces := by
  simp [toArtificialFaceResolvedData]

@[simp]
theorem toArtificialFaceResolvedData_interiorBoundaryTerm
    (D : SelectedInteriorAssemblyData I ω Face) :
    D.toArtificialFaceResolvedData.interiorBoundaryTerm =
      D.interiorBoundaryTerm := by
  simp [toArtificialFaceResolvedData]

end SelectedInteriorAssemblyData

end SelectedInteriorAssembly

end ArtificialFaceFieldReduction

end Stokes

end
