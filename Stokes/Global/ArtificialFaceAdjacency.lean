import Stokes.Global.ArtificialFaceGeometry
import Stokes.Global.ArtificialFaceSelection
import Stokes.Global.CompactActiveBoxes
import Stokes.Global.InteriorLocalStokes

/-!
# Artificial-face adjacency for selected interior boxes

This file records the geometric input that selected interior chart-box faces
are adjacent in opposite coordinate directions.  The data is intentionally
thin: it packages selected boxes, coordinate-face labels, geometric face
identifications, unsigned face terms, and an involutive pairing of the flattened
active face index set.

The main wrappers send this adjacency package to
`ArtificialFaceGeometryData` and to `SelectedBoxArtificialFaceFamilyData`.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section ArtificialFaceAdjacency

universe u w c p f g

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Adjacency data for artificial faces of selected interior chart boxes.

The field `paired_coordinateFace_opposite` is the geometric sign convention:
paired selected faces are the two opposite sides of the same coordinate
direction.  The fields `paired_geometricFace_eq` and
`paired_unsignedFaceTerm_eq` record that the same underlying face is integrated
with equal unsigned magnitude.
-/
structure AdjacentSelectedFacesData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (Chart : Type c) (Piece : Type p) (Face : Type f)
    (Geometry : Type g) where
  /-- Finite chart labels whose selected boxes contribute artificial faces. -/
  activeCharts : Finset Chart
  /-- Selected interior pieces assigned to each active chart label. -/
  interiorPieces : Chart → Finset Piece
  /-- Source chart for a selected interior box. -/
  sourceChart : Chart → Piece → M
  /-- Target chart for a selected interior box. -/
  targetChart : Chart → Piece → M
  /-- Lower corner of a selected coordinate box. -/
  lowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Upper corner of a selected coordinate box. -/
  upperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Selected interior boxes for all active chart/piece indices. -/
  selectedBox :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ interiorPieces x →
        interiorChartSelectedBox I (sourceChart x q) (targetChart x q) ω
          (lowerCorner x q) (upperCorner x q)
  /-- Finite labels for the artificial faces of an active selected box. -/
  faceIndices : Chart → Piece → Finset Face
  /-- Coordinate side and normal direction of each artificial face. -/
  coordinateFace : Chart → Piece → Face → ArtificialCoordinateFace n
  /-- Underlying geometric face, forgetting its orientation. -/
  geometricFace : Chart → Piece → Face → Geometry
  /-- Unsigned integral or magnitude carried by the face. -/
  unsignedFaceTerm : Chart → Piece → Face → Real
  /--
  The signed selected face terms add up to the project-local artificial
  boundary term of every active selected box.
  -/
  boundaryTerm_eq_faceSum :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ interiorPieces x →
        projectInteriorBoundaryIntegral I (sourceChart x q) (targetChart x q) ω
            (lowerCorner x q) (upperCorner x q) =
          Finset.sum (faceIndices x q) fun f =>
            (coordinateFace x q f).sign * unsignedFaceTerm x q f
  /-- Pairing of flattened active artificial faces. -/
  pair :
    ArtificialFaceIndex Chart Piece Face →
      ArtificialFaceIndex Chart Piece Face
  /-- The pairing preserves the active flattened finite index set. -/
  pair_mem :
    ∀ r, r ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      pair r ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices
  /-- The pairing is an involution on active artificial faces. -/
  pair_involutive :
    ∀ r, r ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      pair (pair r) = r
  /-- Paired faces are opposite coordinate faces. -/
  paired_coordinateFace_opposite :
    ∀ r, r ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      coordinateFace (pair r).1.1 (pair r).1.2 (pair r).2 =
        (coordinateFace r.1.1 r.1.2 r.2).opposite
  /-- Paired faces represent the same underlying geometric face. -/
  paired_geometricFace_eq :
    ∀ r, r ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      geometricFace r.1.1 r.1.2 r.2 =
        geometricFace (pair r).1.1 (pair r).1.2 (pair r).2
  /-- Paired faces have equal unsigned terms. -/
  paired_unsignedFaceTerm_eq :
    ∀ r, r ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      artificialFaceTerm unsignedFaceTerm r =
        artificialFaceTerm unsignedFaceTerm (pair r)
  /-- Fixed artificial face terms are already zero. -/
  fixed_terms_zero :
    ∀ r, r ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      pair r = r →
        artificialFaceTerm
          (fun x q f => (coordinateFace x q f).sign * unsignedFaceTerm x q f) r = 0

namespace AdjacentSelectedFacesData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p} {Face : Type f}
variable {Geometry : Type g}

/-- The signed contribution of one selected artificial face. -/
def faceTerm
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry) :
    Chart → Piece → Face → Real :=
  fun x q f => (D.coordinateFace x q f).sign * D.unsignedFaceTerm x q f

/-- The active flattened artificial-face index set carried by the package. -/
def indexSet
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry) :
    Finset (ArtificialFaceIndex Chart Piece Face) :=
  artificialFaceIndexSet D.activeCharts D.interiorPieces D.faceIndices

/-- The paired flattened artificial face. -/
def pairedFace
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry)
    (r : ArtificialFaceIndex Chart Piece Face) :
    ArtificialFaceIndex Chart Piece Face :=
  D.pair r

/-- The coordinate face attached to a flattened selected artificial face. -/
def coordinateFaceOfIndex
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry)
    (r : ArtificialFaceIndex Chart Piece Face) :
    ArtificialCoordinateFace n :=
  D.coordinateFace r.1.1 r.1.2 r.2

/-- The underlying geometric face attached to a flattened selected artificial face. -/
def geometricFaceOfIndex
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry)
    (r : ArtificialFaceIndex Chart Piece Face) : Geometry :=
  D.geometricFace r.1.1 r.1.2 r.2

/-- The paired coordinate face is the opposite coordinate face. -/
theorem paired_coordinateFace_eq_opposite
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry)
    {r : ArtificialFaceIndex Chart Piece Face} (hr : r ∈ D.indexSet) :
    D.coordinateFaceOfIndex (D.pairedFace r) =
      (D.coordinateFaceOfIndex r).opposite :=
  D.paired_coordinateFace_opposite r hr

/-- Paired active faces have the same coordinate dimension. -/
theorem paired_faceDimension_eq
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry)
    {r : ArtificialFaceIndex Chart Piece Face} (hr : r ∈ D.indexSet) :
    (D.coordinateFaceOfIndex r).faceDimension =
      (D.coordinateFaceOfIndex (D.pairedFace r)).faceDimension := by
  rw [D.paired_coordinateFace_eq_opposite hr]
  rfl

/-- Paired active faces have opposite coordinate signs. -/
theorem paired_sign_cancel
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry)
    {r : ArtificialFaceIndex Chart Piece Face} (hr : r ∈ D.indexSet) :
    (D.coordinateFaceOfIndex r).sign +
      (D.coordinateFaceOfIndex (D.pairedFace r)).sign = 0 := by
  rw [D.paired_coordinateFace_eq_opposite hr]
  exact ArtificialCoordinateFace.sign_add_sign_opposite (D.coordinateFaceOfIndex r)

/-- Paired active faces represent the same underlying geometric face. -/
theorem paired_geometricFace_eq'
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry)
    {r : ArtificialFaceIndex Chart Piece Face} (hr : r ∈ D.indexSet) :
    D.geometricFaceOfIndex r = D.geometricFaceOfIndex (D.pairedFace r) :=
  D.paired_geometricFace_eq r hr

/-- Package the adjacency data as geometric artificial-face cancellation data. -/
def toArtificialFaceGeometryData
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry) :
    ArtificialFaceGeometryData Chart Piece Face (Fin (n + 1)) Geometry :=
  ArtificialFaceGeometryData.ofCoordinatePairing D.activeCharts D.interiorPieces
    D.faceIndices D.coordinateFace D.geometricFace D.unsignedFaceTerm D.pair
    D.pair_mem D.pair_involutive D.paired_coordinateFace_opposite
    D.paired_geometricFace_eq D.paired_unsignedFaceTerm_eq D.fixed_terms_zero

/-- Forget the selected-box fields, retaining geometric artificial-face data. -/
def toArtificialFacePairingData
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry) :
    ArtificialFacePairingData Chart Piece Face :=
  D.toArtificialFaceGeometryData.toArtificialFacePairingData

/-- The geometric wrapper has the same active index set. -/
theorem toArtificialFaceGeometryData_indexSet
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry) :
    D.toArtificialFaceGeometryData.indexSet = D.indexSet :=
  rfl

/-- The geometric wrapper has the same signed face term. -/
theorem toArtificialFaceGeometryData_faceTerm
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry) :
    D.toArtificialFaceGeometryData.faceTerm = D.faceTerm :=
  rfl

/-- Package the adjacency data as selected-box artificial-face family data. -/
def toSelectedBoxArtificialFaceFamilyData
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry) :
    SelectedBoxArtificialFaceFamilyData I ω Chart Piece Face where
  activeCharts := D.activeCharts
  interiorPieces := D.interiorPieces
  sourceChart := D.sourceChart
  targetChart := D.targetChart
  lowerCorner := D.lowerCorner
  upperCorner := D.upperCorner
  selectedBox := D.selectedBox
  faceIndices := D.faceIndices
  faceTerm := D.faceTerm
  boundaryTerm_eq_faceSum := D.boundaryTerm_eq_faceSum
  pair := D.pair
  pair_mem := D.pair_mem
  pair_involutive := D.pair_involutive
  paired_terms_cancel := by
    intro r hr
    exact D.toArtificialFacePairingData.paired_terms_cancel r hr
  fixed_terms_zero := by
    intro r hr hfix
    exact D.fixed_terms_zero r hr hfix

/-- The selected-family wrapper has the same active index set. -/
theorem toSelectedBoxArtificialFaceFamilyData_indexSet
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry) :
    D.toSelectedBoxArtificialFaceFamilyData.indexSet = D.indexSet :=
  rfl

/-- The selected-family wrapper has the same project-boundary term. -/
theorem toSelectedBoxArtificialFaceFamilyData_projectBoundaryTerm
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry)
    (x : Chart) (q : Piece) :
    D.toSelectedBoxArtificialFaceFamilyData.projectBoundaryTerm x q =
      projectInteriorBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
        (D.lowerCorner x q) (D.upperCorner x q) :=
  rfl

/--
The adjacency pairing cancels the selected artificial-face sums, via the
selected-family wrapper.
-/
theorem faceSumCancellation
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.interiorPieces x) fun q =>
          Finset.sum (D.faceIndices x q) fun f => D.faceTerm x q f) = 0 :=
  D.toSelectedBoxArtificialFaceFamilyData.faceSumCancellation

/--
The adjacency pairing cancels the project-local artificial boundary terms of
the selected boxes.
-/
theorem projectBoundaryCancellation
    (D : AdjacentSelectedFacesData I ω Chart Piece Face Geometry) :
    (Finset.sum D.activeCharts fun x =>
      Finset.sum (D.interiorPieces x) fun q =>
        projectInteriorBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
          (D.lowerCorner x q) (D.upperCorner x q)) = 0 :=
  D.toSelectedBoxArtificialFaceFamilyData.projectBoundaryCancellation

end AdjacentSelectedFacesData

namespace SelectedBoxPartitionOfUnity

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Face : Type f} {Geometry : Type g}

/--
View a selected-box partition as adjacency data with one interior piece per
active chart index.
-/
def toAdjacentSelectedFacesData
    (P : SelectedBoxPartitionOfUnity I ω)
    (faceIndices : M → Finset Face)
    (coordinateFace : M → Face → ArtificialCoordinateFace n)
    (geometricFace : M → Face → Geometry)
    (unsignedFaceTerm : M → Face → Real)
    (boundaryTerm_eq_faceSum :
      ∀ i, i ∈ P.active →
        projectInteriorBoundaryIntegral I i i ω (P.lower i) (P.upper i) =
          Finset.sum (faceIndices i) fun f =>
            (coordinateFace i f).sign * unsignedFaceTerm i f)
    (pair : ArtificialFaceIndex M PUnit Face → ArtificialFaceIndex M PUnit Face)
    (pair_mem :
      ∀ r,
        r ∈ artificialFaceIndexSet P.active (fun _ : M => Finset.univ)
            (fun i _ => faceIndices i) →
          pair r ∈
            artificialFaceIndexSet P.active (fun _ : M => Finset.univ)
              (fun i _ => faceIndices i))
    (pair_involutive :
      ∀ r,
        r ∈ artificialFaceIndexSet P.active (fun _ : M => Finset.univ)
            (fun i _ => faceIndices i) →
          pair (pair r) = r)
    (paired_coordinateFace_opposite :
      ∀ r,
        r ∈ artificialFaceIndexSet P.active (fun _ : M => Finset.univ)
            (fun i _ => faceIndices i) →
          coordinateFace (pair r).1.1 (pair r).2 =
            (coordinateFace r.1.1 r.2).opposite)
    (paired_geometricFace_eq :
      ∀ r,
        r ∈ artificialFaceIndexSet P.active (fun _ : M => Finset.univ)
            (fun i _ => faceIndices i) →
          geometricFace r.1.1 r.2 = geometricFace (pair r).1.1 (pair r).2)
    (paired_unsignedFaceTerm_eq :
      ∀ r,
        r ∈ artificialFaceIndexSet P.active (fun _ : M => Finset.univ)
            (fun i _ => faceIndices i) →
          artificialFaceTerm (fun i _ f => unsignedFaceTerm i f) r =
            artificialFaceTerm (fun i _ f => unsignedFaceTerm i f) (pair r))
    (fixed_terms_zero :
      ∀ r,
        r ∈ artificialFaceIndexSet P.active (fun _ : M => Finset.univ)
            (fun i _ => faceIndices i) →
          pair r = r →
            artificialFaceTerm
              (fun i _ f => (coordinateFace i f).sign * unsignedFaceTerm i f) r = 0) :
    AdjacentSelectedFacesData I ω M PUnit Face Geometry where
  activeCharts := P.active
  interiorPieces := fun _ => Finset.univ
  sourceChart := fun i _ => i
  targetChart := fun i _ => i
  lowerCorner := fun i _ => P.lower i
  upperCorner := fun i _ => P.upper i
  selectedBox := by
    intro i hi q _hq
    cases q
    exact P.selectedBox hi
  faceIndices := fun i _ => faceIndices i
  coordinateFace := fun i _ f => coordinateFace i f
  geometricFace := fun i _ f => geometricFace i f
  unsignedFaceTerm := fun i _ f => unsignedFaceTerm i f
  boundaryTerm_eq_faceSum := by
    intro i hi q _hq
    cases q
    exact boundaryTerm_eq_faceSum i hi
  pair := pair
  pair_mem := pair_mem
  pair_involutive := pair_involutive
  paired_coordinateFace_opposite := paired_coordinateFace_opposite
  paired_geometricFace_eq := paired_geometricFace_eq
  paired_unsignedFaceTerm_eq := paired_unsignedFaceTerm_eq
  fixed_terms_zero := fixed_terms_zero

end SelectedBoxPartitionOfUnity

namespace CompactActiveExtendedBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Face : Type f} {Geometry : Type g}

/--
View compact active extended boxes as adjacency data with one interior piece per
active chart index.
-/
def toAdjacentSelectedFacesData
    (D : CompactActiveExtendedBoxData I ω)
    (faceIndices : M → Finset Face)
    (coordinateFace : M → Face → ArtificialCoordinateFace n)
    (geometricFace : M → Face → Geometry)
    (unsignedFaceTerm : M → Face → Real)
    (boundaryTerm_eq_faceSum :
      ∀ i, i ∈ D.boxData.finiteActive.active →
        projectInteriorBoundaryIntegral I i i ω
            (D.boxData.lower i) (D.boxData.upper i) =
          Finset.sum (faceIndices i) fun f =>
            (coordinateFace i f).sign * unsignedFaceTerm i f)
    (pair : ArtificialFaceIndex M PUnit Face → ArtificialFaceIndex M PUnit Face)
    (pair_mem :
      ∀ r,
        r ∈ artificialFaceIndexSet D.boxData.finiteActive.active
            (fun _ : M => Finset.univ) (fun i _ => faceIndices i) →
          pair r ∈
            artificialFaceIndexSet D.boxData.finiteActive.active
              (fun _ : M => Finset.univ) (fun i _ => faceIndices i))
    (pair_involutive :
      ∀ r,
        r ∈ artificialFaceIndexSet D.boxData.finiteActive.active
            (fun _ : M => Finset.univ) (fun i _ => faceIndices i) →
          pair (pair r) = r)
    (paired_coordinateFace_opposite :
      ∀ r,
        r ∈ artificialFaceIndexSet D.boxData.finiteActive.active
            (fun _ : M => Finset.univ) (fun i _ => faceIndices i) →
          coordinateFace (pair r).1.1 (pair r).2 =
            (coordinateFace r.1.1 r.2).opposite)
    (paired_geometricFace_eq :
      ∀ r,
        r ∈ artificialFaceIndexSet D.boxData.finiteActive.active
            (fun _ : M => Finset.univ) (fun i _ => faceIndices i) →
          geometricFace r.1.1 r.2 = geometricFace (pair r).1.1 (pair r).2)
    (paired_unsignedFaceTerm_eq :
      ∀ r,
        r ∈ artificialFaceIndexSet D.boxData.finiteActive.active
            (fun _ : M => Finset.univ) (fun i _ => faceIndices i) →
          artificialFaceTerm (fun i _ f => unsignedFaceTerm i f) r =
            artificialFaceTerm (fun i _ f => unsignedFaceTerm i f) (pair r))
    (fixed_terms_zero :
      ∀ r,
        r ∈ artificialFaceIndexSet D.boxData.finiteActive.active
            (fun _ : M => Finset.univ) (fun i _ => faceIndices i) →
          pair r = r →
            artificialFaceTerm
              (fun i _ f => (coordinateFace i f).sign * unsignedFaceTerm i f) r = 0) :
    AdjacentSelectedFacesData I ω M PUnit Face Geometry where
  activeCharts := D.boxData.finiteActive.active
  interiorPieces := fun _ => Finset.univ
  sourceChart := fun i _ => i
  targetChart := fun i _ => i
  lowerCorner := fun i _ => D.boxData.lower i
  upperCorner := fun i _ => D.boxData.upper i
  selectedBox := by
    intro i hi q _hq
    cases q
    exact D.interiorChartSelectedBox hi
  faceIndices := fun i _ => faceIndices i
  coordinateFace := fun i _ f => coordinateFace i f
  geometricFace := fun i _ f => geometricFace i f
  unsignedFaceTerm := fun i _ f => unsignedFaceTerm i f
  boundaryTerm_eq_faceSum := by
    intro i hi q _hq
    cases q
    exact boundaryTerm_eq_faceSum i hi
  pair := pair
  pair_mem := pair_mem
  pair_involutive := pair_involutive
  paired_coordinateFace_opposite := paired_coordinateFace_opposite
  paired_geometricFace_eq := paired_geometricFace_eq
  paired_unsignedFaceTerm_eq := paired_unsignedFaceTerm_eq
  fixed_terms_zero := fixed_terms_zero

end CompactActiveExtendedBoxData

end ArtificialFaceAdjacency

end Stokes

end
