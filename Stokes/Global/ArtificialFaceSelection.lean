import Stokes.Global.ArtificialFacePairing
import Stokes.Global.CompactActiveBoxes
import Stokes.Global.InteriorLocalStokes
import Stokes.Global.BoundaryPieces
import Stokes.Global.Cancellation

/-!
# Artificial face selections for selected interior boxes

This file is a bookkeeping layer between selected interior chart boxes and the
abstract artificial-face pairing API.

For each selected box, `SelectedBoxArtificialFaceData` records a finite family
of non-genuine face terms whose sum is the project-local artificial boundary
term of that box.  A family package then records a pairing of the flattened
chart/piece/face index set and exports the cancellation field expected by the
global Stokes assembly packages.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section SelectedBoxArtificialFaces

universe u w c p f

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Artificial face data for one selected interior chart box.

The face labels are intentionally abstract.  The geometric layer supplies the
finite face set, the signed face term, and the equality saying that these
selected non-genuine faces add up to the project-local artificial boundary term
of the box.
-/
structure SelectedBoxArtificialFaceData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n) (Face : Type f) where
  /-- Source chart for the selected interior box. -/
  sourceChart : M
  /-- Target chart for the selected interior box. -/
  targetChart : M
  /-- Lower corner of the selected coordinate box. -/
  lowerCorner : Fin (n + 1) → Real
  /-- Upper corner of the selected coordinate box. -/
  upperCorner : Fin (n + 1) → Real
  /-- The selected interior chart box. -/
  selectedBox :
    interiorChartSelectedBox I sourceChart targetChart ω lowerCorner upperCorner
  /-- Finite labels for the non-genuine faces of this selected box. -/
  faceIndices : Finset Face
  /-- Signed contribution of one selected artificial face. -/
  faceTerm : Face → Real
  /-- The selected face terms add up to the box artificial boundary term. -/
  boundaryTerm_eq_faceSum :
    projectInteriorBoundaryIntegral I sourceChart targetChart ω
        lowerCorner upperCorner =
      Finset.sum faceIndices fun f => faceTerm f

namespace SelectedBoxArtificialFaceData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n} {Face : Type f}

/-- The project-local artificial boundary term of the selected box. -/
def artificialBoundaryTerm
    (D : SelectedBoxArtificialFaceData I ω Face) : Real :=
  projectInteriorBoundaryIntegral I D.sourceChart D.targetChart ω
    D.lowerCorner D.upperCorner

/-- The selected finite sum of non-genuine face terms. -/
def faceSum (D : SelectedBoxArtificialFaceData I ω Face) : Real :=
  Finset.sum D.faceIndices fun f => D.faceTerm f

/-- The selected face sum is the project-local artificial boundary term. -/
theorem faceSum_eq_artificialBoundaryTerm
    (D : SelectedBoxArtificialFaceData I ω Face) :
    D.faceSum = D.artificialBoundaryTerm := by
  exact D.boundaryTerm_eq_faceSum.symm

/--
Use an extended-box witness to build the usual local Stokes data for this
selected box.
-/
def localStokesDataOfExtendedBox
    (D : SelectedBoxArtificialFaceData I ω Face)
    (hbox :
      interiorChartExtendedBox I D.sourceChart D.targetChart ω
        D.lowerCorner D.upperCorner) :
    InteriorLocalStokesData I ω :=
  InteriorLocalStokesData.ofExtendedBox D.sourceChart D.targetChart
    D.lowerCorner D.upperCorner hbox

@[simp]
theorem localStokesDataOfExtendedBox_artificialBoundaryTerm
    (D : SelectedBoxArtificialFaceData I ω Face)
    (hbox :
      interiorChartExtendedBox I D.sourceChart D.targetChart ω
        D.lowerCorner D.upperCorner) :
    (D.localStokesDataOfExtendedBox hbox).artificialBoundaryTerm =
      D.artificialBoundaryTerm :=
  rfl

end SelectedBoxArtificialFaceData

/--
Family of selected interior boxes with artificial face pairings.

The selected-box and face-sum facts are only required on active chart/piece
indices.  The pairing is stated on the flattened active face index set, so this
structure can be sent directly to `ArtificialFacePairingData`.
-/
structure SelectedBoxArtificialFaceFamilyData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (Chart : Type c) (Piece : Type p) (Face : Type f) where
  /-- Finite chart labels whose selected boxes contribute artificial faces. -/
  activeCharts : Finset Chart
  /-- Interior selected boxes assigned to each active chart label. -/
  interiorPieces : Chart → Finset Piece
  /-- Source chart for a selected box. -/
  sourceChart : Chart → Piece → M
  /-- Target chart for a selected box. -/
  targetChart : Chart → Piece → M
  /-- Lower corner of a selected box. -/
  lowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Upper corner of a selected box. -/
  upperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Selected interior boxes for all active chart/piece indices. -/
  selectedBox :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ interiorPieces x →
        interiorChartSelectedBox I (sourceChart x q) (targetChart x q) ω
          (lowerCorner x q) (upperCorner x q)
  /-- Finite labels for the non-genuine faces of an active selected box. -/
  faceIndices : Chart → Piece → Finset Face
  /-- Signed contribution of one selected artificial face. -/
  faceTerm : Chart → Piece → Face → Real
  /--
  The selected face terms add up to the project-local artificial boundary term
  of every active selected box.
  -/
  boundaryTerm_eq_faceSum :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ interiorPieces x →
        projectInteriorBoundaryIntegral I (sourceChart x q) (targetChart x q) ω
            (lowerCorner x q) (upperCorner x q) =
          Finset.sum (faceIndices x q) fun f => faceTerm x q f
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
  /-- Paired artificial face terms cancel. -/
  paired_terms_cancel :
    ∀ r, r ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      artificialFaceTerm faceTerm r + artificialFaceTerm faceTerm (pair r) = 0
  /-- Fixed artificial face terms are already zero. -/
  fixed_terms_zero :
    ∀ r, r ∈ artificialFaceIndexSet activeCharts interiorPieces faceIndices →
      pair r = r → artificialFaceTerm faceTerm r = 0

namespace SelectedBoxArtificialFaceFamilyData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p} {Face : Type f}

/-- The project-local artificial boundary term of a recorded selected box. -/
def projectBoundaryTerm
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart Piece Face)
    (x : Chart) (q : Piece) : Real :=
  projectInteriorBoundaryIntegral I (F.sourceChart x q) (F.targetChart x q) ω
    (F.lowerCorner x q) (F.upperCorner x q)

/-- The selected finite face sum for a recorded selected box. -/
def faceSumTerm
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart Piece Face)
    (x : Chart) (q : Piece) : Real :=
  Finset.sum (F.faceIndices x q) fun f => F.faceTerm x q f

/-- The active flattened artificial-face index set carried by the family. -/
def indexSet
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart Piece Face) :
    Finset (ArtificialFaceIndex Chart Piece Face) :=
  artificialFaceIndexSet F.activeCharts F.interiorPieces F.faceIndices

/-- The selected-box data for one active chart/piece index. -/
def pieceData
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart Piece Face)
    {x : Chart} (hx : x ∈ F.activeCharts)
    {q : Piece} (hq : q ∈ F.interiorPieces x) :
    SelectedBoxArtificialFaceData I ω Face where
  sourceChart := F.sourceChart x q
  targetChart := F.targetChart x q
  lowerCorner := F.lowerCorner x q
  upperCorner := F.upperCorner x q
  selectedBox := F.selectedBox x hx q hq
  faceIndices := F.faceIndices x q
  faceTerm := F.faceTerm x q
  boundaryTerm_eq_faceSum := F.boundaryTerm_eq_faceSum x hx q hq

/-- Active selected face sums agree with project-local artificial boundary terms. -/
theorem projectBoundaryTerm_eq_faceSumTerm
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart Piece Face)
    {x : Chart} (hx : x ∈ F.activeCharts)
    {q : Piece} (hq : q ∈ F.interiorPieces x) :
    F.projectBoundaryTerm x q = F.faceSumTerm x q :=
  F.boundaryTerm_eq_faceSum x hx q hq

/-- Forget the selected-box fields, retaining the abstract face-pairing package. -/
def toArtificialFacePairingData
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart Piece Face) :
    ArtificialFacePairingData Chart Piece Face where
  activeCharts := F.activeCharts
  interiorPieces := F.interiorPieces
  faceIndices := F.faceIndices
  faceTerm := F.faceTerm
  pair := F.pair
  pair_mem := F.pair_mem
  pair_involutive := F.pair_involutive
  paired_terms_cancel := F.paired_terms_cancel
  fixed_terms_zero := F.fixed_terms_zero

/-- The recorded face pairing cancels the total selected face sum. -/
theorem faceSumCancellation
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart Piece Face) :
    (Finset.sum F.activeCharts fun x =>
        Finset.sum (F.interiorPieces x) fun q =>
          Finset.sum (F.faceIndices x q) fun f => F.faceTerm x q f) = 0 :=
  F.toArtificialFacePairingData.faceSum_cancellation

/--
The recorded face pairing cancels the project-local artificial boundary terms
of the selected boxes.
-/
theorem projectBoundaryCancellation
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart Piece Face) :
    (Finset.sum F.activeCharts fun x =>
      Finset.sum (F.interiorPieces x) fun q => F.projectBoundaryTerm x q) = 0 :=
  F.toArtificialFacePairingData.interiorBoundaryCancellation_of_boundaryTerm_eq_faceSum
    (F.projectBoundaryTerm) (fun x hx q hq =>
      F.boundaryTerm_eq_faceSum x hx q hq)

/--
The raw `ArtificialBoundaryCancellationData` package whose per-piece term is
the selected face sum.
-/
def toArtificialBoundaryCancellationData_faceSum
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart Piece Face) :
    ArtificialBoundaryCancellationData Chart Piece :=
  F.toArtificialFacePairingData.toArtificialBoundaryCancellationData

/--
The `ArtificialBoundaryCancellationData` package whose per-piece term is the
project-local artificial boundary term of the selected box.
-/
def toArtificialBoundaryCancellationData
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart Piece Face) :
    ArtificialBoundaryCancellationData Chart Piece :=
  F.toArtificialFacePairingData.toArtificialBoundaryCancellationData_of_boundaryTerm
    F.projectBoundaryTerm (fun x hx q hq =>
      F.boundaryTerm_eq_faceSum x hx q hq)

/--
Build cancellation data for any external artificial-boundary term that agrees
with the selected-box project boundary term on active pieces.
-/
def toArtificialBoundaryCancellationData_of_boundaryTerm
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart Piece Face)
    (interiorBoundaryTerm : Chart → Piece → Real)
    (hterm :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.interiorPieces x →
          interiorBoundaryTerm x q = F.projectBoundaryTerm x q) :
    ArtificialBoundaryCancellationData Chart Piece where
  activeCharts := F.activeCharts
  interiorPieces := F.interiorPieces
  interiorBoundaryTerm := interiorBoundaryTerm
  cancellation := by
    calc
      (Finset.sum F.activeCharts fun x =>
          Finset.sum (F.interiorPieces x) fun q => interiorBoundaryTerm x q) =
          Finset.sum F.activeCharts fun x =>
            Finset.sum (F.interiorPieces x) fun q => F.projectBoundaryTerm x q := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        refine Finset.sum_congr rfl ?_
        intro q hq
        exact hterm x hx q hq
      _ = 0 := F.projectBoundaryCancellation

/--
Interior-boundary cancellation for any external term agreeing with the selected
box project boundary term on active pieces.
-/
theorem interiorBoundaryCancellation_of_boundaryTerm
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart Piece Face)
    (interiorBoundaryTerm : Chart → Piece → Real)
    (hterm :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.interiorPieces x →
          interiorBoundaryTerm x q = F.projectBoundaryTerm x q) :
    (Finset.sum F.activeCharts fun x =>
      Finset.sum (F.interiorPieces x) fun q => interiorBoundaryTerm x q) = 0 :=
  (F.toArtificialBoundaryCancellationData_of_boundaryTerm
    interiorBoundaryTerm hterm).cancellation

/--
Interior-boundary cancellation for artificial terms carried by local Stokes data
packages, when those terms are the selected-box project boundary terms.
-/
theorem interiorBoundaryCancellation_of_localStokesData
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart Piece Face)
    (localStokesData : Chart → Piece → InteriorLocalStokesData I ω)
    (hterm :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.interiorPieces x →
          (localStokesData x q).artificialBoundaryTerm =
            F.projectBoundaryTerm x q) :
    (Finset.sum F.activeCharts fun x =>
      Finset.sum (F.interiorPieces x) fun q =>
        (localStokesData x q).artificialBoundaryTerm) = 0 :=
  F.interiorBoundaryCancellation_of_boundaryTerm
    (fun x q => (localStokesData x q).artificialBoundaryTerm) hterm

/--
Cancellation data for artificial terms carried by local Stokes data packages.
-/
def toArtificialBoundaryCancellationData_of_localStokesData
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart Piece Face)
    (localStokesData : Chart → Piece → InteriorLocalStokesData I ω)
    (hterm :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.interiorPieces x →
          (localStokesData x q).artificialBoundaryTerm =
            F.projectBoundaryTerm x q) :
    ArtificialBoundaryCancellationData Chart Piece :=
  F.toArtificialBoundaryCancellationData_of_boundaryTerm
    (fun x q => (localStokesData x q).artificialBoundaryTerm) hterm

end SelectedBoxArtificialFaceFamilyData

namespace SelectedBoxPartitionOfUnity

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n} {Face : Type f}

/--
View a selected-box partition as a selected artificial-face family with one
interior piece per active chart index.
-/
def toSelectedBoxArtificialFaceFamilyData
    (P : SelectedBoxPartitionOfUnity I ω)
    (faceIndices : M → Finset Face)
    (faceTerm : M → Face → Real)
    (boundaryTerm_eq_faceSum :
      ∀ i, i ∈ P.active →
        projectInteriorBoundaryIntegral I i i ω (P.lower i) (P.upper i) =
          Finset.sum (faceIndices i) fun f => faceTerm i f)
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
    (paired_terms_cancel :
      ∀ r,
        r ∈ artificialFaceIndexSet P.active (fun _ : M => Finset.univ)
            (fun i _ => faceIndices i) →
          artificialFaceTerm (fun i _ f => faceTerm i f) r +
            artificialFaceTerm (fun i _ f => faceTerm i f) (pair r) = 0)
    (fixed_terms_zero :
      ∀ r,
        r ∈ artificialFaceIndexSet P.active (fun _ : M => Finset.univ)
            (fun i _ => faceIndices i) →
          pair r = r →
            artificialFaceTerm (fun i _ f => faceTerm i f) r = 0) :
    SelectedBoxArtificialFaceFamilyData I ω M PUnit Face where
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
  faceTerm := fun i _ f => faceTerm i f
  boundaryTerm_eq_faceSum := by
    intro i hi q _hq
    cases q
    exact boundaryTerm_eq_faceSum i hi
  pair := pair
  pair_mem := pair_mem
  pair_involutive := pair_involutive
  paired_terms_cancel := paired_terms_cancel
  fixed_terms_zero := fixed_terms_zero

end SelectedBoxPartitionOfUnity

namespace CompactActiveExtendedBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n} {Face : Type f}

/--
View compact active extended boxes as a selected artificial-face family with one
interior piece per active chart index.
-/
def toSelectedBoxArtificialFaceFamilyData
    (D : CompactActiveExtendedBoxData I ω)
    (faceIndices : M → Finset Face)
    (faceTerm : M → Face → Real)
    (boundaryTerm_eq_faceSum :
      ∀ i, i ∈ D.boxData.finiteActive.active →
        projectInteriorBoundaryIntegral I i i ω
            (D.boxData.lower i) (D.boxData.upper i) =
          Finset.sum (faceIndices i) fun f => faceTerm i f)
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
    (paired_terms_cancel :
      ∀ r,
        r ∈ artificialFaceIndexSet D.boxData.finiteActive.active
            (fun _ : M => Finset.univ) (fun i _ => faceIndices i) →
          artificialFaceTerm (fun i _ f => faceTerm i f) r +
            artificialFaceTerm (fun i _ f => faceTerm i f) (pair r) = 0)
    (fixed_terms_zero :
      ∀ r,
        r ∈ artificialFaceIndexSet D.boxData.finiteActive.active
            (fun _ : M => Finset.univ) (fun i _ => faceIndices i) →
          pair r = r →
            artificialFaceTerm (fun i _ f => faceTerm i f) r = 0) :
    SelectedBoxArtificialFaceFamilyData I ω M PUnit Face where
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
  faceTerm := fun i _ f => faceTerm i f
  boundaryTerm_eq_faceSum := by
    intro i hi q _hq
    cases q
    exact boundaryTerm_eq_faceSum i hi
  pair := pair
  pair_mem := pair_mem
  pair_involutive := pair_involutive
  paired_terms_cancel := paired_terms_cancel
  fixed_terms_zero := fixed_terms_zero

end CompactActiveExtendedBoxData

namespace GlobalStokesAssemblyData

variable {BoundaryPiece : Type*}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {InteriorPiece : Type p} {Face : Type f}

/--
Selected artificial-face family data fills the assembly cancellation field for
the selected-box project boundary terms.
-/
theorem interiorBoundaryCancellation_of_selectedBoxArtificialFaces
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart InteriorPiece Face) :
    (Finset.sum F.activeCharts fun x =>
      Finset.sum (F.interiorPieces x) fun q => F.projectBoundaryTerm x q) = 0 :=
  F.projectBoundaryCancellation

/--
Selected artificial-face family data fills the assembly cancellation field for
any term agreeing with the selected-box project boundary term.
-/
theorem interiorBoundaryCancellation_of_selectedBoxArtificialFaces_boundaryTerm
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart InteriorPiece Face)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (hterm :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.interiorPieces x →
          interiorBoundaryTerm x q = F.projectBoundaryTerm x q) :
    (Finset.sum F.activeCharts fun x =>
      Finset.sum (F.interiorPieces x) fun q => interiorBoundaryTerm x q) = 0 :=
  F.interiorBoundaryCancellation_of_boundaryTerm interiorBoundaryTerm hterm

end GlobalStokesAssemblyData

namespace GlobalStokesData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {InteriorPiece : Type p} {Face : Type f}

/--
Selected artificial-face family data fills the final global cancellation field
for the selected-box project boundary terms.
-/
theorem interiorBoundaryCancellation_of_selectedBoxArtificialFaces
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart InteriorPiece Face) :
    (Finset.sum F.activeCharts fun x =>
      Finset.sum (F.interiorPieces x) fun q => F.projectBoundaryTerm x q) = 0 :=
  F.projectBoundaryCancellation

/--
Selected artificial-face family data fills the final global cancellation field
for any term agreeing with the selected-box project boundary term.
-/
theorem interiorBoundaryCancellation_of_selectedBoxArtificialFaces_boundaryTerm
    (F : SelectedBoxArtificialFaceFamilyData I ω Chart InteriorPiece Face)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (hterm :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.interiorPieces x →
          interiorBoundaryTerm x q = F.projectBoundaryTerm x q) :
    (Finset.sum F.activeCharts fun x =>
      Finset.sum (F.interiorPieces x) fun q => interiorBoundaryTerm x q) = 0 :=
  F.interiorBoundaryCancellation_of_boundaryTerm interiorBoundaryTerm hterm

end GlobalStokesData

end SelectedBoxArtificialFaces

end Stokes

end
