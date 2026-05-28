import Stokes.Global.InteriorPieceFamilyConstructor
import Stokes.Global.ArtificialFaceSelection
import Stokes.Global.PartitionCompactSupport

/-!
# Selected interior assembly

This file packages the interior side of the selected-partition mixed
constructor.  A selected partition supplies the active chart labels, localized
interior pieces supply the local Stokes package, and an explicit artificial-face
pairing supplies the cancellation input expected by the mixed global layer.

The geometric pairing is deliberately fielded: downstream files may construct
it from real face geometry, while this assembly layer only consumes the
algebraic `ArtificialFacePairingData`.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section SelectedInteriorAssembly

universe u w f

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Interior assembly data over a selected-box partition.

The mixed constructor sees one singleton interior piece over each selected
active chart.  The `localizedPieces` field carries the actual localized local
Stokes data, and the artificial-face pairing is required to match the localized
artificial boundary term on active singleton pieces.
-/
structure SelectedInteriorAssemblyData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n) (Face : Type f) where
  /-- Selected partition and selected interior boxes controlling the active indices. -/
  selectedPartition : SelectedBoxPartitionOfUnity I ω
  /-- Localized interior pieces indexed by chart labels. -/
  localizedPieces : LocalizedInteriorPieces (ι := M) I ω
  /-- The localized active set is exactly the selected partition active set. -/
  localized_active :
    localizedPieces.active = selectedPartition.active
  /-- The localized coefficients are the selected partition coefficients. -/
  localized_coefficient :
    localizedPieces.coefficient = fun i x => selectedPartition.partition i x
  /-- Pairing data for the selected artificial faces of the localized pieces. -/
  artificialPairing : ArtificialFacePairingData M Unit Face
  /-- The pairing uses the selected partition active set. -/
  artificialPairing_active :
    artificialPairing.activeCharts = selectedPartition.active
  /-- There is one singleton interior piece over each selected chart. -/
  artificialPairing_pieces :
    artificialPairing.interiorPieces = fun _ : M => ({()} : Finset Unit)
  /--
  The face sums recorded by the pairing are the localized artificial boundary
  terms on active singleton pieces.
  -/
  artificialPairing_boundaryTerm :
    ∀ i, i ∈ selectedPartition.active →
      ∀ q, q ∈ ({()} : Finset Unit) →
        localizedPieces.artificialBoundaryTerm i =
          artificialPairing.interiorBoundaryTerm i q

namespace SelectedInteriorAssemblyData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n} {Face : Type f}

/-- The active chart labels exposed to the mixed constructor. -/
def activeCharts (D : SelectedInteriorAssemblyData I ω Face) : Finset M :=
  D.selectedPartition.active

/-- Each selected active chart contributes a single interior piece. -/
def interiorPieces (_D : SelectedInteriorAssemblyData I ω Face) :
    M → Finset Unit :=
  fun _ => {()}

/-- Localized interior bulk term in the mixed-constructor shape. -/
def interiorBulkTerm (D : SelectedInteriorAssemblyData I ω Face) :
    M → Unit → Real :=
  fun i _ => D.localizedPieces.bulkTerm i

/-- Localized artificial-boundary term in the mixed-constructor shape. -/
def interiorBoundaryTerm (D : SelectedInteriorAssemblyData I ω Face) :
    M → Unit → Real :=
  fun i _ => D.localizedPieces.artificialBoundaryTerm i

@[simp]
theorem activeCharts_eq (D : SelectedInteriorAssemblyData I ω Face) :
    D.activeCharts = D.selectedPartition.active :=
  rfl

@[simp]
theorem interiorPieces_eq
    (D : SelectedInteriorAssemblyData I ω Face) (i : M) :
    D.interiorPieces i = ({()} : Finset Unit) :=
  rfl

@[simp]
theorem interiorBulkTerm_unit
    (D : SelectedInteriorAssemblyData I ω Face) (i : M) (q : Unit) :
    D.interiorBulkTerm i q = D.localizedPieces.bulkTerm i := by
  cases q
  rfl

@[simp]
theorem interiorBoundaryTerm_unit
    (D : SelectedInteriorAssemblyData I ω Face) (i : M) (q : Unit) :
    D.interiorBoundaryTerm i q =
      D.localizedPieces.artificialBoundaryTerm i := by
  cases q
  rfl

/-- The selected active set, viewed as the localized active set. -/
theorem mem_localized_active
    (D : SelectedInteriorAssemblyData I ω Face) {i : M}
    (hi : i ∈ D.activeCharts) :
    i ∈ D.localizedPieces.active := by
  simpa [activeCharts, D.localized_active] using hi

/-- Coefficients of localized pieces are the selected partition coefficients. -/
theorem localized_coefficient_apply
    (D : SelectedInteriorAssemblyData I ω Face) (i : M) :
    D.localizedPieces.coefficient i =
      fun x => D.selectedPartition.partition i x :=
  congrFun D.localized_coefficient i

/--
The localized interior pieces as the `MixedInteriorPackage` required by the
mixed constructor.
-/
def toMixedInteriorPackage
    (D : SelectedInteriorAssemblyData I ω Face) :
    MixedInteriorPackage I ω M Unit
      D.activeCharts D.interiorPieces
      D.interiorBulkTerm D.interiorBoundaryTerm where
  localStokes := by
    intro i hi q _hq
    cases q
    exact D.localizedPieces.localProjectEquality i
      (D.mem_localized_active hi)

/-- The local finite-sum equality supplied by the selected interior assembly. -/
theorem localFiniteSum
    (D : SelectedInteriorAssemblyData I ω Face) :
    (Finset.sum D.activeCharts fun i =>
        Finset.sum (D.interiorPieces i) fun q => D.interiorBulkTerm i q) =
      Finset.sum D.activeCharts fun i =>
        Finset.sum (D.interiorPieces i) fun q => D.interiorBoundaryTerm i q := by
  exact GlobalStokesData.sum_localPieces D.activeCharts D.interiorPieces
    D.interiorBulkTerm D.interiorBoundaryTerm
    D.toMixedInteriorPackage.localStokes

/--
Artificial-boundary cancellation data for the localized singleton pieces.

The underlying face pairing keeps its own face labels and pairing map; this
wrapper only aligns its face sums with the localized artificial-boundary term.
-/
def toArtificialBoundaryCancellationData
    (D : SelectedInteriorAssemblyData I ω Face) :
    ArtificialBoundaryCancellationData M Unit :=
  D.artificialPairing.toArtificialBoundaryCancellationData_of_boundaryTerm
    D.interiorBoundaryTerm
    (by
      intro i hi q hq
      have hiP : i ∈ D.selectedPartition.active := by
        simpa [D.artificialPairing_active] using hi
      have hqUnit : q ∈ ({()} : Finset Unit) := by
        cases q
        simp
      exact D.artificialPairing_boundaryTerm i hiP q hqUnit)

@[simp]
theorem toArtificialBoundaryCancellationData_activeCharts
    (D : SelectedInteriorAssemblyData I ω Face) :
    D.toArtificialBoundaryCancellationData.activeCharts = D.activeCharts := by
  simpa [toArtificialBoundaryCancellationData, activeCharts] using
    D.artificialPairing_active

@[simp]
theorem toArtificialBoundaryCancellationData_interiorPieces
    (D : SelectedInteriorAssemblyData I ω Face) :
    D.toArtificialBoundaryCancellationData.interiorPieces = D.interiorPieces := by
  simpa [toArtificialBoundaryCancellationData, interiorPieces] using
    D.artificialPairing_pieces

@[simp]
theorem toArtificialBoundaryCancellationData_interiorBoundaryTerm
    (D : SelectedInteriorAssemblyData I ω Face) :
    D.toArtificialBoundaryCancellationData.interiorBoundaryTerm =
      D.interiorBoundaryTerm :=
  rfl

/-- Artificial-boundary cancellation in the exact selected-interior shape. -/
theorem interiorBoundaryCancellation
    (D : SelectedInteriorAssemblyData I ω Face) :
    (Finset.sum D.activeCharts fun i =>
      Finset.sum (D.interiorPieces i) fun q => D.interiorBoundaryTerm i q) = 0 := by
  simpa using D.toArtificialBoundaryCancellationData.cancellation

/--
Constructor from an already packaged artificial-face pairing.  This keeps
downstream code independent of the structure-field order.
-/
def ofArtificialFacePairing
    (P : SelectedBoxPartitionOfUnity I ω)
    (localizedPieces : LocalizedInteriorPieces (ι := M) I ω)
    (localized_active : localizedPieces.active = P.active)
    (localized_coefficient :
      localizedPieces.coefficient = fun i x => P.partition i x)
    (artificialPairing : ArtificialFacePairingData M Unit Face)
    (artificialPairing_active :
      artificialPairing.activeCharts = P.active)
    (artificialPairing_pieces :
      artificialPairing.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (artificialPairing_boundaryTerm :
      ∀ i, i ∈ P.active →
        ∀ q, q ∈ ({()} : Finset Unit) →
          localizedPieces.artificialBoundaryTerm i =
            artificialPairing.interiorBoundaryTerm i q) :
    SelectedInteriorAssemblyData I ω Face where
  selectedPartition := P
  localizedPieces := localizedPieces
  localized_active := localized_active
  localized_coefficient := localized_coefficient
  artificialPairing := artificialPairing
  artificialPairing_active := artificialPairing_active
  artificialPairing_pieces := artificialPairing_pieces
  artificialPairing_boundaryTerm := artificialPairing_boundaryTerm

/--
Constructor from explicit artificial-face fields.  This is the fielded version
for the eventual geometric pairing of genuine selected artificial faces.
-/
def ofArtificialFaceFields
    (P : SelectedBoxPartitionOfUnity I ω)
    (localizedPieces : LocalizedInteriorPieces (ι := M) I ω)
    (localized_active : localizedPieces.active = P.active)
    (localized_coefficient :
      localizedPieces.coefficient = fun i x => P.partition i x)
    (faceIndices : M → Unit → Finset Face)
    (faceTerm : M → Unit → Face → Real)
    (boundaryTerm_eq_faceSum :
      ∀ i, i ∈ P.active →
        ∀ q, q ∈ ({()} : Finset Unit) →
          localizedPieces.artificialBoundaryTerm i =
            Finset.sum (faceIndices i q) fun f => faceTerm i q f)
    (pair : ArtificialFaceIndex M Unit Face → ArtificialFaceIndex M Unit Face)
    (pair_mem :
      ∀ r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit)) faceIndices →
          pair r ∈
            artificialFaceIndexSet P.active
              (fun _ : M => ({()} : Finset Unit)) faceIndices)
    (pair_involutive :
      ∀ r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit)) faceIndices →
          pair (pair r) = r)
    (paired_terms_cancel :
      ∀ r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit)) faceIndices →
          artificialFaceTerm faceTerm r + artificialFaceTerm faceTerm (pair r) = 0)
    (fixed_terms_zero :
      ∀ r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit)) faceIndices →
          pair r = r → artificialFaceTerm faceTerm r = 0) :
    SelectedInteriorAssemblyData I ω Face where
  selectedPartition := P
  localizedPieces := localizedPieces
  localized_active := localized_active
  localized_coefficient := localized_coefficient
  artificialPairing :=
    { activeCharts := P.active
      interiorPieces := fun _ : M => ({()} : Finset Unit)
      faceIndices := faceIndices
      faceTerm := faceTerm
      pair := pair
      pair_mem := pair_mem
      pair_involutive := pair_involutive
      paired_terms_cancel := paired_terms_cancel
      fixed_terms_zero := fixed_terms_zero }
  artificialPairing_active := rfl
  artificialPairing_pieces := rfl
  artificialPairing_boundaryTerm := by
    intro i hi q hq
    simpa [ArtificialFacePairingData.interiorBoundaryTerm] using
      boundaryTerm_eq_faceSum i hi q hq

/--
Chart-indexed specialization of `ofArtificialFaceFields`, useful when the
singleton interior piece is kept implicit.
-/
def ofChartArtificialFaceFields
    (P : SelectedBoxPartitionOfUnity I ω)
    (localizedPieces : LocalizedInteriorPieces (ι := M) I ω)
    (localized_active : localizedPieces.active = P.active)
    (localized_coefficient :
      localizedPieces.coefficient = fun i x => P.partition i x)
    (faceIndices : M → Finset Face)
    (faceTerm : M → Face → Real)
    (boundaryTerm_eq_faceSum :
      ∀ i, i ∈ P.active →
        localizedPieces.artificialBoundaryTerm i =
          Finset.sum (faceIndices i) fun f => faceTerm i f)
    (pair : ArtificialFaceIndex M Unit Face → ArtificialFaceIndex M Unit Face)
    (pair_mem :
      ∀ r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) →
          pair r ∈
            artificialFaceIndexSet P.active
              (fun _ : M => ({()} : Finset Unit))
              (fun i _ => faceIndices i))
    (pair_involutive :
      ∀ r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) →
          pair (pair r) = r)
    (paired_terms_cancel :
      ∀ r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) →
          artificialFaceTerm (fun i _ f => faceTerm i f) r +
            artificialFaceTerm (fun i _ f => faceTerm i f) (pair r) = 0)
    (fixed_terms_zero :
      ∀ r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) →
          pair r = r →
            artificialFaceTerm (fun i _ f => faceTerm i f) r = 0) :
    SelectedInteriorAssemblyData I ω Face :=
  ofArtificialFaceFields P localizedPieces localized_active
    localized_coefficient (fun i _ => faceIndices i)
    (fun i _ f => faceTerm i f)
    (by
      intro i hi q _hq
      cases q
      exact boundaryTerm_eq_faceSum i hi)
    pair pair_mem pair_involutive paired_terms_cancel fixed_terms_zero

end SelectedInteriorAssemblyData

namespace SelectedBoxPartitionOfUnity

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n} {Face : Type f}

/--
Build localized interior pieces indexed by a selected partition, once the
analytic localized piece for each coefficient has been supplied.
-/
def localizedInteriorPieces
    (P : SelectedBoxPartitionOfUnity I ω)
    (piece :
      ∀ i : M,
        LocalizedInteriorPiece I ω (fun j x => P.partition j x) i) :
    LocalizedInteriorPieces (ι := M) I ω where
  active := P.active
  coefficient := fun j x => P.partition j x
  piece := piece

@[simp]
theorem localizedInteriorPieces_active
    (P : SelectedBoxPartitionOfUnity I ω)
    (piece :
      ∀ i : M,
        LocalizedInteriorPiece I ω (fun j x => P.partition j x) i) :
    (P.localizedInteriorPieces piece).active = P.active :=
  rfl

@[simp]
theorem localizedInteriorPieces_coefficient
    (P : SelectedBoxPartitionOfUnity I ω)
    (piece :
      ∀ i : M,
        LocalizedInteriorPiece I ω (fun j x => P.partition j x) i) :
    (P.localizedInteriorPieces piece).coefficient =
      fun j x => P.partition j x :=
  rfl

/--
Selected-partition constructor for the full selected interior assembly from an
already packaged artificial-face pairing.
-/
def selectedInteriorAssemblyData
    (P : SelectedBoxPartitionOfUnity I ω)
    (localizedPieces : LocalizedInteriorPieces (ι := M) I ω)
    (localized_active : localizedPieces.active = P.active)
    (localized_coefficient :
      localizedPieces.coefficient = fun i x => P.partition i x)
    (artificialPairing : ArtificialFacePairingData M Unit Face)
    (artificialPairing_active :
      artificialPairing.activeCharts = P.active)
    (artificialPairing_pieces :
      artificialPairing.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (artificialPairing_boundaryTerm :
      ∀ i, i ∈ P.active →
        ∀ q, q ∈ ({()} : Finset Unit) →
          localizedPieces.artificialBoundaryTerm i =
            artificialPairing.interiorBoundaryTerm i q) :
    SelectedInteriorAssemblyData I ω Face :=
  SelectedInteriorAssemblyData.ofArtificialFacePairing P localizedPieces
    localized_active localized_coefficient artificialPairing
    artificialPairing_active artificialPairing_pieces
    artificialPairing_boundaryTerm

end SelectedBoxPartitionOfUnity

namespace CompactActiveExtendedBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n} {Face : Type f}

/--
Compact-active entry point: first use the existing selected-partition wrapper,
then assemble the localized interior package and artificial cancellation input.
-/
def toSelectedInteriorAssemblyData
    (D : CompactActiveExtendedBoxData I ω)
    (localizedPieces : LocalizedInteriorPieces (ι := M) I ω)
    (localized_active :
      localizedPieces.active = D.boxData.finiteActive.active)
    (localized_coefficient :
      localizedPieces.coefficient =
        fun i x => D.boxData.finiteActive.partition i x)
    (artificialPairing : ArtificialFacePairingData M Unit Face)
    (artificialPairing_active :
      artificialPairing.activeCharts = D.boxData.finiteActive.active)
    (artificialPairing_pieces :
      artificialPairing.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (artificialPairing_boundaryTerm :
      ∀ i, i ∈ D.boxData.finiteActive.active →
        ∀ q, q ∈ ({()} : Finset Unit) →
          localizedPieces.artificialBoundaryTerm i =
            artificialPairing.interiorBoundaryTerm i q) :
    SelectedInteriorAssemblyData I ω Face :=
  SelectedInteriorAssemblyData.ofArtificialFacePairing
    D.toSelectedBoxPartitionOfUnity localizedPieces
    (by simpa using localized_active)
    (by simpa using localized_coefficient)
    artificialPairing
    (by simpa using artificialPairing_active)
    artificialPairing_pieces
    (by
      intro i hi q hq
      exact artificialPairing_boundaryTerm i (by simpa using hi) q hq)

end CompactActiveExtendedBoxData

end SelectedInteriorAssembly

end Stokes

end
