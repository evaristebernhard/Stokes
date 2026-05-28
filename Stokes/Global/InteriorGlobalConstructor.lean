import Stokes.Global.Cancellation
import Stokes.Global.InteriorLocalStokes

/-!
# Interior-piece constructor for the final global package

This file instantiates `GlobalStokesData` from interior chart pieces only.  The
genuine boundary-piece family is empty, so the represented global boundary
integral is recorded as zero.  The artificial coordinate-box boundary
contributions from the interior pieces are supplied by an explicit cancellation
field.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section InteriorGlobalConstructor

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Interior project-local pieces in the exact shape needed to build
`GlobalStokesData` with no genuine boundary-chart pieces.

Each active piece carries an `InteriorLocalStokesData` package for the fixed
form `ω`.  The remaining fields record global bulk reconstruction, artificial
boundary cancellation, and the empty-boundary reconstruction.
-/
structure InteriorProjectLocalPieces {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in the interior-piece decomposition. -/
  activeCharts : Finset Chart
  /-- Interior-local pieces assigned to an active chart. -/
  interiorPieces : Chart → Finset Piece
  /-- Local Stokes data assigned to each recorded interior piece. -/
  localStokesData : Chart → Piece → InteriorLocalStokesData I ω
  /-- The global bulk integral represented by this interior-only package. -/
  globalBulkIntegral : Real
  /-- The global boundary integral represented by this interior-only package. -/
  globalBoundaryIntegral : Real
  /-- Reconstruction of the global bulk integral from recorded interior bulk terms. -/
  globalBulkIntegral_eq_interiorBulkSum :
    globalBulkIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (interiorPieces x) fun q =>
          (localStokesData x q).bulkTerm
  /-- Artificial boundary contributions from interior boxes cancel. -/
  artificialBoundaryCancellation :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun q =>
        (localStokesData x q).artificialBoundaryTerm) = 0
  /--
  Empty-boundary reconstruction.  Since this package has no genuine boundary
  pieces, the represented boundary integral is zero.
  -/
  globalBoundaryIntegral_eq_zero : globalBoundaryIntegral = 0

namespace InteriorProjectLocalPieces

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Bulk term of one recorded interior piece. -/
def interiorBulkTerm
    (D : InteriorProjectLocalPieces I ω Chart Piece) (x : Chart) (q : Piece) :
    Real :=
  (D.localStokesData x q).bulkTerm

/-- Artificial boundary term of one recorded interior piece. -/
def interiorBoundaryTerm
    (D : InteriorProjectLocalPieces I ω Chart Piece) (x : Chart) (q : Piece) :
    Real :=
  (D.localStokesData x q).artificialBoundaryTerm

/-- Sum of all recorded interior bulk terms. -/
def interiorBulkSum
    (D : InteriorProjectLocalPieces I ω Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.interiorPieces x) fun q => interiorBulkTerm D x q

/-- Sum of all recorded artificial interior-boundary terms. -/
def interiorBoundarySum
    (D : InteriorProjectLocalPieces I ω Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.interiorPieces x) fun q => interiorBoundaryTerm D x q

/-- Local Stokes for every active recorded interior piece. -/
theorem interiorLocalStokes
    (D : InteriorProjectLocalPieces I ω Chart Piece) :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.interiorPieces x →
        interiorBulkTerm D x q = interiorBoundaryTerm D x q := by
  intro x _hx q _hq
  exact (D.localStokesData x q).localEquality

/-- Summed interior local Stokes over all active recorded pieces. -/
theorem interiorBulkSum_eq_interiorBoundarySum
    (D : InteriorProjectLocalPieces I ω Chart Piece) :
    interiorBulkSum D = interiorBoundarySum D := by
  exact GlobalStokesData.sum_localPieces D.activeCharts D.interiorPieces
    (interiorBulkTerm D) (interiorBoundaryTerm D) D.interiorLocalStokes

/-- The recorded artificial-boundary cancellation in package-local notation. -/
theorem interiorBoundaryCancellation
    (D : InteriorProjectLocalPieces I ω Chart Piece) :
    interiorBoundarySum D = 0 := by
  simpa [interiorBoundarySum, interiorBoundaryTerm] using
    D.artificialBoundaryCancellation

/--
Use a standalone `ArtificialBoundaryCancellationData` package to fill the
interior cancellation field for a chosen per-piece boundary term.
-/
theorem interiorBoundaryCancellation_of_cancellationData
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset Piece)
    (interiorBoundaryTerm : Chart → Piece → Real)
    (C : ArtificialBoundaryCancellationData Chart Piece)
    (hactive : C.activeCharts = activeCharts)
    (hpieces : C.interiorPieces = interiorPieces)
    (hterm : C.interiorBoundaryTerm = interiorBoundaryTerm) :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun q => interiorBoundaryTerm x q) = 0 := by
  simpa [hactive, hpieces, hterm] using C.cancellation

/--
Constructor for `InteriorProjectLocalPieces` when artificial-boundary
cancellation is supplied by `ArtificialBoundaryCancellationData`.
-/
def ofCancellationData
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset Piece)
    (localStokesData : Chart → Piece → InteriorLocalStokesData I ω)
    (globalBulkIntegral globalBoundaryIntegral : Real)
    (globalBulkIntegral_eq_interiorBulkSum :
      globalBulkIntegral =
        Finset.sum activeCharts fun x =>
          Finset.sum (interiorPieces x) fun q =>
            (localStokesData x q).bulkTerm)
    (globalBoundaryIntegral_eq_zero : globalBoundaryIntegral = 0)
    (C : ArtificialBoundaryCancellationData Chart Piece)
    (hactive : C.activeCharts = activeCharts)
    (hpieces : C.interiorPieces = interiorPieces)
    (hterm :
      C.interiorBoundaryTerm =
        fun x q => (localStokesData x q).artificialBoundaryTerm) :
    InteriorProjectLocalPieces I ω Chart Piece where
  activeCharts := activeCharts
  interiorPieces := interiorPieces
  localStokesData := localStokesData
  globalBulkIntegral := globalBulkIntegral
  globalBoundaryIntegral := globalBoundaryIntegral
  globalBulkIntegral_eq_interiorBulkSum := globalBulkIntegral_eq_interiorBulkSum
  artificialBoundaryCancellation :=
    interiorBoundaryCancellation_of_cancellationData activeCharts interiorPieces
      (fun x q => (localStokesData x q).artificialBoundaryTerm)
      C hactive hpieces hterm
  globalBoundaryIntegral_eq_zero := globalBoundaryIntegral_eq_zero

/--
Instantiate the final `GlobalStokesData` package from interior pieces only.

The genuine boundary-piece type is `Empty`; artificial boundary terms are
carried by the interior side and cancelled by `D.artificialBoundaryCancellation`.
-/
def toGlobalStokesData
    (D : InteriorProjectLocalPieces I ω Chart Piece) :
    GlobalStokesData I ω Chart Piece Empty where
  activeCharts := D.activeCharts
  interiorPieces := D.interiorPieces
  boundaryPieces := fun _ => ∅
  interiorBulkTerm := interiorBulkTerm D
  interiorBoundaryTerm := interiorBoundaryTerm D
  boundaryBulkTerm := fun _ q => Empty.elim q
  boundaryBoundaryTerm := fun _ q => Empty.elim q
  boundaryPartitionTerm := fun _ q => Empty.elim q
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum := by
    simpa [interiorBulkTerm] using D.globalBulkIntegral_eq_interiorBulkSum
  interiorLocalStokes := D.interiorLocalStokes
  boundaryLocalStokes := by
    intro _x _hx q _hq
    cases q
  interiorBoundaryCancellation := by
    simpa [interiorBoundaryTerm] using D.artificialBoundaryCancellation
  chartChangeCancellation := by
    simp
  globalBoundaryIntegral_eq_boundaryPartitionSum := by
    simpa using D.globalBoundaryIntegral_eq_zero

/-- Interior-only global Stokes via the instantiated final package. -/
theorem stokes
    (D : InteriorProjectLocalPieces I ω Chart Piece) :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  GlobalStokesData.stokes D.toGlobalStokesData

end InteriorProjectLocalPieces

/-- Blueprint-facing final theorem wrapper for interior-only project-local pieces. -/
theorem interiorProjectLocalGlobalStokes
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    {Chart : Type c} {Piece : Type p}
    (D : InteriorProjectLocalPieces I ω Chart Piece) :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  InteriorProjectLocalPieces.stokes D

end InteriorGlobalConstructor

end Stokes

end
