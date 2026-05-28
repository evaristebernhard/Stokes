import Stokes.Global.BoundaryGlobalConstructor
import Stokes.Global.ReconstructionWrappers
import Stokes.BoundaryChart.BoundaryPieceConvenience

/-!
# Boundary integral finite-sum reconstruction

This file isolates the boundary-only reconstruction field used by the global
Stokes packages.

The intended mathematical input is: the manifold boundary integral represented
by a package is equal to the finite sum of the selected boundary-piece terms.
The local Stokes, chart-change, and bulk reconstruction data live in the
neighboring constructor files; this module only packages and projects the
boundary finite-sum equality.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryIntegralReconstruction

universe u v w c i p

/-- Finite sum of the selected boundary-piece terms. -/
def selectedBoundaryPieceSum {Chart : Type c} {Piece : Type p}
    (activeCharts : Finset Chart)
    (selectedBoundaryPieces : Chart → Finset Piece)
    (selectedBoundaryTerm : Chart → Piece → Real) : Real :=
  Finset.sum activeCharts fun x =>
    Finset.sum (selectedBoundaryPieces x) fun q => selectedBoundaryTerm x q

/--
Boundary integral reconstruction data for a fixed finite family.

This is the compact API for the analytic theorem still missing at the global
integration layer: the represented manifold boundary integral is the finite sum
of the selected boundary-piece terms.
-/
structure BoundaryIntegralReconstructionData {Chart : Type c} {Piece : Type p}
    (activeCharts : Finset Chart)
    (selectedBoundaryPieces : Chart → Finset Piece)
    (selectedBoundaryTerm : Chart → Piece → Real)
    (manifoldBoundaryIntegral : Real) where
  /-- The manifold boundary integral reconstructed from selected boundary pieces. -/
  manifoldBoundaryIntegral_eq_selectedBoundarySum :
    manifoldBoundaryIntegral =
      selectedBoundaryPieceSum activeCharts selectedBoundaryPieces selectedBoundaryTerm

namespace BoundaryIntegralReconstructionData

variable {Chart : Type c} {Piece : Type p}
variable {activeCharts : Finset Chart}
variable {selectedBoundaryPieces : Chart → Finset Piece}
variable {selectedBoundaryTerm : Chart → Piece → Real}
variable {manifoldBoundaryIntegral : Real}

/-- Build reconstruction data from an already-proved finite-sum equality. -/
def ofEq
    (h :
      manifoldBoundaryIntegral =
        selectedBoundaryPieceSum activeCharts selectedBoundaryPieces selectedBoundaryTerm) :
    BoundaryIntegralReconstructionData activeCharts selectedBoundaryPieces
      selectedBoundaryTerm manifoldBoundaryIntegral where
  manifoldBoundaryIntegral_eq_selectedBoundarySum := h

/-- The tautological reconstruction package whose integral is defined as the finite sum. -/
def ofSelectedBoundaryPieceSum
    (activeCharts : Finset Chart)
    (selectedBoundaryPieces : Chart → Finset Piece)
    (selectedBoundaryTerm : Chart → Piece → Real) :
    BoundaryIntegralReconstructionData activeCharts selectedBoundaryPieces
      selectedBoundaryTerm
      (selectedBoundaryPieceSum activeCharts selectedBoundaryPieces selectedBoundaryTerm) where
  manifoldBoundaryIntegral_eq_selectedBoundarySum := rfl

/-- Named projection of the reconstruction field. -/
theorem eq_selectedBoundarySum
    (R :
      BoundaryIntegralReconstructionData activeCharts selectedBoundaryPieces
        selectedBoundaryTerm manifoldBoundaryIntegral) :
    manifoldBoundaryIntegral =
      selectedBoundaryPieceSum activeCharts selectedBoundaryPieces selectedBoundaryTerm :=
  R.manifoldBoundaryIntegral_eq_selectedBoundarySum

/-- Expanded finite-sum form of the reconstruction field. -/
theorem eq_selectedBoundarySum_expanded
    (R :
      BoundaryIntegralReconstructionData activeCharts selectedBoundaryPieces
        selectedBoundaryTerm manifoldBoundaryIntegral) :
    manifoldBoundaryIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (selectedBoundaryPieces x) fun q => selectedBoundaryTerm x q := by
  simpa [selectedBoundaryPieceSum] using R.eq_selectedBoundarySum

/--
Projection in the exact shape of
`GlobalStokesData.globalBoundaryIntegral_eq_boundaryPartitionSum`.
-/
theorem globalBoundaryIntegral_eq_boundaryPartitionSum
    {boundaryPieces : Chart → Finset Piece}
    {boundaryPartitionTerm : Chart → Piece → Real}
    {globalBoundaryIntegral : Real}
    (R :
      BoundaryIntegralReconstructionData activeCharts boundaryPieces
        boundaryPartitionTerm globalBoundaryIntegral) :
    globalBoundaryIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun q => boundaryPartitionTerm x q :=
  R.eq_selectedBoundarySum_expanded

/--
Projection in the exact shape of
`ProjectLocalGlobalStokesData.globalBoundaryIntegral_eq_boundaryPartitionSum`.
-/
theorem projectLocal_globalBoundaryIntegral_eq_boundaryPartitionSum
    {localPieces : Chart → Finset Piece}
    {boundaryPartitionTerm : Chart → Piece → Real}
    {globalBoundaryIntegral : Real}
    (R :
      BoundaryIntegralReconstructionData activeCharts localPieces
        boundaryPartitionTerm globalBoundaryIntegral) :
    globalBoundaryIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q => boundaryPartitionTerm x q :=
  R.eq_selectedBoundarySum_expanded

end BoundaryIntegralReconstructionData

section FinalPackageProjections

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace GlobalStokesData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type p}

/-- Extract the boundary-integral reconstruction package from a final data package. -/
def boundaryIntegralReconstructionData
    (D : GlobalStokesData I ω Chart InteriorPiece BoundaryPiece) :
    BoundaryIntegralReconstructionData D.activeCharts D.boundaryPieces
      D.boundaryPartitionTerm D.globalBoundaryIntegral where
  manifoldBoundaryIntegral_eq_selectedBoundarySum := by
    simpa [selectedBoundaryPieceSum] using
      D.globalBoundaryIntegral_eq_boundaryPartitionSum

/--
Construct final global Stokes data while filling the boundary reconstruction
field from `BoundaryIntegralReconstructionData`.
-/
def ofBoundaryIntegralReconstruction
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (boundaryPieces : Chart → Finset BoundaryPiece)
    (interiorBulkTerm interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (boundaryBulkTerm boundaryBoundaryTerm boundaryPartitionTerm :
      Chart → BoundaryPiece → Real)
    (globalBulkIntegral globalBoundaryIntegral : Real)
    (globalBulkIntegral_eq_localBulkSum :
      globalBulkIntegral =
        (Finset.sum activeCharts fun x =>
            Finset.sum (interiorPieces x) fun q => interiorBulkTerm x q) +
          Finset.sum activeCharts fun x =>
            Finset.sum (boundaryPieces x) fun q => boundaryBulkTerm x q)
    (interiorLocalStokes :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ interiorPieces x →
          interiorBulkTerm x q = interiorBoundaryTerm x q)
    (boundaryLocalStokes :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          boundaryBulkTerm x q = boundaryBoundaryTerm x q)
    (interiorBoundaryCancellation :
      (Finset.sum activeCharts fun x =>
        Finset.sum (interiorPieces x) fun q => interiorBoundaryTerm x q) = 0)
    (chartChangeCancellation :
      (Finset.sum activeCharts fun x =>
          Finset.sum (boundaryPieces x) fun q => boundaryBoundaryTerm x q) =
        Finset.sum activeCharts fun x =>
          Finset.sum (boundaryPieces x) fun q => boundaryPartitionTerm x q)
    (boundaryReconstruction :
      BoundaryIntegralReconstructionData activeCharts boundaryPieces
        boundaryPartitionTerm globalBoundaryIntegral) :
    GlobalStokesData I ω Chart InteriorPiece BoundaryPiece where
  activeCharts := activeCharts
  interiorPieces := interiorPieces
  boundaryPieces := boundaryPieces
  interiorBulkTerm := interiorBulkTerm
  interiorBoundaryTerm := interiorBoundaryTerm
  boundaryBulkTerm := boundaryBulkTerm
  boundaryBoundaryTerm := boundaryBoundaryTerm
  boundaryPartitionTerm := boundaryPartitionTerm
  globalBulkIntegral := globalBulkIntegral
  globalBoundaryIntegral := globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum := globalBulkIntegral_eq_localBulkSum
  interiorLocalStokes := interiorLocalStokes
  boundaryLocalStokes := boundaryLocalStokes
  interiorBoundaryCancellation := interiorBoundaryCancellation
  chartChangeCancellation := chartChangeCancellation
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    boundaryReconstruction.globalBoundaryIntegral_eq_boundaryPartitionSum

end GlobalStokesData

namespace ProjectLocalGlobalStokesData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Extract the boundary-integral reconstruction package from a project-local package. -/
def boundaryIntegralReconstructionData
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    BoundaryIntegralReconstructionData D.activeCharts D.localPieces
      D.boundaryPartitionTerm D.globalBoundaryIntegral where
  manifoldBoundaryIntegral_eq_selectedBoundarySum := by
    simpa [selectedBoundaryPieceSum] using
      D.globalBoundaryIntegral_eq_boundaryPartitionSum

/--
Construct project-local global Stokes data while filling the boundary
reconstruction field from `BoundaryIntegralReconstructionData`.
-/
def ofBoundaryIntegralReconstruction
    (activeCharts : Finset Chart)
    (localPieces : Chart → Finset Piece)
    (sourceChart targetChart : Chart → Piece → M)
    (lowerCorner upperCorner : Chart → Piece → Fin (n + 1) → Real)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (globalBulkIntegral globalBoundaryIntegral : Real)
    (globalBulkIntegral_eq_projectLocalSum :
      globalBulkIntegral =
        Finset.sum activeCharts fun x =>
          Finset.sum (localPieces x) fun q =>
            projectLocalBulkIntegral I (sourceChart x q) (targetChart x q) ω
              (lowerCorner x q) (upperCorner x q))
    (localProjectStokes :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          projectLocalBulkIntegral I (sourceChart x q) (targetChart x q) ω
              (lowerCorner x q) (upperCorner x q) =
            projectLocalBoundaryIntegral I (sourceChart x q) (targetChart x q) ω
              (lowerCorner x q) (upperCorner x q))
    (chartChangeCancellation :
      (Finset.sum activeCharts fun x =>
          Finset.sum (localPieces x) fun q =>
            projectLocalBoundaryIntegral I (sourceChart x q) (targetChart x q) ω
              (lowerCorner x q) (upperCorner x q)) =
        Finset.sum activeCharts fun x =>
          Finset.sum (localPieces x) fun q => boundaryPartitionTerm x q)
    (boundaryReconstruction :
      BoundaryIntegralReconstructionData activeCharts localPieces
        boundaryPartitionTerm globalBoundaryIntegral) :
    ProjectLocalGlobalStokesData I ω Chart Piece where
  activeCharts := activeCharts
  localPieces := localPieces
  sourceChart := sourceChart
  targetChart := targetChart
  lowerCorner := lowerCorner
  upperCorner := upperCorner
  boundaryPartitionTerm := boundaryPartitionTerm
  globalBulkIntegral := globalBulkIntegral
  globalBoundaryIntegral := globalBoundaryIntegral
  globalBulkIntegral_eq_projectLocalSum := globalBulkIntegral_eq_projectLocalSum
  localProjectStokes := localProjectStokes
  chartChangeCancellation := chartChangeCancellation
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    boundaryReconstruction.projectLocal_globalBoundaryIntegral_eq_boundaryPartitionSum

end ProjectLocalGlobalStokesData

end FinalPackageProjections

section ReconstructionFieldWrappers

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace GlobalStokesReconstructionFields

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type p}

/--
Build global reconstruction fields while sourcing the boundary reconstruction
equality from `BoundaryIntegralReconstructionData`.
-/
def ofBoundaryIntegralReconstruction
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (boundaryPieces : Chart → Finset BoundaryPiece)
    (interiorBulkTerm : Chart → InteriorPiece → Real)
    (boundaryBulkTerm boundaryPartitionTerm : Chart → BoundaryPiece → Real)
    (globalBulkIntegral globalBoundaryIntegral : Real)
    (globalBulkIntegral_eq_localBulkSum :
      globalBulkIntegral =
        (Finset.sum activeCharts fun x =>
            Finset.sum (interiorPieces x) fun q => interiorBulkTerm x q) +
          Finset.sum activeCharts fun x =>
            Finset.sum (boundaryPieces x) fun q => boundaryBulkTerm x q)
    (boundaryReconstruction :
      BoundaryIntegralReconstructionData activeCharts boundaryPieces
        boundaryPartitionTerm globalBoundaryIntegral) :
    GlobalStokesReconstructionFields I ω Chart InteriorPiece BoundaryPiece where
  activeCharts := activeCharts
  interiorPieces := interiorPieces
  boundaryPieces := boundaryPieces
  interiorBulkTerm := interiorBulkTerm
  boundaryBulkTerm := boundaryBulkTerm
  boundaryPartitionTerm := boundaryPartitionTerm
  globalBulkIntegral := globalBulkIntegral
  globalBoundaryIntegral := globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum := globalBulkIntegral_eq_localBulkSum
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    boundaryReconstruction.globalBoundaryIntegral_eq_boundaryPartitionSum

end GlobalStokesReconstructionFields

namespace PartitionReconstructionData

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace Real E]
variable {I : ModelWithCorners Real E H}
variable {k : Nat} {ω : ManifoldForm I M k}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type p}

/--
Build partition reconstruction data while sourcing the boundary reconstruction
equality from `BoundaryIntegralReconstructionData`.
-/
def ofBoundaryIntegralReconstruction
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (boundaryPieces : Chart → Finset BoundaryPiece)
    (interiorBulkTerm : Chart → InteriorPiece → Real)
    (boundaryBulkTerm boundaryPartitionTerm : Chart → BoundaryPiece → Real)
    (globalBulkIntegral globalBoundaryIntegral : Real)
    (globalBulkIntegral_eq_localBulkSum :
      globalBulkIntegral =
        (Finset.sum activeCharts fun x =>
            Finset.sum (interiorPieces x) fun q => interiorBulkTerm x q) +
          Finset.sum activeCharts fun x =>
            Finset.sum (boundaryPieces x) fun q => boundaryBulkTerm x q)
    (boundaryReconstruction :
      BoundaryIntegralReconstructionData activeCharts boundaryPieces
        boundaryPartitionTerm globalBoundaryIntegral) :
    PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece where
  activeCharts := activeCharts
  interiorPieces := interiorPieces
  boundaryPieces := boundaryPieces
  interiorBulkTerm := interiorBulkTerm
  boundaryBulkTerm := boundaryBulkTerm
  boundaryPartitionTerm := boundaryPartitionTerm
  globalBulkIntegral := globalBulkIntegral
  globalBoundaryIntegral := globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum := globalBulkIntegral_eq_localBulkSum
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    boundaryReconstruction.globalBoundaryIntegral_eq_boundaryPartitionSum

end PartitionReconstructionData

end ReconstructionFieldWrappers

section OrientedBoundaryWrappers

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

namespace BoundaryGlobalConstructorData

variable {D : OrientedBoundaryProjectLocalPieces I ω Chart Piece}

/--
Constructor data for the oriented boundary-global path, with the boundary
reconstruction field filled by `BoundaryIntegralReconstructionData`.
-/
def ofBoundaryIntegralReconstruction
    (chartChangeFamily : OrientedBoundaryChartChangeFamilyData D)
    (boundaryReconstruction :
      BoundaryIntegralReconstructionData D.activeCharts D.localPieces
        D.boundaryPartitionTerm D.globalBoundaryIntegral) :
    BoundaryGlobalConstructorData D where
  chartChangeFamily := chartChangeFamily
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    boundaryReconstruction.globalBoundaryIntegral_eq_boundaryPartitionSum

end BoundaryGlobalConstructorData

namespace OrientedBoundaryProjectLocalPieces

/--
Build final global data from oriented-atlas boundary pieces, chart-change
family data, and boundary integral finite-sum reconstruction.
-/
def toGlobalStokesData_of_orientedAtlas_boundaryIntegralReconstruction
    [IsManifold I 1 M]
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.boundarySourceChart x q ∈ A.charts)
    (chartChangeFamily : OrientedBoundaryChartChangeFamilyData D)
    (boundaryReconstruction :
      BoundaryIntegralReconstructionData D.activeCharts D.localPieces
        D.boundaryPartitionTerm D.globalBoundaryIntegral) :
    GlobalStokesData I ω Chart Empty Piece :=
  (BoundaryGlobalConstructorData.ofBoundaryIntegralReconstruction
      chartChangeFamily boundaryReconstruction).toGlobalStokesData_of_orientedAtlas
    A hsource hboundarySource

/--
Build final global data from oriented-boundary-manifold pieces, chart-change
family data, and boundary integral finite-sum reconstruction.
-/
def toGlobalStokesData_of_orientedManifold_boundaryIntegralReconstruction
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece)
    (chartChangeFamily : OrientedBoundaryChartChangeFamilyData D)
    (boundaryReconstruction :
      BoundaryIntegralReconstructionData D.activeCharts D.localPieces
        D.boundaryPartitionTerm D.globalBoundaryIntegral) :
    GlobalStokesData I ω Chart Empty Piece :=
  (BoundaryGlobalConstructorData.ofBoundaryIntegralReconstruction
      chartChangeFamily boundaryReconstruction).toGlobalStokesData_of_orientedManifold

/--
Oriented-atlas boundary-global Stokes wrapper with boundary reconstruction
supplied by the finite-sum package.
-/
theorem stokes_of_orientedAtlas_boundaryIntegralReconstruction
    [IsManifold I 1 M]
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.boundarySourceChart x q ∈ A.charts)
    (chartChangeFamily : OrientedBoundaryChartChangeFamilyData D)
    (boundaryReconstruction :
      BoundaryIntegralReconstructionData D.activeCharts D.localPieces
        D.boundaryPartitionTerm D.globalBoundaryIntegral) :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  GlobalStokesData.stokes
    (D.toGlobalStokesData_of_orientedAtlas_boundaryIntegralReconstruction
      A hsource hboundarySource chartChangeFamily boundaryReconstruction)

/--
Oriented-boundary-manifold Stokes wrapper with boundary reconstruction supplied
by the finite-sum package.
-/
theorem stokes_of_orientedManifold_boundaryIntegralReconstruction
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece)
    (chartChangeFamily : OrientedBoundaryChartChangeFamilyData D)
    (boundaryReconstruction :
      BoundaryIntegralReconstructionData D.activeCharts D.localPieces
        D.boundaryPartitionTerm D.globalBoundaryIntegral) :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  GlobalStokesData.stokes
    (D.toGlobalStokesData_of_orientedManifold_boundaryIntegralReconstruction
      chartChangeFamily boundaryReconstruction)

end OrientedBoundaryProjectLocalPieces

end OrientedBoundaryWrappers

end BoundaryIntegralReconstruction

end Stokes

end
