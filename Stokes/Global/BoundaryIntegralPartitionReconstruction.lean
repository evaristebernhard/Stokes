import Stokes.Global.BoundaryIntegralReconstruction
import Stokes.Global.BoundaryPieceFamilyConstructor

/-!
# Boundary integral reconstruction from partition terms

This file adds the next boundary-global reconstruction layer.  The core
`BoundaryIntegralReconstructionData` package only remembers the final finite
sum equality.  Here we expose a slightly more analytic input shape: a genuine
boundary-measure integral may be recorded as an intermediate field, and the
finite boundary partition terms reconstruct that measure integral.

The conversions back to the final boundary-global constructors are deliberately
thin wrappers around `BoundaryIntegralReconstructionData`.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryIntegralPartitionReconstruction

universe c p

/--
Boundary integral reconstruction from finite boundary partition terms.

The field `boundaryMeasureIntegral` is the placeholder for the eventual genuine
measure-theoretic boundary integral.  Once the analytic layer proves that it is
both the represented manifold boundary integral and the finite partition sum,
this package immediately yields `BoundaryIntegralReconstructionData`.
-/
structure BoundaryIntegralPartitionReconstructionData {Chart : Type c} {Piece : Type p}
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart → Finset Piece)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (manifoldBoundaryIntegral : Real) where
  /-- The genuine boundary measure integral represented by the partition data. -/
  boundaryMeasureIntegral : Real
  /-- The represented manifold boundary integral agrees with the measure integral. -/
  manifoldBoundaryIntegral_eq_boundaryMeasureIntegral :
    manifoldBoundaryIntegral = boundaryMeasureIntegral
  /-- The boundary measure integral is reconstructed from the finite partition terms. -/
  boundaryMeasureIntegral_eq_partitionSum :
    boundaryMeasureIntegral =
      selectedBoundaryPieceSum activeCharts boundaryPieces boundaryPartitionTerm

namespace BoundaryIntegralPartitionReconstructionData

variable {Chart : Type c} {Piece : Type p}
variable {activeCharts : Finset Chart}
variable {boundaryPieces : Chart → Finset Piece}
variable {boundaryPartitionTerm : Chart → Piece → Real}
variable {manifoldBoundaryIntegral : Real}

/-- Build partition reconstruction data from the two measure-reconstruction fields. -/
def ofBoundaryMeasureEq
    (boundaryMeasureIntegral : Real)
    (hmeasure : manifoldBoundaryIntegral = boundaryMeasureIntegral)
    (hpartition :
      boundaryMeasureIntegral =
        selectedBoundaryPieceSum activeCharts boundaryPieces boundaryPartitionTerm) :
    BoundaryIntegralPartitionReconstructionData activeCharts boundaryPieces
      boundaryPartitionTerm manifoldBoundaryIntegral where
  boundaryMeasureIntegral := boundaryMeasureIntegral
  manifoldBoundaryIntegral_eq_boundaryMeasureIntegral := hmeasure
  boundaryMeasureIntegral_eq_partitionSum := hpartition

/-- Build partition reconstruction data directly from the final finite-sum equality. -/
def ofEq
    (h :
      manifoldBoundaryIntegral =
        selectedBoundaryPieceSum activeCharts boundaryPieces boundaryPartitionTerm) :
    BoundaryIntegralPartitionReconstructionData activeCharts boundaryPieces
      boundaryPartitionTerm manifoldBoundaryIntegral where
  boundaryMeasureIntegral := manifoldBoundaryIntegral
  manifoldBoundaryIntegral_eq_boundaryMeasureIntegral := rfl
  boundaryMeasureIntegral_eq_partitionSum := h

/-- The tautological package whose represented integral is the selected partition sum. -/
def ofSelectedBoundaryPieceSum
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart → Finset Piece)
    (boundaryPartitionTerm : Chart → Piece → Real) :
    BoundaryIntegralPartitionReconstructionData activeCharts boundaryPieces
      boundaryPartitionTerm
      (selectedBoundaryPieceSum activeCharts boundaryPieces boundaryPartitionTerm) where
  boundaryMeasureIntegral :=
    selectedBoundaryPieceSum activeCharts boundaryPieces boundaryPartitionTerm
  manifoldBoundaryIntegral_eq_boundaryMeasureIntegral := rfl
  boundaryMeasureIntegral_eq_partitionSum := rfl

/-- The final reconstruction equality supplied by the partition data. -/
theorem manifoldBoundaryIntegral_eq_partitionSum
    (R :
      BoundaryIntegralPartitionReconstructionData activeCharts boundaryPieces
        boundaryPartitionTerm manifoldBoundaryIntegral) :
    manifoldBoundaryIntegral =
      selectedBoundaryPieceSum activeCharts boundaryPieces boundaryPartitionTerm :=
  R.manifoldBoundaryIntegral_eq_boundaryMeasureIntegral.trans
    R.boundaryMeasureIntegral_eq_partitionSum

/-- Expanded finite-sum form of the partition reconstruction equality. -/
theorem manifoldBoundaryIntegral_eq_partitionSum_expanded
    (R :
      BoundaryIntegralPartitionReconstructionData activeCharts boundaryPieces
        boundaryPartitionTerm manifoldBoundaryIntegral) :
    manifoldBoundaryIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun q => boundaryPartitionTerm x q := by
  simpa [selectedBoundaryPieceSum] using R.manifoldBoundaryIntegral_eq_partitionSum

/-- Expanded finite-sum form of the intermediate measure reconstruction equality. -/
theorem boundaryMeasureIntegral_eq_partitionSum_expanded
    (R :
      BoundaryIntegralPartitionReconstructionData activeCharts boundaryPieces
        boundaryPartitionTerm manifoldBoundaryIntegral) :
    R.boundaryMeasureIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun q => boundaryPartitionTerm x q := by
  simpa [selectedBoundaryPieceSum] using R.boundaryMeasureIntegral_eq_partitionSum

/-- Forget the intermediate measure integral and keep the final finite-sum package. -/
def toBoundaryIntegralReconstructionData
    (R :
      BoundaryIntegralPartitionReconstructionData activeCharts boundaryPieces
        boundaryPartitionTerm manifoldBoundaryIntegral) :
    BoundaryIntegralReconstructionData activeCharts boundaryPieces
      boundaryPartitionTerm manifoldBoundaryIntegral where
  manifoldBoundaryIntegral_eq_selectedBoundarySum :=
    R.manifoldBoundaryIntegral_eq_partitionSum

/--
Projection in the exact shape of
`GlobalStokesData.globalBoundaryIntegral_eq_boundaryPartitionSum`.
-/
theorem globalBoundaryIntegral_eq_boundaryPartitionSum
    {boundaryPieces : Chart → Finset Piece}
    {boundaryPartitionTerm : Chart → Piece → Real}
    {globalBoundaryIntegral : Real}
    (R :
      BoundaryIntegralPartitionReconstructionData activeCharts boundaryPieces
        boundaryPartitionTerm globalBoundaryIntegral) :
    globalBoundaryIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun q => boundaryPartitionTerm x q :=
  R.manifoldBoundaryIntegral_eq_partitionSum_expanded

/--
Projection in the exact shape of
`ProjectLocalGlobalStokesData.globalBoundaryIntegral_eq_boundaryPartitionSum`.
-/
theorem projectLocal_globalBoundaryIntegral_eq_boundaryPartitionSum
    {localPieces : Chart → Finset Piece}
    {boundaryPartitionTerm : Chart → Piece → Real}
    {globalBoundaryIntegral : Real}
    (R :
      BoundaryIntegralPartitionReconstructionData activeCharts localPieces
        boundaryPartitionTerm globalBoundaryIntegral) :
    globalBoundaryIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q => boundaryPartitionTerm x q :=
  R.manifoldBoundaryIntegral_eq_partitionSum_expanded

end BoundaryIntegralPartitionReconstructionData

end BoundaryIntegralPartitionReconstruction

section BoundaryPieceFamilyWrappers

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

namespace BoundaryPieceFamilyInput

/--
Construct boundary integral partition reconstruction data for a finite
boundary-piece family and chosen boundary partition terms.
-/
def boundaryIntegralPartitionReconstructionData
    (D : BoundaryPieceFamilyInput I ω Chart Piece)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (globalBoundaryIntegral boundaryMeasureIntegral : Real)
    (hmeasure : globalBoundaryIntegral = boundaryMeasureIntegral)
    (hpartition :
      boundaryMeasureIntegral =
        selectedBoundaryPieceSum D.activeCharts D.boundaryPieces
          boundaryPartitionTerm) :
    BoundaryIntegralPartitionReconstructionData D.activeCharts D.boundaryPieces
      boundaryPartitionTerm globalBoundaryIntegral :=
  BoundaryIntegralPartitionReconstructionData.ofBoundaryMeasureEq
    boundaryMeasureIntegral hmeasure hpartition

/--
Construct the core boundary reconstruction package directly from a finite
boundary-piece family and chosen partition terms.
-/
def boundaryIntegralReconstructionData
    (D : BoundaryPieceFamilyInput I ω Chart Piece)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (globalBoundaryIntegral boundaryMeasureIntegral : Real)
    (hmeasure : globalBoundaryIntegral = boundaryMeasureIntegral)
    (hpartition :
      boundaryMeasureIntegral =
        selectedBoundaryPieceSum D.activeCharts D.boundaryPieces
          boundaryPartitionTerm) :
    BoundaryIntegralReconstructionData D.activeCharts D.boundaryPieces
      boundaryPartitionTerm globalBoundaryIntegral :=
  let R :=
    D.boundaryIntegralPartitionReconstructionData boundaryPartitionTerm
      globalBoundaryIntegral boundaryMeasureIntegral hmeasure hpartition
  R.toBoundaryIntegralReconstructionData

/--
Tautological reconstruction for the transported target boundary terms of a
finite boundary-piece family.
-/
def boundaryIntegralPartitionReconstructionData_ofBoundaryBoundaryTerm
    (D : BoundaryPieceFamilyInput I ω Chart Piece) :
    BoundaryIntegralPartitionReconstructionData D.activeCharts D.boundaryPieces
      (BoundaryPieceFamilyInput.boundaryBoundaryTerm D)
      (BoundaryPieceFamilyInput.boundaryBoundarySum D) :=
  BoundaryIntegralPartitionReconstructionData.ofSelectedBoundaryPieceSum
    D.activeCharts D.boundaryPieces
    (BoundaryPieceFamilyInput.boundaryBoundaryTerm D)

/--
The transported boundary term recorded by a boundary-piece family is exactly
the outward-first boundary chart integral on the target selected box.
-/
theorem boundaryBoundaryTerm_eq_outwardFirstBoundaryChartIntegral
    (D : BoundaryPieceFamilyInput I ω Chart Piece) (x : Chart) (q : Piece) :
    BoundaryPieceFamilyInput.boundaryBoundaryTerm D x q =
      outwardFirstBoundaryChartIntegral I
        (D.boundarySourceChart x q) (D.boundaryTargetChart x q) ω
        (D.targetLowerCorner x q) (D.targetUpperCorner x q) :=
  rfl

/-- The transported boundary sum, expanded as outward-first chart integrals. -/
theorem boundaryBoundarySum_eq_outwardFirstBoundaryChartIntegral_sum
    (D : BoundaryPieceFamilyInput I ω Chart Piece) :
    BoundaryPieceFamilyInput.boundaryBoundarySum D =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.boundaryPieces x) fun q =>
          outwardFirstBoundaryChartIntegral I
            (D.boundarySourceChart x q) (D.boundaryTargetChart x q) ω
            (D.targetLowerCorner x q) (D.targetUpperCorner x q) := by
  rfl

/--
Tautological reconstruction for the outward-first target boundary terms of a
finite boundary-piece family.
-/
def boundaryIntegralPartitionReconstructionData_ofOutwardFirstBoundaryTerm
    (D : BoundaryPieceFamilyInput I ω Chart Piece) :
    BoundaryIntegralPartitionReconstructionData D.activeCharts D.boundaryPieces
      (fun x q =>
        outwardFirstBoundaryChartIntegral I
          (D.boundarySourceChart x q) (D.boundaryTargetChart x q) ω
          (D.targetLowerCorner x q) (D.targetUpperCorner x q))
      (BoundaryPieceFamilyInput.boundaryBoundarySum D) :=
  BoundaryIntegralPartitionReconstructionData.ofSelectedBoundaryPieceSum
    D.activeCharts D.boundaryPieces
    (fun x q =>
      outwardFirstBoundaryChartIntegral I
        (D.boundarySourceChart x q) (D.boundaryTargetChart x q) ω
        (D.targetLowerCorner x q) (D.targetUpperCorner x q))

/--
If the transported boundary term is the selected boundary partition term
pointwise, then the boundary-piece family reconstructs the global boundary
integral as the selected partition sum.
-/
def boundaryIntegralPartitionReconstructionData_ofBoundaryBoundaryTermEq
    (D : BoundaryPieceFamilyInput I ω Chart Piece)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (globalBoundaryIntegral : Real)
    (hglobal :
      globalBoundaryIntegral = BoundaryPieceFamilyInput.boundaryBoundarySum D)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          BoundaryPieceFamilyInput.boundaryBoundaryTerm D x q =
            boundaryPartitionTerm x q) :
    BoundaryIntegralPartitionReconstructionData D.activeCharts D.boundaryPieces
      boundaryPartitionTerm globalBoundaryIntegral :=
  BoundaryIntegralPartitionReconstructionData.ofEq (by
    calc
      globalBoundaryIntegral =
          BoundaryPieceFamilyInput.boundaryBoundarySum D := hglobal
      _ =
          Finset.sum D.activeCharts fun x =>
            Finset.sum (D.boundaryPieces x) fun q =>
              BoundaryPieceFamilyInput.boundaryBoundaryTerm D x q := by
        rfl
      _ =
          Finset.sum D.activeCharts fun x =>
            Finset.sum (D.boundaryPieces x) fun q =>
              boundaryPartitionTerm x q := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        refine Finset.sum_congr rfl ?_
        intro q hq
        exact hterm x hx q hq
      _ =
          selectedBoundaryPieceSum D.activeCharts D.boundaryPieces
            boundaryPartitionTerm := by
        rfl)

/--
The pointwise equality needed to identify an outward-first local boundary
chart integral with a selected partition term is exactly the corresponding
`boundaryBoundaryTerm` equality.
-/
theorem outwardFirstBoundaryChartIntegral_eq_boundaryPartitionTerm_of_boundaryBoundaryTerm_eq
    (D : BoundaryPieceFamilyInput I ω Chart Piece)
    {boundaryPartitionTerm : Chart → Piece → Real}
    {x : Chart} {q : Piece}
    (hterm :
      BoundaryPieceFamilyInput.boundaryBoundaryTerm D x q =
        boundaryPartitionTerm x q) :
    outwardFirstBoundaryChartIntegral I
        (D.boundarySourceChart x q) (D.boundaryTargetChart x q) ω
        (D.targetLowerCorner x q) (D.targetUpperCorner x q) =
      boundaryPartitionTerm x q :=
  hterm

/--
Boundary reconstruction data over transported boundary terms gives the global
boundary integral as a finite sum of outward-first boundary chart integrals.
-/
theorem globalBoundaryIntegral_eq_outwardFirstBoundaryChartIntegral_sum
    (D : BoundaryPieceFamilyInput I ω Chart Piece)
    {globalBoundaryIntegral : Real}
    (R :
      BoundaryIntegralPartitionReconstructionData D.activeCharts D.boundaryPieces
        (BoundaryPieceFamilyInput.boundaryBoundaryTerm D)
        globalBoundaryIntegral) :
    globalBoundaryIntegral =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.boundaryPieces x) fun q =>
          outwardFirstBoundaryChartIntegral I
            (D.boundarySourceChart x q) (D.boundaryTargetChart x q) ω
            (D.targetLowerCorner x q) (D.targetUpperCorner x q) := by
  simpa using R.manifoldBoundaryIntegral_eq_partitionSum_expanded

/--
Core tautological reconstruction for the transported target boundary terms of a
finite boundary-piece family.
-/
def boundaryIntegralReconstructionData_ofBoundaryBoundaryTerm
    (D : BoundaryPieceFamilyInput I ω Chart Piece) :
    BoundaryIntegralReconstructionData D.activeCharts D.boundaryPieces
      (BoundaryPieceFamilyInput.boundaryBoundaryTerm D)
      (BoundaryPieceFamilyInput.boundaryBoundarySum D) :=
  D.boundaryIntegralPartitionReconstructionData_ofBoundaryBoundaryTerm
    |>.toBoundaryIntegralReconstructionData

end BoundaryPieceFamilyInput

namespace BoundaryProjectLocalPieces

/-- View the boundary-reconstruction field of a project-local package as partition data. -/
def boundaryIntegralPartitionReconstructionData
    (D : BoundaryProjectLocalPieces I ω Chart Piece) :
    BoundaryIntegralPartitionReconstructionData D.activeCharts D.localPieces
      D.boundaryPartitionTerm D.globalBoundaryIntegral :=
  BoundaryIntegralPartitionReconstructionData.ofEq (by
    simpa [selectedBoundaryPieceSum] using
      D.globalBoundaryIntegral_eq_boundaryPartitionSum)

end BoundaryProjectLocalPieces

namespace OrientedBoundaryProjectLocalPieces

/-- View the boundary-reconstruction field of an oriented boundary package as partition data. -/
def boundaryIntegralPartitionReconstructionData
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece) :
    BoundaryIntegralPartitionReconstructionData D.activeCharts D.localPieces
      D.boundaryPartitionTerm D.globalBoundaryIntegral :=
  BoundaryIntegralPartitionReconstructionData.ofEq (by
    simpa [selectedBoundaryPieceSum] using
      D.globalBoundaryIntegral_eq_boundaryPartitionSum)

/--
Construct partition reconstruction data for an oriented boundary package from
an explicit boundary-measure reconstruction field.
-/
def boundaryIntegralPartitionReconstructionDataOfMeasure
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece)
    (boundaryMeasureIntegral : Real)
    (hmeasure : D.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hpartition :
      boundaryMeasureIntegral =
        selectedBoundaryPieceSum D.activeCharts D.localPieces
          D.boundaryPartitionTerm) :
    BoundaryIntegralPartitionReconstructionData D.activeCharts D.localPieces
      D.boundaryPartitionTerm D.globalBoundaryIntegral :=
  BoundaryIntegralPartitionReconstructionData.ofBoundaryMeasureEq
    boundaryMeasureIntegral hmeasure hpartition

end OrientedBoundaryProjectLocalPieces

end BoundaryPieceFamilyWrappers

section OrientedBoundaryWrappers

universe u w c p

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
reconstruction field filled from partition reconstruction data.
-/
def ofBoundaryIntegralPartitionReconstruction
    (chartChangeFamily : OrientedBoundaryChartChangeFamilyData D)
    (boundaryReconstruction :
      BoundaryIntegralPartitionReconstructionData D.activeCharts D.localPieces
        D.boundaryPartitionTerm D.globalBoundaryIntegral) :
    BoundaryGlobalConstructorData D :=
  ofBoundaryIntegralReconstruction chartChangeFamily
    boundaryReconstruction.toBoundaryIntegralReconstructionData

end BoundaryGlobalConstructorData

namespace OrientedBoundaryProjectLocalPieces

/--
Build final global data from oriented-atlas boundary pieces, chart-change
family data, and boundary integral partition reconstruction.
-/
def toGlobalStokesData_of_orientedAtlas_boundaryIntegralPartitionReconstruction
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
      BoundaryIntegralPartitionReconstructionData D.activeCharts D.localPieces
        D.boundaryPartitionTerm D.globalBoundaryIntegral) :
    GlobalStokesData I ω Chart Empty Piece :=
  D.toGlobalStokesData_of_orientedAtlas_boundaryIntegralReconstruction
    A hsource hboundarySource chartChangeFamily
    boundaryReconstruction.toBoundaryIntegralReconstructionData

/--
Build final global data from oriented-boundary-manifold pieces, chart-change
family data, and boundary integral partition reconstruction.
-/
def toGlobalStokesData_of_orientedManifold_boundaryIntegralPartitionReconstruction
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece)
    (chartChangeFamily : OrientedBoundaryChartChangeFamilyData D)
    (boundaryReconstruction :
      BoundaryIntegralPartitionReconstructionData D.activeCharts D.localPieces
        D.boundaryPartitionTerm D.globalBoundaryIntegral) :
    GlobalStokesData I ω Chart Empty Piece :=
  D.toGlobalStokesData_of_orientedManifold_boundaryIntegralReconstruction
    chartChangeFamily boundaryReconstruction.toBoundaryIntegralReconstructionData

/--
Oriented-atlas boundary-global Stokes wrapper with boundary reconstruction
supplied by partition reconstruction data.
-/
theorem stokes_of_orientedAtlas_boundaryIntegralPartitionReconstruction
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
      BoundaryIntegralPartitionReconstructionData D.activeCharts D.localPieces
        D.boundaryPartitionTerm D.globalBoundaryIntegral) :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  D.stokes_of_orientedAtlas_boundaryIntegralReconstruction
    A hsource hboundarySource chartChangeFamily
    boundaryReconstruction.toBoundaryIntegralReconstructionData

/--
Oriented-boundary-manifold Stokes wrapper with boundary reconstruction supplied
by partition reconstruction data.
-/
theorem stokes_of_orientedManifold_boundaryIntegralPartitionReconstruction
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece)
    (chartChangeFamily : OrientedBoundaryChartChangeFamilyData D)
    (boundaryReconstruction :
      BoundaryIntegralPartitionReconstructionData D.activeCharts D.localPieces
        D.boundaryPartitionTerm D.globalBoundaryIntegral) :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  D.stokes_of_orientedManifold_boundaryIntegralReconstruction
    chartChangeFamily boundaryReconstruction.toBoundaryIntegralReconstructionData

end OrientedBoundaryProjectLocalPieces

end OrientedBoundaryWrappers

end Stokes

end
