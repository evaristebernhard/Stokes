import Stokes.Global.BoundaryPieceFamilyConstructor
import Stokes.Global.BoundaryIntegralReconstruction

/-!
# Selected boundary assembly

This file packages the boundary side of the selected mixed constructor.  The
input is deliberately close to the geometric data: selected/extended boundary
boxes for local Stokes, image data for the local boundary-face transport, and
oriented boundary chart-change data from the transported boundary term to the
chosen partition representative.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section SelectedBoundaryAssembly

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Boundary selected-box data assembled in the exact shape needed by the mixed
constructor.

For each active boundary piece, `sourceExtendedBox`, `targetSelectedBox`, and
`imageData` give the boundary local Stokes package.  The `chartChange*` fields
then identify the transported boundary term with the selected boundary
partition representative by an oriented boundary change of variables.
-/
structure SelectedBoundaryAssemblyData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in the selected boundary decomposition. -/
  activeCharts : Finset Chart
  /-- Boundary pieces assigned to each active chart. -/
  boundaryPieces : Chart → Finset Piece
  /-- Source chart for the bulk side of local boundary Stokes. -/
  sourceChart : Chart → Piece → M
  /-- Shared boundary chart: bulk target and transported-boundary source. -/
  boundarySourceChart : Chart → Piece → M
  /-- Target boundary chart for the transported local Stokes boundary term. -/
  boundaryTargetChart : Chart → Piece → M
  /-- Lower corner of the source boundary-chart box. -/
  sourceLowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Upper corner of the source boundary-chart box. -/
  sourceUpperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Lower corner of the transported local Stokes boundary box. -/
  targetLowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Upper corner of the transported local Stokes boundary box. -/
  targetUpperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Extended source boxes used by boundary local Stokes. -/
  sourceExtendedBox :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x →
        boundaryChartExtendedBox I (sourceChart x q) (boundarySourceChart x q) ω
          (sourceLowerCorner x q) (sourceUpperCorner x q)
  /-- Selected transported target boxes used by boundary local Stokes. -/
  targetSelectedBox :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x →
        boundaryChartSelectedBox I (boundarySourceChart x q) (boundaryTargetChart x q) ω
          (targetLowerCorner x q) (targetUpperCorner x q)
  /-- Image data transporting the source boundary face onto the target box. -/
  imageData :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x →
        boundaryChartSelectedBoxImageData I (sourceChart x q) (boundarySourceChart x q)
          (sourceLowerCorner x q) (sourceUpperCorner x q)
          (targetLowerCorner x q) (targetUpperCorner x q)
  /-- Chart used for the selected boundary-partition representative. -/
  partitionTargetChart : Chart → Piece → M
  /-- Lower corner of the selected boundary-partition box. -/
  partitionLowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Upper corner of the selected boundary-partition box. -/
  partitionUpperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Oriented COV from the transported local boundary term to the partition box. -/
  chartChangeOfVariables :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x →
        boundaryChartOrientedChangeOfVariables I
          (boundarySourceChart x q) (boundaryTargetChart x q) ω
          (targetLowerCorner x q) (targetUpperCorner x q)
          (partitionLowerCorner x q) (partitionUpperCorner x q)
  /-- Selected target box for the COV endpoint. -/
  partitionSelectedBox :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x →
        boundaryChartSelectedBox I (boundaryTargetChart x q) (partitionTargetChart x q) ω
          (partitionLowerCorner x q) (partitionUpperCorner x q)
  /-- Boundary partition term used by the global reconstruction package. -/
  boundaryPartitionTerm : Chart → Piece → Real
  /--
  Fieldized endpoint identification for the selected boundary partition term.

  This is the remaining reconstruction/partition choice that is not part of
  the local COV theorem itself.
  -/
  boundaryPartitionTerm_eq :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x →
        boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I (boundaryTargetChart x q)
            (partitionTargetChart x q) ω
            (partitionLowerCorner x q) (partitionUpperCorner x q)

namespace SelectedBoundaryAssemblyData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Bulk term supplied by one selected boundary piece. -/
def boundaryBulkTerm
    (D : SelectedBoundaryAssemblyData I ω Chart Piece) (x : Chart) (q : Piece) :
    Real :=
  projectLocalBulkIntegral I (D.sourceChart x q) (D.boundarySourceChart x q) ω
    (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)

/-- Transported boundary term supplied by boundary local Stokes. -/
def boundaryBoundaryTerm
    (D : SelectedBoundaryAssemblyData I ω Chart Piece) (x : Chart) (q : Piece) :
    Real :=
  projectLocalBoundaryIntegral I
    (D.boundarySourceChart x q) (D.boundaryTargetChart x q) ω
    (D.targetLowerCorner x q) (D.targetUpperCorner x q)

/-- Sum of selected boundary bulk terms. -/
def boundaryBulkSum
    (D : SelectedBoundaryAssemblyData I ω Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => boundaryBulkTerm D x q

/-- Sum of transported selected boundary terms before chart-change assembly. -/
def boundaryBoundarySum
    (D : SelectedBoundaryAssemblyData I ω Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => boundaryBoundaryTerm D x q

/-- Sum of selected boundary partition terms. -/
def boundaryPartitionSum
    (D : SelectedBoundaryAssemblyData I ω Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => D.boundaryPartitionTerm x q

/--
Forget the chart-change endpoint fields, keeping the local boundary data needed
by `BoundaryPieceFamilyInput`.
-/
def toBoundaryPieceFamilyInput
    (D : SelectedBoundaryAssemblyData I ω Chart Piece) :
    BoundaryPieceFamilyInput I ω Chart Piece where
  activeCharts := D.activeCharts
  boundaryPieces := D.boundaryPieces
  sourceChart := D.sourceChart
  boundarySourceChart := D.boundarySourceChart
  boundaryTargetChart := D.boundaryTargetChart
  sourceLowerCorner := D.sourceLowerCorner
  sourceUpperCorner := D.sourceUpperCorner
  targetLowerCorner := D.targetLowerCorner
  targetUpperCorner := D.targetUpperCorner
  sourceExtendedBox := D.sourceExtendedBox
  targetSelectedBox := D.targetSelectedBox
  imageData := D.imageData

/-- Selected boundary assembly as the mixed-constructor boundary package. -/
def toMixedBoundaryPackage_of_orientedAtlas
    [IsManifold I 1 M]
    (D : SelectedBoundaryAssemblyData I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → D.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → D.boundarySourceChart x q ∈ A.charts) :
    MixedBoundaryPackage I ω Chart Piece
      D.activeCharts D.boundaryPieces (boundaryBulkTerm D) (boundaryBoundaryTerm D) where
  localStokes := by
    intro x hx q hq
    simpa [boundaryBulkTerm, boundaryBoundaryTerm, toBoundaryPieceFamilyInput,
      BoundaryPieceFamilyInput.boundaryBulkTerm,
      BoundaryPieceFamilyInput.boundaryBoundaryTerm] using
      (D.toBoundaryPieceFamilyInput.localStokes_of_orientedAtlas
        A hsource hboundarySource x hx q hq)

/-- Selected boundary assembly as the oriented-manifold mixed boundary package. -/
def toMixedBoundaryPackage
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : SelectedBoundaryAssemblyData I ω Chart Piece) :
    MixedBoundaryPackage I ω Chart Piece
      D.activeCharts D.boundaryPieces (boundaryBulkTerm D) (boundaryBoundaryTerm D) where
  localStokes := by
    intro x hx q hq
    simpa [boundaryBulkTerm, boundaryBoundaryTerm, toBoundaryPieceFamilyInput,
      BoundaryPieceFamilyInput.boundaryBulkTerm,
      BoundaryPieceFamilyInput.boundaryBoundaryTerm] using
      (D.toBoundaryPieceFamilyInput.localStokes x hx q hq)

/-- The selected boundary local Stokes identities summed over all active pieces. -/
theorem boundaryBulkSum_eq_boundaryBoundarySum_of_orientedAtlas
    [IsManifold I 1 M]
    (D : SelectedBoundaryAssemblyData I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → D.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → D.boundarySourceChart x q ∈ A.charts) :
    boundaryBulkSum D = boundaryBoundarySum D := by
  exact MixedBoundaryPackage.boundaryBulkSum_eq_boundaryBoundarySum
    (D.toMixedBoundaryPackage_of_orientedAtlas A hsource hboundarySource)

/-- The oriented-manifold selected boundary local Stokes identities summed. -/
theorem boundaryBulkSum_eq_boundaryBoundarySum
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : SelectedBoundaryAssemblyData I ω Chart Piece) :
    boundaryBulkSum D = boundaryBoundarySum D := by
  exact D.toMixedBoundaryPackage.boundaryBulkSum_eq_boundaryBoundarySum

/--
Pointwise chart-change equality from the transported local boundary term to the
selected partition representative.
-/
theorem pointwise_chartChange
    [IsManifold I 1 M]
    (D : SelectedBoundaryAssemblyData I ω Chart Piece) :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.boundaryPieces x →
        boundaryBoundaryTerm D x q = D.boundaryPartitionTerm x q := by
  intro x hx q hq
  calc
    boundaryBoundaryTerm D x q =
        projectLocalBoundaryIntegral I (D.boundaryTargetChart x q)
          (D.partitionTargetChart x q) ω
          (D.partitionLowerCorner x q) (D.partitionUpperCorner x q) := by
          exact projectLocalBoundaryIntegral_chartChange_selected
            (D.boundarySourceChart x q) (D.boundaryTargetChart x q)
            (D.partitionTargetChart x q) ω
            (D.targetLowerCorner x q) (D.targetUpperCorner x q)
            (D.partitionLowerCorner x q) (D.partitionUpperCorner x q)
            (D.chartChangeOfVariables x hx q hq)
            (D.partitionSelectedBox x hx q hq)
    _ = D.boundaryPartitionTerm x q := by
          exact (D.boundaryPartitionTerm_eq x hx q hq).symm

/-- The selected boundary chart-change data as pure finite-sum cancellation data. -/
def toChartChangeCancellationData
    [IsManifold I 1 M]
    (D : SelectedBoundaryAssemblyData I ω Chart Piece) :
    ChartChangeCancellationData Chart Piece Real where
  activeCharts := D.activeCharts
  boundaryPieces := D.boundaryPieces
  oldBoundaryTerm := boundaryBoundaryTerm D
  newBoundaryTerm := D.boundaryPartitionTerm
  term_eq := D.pointwise_chartChange

/-- Finite-sum chart-change cancellation for selected boundary assembly data. -/
theorem chartChangeCancellation
    [IsManifold I 1 M]
    (D : SelectedBoundaryAssemblyData I ω Chart Piece) :
    boundaryBoundarySum D = boundaryPartitionSum D := by
  exact D.toChartChangeCancellationData.chartChangeCancellation

/-- Boundary reconstruction package for a selected boundary assembly. -/
def boundaryIntegralReconstructionData
    (D : SelectedBoundaryAssemblyData I ω Chart Piece)
    (globalBoundaryIntegral : Real)
    (hglobal :
      globalBoundaryIntegral = boundaryPartitionSum D) :
    BoundaryIntegralReconstructionData D.activeCharts D.boundaryPieces
      D.boundaryPartitionTerm globalBoundaryIntegral where
  manifoldBoundaryIntegral_eq_selectedBoundarySum := by
    simpa [boundaryPartitionSum, selectedBoundaryPieceSum] using hglobal

end SelectedBoundaryAssemblyData

end SelectedBoundaryAssembly

end Stokes

end
