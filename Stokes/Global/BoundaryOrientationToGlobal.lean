import Stokes.BoundaryChart.OrientedAtlasSelectedBoxCOV
import Stokes.Global.SelectedBoundaryAssembly
import Stokes.Global.BoundaryIntegralReconstruction

/-!
# Boundary orientation to global assembly

This file connects boundary-chart orientation compatibility with the selected
boundary assembly layer used by the global constructors.

There is not yet a separate `BoundaryChart.OrientationNatural` module in this
workspace.  The corresponding naturality input is therefore kept fieldized:
each selected boundary piece records the target-box selection used for the
partition representative, plus the endpoint equality identifying the selected
partition term with that representative.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryOrientationToGlobal

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Selected boundary assembly input before the oriented COV field has been built.

The local Stokes data are the same source extended boxes, transported target
selected boxes, and image data used by `SelectedBoundaryAssemblyData`.  The
extra `partitionTargetBox` field is the fieldized orientation/naturality input:
once an oriented atlas or oriented boundary manifold is supplied, it produces
the oriented chart-change package from the transported boundary term to the
selected boundary partition representative.
-/
structure BoundaryOrientationSelectedAssemblyInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in the selected boundary decomposition. -/
  activeCharts : Finset Chart
  /-- Boundary pieces assigned to each active chart. -/
  boundaryPieces : Chart -> Finset Piece
  /-- Source chart for the bulk side of local boundary Stokes. -/
  sourceChart : Chart -> Piece -> M
  /-- Shared boundary chart: bulk target and transported-boundary source. -/
  boundarySourceChart : Chart -> Piece -> M
  /-- Target boundary chart for the transported local Stokes boundary term. -/
  boundaryTargetChart : Chart -> Piece -> M
  /-- Lower corner of the source boundary-chart box. -/
  sourceLowerCorner : Chart -> Piece -> Fin (n + 1) -> Real
  /-- Upper corner of the source boundary-chart box. -/
  sourceUpperCorner : Chart -> Piece -> Fin (n + 1) -> Real
  /-- Lower corner of the transported local Stokes boundary box. -/
  targetLowerCorner : Chart -> Piece -> Fin (n + 1) -> Real
  /-- Upper corner of the transported local Stokes boundary box. -/
  targetUpperCorner : Chart -> Piece -> Fin (n + 1) -> Real
  /-- Extended source boxes used by boundary local Stokes. -/
  sourceExtendedBox :
    forall x, x ∈ activeCharts ->
      forall q, q ∈ boundaryPieces x ->
        boundaryChartExtendedBox I (sourceChart x q) (boundarySourceChart x q) omega
          (sourceLowerCorner x q) (sourceUpperCorner x q)
  /-- Selected transported target boxes used by boundary local Stokes. -/
  targetSelectedBox :
    forall x, x ∈ activeCharts ->
      forall q, q ∈ boundaryPieces x ->
        boundaryChartSelectedBox I (boundarySourceChart x q) (boundaryTargetChart x q)
          omega (targetLowerCorner x q) (targetUpperCorner x q)
  /-- Image data transporting the source boundary face onto the target box. -/
  imageData :
    forall x, x ∈ activeCharts ->
      forall q, q ∈ boundaryPieces x ->
        boundaryChartSelectedBoxImageData I (sourceChart x q) (boundarySourceChart x q)
          (sourceLowerCorner x q) (sourceUpperCorner x q)
          (targetLowerCorner x q) (targetUpperCorner x q)
  /-- Chart used for the selected boundary-partition representative. -/
  partitionTargetChart : Chart -> Piece -> M
  /-- Target-box selection for the COV from transported boundary term to partition term. -/
  partitionTargetBox :
    forall x q,
      BoundaryChartTargetBoxSelection I (boundarySourceChart x q) (boundaryTargetChart x q)
        (targetLowerCorner x q) (targetUpperCorner x q)
  /-- Selected auxiliary target box for the selected partition representative. -/
  partitionSelectedBox :
    forall x, x ∈ activeCharts ->
      forall q, q ∈ boundaryPieces x ->
        boundaryChartSelectedBox I (boundaryTargetChart x q) (partitionTargetChart x q)
          omega ((partitionTargetBox x q).lowerCorner) ((partitionTargetBox x q).upperCorner)
  /-- Boundary partition term used by the global reconstruction package. -/
  boundaryPartitionTerm : Chart -> Piece -> Real
  /-- Endpoint identification for the selected boundary partition term. -/
  boundaryPartitionTerm_eq :
    forall x, x ∈ activeCharts ->
      forall q, q ∈ boundaryPieces x ->
        boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I (boundaryTargetChart x q)
            (partitionTargetChart x q) omega
            ((partitionTargetBox x q).lowerCorner) ((partitionTargetBox x q).upperCorner)

namespace BoundaryOrientationSelectedAssemblyInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Lower corner selected for the boundary partition representative. -/
def partitionLowerCorner
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) -> Real :=
  (D.partitionTargetBox x q).lowerCorner

/-- Upper corner selected for the boundary partition representative. -/
def partitionUpperCorner
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) -> Real :=
  (D.partitionTargetBox x q).upperCorner

/-- Bulk term supplied by one selected boundary piece. -/
def boundaryBulkTerm
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (x : Chart) (q : Piece) : Real :=
  projectLocalBulkIntegral I (D.sourceChart x q) (D.boundarySourceChart x q) omega
    (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)

/-- Transported boundary term supplied by boundary local Stokes. -/
def boundaryBoundaryTerm
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (x : Chart) (q : Piece) : Real :=
  projectLocalBoundaryIntegral I
    (D.boundarySourceChart x q) (D.boundaryTargetChart x q) omega
    (D.targetLowerCorner x q) (D.targetUpperCorner x q)

/-- Sum of selected boundary bulk terms. -/
def boundaryBulkSum
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => boundaryBulkTerm D x q

/-- Sum of transported selected boundary terms before chart-change assembly. -/
def boundaryBoundarySum
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => boundaryBoundaryTerm D x q

/-- Sum of selected boundary partition terms. -/
def boundaryPartitionSum
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => D.boundaryPartitionTerm x q

/--
Forget the partition endpoint fields, retaining the local boundary-piece family
data used by the local Stokes constructor.
-/
def toBoundaryPieceFamilyInput
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece) :
    BoundaryPieceFamilyInput I omega Chart Piece where
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

/--
View the transported boundary-to-partition step as a selected-box COV family.
The oriented atlas/manifold wrappers below turn this into actual oriented COV
data.
-/
def toBoundaryChartSelectedBoxCOVFamilyData
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece) :
    BoundaryChartSelectedBoxCOVFamilyData I omega Chart Piece where
  activeCharts := D.activeCharts
  localPieces := D.boundaryPieces
  sourceChart := D.boundarySourceChart
  boundarySourceChart := D.boundaryTargetChart
  boundaryTargetChart := D.partitionTargetChart
  sourceLowerCorner := D.targetLowerCorner
  sourceUpperCorner := D.targetUpperCorner
  sourceSelectedBox := D.targetSelectedBox
  targetBox := D.partitionTargetBox
  targetSelectedBox := D.partitionSelectedBox

/-- Build the selected-boundary assembly data from an oriented boundary atlas. -/
def toSelectedBoundaryAssemblyData_of_orientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hboundarySource :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundarySourceChart x q ∈ A.charts)
    (hboundaryTarget :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundaryTargetChart x q ∈ A.charts) :
    SelectedBoundaryAssemblyData I omega Chart Piece where
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
  partitionTargetChart := D.partitionTargetChart
  partitionLowerCorner := D.partitionLowerCorner
  partitionUpperCorner := D.partitionUpperCorner
  chartChangeOfVariables := by
    intro x hx q hq
    simpa [toBoundaryChartSelectedBoxCOVFamilyData, partitionLowerCorner,
      partitionUpperCorner] using
      (D.toBoundaryChartSelectedBoxCOVFamilyData
        |>.toChangeOfVariablesFamilyOfOrientedAtlas A hboundarySource hboundaryTarget
        |>.changeOfVariables x hx q hq)
  partitionSelectedBox := by
    intro x hx q hq
    simpa [partitionLowerCorner, partitionUpperCorner] using
      D.partitionSelectedBox x hx q hq
  boundaryPartitionTerm := D.boundaryPartitionTerm
  boundaryPartitionTerm_eq := by
    intro x hx q hq
    simpa [partitionLowerCorner, partitionUpperCorner] using
      D.boundaryPartitionTerm_eq x hx q hq

/-- Build the selected-boundary assembly data from global oriented-manifold data. -/
def toSelectedBoundaryAssemblyData_of_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece) :
    SelectedBoundaryAssemblyData I omega Chart Piece where
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
  partitionTargetChart := D.partitionTargetChart
  partitionLowerCorner := D.partitionLowerCorner
  partitionUpperCorner := D.partitionUpperCorner
  chartChangeOfVariables := by
    intro x hx q hq
    simpa [toBoundaryChartSelectedBoxCOVFamilyData, partitionLowerCorner,
      partitionUpperCorner] using
      (D.toBoundaryChartSelectedBoxCOVFamilyData
        |>.toChangeOfVariablesFamilyOfOrientedManifold
        |>.changeOfVariables x hx q hq)
  partitionSelectedBox := by
    intro x hx q hq
    simpa [partitionLowerCorner, partitionUpperCorner] using
      D.partitionSelectedBox x hx q hq
  boundaryPartitionTerm := D.boundaryPartitionTerm
  boundaryPartitionTerm_eq := by
    intro x hx q hq
    simpa [partitionLowerCorner, partitionUpperCorner] using
      D.boundaryPartitionTerm_eq x hx q hq

/-- Selected boundary assembly as the mixed-constructor boundary package. -/
def toMixedBoundaryPackage_of_orientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.sourceChart x q ∈ A.charts)
    (hboundarySource :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundarySourceChart x q ∈ A.charts)
    (hboundaryTarget :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundaryTargetChart x q ∈ A.charts) :
    MixedBoundaryPackage I omega Chart Piece
      D.activeCharts D.boundaryPieces (boundaryBulkTerm D) (boundaryBoundaryTerm D) := by
  simpa [boundaryBulkTerm, boundaryBoundaryTerm,
    toSelectedBoundaryAssemblyData_of_orientedAtlas,
    SelectedBoundaryAssemblyData.boundaryBulkTerm,
    SelectedBoundaryAssemblyData.boundaryBoundaryTerm] using
    (D.toSelectedBoundaryAssemblyData_of_orientedAtlas A hboundarySource hboundaryTarget
      |>.toMixedBoundaryPackage_of_orientedAtlas A hsource hboundarySource)

/-- Selected boundary assembly as the oriented-manifold mixed boundary package. -/
def toMixedBoundaryPackage_of_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece) :
    MixedBoundaryPackage I omega Chart Piece
      D.activeCharts D.boundaryPieces (boundaryBulkTerm D) (boundaryBoundaryTerm D) := by
  simpa [boundaryBulkTerm, boundaryBoundaryTerm,
    toSelectedBoundaryAssemblyData_of_orientedManifold,
    SelectedBoundaryAssemblyData.boundaryBulkTerm,
    SelectedBoundaryAssemblyData.boundaryBoundaryTerm] using
    (D.toSelectedBoundaryAssemblyData_of_orientedManifold
      |>.toMixedBoundaryPackage)

/-- Finite-sum chart-change cancellation from oriented-atlas data. -/
theorem chartChangeCancellation_of_orientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hboundarySource :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundarySourceChart x q ∈ A.charts)
    (hboundaryTarget :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundaryTargetChart x q ∈ A.charts) :
    boundaryBoundarySum D = boundaryPartitionSum D := by
  simpa [boundaryBoundarySum, boundaryPartitionSum, boundaryBoundaryTerm,
    toSelectedBoundaryAssemblyData_of_orientedAtlas,
    SelectedBoundaryAssemblyData.boundaryBoundarySum,
    SelectedBoundaryAssemblyData.boundaryPartitionSum,
    SelectedBoundaryAssemblyData.boundaryBoundaryTerm] using
    (D.toSelectedBoundaryAssemblyData_of_orientedAtlas A hboundarySource hboundaryTarget
      |>.chartChangeCancellation)

/-- Finite-sum chart-change cancellation from oriented-manifold data. -/
theorem chartChangeCancellation_of_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece) :
    boundaryBoundarySum D = boundaryPartitionSum D := by
  simpa [boundaryBoundarySum, boundaryPartitionSum, boundaryBoundaryTerm,
    toSelectedBoundaryAssemblyData_of_orientedManifold,
    SelectedBoundaryAssemblyData.boundaryBoundarySum,
    SelectedBoundaryAssemblyData.boundaryPartitionSum,
    SelectedBoundaryAssemblyData.boundaryBoundaryTerm] using
    (D.toSelectedBoundaryAssemblyData_of_orientedManifold |>.chartChangeCancellation)

/--
Package the selected boundary data as `OrientedBoundaryProjectLocalPieces`, with
global integrals supplied by the reconstruction layer.
-/
def toOrientedBoundaryProjectLocalPieces_of_orientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hboundarySource :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundarySourceChart x q ∈ A.charts)
    (hboundaryTarget :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundaryTargetChart x q ∈ A.charts)
    (globalBulkIntegral globalBoundaryIntegral : Real)
    (hbulk : globalBulkIntegral = boundaryBulkSum D)
    (hboundary : globalBoundaryIntegral = boundaryPartitionSum D) :
    OrientedBoundaryProjectLocalPieces I omega Chart Piece where
  activeCharts := D.activeCharts
  localPieces := D.boundaryPieces
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
  boundaryPartitionTerm := D.boundaryPartitionTerm
  globalBulkIntegral := globalBulkIntegral
  globalBoundaryIntegral := globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum := by
    simpa [boundaryBulkSum, boundaryBulkTerm] using hbulk
  chartChangeCancellation := by
    simpa [boundaryBoundarySum, boundaryPartitionSum, boundaryBoundaryTerm,
      OrientedBoundaryProjectLocalPieces.projectLocalBoundaryTerm] using
      D.chartChangeCancellation_of_orientedAtlas A hboundarySource hboundaryTarget
  globalBoundaryIntegral_eq_boundaryPartitionSum := by
    simpa [boundaryPartitionSum] using hboundary

/--
Package the selected boundary data as `OrientedBoundaryProjectLocalPieces`, with
global integrals supplied by the reconstruction layer.
-/
def toOrientedBoundaryProjectLocalPieces_of_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (globalBulkIntegral globalBoundaryIntegral : Real)
    (hbulk : globalBulkIntegral = boundaryBulkSum D)
    (hboundary : globalBoundaryIntegral = boundaryPartitionSum D) :
    OrientedBoundaryProjectLocalPieces I omega Chart Piece where
  activeCharts := D.activeCharts
  localPieces := D.boundaryPieces
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
  boundaryPartitionTerm := D.boundaryPartitionTerm
  globalBulkIntegral := globalBulkIntegral
  globalBoundaryIntegral := globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum := by
    simpa [boundaryBulkSum, boundaryBulkTerm] using hbulk
  chartChangeCancellation := by
    simpa [boundaryBoundarySum, boundaryPartitionSum, boundaryBoundaryTerm,
      OrientedBoundaryProjectLocalPieces.projectLocalBoundaryTerm] using
      D.chartChangeCancellation_of_orientedManifold
  globalBoundaryIntegral_eq_boundaryPartitionSum := by
    simpa [boundaryPartitionSum] using hboundary

/-- Pointwise chart-change family for the oriented-atlas global constructor. -/
def toOrientedBoundaryChartChangeFamilyData_of_orientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hboundarySource :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundarySourceChart x q ∈ A.charts)
    (hboundaryTarget :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundaryTargetChart x q ∈ A.charts)
    (globalBulkIntegral globalBoundaryIntegral : Real)
    (hbulk : globalBulkIntegral = boundaryBulkSum D)
    (hboundary : globalBoundaryIntegral = boundaryPartitionSum D) :
    OrientedBoundaryChartChangeFamilyData
      (D.toOrientedBoundaryProjectLocalPieces_of_orientedAtlas
        A hboundarySource hboundaryTarget globalBulkIntegral globalBoundaryIntegral
        hbulk hboundary) where
  term_eq := by
    intro x hx q hq
    simpa [toOrientedBoundaryProjectLocalPieces_of_orientedAtlas,
      OrientedBoundaryProjectLocalPieces.projectLocalBoundaryTerm,
      toSelectedBoundaryAssemblyData_of_orientedAtlas,
      SelectedBoundaryAssemblyData.boundaryBoundaryTerm,
      boundaryBoundaryTerm] using
      (D.toSelectedBoundaryAssemblyData_of_orientedAtlas A hboundarySource hboundaryTarget
        |>.pointwise_chartChange x hx q hq)

/-- Pointwise chart-change family for the oriented-manifold global constructor. -/
def toOrientedBoundaryChartChangeFamilyData_of_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (globalBulkIntegral globalBoundaryIntegral : Real)
    (hbulk : globalBulkIntegral = boundaryBulkSum D)
    (hboundary : globalBoundaryIntegral = boundaryPartitionSum D) :
    OrientedBoundaryChartChangeFamilyData
      (D.toOrientedBoundaryProjectLocalPieces_of_orientedManifold
        globalBulkIntegral globalBoundaryIntegral hbulk hboundary) where
  term_eq := by
    intro x hx q hq
    simpa [toOrientedBoundaryProjectLocalPieces_of_orientedManifold,
      OrientedBoundaryProjectLocalPieces.projectLocalBoundaryTerm,
      toSelectedBoundaryAssemblyData_of_orientedManifold,
      SelectedBoundaryAssemblyData.boundaryBoundaryTerm,
      boundaryBoundaryTerm] using
      (D.toSelectedBoundaryAssemblyData_of_orientedManifold
        |>.pointwise_chartChange x hx q hq)

/-- Boundary-global constructor data from oriented-atlas selected assembly input. -/
def toBoundaryGlobalConstructorData_of_orientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hboundarySource :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundarySourceChart x q ∈ A.charts)
    (hboundaryTarget :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundaryTargetChart x q ∈ A.charts)
    (globalBulkIntegral globalBoundaryIntegral : Real)
    (hbulk : globalBulkIntegral = boundaryBulkSum D)
    (hboundary : globalBoundaryIntegral = boundaryPartitionSum D) :
    BoundaryGlobalConstructorData
      (D.toOrientedBoundaryProjectLocalPieces_of_orientedAtlas
        A hboundarySource hboundaryTarget globalBulkIntegral globalBoundaryIntegral
        hbulk hboundary) where
  chartChangeFamily :=
    D.toOrientedBoundaryChartChangeFamilyData_of_orientedAtlas
      A hboundarySource hboundaryTarget globalBulkIntegral globalBoundaryIntegral
      hbulk hboundary
  globalBoundaryIntegral_eq_boundaryPartitionSum := by
    simpa [toOrientedBoundaryProjectLocalPieces_of_orientedAtlas,
      boundaryPartitionSum] using hboundary

/-- Boundary-global constructor data from oriented-manifold selected assembly input. -/
def toBoundaryGlobalConstructorData_of_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (globalBulkIntegral globalBoundaryIntegral : Real)
    (hbulk : globalBulkIntegral = boundaryBulkSum D)
    (hboundary : globalBoundaryIntegral = boundaryPartitionSum D) :
    BoundaryGlobalConstructorData
      (D.toOrientedBoundaryProjectLocalPieces_of_orientedManifold
        globalBulkIntegral globalBoundaryIntegral hbulk hboundary) where
  chartChangeFamily :=
    D.toOrientedBoundaryChartChangeFamilyData_of_orientedManifold
      globalBulkIntegral globalBoundaryIntegral hbulk hboundary
  globalBoundaryIntegral_eq_boundaryPartitionSum := by
    simpa [toOrientedBoundaryProjectLocalPieces_of_orientedManifold,
      boundaryPartitionSum] using hboundary

/-- Final global data from oriented-atlas selected boundary assembly input. -/
def toGlobalStokesData_of_orientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.sourceChart x q ∈ A.charts)
    (hboundarySource :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundarySourceChart x q ∈ A.charts)
    (hboundaryTarget :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundaryTargetChart x q ∈ A.charts)
    (globalBulkIntegral globalBoundaryIntegral : Real)
    (hbulk : globalBulkIntegral = boundaryBulkSum D)
    (hboundary : globalBoundaryIntegral = boundaryPartitionSum D) :
    GlobalStokesData I omega Chart Empty Piece :=
  (D.toBoundaryGlobalConstructorData_of_orientedAtlas
      A hboundarySource hboundaryTarget globalBulkIntegral globalBoundaryIntegral
      hbulk hboundary).toGlobalStokesData_of_orientedAtlas
    A hsource hboundarySource

/-- Final global data from oriented-manifold selected boundary assembly input. -/
def toGlobalStokesData_of_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (globalBulkIntegral globalBoundaryIntegral : Real)
    (hbulk : globalBulkIntegral = boundaryBulkSum D)
    (hboundary : globalBoundaryIntegral = boundaryPartitionSum D) :
    GlobalStokesData I omega Chart Empty Piece :=
  (D.toBoundaryGlobalConstructorData_of_orientedManifold
      globalBulkIntegral globalBoundaryIntegral hbulk hboundary)
    |>.toGlobalStokesData_of_orientedManifold

/-- Boundary-global Stokes from oriented-atlas selected boundary assembly input. -/
theorem stokes_of_orientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.sourceChart x q ∈ A.charts)
    (hboundarySource :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundarySourceChart x q ∈ A.charts)
    (hboundaryTarget :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundaryTargetChart x q ∈ A.charts)
    (globalBulkIntegral globalBoundaryIntegral : Real)
    (hbulk : globalBulkIntegral = boundaryBulkSum D)
    (hboundary : globalBoundaryIntegral = boundaryPartitionSum D) :
    globalBulkIntegral = globalBoundaryIntegral :=
  boundaryGlobalStokes_of_orientedAtlas
    (D.toBoundaryGlobalConstructorData_of_orientedAtlas
      A hboundarySource hboundaryTarget globalBulkIntegral globalBoundaryIntegral
      hbulk hboundary)
    A hsource hboundarySource

/-- Boundary-global Stokes from oriented-manifold selected boundary assembly input. -/
theorem stokes_of_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (globalBulkIntegral globalBoundaryIntegral : Real)
    (hbulk : globalBulkIntegral = boundaryBulkSum D)
    (hboundary : globalBoundaryIntegral = boundaryPartitionSum D) :
    globalBulkIntegral = globalBoundaryIntegral :=
  boundaryGlobalStokes_of_orientedManifold
    (D.toBoundaryGlobalConstructorData_of_orientedManifold
      globalBulkIntegral globalBoundaryIntegral hbulk hboundary)

end BoundaryOrientationSelectedAssemblyInput

end BoundaryOrientationToGlobal

end Stokes

end
