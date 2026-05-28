import Stokes.BoundaryChart.TargetImageFieldReduction
import Stokes.Global.BoundaryOrientationToGlobal

/-!
# Boundary target-image data to selected assembly

This file is the global adapter from boundary target-image selections to the
selected boundary assembly layer.

The pure boundary-chart layer now provides
`BoundaryChartTargetImageResolvedFamily`.  This file keeps the global assembly
data in the shape expected by `BoundaryOrientationToGlobal`, and supplies
adapters from the pure resolved family by adding only the extra global
`sourceExtendedBox` field needed for local boundary Stokes.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryTargetImageToAssembly

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Fieldized output of the boundary target-image reduction step.

The `targetImage` field replaces the three separate target fields needed by
boundary local Stokes: target lower corner, target upper corner, and image data.
The remaining fields are exactly the source extended boxes and target selected
boxes consumed by `BoundaryPieceFamilyInput` and `SelectedBoundaryAssemblyData`.
-/
structure BoundaryTargetImageFieldReductionData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in the boundary decomposition. -/
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
  /-- Extended source boxes used by boundary local Stokes. -/
  sourceExtendedBox :
    forall x, x ∈ activeCharts ->
      forall q, q ∈ boundaryPieces x ->
        boundaryChartExtendedBox I (sourceChart x q) (boundarySourceChart x q) omega
          (sourceLowerCorner x q) (sourceUpperCorner x q)
  /--
  Selected target image boxes for the source-to-boundary-source transition.

  Each package supplies the target lower/upper corners and the image-data
  theorem required by the local boundary Stokes wrapper.
  -/
  targetImage :
    (x : Chart) -> (q : Piece) ->
      BoundaryChartTargetBoxSelection I (sourceChart x q) (boundarySourceChart x q)
        (sourceLowerCorner x q) (sourceUpperCorner x q)
  /-- Selected target boxes used by boundary local Stokes. -/
  targetSelectedBox :
    forall x, x ∈ activeCharts ->
      forall q, q ∈ boundaryPieces x ->
        boundaryChartSelectedBox I (boundarySourceChart x q) (boundaryTargetChart x q)
          omega ((targetImage x q).lowerCorner) ((targetImage x q).upperCorner)

namespace BoundaryTargetImageFieldReductionData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Lower corner selected by the target-image reduction step. -/
def targetLowerCorner
    (D : BoundaryTargetImageFieldReductionData I omega Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) -> Real :=
  (D.targetImage x q).lowerCorner

/-- Upper corner selected by the target-image reduction step. -/
def targetUpperCorner
    (D : BoundaryTargetImageFieldReductionData I omega Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) -> Real :=
  (D.targetImage x q).upperCorner

/-- The selected target lower corner lies on the lower zero face. -/
theorem targetLowerCorner_zero
    (D : BoundaryTargetImageFieldReductionData I omega Chart Piece)
    (x : Chart) (q : Piece) :
    D.targetLowerCorner x q 0 = 0 :=
  (D.targetImage x q).lowerCorner_zero

/-- The selected target corners are coordinatewise ordered. -/
theorem targetLower_le_targetUpper
    (D : BoundaryTargetImageFieldReductionData I omega Chart Piece)
    (x : Chart) (q : Piece) :
    D.targetLowerCorner x q <= D.targetUpperCorner x q :=
  (D.targetImage x q).lower_le_upper

/-- Image data projected from the selected target-image box. -/
theorem imageData
    (D : BoundaryTargetImageFieldReductionData I omega Chart Piece)
    (x : Chart) (q : Piece) :
    boundaryChartSelectedBoxImageData I (D.sourceChart x q) (D.boundarySourceChart x q)
      (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)
      (D.targetLowerCorner x q) (D.targetUpperCorner x q) := by
  simpa [targetLowerCorner, targetUpperCorner] using
    (D.targetImage x q).imageData

/--
Forget the target-image packaging, exposing the ordinary boundary-piece family
input consumed by local boundary Stokes.
-/
def toBoundaryPieceFamilyInput
    (D : BoundaryTargetImageFieldReductionData I omega Chart Piece) :
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
  imageData := by
    intro x _hx q _hq
    exact D.imageData x q

end BoundaryTargetImageFieldReductionData

namespace BoundaryChartTargetImageResolvedFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/--
Global boundary-target-image data obtained from the pure resolved boundary-chart
family, after supplying the stronger source extended-box field required by
local boundary Stokes.
-/
def toBoundaryTargetImageFieldReductionData
    (F : BoundaryChartTargetImageResolvedFamily I omega Chart Piece)
    (sourceExtendedBox :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          boundaryChartExtendedBox I (F.sourceChart x q) (F.boundarySourceChart x q)
            omega (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)) :
    BoundaryTargetImageFieldReductionData I omega Chart Piece where
  activeCharts := F.activeCharts
  boundaryPieces := F.localPieces
  sourceChart := F.sourceChart
  boundarySourceChart := F.boundarySourceChart
  boundaryTargetChart := F.boundaryTargetChart
  sourceLowerCorner := F.sourceLowerCorner
  sourceUpperCorner := F.sourceUpperCorner
  sourceExtendedBox := sourceExtendedBox
  targetImage := F.targetBox
  targetSelectedBox := F.targetSelectedBox

/-- The global adapter preserves the underlying local boundary-piece family. -/
theorem toBoundaryPieceFamilyInput_toBoundaryTargetImageFieldReductionData
    (F : BoundaryChartTargetImageResolvedFamily I omega Chart Piece)
    (sourceExtendedBox :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          boundaryChartExtendedBox I (F.sourceChart x q) (F.boundarySourceChart x q)
            omega (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)) :
    (F.toBoundaryTargetImageFieldReductionData sourceExtendedBox).toBoundaryPieceFamilyInput =
      { activeCharts := F.activeCharts
        boundaryPieces := F.localPieces
        sourceChart := F.sourceChart
        boundarySourceChart := F.boundarySourceChart
        boundaryTargetChart := F.boundaryTargetChart
        sourceLowerCorner := F.sourceLowerCorner
        sourceUpperCorner := F.sourceUpperCorner
        targetLowerCorner := F.targetLowerCorner
        targetUpperCorner := F.targetUpperCorner
        sourceExtendedBox := sourceExtendedBox
        targetSelectedBox := F.targetSelectedBox
        imageData := by
          intro x _hx q _hq
          exact F.imageData x q } := by
  rfl

end BoundaryChartTargetImageResolvedFamily

/--
Target-image reduction data plus the boundary partition endpoint fields needed
by the selected assembly and orientation-to-global layers.
-/
structure BoundaryTargetImageToAssemblyInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (Chart : Type c) (Piece : Type p) where
  /-- Boundary local-Stokes data with target image boxes already reduced. -/
  targetImageData : BoundaryTargetImageFieldReductionData I omega Chart Piece
  /-- Chart used for the selected boundary-partition representative. -/
  partitionTargetChart : Chart -> Piece -> M
  /-- Target-box selection for the COV from transported boundary term to partition term. -/
  partitionTargetBox :
    (x : Chart) -> (q : Piece) ->
      BoundaryChartTargetBoxSelection I
        (targetImageData.boundarySourceChart x q)
        (targetImageData.boundaryTargetChart x q)
        (targetImageData.targetLowerCorner x q)
        (targetImageData.targetUpperCorner x q)
  /-- Selected auxiliary target box for the selected partition representative. -/
  partitionSelectedBox :
    forall x, x ∈ targetImageData.activeCharts ->
      forall q, q ∈ targetImageData.boundaryPieces x ->
        boundaryChartSelectedBox I
          (targetImageData.boundaryTargetChart x q)
          (partitionTargetChart x q) omega
          ((partitionTargetBox x q).lowerCorner)
          ((partitionTargetBox x q).upperCorner)
  /-- Boundary partition term used by the global reconstruction package. -/
  boundaryPartitionTerm : Chart -> Piece -> Real
  /-- Endpoint identification for the selected boundary partition term. -/
  boundaryPartitionTerm_eq :
    forall x, x ∈ targetImageData.activeCharts ->
      forall q, q ∈ targetImageData.boundaryPieces x ->
        boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I
            (targetImageData.boundaryTargetChart x q)
            (partitionTargetChart x q) omega
            ((partitionTargetBox x q).lowerCorner)
            ((partitionTargetBox x q).upperCorner)

namespace BoundaryTargetImageToAssemblyInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Active chart labels inherited from the target-image data. -/
def activeCharts
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece) :
    Finset Chart :=
  D.targetImageData.activeCharts

/-- Boundary pieces inherited from the target-image data. -/
def boundaryPieces
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece) :
    Chart -> Finset Piece :=
  D.targetImageData.boundaryPieces

/-- Source chart inherited from the target-image data. -/
def sourceChart
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece) :
    Chart -> Piece -> M :=
  D.targetImageData.sourceChart

/-- Shared boundary source chart inherited from the target-image data. -/
def boundarySourceChart
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece) :
    Chart -> Piece -> M :=
  D.targetImageData.boundarySourceChart

/-- Boundary target chart inherited from the target-image data. -/
def boundaryTargetChart
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece) :
    Chart -> Piece -> M :=
  D.targetImageData.boundaryTargetChart

/-- Source lower corner inherited from the target-image data. -/
def sourceLowerCorner
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece) :
    Chart -> Piece -> Fin (n + 1) -> Real :=
  D.targetImageData.sourceLowerCorner

/-- Source upper corner inherited from the target-image data. -/
def sourceUpperCorner
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece) :
    Chart -> Piece -> Fin (n + 1) -> Real :=
  D.targetImageData.sourceUpperCorner

/-- Target lower corner projected from the target-image data. -/
def targetLowerCorner
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) -> Real :=
  D.targetImageData.targetLowerCorner x q

/-- Target upper corner projected from the target-image data. -/
def targetUpperCorner
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) -> Real :=
  D.targetImageData.targetUpperCorner x q

/-- Partition lower corner selected for the boundary partition representative. -/
def partitionLowerCorner
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) -> Real :=
  (D.partitionTargetBox x q).lowerCorner

/-- Partition upper corner selected for the boundary partition representative. -/
def partitionUpperCorner
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece)
    (x : Chart) (q : Piece) : Fin (n + 1) -> Real :=
  (D.partitionTargetBox x q).upperCorner

/-- Image data projected from the target-image reduction package. -/
theorem imageData
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece)
    (x : Chart) (q : Piece) :
    boundaryChartSelectedBoxImageData I (D.sourceChart x q) (D.boundarySourceChart x q)
      (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)
      (D.targetLowerCorner x q) (D.targetUpperCorner x q) := by
  simpa [sourceChart, boundarySourceChart, sourceLowerCorner, sourceUpperCorner,
    targetLowerCorner, targetUpperCorner] using
    D.targetImageData.imageData x q

/--
Build the global assembly input directly from the pure resolved target-image
family, adding the source extended boxes and the partition endpoint data that
belong to the global assembly layer.
-/
def ofResolvedFamily
    (F : BoundaryChartTargetImageResolvedFamily I omega Chart Piece)
    (sourceExtendedBox :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          boundaryChartExtendedBox I (F.sourceChart x q) (F.boundarySourceChart x q)
            omega (F.sourceLowerCorner x q) (F.sourceUpperCorner x q))
    (partitionTargetChart : Chart -> Piece -> M)
    (partitionTargetBox :
      (x : Chart) -> (q : Piece) ->
        BoundaryChartTargetBoxSelection I
          (F.boundarySourceChart x q) (F.boundaryTargetChart x q)
          (F.targetLowerCorner x q) (F.targetUpperCorner x q))
    (partitionSelectedBox :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          boundaryChartSelectedBox I
            (F.boundaryTargetChart x q) (partitionTargetChart x q) omega
            ((partitionTargetBox x q).lowerCorner)
            ((partitionTargetBox x q).upperCorner))
    (boundaryPartitionTerm : Chart -> Piece -> Real)
    (boundaryPartitionTerm_eq :
      forall x, x ∈ F.activeCharts ->
        forall q, q ∈ F.localPieces x ->
          boundaryPartitionTerm x q =
            projectLocalBoundaryIntegral I
              (F.boundaryTargetChart x q) (partitionTargetChart x q) omega
              ((partitionTargetBox x q).lowerCorner)
              ((partitionTargetBox x q).upperCorner)) :
    BoundaryTargetImageToAssemblyInput I omega Chart Piece where
  targetImageData := F.toBoundaryTargetImageFieldReductionData sourceExtendedBox
  partitionTargetChart := partitionTargetChart
  partitionTargetBox := partitionTargetBox
  partitionSelectedBox := by
    intro x hx q hq
    exact partitionSelectedBox x hx q hq
  boundaryPartitionTerm := boundaryPartitionTerm
  boundaryPartitionTerm_eq := by
    intro x hx q hq
    exact boundaryPartitionTerm_eq x hx q hq

/--
Expose the fieldized target-image package as the ordinary orientation-selected
assembly input used by `BoundaryOrientationToGlobal`.
-/
def toBoundaryOrientationSelectedAssemblyInput
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece) :
    BoundaryOrientationSelectedAssemblyInput I omega Chart Piece where
  activeCharts := D.activeCharts
  boundaryPieces := D.boundaryPieces
  sourceChart := D.sourceChart
  boundarySourceChart := D.boundarySourceChart
  boundaryTargetChart := D.boundaryTargetChart
  sourceLowerCorner := D.sourceLowerCorner
  sourceUpperCorner := D.sourceUpperCorner
  targetLowerCorner := D.targetLowerCorner
  targetUpperCorner := D.targetUpperCorner
  sourceExtendedBox := by
    intro x hx q hq
    exact D.targetImageData.sourceExtendedBox x hx q hq
  targetSelectedBox := by
    intro x hx q hq
    exact D.targetImageData.targetSelectedBox x hx q hq
  imageData := by
    intro x _hx q _hq
    exact D.imageData x q
  partitionTargetChart := D.partitionTargetChart
  partitionTargetBox := D.partitionTargetBox
  partitionSelectedBox := by
    intro x hx q hq
    exact D.partitionSelectedBox x hx q hq
  boundaryPartitionTerm := D.boundaryPartitionTerm
  boundaryPartitionTerm_eq := by
    intro x hx q hq
    exact D.boundaryPartitionTerm_eq x hx q hq

/--
Build selected boundary assembly data when the oriented chart-change package is
already supplied explicitly.
-/
def toSelectedBoundaryAssemblyData
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece)
    (chartChangeOfVariables :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          boundaryChartOrientedChangeOfVariables I
            (D.boundarySourceChart x q) (D.boundaryTargetChart x q) omega
            (D.targetLowerCorner x q) (D.targetUpperCorner x q)
            (D.partitionLowerCorner x q) (D.partitionUpperCorner x q)) :
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
  sourceExtendedBox := by
    intro x hx q hq
    exact D.targetImageData.sourceExtendedBox x hx q hq
  targetSelectedBox := by
    intro x hx q hq
    exact D.targetImageData.targetSelectedBox x hx q hq
  imageData := by
    intro x _hx q _hq
    exact D.imageData x q
  partitionTargetChart := D.partitionTargetChart
  partitionLowerCorner := D.partitionLowerCorner
  partitionUpperCorner := D.partitionUpperCorner
  chartChangeOfVariables := chartChangeOfVariables
  partitionSelectedBox := by
    intro x hx q hq
    exact D.partitionSelectedBox x hx q hq
  boundaryPartitionTerm := D.boundaryPartitionTerm
  boundaryPartitionTerm_eq := by
    intro x hx q hq
    exact D.boundaryPartitionTerm_eq x hx q hq

/-- Build selected boundary assembly data from an oriented boundary atlas. -/
def toSelectedBoundaryAssemblyData_of_orientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hboundarySource :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundarySourceChart x q ∈ A.charts)
    (hboundaryTarget :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x -> D.boundaryTargetChart x q ∈ A.charts) :
    SelectedBoundaryAssemblyData I omega Chart Piece :=
  D.toBoundaryOrientationSelectedAssemblyInput
    |>.toSelectedBoundaryAssemblyData_of_orientedAtlas A hboundarySource hboundaryTarget

/-- Build selected boundary assembly data from oriented-boundary-manifold data. -/
def toSelectedBoundaryAssemblyData_of_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece) :
    SelectedBoundaryAssemblyData I omega Chart Piece :=
  D.toBoundaryOrientationSelectedAssemblyInput
    |>.toSelectedBoundaryAssemblyData_of_orientedManifold

end BoundaryTargetImageToAssemblyInput

end BoundaryTargetImageToAssembly

end Stokes

end
