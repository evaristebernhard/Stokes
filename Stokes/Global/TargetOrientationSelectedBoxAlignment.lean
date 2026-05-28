import Stokes.BoundaryChart.OrientationAtlasBoundarySign
import Stokes.BoundaryChart.TargetImageSelectedBoxAuto
import Stokes.Global.BoundaryMeasureTargetAssembly
import Stokes.Global.OrientedAtlasToM8
import Stokes.Global.TargetImageToM8

/-!
# Target-image and orientation selected-box alignment

This file is a thin projection layer.  It records that the target-image input
already carries the chart-membership data needed to expose M8 orientation
fields, and that each selected target-image piece can be combined with the
oriented-atlas boundary-sign package to produce the selected-box COV data used
by the boundary chart-change route.

No local inverse, open-mapping, orientation, or measure theorem is proved here:
those remain fields of the lower-level target-image, orientation, and boundary
measure packages.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section TargetOrientationSelectedBoxAlignment

universe u w p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type p}

namespace BoundaryChartSelectedBoxTargetImageAutoData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {x0 x1 : M} {omega : ManifoldForm I M n}
variable {a b : Fin (n + 1) -> Real}

/--
Combine selected target-image data with selected-box orientation data in the
shape consumed by boundary chart change of variables.
-/
def toOrientationCovData
    (T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 omega a b)
    (O : BoundaryChartAtlasBoundarySignData I x0 x1 omega a b) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 omega a b
      T.targetLowerCorner T.targetUpperCorner :=
  O.toSelectedBoxOrientationCovData T.imageData

/-- The aligned selected-box data immediately supplies oriented COV. -/
theorem orientedChangeOfVariables
    [IsManifold I 1 M]
    (T : BoundaryChartSelectedBoxTargetImageAutoData I x0 x1 omega a b)
    (O : BoundaryChartAtlasBoundarySignData I x0 x1 omega a b) :
    boundaryChartOrientedChangeOfVariables I x0 x1 omega a b
      T.targetLowerCorner T.targetUpperCorner :=
  (T.toOrientationCovData O).orientedChangeOfVariables

end BoundaryChartSelectedBoxTargetImageAutoData

namespace M8TargetImageInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/--
The orientation-facing M8 fields projected from an already resolved target-image
input.  This keeps target-image and orientation data indexed by the same
selected boundary pieces.
-/
def toM8TargetOrientationFields
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    M8TargetOrientationFields I omega BoundaryPiece D.targetImages where
  orientedBoundaryAtlas := orientedBoundaryAtlas
  source_mem := D.targetImages_source_mem
  boundarySource_mem := D.targetImages_boundarySource_mem

@[simp]
theorem toM8TargetOrientationFields_orientedBoundaryAtlas
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    D.toM8TargetOrientationFields.orientedBoundaryAtlas =
      orientedBoundaryAtlas :=
  rfl

/--
Selected-box boundary-sign data for one active target-image piece, using the
same source and boundary-source charts that the M8 target-image family records.
-/
def sourceSelectedBoxBoundarySignData
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    {x : M} (hx : x ∈ D.targetImages.activeCharts)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    BoundaryChartAtlasBoundarySignData I
      (D.targetImages.sourceChart x q)
      (D.targetImages.boundarySourceChart x q) omega
      (D.targetImages.sourceLowerCorner x q)
      (D.targetImages.sourceUpperCorner x q) :=
  orientedBoundaryAtlas.selectedBoxBoundarySignData
    (D.targetImages_source_mem x hx q hq)
    (D.targetImages_boundarySource_mem x hx q hq)
    (D.targetImages.sourceSelectedBox hx hq)

/--
Selected-box orientation/COV data for one active target-image piece.  This is
the pointwise bridge from resolved target boxes plus oriented atlas data to the
boundary chart-change theorem.
-/
def sourceSelectedBoxOrientationCovData
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    {x : M} (hx : x ∈ D.targetImages.activeCharts)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    BoundaryChartSelectedBoxOrientationCovData I
      (D.targetImages.sourceChart x q)
      (D.targetImages.boundarySourceChart x q) omega
      (D.targetImages.sourceLowerCorner x q)
      (D.targetImages.sourceUpperCorner x q)
      (D.targetImages.targetLowerCorner x q)
      (D.targetImages.targetUpperCorner x q) :=
  (D.sourceSelectedBoxBoundarySignData hx hq).toSelectedBoxOrientationCovData
    (D.targetImages.imageData x hx q hq)

/-- Pointwise oriented COV obtained from the aligned target-image input. -/
theorem sourceSelectedBox_orientedChangeOfVariables
    [IsManifold I 1 M]
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    {x : M} (hx : x ∈ D.targetImages.activeCharts)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    boundaryChartOrientedChangeOfVariables I
      (D.targetImages.sourceChart x q)
      (D.targetImages.boundarySourceChart x q) omega
      (D.targetImages.sourceLowerCorner x q)
      (D.targetImages.sourceUpperCorner x q)
      (D.targetImages.targetLowerCorner x q)
      (D.targetImages.targetUpperCorner x q) :=
  (D.sourceSelectedBoxOrientationCovData hx hq).orientedChangeOfVariables

end M8TargetImageInput

end TargetOrientationSelectedBoxAlignment

end Stokes

end
