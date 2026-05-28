import Stokes.Global.MixedSelectedConstructor
import Stokes.Global.ArtificialFaceSelection
import Stokes.Global.BoundaryPieceFamilyConstructor

/-!
# Global Stokes prototype input

This file gives a prototype M7-facing theorem around the strongest current
selected mixed constructor.  The not-yet-analytic parts are still explicit:
global integral reconstruction, artificial-face cancellation data, and
boundary target-image data.

There is not yet a separate `NaturalInputData` module in this workspace, so the
prototype keeps those natural-facing fields directly in the input structure.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section GlobalStokesPrototype

universe u w i b f

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Prototype input for the M7 global Stokes wrapper.

The statement is close to the intended natural data: it starts from a selected
partition, selected artificial faces for the interior boxes, and a boundary
piece family carrying target-image data.  The remaining global reconstruction
and boundary-partition comparison fields are deliberately explicit.
-/
structure GlobalStokesPrototypeInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (InteriorPiece : Type i) (BoundaryPiece : Type b) (Face : Type f) where
  /-- Selected partition of unity and interior chart boxes. -/
  selectedPartition : SelectedBoxPartitionOfUnity I omega
  /-- Reconstruction of the two represented global integrals from local sums. -/
  reconstruction : PartitionReconstructionData I omega M InteriorPiece BoundaryPiece
  /-- The reconstruction active set is the selected partition active set. -/
  selectedPartition_active :
    selectedPartition.active = reconstruction.activeCharts
  /-- Artificial boundary term supplied by the interior local constructor. -/
  interiorBoundaryTerm : M → InteriorPiece → Real
  /-- Local Stokes on every reconstructed interior piece. -/
  interiorLocalStokes :
    ∀ x, x ∈ reconstruction.activeCharts →
      ∀ q, q ∈ reconstruction.interiorPieces x →
        reconstruction.interiorBulkTerm x q = interiorBoundaryTerm x q
  /-- Selected artificial-face data explaining cancellation of interior faces. -/
  artificialFaces :
    SelectedBoxArtificialFaceFamilyData I omega M InteriorPiece Face
  /-- Artificial-face data uses the reconstruction active set. -/
  artificialFaces_active :
    artificialFaces.activeCharts = reconstruction.activeCharts
  /-- Artificial-face data uses the reconstruction interior pieces. -/
  artificialFaces_pieces :
    artificialFaces.interiorPieces = reconstruction.interiorPieces
  /-- The recorded interior boundary term is the selected-box project boundary term. -/
  artificialFaces_boundaryTerm :
    ∀ x, x ∈ artificialFaces.activeCharts →
      ∀ q, q ∈ artificialFaces.interiorPieces x →
        interiorBoundaryTerm x q = artificialFaces.projectBoundaryTerm x q
  /--
  Boundary pieces carrying source boxes, selected target boxes, and image data.
  This is the explicit target-image field of the prototype.
  -/
  targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece
  /-- Target-image boundary data uses the reconstruction active set. -/
  targetImages_active :
    targetImages.activeCharts = reconstruction.activeCharts
  /-- Target-image boundary data uses the reconstruction boundary pieces. -/
  targetImages_boundaryPieces :
    targetImages.boundaryPieces = reconstruction.boundaryPieces
  /-- Target-image boundary bulk terms are the reconstruction boundary bulk terms. -/
  targetImages_boundaryBulkTerm :
    BoundaryPieceFamilyInput.boundaryBulkTerm targetImages =
      reconstruction.boundaryBulkTerm
  /-- Boundary term after transport to the selected target image. -/
  boundaryBoundaryTerm : M → BoundaryPiece → Real
  /-- The transported target-image term is the recorded boundary boundary term. -/
  targetImages_boundaryBoundaryTerm :
    BoundaryPieceFamilyInput.boundaryBoundaryTerm targetImages =
      boundaryBoundaryTerm
  /-- The transported target-image terms agree with the boundary partition terms. -/
  targetBoundaryTerm_eq_partition :
    ∀ x, x ∈ reconstruction.activeCharts →
      ∀ q, q ∈ reconstruction.boundaryPieces x →
        boundaryBoundaryTerm x q = reconstruction.boundaryPartitionTerm x q

namespace GlobalStokesPrototypeInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {InteriorPiece : Type i} {BoundaryPiece : Type b} {Face : Type f}

/-- Interior local Stokes data in the mixed-constructor package shape. -/
def toMixedInteriorPackage
    (D : GlobalStokesPrototypeInput I omega InteriorPiece BoundaryPiece Face) :
    MixedInteriorPackage I omega M InteriorPiece
      D.reconstruction.activeCharts D.reconstruction.interiorPieces
      D.reconstruction.interiorBulkTerm D.interiorBoundaryTerm where
  localStokes := D.interiorLocalStokes

/--
Boundary target-image data in the mixed-constructor package shape.

The source is `BoundaryPieceFamilyInput`, whose fields include the selected
target boxes and image data needed for the local boundary Stokes theorem.
-/
def toMixedBoundaryPackage
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : GlobalStokesPrototypeInput I omega InteriorPiece BoundaryPiece Face) :
    MixedBoundaryPackage I omega M BoundaryPiece
      D.reconstruction.activeCharts D.reconstruction.boundaryPieces
      D.reconstruction.boundaryBulkTerm D.boundaryBoundaryTerm := by
  simpa [D.targetImages_active, D.targetImages_boundaryPieces,
    D.targetImages_boundaryBulkTerm, D.targetImages_boundaryBoundaryTerm] using
    D.targetImages.toMixedBoundaryPackage

/-- Artificial-face cancellation in the exact reconstruction-indexed shape. -/
theorem interiorBoundaryCancellation
    (D : GlobalStokesPrototypeInput I omega InteriorPiece BoundaryPiece Face) :
    (Finset.sum D.reconstruction.activeCharts fun x =>
      Finset.sum (D.reconstruction.interiorPieces x) fun q =>
        D.interiorBoundaryTerm x q) = 0 := by
  simpa [D.artificialFaces_active, D.artificialFaces_pieces] using
    (D.artificialFaces.interiorBoundaryCancellation_of_boundaryTerm
      D.interiorBoundaryTerm D.artificialFaces_boundaryTerm)

/-- Artificial-face cancellation as the package expected by the selected constructor. -/
def toArtificialBoundaryCancellationData
    (D : GlobalStokesPrototypeInput I omega InteriorPiece BoundaryPiece Face) :
    ArtificialBoundaryCancellationData M InteriorPiece where
  activeCharts := D.reconstruction.activeCharts
  interiorPieces := D.reconstruction.interiorPieces
  interiorBoundaryTerm := D.interiorBoundaryTerm
  cancellation := D.interiorBoundaryCancellation

/-- Target-image-to-boundary-partition comparison as chart-change data. -/
def toChartChangeCancellationData
    (D : GlobalStokesPrototypeInput I omega InteriorPiece BoundaryPiece Face) :
    ChartChangeCancellationData M BoundaryPiece Real where
  activeCharts := D.reconstruction.activeCharts
  boundaryPieces := D.reconstruction.boundaryPieces
  oldBoundaryTerm := D.boundaryBoundaryTerm
  newBoundaryTerm := D.reconstruction.boundaryPartitionTerm
  term_eq := D.targetBoundaryTerm_eq_partition

/-- Convert the prototype input to the current selected mixed constructor input. -/
def toSelectedMixedGlobalInput
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : GlobalStokesPrototypeInput I omega InteriorPiece BoundaryPiece Face) :
    SelectedMixedGlobalInput I omega InteriorPiece BoundaryPiece where
  selectedPartition := D.selectedPartition
  reconstruction := D.reconstruction
  selectedPartition_active := D.selectedPartition_active
  interiorBoundaryTerm := D.interiorBoundaryTerm
  boundaryBoundaryTerm := D.boundaryBoundaryTerm
  interiorPackage := D.toMixedInteriorPackage
  boundaryPackage := D.toMixedBoundaryPackage
  artificialCancellation := D.toArtificialBoundaryCancellationData
  artificialCancellation_active := rfl
  artificialCancellation_pieces := rfl
  artificialCancellation_term := rfl
  chartChange := D.toChartChangeCancellationData
  chartChange_active := rfl
  chartChange_pieces := rfl
  chartChange_oldTerm := rfl
  chartChange_newTerm := rfl

/-- Prototype M7 Stokes theorem for the natural-facing input package. -/
theorem stokes
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : GlobalStokesPrototypeInput I omega InteriorPiece BoundaryPiece Face) :
    D.reconstruction.globalBulkIntegral =
      D.reconstruction.globalBoundaryIntegral :=
  selectedMixedGlobalStokes D.toSelectedMixedGlobalInput

end GlobalStokesPrototypeInput

/--
M7 prototype global Stokes theorem.

This wrapper exposes a natural-facing input package while still keeping the
global reconstruction, artificial-face cancellation, and target-image boundary
fields explicit.
-/
theorem globalStokesPrototype
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    {omega : ManifoldForm I M n}
    {InteriorPiece : Type i} {BoundaryPiece : Type b} {Face : Type f}
    (D : GlobalStokesPrototypeInput I omega InteriorPiece BoundaryPiece Face) :
    D.reconstruction.globalBulkIntegral =
      D.reconstruction.globalBoundaryIntegral :=
  D.stokes

end GlobalStokesPrototype

end Stokes

end
