import Stokes.Global.MixedGlobalConstructor
import Stokes.Global.LocalizedInteriorPieces
import Stokes.Global.BoundaryPieces
import Stokes.Global.BoundaryGlobalConstructor
import Stokes.Global.InteriorGlobalConstructor

/-!
# Selected-partition mixed global Stokes constructor

This file packages the inputs for the mixed global constructor when the chart
decomposition is tied to a selected-box partition of unity.  It deliberately
keeps the global bulk and boundary reconstruction as an explicit
`PartitionReconstructionData` field: no global integral reconstruction is
proved or faked here.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section MixedSelectedConstructor

universe u w i b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Input package for the mixed global constructor over a selected-box partition.

The selected partition records the geometric cover/box choices.  The
`reconstruction` field is still the explicit global integration input.  Local
Stokes, artificial-face cancellation, and boundary chart-change compatibility
are supplied by their own packages and merely aligned with the reconstruction
indices here.
-/
structure SelectedMixedGlobalInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (InteriorPiece : Type i) (BoundaryPiece : Type b) where
  /-- Selected partition of unity and selected interior boxes. -/
  selectedPartition : SelectedBoxPartitionOfUnity I omega
  /-- Reconstruction of the global integrals from the selected local sums. -/
  reconstruction : PartitionReconstructionData I omega M InteriorPiece BoundaryPiece
  /-- The reconstruction active set is the selected partition active set. -/
  selectedPartition_active :
    selectedPartition.active = reconstruction.activeCharts
  /-- Artificial boundary term supplied by the interior local constructor. -/
  interiorBoundaryTerm : M → InteriorPiece → Real
  /-- Boundary-chart term supplied by the boundary local constructor. -/
  boundaryBoundaryTerm : M → BoundaryPiece → Real
  /-- Local Stokes package for the selected interior pieces. -/
  interiorPackage :
    MixedInteriorPackage I omega M InteriorPiece
      reconstruction.activeCharts reconstruction.interiorPieces
      reconstruction.interiorBulkTerm interiorBoundaryTerm
  /-- Local Stokes package for the selected boundary pieces. -/
  boundaryPackage :
    MixedBoundaryPackage I omega M BoundaryPiece
      reconstruction.activeCharts reconstruction.boundaryPieces
      reconstruction.boundaryBulkTerm boundaryBoundaryTerm
  /-- Artificial-boundary cancellation package for the interior pieces. -/
  artificialCancellation : ArtificialBoundaryCancellationData M InteriorPiece
  /-- The cancellation package uses the reconstruction active set. -/
  artificialCancellation_active :
    artificialCancellation.activeCharts = reconstruction.activeCharts
  /-- The cancellation package uses the reconstruction interior pieces. -/
  artificialCancellation_pieces :
    artificialCancellation.interiorPieces = reconstruction.interiorPieces
  /-- The cancellation package uses the recorded interior boundary term. -/
  artificialCancellation_term :
    artificialCancellation.interiorBoundaryTerm = interiorBoundaryTerm
  /-- Boundary chart-change package for the selected boundary pieces. -/
  chartChange : ChartChangeCancellationData M BoundaryPiece Real
  /-- The chart-change package uses the reconstruction active set. -/
  chartChange_active :
    chartChange.activeCharts = reconstruction.activeCharts
  /-- The chart-change package uses the reconstruction boundary pieces. -/
  chartChange_pieces :
    chartChange.boundaryPieces = reconstruction.boundaryPieces
  /-- The chart-change package starts from the recorded boundary-chart term. -/
  chartChange_oldTerm :
    chartChange.oldBoundaryTerm = boundaryBoundaryTerm
  /-- The chart-change package ends at the reconstruction boundary partition term. -/
  chartChange_newTerm :
    chartChange.newBoundaryTerm = reconstruction.boundaryPartitionTerm

namespace SelectedMixedGlobalInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {InteriorPiece : Type i} {BoundaryPiece : Type b}

/-- Artificial-boundary cancellation in the exact mixed-constructor shape. -/
theorem interiorBoundaryCancellation
    (D : SelectedMixedGlobalInput I omega InteriorPiece BoundaryPiece) :
    (Finset.sum D.reconstruction.activeCharts fun x =>
      Finset.sum (D.reconstruction.interiorPieces x) fun q =>
        D.interiorBoundaryTerm x q) = 0 := by
  simpa [D.artificialCancellation_active, D.artificialCancellation_pieces,
    D.artificialCancellation_term] using D.artificialCancellation.cancellation

/-- Boundary chart-change cancellation in the exact mixed-constructor shape. -/
theorem chartChangeCancellation
    (D : SelectedMixedGlobalInput I omega InteriorPiece BoundaryPiece) :
    (Finset.sum D.reconstruction.activeCharts fun x =>
        Finset.sum (D.reconstruction.boundaryPieces x) fun q =>
          D.boundaryBoundaryTerm x q) =
      Finset.sum D.reconstruction.activeCharts fun x =>
        Finset.sum (D.reconstruction.boundaryPieces x) fun q =>
          D.reconstruction.boundaryPartitionTerm x q := by
  simpa [D.chartChange_active, D.chartChange_pieces, D.chartChange_oldTerm,
    D.chartChange_newTerm] using D.chartChange.chartChangeCancellation

/--
Convert selected mixed input into the existing mixed global Stokes data.

This is a bookkeeping conversion: reconstruction remains the explicit
`PartitionReconstructionData` field supplied by `D`.
-/
def toMixedGlobalStokesData
    (D : SelectedMixedGlobalInput I omega InteriorPiece BoundaryPiece) :
    MixedGlobalStokesData I omega M InteriorPiece BoundaryPiece where
  reconstruction := D.reconstruction
  interiorBoundaryTerm := D.interiorBoundaryTerm
  boundaryBoundaryTerm := D.boundaryBoundaryTerm
  interiorPackage := D.interiorPackage
  boundaryPackage := D.boundaryPackage
  interiorBoundaryCancellation := D.interiorBoundaryCancellation
  chartChangeCancellation := D.chartChangeCancellation

/-- Direct conversion to the final global data package. -/
def toGlobalStokesData
    (D : SelectedMixedGlobalInput I omega InteriorPiece BoundaryPiece) :
    GlobalStokesData I omega M InteriorPiece BoundaryPiece :=
  D.toMixedGlobalStokesData.toGlobalStokesData

@[simp]
theorem toMixedGlobalStokesData_reconstruction
    (D : SelectedMixedGlobalInput I omega InteriorPiece BoundaryPiece) :
    D.toMixedGlobalStokesData.reconstruction = D.reconstruction :=
  rfl

@[simp]
theorem toMixedGlobalStokesData_globalBulkIntegral
    (D : SelectedMixedGlobalInput I omega InteriorPiece BoundaryPiece) :
    D.toMixedGlobalStokesData.reconstruction.globalBulkIntegral =
      D.reconstruction.globalBulkIntegral :=
  rfl

@[simp]
theorem toMixedGlobalStokesData_globalBoundaryIntegral
    (D : SelectedMixedGlobalInput I omega InteriorPiece BoundaryPiece) :
    D.toMixedGlobalStokesData.reconstruction.globalBoundaryIntegral =
      D.reconstruction.globalBoundaryIntegral :=
  rfl

/-- Selected mixed constructor theorem. -/
theorem stokes
    (D : SelectedMixedGlobalInput I omega InteriorPiece BoundaryPiece) :
    D.reconstruction.globalBulkIntegral =
      D.reconstruction.globalBoundaryIntegral :=
  D.toMixedGlobalStokesData.stokes

end SelectedMixedGlobalInput

/-- Blueprint-facing selected mixed global Stokes wrapper. -/
theorem selectedMixedGlobalStokes
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {omega : ManifoldForm I M n}
    {InteriorPiece : Type i} {BoundaryPiece : Type b}
    (D : SelectedMixedGlobalInput I omega InteriorPiece BoundaryPiece) :
    D.reconstruction.globalBulkIntegral =
      D.reconstruction.globalBoundaryIntegral :=
  D.stokes

end MixedSelectedConstructor

end Stokes

end
