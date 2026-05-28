import Stokes.Global.MixedSelectedConstructor
import Stokes.Global.ProjectLocalConstructor
import Stokes.Global.BoundaryIntegralReconstruction
import Stokes.Global.IntegralReconstruction
import Stokes.Global.LocalizedSupport

/-!
# Natural-input data for the final global Stokes package

This file records the intended user-facing inputs for a future global Stokes
theorem: a compactly supported smooth form, oriented boundary-chart data,
selected partition boxes, and the still-explicit reconstruction/local fields.

No analytic reconstruction theorem is proved here.  The conversion to
`SelectedMixedGlobalInput` is only bookkeeping: the bulk and boundary
reconstruction packages are assembled into `PartitionReconstructionData`, and
the remaining local/cancellation/chart-change packages are passed through.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalInputData

universe u w i b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Compactly supported smooth top-degree input form data.

The support set is an explicit compact set containing the algebraic support of
the form.  This is intentionally weaker than a completed integration theorem:
it only records the compact-support and chartwise-smooth hypotheses that later
global integration reconstruction should consume.
-/
structure CompactlySupportedSmoothFormData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n) where
  /-- Compact manifold-side set controlling the form support. -/
  supportSet : Set M
  /-- Compactness of the chosen support set. -/
  isCompact_supportSet : IsCompact supportSet
  /-- The form vanishes outside the chosen compact support set. -/
  support_subset_supportSet : ManifoldForm.support I ω ⊆ supportSet
  /-- Chartwise smoothness of the manifold form. -/
  chartwiseSmooth : ManifoldForm.ChartwiseSmooth I ω

/--
Natural input package for the mixed global Stokes constructor.

The first fields are the natural geometric data expected at the final theorem
boundary.  The reconstruction and local/cancellation fields remain explicit:
this package does not attempt to prove compact-support integration
reconstruction, local Stokes, artificial-face cancellation, or chart-change
compatibility.
-/
structure NaturalGlobalStokesInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (InteriorPiece : Type i) (BoundaryPiece : Type b) where
  /-- Compactly supported smooth input form. -/
  formData : CompactlySupportedSmoothFormData I ω
  /--
  Oriented boundary-chart atlas data.  If the manifold is represented by the
  typeclass-style `BoundaryChartOrientedManifold`, use
  `BoundaryChartOrientedManifold.toOrientedAtlas` for this field.
  -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Selected partition of unity and selected interior boxes. -/
  selectedPartition : SelectedBoxPartitionOfUnity I ω
  /-- The selected partition is controlled by the compact form-support set. -/
  selectedPartition_supportSet :
    selectedPartition.K = formData.supportSet
  /-- Bulk integral reconstruction from selected interior and boundary pieces. -/
  bulkReconstruction :
    BulkIntegralReconstructionData I ω M InteriorPiece BoundaryPiece
  /-- Boundary contribution after chart changes and boundary reconstruction. -/
  boundaryPartitionTerm : M → BoundaryPiece → Real
  /-- The represented global boundary integral. -/
  globalBoundaryIntegral : Real
  /-- Boundary integral reconstruction from the selected boundary pieces. -/
  boundaryReconstruction :
    BoundaryIntegralReconstructionData bulkReconstruction.activeCharts
      bulkReconstruction.boundaryPieces boundaryPartitionTerm globalBoundaryIntegral
  /-- The selected partition active set matches the reconstruction active set. -/
  selectedPartition_active :
    selectedPartition.active = bulkReconstruction.activeCharts
  /-- Artificial boundary term supplied by the interior local constructor. -/
  interiorBoundaryTerm : M → InteriorPiece → Real
  /-- Boundary-chart term supplied by the boundary local constructor. -/
  boundaryBoundaryTerm : M → BoundaryPiece → Real
  /-- Local Stokes package for the selected interior pieces. -/
  interiorPackage :
    MixedInteriorPackage I ω M InteriorPiece
      bulkReconstruction.activeCharts bulkReconstruction.interiorPieces
      bulkReconstruction.interiorBulkTerm interiorBoundaryTerm
  /-- Local Stokes package for the selected boundary pieces. -/
  boundaryPackage :
    MixedBoundaryPackage I ω M BoundaryPiece
      bulkReconstruction.activeCharts bulkReconstruction.boundaryPieces
      bulkReconstruction.boundaryBulkTerm boundaryBoundaryTerm
  /-- Artificial-boundary cancellation package for the interior pieces. -/
  artificialCancellation : ArtificialBoundaryCancellationData M InteriorPiece
  /-- The cancellation package uses the reconstruction active set. -/
  artificialCancellation_active :
    artificialCancellation.activeCharts = bulkReconstruction.activeCharts
  /-- The cancellation package uses the reconstruction interior pieces. -/
  artificialCancellation_pieces :
    artificialCancellation.interiorPieces = bulkReconstruction.interiorPieces
  /-- The cancellation package uses the recorded interior boundary term. -/
  artificialCancellation_term :
    artificialCancellation.interiorBoundaryTerm = interiorBoundaryTerm
  /-- Boundary chart-change package for the selected boundary pieces. -/
  chartChange : ChartChangeCancellationData M BoundaryPiece Real
  /-- The chart-change package uses the reconstruction active set. -/
  chartChange_active :
    chartChange.activeCharts = bulkReconstruction.activeCharts
  /-- The chart-change package uses the reconstruction boundary pieces. -/
  chartChange_pieces :
    chartChange.boundaryPieces = bulkReconstruction.boundaryPieces
  /-- The chart-change package starts from the recorded boundary-chart term. -/
  chartChange_oldTerm :
    chartChange.oldBoundaryTerm = boundaryBoundaryTerm
  /-- The chart-change package ends at the reconstructed boundary partition term. -/
  chartChange_newTerm :
    chartChange.newBoundaryTerm = boundaryPartitionTerm

namespace NaturalGlobalStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {InteriorPiece : Type i} {BoundaryPiece : Type b}

/--
Assemble the separated bulk and boundary reconstruction fields into the
existing `PartitionReconstructionData` shape.
-/
def toPartitionReconstructionData
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    PartitionReconstructionData I ω M InteriorPiece BoundaryPiece :=
  PartitionReconstructionData.ofBoundaryIntegralReconstruction
    D.bulkReconstruction.activeCharts
    D.bulkReconstruction.interiorPieces
    D.bulkReconstruction.boundaryPieces
    D.bulkReconstruction.interiorBulkTerm
    D.bulkReconstruction.boundaryBulkTerm
    D.boundaryPartitionTerm
    D.bulkReconstruction.globalBulkIntegral
    D.globalBoundaryIntegral
    D.bulkReconstruction.globalBulkIntegral_eq_localBulkSum
    D.boundaryReconstruction

@[simp]
theorem toPartitionReconstructionData_activeCharts
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    D.toPartitionReconstructionData.activeCharts =
      D.bulkReconstruction.activeCharts :=
  rfl

@[simp]
theorem toPartitionReconstructionData_globalBulkIntegral
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    D.toPartitionReconstructionData.globalBulkIntegral =
      D.bulkReconstruction.globalBulkIntegral :=
  rfl

@[simp]
theorem toPartitionReconstructionData_globalBoundaryIntegral
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    D.toPartitionReconstructionData.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

@[simp]
theorem toPartitionReconstructionData_boundaryPartitionTerm
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    D.toPartitionReconstructionData.boundaryPartitionTerm =
      D.boundaryPartitionTerm :=
  rfl

/--
Convert natural global input into the selected mixed constructor input.

This is a clean field projection.  All mathematical obligations used by
`SelectedMixedGlobalInput` are already explicit fields of `D`.
-/
def toSelectedMixedGlobalInput
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    SelectedMixedGlobalInput I ω InteriorPiece BoundaryPiece where
  selectedPartition := D.selectedPartition
  reconstruction := D.toPartitionReconstructionData
  selectedPartition_active := by
    simpa [toPartitionReconstructionData] using D.selectedPartition_active
  interiorBoundaryTerm := D.interiorBoundaryTerm
  boundaryBoundaryTerm := D.boundaryBoundaryTerm
  interiorPackage := by
    simpa [toPartitionReconstructionData] using D.interiorPackage
  boundaryPackage := by
    simpa [toPartitionReconstructionData] using D.boundaryPackage
  artificialCancellation := D.artificialCancellation
  artificialCancellation_active := by
    simpa [toPartitionReconstructionData] using D.artificialCancellation_active
  artificialCancellation_pieces := by
    simpa [toPartitionReconstructionData] using D.artificialCancellation_pieces
  artificialCancellation_term := D.artificialCancellation_term
  chartChange := D.chartChange
  chartChange_active := by
    simpa [toPartitionReconstructionData] using D.chartChange_active
  chartChange_pieces := by
    simpa [toPartitionReconstructionData] using D.chartChange_pieces
  chartChange_oldTerm := D.chartChange_oldTerm
  chartChange_newTerm := by
    simpa [toPartitionReconstructionData] using D.chartChange_newTerm

@[simp]
theorem toSelectedMixedGlobalInput_selectedPartition
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    D.toSelectedMixedGlobalInput.selectedPartition = D.selectedPartition :=
  rfl

@[simp]
theorem toSelectedMixedGlobalInput_reconstruction
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    D.toSelectedMixedGlobalInput.reconstruction =
      D.toPartitionReconstructionData :=
  rfl

@[simp]
theorem toSelectedMixedGlobalInput_globalBulkIntegral
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    D.toSelectedMixedGlobalInput.reconstruction.globalBulkIntegral =
      D.bulkReconstruction.globalBulkIntegral :=
  rfl

@[simp]
theorem toSelectedMixedGlobalInput_globalBoundaryIntegral
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    D.toSelectedMixedGlobalInput.reconstruction.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

end NaturalGlobalStokesInput

end NaturalInputData

end Stokes

end
