import Stokes.Global.NaturalInputData
import Stokes.Global.Theorem

/-!
# Natural global Stokes statement

This file gives the current most user-facing wrapper for global Stokes.

The natural input data is defined in `Stokes.Global.NaturalInputData`.  This
module only proves the theorem projections from that data, so the public
statement stays aligned with the single natural-input record.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalStatement

universe u w i b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace NaturalGlobalStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {InteriorPiece : Type i} {BoundaryPiece : Type b}

/-- The selected mixed input carried by a natural global package. -/
abbrev selectedMixedInput
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    SelectedMixedGlobalInput I ω InteriorPiece BoundaryPiece :=
  D.toSelectedMixedGlobalInput

/-- The reconstruction package underlying the natural global statement. -/
abbrev reconstruction
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    PartitionReconstructionData I ω M InteriorPiece BoundaryPiece :=
  D.toPartitionReconstructionData

/-- Conversion to the mixed global constructor package. -/
abbrev toMixedGlobalStokesData
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    MixedGlobalStokesData I ω M InteriorPiece BoundaryPiece :=
  D.toSelectedMixedGlobalInput.toMixedGlobalStokesData

/-- Conversion to the final global Stokes data package. -/
abbrev toGlobalStokesData
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    GlobalStokesData I ω M InteriorPiece BoundaryPiece :=
  D.toSelectedMixedGlobalInput.toGlobalStokesData

@[simp]
theorem selectedMixedInput_eq
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    D.selectedMixedInput = D.toSelectedMixedGlobalInput :=
  rfl

@[simp]
theorem reconstruction_eq
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    D.reconstruction = D.toPartitionReconstructionData :=
  rfl

@[simp]
theorem toMixedGlobalStokesData_reconstruction
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    D.toMixedGlobalStokesData.reconstruction = D.reconstruction :=
  rfl

@[simp]
theorem toGlobalStokesData_globalBulkIntegral
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    D.toGlobalStokesData.globalBulkIntegral =
      D.bulkReconstruction.globalBulkIntegral :=
  rfl

@[simp]
theorem toGlobalStokesData_globalBoundaryIntegral
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    D.toGlobalStokesData.globalBoundaryIntegral = D.globalBoundaryIntegral :=
  rfl

/-- The selected mixed constructor proves Stokes for the represented integrals. -/
theorem reconstruction_stokes
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    D.reconstruction.globalBulkIntegral =
      D.reconstruction.globalBoundaryIntegral :=
  D.toSelectedMixedGlobalInput.stokes

/--
Natural global Stokes theorem for the current selected-partition input.

The bulk side is the represented global bulk integral in
`D.bulkReconstruction`; the boundary side is the represented global boundary
integral field of `D`.
-/
theorem stokes
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    D.bulkReconstruction.globalBulkIntegral = D.globalBoundaryIntegral := by
  calc
    D.bulkReconstruction.globalBulkIntegral =
        D.reconstruction.globalBulkIntegral := by
      exact D.toPartitionReconstructionData_globalBulkIntegral.symm
    _ = D.reconstruction.globalBoundaryIntegral := D.reconstruction_stokes
    _ = D.globalBoundaryIntegral := D.toPartitionReconstructionData_globalBoundaryIntegral

/-- Final-data version of the natural wrapper, useful for downstream projections. -/
theorem toGlobalStokesData_stokes
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    D.toGlobalStokesData.globalBulkIntegral =
      D.toGlobalStokesData.globalBoundaryIntegral :=
  globalStokes D.toGlobalStokesData

end NaturalGlobalStokesInput

/-- Blueprint-facing natural global Stokes wrapper. -/
theorem naturalGlobalStokes
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    {InteriorPiece : Type i} {BoundaryPiece : Type b}
    (D : NaturalGlobalStokesInput I ω InteriorPiece BoundaryPiece) :
    D.bulkReconstruction.globalBulkIntegral = D.globalBoundaryIntegral :=
  D.stokes

end NaturalStatement

end Stokes

end
