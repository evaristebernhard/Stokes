import Stokes.Global.BoundaryIntegralPartitionReconstruction
import Stokes.Global.TargetImageToM8

/-!
# Boundary partition-term alignment

This file centralizes the pointwise boundary-term identification used by the
boundary reconstruction route.

The mathematical content is the selected boundary chart-change theorem:
the transported boundary term produced by local half-space Stokes agrees with
the selected boundary partition term.  The lemmas below expose that same fact
at the selected-assembly, target-image assembly, and M8 target-image layers.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryPartitionTermAlignment

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {Piece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

namespace SelectedBoundaryAssemblyData

/--
The boundary-piece family induced by selected boundary assembly data has the
same transported boundary term as the selected boundary partition term.
-/
theorem boundaryPieceFamily_boundaryBoundaryTerm_eq_boundaryPartitionTerm
    [IsManifold I 1 M]
    (D : SelectedBoundaryAssemblyData I ω Chart Piece) :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.boundaryPieces x →
        BoundaryPieceFamilyInput.boundaryBoundaryTerm
            D.toBoundaryPieceFamilyInput x q =
          D.boundaryPartitionTerm x q := by
  intro x hx q hq
  simpa [toBoundaryPieceFamilyInput, boundaryBoundaryTerm,
    BoundaryPieceFamilyInput.boundaryBoundaryTerm] using
    D.pointwise_chartChange x hx q hq

end SelectedBoundaryAssemblyData

namespace BoundaryTargetImageToAssemblyInput

/--
Target-image assembly data, together with oriented-atlas chart-change data,
identifies the transported target-image boundary term with the selected
boundary partition term pointwise.
-/
theorem boundaryPieceFamily_boundaryBoundaryTerm_eq_boundaryPartitionTerm_of_orientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryTargetImageToAssemblyInput I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hboundarySource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → D.boundarySourceChart x q ∈ A.charts)
    (hboundaryTarget :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → D.boundaryTargetChart x q ∈ A.charts) :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.boundaryPieces x →
        BoundaryPieceFamilyInput.boundaryBoundaryTerm
            D.targetImageData.toBoundaryPieceFamilyInput x q =
          D.boundaryPartitionTerm x q := by
  intro x hx q hq
  let S := D.toSelectedBoundaryAssemblyData_of_orientedAtlas
    A hboundarySource hboundaryTarget
  have hpoint :
      BoundaryPieceFamilyInput.boundaryBoundaryTerm
          S.toBoundaryPieceFamilyInput x q =
        S.boundaryPartitionTerm x q :=
    S.boundaryPieceFamily_boundaryBoundaryTerm_eq_boundaryPartitionTerm
      x (by simpa [S] using hx) q (by simpa [S] using hq)
  simpa [S, toSelectedBoundaryAssemblyData_of_orientedAtlas,
    toBoundaryOrientationSelectedAssemblyInput,
    BoundaryOrientationSelectedAssemblyInput.toSelectedBoundaryAssemblyData_of_orientedAtlas,
    BoundaryTargetImageFieldReductionData.toBoundaryPieceFamilyInput] using
    hpoint

end BoundaryTargetImageToAssemblyInput

namespace M8TargetImageInput

variable {selectedPartition : SelectedBoxPartitionOfUnity I ω}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/--
M8-facing pointwise boundary-term identification against the boundary
partition term recorded by the underlying assembly input.
-/
theorem boundaryBoundaryTerm_eq_assemblyBoundaryPartitionTerm
    [IsManifold I 1 M]
    (D :
      M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece) :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ D.targetImages.boundaryPieces x →
        BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages x q =
          D.assembly.boundaryPartitionTerm x q := by
  simpa using
    D.targetBoundaryTerm_eq_partition D.assembly.boundaryPartitionTerm rfl

/--
The same pointwise alignment in the exact shape expected by an external
boundary measure-localization package.
-/
theorem boundaryBoundaryTerm_eq_measureLocalization
    [IsManifold I 1 M]
    (D :
      M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece)
    (measureLocalization :
      M8MeasureLocalizationData I ω selectedPartition D.targetImages)
    (hterm :
      D.assembly.boundaryPartitionTerm =
        measureLocalization.boundaryPartitionTerm) :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ D.targetImages.boundaryPieces x →
        BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages x q =
          measureLocalization.boundaryPartitionTerm x q :=
  D.targetBoundaryTerm_eq_measureLocalization measureLocalization hterm

/--
Outward-first target boundary chart integrals are the selected assembly
boundary partition terms pointwise.
-/
theorem outwardFirstBoundaryChartIntegral_eq_assemblyBoundaryPartitionTerm
    [IsManifold I 1 M]
    (D :
      M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece) :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ D.targetImages.boundaryPieces x →
        outwardFirstBoundaryChartIntegral I
            (D.targetImages.boundarySourceChart x q)
            (D.targetImages.boundaryTargetChart x q) ω
            (D.targetImages.targetLowerCorner x q)
            (D.targetImages.targetUpperCorner x q) =
          D.assembly.boundaryPartitionTerm x q := by
  intro x hx q hq
  exact D.boundaryBoundaryTerm_eq_assemblyBoundaryPartitionTerm x hx q hq

/--
Boundary partition reconstruction for the selected assembly partition term,
when the represented global boundary integral is the transported boundary sum.
-/
def boundaryIntegralPartitionReconstructionData_of_assemblyBoundaryPartitionTerm
    [IsManifold I 1 M]
    (D :
      M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece)
    (globalBoundaryIntegral : Real)
    (hglobal :
      globalBoundaryIntegral =
        BoundaryPieceFamilyInput.boundaryBoundarySum D.targetImages) :
    BoundaryIntegralPartitionReconstructionData
      D.targetImages.activeCharts D.targetImages.boundaryPieces
      D.assembly.boundaryPartitionTerm globalBoundaryIntegral :=
  D.targetImages.boundaryIntegralPartitionReconstructionData_ofBoundaryBoundaryTermEq
    D.assembly.boundaryPartitionTerm globalBoundaryIntegral hglobal (by
      intro x hx q hq
      have hx' : x ∈ selectedPartition.active := by
        simpa [D.targetImages_active] using hx
      exact D.boundaryBoundaryTerm_eq_assemblyBoundaryPartitionTerm x hx' q hq)

end M8TargetImageInput

end BoundaryPartitionTermAlignment

end Stokes

end
