import Stokes.Global.BoundaryMeasureCanonicalRoute
import Stokes.Global.BoundaryMeasureTargetAssembly
import Stokes.Global.TargetImageResolvedToM8Input
import Stokes.Global.TargetImageLocalOpennessToM8
import Stokes.Global.TargetImageIFTToM8
import Stokes.BoundaryChart.TargetImageSelectedBoxAuto

/-!
# Boundary target selected-box alignment

This file is a bookkeeping layer for the boundary-measure / target-image handoff.
It records the alignments that are already present in the target-image route:

* target-image active charts are the selected partition active charts;
* boundary-measure partition data uses the same boundary pieces and partition
  term as the target-image assembly;
* resolved/local-openness/IFT target-image packages feed the same M8 target-image
  input shape;
* the boundary partition term is the selected project-local boundary integral.

No boundary change-of-variables theorem or genuine boundary measure equality is
proved here.  Those remain explicit inputs of the canonical boundary-measure
route.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryTargetSelectedBoxAlignment

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {α : Type a} [MeasurableSpace α]
variable {μ : Measure α}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/--
The selected-box alignment data carried by an M8 target-image input.

This is intentionally only structural alignment: active charts, boundary pieces,
partition terms, and the already-recorded project-local endpoint equality.
-/
structure BoundaryTargetSelectedBoxAlignmentData
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) where
  /-- The target-image family is indexed by the selected partition active set. -/
  targetImages_active_eq_selected :
    D.targetImages.activeCharts = selectedPartition.active
  /-- Boundary-measure partition data is also indexed by the selected active set. -/
  partitionData_active_eq_selected :
    D.toSelectedBoundaryMeasurePartitionData.activeCharts =
      selectedPartition.active
  /-- Boundary-measure partition pieces are the target-image boundary pieces. -/
  partitionData_boundaryPieces_eq_target :
    D.toSelectedBoundaryMeasurePartitionData.boundaryPieces =
      D.targetImages.boundaryPieces
  /-- Boundary-measure partition terms are the target-image assembly terms. -/
  partitionData_boundaryPartitionTerm_eq_assembly :
    D.toSelectedBoundaryMeasurePartitionData.boundaryPartitionTerm =
      D.assembly.boundaryPartitionTerm
  /--
  On selected active charts, the assembly boundary partition term is exactly the
  selected project-local boundary integral recorded by the target-image route.
  -/
  boundaryPartitionTerm_eq_projectLocal :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ D.targetImages.boundaryPieces x →
        D.assembly.boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I
            (D.assembly.boundaryTargetChart x q)
            (D.assembly.partitionTargetChart x q) omega
            (D.assembly.partitionLowerCorner x q)
            (D.assembly.partitionUpperCorner x q)

namespace M8TargetImageInput

variable
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)

/-- Selected-active version of the assembly endpoint identity. -/
theorem boundaryPartitionTerm_eq_projectLocal_of_selected
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    D.assembly.boundaryPartitionTerm x q =
      projectLocalBoundaryIntegral I
        (D.assembly.boundaryTargetChart x q)
        (D.assembly.partitionTargetChart x q) omega
        (D.assembly.partitionLowerCorner x q)
        (D.assembly.partitionUpperCorner x q) := by
  have hx' : x ∈ D.assembly.activeCharts := by
    simpa [D.active_eq] using hx
  simpa [targetImages] using
    D.assembly.boundaryPartitionTerm_eq x hx' q hq

/-- Bundle the selected-box alignment data exposed by an M8 target-image input. -/
def boundaryTargetSelectedBoxAlignmentData :
    BoundaryTargetSelectedBoxAlignmentData D where
  targetImages_active_eq_selected := D.targetImages_active
  partitionData_active_eq_selected :=
    D.toSelectedBoundaryMeasurePartitionData_activeCharts
  partitionData_boundaryPieces_eq_target :=
    D.toSelectedBoundaryMeasurePartitionData_boundaryPieces
  partitionData_boundaryPartitionTerm_eq_assembly :=
    D.toSelectedBoundaryMeasurePartitionData_boundaryPartitionTerm
  boundaryPartitionTerm_eq_projectLocal := by
    intro x hx q hq
    exact D.boundaryPartitionTerm_eq_projectLocal_of_selected hx hq

@[simp]
theorem boundaryTargetSelectedBoxAlignmentData_active :
    D.boundaryTargetSelectedBoxAlignmentData.targetImages_active_eq_selected =
      D.targetImages_active := rfl

@[simp]
theorem boundaryTargetSelectedBoxAlignmentData_partitionTerm :
    (D.boundaryTargetSelectedBoxAlignmentData).partitionData_boundaryPartitionTerm_eq_assembly =
      D.toSelectedBoundaryMeasurePartitionData_boundaryPartitionTerm := rfl

end M8TargetImageInput

namespace M8TargetImageResolvedInput

variable
    (D :
      M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)

/-- Resolved target-image data routed to the canonical M8 target-image input. -/
abbrev selectedBoxM8TargetInput :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece :=
  D.toM8TargetImageInput

/-- Alignment package for a resolved target-image input after routing to M8. -/
def boundaryTargetSelectedBoxAlignmentData :
    BoundaryTargetSelectedBoxAlignmentData D.selectedBoxM8TargetInput :=
  D.selectedBoxM8TargetInput.boundaryTargetSelectedBoxAlignmentData

@[simp]
theorem selectedBoxM8TargetInput_targetImages :
    D.selectedBoxM8TargetInput.targetImages =
      D.toM8TargetImageInput.targetImages := rfl

@[simp]
theorem selectedBoxM8TargetInput_active :
    D.selectedBoxM8TargetInput.targetImages.activeCharts =
      selectedPartition.active :=
  D.toM8TargetImageInput.targetImages_active

@[simp]
theorem selectedBoxM8TargetInput_boundaryPieces :
    D.selectedBoxM8TargetInput.targetImages.boundaryPieces =
      D.family.localPieces := rfl

@[simp]
theorem selectedBoxM8TargetInput_boundaryPartitionTerm :
    D.selectedBoxM8TargetInput.assembly.boundaryPartitionTerm =
      D.boundaryPartitionTerm := rfl

/--
Resolved-input version of the selected project-local endpoint identity, stated
with the boundary partition term carried by the resolved input.
-/
theorem boundaryPartitionTerm_eq_projectLocal_of_selected
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece}
    (hq : q ∈ D.selectedBoxM8TargetInput.targetImages.boundaryPieces x) :
    D.boundaryPartitionTerm x q =
      projectLocalBoundaryIntegral I
        (D.family.boundaryTargetChart x q)
        (D.partitionTargetChart x q) omega
        ((D.partitionTargetBox x q).lowerCorner)
        ((D.partitionTargetBox x q).upperCorner) := by
  have hxF : x ∈ D.family.activeCharts := by
    simpa [D.active_eq] using hx
  have hqF : q ∈ D.family.localPieces x := by
    simpa using hq
  exact D.boundaryPartitionTerm_eq x hxF q hqF

end M8TargetImageResolvedInput

namespace M8TargetImageLocalOpennessInput

variable
    (D :
      M8TargetImageLocalOpennessInput I omega selectedPartition
        orientedBoundaryAtlas BoundaryPiece)

/-- Local-openness target-image data routed through the resolved M8 input. -/
abbrev selectedBoxResolvedInput :
    M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece :=
  D.toResolvedInput

/-- Alignment package for local-openness target-image data after routing to M8. -/
def boundaryTargetSelectedBoxAlignmentData :
    BoundaryTargetSelectedBoxAlignmentData D.toM8TargetImageInput :=
  D.toM8TargetImageInput.boundaryTargetSelectedBoxAlignmentData

@[simp]
theorem toM8TargetImageInput_active :
    D.toM8TargetImageInput.targetImages.activeCharts =
      selectedPartition.active :=
  D.toM8TargetImageInput.targetImages_active

@[simp]
theorem toM8TargetImageInput_boundaryPartitionTerm :
    D.toM8TargetImageInput.assembly.boundaryPartitionTerm =
      D.boundaryPartitionTerm := rfl

/-- Local-openness version of the selected project-local endpoint identity. -/
theorem boundaryPartitionTerm_eq_projectLocal_of_selected
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece}
    (hq : q ∈ D.toM8TargetImageInput.targetImages.boundaryPieces x) :
    D.boundaryPartitionTerm x q =
      projectLocalBoundaryIntegral I
        (D.family.toTargetImageResolvedFamily.boundaryTargetChart x q)
        (D.partitionTargetChart x q) omega
        ((D.partitionTargetBox x q).lowerCorner)
        ((D.partitionTargetBox x q).upperCorner) :=
  D.toResolvedInput.boundaryPartitionTerm_eq_projectLocal_of_selected hx hq

end M8TargetImageLocalOpennessInput

namespace M8TargetImageIFTInput

variable
    (D :
      M8TargetImageIFTInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)

/-- IFT target-image data routed through the resolved M8 input. -/
abbrev selectedBoxResolvedInput :
    M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece :=
  D.toResolvedInput

/-- Alignment package for IFT target-image data after routing to M8. -/
def boundaryTargetSelectedBoxAlignmentData :
    BoundaryTargetSelectedBoxAlignmentData D.toM8TargetImageInput :=
  D.toM8TargetImageInput.boundaryTargetSelectedBoxAlignmentData

@[simp]
theorem toM8TargetImageInput_active :
    D.toM8TargetImageInput.targetImages.activeCharts =
      selectedPartition.active :=
  D.toM8TargetImageInput.targetImages_active

@[simp]
theorem toM8TargetImageInput_boundaryPartitionTerm :
    D.toM8TargetImageInput.assembly.boundaryPartitionTerm =
      D.boundaryPartitionTerm := rfl

/-- IFT version of the selected project-local endpoint identity. -/
theorem boundaryPartitionTerm_eq_projectLocal_of_selected
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece}
    (hq : q ∈ D.toM8TargetImageInput.targetImages.boundaryPieces x) :
    D.boundaryPartitionTerm x q =
      projectLocalBoundaryIntegral I
        (D.family.toTargetImageResolvedFamily.boundaryTargetChart x q)
        (D.partitionTargetChart x q) omega
        ((D.partitionTargetBox x q).lowerCorner)
        ((D.partitionTargetBox x q).upperCorner) :=
  D.toResolvedInput.boundaryPartitionTerm_eq_projectLocal_of_selected hx hq

end M8TargetImageIFTInput

namespace CanonicalBoundaryTargetCompactSupportInput

variable [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
variable [IsFiniteMeasureOnCompacts μ]
variable
    {D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}
    (B : CanonicalBoundaryTargetCompactSupportInput (α := α) D μ)

/--
The canonical boundary compact-support route uses the same selected-box
alignment package as its target-image input.
-/
def boundaryTargetSelectedBoxAlignmentData :
    BoundaryTargetSelectedBoxAlignmentData D :=
  D.boundaryTargetSelectedBoxAlignmentData

@[simp]
theorem canonicalBoundaryCompactFields_active :
    B.canonicalBoundaryCompactFields.boundaryMeasureIntegral =
      B.boundaryMeasureIntegral := rfl

@[simp]
theorem canonicalBoundaryM8MeasureData_boundaryPartitionTerm_eq_target :
    B.canonicalBoundaryM8MeasureData.boundaryPartitionTerm =
      D.assembly.boundaryPartitionTerm := rfl

/--
Canonical boundary data reconstructs the boundary measure from the selected
target-image pieces and the target-image assembly partition term.
-/
theorem canonicalBoundaryM8MeasureData_boundaryMeasureIntegral_eq_selectedTargetSum :
    B.canonicalBoundaryM8MeasureData.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        D.targetImages.boundaryPieces D.assembly.boundaryPartitionTerm :=
  B.canonicalBoundaryM8MeasureData_boundaryMeasureIntegral_eq_partitionSum

end CanonicalBoundaryTargetCompactSupportInput

end BoundaryTargetSelectedBoxAlignment

end Stokes

end
