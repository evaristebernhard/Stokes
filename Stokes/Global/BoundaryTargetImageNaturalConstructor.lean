import Stokes.Global.TargetImageResolvedToM8Input
import Stokes.Global.TargetImageLocalOpennessToM8
import Stokes.Global.TargetImageIFTToM8

/-!
# Natural boundary target-image constructor

This file provides a thin constructor from already selected boundary target
assembly data to the M8 target-image input.  The assembly data contains the
selected boundary boxes, image data, and boundary-partition endpoint data; the
only remaining M8 facts are the selected active-set alignment and oriented-atlas
membership of the chart labels.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryTargetImageNaturalConstructor

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

namespace BoundaryTargetImageToAssemblyInput

/--
Direct M8 target-image constructor from selected boundary target assembly data.

The geometric payload stays in `D`: source extended boxes, selected target
boxes, image data, partition target boxes, and the endpoint identification for
the boundary partition term.  This constructor adds only the active-set
alignment and oriented-atlas membership facts that are genuinely M8-facing.
-/
def toM8TargetImageInput
    (D : BoundaryTargetImageToAssemblyInput I omega M BoundaryPiece)
    (active_eq : D.activeCharts = selectedPartition.active)
    (source_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.sourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundarySource_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundaryTarget_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.boundaryTargetChart x q ∈ orientedBoundaryAtlas.charts) :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece where
  assembly := D
  active_eq := active_eq
  source_mem := source_mem
  boundarySource_mem := boundarySource_mem
  boundaryTarget_mem := boundaryTarget_mem

@[simp]
theorem toM8TargetImageInput_assembly
    (D : BoundaryTargetImageToAssemblyInput I omega M BoundaryPiece)
    (active_eq : D.activeCharts = selectedPartition.active)
    (source_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.sourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundarySource_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundaryTarget_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.boundaryTargetChart x q ∈ orientedBoundaryAtlas.charts) :
    (D.toM8TargetImageInput active_eq source_mem boundarySource_mem
      boundaryTarget_mem).assembly = D :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages
    (D : BoundaryTargetImageToAssemblyInput I omega M BoundaryPiece)
    (active_eq : D.activeCharts = selectedPartition.active)
    (source_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.sourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundarySource_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundaryTarget_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.boundaryTargetChart x q ∈ orientedBoundaryAtlas.charts) :
    (D.toM8TargetImageInput active_eq source_mem boundarySource_mem
      boundaryTarget_mem).targetImages =
        D.targetImageData.toBoundaryPieceFamilyInput :=
  rfl

/-- The constructed target-image family is indexed by the selected active set. -/
theorem toM8TargetImageInput_targetImages_active
    (D : BoundaryTargetImageToAssemblyInput I omega M BoundaryPiece)
    (active_eq : D.activeCharts = selectedPartition.active)
    (source_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.sourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundarySource_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundaryTarget_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.boundaryTargetChart x q ∈ orientedBoundaryAtlas.charts) :
    (D.toM8TargetImageInput active_eq source_mem boundarySource_mem
      boundaryTarget_mem).targetImages.activeCharts =
        selectedPartition.active := by
  simpa using
    (D.toM8TargetImageInput active_eq source_mem boundarySource_mem
      boundaryTarget_mem).targetImages_active

/--
Pointwise boundary chart-change equality exposed by the direct constructor.
This is the M8-facing form of the selected boundary COV theorem.
-/
theorem toM8TargetImageInput_boundaryBoundaryTerm_eq_partitionTerm
    [IsManifold I 1 M]
    (D : BoundaryTargetImageToAssemblyInput I omega M BoundaryPiece)
    (active_eq : D.activeCharts = selectedPartition.active)
    (source_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.sourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundarySource_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundaryTarget_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.boundaryTargetChart x q ∈ orientedBoundaryAtlas.charts)
    {x : M}
    (hx :
      x ∈
        (D.toM8TargetImageInput active_eq source_mem boundarySource_mem
          boundaryTarget_mem).targetImages.activeCharts)
    {q : BoundaryPiece}
    (hq :
      q ∈
        (D.toM8TargetImageInput active_eq source_mem boundarySource_mem
          boundaryTarget_mem).targetImages.boundaryPieces x) :
    BoundaryPieceFamilyInput.boundaryBoundaryTerm
        (D.toM8TargetImageInput active_eq source_mem boundarySource_mem
          boundaryTarget_mem).targetImages x q =
      D.boundaryPartitionTerm x q := by
  simpa [toM8TargetImageInput] using
    (D.toM8TargetImageInput active_eq source_mem boundarySource_mem
      boundaryTarget_mem).targetBoundaryTerm_eq_assemblyPartition x hx q hq

/--
Selected-active version of the pointwise boundary term equality.  This is the
shape consumed by `M8GlobalStokesInput` once the measure-localization boundary
partition term is identified with `D.boundaryPartitionTerm`.
-/
theorem toM8TargetImageInput_boundaryBoundaryTerm_eq_partitionTerm_of_selected
    [IsManifold I 1 M]
    (D : BoundaryTargetImageToAssemblyInput I omega M BoundaryPiece)
    (active_eq : D.activeCharts = selectedPartition.active)
    (source_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.sourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundarySource_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundaryTarget_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.boundaryTargetChart x q ∈ orientedBoundaryAtlas.charts)
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece}
    (hq :
      q ∈
        (D.toM8TargetImageInput active_eq source_mem boundarySource_mem
          boundaryTarget_mem).targetImages.boundaryPieces x) :
    BoundaryPieceFamilyInput.boundaryBoundaryTerm
        (D.toM8TargetImageInput active_eq source_mem boundarySource_mem
          boundaryTarget_mem).targetImages x q =
      D.boundaryPartitionTerm x q := by
  have hxTarget :
      x ∈
        (D.toM8TargetImageInput active_eq source_mem boundarySource_mem
          boundaryTarget_mem).targetImages.activeCharts := by
    have hactive :=
      D.toM8TargetImageInput_targetImages_active active_eq source_mem
        boundarySource_mem boundaryTarget_mem
    rw [hactive]
    exact hx
  exact
    D.toM8TargetImageInput_boundaryBoundaryTerm_eq_partitionTerm active_eq
      source_mem boundarySource_mem boundaryTarget_mem hxTarget hq

/-- The same boundary equality, with the partition term expanded to its
selected project-local boundary integral. -/
theorem toM8TargetImageInput_boundaryBoundaryTerm_eq_projectLocal_of_selected
    [IsManifold I 1 M]
    (D : BoundaryTargetImageToAssemblyInput I omega M BoundaryPiece)
    (active_eq : D.activeCharts = selectedPartition.active)
    (source_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.sourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundarySource_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts)
    (boundaryTarget_mem :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.boundaryPieces x ->
          D.boundaryTargetChart x q ∈ orientedBoundaryAtlas.charts)
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece}
    (hq :
      q ∈
        (D.toM8TargetImageInput active_eq source_mem boundarySource_mem
          boundaryTarget_mem).targetImages.boundaryPieces x) :
    BoundaryPieceFamilyInput.boundaryBoundaryTerm
        (D.toM8TargetImageInput active_eq source_mem boundarySource_mem
          boundaryTarget_mem).targetImages x q =
      projectLocalBoundaryIntegral I
        (D.boundaryTargetChart x q) (D.partitionTargetChart x q) omega
        (D.partitionLowerCorner x q) (D.partitionUpperCorner x q) := by
  have hterm :
      BoundaryPieceFamilyInput.boundaryBoundaryTerm
          (D.toM8TargetImageInput active_eq source_mem boundarySource_mem
            boundaryTarget_mem).targetImages x q =
        D.boundaryPartitionTerm x q :=
    D.toM8TargetImageInput_boundaryBoundaryTerm_eq_partitionTerm_of_selected
      active_eq source_mem boundarySource_mem boundaryTarget_mem hx hq
  have hxD : x ∈ D.activeCharts := by
    simpa [active_eq] using hx
  have hqD : q ∈ D.boundaryPieces x := by
    simpa [toM8TargetImageInput] using hq
  exact hterm.trans (D.boundaryPartitionTerm_eq x hxD q hqD)

end BoundaryTargetImageToAssemblyInput

namespace M8TargetImageResolvedInput

/--
Resolved target-image data exposed through the direct assembly constructor.
This is definitionally the same assembly route, but stated in the constructor's
natural theorem-facing shape.
-/
def toM8TargetImageInputFromAssembly
    (D :
      M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece :=
  D.toAssemblyInput.toM8TargetImageInput
    (by simpa [M8TargetImageResolvedInput.toAssemblyInput] using D.active_eq)
    (by
      intro x hx q hq
      exact D.source_mem x (by simpa [M8TargetImageResolvedInput.toAssemblyInput] using hx)
        q (by simpa [M8TargetImageResolvedInput.toAssemblyInput] using hq))
    (by
      intro x hx q hq
      exact D.boundarySource_mem x
        (by simpa [M8TargetImageResolvedInput.toAssemblyInput] using hx)
        q (by simpa [M8TargetImageResolvedInput.toAssemblyInput] using hq))
    (by
      intro x hx q hq
      exact D.boundaryTarget_mem x
        (by simpa [M8TargetImageResolvedInput.toAssemblyInput] using hx)
        q (by simpa [M8TargetImageResolvedInput.toAssemblyInput] using hq))

@[simp]
theorem toM8TargetImageInputFromAssembly_targetImages_active
    (D :
      M8TargetImageResolvedInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    D.toM8TargetImageInputFromAssembly.targetImages.activeCharts =
      selectedPartition.active :=
  D.toAssemblyInput.toM8TargetImageInput_targetImages_active
    (by simpa [M8TargetImageResolvedInput.toAssemblyInput] using D.active_eq)
    (by
      intro x hx q hq
      exact D.source_mem x (by simpa [M8TargetImageResolvedInput.toAssemblyInput] using hx)
        q (by simpa [M8TargetImageResolvedInput.toAssemblyInput] using hq))
    (by
      intro x hx q hq
      exact D.boundarySource_mem x
        (by simpa [M8TargetImageResolvedInput.toAssemblyInput] using hx)
        q (by simpa [M8TargetImageResolvedInput.toAssemblyInput] using hq))
    (by
      intro x hx q hq
      exact D.boundaryTarget_mem x
        (by simpa [M8TargetImageResolvedInput.toAssemblyInput] using hx)
        q (by simpa [M8TargetImageResolvedInput.toAssemblyInput] using hq))

end M8TargetImageResolvedInput

namespace M8TargetImageLocalOpennessInput

/-- Local-openness target-image data routed through the direct assembly constructor. -/
def toM8TargetImageInputFromAssembly
    (D :
      M8TargetImageLocalOpennessInput I omega selectedPartition
        orientedBoundaryAtlas BoundaryPiece) :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece :=
  D.toResolvedInput.toM8TargetImageInputFromAssembly

@[simp]
theorem toM8TargetImageInputFromAssembly_targetImages_active
    (D :
      M8TargetImageLocalOpennessInput I omega selectedPartition
        orientedBoundaryAtlas BoundaryPiece) :
    D.toM8TargetImageInputFromAssembly.targetImages.activeCharts =
      selectedPartition.active :=
  D.toResolvedInput.toM8TargetImageInputFromAssembly_targetImages_active

end M8TargetImageLocalOpennessInput

namespace M8TargetImageIFTInput

/-- IFT target-image data routed through the direct assembly constructor. -/
def toM8TargetImageInputFromAssembly
    (D :
      M8TargetImageIFTInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece :=
  D.toResolvedInput.toM8TargetImageInputFromAssembly

@[simp]
theorem toM8TargetImageInputFromAssembly_targetImages_active
    (D :
      M8TargetImageIFTInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece) :
    D.toM8TargetImageInputFromAssembly.targetImages.activeCharts =
      selectedPartition.active :=
  D.toResolvedInput.toM8TargetImageInputFromAssembly_targetImages_active

end M8TargetImageIFTInput

end BoundaryTargetImageNaturalConstructor

end Stokes

end
