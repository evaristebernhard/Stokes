import Stokes.Global.NaturalCompactSupportCombinedEndpoint

/-!
# Boundary atlas membership automation

This module records the small atlas-membership layer used by the resolved
target-image boundary route.  The raw boundary-chart COV constructors need the
source chart and the boundary-source chart to lie in the oriented boundary
atlas.  At the global endpoint those facts are already carried by the
target-image/M8 input and the source/project-local alignment data; callers
should not have to pass them again as two unrelated hypotheses.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryAtlasMembershipAuto

universe u w c p b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {Piece : Type p} {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}

namespace BoundaryChartTargetImageResolvedFamily

variable
    (F : BoundaryChartTargetImageResolvedFamily I omega Chart Piece)
    (D : ProjectLocalGlobalStokesData I omega Chart Piece)

/--
Compatibility aligning a resolved target-image/local-inverse COV family with a
project-local boundary package.

The analytic COV data is intentionally not a field here: it is reconstructed
from `F` plus the oriented-atlas or oriented-manifold source downstream.  The
only global assertion kept as a field is the real partition-term
identification.
-/
structure ProjectLocalCompatibility where
  /-- The active chart labels agree. -/
  activeCharts_eq : D.activeCharts = F.activeCharts
  /-- The local boundary-piece labels agree pointwise. -/
  localPieces_eq : ∀ x, D.localPieces x = F.localPieces x
  /-- Project-local source charts are the resolved-family source charts. -/
  sourceChart_eq : ∀ x q, D.sourceChart x q = F.sourceChart x q
  /-- Project-local target charts are the resolved-family boundary source charts. -/
  targetChart_eq : ∀ x q, D.targetChart x q = F.boundarySourceChart x q
  /-- Project-local lower corners are the resolved-family source lower corners. -/
  lowerCorner_eq : ∀ x q, D.lowerCorner x q = F.sourceLowerCorner x q
  /-- Project-local upper corners are the resolved-family source upper corners. -/
  upperCorner_eq : ∀ x q, D.upperCorner x q = F.sourceUpperCorner x q
  /-- The selected boundary partition term is the transported target chart term. -/
  boundaryPartitionTerm_eq :
    ∀ x, x ∈ F.activeCharts →
      ∀ q, q ∈ F.localPieces x →
        D.boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I (F.boundarySourceChart x q)
            (F.boundaryTargetChart x q) omega
            (F.targetLowerCorner x q) (F.targetUpperCorner x q)

namespace ProjectLocalCompatibility

variable {F : BoundaryChartTargetImageResolvedFamily I omega Chart Piece}
variable {D : ProjectLocalGlobalStokesData I omega Chart Piece}

/-- Convert active membership from the project-local package to the resolved family. -/
theorem mem_active
    (C : ProjectLocalCompatibility F D) {x : Chart}
    (hx : x ∈ D.activeCharts) :
    x ∈ F.activeCharts := by
  simpa [C.activeCharts_eq] using hx

/-- Convert local-piece membership from the project-local package to the resolved family. -/
theorem mem_localPiece
    (C : ProjectLocalCompatibility F D) {x : Chart} {q : Piece}
    (hq : q ∈ D.localPieces x) :
    q ∈ F.localPieces x := by
  simpa [C.localPieces_eq x] using hq

end ProjectLocalCompatibility

variable
    (F : BoundaryChartTargetImageResolvedFamily I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)

/-- Atlas membership facts needed by the oriented-atlas COV route. -/
structure BoundaryAtlasMembership where
  /-- Source charts lie in the oriented boundary atlas. -/
  sourceChart_mem :
    ∀ x, x ∈ F.activeCharts →
      ∀ q, q ∈ F.localPieces x → F.sourceChart x q ∈ A.charts
  /-- Boundary-source charts lie in the oriented boundary atlas. -/
  boundarySourceChart_mem :
    ∀ x, x ∈ F.activeCharts →
      ∀ q, q ∈ F.localPieces x → F.boundarySourceChart x q ∈ A.charts

namespace BoundaryAtlasMembership

variable {F : BoundaryChartTargetImageResolvedFamily I omega Chart Piece}
variable {A : BoundaryChartOrientedAtlas I M}

/-- Source-chart membership projection. -/
theorem sourceChart_mem'
    (D : BoundaryAtlasMembership F A)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    F.sourceChart x q ∈ A.charts :=
  D.sourceChart_mem x hx q hq

/-- Boundary-source-chart membership projection. -/
theorem boundarySourceChart_mem'
    (D : BoundaryAtlasMembership F A)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    F.boundarySourceChart x q ∈ A.charts :=
  D.boundarySourceChart_mem x hx q hq

end BoundaryAtlasMembership

variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
variable
    {T :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}
variable {P : ProjectLocalGlobalStokesData I omega M BoundaryPiece}
variable
    {F : BoundaryChartTargetImageResolvedFamily I omega M BoundaryPiece}

/--
Recover resolved-family atlas membership from the endpoint target-image input
and the source/project-local alignment.
-/
def boundaryAtlasMembershipOfProjectLocalAlignment
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (C : F.ProjectLocalCompatibility P) :
    F.BoundaryAtlasMembership orientedBoundaryAtlas where
  sourceChart_mem := by
    intro x hx q hq
    have hxP : x ∈ P.activeCharts := by
      simpa [C.activeCharts_eq] using hx
    have hxSelected : x ∈ selectedPartition.active := by
      simpa [sourceAlignment.activeCharts_eq] using hxP
    have hxT : x ∈ T.targetImages.activeCharts := by
      simpa [T.targetImages_active] using hxSelected
    have hqP : q ∈ P.localPieces x := by
      simpa [C.localPieces_eq x] using hq
    have hqT : q ∈ T.targetImages.boundaryPieces x := by
      simpa [sourceAlignment.localPieces_eq x] using hqP
    have hmem := T.targetImages_source_mem x hxT q hqT
    simpa [← sourceAlignment.sourceChart_eq x q, C.sourceChart_eq x q] using hmem
  boundarySourceChart_mem := by
    intro x hx q hq
    have hxP : x ∈ P.activeCharts := by
      simpa [C.activeCharts_eq] using hx
    have hxSelected : x ∈ selectedPartition.active := by
      simpa [sourceAlignment.activeCharts_eq] using hxP
    have hxT : x ∈ T.targetImages.activeCharts := by
      simpa [T.targetImages_active] using hxSelected
    have hqP : q ∈ P.localPieces x := by
      simpa [C.localPieces_eq x] using hq
    have hqT : q ∈ T.targetImages.boundaryPieces x := by
      simpa [sourceAlignment.localPieces_eq x] using hqP
    have hmem := T.targetImages_boundarySource_mem x hxT q hqT
    simpa [← sourceAlignment.targetChart_eq x q, C.targetChart_eq x q] using hmem

end BoundaryChartTargetImageResolvedFamily

namespace M8TargetImageResolvedInput

variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
variable
    (D :
      _root_.Stokes.M8TargetImageResolvedInput I omega selectedPartition
        orientedBoundaryAtlas BoundaryPiece)

/-- Atlas membership exposed by a resolved M8 target-image input. -/
def boundaryAtlasMembership :
    D.family.BoundaryAtlasMembership orientedBoundaryAtlas where
  sourceChart_mem := D.source_mem
  boundarySourceChart_mem := D.boundarySource_mem

@[simp]
theorem boundaryAtlasMembership_sourceChart_mem
    (x : M) (hx : x ∈ D.family.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ D.family.localPieces x) :
    D.boundaryAtlasMembership.sourceChart_mem x hx q hq =
      D.source_mem x hx q hq := by
  rfl

@[simp]
theorem boundaryAtlasMembership_boundarySourceChart_mem
    (x : M) (hx : x ∈ D.family.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ D.family.localPieces x) :
    D.boundaryAtlasMembership.boundarySourceChart_mem x hx q hq =
      D.boundarySource_mem x hx q hq := by
  rfl

end M8TargetImageResolvedInput

end BoundaryAtlasMembershipAuto

end Stokes

end
