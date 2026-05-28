import Stokes.Global.BoundarySourceAlignmentAuto
import Stokes.Global.ProjectLocalConstructor

/-!
# Boundary source alignment constructors

This file adds constructor-facing lemmas for source alignment.  The existing
`BoundarySourceAlignmentAuto` module defines the final field bundle; here we
expose constructors whose hypotheses are stated against the natural upstream
data:

* a generic `M8TargetImageInput`;
* source-shrink `M8ResolvedFields`, where the target-image fields unfold to the
  source-shrink family `F`;
* project-local constructor data whose final `ProjectLocalGlobalStokesData`
  is definitionally built from named constructor fields.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundarySourceAlignmentConstructors

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

namespace BoundarySourceTargetImageAlignmentFields

variable
    {T :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}
    {P : ProjectLocalGlobalStokesData I omega M BoundaryPiece}

/--
Constructor for source alignment fields stated directly against the
target-image package.

This is the field-bundle counterpart of
`BoundarySourceProjectLocalAlignment.ofTargetImageFields`.
-/
def ofTargetImageFields
    (activeCharts_eq_targetImages :
      P.activeCharts = T.targetImages.activeCharts)
    (localPieces_eq_targetImages :
      forall x, P.localPieces x = T.targetImages.boundaryPieces x)
    (sourceChart_eq_targetImages :
      forall x q, P.sourceChart x q = T.targetImages.sourceChart x q)
    (targetChart_eq_targetImages :
      forall x q, P.targetChart x q = T.targetImages.boundarySourceChart x q)
    (lowerCorner_eq_targetImages :
      forall x q, P.lowerCorner x q = T.targetImages.sourceLowerCorner x q)
    (upperCorner_eq_targetImages :
      forall x q, P.upperCorner x q = T.targetImages.sourceUpperCorner x q) :
    BoundarySourceTargetImageAlignmentFields T P where
  activeCharts_eq_targetImages := activeCharts_eq_targetImages
  localPieces_eq_targetImages := localPieces_eq_targetImages
  sourceChart_eq_targetImages := sourceChart_eq_targetImages
  targetChart_eq_targetImages := targetChart_eq_targetImages
  lowerCorner_eq_targetImages := lowerCorner_eq_targetImages
  upperCorner_eq_targetImages := upperCorner_eq_targetImages

@[simp]
theorem ofTargetImageFields_activeCharts_eq_targetImages
    (activeCharts_eq_targetImages :
      P.activeCharts = T.targetImages.activeCharts)
    (localPieces_eq_targetImages :
      forall x, P.localPieces x = T.targetImages.boundaryPieces x)
    (sourceChart_eq_targetImages :
      forall x q, P.sourceChart x q = T.targetImages.sourceChart x q)
    (targetChart_eq_targetImages :
      forall x q, P.targetChart x q = T.targetImages.boundarySourceChart x q)
    (lowerCorner_eq_targetImages :
      forall x q, P.lowerCorner x q = T.targetImages.sourceLowerCorner x q)
    (upperCorner_eq_targetImages :
      forall x q, P.upperCorner x q = T.targetImages.sourceUpperCorner x q) :
    (ofTargetImageFields (T := T) (P := P)
      activeCharts_eq_targetImages localPieces_eq_targetImages
      sourceChart_eq_targetImages targetChart_eq_targetImages
      lowerCorner_eq_targetImages
      upperCorner_eq_targetImages).activeCharts_eq_targetImages =
      activeCharts_eq_targetImages := by
  rfl

@[simp]
theorem ofTargetImageFields_localPieces_eq_targetImages
    (activeCharts_eq_targetImages :
      P.activeCharts = T.targetImages.activeCharts)
    (localPieces_eq_targetImages :
      forall x, P.localPieces x = T.targetImages.boundaryPieces x)
    (sourceChart_eq_targetImages :
      forall x q, P.sourceChart x q = T.targetImages.sourceChart x q)
    (targetChart_eq_targetImages :
      forall x q, P.targetChart x q = T.targetImages.boundarySourceChart x q)
    (lowerCorner_eq_targetImages :
      forall x q, P.lowerCorner x q = T.targetImages.sourceLowerCorner x q)
    (upperCorner_eq_targetImages :
      forall x q, P.upperCorner x q = T.targetImages.sourceUpperCorner x q)
    (x : M) :
    (ofTargetImageFields (T := T) (P := P)
      activeCharts_eq_targetImages localPieces_eq_targetImages
      sourceChart_eq_targetImages targetChart_eq_targetImages
      lowerCorner_eq_targetImages
      upperCorner_eq_targetImages).localPieces_eq_targetImages x =
      localPieces_eq_targetImages x := by
  rfl

end BoundarySourceTargetImageAlignmentFields

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.M8ResolvedFields

variable
    {F :
      BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega M
        BoundaryPiece}

variable
    (D :
      M8ResolvedFields F selectedPartition orientedBoundaryAtlas)

@[simp]
theorem toM8TargetImageInput_targetImages_activeCharts :
    D.toM8TargetImageInput.targetImages.activeCharts = F.activeCharts := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundaryPieces :
    D.toM8TargetImageInput.targetImages.boundaryPieces = F.localPieces := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceChart :
    D.toM8TargetImageInput.targetImages.sourceChart = F.sourceChart := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundarySourceChart :
    D.toM8TargetImageInput.targetImages.boundarySourceChart =
      F.boundarySourceChart := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceLowerCorner :
    D.toM8TargetImageInput.targetImages.sourceLowerCorner =
      F.sourceLowerCorner := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceUpperCorner :
    D.toM8TargetImageInput.targetImages.sourceUpperCorner =
      F.sourceUpperCorner := by
  rfl

/--
Source alignment for a source-shrink/M8-resolved package from project-local
fields aligned with the source-shrink family `F`.
-/
def toBoundarySourceTargetImageAlignmentFieldsOfProjectLocal
    (P : ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (activeCharts_eq : P.activeCharts = F.activeCharts)
    (localPieces_eq : forall x, P.localPieces x = F.localPieces x)
    (sourceChart_eq : forall x q, P.sourceChart x q = F.sourceChart x q)
    (targetChart_eq :
      forall x q, P.targetChart x q = F.boundarySourceChart x q)
    (lowerCorner_eq : forall x q, P.lowerCorner x q = F.sourceLowerCorner x q)
    (upperCorner_eq : forall x q, P.upperCorner x q = F.sourceUpperCorner x q) :
    BoundarySourceTargetImageAlignmentFields D.toM8TargetImageInput P where
  activeCharts_eq_targetImages := by
    simpa using activeCharts_eq
  localPieces_eq_targetImages := by
    intro x
    simpa using localPieces_eq x
  sourceChart_eq_targetImages := by
    intro x q
    simpa using sourceChart_eq x q
  targetChart_eq_targetImages := by
    intro x q
    simpa using targetChart_eq x q
  lowerCorner_eq_targetImages := by
    intro x q
    simpa using lowerCorner_eq x q
  upperCorner_eq_targetImages := by
    intro x q
    simpa using upperCorner_eq x q

/--
Source/project-local alignment for a source-shrink/M8-resolved package from
project-local fields aligned with the source-shrink family `F`.
-/
def toBoundarySourceProjectLocalAlignmentOfProjectLocal
    (P : ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (activeCharts_eq : P.activeCharts = F.activeCharts)
    (localPieces_eq : forall x, P.localPieces x = F.localPieces x)
    (sourceChart_eq : forall x q, P.sourceChart x q = F.sourceChart x q)
    (targetChart_eq :
      forall x q, P.targetChart x q = F.boundarySourceChart x q)
    (lowerCorner_eq : forall x q, P.lowerCorner x q = F.sourceLowerCorner x q)
    (upperCorner_eq : forall x q, P.upperCorner x q = F.sourceUpperCorner x q) :
    BoundarySourceProjectLocalAlignment D.toM8TargetImageInput P :=
  (D.toBoundarySourceTargetImageAlignmentFieldsOfProjectLocal P
    activeCharts_eq localPieces_eq sourceChart_eq targetChart_eq
    lowerCorner_eq upperCorner_eq).toBoundarySourceProjectLocalAlignment

@[simp]
theorem toBoundarySourceTargetImageAlignmentFieldsOfProjectLocal_localPieces
    (P : ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (activeCharts_eq : P.activeCharts = F.activeCharts)
    (localPieces_eq : forall x, P.localPieces x = F.localPieces x)
    (sourceChart_eq : forall x q, P.sourceChart x q = F.sourceChart x q)
    (targetChart_eq :
      forall x q, P.targetChart x q = F.boundarySourceChart x q)
    (lowerCorner_eq : forall x q, P.lowerCorner x q = F.sourceLowerCorner x q)
    (upperCorner_eq : forall x q, P.upperCorner x q = F.sourceUpperCorner x q)
    (x : M) :
    (D.toBoundarySourceTargetImageAlignmentFieldsOfProjectLocal P
      activeCharts_eq localPieces_eq sourceChart_eq targetChart_eq
      lowerCorner_eq upperCorner_eq).localPieces_eq_targetImages x =
      localPieces_eq x := by
  rfl

end BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.M8ResolvedFields

namespace ProjectLocalConstructorData

/--
For a project-local constructor whose chart labels are manifold points, build
source alignment fields from equalities against a target-image input.  The
conclusion targets the final `ProjectLocalGlobalStokesData` generated by the
constructor package.
-/
def toBoundarySourceTargetImageAlignmentFields
    (C : ProjectLocalConstructorData I omega M BoundaryPiece)
    (T :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (activeCharts_eq_targetImages :
      C.activeCharts = T.targetImages.activeCharts)
    (localPieces_eq_targetImages :
      forall x, C.localPieces x = T.targetImages.boundaryPieces x)
    (sourceChart_eq_targetImages :
      forall x q, C.sourceChart x q = T.targetImages.sourceChart x q)
    (targetChart_eq_targetImages :
      forall x q, C.targetChart x q = T.targetImages.boundarySourceChart x q)
    (lowerCorner_eq_targetImages :
      forall x q, C.lowerCorner x q = T.targetImages.sourceLowerCorner x q)
    (upperCorner_eq_targetImages :
      forall x q, C.upperCorner x q = T.targetImages.sourceUpperCorner x q) :
    BoundarySourceTargetImageAlignmentFields T C.toProjectLocalGlobalStokesData :=
  BoundarySourceTargetImageAlignmentFields.ofTargetImageFields
    (T := T) (P := C.toProjectLocalGlobalStokesData)
    activeCharts_eq_targetImages localPieces_eq_targetImages
    sourceChart_eq_targetImages targetChart_eq_targetImages
    lowerCorner_eq_targetImages upperCorner_eq_targetImages

/--
Project-local constructor data aligned with a source-shrink/M8-resolved family.
The hypotheses are stated against the named source-shrink family fields `F`,
which are definitionally the target-image fields of `D.toM8TargetImageInput`.
-/
def toBoundarySourceTargetImageAlignmentFieldsOfM8Resolved
    {F :
      BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega M
        BoundaryPiece}
    (C : ProjectLocalConstructorData I omega M BoundaryPiece)
    (D :
      BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.M8ResolvedFields
        F selectedPartition orientedBoundaryAtlas)
    (activeCharts_eq : C.activeCharts = F.activeCharts)
    (localPieces_eq : forall x, C.localPieces x = F.localPieces x)
    (sourceChart_eq : forall x q, C.sourceChart x q = F.sourceChart x q)
    (targetChart_eq :
      forall x q, C.targetChart x q = F.boundarySourceChart x q)
    (lowerCorner_eq : forall x q, C.lowerCorner x q = F.sourceLowerCorner x q)
    (upperCorner_eq : forall x q, C.upperCorner x q = F.sourceUpperCorner x q) :
    BoundarySourceTargetImageAlignmentFields D.toM8TargetImageInput
      C.toProjectLocalGlobalStokesData :=
  D.toBoundarySourceTargetImageAlignmentFieldsOfProjectLocal
    C.toProjectLocalGlobalStokesData activeCharts_eq localPieces_eq
    sourceChart_eq targetChart_eq lowerCorner_eq upperCorner_eq

/--
Project-local source alignment, directly from project-local constructor data
and a source-shrink/M8-resolved family.
-/
def toBoundarySourceProjectLocalAlignmentOfM8Resolved
    {F :
      BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega M
        BoundaryPiece}
    (C : ProjectLocalConstructorData I omega M BoundaryPiece)
    (D :
      BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.M8ResolvedFields
        F selectedPartition orientedBoundaryAtlas)
    (activeCharts_eq : C.activeCharts = F.activeCharts)
    (localPieces_eq : forall x, C.localPieces x = F.localPieces x)
    (sourceChart_eq : forall x q, C.sourceChart x q = F.sourceChart x q)
    (targetChart_eq :
      forall x q, C.targetChart x q = F.boundarySourceChart x q)
    (lowerCorner_eq : forall x q, C.lowerCorner x q = F.sourceLowerCorner x q)
    (upperCorner_eq : forall x q, C.upperCorner x q = F.sourceUpperCorner x q) :
    BoundarySourceProjectLocalAlignment D.toM8TargetImageInput
      C.toProjectLocalGlobalStokesData :=
  (C.toBoundarySourceTargetImageAlignmentFieldsOfM8Resolved D
    activeCharts_eq localPieces_eq sourceChart_eq targetChart_eq
    lowerCorner_eq upperCorner_eq).toBoundarySourceProjectLocalAlignment

end ProjectLocalConstructorData

end BoundarySourceAlignmentConstructors

end Stokes

end
