import Stokes.Global.BoundaryCanonicalRouteFromContinuity
import Stokes.BoundaryChart.TargetBoxToM8Glue

/-!
# Boundary source alignment constructors

This file is a small automation layer for
`BoundarySourceProjectLocalAlignment`.

The remaining content is still genuine coordinate bookkeeping: callers must
identify the project-local source data with the selected target-image source
data.  The constructors below package those pointwise identifications in the
same shape as the target-image and source-shrink/M8 APIs, so downstream
boundary routes consume one natural field bundle instead of six unrelated
equalities.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundarySourceAlignmentAuto

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
variable
    {T :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}
variable {P : ProjectLocalGlobalStokesData I omega M BoundaryPiece}

/--
Pointwise source-alignment fields against the target-image package.

Compared with `BoundarySourceProjectLocalAlignment`, the active-set field is
stated against `T.targetImages.activeCharts`; the selected-partition equality
is then inherited from `T`.
-/
structure BoundarySourceTargetImageAlignmentFields
    (T :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (P : ProjectLocalGlobalStokesData I omega M BoundaryPiece) where
  /-- Project-local active labels are the target-image active labels. -/
  activeCharts_eq_targetImages :
    P.activeCharts = T.targetImages.activeCharts
  /-- Project-local pieces are the target-image boundary pieces. -/
  localPieces_eq_targetImages :
    forall x, P.localPieces x = T.targetImages.boundaryPieces x
  /-- Project-local source charts are the target-image source charts. -/
  sourceChart_eq_targetImages :
    forall x q, P.sourceChart x q = T.targetImages.sourceChart x q
  /-- Project-local target charts are the target-image boundary-source charts. -/
  targetChart_eq_targetImages :
    forall x q, P.targetChart x q = T.targetImages.boundarySourceChart x q
  /-- Project-local source lower corners are the target-image source lower corners. -/
  lowerCorner_eq_targetImages :
    forall x q, P.lowerCorner x q = T.targetImages.sourceLowerCorner x q
  /-- Project-local source upper corners are the target-image source upper corners. -/
  upperCorner_eq_targetImages :
    forall x q, P.upperCorner x q = T.targetImages.sourceUpperCorner x q

namespace BoundarySourceTargetImageAlignmentFields

variable (A : BoundarySourceTargetImageAlignmentFields T P)

/-- Convert target-image-facing source fields to the older alignment record. -/
def toBoundarySourceProjectLocalAlignment :
    BoundarySourceProjectLocalAlignment T P where
  activeCharts_eq :=
    A.activeCharts_eq_targetImages.trans T.targetImages_active
  localPieces_eq := A.localPieces_eq_targetImages
  sourceChart_eq := A.sourceChart_eq_targetImages
  targetChart_eq := A.targetChart_eq_targetImages
  lowerCorner_eq := A.lowerCorner_eq_targetImages
  upperCorner_eq := A.upperCorner_eq_targetImages

@[simp]
theorem toBoundarySourceProjectLocalAlignment_localPieces_eq
    (x : M) :
    (toBoundarySourceProjectLocalAlignment A).localPieces_eq x =
      A.localPieces_eq_targetImages x := by
  rfl

@[simp]
theorem toBoundarySourceProjectLocalAlignment_sourceChart_eq
    (x : M) (q : BoundaryPiece) :
    (toBoundarySourceProjectLocalAlignment A).sourceChart_eq x q =
      A.sourceChart_eq_targetImages x q := by
  rfl

@[simp]
theorem toBoundarySourceProjectLocalAlignment_targetChart_eq
    (x : M) (q : BoundaryPiece) :
    (toBoundarySourceProjectLocalAlignment A).targetChart_eq x q =
      A.targetChart_eq_targetImages x q := by
  rfl

@[simp]
theorem toBoundarySourceProjectLocalAlignment_lowerCorner_eq
    (x : M) (q : BoundaryPiece) :
    (toBoundarySourceProjectLocalAlignment A).lowerCorner_eq x q =
      A.lowerCorner_eq_targetImages x q := by
  rfl

@[simp]
theorem toBoundarySourceProjectLocalAlignment_upperCorner_eq
    (x : M) (q : BoundaryPiece) :
    (toBoundarySourceProjectLocalAlignment A).upperCorner_eq x q =
      A.upperCorner_eq_targetImages x q := by
  rfl

/-- Active-set projection in the selected-partition shape. -/
theorem activeCharts_eq_selected
    (A : BoundarySourceTargetImageAlignmentFields T P) :
    P.activeCharts = selectedPartition.active :=
  (toBoundarySourceProjectLocalAlignment A).activeCharts_eq

/-- Boundary-piece projection in the selected target-image shape. -/
theorem localPieces_eq
    (A : BoundarySourceTargetImageAlignmentFields T P)
    (x : M) :
    P.localPieces x = T.targetImages.boundaryPieces x :=
  (toBoundarySourceProjectLocalAlignment A).localPieces_eq x

/-- Source-chart projection in the selected target-image shape. -/
theorem sourceChart_eq
    (A : BoundarySourceTargetImageAlignmentFields T P)
    (x : M) (q : BoundaryPiece) :
    P.sourceChart x q = T.targetImages.sourceChart x q :=
  (toBoundarySourceProjectLocalAlignment A).sourceChart_eq x q

/-- Boundary-source-chart projection in the selected target-image shape. -/
theorem targetChart_eq
    (A : BoundarySourceTargetImageAlignmentFields T P)
    (x : M) (q : BoundaryPiece) :
    P.targetChart x q = T.targetImages.boundarySourceChart x q :=
  (toBoundarySourceProjectLocalAlignment A).targetChart_eq x q

/-- Source lower-corner projection in the selected target-image shape. -/
theorem lowerCorner_eq
    (A : BoundarySourceTargetImageAlignmentFields T P)
    (x : M) (q : BoundaryPiece) :
    P.lowerCorner x q = T.targetImages.sourceLowerCorner x q :=
  (toBoundarySourceProjectLocalAlignment A).lowerCorner_eq x q

/-- Source upper-corner projection in the selected target-image shape. -/
theorem upperCorner_eq
    (A : BoundarySourceTargetImageAlignmentFields T P)
    (x : M) (q : BoundaryPiece) :
    P.upperCorner x q = T.targetImages.sourceUpperCorner x q :=
  (toBoundarySourceProjectLocalAlignment A).upperCorner_eq x q

end BoundarySourceTargetImageAlignmentFields

namespace BoundarySourceProjectLocalAlignment

/--
Constructor from pointwise equalities against `T.targetImages`.

This is the direct theorem-facing entry point when no separate named field
bundle is needed.
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
    BoundarySourceProjectLocalAlignment T P :=
  BoundarySourceTargetImageAlignmentFields.toBoundarySourceProjectLocalAlignment
    (BoundarySourceTargetImageAlignmentFields.mk
      activeCharts_eq_targetImages localPieces_eq_targetImages
      sourceChart_eq_targetImages targetChart_eq_targetImages
      lowerCorner_eq_targetImages upperCorner_eq_targetImages)

@[simp]
theorem ofTargetImageFields_localPieces_eq
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
    (ofTargetImageFields
      (T := T) (P := P)
      activeCharts_eq_targetImages localPieces_eq_targetImages
      sourceChart_eq_targetImages targetChart_eq_targetImages
      lowerCorner_eq_targetImages upperCorner_eq_targetImages).localPieces_eq x =
      localPieces_eq_targetImages x := by
  rfl

end BoundarySourceProjectLocalAlignment

namespace BoundaryCanonicalRouteMeasureInput

/--
Canonical-route input from source alignment fields stated against the selected
target-image package.
-/
def ofTargetImageAlignmentFields
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (projectLocal : ProjectLocalBoundaryMeasureConstructorInput P)
    (sourceAlignment : BoundarySourceTargetImageAlignmentFields T P) :
    BoundaryCanonicalRouteMeasureInput T P where
  faceContinuity := faceContinuity
  projectLocal := projectLocal
  sourceAlignment :=
    BoundarySourceTargetImageAlignmentFields.toBoundarySourceProjectLocalAlignment
      sourceAlignment

@[simp]
theorem ofTargetImageAlignmentFields_sourceAlignment
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (projectLocal : ProjectLocalBoundaryMeasureConstructorInput P)
    (sourceAlignment : BoundarySourceTargetImageAlignmentFields T P) :
    (ofTargetImageAlignmentFields
      (T := T) (P := P)
      faceContinuity projectLocal sourceAlignment).sourceAlignment =
      BoundarySourceTargetImageAlignmentFields.toBoundarySourceProjectLocalAlignment
        sourceAlignment := by
  rfl

@[simp]
theorem ofTargetImageAlignmentFields_projectLocal
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (projectLocal : ProjectLocalBoundaryMeasureConstructorInput P)
    (sourceAlignment : BoundarySourceTargetImageAlignmentFields T P) :
    (ofTargetImageAlignmentFields
      (T := T) (P := P)
      faceContinuity projectLocal sourceAlignment).projectLocal =
      projectLocal := by
  rfl

end BoundaryCanonicalRouteMeasureInput

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.M8ResolvedFields

variable
    {F :
      BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega M
        BoundaryPiece}

/--
Alignment fields for a source-shrink/M8-resolved package.

This abbreviation keeps the source-shrink-facing call sites short: after
`M8ResolvedFields` has produced its `M8TargetImageInput`, the source alignment
is just the pointwise identification of the project-local data with that
target-image input.
-/
abbrev BoundarySourceAlignmentFields
    (D :
      M8ResolvedFields F selectedPartition orientedBoundaryAtlas)
    (P : ProjectLocalGlobalStokesData I omega M BoundaryPiece) :=
  BoundarySourceTargetImageAlignmentFields D.toM8TargetImageInput P

/-- Build source/project-local alignment from source-shrink/M8 alignment fields. -/
def toBoundarySourceProjectLocalAlignment
    (D :
      M8ResolvedFields F selectedPartition orientedBoundaryAtlas)
    (A : BoundarySourceAlignmentFields D P) :
    BoundarySourceProjectLocalAlignment D.toM8TargetImageInput P :=
  BoundarySourceTargetImageAlignmentFields.toBoundarySourceProjectLocalAlignment A

@[simp]
theorem toBoundarySourceProjectLocalAlignment_localPieces_eq
    (D :
      M8ResolvedFields F selectedPartition orientedBoundaryAtlas)
    (A : BoundarySourceAlignmentFields D P)
    (x : M) :
    (toBoundarySourceProjectLocalAlignment D A).localPieces_eq x =
      A.localPieces_eq_targetImages x := by
  rfl

end BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.M8ResolvedFields

end BoundarySourceAlignmentAuto

end Stokes

end
