import Stokes.Global.BoundarySourceAlignmentConstructors

/-!
# Unified boundary source alignment input

This module packages the source-shrink/M8 target-image data together with the
project-local constructor fields in a single source of truth.  The
project-local source data are projected directly from the same
`BoundaryChartSourceShrinkOpenPartialHomeomorphFamily` used by the M8-resolved
target-image input, so the six source-alignment equalities are definitional.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped BigOperators Manifold Topology

namespace Stokes

section BoundarySourceAlignmentUnified

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/--
Unified input for source alignment.

The family `F` is the single source for the project-local source fields and
for the M8 target-image source fields.  The remaining fields are exactly the
non-source-alignment fields required by `ProjectLocalConstructorData`, with the
boundary partition term shared from `m8Fields`.
-/
structure BoundarySourceAlignmentUnifiedData where
  /-- Source-shrink family used by the M8 target-image route. -/
  family :
    BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega M BoundaryPiece
  /-- M8-resolved global fields attached to the same source-shrink family. -/
  m8Fields :
    BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.M8ResolvedFields
      family selectedPartition orientedBoundaryAtlas
  /-- The global bulk integral represented by this unified package. -/
  globalBulkIntegral : Real
  /-- The global boundary integral represented by this unified package. -/
  globalBoundaryIntegral : Real
  /-- Reconstruction of the global bulk integral from the shared source family. -/
  globalBulkIntegral_eq_projectLocalSum :
    globalBulkIntegral =
      Finset.sum family.activeCharts fun x =>
        Finset.sum (family.localPieces x) fun q =>
          projectLocalBulkIntegral I (family.sourceChart x q)
            (family.boundarySourceChart x q) omega
            (family.sourceLowerCorner x q) (family.sourceUpperCorner x q)
  /-- Project-local Stokes on every active shared source piece. -/
  localProjectStokes :
    forall x, x ∈ family.activeCharts ->
      forall q, q ∈ family.localPieces x ->
        projectLocalBulkIntegral I (family.sourceChart x q)
            (family.boundarySourceChart x q) omega
            (family.sourceLowerCorner x q) (family.sourceUpperCorner x q) =
          projectLocalBoundaryIntegral I (family.sourceChart x q)
            (family.boundarySourceChart x q) omega
            (family.sourceLowerCorner x q) (family.sourceUpperCorner x q)
  /--
  Compatibility of project-local boundary terms with the shared M8 boundary
  partition term.
  -/
  chartChangeCancellation :
    (Finset.sum family.activeCharts fun x =>
        Finset.sum (family.localPieces x) fun q =>
          projectLocalBoundaryIntegral I (family.sourceChart x q)
            (family.boundarySourceChart x q) omega
            (family.sourceLowerCorner x q) (family.sourceUpperCorner x q)) =
      Finset.sum family.activeCharts fun x =>
        Finset.sum (family.localPieces x) fun q =>
          m8Fields.boundaryPartitionTerm x q
  /-- Reconstruction of the global boundary integral from the shared M8 term. -/
  globalBoundaryIntegral_eq_boundaryPartitionSum :
    globalBoundaryIntegral =
      Finset.sum family.activeCharts fun x =>
        Finset.sum (family.localPieces x) fun q =>
          m8Fields.boundaryPartitionTerm x q

namespace BoundarySourceAlignmentUnifiedData

variable (U :
  BoundarySourceAlignmentUnifiedData
    (I := I) (omega := omega)
    (selectedPartition := selectedPartition)
    (orientedBoundaryAtlas := orientedBoundaryAtlas)
    (BoundaryPiece := BoundaryPiece))

/-- Project-local constructor data obtained by projection from the unified input. -/
def toProjectLocalConstructorData :
    ProjectLocalConstructorData I omega M BoundaryPiece where
  activeCharts := U.family.activeCharts
  localPieces := U.family.localPieces
  sourceChart := U.family.sourceChart
  targetChart := U.family.boundarySourceChart
  lowerCorner := U.family.sourceLowerCorner
  upperCorner := U.family.sourceUpperCorner
  boundaryPartitionTerm := U.m8Fields.boundaryPartitionTerm
  globalBulkIntegral := U.globalBulkIntegral
  globalBoundaryIntegral := U.globalBoundaryIntegral
  globalBulkIntegral_eq_projectLocalSum :=
    U.globalBulkIntegral_eq_projectLocalSum
  localProjectStokes := U.localProjectStokes
  chartChangeCancellation := U.chartChangeCancellation
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    U.globalBoundaryIntegral_eq_boundaryPartitionSum

/-- Final project-local data obtained from the unified constructor package. -/
def toProjectLocalGlobalStokesData :
    ProjectLocalGlobalStokesData I omega M BoundaryPiece :=
  U.toProjectLocalConstructorData.toProjectLocalGlobalStokesData

/-- M8 target-image input obtained from the shared M8-resolved fields. -/
def toM8TargetImageInput :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece :=
  U.m8Fields.toM8TargetImageInput

@[simp]
theorem toProjectLocalConstructorData_activeCharts :
    U.toProjectLocalConstructorData.activeCharts = U.family.activeCharts :=
  rfl

@[simp]
theorem toProjectLocalConstructorData_localPieces :
    U.toProjectLocalConstructorData.localPieces = U.family.localPieces :=
  rfl

@[simp]
theorem toProjectLocalConstructorData_sourceChart :
    U.toProjectLocalConstructorData.sourceChart = U.family.sourceChart :=
  rfl

@[simp]
theorem toProjectLocalConstructorData_targetChart :
    U.toProjectLocalConstructorData.targetChart = U.family.boundarySourceChart :=
  rfl

@[simp]
theorem toProjectLocalConstructorData_lowerCorner :
    U.toProjectLocalConstructorData.lowerCorner = U.family.sourceLowerCorner :=
  rfl

@[simp]
theorem toProjectLocalConstructorData_upperCorner :
    U.toProjectLocalConstructorData.upperCorner = U.family.sourceUpperCorner :=
  rfl

@[simp]
theorem toProjectLocalConstructorData_boundaryPartitionTerm :
    U.toProjectLocalConstructorData.boundaryPartitionTerm =
      U.m8Fields.boundaryPartitionTerm :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_activeCharts :
    U.toM8TargetImageInput.targetImages.activeCharts =
      U.family.activeCharts :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundaryPieces :
    U.toM8TargetImageInput.targetImages.boundaryPieces =
      U.family.localPieces :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceChart :
    U.toM8TargetImageInput.targetImages.sourceChart =
      U.family.sourceChart :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundarySourceChart :
    U.toM8TargetImageInput.targetImages.boundarySourceChart =
      U.family.boundarySourceChart :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceLowerCorner :
    U.toM8TargetImageInput.targetImages.sourceLowerCorner =
      U.family.sourceLowerCorner :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceUpperCorner :
    U.toM8TargetImageInput.targetImages.sourceUpperCorner =
      U.family.sourceUpperCorner :=
  rfl

/--
Source-alignment fields generated from unified data.

All six source-alignment equalities are definitional because both sides are
projected from `U.family`.
-/
def toBoundarySourceTargetImageAlignmentFields :
    BoundarySourceTargetImageAlignmentFields U.toM8TargetImageInput
      U.toProjectLocalGlobalStokesData where
  activeCharts_eq_targetImages := rfl
  localPieces_eq_targetImages := fun _ => rfl
  sourceChart_eq_targetImages := fun _ _ => rfl
  targetChart_eq_targetImages := fun _ _ => rfl
  lowerCorner_eq_targetImages := fun _ _ => rfl
  upperCorner_eq_targetImages := fun _ _ => rfl

@[simp]
theorem toBoundarySourceTargetImageAlignmentFields_activeCharts :
    U.toBoundarySourceTargetImageAlignmentFields.activeCharts_eq_targetImages =
      rfl :=
  rfl

@[simp]
theorem toBoundarySourceTargetImageAlignmentFields_localPieces
    (x : M) :
    U.toBoundarySourceTargetImageAlignmentFields.localPieces_eq_targetImages x =
      rfl :=
  rfl

@[simp]
theorem toBoundarySourceTargetImageAlignmentFields_sourceChart
    (x : M) (q : BoundaryPiece) :
    U.toBoundarySourceTargetImageAlignmentFields.sourceChart_eq_targetImages x q =
      rfl :=
  rfl

@[simp]
theorem toBoundarySourceTargetImageAlignmentFields_targetChart
    (x : M) (q : BoundaryPiece) :
    U.toBoundarySourceTargetImageAlignmentFields.targetChart_eq_targetImages x q =
      rfl :=
  rfl

@[simp]
theorem toBoundarySourceTargetImageAlignmentFields_lowerCorner
    (x : M) (q : BoundaryPiece) :
    U.toBoundarySourceTargetImageAlignmentFields.lowerCorner_eq_targetImages x q =
      rfl :=
  rfl

@[simp]
theorem toBoundarySourceTargetImageAlignmentFields_upperCorner
    (x : M) (q : BoundaryPiece) :
    U.toBoundarySourceTargetImageAlignmentFields.upperCorner_eq_targetImages x q =
      rfl :=
  rfl

/-- Source/project-local alignment generated from unified source fields. -/
def toBoundarySourceProjectLocalAlignment :
    BoundarySourceProjectLocalAlignment U.toM8TargetImageInput
      U.toProjectLocalGlobalStokesData :=
  U.toBoundarySourceTargetImageAlignmentFields.toBoundarySourceProjectLocalAlignment

/-- Canonical-route input from unified source-alignment data. -/
def toBoundaryCanonicalRouteMeasureInput
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData)
    (projectLocal :
      ProjectLocalBoundaryMeasureConstructorInput
        U.toProjectLocalGlobalStokesData) :
    BoundaryCanonicalRouteMeasureInput U.toM8TargetImageInput
      U.toProjectLocalGlobalStokesData :=
  BoundaryCanonicalRouteMeasureInput.ofTargetImageAlignmentFields
    faceContinuity projectLocal U.toBoundarySourceTargetImageAlignmentFields

@[simp]
theorem toBoundaryCanonicalRouteMeasureInput_sourceAlignment
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData)
    (projectLocal :
      ProjectLocalBoundaryMeasureConstructorInput
        U.toProjectLocalGlobalStokesData) :
    (U.toBoundaryCanonicalRouteMeasureInput faceContinuity projectLocal).sourceAlignment =
      U.toBoundarySourceProjectLocalAlignment :=
  rfl

/-- The project-local Stokes conclusion exposed from unified constructor data. -/
theorem stokes :
    U.globalBulkIntegral = U.globalBoundaryIntegral :=
  U.toProjectLocalConstructorData.stokes

end BoundarySourceAlignmentUnifiedData

end BoundarySourceAlignmentUnified

end Stokes

end
