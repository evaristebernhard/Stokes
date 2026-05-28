import Stokes.Global.BoundaryControlledTargetToM8Auto
import Stokes.Global.BoundaryOrientationMembershipToCOVAuto
import Stokes.Global.BoundaryChartChangeFromCOVAuto
import Stokes.Global.BoundaryPartitionTermFromResolvedTarget
import Stokes.Global.BoundaryPartitionTermAlignmentAuto

/-!
# Controlled target boxes with orientation-membership endpoint routing

This module is the endpoint-facing glue for the controlled-target-box boundary
route.  The controlled family already packages the target-image boxes used by
M8, while `BoundaryOrientationMembershipToCOVAuto` packages the oriented-atlas
membership needed by the selected boundary-partition chart change.

The declarations below compose those two routes.  They avoid exposing raw
boundary COV or target-image fields at the endpoint: callers work with a
controlled target family, its M8 resolved fields, and the usual project-local
alignment data.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryControlledTargetOrientationEndpointAuto

universe u w b ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

namespace BoundaryChartControlledTargetImageFamily.M8ResolvedFields

variable
    {F :
      BoundaryChartControlledTargetImageFamily I omega M BoundaryPiece}

variable
    (D :
      M8ResolvedFields F selectedPartition orientedBoundaryAtlas)

/-- Membership package for the boundary-partition chart change induced by the
controlled target endpoint fields. -/
def boundaryPartitionOrientationMembership
    (x : M) (hx : x ∈ F.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ F.localPieces x) :
    BoundaryChartOrientationMembership orientedBoundaryAtlas.charts
      (F.boundarySourceChart x q) (F.boundaryTargetChart x q) :=
  BoundaryChartOrientationMembership.of_mem
    (D.boundarySource_mem x hx q hq)
    (D.boundaryTarget_mem x hx q hq)

@[simp]
theorem boundaryPartitionOrientationMembership_source_mem
    (x : M) (hx : x ∈ F.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ F.localPieces x) :
    (D.boundaryPartitionOrientationMembership x hx q hq).source_mem =
      D.boundarySource_mem x hx q hq := by
  rfl

@[simp]
theorem boundaryPartitionOrientationMembership_boundarySource_mem
    (x : M) (hx : x ∈ F.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ F.localPieces x) :
    (D.boundaryPartitionOrientationMembership x hx q hq).boundarySource_mem =
      D.boundaryTarget_mem x hx q hq := by
  rfl

/-- Selected boundary assembly for the controlled target endpoint, using the
orientation-membership route rather than naked COV proofs. -/
def toSelectedBoundaryAssemblyDataOfOrientationMembership
    [IsManifold I 1 M] :
    SelectedBoundaryAssemblyData I omega M BoundaryPiece :=
  D.toM8ResolvedInput.toAssemblyInput
    |>.toSelectedBoundaryAssemblyData_of_orientationMembership
      orientedBoundaryAtlas
      (by
        intro x hx q hq
        exact D.boundaryPartitionOrientationMembership x hx q hq)

@[simp]
theorem toSelectedBoundaryAssemblyDataOfOrientationMembership_activeCharts
    [IsManifold I 1 M] :
    (D.toSelectedBoundaryAssemblyDataOfOrientationMembership).activeCharts =
      F.activeCharts := by
  rfl

@[simp]
theorem toSelectedBoundaryAssemblyDataOfOrientationMembership_boundaryPieces
    [IsManifold I 1 M] :
    (D.toSelectedBoundaryAssemblyDataOfOrientationMembership).boundaryPieces =
      F.localPieces := by
  rfl

/-- Pointwise selected COV for the boundary-partition term, reconstructed from
the controlled target fields plus orientation membership. -/
theorem boundaryPartitionSelectedCOVOfOrientationMembership
    [IsManifold I 1 M]
    (x : M) (hx : x ∈ F.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ F.localPieces x) :
    boundaryChartOrientedChangeOfVariables I
      (F.boundarySourceChart x q) (F.boundaryTargetChart x q) omega
      (F.targetLowerCorner x q) (F.targetUpperCorner x q)
      ((D.partitionTargetBox x q).lowerCorner)
      ((D.partitionTargetBox x q).upperCorner) := by
  simpa [toSelectedBoundaryAssemblyDataOfOrientationMembership,
    M8TargetImageResolvedInput.toAssemblyInput,
    BoundaryTargetImageToAssemblyInput.toBoundaryOrientationSelectedAssemblyInput,
    BoundaryTargetImageToAssemblyInput.partitionLowerCorner,
    BoundaryTargetImageToAssemblyInput.partitionUpperCorner,
    BoundaryChartControlledTargetImageFamily.targetLowerCorner,
    BoundaryChartControlledTargetImageFamily.targetUpperCorner] using
    (D.toSelectedBoundaryAssemblyDataOfOrientationMembership
      |>.chartChangeOfVariables x hx q hq)

/-- The controlled target endpoint identifies the selected boundary partition
term with the transported target-image boundary integral. -/
theorem boundaryPartitionTerm_eq_targetIntegral_of_orientationMembership
    [IsManifold I 1 M]
    (x : M) (hx : x ∈ F.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ F.localPieces x) :
    D.boundaryPartitionTerm x q =
      projectLocalBoundaryIntegral I
        (F.boundarySourceChart x q) (F.boundaryTargetChart x q) omega
        (F.targetLowerCorner x q) (F.targetUpperCorner x q) := by
  let S := D.toSelectedBoundaryAssemblyDataOfOrientationMembership
  have hpoint :
      SelectedBoundaryAssemblyData.boundaryBoundaryTerm S x q =
        S.boundaryPartitionTerm x q :=
    S.pointwise_chartChange x (by simpa [S] using hx) q
      (by simpa [S] using hq)
  simpa [S, toSelectedBoundaryAssemblyDataOfOrientationMembership,
    SelectedBoundaryAssemblyData.boundaryBoundaryTerm,
    M8TargetImageResolvedInput.toAssemblyInput,
    BoundaryTargetImageToAssemblyInput.toBoundaryOrientationSelectedAssemblyInput,
    BoundaryChartControlledTargetImageFamily.targetLowerCorner,
    BoundaryChartControlledTargetImageFamily.targetUpperCorner] using
    hpoint.symm

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

/-- Source alignment fields for a controlled target/M8-resolved package from
project-local fields aligned with the controlled family. -/
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

/-- Source/project-local alignment for a controlled target/M8-resolved package. -/
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

/-- Resolved-family/project-local compatibility generated from a controlled
target package and source-field equalities.  The boundary partition equality is
derived from the orientation-membership selected assembly above. -/
def toResolvedProjectLocalCompatibilityOfProjectLocal
    [IsManifold I 1 M]
    (P : ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (activeCharts_eq : P.activeCharts = F.activeCharts)
    (localPieces_eq : forall x, P.localPieces x = F.localPieces x)
    (sourceChart_eq : forall x q, P.sourceChart x q = F.sourceChart x q)
    (targetChart_eq :
      forall x q, P.targetChart x q = F.boundarySourceChart x q)
    (lowerCorner_eq : forall x q, P.lowerCorner x q = F.sourceLowerCorner x q)
    (upperCorner_eq : forall x q, P.upperCorner x q = F.sourceUpperCorner x q)
    (boundaryPartitionTerm_eq :
      forall x q, P.boundaryPartitionTerm x q = D.boundaryPartitionTerm x q) :
    F.toTargetImageResolvedFamily.ProjectLocalCompatibility P where
  activeCharts_eq := by
    simpa [BoundaryChartControlledTargetImageFamily.toTargetImageResolvedFamily]
      using activeCharts_eq
  localPieces_eq := by
    intro x
    simpa [BoundaryChartControlledTargetImageFamily.toTargetImageResolvedFamily]
      using localPieces_eq x
  sourceChart_eq := by
    intro x q
    simpa [BoundaryChartControlledTargetImageFamily.toTargetImageResolvedFamily]
      using sourceChart_eq x q
  targetChart_eq := by
    intro x q
    simpa [BoundaryChartControlledTargetImageFamily.toTargetImageResolvedFamily]
      using targetChart_eq x q
  lowerCorner_eq := by
    intro x q
    simpa [BoundaryChartControlledTargetImageFamily.toTargetImageResolvedFamily]
      using lowerCorner_eq x q
  upperCorner_eq := by
    intro x q
    simpa [BoundaryChartControlledTargetImageFamily.toTargetImageResolvedFamily]
      using upperCorner_eq x q
  boundaryPartitionTerm_eq := by
    intro x hx q hq
    calc
      P.boundaryPartitionTerm x q = D.boundaryPartitionTerm x q := by
        exact boundaryPartitionTerm_eq x q
      _ =
          projectLocalBoundaryIntegral I
            (F.boundarySourceChart x q) (F.boundaryTargetChart x q) omega
            (F.toTargetImageResolvedFamily.targetLowerCorner x q)
            (F.toTargetImageResolvedFamily.targetUpperCorner x q) := by
        simpa [BoundaryChartControlledTargetImageFamily.toTargetImageResolvedFamily,
          BoundaryChartTargetImageResolvedFamily.targetLowerCorner,
          BoundaryChartTargetImageResolvedFamily.targetUpperCorner,
          BoundaryChartControlledTargetImageFamily.targetBoxSelection,
          BoundaryChartControlledTargetImageFamily.targetLowerCorner,
          BoundaryChartControlledTargetImageFamily.targetUpperCorner] using
          D.boundaryPartitionTerm_eq_targetIntegral_of_orientationMembership
            x hx q hq

/-- Canonical boundary route input from controlled target data, with both the
source alignment and the selected chart-change route generated from the same
source-field equalities. -/
def toBoundaryCanonicalRouteMeasureInputOfProjectLocal
    [IsManifold I 1 M]
    (P : ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (globalMeasure : ProjectLocalBoundaryGlobalMeasureFacts P)
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (activeCharts_eq : P.activeCharts = F.activeCharts)
    (localPieces_eq : forall x, P.localPieces x = F.localPieces x)
    (sourceChart_eq : forall x q, P.sourceChart x q = F.sourceChart x q)
    (targetChart_eq :
      forall x q, P.targetChart x q = F.boundarySourceChart x q)
    (lowerCorner_eq : forall x q, P.lowerCorner x q = F.sourceLowerCorner x q)
    (upperCorner_eq : forall x q, P.upperCorner x q = F.sourceUpperCorner x q)
    (boundaryPartitionTerm_eq :
      forall x q, P.boundaryPartitionTerm x q = D.boundaryPartitionTerm x q) :
    BoundaryCanonicalRouteMeasureInput D.toM8TargetImageInput P :=
  globalMeasure.toBoundaryCanonicalRouteMeasureInputOfOrientationMembershipTargetImageResolved
    faceContinuity
    (D.toBoundarySourceProjectLocalAlignmentOfProjectLocal P activeCharts_eq
      localPieces_eq sourceChart_eq targetChart_eq lowerCorner_eq
      upperCorner_eq)
    F.toTargetImageResolvedFamily
    (toResolvedProjectLocalCompatibilityOfProjectLocal D P activeCharts_eq
      localPieces_eq sourceChart_eq targetChart_eq lowerCorner_eq
      upperCorner_eq boundaryPartitionTerm_eq)

/-- Support-finite variant of the controlled target canonical boundary route. -/
def toBoundaryCanonicalRouteMeasureInputOfSupportFiniteProjectLocal
    [IsManifold I 1 M]
    (P : ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (supportFinite : ProjectLocalBoundarySupportFiniteMeasureFacts P)
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (activeCharts_eq : P.activeCharts = F.activeCharts)
    (localPieces_eq : forall x, P.localPieces x = F.localPieces x)
    (sourceChart_eq : forall x q, P.sourceChart x q = F.sourceChart x q)
    (targetChart_eq :
      forall x q, P.targetChart x q = F.boundarySourceChart x q)
    (lowerCorner_eq : forall x q, P.lowerCorner x q = F.sourceLowerCorner x q)
    (upperCorner_eq : forall x q, P.upperCorner x q = F.sourceUpperCorner x q)
    (boundaryPartitionTerm_eq :
      forall x q, P.boundaryPartitionTerm x q = D.boundaryPartitionTerm x q) :
    BoundaryCanonicalRouteMeasureInput D.toM8TargetImageInput P :=
  D.toBoundaryCanonicalRouteMeasureInputOfProjectLocal P
    supportFinite.toGlobalMeasureFacts faceContinuity activeCharts_eq
    localPieces_eq sourceChart_eq targetChart_eq lowerCorner_eq upperCorner_eq
    boundaryPartitionTerm_eq

end BoundaryChartControlledTargetImageFamily.M8ResolvedFields

namespace ProjectLocalConstructorData

variable
    {F :
      BoundaryChartControlledTargetImageFamily I omega M BoundaryPiece}

/-- Project-local constructor data aligned with a controlled target/M8-resolved
family.  This is the constructor-data analogue of the controlled source
alignment wrapper above. -/
def toBoundarySourceTargetImageAlignmentFieldsOfControlledM8Resolved
    (C : ProjectLocalConstructorData I omega M BoundaryPiece)
    (D :
      BoundaryChartControlledTargetImageFamily.M8ResolvedFields
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

/-- Project-local constructor data as a controlled target source alignment. -/
def toBoundarySourceProjectLocalAlignmentOfControlledM8Resolved
    (C : ProjectLocalConstructorData I omega M BoundaryPiece)
    (D :
      BoundaryChartControlledTargetImageFamily.M8ResolvedFields
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
  (C.toBoundarySourceTargetImageAlignmentFieldsOfControlledM8Resolved D
    activeCharts_eq localPieces_eq sourceChart_eq targetChart_eq
    lowerCorner_eq upperCorner_eq).toBoundarySourceProjectLocalAlignment

end ProjectLocalConstructorData

section Endpoint

variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]

namespace NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

variable
    (B :
      NaturalCompactSupportBulkProjectLocalAutoCollapsedInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)

/-- Endpoint base input from a controlled target family.  The selected
boundary-partition COV and resolved target-image compatibility are generated
internally from the controlled target package and oriented-atlas membership. -/
def toBulkBoundarySeparatedBaseInputOfControlledTargetOrientationMembership
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts boundaryProjectLocal)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData boundaryProjectLocal)
    (F :
      BoundaryChartControlledTargetImageFamily I omega M BoundaryPiece)
    (D :
      BoundaryChartControlledTargetImageFamily.M8ResolvedFields
        F B.selectedPartition B.orientedBoundaryAtlas)
    (activeCharts_eq : boundaryProjectLocal.activeCharts = F.activeCharts)
    (localPieces_eq :
      forall x, boundaryProjectLocal.localPieces x = F.localPieces x)
    (sourceChart_eq :
      forall x q, boundaryProjectLocal.sourceChart x q = F.sourceChart x q)
    (targetChart_eq :
      forall x q,
        boundaryProjectLocal.targetChart x q = F.boundarySourceChart x q)
    (lowerCorner_eq :
      forall x q, boundaryProjectLocal.lowerCorner x q = F.sourceLowerCorner x q)
    (upperCorner_eq :
      forall x q, boundaryProjectLocal.upperCorner x q = F.sourceUpperCorner x q)
    (boundaryPartitionTerm_eq :
      forall x q,
        boundaryProjectLocal.boundaryPartitionTerm x q =
          D.boundaryPartitionTerm x q)
    (targetImageInput_eq : B.targetImageInput = D.toM8TargetImageInput) :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  B.toBulkBoundarySeparatedBaseInput boundaryProjectLocal
    (by
      simpa [targetImageInput_eq] using
        (D.toBoundaryCanonicalRouteMeasureInputOfProjectLocal
          boundaryProjectLocal globalMeasure faceContinuity activeCharts_eq
          localPieces_eq sourceChart_eq targetChart_eq lowerCorner_eq
          upperCorner_eq boundaryPartitionTerm_eq))

end NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

end Endpoint

end BoundaryControlledTargetOrientationEndpointAuto

end Stokes

end
