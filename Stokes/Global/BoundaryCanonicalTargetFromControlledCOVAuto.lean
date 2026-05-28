import Stokes.Global.BoundaryControlledTargetToM8Auto
import Stokes.Global.BoundaryOrientationMembershipToCOVAuto

/-!
# Canonical boundary target route from controlled COV data

This file is a thin constructor layer for the controlled-target boundary route.

`BoundaryControlledTargetToM8Auto` packages the target-image side as a
controlled family plus M8 resolved fields.  The canonical boundary-measure route
still wants either a `BoundaryCanonicalRouteMeasureInput` or the downstream
`CanonicalBoundaryTargetCompactSupportInput`.  The adapters below bridge those
two shapes without asking endpoint code to pass the large `boundaryTarget`
package directly.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryCanonicalTargetFromControlledCOVAuto

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

namespace BoundaryCanonicalRouteMeasureInput

variable
    {T :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}
    {P : ProjectLocalGlobalStokesData I omega M BoundaryPiece}

/-- The canonical compact-support boundary target package exposed directly from
the three-field canonical route wrapper. -/
def toCanonicalBoundaryTargetCompactSupportInput
    [IsManifold I 1 M]
    (R : BoundaryCanonicalRouteMeasureInput T P) :
    CanonicalBoundaryTargetCompactSupportInput
      (α := Fin n -> Real) T (volume : Measure (Fin n -> Real)) :=
  R.toBoundaryPieceSupportFiniteSumTargetCOVInput
    |>.toCanonicalBoundaryTargetCompactSupportInput

@[simp]
theorem toCanonicalBoundaryTargetCompactSupportInput_boundaryMeasureIntegral
    [IsManifold I 1 M]
    (R : BoundaryCanonicalRouteMeasureInput T P) :
    R.toCanonicalBoundaryTargetCompactSupportInput.boundaryMeasureIntegral =
      R.projectLocal.boundaryMeasureIntegral := by
  rfl

@[simp]
theorem toCanonicalBoundaryTargetCompactSupportInput_globalBoundaryIntegral
    [IsManifold I 1 M]
    (R : BoundaryCanonicalRouteMeasureInput T P) :
    R.toCanonicalBoundaryTargetCompactSupportInput.globalBoundaryIntegral =
      P.globalBoundaryIntegral := by
  rfl

/-- Boundary-only M8 measure data exposed directly from the canonical route. -/
def toCanonicalBoundaryM8MeasureData
    [IsManifold I 1 M]
    (R : BoundaryCanonicalRouteMeasureInput T P) :
    M8BoundaryMeasureData I omega selectedPartition T.targetImages :=
  R.toCanonicalBoundaryTargetCompactSupportInput.canonicalBoundaryM8MeasureData

@[simp]
theorem toCanonicalBoundaryM8MeasureData_boundaryPartitionTerm
    [IsManifold I 1 M]
    (R : BoundaryCanonicalRouteMeasureInput T P) :
    R.toCanonicalBoundaryM8MeasureData.boundaryPartitionTerm =
      T.assembly.boundaryPartitionTerm := by
  rfl

@[simp]
theorem toCanonicalBoundaryM8MeasureData_boundaryMeasureIntegral
    [IsManifold I 1 M]
    (R : BoundaryCanonicalRouteMeasureInput T P) :
    R.toCanonicalBoundaryM8MeasureData.boundaryMeasureIntegral =
      R.projectLocal.boundaryMeasureIntegral := by
  rfl

end BoundaryCanonicalRouteMeasureInput

namespace BoundaryChartControlledTargetImageFamily.M8ResolvedFields

variable
    {F : BoundaryChartControlledTargetImageFamily I omega M BoundaryPiece}
    (D : M8ResolvedFields F selectedPartition orientedBoundaryAtlas)

@[simp]
theorem toM8TargetImageInput_targetImages_activeChartsCanonical :
    D.toM8TargetImageInput.targetImages.activeCharts = F.activeCharts := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundaryPiecesCanonical :
    D.toM8TargetImageInput.targetImages.boundaryPieces = F.localPieces := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceChartCanonical :
    D.toM8TargetImageInput.targetImages.sourceChart = F.sourceChart := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundarySourceChartCanonical :
    D.toM8TargetImageInput.targetImages.boundarySourceChart =
      F.boundarySourceChart := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceLowerCornerCanonical :
    D.toM8TargetImageInput.targetImages.sourceLowerCorner =
      F.sourceLowerCorner := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceUpperCornerCanonical :
    D.toM8TargetImageInput.targetImages.sourceUpperCorner =
      F.sourceUpperCorner := by
  rfl

/-- Source-alignment fields for a controlled/M8-resolved package, with the
hypotheses stated against the natural controlled family fields. -/
def toBoundarySourceTargetImageAlignmentFieldsOfProjectLocalCanonical
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

/-- Source/project-local alignment for a controlled/M8-resolved package. -/
def toBoundarySourceProjectLocalAlignmentOfProjectLocalCanonical
    (P : ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (activeCharts_eq : P.activeCharts = F.activeCharts)
    (localPieces_eq : forall x, P.localPieces x = F.localPieces x)
    (sourceChart_eq : forall x q, P.sourceChart x q = F.sourceChart x q)
    (targetChart_eq :
      forall x q, P.targetChart x q = F.boundarySourceChart x q)
    (lowerCorner_eq : forall x q, P.lowerCorner x q = F.sourceLowerCorner x q)
    (upperCorner_eq : forall x q, P.upperCorner x q = F.sourceUpperCorner x q) :
    BoundarySourceProjectLocalAlignment D.toM8TargetImageInput P :=
  (D.toBoundarySourceTargetImageAlignmentFieldsOfProjectLocalCanonical P
    activeCharts_eq localPieces_eq sourceChart_eq targetChart_eq
    lowerCorner_eq upperCorner_eq).toBoundarySourceProjectLocalAlignment

/-- The controlled M8 resolved fields identify their selected boundary
partition term with the transported target-image boundary integral. -/
theorem boundaryPartitionTerm_eq_targetIntegral_of_orientedAtlas
    [IsManifold I 1 M]
    (x : M) (hx : x ∈ F.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ F.localPieces x) :
    D.boundaryPartitionTerm x q =
      projectLocalBoundaryIntegral I
        (F.boundarySourceChart x q) (F.boundaryTargetChart x q) omega
        (F.targetLowerCorner x q) (F.targetUpperCorner x q) := by
  let A := D.toM8ResolvedInput.toAssemblyInput
  let S :=
    A.toSelectedBoundaryAssemblyData_of_orientedAtlas orientedBoundaryAtlas
      (by
        intro y hy r hr
        exact D.boundarySource_mem y hy r hr)
      (by
        intro y hy r hr
        exact D.boundaryTarget_mem y hy r hr)
  have hpoint :
      SelectedBoundaryAssemblyData.boundaryBoundaryTerm S x q =
        S.boundaryPartitionTerm x q :=
    S.pointwise_chartChange x (by simpa [S, A] using hx) q
      (by simpa [S, A] using hq)
  simpa [S, A, SelectedBoundaryAssemblyData.boundaryBoundaryTerm,
    BoundaryChartControlledTargetImageFamily.targetLowerCorner,
    BoundaryChartControlledTargetImageFamily.targetUpperCorner] using
    hpoint.symm

end BoundaryChartControlledTargetImageFamily.M8ResolvedFields

namespace M8BoundaryControlledTargetInput

variable
    (D :
      M8BoundaryControlledTargetInput I omega selectedPartition
        orientedBoundaryAtlas BoundaryPiece)
    {P : ProjectLocalGlobalStokesData I omega M BoundaryPiece}

/-- The small extra project-local alignment bundle needed to use a controlled
target package as the canonical boundary target route.

The source alignment identifies the project-local source package with the
controlled target images.  The final field says that the project-local boundary
partition term is the one selected by the controlled M8 fields. -/
structure BoundaryCanonicalProjectLocalFields where
  /-- Source coordinate alignment with the controlled target-image input. -/
  sourceAlignment :
    BoundarySourceProjectLocalAlignment D.toM8TargetImageInput P
  /-- Project-local boundary partition terms are the controlled M8 terms. -/
  boundaryPartitionTerm_eq_controlled :
    forall x q, P.boundaryPartitionTerm x q = D.fields.boundaryPartitionTerm x q

namespace BoundaryCanonicalProjectLocalFields

variable (A : BoundaryCanonicalProjectLocalFields D (P := P))

/-- Resolved-family/project-local compatibility generated from the controlled
target package and the small boundary partition-term alignment field. -/
def toResolvedProjectLocalCompatibility
    [IsManifold I 1 M] :
    D.family.toTargetImageResolvedFamily.ProjectLocalCompatibility P where
  activeCharts_eq := A.sourceAlignment.activeCharts_eq.trans D.fields.active_eq.symm
  localPieces_eq := by
    intro x
    simpa [BoundaryChartControlledTargetImageFamily.toTargetImageResolvedFamily] using
      A.sourceAlignment.localPieces_eq x
  sourceChart_eq := by
    intro x q
    simpa [BoundaryChartControlledTargetImageFamily.toTargetImageResolvedFamily] using
      A.sourceAlignment.sourceChart_eq x q
  targetChart_eq := by
    intro x q
    simpa [BoundaryChartControlledTargetImageFamily.toTargetImageResolvedFamily] using
      A.sourceAlignment.targetChart_eq x q
  lowerCorner_eq := by
    intro x q
    simpa [BoundaryChartControlledTargetImageFamily.toTargetImageResolvedFamily] using
      A.sourceAlignment.lowerCorner_eq x q
  upperCorner_eq := by
    intro x q
    simpa [BoundaryChartControlledTargetImageFamily.toTargetImageResolvedFamily] using
      A.sourceAlignment.upperCorner_eq x q
  boundaryPartitionTerm_eq := by
    intro x hx q hq
    exact (A.boundaryPartitionTerm_eq_controlled x q).trans
      (by
        simpa [BoundaryChartControlledTargetImageFamily.toTargetImageResolvedFamily,
          BoundaryChartTargetImageResolvedFamily.targetLowerCorner,
          BoundaryChartTargetImageResolvedFamily.targetUpperCorner,
          BoundaryChartControlledTargetImageFamily.targetBoxSelection,
          BoundaryChartControlledTargetImageFamily.targetLowerCorner,
          BoundaryChartControlledTargetImageFamily.targetUpperCorner] using
          D.fields.boundaryPartitionTerm_eq_targetIntegral_of_orientedAtlas
            x hx q hq)

/-- Canonical route input from global project-local measure facts and the
controlled target package, using orientation-membership COV internally. -/
def toBoundaryCanonicalRouteMeasureInputOfGlobalMeasure
    [IsManifold I 1 M]
    (globalMeasure : ProjectLocalBoundaryGlobalMeasureFacts P)
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P) :
    BoundaryCanonicalRouteMeasureInput D.toM8TargetImageInput P :=
  globalMeasure.toBoundaryCanonicalRouteMeasureInputOfOrientationMembershipTargetImageResolved
    faceContinuity A.sourceAlignment D.family.toTargetImageResolvedFamily
    A.toResolvedProjectLocalCompatibility

/-- Support-finite variant of the controlled canonical boundary route. -/
def toBoundaryCanonicalRouteMeasureInputOfSupportFinite
    [IsManifold I 1 M]
    (supportFinite : ProjectLocalBoundarySupportFiniteMeasureFacts P)
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P) :
    BoundaryCanonicalRouteMeasureInput D.toM8TargetImageInput P :=
  supportFinite.toBoundaryCanonicalRouteMeasureInputOfOrientationMembershipTargetImageResolved
    faceContinuity A.sourceAlignment D.family.toTargetImageResolvedFamily
    A.toResolvedProjectLocalCompatibility

/-- Canonical compact-support boundary target input from the controlled target
package and global project-local measure facts. -/
def toCanonicalBoundaryTargetCompactSupportInputOfGlobalMeasure
    [IsManifold I 1 M]
    (globalMeasure : ProjectLocalBoundaryGlobalMeasureFacts P)
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P) :
    CanonicalBoundaryTargetCompactSupportInput
      (α := Fin n -> Real) D.toM8TargetImageInput
      (volume : Measure (Fin n -> Real)) :=
  (toBoundaryCanonicalRouteMeasureInputOfGlobalMeasure
    (D := D) (P := P) A globalMeasure
    faceContinuity).toCanonicalBoundaryTargetCompactSupportInput

/-- Canonical compact-support boundary target input from the controlled target
package and support-finite project-local measure facts. -/
def toCanonicalBoundaryTargetCompactSupportInputOfSupportFinite
    [IsManifold I 1 M]
    (supportFinite : ProjectLocalBoundarySupportFiniteMeasureFacts P)
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P) :
    CanonicalBoundaryTargetCompactSupportInput
      (α := Fin n -> Real) D.toM8TargetImageInput
      (volume : Measure (Fin n -> Real)) :=
  (toBoundaryCanonicalRouteMeasureInputOfSupportFinite
    (D := D) (P := P) A supportFinite
    faceContinuity).toCanonicalBoundaryTargetCompactSupportInput

/-- Boundary-only M8 measure data from the controlled target package and global
project-local measure facts. -/
def toCanonicalBoundaryM8MeasureDataOfGlobalMeasure
    [IsManifold I 1 M]
    (globalMeasure : ProjectLocalBoundaryGlobalMeasureFacts P)
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P) :
    M8BoundaryMeasureData I omega selectedPartition D.toM8TargetImageInput.targetImages :=
  (toBoundaryCanonicalRouteMeasureInputOfGlobalMeasure
    (D := D) (P := P) A globalMeasure
    faceContinuity).toCanonicalBoundaryM8MeasureData

@[simp]
theorem toBoundaryCanonicalRouteMeasureInputOfGlobalMeasure_sourceAlignment
    [IsManifold I 1 M]
    (globalMeasure : ProjectLocalBoundaryGlobalMeasureFacts P)
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P) :
    (toBoundaryCanonicalRouteMeasureInputOfGlobalMeasure
      (D := D) (P := P) A globalMeasure faceContinuity).sourceAlignment =
      A.sourceAlignment := by
  rfl

end BoundaryCanonicalProjectLocalFields

end M8BoundaryControlledTargetInput

end BoundaryCanonicalTargetFromControlledCOVAuto

end Stokes

end
