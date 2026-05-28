import Stokes.Global.BoundaryGlobalMeasureFactsAuto

/-!
# Boundary partition-term alignment automation

This module packages the pointwise chart-change/COV alignment in the exact
shape consumed by `ProjectLocalBoundaryCanonicalFaceContinuityData.toGlobalMeasureFacts`.

The only content is direction and adapter bookkeeping: selected-target,
extended-target, and pure COV families already prove that the project-local
boundary integral agrees with the selected boundary partition term.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryPartitionTermAlignmentAuto

universe u w c p b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {Piece : Type p} {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

namespace BoundaryChartChangeFamilyData

variable [IsManifold I 1 M]
variable {D : ProjectLocalGlobalStokesData I omega Chart Piece}

/-- Selected-target chart-change data gives the term alignment consumed by
canonical boundary-measure constructors. -/
theorem boundaryPartitionTerm_eq_projectLocalBoundaryIntegral_selected
    (S : BoundaryChartChangeSelectedFamilyData D) :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        D.boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q)
            omega (D.lowerCorner x q) (D.upperCorner x q) := by
  intro x hx q hq
  exact (S.pointwise_eq_boundaryPartition_selected x hx q hq).symm

/-- Extended-target chart-change data gives the term alignment consumed by
canonical boundary-measure constructors. -/
theorem boundaryPartitionTerm_eq_projectLocalBoundaryIntegral_extended
    (S : BoundaryChartChangeExtendedFamilyData D) :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        D.boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q)
            omega (D.lowerCorner x q) (D.upperCorner x q) := by
  intro x hx q hq
  exact (S.pointwise_eq_boundaryPartition_extended x hx q hq).symm

end BoundaryChartChangeFamilyData

namespace BoundaryChartChangeOfVariablesFamily

variable [IsManifold I 1 M]
variable (S : BoundaryChartChangeOfVariablesFamily I omega Chart Piece)
variable {D : ProjectLocalGlobalStokesData I omega Chart Piece}

/-- A pure COV family plus project-local compatibility gives the term
alignment consumed by canonical boundary-measure constructors. -/
theorem boundaryPartitionTerm_eq_projectLocalBoundaryIntegral
    (A : ProjectLocalChartChangeCompatibility S D) :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        D.boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q)
            omega (D.lowerCorner x q) (D.upperCorner x q) := by
  exact
    (S.toBoundaryChartChangeSelectedFamilyData A)
      |>.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral_selected

end BoundaryChartChangeOfVariablesFamily

namespace ProjectLocalBoundaryCanonicalFaceContinuityData

variable {D : ProjectLocalGlobalStokesData I omega Chart Piece}
variable (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)
variable [IsManifold I 1 M]

/-- Selected-target chart-change data supplies the explicit `hterm` needed by
`toIndicatorIntegralReconstructionFacts`. -/
def toIndicatorIntegralReconstructionFactsOfSelected
    (S : BoundaryChartChangeSelectedFamilyData D) :
    ProjectLocalBoundaryIndicatorIntegralReconstructionFacts D :=
  F.toIndicatorIntegralReconstructionFacts
    S.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral_selected

/-- Extended-target chart-change data supplies the explicit `hterm` needed by
`toIndicatorIntegralReconstructionFacts`. -/
def toIndicatorIntegralReconstructionFactsOfExtended
    (S : BoundaryChartChangeExtendedFamilyData D) :
    ProjectLocalBoundaryIndicatorIntegralReconstructionFacts D :=
  F.toIndicatorIntegralReconstructionFacts
    S.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral_extended

/-- Pure COV data plus project-local compatibility supplies the explicit
`hterm` needed by `toIndicatorIntegralReconstructionFacts`. -/
def toIndicatorIntegralReconstructionFactsOfCOV
    (S : BoundaryChartChangeOfVariablesFamily I omega Chart Piece)
    (A :
      BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility
        S D) :
    ProjectLocalBoundaryIndicatorIntegralReconstructionFacts D :=
  F.toIndicatorIntegralReconstructionFacts
    (S.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral A)

/-- Canonical-indicator global measure facts from selected-target chart-change
alignment. -/
def toCanonicalIndicatorGlobalMeasureFactsOfSelected
    (S : BoundaryChartChangeSelectedFamilyData D) :
    ProjectLocalBoundaryCanonicalIndicatorGlobalMeasureFacts D :=
  (F.toIndicatorIntegralReconstructionFactsOfSelected S)
    |>.toCanonicalIndicatorGlobalMeasureFacts

/-- Canonical-indicator global measure facts from extended-target chart-change
alignment. -/
def toCanonicalIndicatorGlobalMeasureFactsOfExtended
    (S : BoundaryChartChangeExtendedFamilyData D) :
    ProjectLocalBoundaryCanonicalIndicatorGlobalMeasureFacts D :=
  (F.toIndicatorIntegralReconstructionFactsOfExtended S)
    |>.toCanonicalIndicatorGlobalMeasureFacts

/-- Canonical-indicator global measure facts from pure COV data and
project-local compatibility. -/
def toCanonicalIndicatorGlobalMeasureFactsOfCOV
    (S : BoundaryChartChangeOfVariablesFamily I omega Chart Piece)
    (A :
      BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility
        S D) :
    ProjectLocalBoundaryCanonicalIndicatorGlobalMeasureFacts D :=
  (F.toIndicatorIntegralReconstructionFactsOfCOV S A)
    |>.toCanonicalIndicatorGlobalMeasureFacts

/-- General project-local global boundary-measure facts from selected-target
chart-change alignment. -/
def toGlobalMeasureFactsOfSelected
    (S : BoundaryChartChangeSelectedFamilyData D) :
    ProjectLocalBoundaryGlobalMeasureFacts D :=
  (F.toIndicatorIntegralReconstructionFactsOfSelected S).toGlobalMeasureFacts

/-- General project-local global boundary-measure facts from extended-target
chart-change alignment. -/
def toGlobalMeasureFactsOfExtended
    (S : BoundaryChartChangeExtendedFamilyData D) :
    ProjectLocalBoundaryGlobalMeasureFacts D :=
  (F.toIndicatorIntegralReconstructionFactsOfExtended S).toGlobalMeasureFacts

/-- General project-local global boundary-measure facts from pure COV data and
project-local compatibility. -/
def toGlobalMeasureFactsOfCOV
    (S : BoundaryChartChangeOfVariablesFamily I omega Chart Piece)
    (A :
      BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility
        S D) :
    ProjectLocalBoundaryGlobalMeasureFacts D :=
  (F.toIndicatorIntegralReconstructionFactsOfCOV S A).toGlobalMeasureFacts

@[simp]
theorem toGlobalMeasureFactsOfSelected_boundaryIntegrand
    (S : BoundaryChartChangeSelectedFamilyData D) :
    (F.toGlobalMeasureFactsOfSelected S).boundaryIntegrand =
      D.projectLocalBoundaryCanonicalIndicatorSum := by
  rfl

@[simp]
theorem toGlobalMeasureFactsOfSelected_boundaryMeasureIntegral
    (S : BoundaryChartChangeSelectedFamilyData D) :
    (F.toGlobalMeasureFactsOfSelected S).boundaryMeasureIntegral =
      D.projectLocalBoundaryCanonicalIndicatorIntegral := by
  rfl

@[simp]
theorem toGlobalMeasureFactsOfExtended_boundaryIntegrand
    (S : BoundaryChartChangeExtendedFamilyData D) :
    (F.toGlobalMeasureFactsOfExtended S).boundaryIntegrand =
      D.projectLocalBoundaryCanonicalIndicatorSum := by
  rfl

@[simp]
theorem toGlobalMeasureFactsOfExtended_boundaryMeasureIntegral
    (S : BoundaryChartChangeExtendedFamilyData D) :
    (F.toGlobalMeasureFactsOfExtended S).boundaryMeasureIntegral =
      D.projectLocalBoundaryCanonicalIndicatorIntegral := by
  rfl

@[simp]
theorem toGlobalMeasureFactsOfCOV_boundaryIntegrand
    (S : BoundaryChartChangeOfVariablesFamily I omega Chart Piece)
    (A :
      BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility
        S D) :
    (F.toGlobalMeasureFactsOfCOV S A).boundaryIntegrand =
      D.projectLocalBoundaryCanonicalIndicatorSum := by
  rfl

@[simp]
theorem toGlobalMeasureFactsOfCOV_boundaryMeasureIntegral
    (S : BoundaryChartChangeOfVariablesFamily I omega Chart Piece)
    (A :
      BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility
        S D) :
    (F.toGlobalMeasureFactsOfCOV S A).boundaryMeasureIntegral =
      D.projectLocalBoundaryCanonicalIndicatorIntegral := by
  rfl

end ProjectLocalBoundaryCanonicalFaceContinuityData

section Route

variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
variable
    {T :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}
variable {P : ProjectLocalGlobalStokesData I omega M BoundaryPiece}
variable [IsManifold I 1 M]

namespace ProjectLocalBoundaryCanonicalFaceContinuityData

variable (F : ProjectLocalBoundaryCanonicalFaceContinuityData P)

/-- Canonical route input from selected-target chart-change alignment. -/
def toBoundaryCanonicalRouteMeasureInputOfSelected
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (S : BoundaryChartChangeSelectedFamilyData P) :
    BoundaryCanonicalRouteMeasureInput T P :=
  (F.toGlobalMeasureFactsOfSelected S).toBoundaryCanonicalRouteMeasureInput
    F sourceAlignment
    S.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral_selected

/-- Canonical route input from extended-target chart-change alignment. -/
def toBoundaryCanonicalRouteMeasureInputOfExtended
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (S : BoundaryChartChangeExtendedFamilyData P) :
    BoundaryCanonicalRouteMeasureInput T P :=
  (F.toGlobalMeasureFactsOfExtended S).toBoundaryCanonicalRouteMeasureInput
    F sourceAlignment
    S.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral_extended

/-- Canonical route input from pure COV data plus project-local
compatibility. -/
def toBoundaryCanonicalRouteMeasureInputOfCOV
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (S : BoundaryChartChangeOfVariablesFamily I omega M BoundaryPiece)
    (A :
      BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility
        S P) :
    BoundaryCanonicalRouteMeasureInput T P :=
  (F.toGlobalMeasureFactsOfCOV S A).toBoundaryCanonicalRouteMeasureInput
    F sourceAlignment
    (S.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral A)

@[simp]
theorem toBoundaryCanonicalRouteMeasureInputOfSelected_projectLocal
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (S : BoundaryChartChangeSelectedFamilyData P) :
    (F.toBoundaryCanonicalRouteMeasureInputOfSelected
      (T := T) sourceAlignment S).projectLocal =
      (F.toGlobalMeasureFactsOfSelected S).toProjectLocalBoundaryMeasureConstructorInput
        F S.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral_selected := by
  rfl

@[simp]
theorem toBoundaryCanonicalRouteMeasureInputOfExtended_projectLocal
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (S : BoundaryChartChangeExtendedFamilyData P) :
    (F.toBoundaryCanonicalRouteMeasureInputOfExtended
      (T := T) sourceAlignment S).projectLocal =
      (F.toGlobalMeasureFactsOfExtended S).toProjectLocalBoundaryMeasureConstructorInput
        F S.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral_extended := by
  rfl

@[simp]
theorem toBoundaryCanonicalRouteMeasureInputOfCOV_projectLocal
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (S : BoundaryChartChangeOfVariablesFamily I omega M BoundaryPiece)
    (A :
      BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility
        S P) :
    (F.toBoundaryCanonicalRouteMeasureInputOfCOV
      (T := T) sourceAlignment S A).projectLocal =
      (F.toGlobalMeasureFactsOfCOV S A).toProjectLocalBoundaryMeasureConstructorInput
        F (S.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral A) := by
  rfl

end ProjectLocalBoundaryCanonicalFaceContinuityData

end Route

end BoundaryPartitionTermAlignmentAuto

end Stokes

end
