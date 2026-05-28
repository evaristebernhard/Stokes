import Stokes.Global.BoundaryCanonicalRouteFromContinuity

/-!
# Semi-automatic project-local boundary measure constructors

This module narrows the caller surface for
`ProjectLocalBoundaryMeasureConstructorInput`.

The genuine global reconstruction facts are not hidden: the represented
boundary integral and the a.e. indicator reconstruction remain explicit in the
`ProjectLocalBoundaryGlobalMeasureFacts` record.  A second support-finite record
derives the a.e. reconstruction from support containment of the canonical
project-local lower-face pieces.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section ProjectLocalBoundaryMeasureAuto

universe u w c p b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {Piece : Type p} {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/--
The remaining genuine global measure facts for the canonical project-local
lower-face representation.

Canonical face continuity discharges measurability and local integrability;
chart-change data discharges the pointwise partition-term alignment.  The
fields here are exactly the global integral and a.e. reconstruction assertions
that still have to come from a measure/partition reconstruction theorem.
-/
structure ProjectLocalBoundaryGlobalMeasureFacts
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) where
  /-- Boundary-side integrand represented by the global boundary measure. -/
  boundaryIntegrand : (Fin n → Real) → Real
  /-- The genuine boundary measure integral. -/
  boundaryMeasureIntegral : Real
  /-- The represented project-local global boundary integral is this measure integral. -/
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :
    D.globalBoundaryIntegral = boundaryMeasureIntegral
  /-- The boundary measure integral is the integral of the global boundary integrand. -/
  boundaryMeasureIntegral_eq_integral :
    boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume
  /-- A.e. reconstruction by the canonical lower-zero-face indicator pieces. -/
  boundaryIntegrand_ae_eq_indicatorSum :
    boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
      boundaryMeasureIndicatorSum D.activeCharts D.localPieces
        D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand

namespace ProjectLocalBoundaryGlobalMeasureFacts

variable {D : ProjectLocalGlobalStokesData I ω Chart Piece}
variable (G : ProjectLocalBoundaryGlobalMeasureFacts D)

/--
Canonical face continuity plus a pointwise partition-term alignment fills the
project-local boundary measure constructor.
-/
def toProjectLocalBoundaryMeasureConstructorInput
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          D.boundaryPartitionTerm x q =
            projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
              (D.lowerCorner x q) (D.upperCorner x q)) :
    ProjectLocalBoundaryMeasureConstructorInput D :=
  F.toProjectLocalBoundaryMeasureConstructorInput
    G.boundaryIntegrand G.boundaryMeasureIntegral
    G.boundaryMeasureIntegral_eq_integral
    G.globalBoundaryIntegral_eq_boundaryMeasureIntegral
    hterm G.boundaryIntegrand_ae_eq_indicatorSum

@[simp]
theorem toProjectLocalBoundaryMeasureConstructorInput_boundaryIntegrand
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          D.boundaryPartitionTerm x q =
            projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
              (D.lowerCorner x q) (D.upperCorner x q)) :
    (G.toProjectLocalBoundaryMeasureConstructorInput F hterm).boundaryIntegrand =
      G.boundaryIntegrand := by
  rfl

@[simp]
theorem toProjectLocalBoundaryMeasureConstructorInput_boundaryMeasureIntegral
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          D.boundaryPartitionTerm x q =
            projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
              (D.lowerCorner x q) (D.upperCorner x q)) :
    (G.toProjectLocalBoundaryMeasureConstructorInput F hterm).boundaryMeasureIntegral =
      G.boundaryMeasureIntegral := by
  rfl

/-- Constructor from selected-target boundary chart-change data. -/
def toProjectLocalBoundaryMeasureConstructorInputOfSelected
    [IsManifold I 1 M]
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)
    (S : BoundaryChartChangeSelectedFamilyData D) :
    ProjectLocalBoundaryMeasureConstructorInput D :=
  G.toProjectLocalBoundaryMeasureConstructorInput F (by
    intro x hx q hq
    exact (S.pointwise_eq_boundaryPartition_selected x hx q hq).symm)

/-- Constructor from extended-target boundary chart-change data. -/
def toProjectLocalBoundaryMeasureConstructorInputOfExtended
    [IsManifold I 1 M]
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)
    (S : BoundaryChartChangeExtendedFamilyData D) :
    ProjectLocalBoundaryMeasureConstructorInput D :=
  G.toProjectLocalBoundaryMeasureConstructorInput F (by
    intro x hx q hq
    exact (S.pointwise_eq_boundaryPartition_extended x hx q hq).symm)

/-- Constructor from a pure COV family plus project-local chart-change compatibility. -/
def toProjectLocalBoundaryMeasureConstructorInputOfCOV
    [IsManifold I 1 M]
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)
    (S : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (A : BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility S D) :
    ProjectLocalBoundaryMeasureConstructorInput D :=
  G.toProjectLocalBoundaryMeasureConstructorInputOfSelected F
    (S.toBoundaryChartChangeSelectedFamilyData A)

end ProjectLocalBoundaryGlobalMeasureFacts

/--
Support-finite source for the project-local boundary global measure facts.

Here the global boundary integrand is the finite sum of the canonical
project-local lower-face scalar pieces by definition.  The a.e. indicator
reconstruction is then derived from the support-containment field below.
The actual integral identity for that finite sum remains a field.
-/
structure ProjectLocalBoundarySupportFiniteMeasureFacts
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) where
  /-- The genuine boundary measure integral. -/
  boundaryMeasureIntegral : Real
  /-- The represented project-local global boundary integral is this measure integral. -/
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :
    D.globalBoundaryIntegral = boundaryMeasureIntegral
  /-- The finite canonical piece sum integrates to the represented boundary measure. -/
  boundaryMeasureIntegral_eq_integral :
    boundaryMeasureIntegral =
      ∫ y,
        boundaryMeasurePieceSum D.activeCharts D.localPieces
          D.projectLocalBoundaryPieceIntegrand y ∂volume
  /-- Active canonical lower-face pieces are supported in their selected face domains. -/
  boundaryPiece_support_subset :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        Function.support (D.projectLocalBoundaryPieceIntegrand x q) ⊆
          D.projectLocalBoundaryPieceSet x q

namespace ProjectLocalBoundarySupportFiniteMeasureFacts

variable {D : ProjectLocalGlobalStokesData I ω Chart Piece}
variable (G : ProjectLocalBoundarySupportFiniteMeasureFacts D)

/-- The canonical finite-sum global boundary integrand. -/
def boundaryIntegrand (_G : ProjectLocalBoundarySupportFiniteMeasureFacts D) :
    (Fin n → Real) → Real :=
  boundaryMeasurePieceSum D.activeCharts D.localPieces
    D.projectLocalBoundaryPieceIntegrand

@[simp]
theorem boundaryIntegrand_eq_pieceSum :
    G.boundaryIntegrand =
      boundaryMeasurePieceSum D.activeCharts D.localPieces
        D.projectLocalBoundaryPieceIntegrand := by
  rfl

/-- The a.e. indicator reconstruction derived from support containment. -/
theorem boundaryIntegrand_ae_eq_indicatorSum :
    G.boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
      boundaryMeasureIndicatorSum D.activeCharts D.localPieces
        D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand := by
  simpa [boundaryIntegrand] using
    (boundaryMeasurePieceSum_ae_eq_indicatorSum_of_support_subset
      (μ := (volume : Measure (Fin n → Real)))
      D.activeCharts D.localPieces
      D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand
      G.boundaryPiece_support_subset)

/-- Forget support-finite reconstruction to the global-measure facts record. -/
def toGlobalMeasureFacts :
    ProjectLocalBoundaryGlobalMeasureFacts D where
  boundaryIntegrand := G.boundaryIntegrand
  boundaryMeasureIntegral := G.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    G.globalBoundaryIntegral_eq_boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_integral := by
    simpa [boundaryIntegrand] using G.boundaryMeasureIntegral_eq_integral
  boundaryIntegrand_ae_eq_indicatorSum :=
    G.boundaryIntegrand_ae_eq_indicatorSum

@[simp]
theorem toGlobalMeasureFacts_boundaryIntegrand :
    G.toGlobalMeasureFacts.boundaryIntegrand = G.boundaryIntegrand := by
  rfl

@[simp]
theorem toGlobalMeasureFacts_boundaryMeasureIntegral :
    G.toGlobalMeasureFacts.boundaryMeasureIntegral =
      G.boundaryMeasureIntegral := by
  rfl

/-- Support-finite facts plus face continuity and term alignment build the constructor input. -/
def toProjectLocalBoundaryMeasureConstructorInput
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          D.boundaryPartitionTerm x q =
            projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
              (D.lowerCorner x q) (D.upperCorner x q)) :
    ProjectLocalBoundaryMeasureConstructorInput D :=
  G.toGlobalMeasureFacts.toProjectLocalBoundaryMeasureConstructorInput F hterm

/-- Selected-target chart-change constructor from support-finite global facts. -/
def toProjectLocalBoundaryMeasureConstructorInputOfSelected
    [IsManifold I 1 M]
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)
    (S : BoundaryChartChangeSelectedFamilyData D) :
    ProjectLocalBoundaryMeasureConstructorInput D :=
  G.toGlobalMeasureFacts.toProjectLocalBoundaryMeasureConstructorInputOfSelected F S

/-- Extended-target chart-change constructor from support-finite global facts. -/
def toProjectLocalBoundaryMeasureConstructorInputOfExtended
    [IsManifold I 1 M]
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)
    (S : BoundaryChartChangeExtendedFamilyData D) :
    ProjectLocalBoundaryMeasureConstructorInput D :=
  G.toGlobalMeasureFacts.toProjectLocalBoundaryMeasureConstructorInputOfExtended F S

/-- COV-family constructor from support-finite global facts. -/
def toProjectLocalBoundaryMeasureConstructorInputOfCOV
    [IsManifold I 1 M]
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)
    (S : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (A : BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility S D) :
    ProjectLocalBoundaryMeasureConstructorInput D :=
  G.toGlobalMeasureFacts.toProjectLocalBoundaryMeasureConstructorInputOfCOV F S A

end ProjectLocalBoundarySupportFiniteMeasureFacts

section Route

variable {selectedPartition : SelectedBoxPartitionOfUnity I ω}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
variable
    {T :
      M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas
        BoundaryPiece}
variable {P : ProjectLocalGlobalStokesData I ω M BoundaryPiece}

namespace ProjectLocalBoundaryGlobalMeasureFacts

variable (G : ProjectLocalBoundaryGlobalMeasureFacts P)

/--
Global measure facts, canonical face continuity, and source alignment build
the compact route input once chart-change alignment is supplied.
-/
def toBoundaryCanonicalRouteMeasureInput
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (hterm :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.localPieces x →
          P.boundaryPartitionTerm x q =
            projectLocalBoundaryIntegral I (P.sourceChart x q) (P.targetChart x q) ω
              (P.lowerCorner x q) (P.upperCorner x q)) :
    BoundaryCanonicalRouteMeasureInput T P where
  faceContinuity := F
  projectLocal := G.toProjectLocalBoundaryMeasureConstructorInput F hterm
  sourceAlignment := sourceAlignment

/-- Selected-target chart-change route constructor. -/
def toBoundaryCanonicalRouteMeasureInputOfSelected
    [IsManifold I 1 M]
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (S : BoundaryChartChangeSelectedFamilyData P) :
    BoundaryCanonicalRouteMeasureInput T P :=
  G.toBoundaryCanonicalRouteMeasureInput F sourceAlignment (by
    intro x hx q hq
    exact (S.pointwise_eq_boundaryPartition_selected x hx q hq).symm)

/-- Extended-target chart-change route constructor. -/
def toBoundaryCanonicalRouteMeasureInputOfExtended
    [IsManifold I 1 M]
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (S : BoundaryChartChangeExtendedFamilyData P) :
    BoundaryCanonicalRouteMeasureInput T P :=
  G.toBoundaryCanonicalRouteMeasureInput F sourceAlignment (by
    intro x hx q hq
    exact (S.pointwise_eq_boundaryPartition_extended x hx q hq).symm)

/-- COV-family route constructor. -/
def toBoundaryCanonicalRouteMeasureInputOfCOV
    [IsManifold I 1 M]
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (S : BoundaryChartChangeOfVariablesFamily I ω M BoundaryPiece)
    (A : BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility S P) :
    BoundaryCanonicalRouteMeasureInput T P :=
  G.toBoundaryCanonicalRouteMeasureInputOfSelected F sourceAlignment
    (S.toBoundaryChartChangeSelectedFamilyData A)

end ProjectLocalBoundaryGlobalMeasureFacts

namespace ProjectLocalBoundarySupportFiniteMeasureFacts

variable (G : ProjectLocalBoundarySupportFiniteMeasureFacts P)

/-- Support-finite global facts plus route data build the compact boundary route input. -/
def toBoundaryCanonicalRouteMeasureInput
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (hterm :
      ∀ x, x ∈ P.activeCharts →
        ∀ q, q ∈ P.localPieces x →
          P.boundaryPartitionTerm x q =
            projectLocalBoundaryIntegral I (P.sourceChart x q) (P.targetChart x q) ω
              (P.lowerCorner x q) (P.upperCorner x q)) :
    BoundaryCanonicalRouteMeasureInput T P :=
  G.toGlobalMeasureFacts.toBoundaryCanonicalRouteMeasureInput F sourceAlignment hterm

/-- Selected-target chart-change route constructor from support-finite global facts. -/
def toBoundaryCanonicalRouteMeasureInputOfSelected
    [IsManifold I 1 M]
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (S : BoundaryChartChangeSelectedFamilyData P) :
    BoundaryCanonicalRouteMeasureInput T P :=
  G.toGlobalMeasureFacts.toBoundaryCanonicalRouteMeasureInputOfSelected
    F sourceAlignment S

/-- Extended-target chart-change route constructor from support-finite global facts. -/
def toBoundaryCanonicalRouteMeasureInputOfExtended
    [IsManifold I 1 M]
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (S : BoundaryChartChangeExtendedFamilyData P) :
    BoundaryCanonicalRouteMeasureInput T P :=
  G.toGlobalMeasureFacts.toBoundaryCanonicalRouteMeasureInputOfExtended
    F sourceAlignment S

/-- COV-family route constructor from support-finite global facts. -/
def toBoundaryCanonicalRouteMeasureInputOfCOV
    [IsManifold I 1 M]
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (S : BoundaryChartChangeOfVariablesFamily I ω M BoundaryPiece)
    (A : BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility S P) :
    BoundaryCanonicalRouteMeasureInput T P :=
  G.toGlobalMeasureFacts.toBoundaryCanonicalRouteMeasureInputOfCOV
    F sourceAlignment S A

end ProjectLocalBoundarySupportFiniteMeasureFacts

end Route

end ProjectLocalBoundaryMeasureAuto

end Stokes

end
