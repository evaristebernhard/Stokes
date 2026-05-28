import Stokes.Global.BoundaryCanonicalFaceMeasureFacts
import Stokes.Global.BoundaryCanonicalFiniteReconstruction
import Stokes.Global.BoundaryIndicatorCompactSupport

/-!
# Boundary canonical route from face continuity

This module collects the natural source-side boundary-measure route that starts
from canonical lower-zero-face continuity data.

The route keeps the genuine global measure inputs explicit:

* the represented boundary integrand and measure integral;
* the a.e. reconstruction by canonical lower-face indicator pieces;
* the source/project-local alignment with the selected target-image data; and
* compact-support integrability for the indicator-localized pieces.

The last item is intentionally a field: the canonical continuity data gives
`IntegrableOn` for the raw lower-face pieces, while the support-finite target
COV route currently asks for compact-support data for the localized indicator
pieces.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryCanonicalRouteFromContinuity

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
variable
    {T :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}
variable {P : ProjectLocalGlobalStokesData I omega M BoundaryPiece}

/--
Natural canonical boundary route input.

This record is the shortest current route from canonical lower-face continuity
data to the support-finite target-COV boundary package.  The chart-change/COV
content is represented by the pointwise alignment between the selected
boundary partition terms and the project-local boundary integrals; constructors
below fill that field from selected-target, extended-target, or pure COV
families.
-/
structure BoundaryCanonicalRouteFromContinuityInput
    (T :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (P : ProjectLocalGlobalStokesData I omega M BoundaryPiece) where
  /-- Local canonical lower-zero-face facts for active project-local pieces. -/
  faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P
  /-- Boundary-side integrand represented by the global boundary measure. -/
  boundaryIntegrand : (Fin n → Real) → Real
  /-- The genuine boundary measure integral. -/
  boundaryMeasureIntegral : Real
  /-- The represented global boundary integral is this measure integral. -/
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :
    P.globalBoundaryIntegral = boundaryMeasureIntegral
  /-- The boundary measure integral is the integral of the global boundary integrand. -/
  boundaryMeasureIntegral_eq_integral :
    boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume
  /-- The selected boundary partition term is the project-local boundary integral. -/
  boundaryPartitionTerm_eq_projectLocalBoundaryIntegral :
    ∀ x, x ∈ P.activeCharts →
      ∀ q, q ∈ P.localPieces x →
        P.boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I (P.sourceChart x q) (P.targetChart x q) omega
            (P.lowerCorner x q) (P.upperCorner x q)
  /-- A.e. reconstruction by the canonical lower-zero-face indicator pieces. -/
  boundaryIntegrand_ae_eq_indicatorSum :
    boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
      boundaryMeasureIndicatorSum P.activeCharts P.localPieces
        P.projectLocalBoundaryPieceSet P.projectLocalBoundaryPieceIntegrand
  /-- Source coordinate bookkeeping aligning the project-local package with target COV. -/
  sourceAlignment : BoundarySourceProjectLocalAlignment T P
  /--
  Compact-support integrability for the indicator-localized canonical pieces.

  This is the explicit handoff to the later compact-support task: continuity
  handles the raw canonical face integrals, while target COV still consumes
  compact-support data for these localized support-finite pieces.
  -/
  boundaryPieceCompact :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ T.targetImages.boundaryPieces x →
        CompactSupportIntegrabilityData
          (boundaryMeasurePieceIndicator P.projectLocalBoundaryPieceSet
            P.projectLocalBoundaryPieceIntegrand x q)

namespace BoundaryCanonicalRouteFromContinuityInput

variable (R : BoundaryCanonicalRouteFromContinuityInput T P)

/-- The project-local constructor input supplied by continuity plus partition alignment. -/
def toProjectLocalBoundaryMeasureConstructorInput :
    ProjectLocalBoundaryMeasureConstructorInput P :=
  R.faceContinuity.toProjectLocalBoundaryMeasureConstructorInput
    R.boundaryIntegrand R.boundaryMeasureIntegral
    R.boundaryMeasureIntegral_eq_integral
    R.globalBoundaryIntegral_eq_boundaryMeasureIntegral
    R.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral
    R.boundaryIntegrand_ae_eq_indicatorSum

@[simp]
theorem toProjectLocalBoundaryMeasureConstructorInput_boundaryIntegrand :
    R.toProjectLocalBoundaryMeasureConstructorInput.boundaryIntegrand =
      R.boundaryIntegrand := by
  rfl

@[simp]
theorem toProjectLocalBoundaryMeasureConstructorInput_boundaryMeasureIntegral :
    R.toProjectLocalBoundaryMeasureConstructorInput.boundaryMeasureIntegral =
      R.boundaryMeasureIntegral := by
  rfl

/-- The project-local boundary measure data obtained from the canonical route. -/
def toProjectLocalBoundaryMeasureData :
    ProjectLocalBoundaryMeasureData
      (α := Fin n → Real) P (volume : Measure (Fin n → Real)) :=
  R.toProjectLocalBoundaryMeasureConstructorInput.toProjectLocalBoundaryMeasureData

@[simp]
theorem toProjectLocalBoundaryMeasureData_boundaryPieceSet :
    R.toProjectLocalBoundaryMeasureData.boundaryPieceSet =
      P.projectLocalBoundaryPieceSet := by
  rfl

@[simp]
theorem toProjectLocalBoundaryMeasureData_boundaryPieceIntegrand :
    R.toProjectLocalBoundaryMeasureData.boundaryPieceIntegrand =
      P.projectLocalBoundaryPieceIntegrand := by
  rfl

/-- The selected support-finite pieces used by the target-COV route. -/
def pieces :
    BoundaryPieceSupportFiniteSumInput
      (α := Fin n → Real) T.toSelectedBoundaryMeasurePartitionData :=
  R.toProjectLocalBoundaryMeasureConstructorInput
    |>.toSelectedBoundaryPieceSupportFiniteSumInput R.sourceAlignment

@[simp]
theorem pieces_boundaryPieceSet :
    R.pieces.boundaryPieceSet =
      P.projectLocalBoundaryPieceSet := by
  rfl

@[simp]
theorem pieces_boundaryPieceIntegrand :
    R.pieces.boundaryPieceIntegrand =
      boundaryMeasurePieceIndicator P.projectLocalBoundaryPieceSet
        P.projectLocalBoundaryPieceIntegrand := by
  rfl

/-- Canonical finite reconstruction input produced by the route. -/
def toBoundaryCanonicalFiniteReconstructionInput :
    BoundaryCanonicalFiniteReconstructionInput
      (α := Fin n → Real) T P (volume : Measure (Fin n → Real)) where
  projectLocal := R.toProjectLocalBoundaryMeasureData
  sourceAlignment := R.sourceAlignment
  boundaryPieceCompact := by
    intro x hx q hq
    simpa [toProjectLocalBoundaryMeasureData,
      ProjectLocalBoundaryMeasureData.toSelectedBoundaryPieceSupportFiniteSumInput]
      using R.boundaryPieceCompact x hx q hq

@[simp]
theorem toBoundaryCanonicalFiniteReconstructionInput_projectLocal :
    R.toBoundaryCanonicalFiniteReconstructionInput.projectLocal =
      R.toProjectLocalBoundaryMeasureData := by
  rfl

@[simp]
theorem toBoundaryCanonicalFiniteReconstructionInput_sourceAlignment :
    R.toBoundaryCanonicalFiniteReconstructionInput.sourceAlignment =
      R.sourceAlignment := by
  rfl

/-- Support-finite target-COV boundary input produced by the route. -/
def toBoundaryPieceSupportFiniteSumTargetCOVInput :
    BoundaryPieceSupportFiniteSumTargetCOVInput
      (α := Fin n → Real) T (volume : Measure (Fin n → Real)) :=
  R.toBoundaryCanonicalFiniteReconstructionInput
    |>.toBoundaryPieceSupportFiniteSumTargetCOVInput

@[simp]
theorem toBoundaryPieceSupportFiniteSumTargetCOVInput_pieces :
    R.toBoundaryPieceSupportFiniteSumTargetCOVInput.pieces =
      R.pieces := by
  rfl

@[simp]
theorem toBoundaryPieceSupportFiniteSumTargetCOVInput_boundaryMeasureIntegral :
    R.toBoundaryPieceSupportFiniteSumTargetCOVInput.boundaryMeasureIntegral =
      R.boundaryMeasureIntegral := by
  rfl

@[simp]
theorem toBoundaryPieceSupportFiniteSumTargetCOVInput_globalBoundaryIntegral :
    R.toBoundaryPieceSupportFiniteSumTargetCOVInput.globalBoundaryIntegral =
      P.globalBoundaryIntegral := by
  rfl

/-- The older COV-backed boundary-measure input obtained from the same route. -/
def toBoundaryMeasureFromTargetCOVInput :
    BoundaryMeasureFromTargetCOVInput
      (α := Fin n → Real) T (volume : Measure (Fin n → Real)) :=
  R.toBoundaryPieceSupportFiniteSumTargetCOVInput
    |>.toBoundaryMeasureFromTargetCOVInput

end BoundaryCanonicalRouteFromContinuityInput

namespace ProjectLocalBoundaryMeasureConstructorInput

variable (C : ProjectLocalBoundaryMeasureConstructorInput P)

/--
Canonical project-local boundary measure data, canonical face continuity, and
source/target alignment assemble the full continuity route.

This is the compact handoff for callers that already built the canonical
project-local measure package: the localized compact-support field required by
the target-COV route is synthesized from the face-continuity data and the
alignment with the selected target-image pieces.
-/
def toBoundaryCanonicalRouteFromContinuityInput
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P) :
    BoundaryCanonicalRouteFromContinuityInput T P where
  faceContinuity := faceContinuity
  boundaryIntegrand := C.boundaryIntegrand
  boundaryMeasureIntegral := C.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    C.globalBoundaryIntegral_eq_boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_integral :=
    C.boundaryMeasureIntegral_eq_integral
  boundaryPartitionTerm_eq_projectLocalBoundaryIntegral :=
    C.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral
  boundaryIntegrand_ae_eq_indicatorSum :=
    C.boundaryIntegrand_ae_eq_indicatorSum
  sourceAlignment := sourceAlignment
  boundaryPieceCompact :=
    ProjectLocalBoundaryCanonicalFaceContinuityData.selectedBoundaryPieceCompact
      (T := T) faceContinuity sourceAlignment

@[simp]
theorem toBoundaryCanonicalRouteFromContinuityInput_boundaryIntegrand
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P) :
    (C.toBoundaryCanonicalRouteFromContinuityInput
      faceContinuity sourceAlignment).boundaryIntegrand =
      C.boundaryIntegrand := by
  rfl

@[simp]
theorem toBoundaryCanonicalRouteFromContinuityInput_boundaryMeasureIntegral
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P) :
    (C.toBoundaryCanonicalRouteFromContinuityInput
      faceContinuity sourceAlignment).boundaryMeasureIntegral =
      C.boundaryMeasureIntegral := by
  rfl

@[simp]
theorem toBoundaryCanonicalRouteFromContinuityInput_sourceAlignment
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P) :
    (C.toBoundaryCanonicalRouteFromContinuityInput
      faceContinuity sourceAlignment).sourceAlignment =
      sourceAlignment := by
  rfl

/-- Direct theorem-facing finite-reconstruction input from canonical
project-local measure data. -/
def toBoundaryCanonicalFiniteReconstructionInputCanonicalFace
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P) :
    BoundaryCanonicalFiniteReconstructionInput
      (α := Fin n → Real) T P (volume : Measure (Fin n → Real)) :=
  (C.toBoundaryCanonicalRouteFromContinuityInput
    (T := T) faceContinuity sourceAlignment)
    |>.toBoundaryCanonicalFiniteReconstructionInput

@[simp]
theorem toBoundaryCanonicalFiniteReconstructionInputCanonicalFace_sourceAlignment
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P) :
    (C.toBoundaryCanonicalFiniteReconstructionInputCanonicalFace
      (T := T) faceContinuity sourceAlignment).sourceAlignment =
      sourceAlignment := by
  rfl

/-- Route-specific support-finite target-COV input from canonical
project-local measure data.  This is equivalent in strength to the direct
constructor in `BoundaryIndicatorCompactSupport`, but keeps the
`BoundaryCanonicalRouteFromContinuityInput` intermediate available to callers
that need it. -/
def toBoundaryPieceSupportFiniteSumTargetCOVInputCanonicalRoute
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P) :
    BoundaryPieceSupportFiniteSumTargetCOVInput
      (α := Fin n → Real) T (volume : Measure (Fin n → Real)) :=
  (C.toBoundaryCanonicalRouteFromContinuityInput
    (T := T) faceContinuity sourceAlignment)
    |>.toBoundaryPieceSupportFiniteSumTargetCOVInput

@[simp]
theorem toBoundaryPieceSupportFiniteSumTargetCOVInputCanonicalRoute_boundaryMeasureIntegral
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P) :
    (C.toBoundaryPieceSupportFiniteSumTargetCOVInputCanonicalRoute
      (T := T) faceContinuity sourceAlignment).boundaryMeasureIntegral =
      C.boundaryMeasureIntegral := by
  rfl

/-- Older COV-backed boundary-measure input from the same compact route. -/
def toBoundaryMeasureFromTargetCOVInputCanonicalRoute
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P) :
    BoundaryMeasureFromTargetCOVInput
      (α := Fin n → Real) T (volume : Measure (Fin n → Real)) :=
  (C.toBoundaryPieceSupportFiniteSumTargetCOVInputCanonicalRoute
    (T := T) faceContinuity sourceAlignment)
    |>.toBoundaryMeasureFromTargetCOVInput

@[simp]
theorem toBoundaryMeasureFromTargetCOVInputCanonicalRoute_boundaryMeasureIntegral
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P) :
    (C.toBoundaryMeasureFromTargetCOVInputCanonicalRoute
      (T := T) faceContinuity sourceAlignment).boundaryMeasureIntegral =
      C.boundaryMeasureIntegral := by
  rfl

end ProjectLocalBoundaryMeasureConstructorInput

/--
Three-field theorem-facing input for the canonical boundary route.

The record makes the intended caller surface explicit: once project-local
boundary measure data is available in the canonical lower-face shape, the only
remaining route data is canonical face continuity and the alignment with the
selected target-image boundary pieces.
-/
structure BoundaryCanonicalRouteMeasureInput
    (T :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (P : ProjectLocalGlobalStokesData I omega M BoundaryPiece) where
  /-- Canonical lower-zero-face smoothness/measure facts. -/
  faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P
  /-- Canonical project-local boundary measure data. -/
  projectLocal : ProjectLocalBoundaryMeasureConstructorInput P
  /-- Alignment from project-local source pieces to selected target-image pieces. -/
  sourceAlignment : BoundarySourceProjectLocalAlignment T P

namespace BoundaryCanonicalRouteMeasureInput

variable (R : BoundaryCanonicalRouteMeasureInput T P)

/-- Full route input assembled from the compact three-field wrapper. -/
def toBoundaryCanonicalRouteFromContinuityInput :
    BoundaryCanonicalRouteFromContinuityInput T P :=
  R.projectLocal.toBoundaryCanonicalRouteFromContinuityInput
    R.faceContinuity R.sourceAlignment

@[simp]
theorem toBoundaryCanonicalRouteFromContinuityInput_boundaryIntegrand :
    R.toBoundaryCanonicalRouteFromContinuityInput.boundaryIntegrand =
      R.projectLocal.boundaryIntegrand := by
  rfl

@[simp]
theorem toBoundaryCanonicalRouteFromContinuityInput_boundaryMeasureIntegral :
    R.toBoundaryCanonicalRouteFromContinuityInput.boundaryMeasureIntegral =
      R.projectLocal.boundaryMeasureIntegral := by
  rfl

/-- Finite-reconstruction input exposed by the compact wrapper. -/
def toBoundaryCanonicalFiniteReconstructionInput :
    BoundaryCanonicalFiniteReconstructionInput
      (α := Fin n → Real) T P (volume : Measure (Fin n → Real)) :=
  R.toBoundaryCanonicalRouteFromContinuityInput
    |>.toBoundaryCanonicalFiniteReconstructionInput

/-- Support-finite target-COV input exposed by the compact wrapper. -/
def toBoundaryPieceSupportFiniteSumTargetCOVInput :
    BoundaryPieceSupportFiniteSumTargetCOVInput
      (α := Fin n → Real) T (volume : Measure (Fin n → Real)) :=
  R.toBoundaryCanonicalRouteFromContinuityInput
    |>.toBoundaryPieceSupportFiniteSumTargetCOVInput

/-- Older COV-backed boundary-measure input exposed by the compact wrapper. -/
def toBoundaryMeasureFromTargetCOVInput :
    BoundaryMeasureFromTargetCOVInput
      (α := Fin n → Real) T (volume : Measure (Fin n → Real)) :=
  R.toBoundaryPieceSupportFiniteSumTargetCOVInput
    |>.toBoundaryMeasureFromTargetCOVInput

@[simp]
theorem toBoundaryPieceSupportFiniteSumTargetCOVInput_boundaryMeasureIntegral :
    R.toBoundaryPieceSupportFiniteSumTargetCOVInput.boundaryMeasureIntegral =
      R.projectLocal.boundaryMeasureIntegral := by
  rfl

@[simp]
theorem toBoundaryMeasureFromTargetCOVInput_boundaryMeasureIntegral :
    R.toBoundaryMeasureFromTargetCOVInput.boundaryMeasureIntegral =
      R.projectLocal.boundaryMeasureIntegral := by
  rfl

end BoundaryCanonicalRouteMeasureInput

/--
Constructor from a selected-target boundary chart-change family.

The family supplies the partition-term/project-local-integral alignment, while
the canonical face continuity data supplies local measurability and
integrability.
-/
def boundaryCanonicalRouteFromContinuityOfSelectedBoundaryChartChange
    [IsManifold I 1 M]
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hglobal : P.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum P.activeCharts P.localPieces
          P.projectLocalBoundaryPieceSet P.projectLocalBoundaryPieceIntegrand)
    (chartChange : BoundaryChartChangeSelectedFamilyData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (boundaryPieceCompact :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ T.targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData
            (boundaryMeasurePieceIndicator P.projectLocalBoundaryPieceSet
              P.projectLocalBoundaryPieceIntegrand x q)) :
    BoundaryCanonicalRouteFromContinuityInput T P where
  faceContinuity := faceContinuity
  boundaryIntegrand := boundaryIntegrand
  boundaryMeasureIntegral := boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := hglobal
  boundaryMeasureIntegral_eq_integral := hmeasure
  boundaryPartitionTerm_eq_projectLocalBoundaryIntegral := by
    intro x hx q hq
    exact (chartChange.pointwise_eq_boundaryPartition_selected x hx q hq).symm
  boundaryIntegrand_ae_eq_indicatorSum := hboundary
  sourceAlignment := sourceAlignment
  boundaryPieceCompact := boundaryPieceCompact

/-- Constructor from an extended-target boundary chart-change family. -/
def boundaryCanonicalRouteFromContinuityOfExtendedBoundaryChartChange
    [IsManifold I 1 M]
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hglobal : P.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum P.activeCharts P.localPieces
          P.projectLocalBoundaryPieceSet P.projectLocalBoundaryPieceIntegrand)
    (chartChange : BoundaryChartChangeExtendedFamilyData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (boundaryPieceCompact :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ T.targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData
            (boundaryMeasurePieceIndicator P.projectLocalBoundaryPieceSet
              P.projectLocalBoundaryPieceIntegrand x q)) :
    BoundaryCanonicalRouteFromContinuityInput T P where
  faceContinuity := faceContinuity
  boundaryIntegrand := boundaryIntegrand
  boundaryMeasureIntegral := boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := hglobal
  boundaryMeasureIntegral_eq_integral := hmeasure
  boundaryPartitionTerm_eq_projectLocalBoundaryIntegral := by
    intro x hx q hq
    exact (chartChange.pointwise_eq_boundaryPartition_extended x hx q hq).symm
  boundaryIntegrand_ae_eq_indicatorSum := hboundary
  sourceAlignment := sourceAlignment
  boundaryPieceCompact := boundaryPieceCompact

/-- Constructor from a pure boundary COV family plus project-local compatibility. -/
def boundaryCanonicalRouteFromContinuityOfCOVFamilyCompatibility
    [IsManifold I 1 M]
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hglobal : P.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum P.activeCharts P.localPieces
          P.projectLocalBoundaryPieceSet P.projectLocalBoundaryPieceIntegrand)
    (covFamily : BoundaryChartChangeOfVariablesFamily I omega M BoundaryPiece)
    (chartCompatibility :
      BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility
        covFamily P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (boundaryPieceCompact :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ T.targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData
            (boundaryMeasurePieceIndicator P.projectLocalBoundaryPieceSet
              P.projectLocalBoundaryPieceIntegrand x q)) :
    BoundaryCanonicalRouteFromContinuityInput T P :=
  boundaryCanonicalRouteFromContinuityOfSelectedBoundaryChartChange
    faceContinuity boundaryIntegrand boundaryMeasureIntegral hglobal hmeasure
    hboundary
    (covFamily.toBoundaryChartChangeSelectedFamilyData chartCompatibility)
    sourceAlignment boundaryPieceCompact

/--
Selected-target constructor with the compact-support field produced from the
same canonical face continuity data.
-/
def boundaryCanonicalRouteFromContinuityOfSelectedBoundaryChartChangeCanonicalFace
    [IsManifold I 1 M]
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hglobal : P.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum P.activeCharts P.localPieces
          P.projectLocalBoundaryPieceSet P.projectLocalBoundaryPieceIntegrand)
    (chartChange : BoundaryChartChangeSelectedFamilyData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P) :
    BoundaryCanonicalRouteFromContinuityInput T P :=
  boundaryCanonicalRouteFromContinuityOfSelectedBoundaryChartChange
    faceContinuity boundaryIntegrand boundaryMeasureIntegral hglobal hmeasure
    hboundary chartChange sourceAlignment
    (ProjectLocalBoundaryCanonicalFaceContinuityData.selectedBoundaryPieceCompact
      (T := T) faceContinuity sourceAlignment)

/--
Extended-target constructor with the compact-support field produced from
canonical face continuity.
-/
def boundaryCanonicalRouteFromContinuityOfExtendedBoundaryChartChangeCanonicalFace
    [IsManifold I 1 M]
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hglobal : P.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum P.activeCharts P.localPieces
          P.projectLocalBoundaryPieceSet P.projectLocalBoundaryPieceIntegrand)
    (chartChange : BoundaryChartChangeExtendedFamilyData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P) :
    BoundaryCanonicalRouteFromContinuityInput T P :=
  boundaryCanonicalRouteFromContinuityOfExtendedBoundaryChartChange
    faceContinuity boundaryIntegrand boundaryMeasureIntegral hglobal hmeasure
    hboundary chartChange sourceAlignment
    (ProjectLocalBoundaryCanonicalFaceContinuityData.selectedBoundaryPieceCompact
      (T := T) faceContinuity sourceAlignment)

/--
Pure COV-family constructor with compact-support data produced from canonical
face continuity.
-/
def boundaryCanonicalRouteFromContinuityOfCOVFamilyCompatibilityCanonicalFace
    [IsManifold I 1 M]
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hglobal : P.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum P.activeCharts P.localPieces
          P.projectLocalBoundaryPieceSet P.projectLocalBoundaryPieceIntegrand)
    (covFamily : BoundaryChartChangeOfVariablesFamily I omega M BoundaryPiece)
    (chartCompatibility :
      BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility
        covFamily P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P) :
    BoundaryCanonicalRouteFromContinuityInput T P :=
  boundaryCanonicalRouteFromContinuityOfCOVFamilyCompatibility
    faceContinuity boundaryIntegrand boundaryMeasureIntegral hglobal hmeasure
    hboundary covFamily chartCompatibility sourceAlignment
    (ProjectLocalBoundaryCanonicalFaceContinuityData.selectedBoundaryPieceCompact
      (T := T) faceContinuity sourceAlignment)

/--
Direct selected-target constructor for the finite reconstruction input.

This is the immediate handoff to the finite reconstruction layer; the record
constructor above is useful when callers also want the intermediate
project-local data.
-/
def boundaryCanonicalFiniteReconstructionInputOfSelectedBoundaryChartChange
    [IsManifold I 1 M]
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hglobal : P.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum P.activeCharts P.localPieces
          P.projectLocalBoundaryPieceSet P.projectLocalBoundaryPieceIntegrand)
    (chartChange : BoundaryChartChangeSelectedFamilyData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (boundaryPieceCompact :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ T.targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData
            (boundaryMeasurePieceIndicator P.projectLocalBoundaryPieceSet
              P.projectLocalBoundaryPieceIntegrand x q)) :
    BoundaryCanonicalFiniteReconstructionInput
      (α := Fin n → Real) T P (volume : Measure (Fin n → Real)) :=
  (boundaryCanonicalRouteFromContinuityOfSelectedBoundaryChartChange
    faceContinuity boundaryIntegrand boundaryMeasureIntegral hglobal hmeasure
    hboundary chartChange sourceAlignment boundaryPieceCompact)
    |>.toBoundaryCanonicalFiniteReconstructionInput

/--
Direct selected-target finite reconstruction constructor with compact-support
data derived from canonical face continuity.
-/
def boundaryCanonicalFiniteReconstructionInputOfSelectedBoundaryChartChangeCanonicalFace
    [IsManifold I 1 M]
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hglobal : P.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum P.activeCharts P.localPieces
          P.projectLocalBoundaryPieceSet P.projectLocalBoundaryPieceIntegrand)
    (chartChange : BoundaryChartChangeSelectedFamilyData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P) :
    BoundaryCanonicalFiniteReconstructionInput
      (α := Fin n → Real) T P (volume : Measure (Fin n → Real)) :=
  (boundaryCanonicalRouteFromContinuityOfSelectedBoundaryChartChangeCanonicalFace
    faceContinuity boundaryIntegrand boundaryMeasureIntegral hglobal hmeasure
    hboundary chartChange sourceAlignment)
    |>.toBoundaryCanonicalFiniteReconstructionInput

/-- Direct selected-target constructor for the support-finite target-COV input. -/
def boundaryPieceSupportFiniteSumTargetCOVInputOfSelectedBoundaryChartChange
    [IsManifold I 1 M]
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hglobal : P.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum P.activeCharts P.localPieces
          P.projectLocalBoundaryPieceSet P.projectLocalBoundaryPieceIntegrand)
    (chartChange : BoundaryChartChangeSelectedFamilyData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (boundaryPieceCompact :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ T.targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData
            (boundaryMeasurePieceIndicator P.projectLocalBoundaryPieceSet
              P.projectLocalBoundaryPieceIntegrand x q)) :
    BoundaryPieceSupportFiniteSumTargetCOVInput
      (α := Fin n → Real) T (volume : Measure (Fin n → Real)) :=
  (boundaryCanonicalRouteFromContinuityOfSelectedBoundaryChartChange
    faceContinuity boundaryIntegrand boundaryMeasureIntegral hglobal hmeasure
    hboundary chartChange sourceAlignment boundaryPieceCompact)
    |>.toBoundaryPieceSupportFiniteSumTargetCOVInput

/--
Direct selected-target support-finite COV constructor with compact-support data
derived from canonical face continuity.
-/
def boundaryPieceSupportFiniteSumTargetCOVInputOfSelectedBoundaryChartChangeCanonicalFace
    [IsManifold I 1 M]
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hglobal : P.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum P.activeCharts P.localPieces
          P.projectLocalBoundaryPieceSet P.projectLocalBoundaryPieceIntegrand)
    (chartChange : BoundaryChartChangeSelectedFamilyData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P) :
    BoundaryPieceSupportFiniteSumTargetCOVInput
      (α := Fin n → Real) T (volume : Measure (Fin n → Real)) :=
  (boundaryCanonicalRouteFromContinuityOfSelectedBoundaryChartChangeCanonicalFace
    faceContinuity boundaryIntegrand boundaryMeasureIntegral hglobal hmeasure
    hboundary chartChange sourceAlignment)
    |>.toBoundaryPieceSupportFiniteSumTargetCOVInput

end BoundaryCanonicalRouteFromContinuity

end Stokes

end
