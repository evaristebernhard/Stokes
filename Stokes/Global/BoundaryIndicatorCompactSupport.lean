import Stokes.Global.BoundaryCanonicalFiniteReconstruction
import Stokes.Global.BoundaryCanonicalFaceMeasureFacts

/-!
# Compact support for indicator-localized boundary pieces

The support-finite boundary route uses indicator-localized lower-zero-face
pieces.  This module packages the compact-support data for those pieces: the
indicator gives algebraic support containment in the selected face set, and on
that set the indicator-localized function is equal to the raw face integrand,
so continuity is inherited from the canonical raw representative.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped Manifold Topology

namespace Stokes

section BoundaryIndicatorCompactSupport

universe u w c p a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {Piece : Type p}
variable {α : Type a} [TopologicalSpace α]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/-- On its own indicator set, an indicator-localized boundary piece inherits
continuity from the raw boundary piece. -/
theorem boundaryMeasurePieceIndicator_continuousOn_pieceSet
    (boundaryPieceSet : Chart → Piece → Set α)
    (rawBoundaryPieceIntegrand : Chart → Piece → α → Real)
    {x : Chart} {q : Piece}
    (hcont :
      ContinuousOn (rawBoundaryPieceIntegrand x q)
        (boundaryPieceSet x q)) :
    ContinuousOn
      (boundaryMeasurePieceIndicator boundaryPieceSet
        rawBoundaryPieceIntegrand x q)
      (boundaryPieceSet x q) := by
  refine hcont.congr ?_
  intro y hy
  simp [boundaryMeasurePieceIndicator, hy]

/-- Compact-support data for an indicator-localized boundary piece, using the
indicator set itself as compact carrier. -/
def boundaryMeasurePieceIndicator_compactSupportData
    (boundaryPieceSet : Chart → Piece → Set α)
    (rawBoundaryPieceIntegrand : Chart → Piece → α → Real)
    {x : Chart} {q : Piece}
    (hcompact : IsCompact (boundaryPieceSet x q))
    (hcont :
      ContinuousOn (rawBoundaryPieceIntegrand x q)
        (boundaryPieceSet x q)) :
    CompactSupportIntegrabilityData
      (boundaryMeasurePieceIndicator boundaryPieceSet
        rawBoundaryPieceIntegrand x q) :=
  CompactSupportIntegrabilityData.of (boundaryPieceSet x q) hcompact
    (boundaryMeasurePieceIndicator_continuousOn_pieceSet
      boundaryPieceSet rawBoundaryPieceIntegrand hcont)
    (boundaryMeasurePieceIndicator_support_subset
      boundaryPieceSet rawBoundaryPieceIntegrand x q)

namespace ProjectLocalGlobalStokesData

variable (D : ProjectLocalGlobalStokesData I ω Chart Piece)

/-- The canonical project-local boundary piece set is compact. -/
theorem projectLocalBoundaryPieceSet_isCompact
    (x : Chart) (q : Piece) :
    IsCompact (D.projectLocalBoundaryPieceSet x q) := by
  simpa [projectLocalBoundaryPieceSet] using
    (isCompact_lowerZeroFaceDomain (D.lowerCorner x q) (D.upperCorner x q))

/-- Compact-support data for the indicator-localized canonical
project-local boundary piece, assuming continuity of the raw canonical
integrand on its lower-zero-face domain. -/
def projectLocalBoundaryPieceIndicatorCompactSupportData
    {x : Chart} {q : Piece}
    (hcont :
      ContinuousOn (D.projectLocalBoundaryPieceIntegrand x q)
        (D.projectLocalBoundaryPieceSet x q)) :
    CompactSupportIntegrabilityData
      (boundaryMeasurePieceIndicator D.projectLocalBoundaryPieceSet
        D.projectLocalBoundaryPieceIntegrand x q) :=
  boundaryMeasurePieceIndicator_compactSupportData
    D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand
    (D.projectLocalBoundaryPieceSet_isCompact x q) hcont

/-- Ambient-box continuity of the transition pullback supplies compact-support
data for the indicator-localized canonical boundary piece. -/
def projectLocalBoundaryPieceIndicatorCompactSupportData_of_transition_continuousOn
    {x : Chart} {q : Piece}
    (ha0 : D.lowerCorner x q (0 : Fin (n + 1)) = 0)
    (hle : D.lowerCorner x q ≤ D.upperCorner x q)
    (hω :
      ContinuousOn
        (ManifoldForm.transitionPullbackInChart I (D.sourceChart x q)
          (D.targetChart x q) ω)
        (Icc (D.lowerCorner x q) (D.upperCorner x q))) :
    CompactSupportIntegrabilityData
      (boundaryMeasurePieceIndicator D.projectLocalBoundaryPieceSet
        D.projectLocalBoundaryPieceIntegrand x q) :=
  D.projectLocalBoundaryPieceIndicatorCompactSupportData
    (D.projectLocalBoundaryPieceIntegrand_continuousOn_of_transition_continuousOn
      ha0 hle hω)

end ProjectLocalGlobalStokesData

namespace ProjectLocalBoundaryCanonicalFaceContinuityData

variable {D : ProjectLocalGlobalStokesData I ω Chart Piece}
variable (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)

/-- Active compact-support data for the indicator-localized canonical
lower-zero-face pieces. -/
def boundaryPieceIndicatorCompactSupportData
    (x : Chart) (hx : x ∈ D.activeCharts)
    (q : Piece) (hq : q ∈ D.localPieces x) :
    CompactSupportIntegrabilityData
      (boundaryMeasurePieceIndicator D.projectLocalBoundaryPieceSet
        D.projectLocalBoundaryPieceIntegrand x q) :=
  D.projectLocalBoundaryPieceIndicatorCompactSupportData_of_transition_continuousOn
    (F.lowerCorner_zero x hx q hq)
    (F.lowerCorner_le_upper x hx q hq)
    (F.transitionPullback_continuousOn x hx q hq)

end ProjectLocalBoundaryCanonicalFaceContinuityData

end BoundaryIndicatorCompactSupport

section BoundaryIndicatorTargetCOV

universe u w p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type p}
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

namespace ProjectLocalBoundaryCanonicalFaceContinuityData

variable (F : ProjectLocalBoundaryCanonicalFaceContinuityData P)

/-- Selected-target-indexed compact-support field for the support-finite
canonical boundary pieces. -/
def selectedBoundaryPieceCompact
    (A : BoundarySourceProjectLocalAlignment T P) :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ T.targetImages.boundaryPieces x →
        CompactSupportIntegrabilityData
          (boundaryMeasurePieceIndicator P.projectLocalBoundaryPieceSet
            P.projectLocalBoundaryPieceIntegrand x q) := by
  intro x hx q hq
  exact
    ProjectLocalBoundaryCanonicalFaceContinuityData.boundaryPieceIndicatorCompactSupportData
      (D := P) F x (A.mem_active hx) q (A.mem_localPiece hq)

end ProjectLocalBoundaryCanonicalFaceContinuityData

namespace ProjectLocalBoundaryMeasureConstructorInput

variable (C : ProjectLocalBoundaryMeasureConstructorInput P)

/-- The compact-support field needed by
`ProjectLocalBoundaryMeasureConstructorInput.toBoundaryPieceSupportFiniteSumTargetCOVInput`,
constructed from canonical face continuity data. -/
def selectedBoundaryPieceCompact
    (A : BoundarySourceProjectLocalAlignment T P)
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData P) :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ T.targetImages.boundaryPieces x →
        CompactSupportIntegrabilityData
          ((C.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryPieceIntegrand
            x q) := by
  intro x hx q hq
  exact
    ProjectLocalBoundaryCanonicalFaceContinuityData.selectedBoundaryPieceCompact
      (T := T) F A x hx q hq

/-- Constructor version of the canonical finite-reconstruction target-COV input:
canonical face continuity supplies the missing compact-support field for the
indicator-localized lower-zero-face pieces. -/
def toBoundaryPieceSupportFiniteSumTargetCOVInputCanonicalFace
    (A : BoundarySourceProjectLocalAlignment T P)
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData P) :
    BoundaryPieceSupportFiniteSumTargetCOVInput
      (α := Fin n → Real) T (volume : Measure (Fin n → Real)) :=
  C.toBoundaryPieceSupportFiniteSumTargetCOVInput A
    (C.selectedBoundaryPieceCompact A F)

@[simp]
theorem toBoundaryPieceSupportFiniteSumTargetCOVInputCanonicalFace_pieces
    (A : BoundarySourceProjectLocalAlignment T P)
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData P) :
    (C.toBoundaryPieceSupportFiniteSumTargetCOVInputCanonicalFace A F).pieces =
      C.toSelectedBoundaryPieceSupportFiniteSumInput A := by
  rfl

@[simp]
theorem toBoundaryPieceSupportFiniteSumTargetCOVInputCanonicalFace_boundaryMeasureIntegral
    (A : BoundarySourceProjectLocalAlignment T P)
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData P) :
    (C.toBoundaryPieceSupportFiniteSumTargetCOVInputCanonicalFace A F).boundaryMeasureIntegral =
      C.boundaryMeasureIntegral := by
  rfl

end ProjectLocalBoundaryMeasureConstructorInput

end BoundaryIndicatorTargetCOV

end Stokes

end
