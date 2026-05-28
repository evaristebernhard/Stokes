import Stokes.Global.BoundaryMeasureAEReconstruction
import Stokes.Global.BoundaryMeasureFromTargetCOV

/-!
# Boundary finite-piece sums from support containment

This file is a small bridge for the boundary measure route.  It removes one
piece of arbitrary input from `BoundaryMeasureAEReconstructionInput`: the
global boundary integrand is now the selected finite piece sum by definition,
and the a.e. indicator reconstruction follows from active piece support
containment.

For the common localized-piece case, we also provide an indicator-piece
constructor.  If each boundary piece is already written as the indicator of its
piece set, the support containment is automatic.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryPieceSupportFiniteSum

universe u w c p a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {Piece : Type p}
variable {α : Type a} [MeasurableSpace α]
variable {μ : Measure α}

omit [MeasurableSpace α] in
/-- Indicator-localized boundary pieces are supported in their indicator set. -/
theorem boundaryMeasurePieceIndicator_support_subset
    (boundaryPieceSet : Chart → Piece → Set α)
    (rawBoundaryPieceIntegrand : Chart → Piece → α → Real)
    (x : Chart) (q : Piece) :
    Function.support
        (boundaryMeasurePieceIndicator boundaryPieceSet
          rawBoundaryPieceIntegrand x q) ⊆
      boundaryPieceSet x q := by
  intro y hy
  by_contra hmem
  exact hy (by
    simp [boundaryMeasurePieceIndicator, Set.indicator_of_notMem hmem])

/--
Boundary-piece data whose global boundary integrand is canonically the finite
sum of the selected active pieces.

Compared with `BoundaryMeasureAEReconstructionInput`, this record no longer
asks for an arbitrary `boundaryIntegrand` plus a proof that it is the selected
piece sum.  The only remaining reconstruction content is the geometric support
containment of active pieces in their selected piece sets.
-/
structure BoundaryPieceSupportFiniteSumInput
    (P : BoundaryMeasurePartitionData Chart Piece) where
  /-- Selected boundary-piece support set. -/
  boundaryPieceSet : Chart → Piece → Set α
  /-- Scalar integrand attached to one selected boundary piece. -/
  boundaryPieceIntegrand : Chart → Piece → α → Real
  /-- Active selected piece integrands are supported in their piece sets. -/
  boundaryPiece_support_subset :
    ∀ x, x ∈ P.activeCharts →
      ∀ q, q ∈ P.boundaryPieces x →
        Function.support (boundaryPieceIntegrand x q) ⊆
          boundaryPieceSet x q

namespace BoundaryPieceSupportFiniteSumInput

variable {P : BoundaryMeasurePartitionData Chart Piece}
variable (R : BoundaryPieceSupportFiniteSumInput (α := α) P)

/-- The canonical global boundary integrand represented by the selected pieces. -/
def boundaryIntegrand : α → Real :=
  boundaryMeasurePieceSum P.activeCharts P.boundaryPieces
    R.boundaryPieceIntegrand

@[simp]
theorem boundaryIntegrand_eq_pieceSum :
    R.boundaryIntegrand =
      boundaryMeasurePieceSum P.activeCharts P.boundaryPieces
        R.boundaryPieceIntegrand := by
  rfl

/-- The support-finite-sum input fills the existing AE reconstruction input. -/
def toBoundaryMeasureAEReconstructionInput :
    BoundaryMeasureAEReconstructionInput (α := α) P where
  boundaryIntegrand := R.boundaryIntegrand
  boundaryPieceSet := R.boundaryPieceSet
  boundaryPieceIntegrand := R.boundaryPieceIntegrand
  boundaryIntegrand_eq_pieceSum := by
    rfl
  boundaryPiece_support_subset := R.boundaryPiece_support_subset

@[simp]
theorem toBoundaryMeasureAEReconstructionInput_boundaryIntegrand :
    R.toBoundaryMeasureAEReconstructionInput.boundaryIntegrand =
      R.boundaryIntegrand := by
  rfl

@[simp]
theorem toBoundaryMeasureAEReconstructionInput_boundaryPieceSet :
    R.toBoundaryMeasureAEReconstructionInput.boundaryPieceSet =
      R.boundaryPieceSet := by
  rfl

@[simp]
theorem toBoundaryMeasureAEReconstructionInput_boundaryPieceIntegrand :
    R.toBoundaryMeasureAEReconstructionInput.boundaryPieceIntegrand =
      R.boundaryPieceIntegrand := by
  rfl

/-- The exact selected indicator reconstruction supplied by support containment. -/
theorem boundaryIntegrand_eq_selectedIndicatorSum :
    R.boundaryIntegrand =
      boundaryMeasureIndicatorSum P.activeCharts P.boundaryPieces
        R.boundaryPieceSet R.boundaryPieceIntegrand :=
  R.toBoundaryMeasureAEReconstructionInput
    |>.boundaryIntegrand_eq_selectedTargetIndicatorSum

/-- The downstream a.e. selected indicator reconstruction. -/
theorem boundaryIntegrand_ae_eq_selectedIndicatorSum :
    R.boundaryIntegrand =ᵐ[μ]
      boundaryMeasureIndicatorSum P.activeCharts P.boundaryPieces
        R.boundaryPieceSet R.boundaryPieceIntegrand :=
  R.toBoundaryMeasureAEReconstructionInput
    |>.boundaryIntegrand_ae_eq_selectedTargetIndicatorSum (μ := μ)

/--
Build support-finite-sum data when every selected piece is already written as
an indicator-localized raw piece.
-/
def ofIndicatorPieces
    (P : BoundaryMeasurePartitionData Chart Piece)
    (boundaryPieceSet : Chart → Piece → Set α)
    (rawBoundaryPieceIntegrand : Chart → Piece → α → Real) :
    BoundaryPieceSupportFiniteSumInput (α := α) P where
  boundaryPieceSet := boundaryPieceSet
  boundaryPieceIntegrand :=
    boundaryMeasurePieceIndicator boundaryPieceSet rawBoundaryPieceIntegrand
  boundaryPiece_support_subset := by
    intro x _hx q _hq
    exact boundaryMeasurePieceIndicator_support_subset
      boundaryPieceSet rawBoundaryPieceIntegrand x q

@[simp]
theorem ofIndicatorPieces_boundaryPieceSet
    (P : BoundaryMeasurePartitionData Chart Piece)
    (boundaryPieceSet : Chart → Piece → Set α)
    (rawBoundaryPieceIntegrand : Chart → Piece → α → Real) :
    (ofIndicatorPieces (α := α) P boundaryPieceSet
      rawBoundaryPieceIntegrand).boundaryPieceSet =
        boundaryPieceSet := by
  rfl

@[simp]
theorem ofIndicatorPieces_boundaryPieceIntegrand
    (P : BoundaryMeasurePartitionData Chart Piece)
    (boundaryPieceSet : Chart → Piece → Set α)
    (rawBoundaryPieceIntegrand : Chart → Piece → α → Real) :
    (ofIndicatorPieces (α := α) P boundaryPieceSet
      rawBoundaryPieceIntegrand).boundaryPieceIntegrand =
        boundaryMeasurePieceIndicator boundaryPieceSet
          rawBoundaryPieceIntegrand := by
  rfl

@[simp]
theorem ofIndicatorPieces_boundaryIntegrand
    (P : BoundaryMeasurePartitionData Chart Piece)
    (boundaryPieceSet : Chart → Piece → Set α)
    (rawBoundaryPieceIntegrand : Chart → Piece → α → Real) :
    (ofIndicatorPieces (α := α) P boundaryPieceSet
      rawBoundaryPieceIntegrand).boundaryIntegrand =
        boundaryMeasureIndicatorSum P.activeCharts P.boundaryPieces
          boundaryPieceSet rawBoundaryPieceIntegrand := by
  rfl

end BoundaryPieceSupportFiniteSumInput

section TargetCOVRoute

variable [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
variable [IsFiniteMeasureOnCompacts μ]
variable {BoundaryPiece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/--
Target-image COV boundary-measure input with the finite-piece reconstruction
factored through `BoundaryPieceSupportFiniteSumInput`.

This is smaller than `BoundaryMeasureFromTargetCOVInput`: it has no independent
`boundaryIntegrand` and no a.e. reconstruction field.  The boundary integrand
is the selected finite piece sum, and the a.e. reconstruction is derived from
support containment.
-/
structure BoundaryPieceSupportFiniteSumTargetCOVInput
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (μ : Measure α) where
  /-- Selected finite-piece data and active support containment. -/
  pieces :
    BoundaryPieceSupportFiniteSumInput (α := α)
      D.toSelectedBoundaryMeasurePartitionData
  /-- Genuine boundary measure integral. -/
  boundaryMeasureIntegral : Real
  /-- The boundary measure integral is the integral of the canonical piece sum. -/
  boundaryMeasureIntegral_eq_integral :
    boundaryMeasureIntegral = ∫ y, pieces.boundaryIntegrand y ∂μ
  /-- Active boundary support sets are measurable. -/
  boundaryPieceSet_measurable :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ D.targetImages.boundaryPieces x →
        MeasurableSet (pieces.boundaryPieceSet x q)
  /-- Active boundary-piece integrands have compact-support integrability. -/
  boundaryPieceCompact :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ D.targetImages.boundaryPieces x →
        CompactSupportIntegrabilityData (pieces.boundaryPieceIntegrand x q)
  /--
  Missing measure theorem: the source project-local boundary integral is the
  genuine set integral on this localized boundary piece.
  -/
  sourceProjectLocal_eq_setIntegral :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ D.targetImages.boundaryPieces x →
        projectLocalBoundaryIntegral I
            (D.targetImages.sourceChart x q)
            (D.targetImages.boundarySourceChart x q) omega
            (D.targetImages.sourceLowerCorner x q)
            (D.targetImages.sourceUpperCorner x q) =
          ∫ y in pieces.boundaryPieceSet x q,
            pieces.boundaryPieceIntegrand x q y ∂μ
  /-- The represented global boundary integral. -/
  globalBoundaryIntegral : Real
  /-- The represented global boundary integral is the measure integral. -/
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :
    globalBoundaryIntegral = boundaryMeasureIntegral

namespace BoundaryPieceSupportFiniteSumTargetCOVInput

variable
    {D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}
    (B : BoundaryPieceSupportFiniteSumTargetCOVInput (α := α) D μ)

/-- The derived a.e. reconstruction in the selected target-image shape. -/
theorem boundaryIntegrand_ae_eq_indicatorSum :
    B.pieces.boundaryIntegrand =ᵐ[μ]
      boundaryMeasureIndicatorSum selectedPartition.active
        D.targetImages.boundaryPieces B.pieces.boundaryPieceSet
        B.pieces.boundaryPieceIntegrand := by
  simpa using
    (B.pieces.boundaryIntegrand_ae_eq_selectedIndicatorSum (μ := μ))

/-- Fill the older COV-backed boundary measure input without an AE field. -/
def toBoundaryMeasureFromTargetCOVInput :
    BoundaryMeasureFromTargetCOVInput (α := α) D μ where
  boundaryIntegrand := B.pieces.boundaryIntegrand
  boundaryPieceSet := B.pieces.boundaryPieceSet
  boundaryPieceIntegrand := B.pieces.boundaryPieceIntegrand
  boundaryMeasureIntegral := B.boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_integral :=
    B.boundaryMeasureIntegral_eq_integral
  boundaryPieceSet_measurable := B.boundaryPieceSet_measurable
  boundaryPieceCompact := B.boundaryPieceCompact
  sourceProjectLocal_eq_setIntegral :=
    B.sourceProjectLocal_eq_setIntegral
  boundaryIntegrand_ae_eq_indicatorSum :=
    B.boundaryIntegrand_ae_eq_indicatorSum
  globalBoundaryIntegral := B.globalBoundaryIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    B.globalBoundaryIntegral_eq_boundaryMeasureIntegral

@[simp]
theorem toBoundaryMeasureFromTargetCOVInput_boundaryIntegrand :
    B.toBoundaryMeasureFromTargetCOVInput.boundaryIntegrand =
      B.pieces.boundaryIntegrand := by
  rfl

@[simp]
theorem toBoundaryMeasureFromTargetCOVInput_boundaryPieceSet :
    B.toBoundaryMeasureFromTargetCOVInput.boundaryPieceSet =
      B.pieces.boundaryPieceSet := by
  rfl

@[simp]
theorem toBoundaryMeasureFromTargetCOVInput_boundaryPieceIntegrand :
    B.toBoundaryMeasureFromTargetCOVInput.boundaryPieceIntegrand =
      B.pieces.boundaryPieceIntegrand := by
  rfl

@[simp]
theorem toBoundaryMeasureFromTargetCOVInput_boundaryMeasureIntegral :
    B.toBoundaryMeasureFromTargetCOVInput.boundaryMeasureIntegral =
      B.boundaryMeasureIntegral := by
  rfl

@[simp]
theorem toBoundaryMeasureFromTargetCOVInput_globalBoundaryIntegral :
    B.toBoundaryMeasureFromTargetCOVInput.globalBoundaryIntegral =
      B.globalBoundaryIntegral := by
  rfl

/--
Canonical compact-support target boundary input produced from support-finite
piece sums plus the oriented COV source set-integral theorem.
-/
def toCanonicalBoundaryTargetCompactSupportInput
    [IsManifold I 1 M] :
    CanonicalBoundaryTargetCompactSupportInput (α := α) D μ :=
  B.toBoundaryMeasureFromTargetCOVInput
    |>.toCanonicalBoundaryTargetCompactSupportInput

@[simp]
theorem toCanonicalBoundaryTargetCompactSupportInput_boundaryMeasureIntegral
    [IsManifold I 1 M] :
    B.toCanonicalBoundaryTargetCompactSupportInput.boundaryMeasureIntegral =
      B.boundaryMeasureIntegral := by
  rfl

@[simp]
theorem toCanonicalBoundaryTargetCompactSupportInput_globalBoundaryIntegral
    [IsManifold I 1 M] :
    B.toCanonicalBoundaryTargetCompactSupportInput.globalBoundaryIntegral =
      B.globalBoundaryIntegral := by
  rfl

end BoundaryPieceSupportFiniteSumTargetCOVInput

end TargetCOVRoute

end BoundaryPieceSupportFiniteSum

end Stokes

end
