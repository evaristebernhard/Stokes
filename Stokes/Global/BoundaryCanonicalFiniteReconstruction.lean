import Stokes.Global.BoundaryPieceSupportFiniteSum
import Stokes.Global.ProjectLocalBoundaryMeasureConstructor

/-!
# Boundary canonical finite reconstruction glue

This module connects the project-local/canonical lower-zero-face boundary
measure route to the support-finite-sum boundary route.

The raw lower-zero-face scalar representative is not algebraically supported in
the face set by definition.  The finite reconstruction route therefore uses
the indicator-localized representative as the support-finite piece.  Existing
project-local measure data supplies the a.e. reconstruction by the raw
indicator sum; this file repackages that reconstruction as a definitional
finite piece sum and carries the source set-integral equality through the
indicator localization.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryCanonicalFiniteReconstruction

universe u w c p a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {Piece : Type p}
variable {α : Type a} [MeasurableSpace α]
variable {μ : Measure α}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/-- On a measurable set, replacing a raw piece by its own indicator-localized
version does not change the set integral over that set. -/
theorem setIntegral_boundaryMeasurePieceIndicator_eq
    (boundaryPieceSet : Chart → Piece → Set α)
    (rawBoundaryPieceIntegrand : Chart → Piece → α → Real)
    {x : Chart} {q : Piece}
    (hset : MeasurableSet (boundaryPieceSet x q)) :
    (∫ y in boundaryPieceSet x q,
        boundaryMeasurePieceIndicator boundaryPieceSet
          rawBoundaryPieceIntegrand x q y ∂μ) =
      ∫ y in boundaryPieceSet x q,
        rawBoundaryPieceIntegrand x q y ∂μ := by
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem hset] with y hy
  simp [boundaryMeasurePieceIndicator, hy]

namespace ProjectLocalBoundaryMeasureData

variable {D : ProjectLocalGlobalStokesData I ω Chart Piece}
variable (B : ProjectLocalBoundaryMeasureData (α := α) D μ)

/-- Project-local boundary measure data as support-finite selected pieces.

The pieces are the indicator-localized versions of the recorded raw
project-local piece integrands, so support containment is automatic and the
global boundary integrand is the selected finite piece sum by definition. -/
def toBoundaryPieceSupportFiniteSumInput :
    BoundaryPieceSupportFiniteSumInput (α := α)
      D.boundaryMeasurePartitionData :=
  BoundaryPieceSupportFiniteSumInput.ofIndicatorPieces
    (α := α) D.boundaryMeasurePartitionData
    B.boundaryPieceSet B.boundaryPieceIntegrand

@[simp]
theorem toBoundaryPieceSupportFiniteSumInput_boundaryPieceSet :
    B.toBoundaryPieceSupportFiniteSumInput.boundaryPieceSet =
      B.boundaryPieceSet := by
  rfl

@[simp]
theorem toBoundaryPieceSupportFiniteSumInput_boundaryPieceIntegrand :
    B.toBoundaryPieceSupportFiniteSumInput.boundaryPieceIntegrand =
      boundaryMeasurePieceIndicator B.boundaryPieceSet
        B.boundaryPieceIntegrand := by
  rfl

@[simp]
theorem toBoundaryPieceSupportFiniteSumInput_boundaryIntegrand :
    B.toBoundaryPieceSupportFiniteSumInput.boundaryIntegrand =
      boundaryMeasureIndicatorSum D.activeCharts D.localPieces
        B.boundaryPieceSet B.boundaryPieceIntegrand := by
  rfl

/-- The original boundary integrand is a.e. the support-finite canonical sum. -/
theorem boundaryIntegrand_ae_eq_supportFiniteSumBoundaryIntegrand :
    B.boundaryIntegrand =ᵐ[μ]
      B.toBoundaryPieceSupportFiniteSumInput.boundaryIntegrand := by
  simpa [toBoundaryPieceSupportFiniteSumInput] using
    B.boundaryIntegrand_ae_eq_indicatorSum

/-- The measure integral can be rewritten using the support-finite canonical
finite-sum integrand. -/
theorem boundaryMeasureIntegral_eq_supportFiniteSumIntegral :
    B.boundaryMeasureIntegral =
      ∫ y, B.toBoundaryPieceSupportFiniteSumInput.boundaryIntegrand y ∂μ := by
  calc
    B.boundaryMeasureIntegral =
        ∫ y, B.boundaryIntegrand y ∂μ :=
      B.boundaryMeasureIntegral_eq_integral
    _ =
        ∫ y, B.toBoundaryPieceSupportFiniteSumInput.boundaryIntegrand y ∂μ :=
      integral_congr_ae
        B.boundaryIntegrand_ae_eq_supportFiniteSumBoundaryIntegrand

/-- The project-local source set-integral equality survives the
indicator-localization used by the support-finite route. -/
theorem projectLocalBoundaryIntegral_eq_indicatorSetIntegral
    {x : Chart} (hx : x ∈ D.activeCharts)
    {q : Piece} (hq : q ∈ D.localPieces x) :
    projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
        (D.lowerCorner x q) (D.upperCorner x q) =
      ∫ y in B.toBoundaryPieceSupportFiniteSumInput.boundaryPieceSet x q,
        B.toBoundaryPieceSupportFiniteSumInput.boundaryPieceIntegrand x q y ∂μ := by
  calc
    projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
        (D.lowerCorner x q) (D.upperCorner x q) =
        ∫ y in B.boundaryPieceSet x q,
          B.boundaryPieceIntegrand x q y ∂μ :=
      B.projectLocalBoundaryIntegral_eq_setIntegral x hx q hq
    _ =
        ∫ y in B.toBoundaryPieceSupportFiniteSumInput.boundaryPieceSet x q,
          B.toBoundaryPieceSupportFiniteSumInput.boundaryPieceIntegrand x q y ∂μ := by
      simpa [toBoundaryPieceSupportFiniteSumInput] using
        (setIntegral_boundaryMeasurePieceIndicator_eq
          (μ := μ) B.boundaryPieceSet B.boundaryPieceIntegrand
          (x := x) (q := q)
          (B.boundaryPieceSet_measurable x hx q hq)).symm

/-- The selected boundary partition term is the indicator-localized set
integral used by the support-finite pieces. -/
theorem boundaryPartitionTerm_eq_indicatorSetIntegral
    {x : Chart} (hx : x ∈ D.activeCharts)
    {q : Piece} (hq : q ∈ D.localPieces x) :
    D.boundaryPartitionTerm x q =
      ∫ y in B.toBoundaryPieceSupportFiniteSumInput.boundaryPieceSet x q,
        B.toBoundaryPieceSupportFiniteSumInput.boundaryPieceIntegrand x q y ∂μ := by
  calc
    D.boundaryPartitionTerm x q =
        projectLocalBoundaryIntegral I (D.sourceChart x q)
          (D.targetChart x q) ω (D.lowerCorner x q)
          (D.upperCorner x q) :=
      B.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral x hx q hq
    _ =
        ∫ y in B.toBoundaryPieceSupportFiniteSumInput.boundaryPieceSet x q,
          B.toBoundaryPieceSupportFiniteSumInput.boundaryPieceIntegrand x q y ∂μ :=
      B.projectLocalBoundaryIntegral_eq_indicatorSetIntegral hx hq

end ProjectLocalBoundaryMeasureData

namespace ProjectLocalBoundaryMeasureConstructorInput

variable {D : ProjectLocalGlobalStokesData I ω Chart Piece}
variable (C : ProjectLocalBoundaryMeasureConstructorInput D)

/-- Canonical lower-zero-face constructor data as support-finite selected
pieces.  The raw lower-zero-face representative is indicator-localized before
entering the support-finite route. -/
def toBoundaryPieceSupportFiniteSumInput :
    BoundaryPieceSupportFiniteSumInput
      (α := Fin n → Real) D.boundaryMeasurePartitionData :=
  C.toProjectLocalBoundaryMeasureData.toBoundaryPieceSupportFiniteSumInput

@[simp]
theorem toBoundaryPieceSupportFiniteSumInput_boundaryPieceSet :
    C.toBoundaryPieceSupportFiniteSumInput.boundaryPieceSet =
      D.projectLocalBoundaryPieceSet := by
  rfl

@[simp]
theorem toBoundaryPieceSupportFiniteSumInput_boundaryPieceIntegrand :
    C.toBoundaryPieceSupportFiniteSumInput.boundaryPieceIntegrand =
      boundaryMeasurePieceIndicator D.projectLocalBoundaryPieceSet
        D.projectLocalBoundaryPieceIntegrand := by
  rfl

@[simp]
theorem toBoundaryPieceSupportFiniteSumInput_boundaryIntegrand :
    C.toBoundaryPieceSupportFiniteSumInput.boundaryIntegrand =
      boundaryMeasureIndicatorSum D.activeCharts D.localPieces
        D.projectLocalBoundaryPieceSet
        D.projectLocalBoundaryPieceIntegrand := by
  rfl

/-- The constructor's original boundary integrand is a.e. the canonical
support-finite lower-zero-face sum. -/
theorem boundaryIntegrand_ae_eq_supportFiniteSumBoundaryIntegrand :
    C.boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
      C.toBoundaryPieceSupportFiniteSumInput.boundaryIntegrand := by
  simpa [toBoundaryPieceSupportFiniteSumInput] using
    C.toProjectLocalBoundaryMeasureData
      |>.boundaryIntegrand_ae_eq_supportFiniteSumBoundaryIntegrand

/-- The constructor's boundary measure integral is the integral of the
support-finite canonical lower-zero-face finite sum. -/
theorem boundaryMeasureIntegral_eq_supportFiniteSumIntegral :
    C.boundaryMeasureIntegral =
      ∫ y, C.toBoundaryPieceSupportFiniteSumInput.boundaryIntegrand y
        ∂(volume : Measure (Fin n → Real)) := by
  simpa [toBoundaryPieceSupportFiniteSumInput] using
    C.toProjectLocalBoundaryMeasureData
      |>.boundaryMeasureIntegral_eq_supportFiniteSumIntegral

/-- The canonical project-local set-integral equality in the indicator-localized
support-finite shape. -/
theorem projectLocalBoundaryIntegral_eq_indicatorSetIntegral
    {x : Chart} (hx : x ∈ D.activeCharts)
    {q : Piece} (hq : q ∈ D.localPieces x) :
    projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
        (D.lowerCorner x q) (D.upperCorner x q) =
      ∫ y in C.toBoundaryPieceSupportFiniteSumInput.boundaryPieceSet x q,
        C.toBoundaryPieceSupportFiniteSumInput.boundaryPieceIntegrand x q y
          ∂(volume : Measure (Fin n → Real)) := by
  simpa [toBoundaryPieceSupportFiniteSumInput] using
    C.toProjectLocalBoundaryMeasureData
      |>.projectLocalBoundaryIntegral_eq_indicatorSetIntegral hx hq

/-- The selected partition term in the indicator-localized support-finite
shape. -/
theorem boundaryPartitionTerm_eq_indicatorSetIntegral
    {x : Chart} (hx : x ∈ D.activeCharts)
    {q : Piece} (hq : q ∈ D.localPieces x) :
    D.boundaryPartitionTerm x q =
      ∫ y in C.toBoundaryPieceSupportFiniteSumInput.boundaryPieceSet x q,
        C.toBoundaryPieceSupportFiniteSumInput.boundaryPieceIntegrand x q y
          ∂(volume : Measure (Fin n → Real)) := by
  simpa [toBoundaryPieceSupportFiniteSumInput] using
    C.toProjectLocalBoundaryMeasureData
      |>.boundaryPartitionTerm_eq_indicatorSetIntegral hx hq

end ProjectLocalBoundaryMeasureConstructorInput

section TargetCOV

variable [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
variable [IsFiniteMeasureOnCompacts μ]
variable {BoundaryPiece : Type p}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
variable
    {T :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}
variable {P : ProjectLocalGlobalStokesData I omega M BoundaryPiece}

namespace ProjectLocalBoundaryMeasureData

variable (B : ProjectLocalBoundaryMeasureData (α := α) P μ)

/-- The same indicator-localized project-local pieces, re-indexed by the
selected target-image boundary partition. -/
def toSelectedBoundaryPieceSupportFiniteSumInput
    (_A : BoundarySourceProjectLocalAlignment T P) :
    BoundaryPieceSupportFiniteSumInput (α := α)
      T.toSelectedBoundaryMeasurePartitionData :=
  BoundaryPieceSupportFiniteSumInput.ofIndicatorPieces
    (α := α) T.toSelectedBoundaryMeasurePartitionData
    B.boundaryPieceSet B.boundaryPieceIntegrand

@[simp]
theorem toSelectedBoundaryPieceSupportFiniteSumInput_boundaryPieceSet
    (A : BoundarySourceProjectLocalAlignment T P) :
    (B.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryPieceSet =
      B.boundaryPieceSet := by
  rfl

@[simp]
theorem toSelectedBoundaryPieceSupportFiniteSumInput_boundaryPieceIntegrand
    (A : BoundarySourceProjectLocalAlignment T P) :
    (B.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryPieceIntegrand =
      boundaryMeasurePieceIndicator B.boundaryPieceSet
        B.boundaryPieceIntegrand := by
  rfl

@[simp]
theorem toSelectedBoundaryPieceSupportFiniteSumInput_boundaryIntegrand
    (A : BoundarySourceProjectLocalAlignment T P) :
    (B.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryIntegrand =
      boundaryMeasureIndicatorSum selectedPartition.active
        T.targetImages.boundaryPieces B.boundaryPieceSet
        B.boundaryPieceIntegrand := by
  rfl

/-- The original project-local boundary integrand is a.e. the selected target
support-finite canonical sum. -/
theorem boundaryIntegrand_ae_eq_selectedSupportFiniteSumBoundaryIntegrand
    (A : BoundarySourceProjectLocalAlignment T P) :
    B.boundaryIntegrand =ᵐ[μ]
      (B.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryIntegrand := by
  have hpieces : P.localPieces = T.assembly.boundaryPieces := by
    funext x
    simpa using (A.localPieces_eq x)
  simpa [toSelectedBoundaryPieceSupportFiniteSumInput, A.activeCharts_eq,
    hpieces, boundaryMeasureIndicatorSum] using
    B.boundaryIntegrand_ae_eq_indicatorSum

/-- The measure integral can be rewritten using the selected target
support-finite canonical finite-sum integrand. -/
theorem boundaryMeasureIntegral_eq_selectedSupportFiniteSumIntegral
    (A : BoundarySourceProjectLocalAlignment T P) :
    B.boundaryMeasureIntegral =
      ∫ y, (B.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryIntegrand y
        ∂μ := by
  calc
    B.boundaryMeasureIntegral =
        ∫ y, B.boundaryIntegrand y ∂μ :=
      B.boundaryMeasureIntegral_eq_integral
    _ =
        ∫ y, (B.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryIntegrand y
          ∂μ :=
      integral_congr_ae
        (B.boundaryIntegrand_ae_eq_selectedSupportFiniteSumBoundaryIntegrand A)

/-- Aligned project-local boundary measure data as a target-COV
support-finite-sum input.

The only extra analytic input, beyond `ProjectLocalBoundaryMeasureData`, is
compact-support integrability for the indicator-localized support-finite
pieces. -/
def toBoundaryPieceSupportFiniteSumTargetCOVInput
    (A : BoundarySourceProjectLocalAlignment T P)
    (boundaryPieceCompact :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ T.targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData
            ((B.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryPieceIntegrand
              x q)) :
    BoundaryPieceSupportFiniteSumTargetCOVInput (α := α) T μ where
  pieces := B.toSelectedBoundaryPieceSupportFiniteSumInput A
  boundaryMeasureIntegral := B.boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_integral :=
    B.boundaryMeasureIntegral_eq_selectedSupportFiniteSumIntegral A
  boundaryPieceSet_measurable := by
    intro x hx q hq
    exact B.boundaryPieceSet_measurable x (A.mem_active hx) q
      (A.mem_localPiece hq)
  boundaryPieceCompact := boundaryPieceCompact
  sourceProjectLocal_eq_setIntegral := by
    intro x hx q hq
    calc
      projectLocalBoundaryIntegral I
          (T.targetImages.sourceChart x q)
          (T.targetImages.boundarySourceChart x q) omega
          (T.targetImages.sourceLowerCorner x q)
          (T.targetImages.sourceUpperCorner x q) =
          ∫ y in B.boundaryPieceSet x q,
            B.boundaryPieceIntegrand x q y ∂μ :=
        A.projectLocalBoundaryMeasure_sourceProjectLocal_eq_setIntegral
          B hx hq
      _ =
          ∫ y in (B.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryPieceSet x q,
            (B.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryPieceIntegrand
              x q y ∂μ := by
        simpa [ProjectLocalBoundaryMeasureData.toSelectedBoundaryPieceSupportFiniteSumInput] using
          (setIntegral_boundaryMeasurePieceIndicator_eq
            (μ := μ) B.boundaryPieceSet B.boundaryPieceIntegrand
            (x := x) (q := q)
            (B.boundaryPieceSet_measurable x (A.mem_active hx) q
              (A.mem_localPiece hq))).symm
  globalBoundaryIntegral := P.globalBoundaryIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    B.globalBoundaryIntegral_eq_boundaryMeasureIntegral

@[simp]
theorem toBoundaryPieceSupportFiniteSumTargetCOVInput_pieces
    (A : BoundarySourceProjectLocalAlignment T P)
    (boundaryPieceCompact :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ T.targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData
            ((B.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryPieceIntegrand
              x q)) :
    (B.toBoundaryPieceSupportFiniteSumTargetCOVInput A
      boundaryPieceCompact).pieces =
      B.toSelectedBoundaryPieceSupportFiniteSumInput A := by
  rfl

@[simp]
theorem toBoundaryPieceSupportFiniteSumTargetCOVInput_boundaryMeasureIntegral
    (A : BoundarySourceProjectLocalAlignment T P)
    (boundaryPieceCompact :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ T.targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData
            ((B.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryPieceIntegrand
              x q)) :
    (B.toBoundaryPieceSupportFiniteSumTargetCOVInput A
      boundaryPieceCompact).boundaryMeasureIntegral =
      B.boundaryMeasureIntegral := by
  rfl

@[simp]
theorem toBoundaryPieceSupportFiniteSumTargetCOVInput_globalBoundaryIntegral
    (A : BoundarySourceProjectLocalAlignment T P)
    (boundaryPieceCompact :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ T.targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData
            ((B.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryPieceIntegrand
              x q)) :
    (B.toBoundaryPieceSupportFiniteSumTargetCOVInput A
      boundaryPieceCompact).globalBoundaryIntegral =
      P.globalBoundaryIntegral := by
  rfl

end ProjectLocalBoundaryMeasureData

namespace ProjectLocalBoundaryMeasureConstructorInput

variable (C : ProjectLocalBoundaryMeasureConstructorInput P)

/-- Canonical lower-zero-face pieces re-indexed by the selected target-image
boundary partition. -/
def toSelectedBoundaryPieceSupportFiniteSumInput
    (A : BoundarySourceProjectLocalAlignment T P) :
    BoundaryPieceSupportFiniteSumInput
      (α := Fin n → Real) T.toSelectedBoundaryMeasurePartitionData :=
  C.toProjectLocalBoundaryMeasureData
    |>.toSelectedBoundaryPieceSupportFiniteSumInput A

@[simp]
theorem toSelectedBoundaryPieceSupportFiniteSumInput_boundaryPieceSet
    (A : BoundarySourceProjectLocalAlignment T P) :
    (C.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryPieceSet =
      P.projectLocalBoundaryPieceSet := by
  rfl

@[simp]
theorem toSelectedBoundaryPieceSupportFiniteSumInput_boundaryPieceIntegrand
    (A : BoundarySourceProjectLocalAlignment T P) :
    (C.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryPieceIntegrand =
      boundaryMeasurePieceIndicator P.projectLocalBoundaryPieceSet
        P.projectLocalBoundaryPieceIntegrand := by
  rfl

/-- Canonical lower-zero-face constructor data as a target-COV
support-finite-sum input, assuming compact-support data for the
indicator-localized canonical pieces. -/
def toBoundaryPieceSupportFiniteSumTargetCOVInput
    (A : BoundarySourceProjectLocalAlignment T P)
    (boundaryPieceCompact :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ T.targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData
            ((C.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryPieceIntegrand
              x q)) :
    BoundaryPieceSupportFiniteSumTargetCOVInput
      (α := Fin n → Real) T (volume : Measure (Fin n → Real)) :=
  C.toProjectLocalBoundaryMeasureData
    |>.toBoundaryPieceSupportFiniteSumTargetCOVInput A boundaryPieceCompact

@[simp]
theorem toBoundaryPieceSupportFiniteSumTargetCOVInput_pieces
    (A : BoundarySourceProjectLocalAlignment T P)
    (boundaryPieceCompact :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ T.targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData
            ((C.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryPieceIntegrand
              x q)) :
    (C.toBoundaryPieceSupportFiniteSumTargetCOVInput A
      boundaryPieceCompact).pieces =
      C.toSelectedBoundaryPieceSupportFiniteSumInput A := by
  rfl

@[simp]
theorem toBoundaryPieceSupportFiniteSumTargetCOVInput_boundaryMeasureIntegral
    (A : BoundarySourceProjectLocalAlignment T P)
    (boundaryPieceCompact :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ T.targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData
            ((C.toSelectedBoundaryPieceSupportFiniteSumInput A).boundaryPieceIntegrand
              x q)) :
    (C.toBoundaryPieceSupportFiniteSumTargetCOVInput A
      boundaryPieceCompact).boundaryMeasureIntegral =
      C.boundaryMeasureIntegral := by
  rfl

end ProjectLocalBoundaryMeasureConstructorInput

/-- Minimal package needed to turn aligned project-local boundary measure data
into the support-finite target-COV boundary input. -/
structure BoundaryCanonicalFiniteReconstructionInput
    (T :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (P : ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (μ : Measure α) where
  /-- Project-local boundary measure data, including the raw indicator-sum
  reconstruction and source set-integral identities. -/
  projectLocal : ProjectLocalBoundaryMeasureData (α := α) P μ
  /-- Coordinate bookkeeping aligning the project-local package with the
  selected target-image source data. -/
  sourceAlignment : BoundarySourceProjectLocalAlignment T P
  /-- Compact-support data for the indicator-localized support-finite pieces. -/
  boundaryPieceCompact :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ T.targetImages.boundaryPieces x →
        CompactSupportIntegrabilityData
          ((projectLocal.toSelectedBoundaryPieceSupportFiniteSumInput
            sourceAlignment).boundaryPieceIntegrand x q)

namespace BoundaryCanonicalFiniteReconstructionInput

variable (R : BoundaryCanonicalFiniteReconstructionInput T P μ)

/-- The support-finite selected pieces obtained from the project-local package. -/
def pieces :
    BoundaryPieceSupportFiniteSumInput (α := α)
      T.toSelectedBoundaryMeasurePartitionData :=
  R.projectLocal.toSelectedBoundaryPieceSupportFiniteSumInput R.sourceAlignment

@[simp]
theorem pieces_boundaryPieceSet :
    R.pieces.boundaryPieceSet =
      R.projectLocal.boundaryPieceSet := by
  rfl

@[simp]
theorem pieces_boundaryPieceIntegrand :
    R.pieces.boundaryPieceIntegrand =
      boundaryMeasurePieceIndicator R.projectLocal.boundaryPieceSet
        R.projectLocal.boundaryPieceIntegrand := by
  rfl

/-- The assembled target-COV input in the support-finite-sum shape. -/
def toBoundaryPieceSupportFiniteSumTargetCOVInput :
    BoundaryPieceSupportFiniteSumTargetCOVInput (α := α) T μ :=
  R.projectLocal.toBoundaryPieceSupportFiniteSumTargetCOVInput
    R.sourceAlignment R.boundaryPieceCompact

@[simp]
theorem toBoundaryPieceSupportFiniteSumTargetCOVInput_pieces :
    R.toBoundaryPieceSupportFiniteSumTargetCOVInput.pieces =
      R.pieces := by
  rfl

@[simp]
theorem toBoundaryPieceSupportFiniteSumTargetCOVInput_boundaryMeasureIntegral :
    R.toBoundaryPieceSupportFiniteSumTargetCOVInput.boundaryMeasureIntegral =
      R.projectLocal.boundaryMeasureIntegral := by
  rfl

@[simp]
theorem toBoundaryPieceSupportFiniteSumTargetCOVInput_globalBoundaryIntegral :
    R.toBoundaryPieceSupportFiniteSumTargetCOVInput.globalBoundaryIntegral =
      P.globalBoundaryIntegral := by
  rfl

/-- The older COV-backed boundary-measure input obtained from the minimal
canonical finite reconstruction package. -/
def toBoundaryMeasureFromTargetCOVInput :
    BoundaryMeasureFromTargetCOVInput (α := α) T μ :=
  R.toBoundaryPieceSupportFiniteSumTargetCOVInput
    |>.toBoundaryMeasureFromTargetCOVInput

/-- The compact-support target route obtained from the minimal package. -/
def toCanonicalBoundaryTargetCompactSupportInput
    [IsManifold I 1 M] :
    CanonicalBoundaryTargetCompactSupportInput (α := α) T μ :=
  R.toBoundaryPieceSupportFiniteSumTargetCOVInput
    |>.toCanonicalBoundaryTargetCompactSupportInput

@[simp]
theorem toCanonicalBoundaryTargetCompactSupportInput_boundaryMeasureIntegral
    [IsManifold I 1 M] :
    R.toCanonicalBoundaryTargetCompactSupportInput.boundaryMeasureIntegral =
      R.projectLocal.boundaryMeasureIntegral := by
  rfl

/-- The downstream finite selected-boundary-piece sum supplied by the canonical
target compact-support route. -/
theorem boundaryMeasureIntegral_eq_selectedBoundaryPieceSum
    [IsManifold I 1 M] :
    R.projectLocal.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        T.targetImages.boundaryPieces T.assembly.boundaryPartitionTerm := by
  simpa using
    R.toCanonicalBoundaryTargetCompactSupportInput
      |>.canonicalBoundaryMeasureIntegral_eq_partitionSum

end BoundaryCanonicalFiniteReconstructionInput

end TargetCOV

end BoundaryCanonicalFiniteReconstruction

end Stokes

end
