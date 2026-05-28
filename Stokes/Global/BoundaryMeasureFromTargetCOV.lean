import Stokes.Global.TargetOrientationSelectedBoxAlignment
import Stokes.Global.BoundaryTargetMeasureBuilderGlue
import Stokes.Global.BoundaryMeasurePartitionLocalizationWrappers

/-!
# Boundary measure fields from target-image COV

This file is a thin bridge from the target-image oriented COV package to the
boundary compact-measure input used by the canonical compact-support route.

The genuine measure theorem is not hidden here.  The new input record asks for
the source project-local boundary integral to be the corresponding set integral;
the oriented target-image COV and the existing target assembly wrappers then
transport that equality to the selected boundary partition term.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryMeasureFromTargetCOV

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

namespace M8TargetImageInput

variable
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)

/--
For one target-image piece, the oriented source selected-box COV identifies the
source project-local boundary integral with the transported target boundary
term carried by the target-image family.
-/
theorem sourceSelectedBox_projectLocal_eq_targetBoundaryTerm
    [IsManifold I 1 M]
    {x : M} (hx : x ∈ D.targetImages.activeCharts)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    projectLocalBoundaryIntegral I
        (D.targetImages.sourceChart x q)
        (D.targetImages.boundarySourceChart x q) omega
        (D.targetImages.sourceLowerCorner x q)
        (D.targetImages.sourceUpperCorner x q) =
      BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages x q := by
  calc
    projectLocalBoundaryIntegral I
        (D.targetImages.sourceChart x q)
        (D.targetImages.boundarySourceChart x q) omega
        (D.targetImages.sourceLowerCorner x q)
        (D.targetImages.sourceUpperCorner x q) =
        outwardFirstBoundaryInChartIntegral I
          (D.targetImages.boundarySourceChart x q) omega
          (D.targetImages.targetLowerCorner x q)
          (D.targetImages.targetUpperCorner x q) := by
          simpa [projectLocalBoundaryIntegral] using
            outwardFirstBoundaryChartIntegral_eq_inChart_of_orientedChangeOfVariables
              (D.targetImages.sourceChart x q)
              (D.targetImages.boundarySourceChart x q) omega
              (D.targetImages.sourceLowerCorner x q)
              (D.targetImages.sourceUpperCorner x q)
              (D.targetImages.targetLowerCorner x q)
              (D.targetImages.targetUpperCorner x q)
              (D.sourceSelectedBox_orientedChangeOfVariables hx hq)
    _ = BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages x q := by
          have htarget :
              outwardFirstBoundaryChartIntegral I
                  (D.targetImages.boundarySourceChart x q)
                  (D.targetImages.boundaryTargetChart x q) omega
                  (D.targetImages.targetLowerCorner x q)
                  (D.targetImages.targetUpperCorner x q) =
                outwardFirstBoundaryInChartIntegral I
                  (D.targetImages.boundarySourceChart x q) omega
                  (D.targetImages.targetLowerCorner x q)
                  (D.targetImages.targetUpperCorner x q) :=
            outwardFirstBoundaryChartIntegral_eq_inChart_of_boundaryFace_subset_overlap
              (D.targetImages.boundarySourceChart x q)
              (D.targetImages.boundaryTargetChart x q) omega
              (D.targetImages.targetLowerCorner x q)
              (D.targetImages.targetUpperCorner x q)
              (D.targetImages.targetSelectedBox x hx q hq).boundaryFace_subset_overlap
          simpa [BoundaryPieceFamilyInput.boundaryBoundaryTerm,
            projectLocalBoundaryIntegral] using htarget.symm

/--
The same COV equality, followed by the existing target assembly wrapper, gives
the selected boundary partition term.
-/
theorem sourceSelectedBox_projectLocal_eq_boundaryPartitionTerm
    [IsManifold I 1 M]
    {x : M} (hx : x ∈ D.targetImages.activeCharts)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    projectLocalBoundaryIntegral I
        (D.targetImages.sourceChart x q)
        (D.targetImages.boundarySourceChart x q) omega
        (D.targetImages.sourceLowerCorner x q)
        (D.targetImages.sourceUpperCorner x q) =
      D.assembly.boundaryPartitionTerm x q :=
  (D.sourceSelectedBox_projectLocal_eq_targetBoundaryTerm hx hq).trans
    (D.targetBoundaryTerm_eq_assemblyPartition x hx q hq)

/-- Selected-active version of the source-COV-to-partition equality. -/
theorem sourceSelectedBox_projectLocal_eq_boundaryPartitionTerm_of_selected
    [IsManifold I 1 M]
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    projectLocalBoundaryIntegral I
        (D.targetImages.sourceChart x q)
        (D.targetImages.boundarySourceChart x q) omega
        (D.targetImages.sourceLowerCorner x q)
        (D.targetImages.sourceUpperCorner x q) =
      D.assembly.boundaryPartitionTerm x q := by
  have hx' : x ∈ D.targetImages.activeCharts := by
    simpa [D.targetImages_active] using hx
  exact D.sourceSelectedBox_projectLocal_eq_boundaryPartitionTerm hx' hq

/--
If the source project-local boundary integral has already been identified with
a genuine set integral, the target-image oriented COV transports that identity
to the selected boundary partition term.
-/
theorem boundaryPartitionTerm_eq_setIntegral_of_orientedCOV
    [IsManifold I 1 M]
    (boundaryPieceSet : M → BoundaryPiece → Set α)
    (boundaryPieceIntegrand : M → BoundaryPiece → α → Real)
    (hsourceSetIntegral :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.targetImages.boundaryPieces x →
          projectLocalBoundaryIntegral I
              (D.targetImages.sourceChart x q)
              (D.targetImages.boundarySourceChart x q) omega
              (D.targetImages.sourceLowerCorner x q)
              (D.targetImages.sourceUpperCorner x q) =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂μ)
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    D.assembly.boundaryPartitionTerm x q =
      ∫ y in boundaryPieceSet x q,
        boundaryPieceIntegrand x q y ∂μ :=
  (D.sourceSelectedBox_projectLocal_eq_boundaryPartitionTerm_of_selected hx hq).symm.trans
    (hsourceSetIntegral x hx q hq)

end M8TargetImageInput

/--
Minimal boundary-measure input whose set-integral term is obtained from the
source target-image COV route.

The key exposed analytic hypothesis is `sourceProjectLocal_eq_setIntegral`.
All global measure, compact-support, and a.e. reconstruction facts remain
ordinary fields; this record only lets the already-proved target COV transport
the source set integral to the selected boundary partition term.
-/
structure BoundaryMeasureFromTargetCOVInput
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (μ : Measure α) where
  /-- Boundary-side integrand represented by the measure integral. -/
  boundaryIntegrand : α → Real
  /-- Selected boundary-piece support set. -/
  boundaryPieceSet : M → BoundaryPiece → Set α
  /-- Selected boundary-piece scalar integrand. -/
  boundaryPieceIntegrand : M → BoundaryPiece → α → Real
  /-- Genuine boundary measure integral. -/
  boundaryMeasureIntegral : Real
  /-- The boundary measure integral is the integral of `boundaryIntegrand`. -/
  boundaryMeasureIntegral_eq_integral :
    boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ
  /-- Active boundary support sets are measurable. -/
  boundaryPieceSet_measurable :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ D.targetImages.boundaryPieces x →
        MeasurableSet (boundaryPieceSet x q)
  /-- Active boundary-piece integrands have compact-support integrability. -/
  boundaryPieceCompact :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ D.targetImages.boundaryPieces x →
        CompactSupportIntegrabilityData (boundaryPieceIntegrand x q)
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
          ∫ y in boundaryPieceSet x q,
            boundaryPieceIntegrand x q y ∂μ
  /-- AE reconstruction by selected boundary indicator pieces. -/
  boundaryIntegrand_ae_eq_indicatorSum :
    boundaryIntegrand =ᵐ[μ]
      boundaryMeasureIndicatorSum selectedPartition.active
        D.targetImages.boundaryPieces boundaryPieceSet boundaryPieceIntegrand
  /-- The represented global boundary integral. -/
  globalBoundaryIntegral : Real
  /-- The represented global boundary integral is the measure integral. -/
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :
    globalBoundaryIntegral = boundaryMeasureIntegral

namespace BoundaryMeasureFromTargetCOVInput

variable
    {D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}
    (B : BoundaryMeasureFromTargetCOVInput (α := α) D μ)

/-- The transported boundary partition term is the selected set integral. -/
theorem boundaryPartitionTerm_eq_setIntegral
    [IsManifold I 1 M]
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    D.assembly.boundaryPartitionTerm x q =
      ∫ y in B.boundaryPieceSet x q,
        B.boundaryPieceIntegrand x q y ∂μ :=
  D.boundaryPartitionTerm_eq_setIntegral_of_orientedCOV
    (μ := μ) B.boundaryPieceSet B.boundaryPieceIntegrand
    B.sourceProjectLocal_eq_setIntegral hx hq

/--
The COV-backed input fills the canonical compact-support boundary target route.
This is the field consumed downstream by `BoundaryTargetMeasureBuilderGlue`.
-/
def toCanonicalBoundaryTargetCompactSupportInput
    [IsManifold I 1 M] :
    CanonicalBoundaryTargetCompactSupportInput (α := α) D μ where
  boundaryIntegrand := B.boundaryIntegrand
  boundaryPieceSet := B.boundaryPieceSet
  boundaryPieceIntegrand := B.boundaryPieceIntegrand
  boundaryMeasureIntegral := B.boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_integral :=
    B.boundaryMeasureIntegral_eq_integral
  boundaryPieceSet_measurable := B.boundaryPieceSet_measurable
  boundaryPieceCompact := B.boundaryPieceCompact
  boundaryPartitionTerm_eq_setIntegral := by
    intro x hx q hq
    exact B.boundaryPartitionTerm_eq_setIntegral hx hq
  boundaryIntegrand_ae_eq_indicatorSum :=
    B.boundaryIntegrand_ae_eq_indicatorSum
  globalBoundaryIntegral := B.globalBoundaryIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    B.globalBoundaryIntegral_eq_boundaryMeasureIntegral

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

/--
Canonical compact fields produced from the COV-backed input expose the same
selected boundary set-integral equality.
-/
theorem canonical_selectedBoundaryPartitionTerm_eq_setIntegral
    [IsManifold I 1 M]
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    D.assembly.boundaryPartitionTerm x q =
      ∫ y in B.boundaryPieceSet x q,
        B.boundaryPieceIntegrand x q y ∂μ := by
  simpa [toCanonicalBoundaryTargetCompactSupportInput] using
    (B.toCanonicalBoundaryTargetCompactSupportInput
      |>.selectedBoundaryPartitionTerm_eq_setIntegral hx hq)

/--
Boundary partition-to-M8 data obtained through the canonical target compact
route.  This consumes the wrapper API from
`BoundaryMeasurePartitionLocalizationWrappers`.
-/
def toBoundaryMeasurePartitionToM8Data
    [IsManifold I 1 M] :
    BoundaryMeasurePartitionToM8Data
      (α := α) I omega selectedPartition D.targetImages μ
      B.globalBoundaryIntegral :=
  B.toCanonicalBoundaryTargetCompactSupportInput
    |>.toBoundaryMeasurePartitionToM8Data

@[simp]
theorem toBoundaryMeasurePartitionToM8Data_boundaryMeasureIntegral
    [IsManifold I 1 M] :
    B.toBoundaryMeasurePartitionToM8Data.boundaryMeasureIntegral =
      B.boundaryMeasureIntegral := by
  rfl

/--
The boundary partition-to-M8 data keeps the COV-backed selected set-integral
term equality.
-/
theorem toBoundaryMeasurePartitionToM8Data_selectedBoundaryPartitionTerm_eq_setIntegral
    [IsManifold I 1 M]
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    B.toBoundaryMeasurePartitionToM8Data.boundaryPartition.boundaryPartitionTerm x q =
      ∫ y in B.boundaryPieceSet x q,
        B.boundaryPieceIntegrand x q y ∂μ := by
  simpa [toBoundaryMeasurePartitionToM8Data,
    toCanonicalBoundaryTargetCompactSupportInput] using
    (B.toBoundaryMeasurePartitionToM8Data
      |>.selectedBoundaryPartitionTerm_eq_setIntegral hx hq)

/--
Compact-support measure-builder data obtained from the COV-backed boundary
route plus any compatible bulk measure package.  This is the exact handoff used
by `BoundaryTargetMeasureBuilderGlue`.
-/
def toMeasureBuilderData
    [IsManifold I 1 M] {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition D.targetImages
        globalBulkIntegral) :
    CompactSupportMeasureToM8BuilderData
      (α := α) I omega selectedPartition D.targetImages μ
      globalBulkIntegral B.globalBoundaryIntegral :=
  B.toCanonicalBoundaryTargetCompactSupportInput.toMeasureBuilderData bulk

@[simp]
theorem toMeasureBuilderData_boundaryMeasureIntegral
    [IsManifold I 1 M] {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := α) (μ := μ) selectedPartition D.targetImages
        globalBulkIntegral) :
    (B.toMeasureBuilderData bulk).boundaryMeasureIntegral =
      B.boundaryMeasureIntegral := by
  rfl

end BoundaryMeasureFromTargetCOVInput

end BoundaryMeasureFromTargetCOV

end Stokes

end
