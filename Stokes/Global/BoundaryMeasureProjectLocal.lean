import Stokes.Global.BoundaryMeasureFromPartition
import Stokes.Global.BoundaryMeasureToM8
import Stokes.Global.ProjectLocalConstructor

/-!
# Project-local boundary measure adapters

This file adds a project-local-facing boundary measure adapter.

The analytic facts stay explicit: callers provide the genuine boundary measure
integral, the set-integral identity for each active project-local boundary
piece, the pointwise alignment from project-local piece integrals to boundary
partition terms, and the a.e. finite indicator reconstruction of the boundary
integrand.  The definitions here only repackage those hypotheses into the
existing `BoundaryMeasureLocalizationData` and `M8BoundaryMeasureData` APIs.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section ProjectLocalBoundaryMeasure

universe u w c p a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {Piece : Type p}
variable {α : Type a} [MeasurableSpace α]
variable {μ : Measure α}

namespace ProjectLocalGlobalStokesData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/-- The finite boundary partition carried by a project-local package. -/
def boundaryMeasurePartitionData
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    BoundaryMeasurePartitionData Chart Piece where
  activeCharts := D.activeCharts
  boundaryPieces := D.localPieces
  boundaryPartitionTerm := D.boundaryPartitionTerm

@[simp]
theorem boundaryMeasurePartitionData_activeCharts
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    D.boundaryMeasurePartitionData.activeCharts = D.activeCharts :=
  rfl

@[simp]
theorem boundaryMeasurePartitionData_boundaryPieces
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    D.boundaryMeasurePartitionData.boundaryPieces = D.localPieces :=
  rfl

@[simp]
theorem boundaryMeasurePartitionData_boundaryPartitionTerm
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    D.boundaryMeasurePartitionData.boundaryPartitionTerm =
      D.boundaryPartitionTerm :=
  rfl

@[simp]
theorem boundaryMeasurePartitionData_boundaryPartitionSum
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :
    D.boundaryMeasurePartitionData.boundaryPartitionSum =
      selectedBoundaryPieceSum D.activeCharts D.localPieces
        D.boundaryPartitionTerm :=
  rfl

end ProjectLocalGlobalStokesData

/--
Boundary measure data aligned with a project-local global package.

The fields intentionally expose the real analytic obligations.  In particular,
the project-local piece integral is identified with a genuine set integral,
and the selected partition term is separately identified with that piece
integral.  The adapter below only composes these equalities.
-/
structure ProjectLocalBoundaryMeasureData {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    (D : ProjectLocalGlobalStokesData I ω Chart Piece)
    (μ : Measure α) where
  /-- Boundary-side integrand represented by the boundary measure integral. -/
  boundaryIntegrand : α → Real
  /-- Measurable localization set for one project-local boundary piece. -/
  boundaryPieceSet : Chart → Piece → Set α
  /-- Scalar integrand attached to one project-local boundary piece. -/
  boundaryPieceIntegrand : Chart → Piece → α → Real
  /-- The genuine boundary measure integral. -/
  boundaryMeasureIntegral : Real
  /-- The represented project-local boundary integral is the measure integral. -/
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :
    D.globalBoundaryIntegral = boundaryMeasureIntegral
  /-- The genuine boundary measure integral is the integral of `boundaryIntegrand`. -/
  boundaryMeasureIntegral_eq_integral :
    boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ
  /-- Active localization sets are measurable. -/
  boundaryPieceSet_measurable :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x → MeasurableSet (boundaryPieceSet x q)
  /-- Active piece integrands are integrable on their localization sets. -/
  boundaryPieceIntegrableOn :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        IntegrableOn (boundaryPieceIntegrand x q) (boundaryPieceSet x q) μ
  /-- Each project-local boundary piece integral is the corresponding set integral. -/
  projectLocalBoundaryIntegral_eq_setIntegral :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
            (D.lowerCorner x q) (D.upperCorner x q) =
          ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ
  /-- The selected boundary partition term is the project-local piece integral. -/
  boundaryPartitionTerm_eq_projectLocalBoundaryIntegral :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        D.boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
            (D.lowerCorner x q) (D.upperCorner x q)
  /-- A.e. reconstruction by the finite indicator-localized project-local sum. -/
  boundaryIntegrand_ae_eq_indicatorSum :
    boundaryIntegrand =ᵐ[μ]
      boundaryMeasureIndicatorSum D.activeCharts D.localPieces
        boundaryPieceSet boundaryPieceIntegrand

namespace ProjectLocalBoundaryMeasureData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {D : ProjectLocalGlobalStokesData I ω Chart Piece}

/-- The boundary partition term as the genuine set integral for one active piece. -/
theorem boundaryPartitionTerm_eq_setIntegral
    (B : ProjectLocalBoundaryMeasureData (α := α) D μ)
    {x : Chart} (hx : x ∈ D.activeCharts)
    {q : Piece} (hq : q ∈ D.localPieces x) :
    D.boundaryPartitionTerm x q =
      ∫ y in B.boundaryPieceSet x q, B.boundaryPieceIntegrand x q y ∂μ :=
  (B.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral x hx q hq).trans
    (B.projectLocalBoundaryIntegral_eq_setIntegral x hx q hq)

/-- Project-local boundary data as the compact/set-integral boundary package. -/
def toBoundaryCompactMeasureFields
    (B : ProjectLocalBoundaryMeasureData (α := α) D μ) :
    BoundaryCompactMeasureFields μ D.activeCharts D.localPieces
      D.boundaryPartitionTerm :=
  D.boundaryMeasurePartitionData.compactFieldsOfIntegrableOn
    (μ := μ) B.boundaryIntegrand B.boundaryPieceSet
    B.boundaryPieceIntegrand B.boundaryMeasureIntegral
    B.boundaryMeasureIntegral_eq_integral B.boundaryPieceSet_measurable
    B.boundaryPieceIntegrableOn
    (fun x hx q hq =>
      B.boundaryPartitionTerm_eq_setIntegral (x := x) hx (q := q) hq)
    B.boundaryIntegrand_ae_eq_indicatorSum

/-- Project-local boundary data as analytic boundary measure localization data. -/
def toBoundaryMeasureLocalizationData
    (B : ProjectLocalBoundaryMeasureData (α := α) D μ) :
    BoundaryMeasureLocalizationData μ D.activeCharts D.localPieces
      D.boundaryPartitionTerm :=
  B.toBoundaryCompactMeasureFields.toBoundaryMeasureLocalizationData

/-- Project-local boundary data in the natural fieldized boundary-measure shape. -/
def toBoundaryMeasureLocalizationFields
    (B : ProjectLocalBoundaryMeasureData (α := α) D μ) :
    BoundaryMeasureLocalizationFields D.activeCharts D.localPieces
      D.boundaryPartitionTerm D.globalBoundaryIntegral :=
  B.toBoundaryMeasureLocalizationData.toBoundaryMeasureLocalizationFields
    D.globalBoundaryIntegral B.globalBoundaryIntegral_eq_boundaryMeasureIntegral

@[simp]
theorem toBoundaryMeasureLocalizationData_boundaryMeasureIntegral
    (B : ProjectLocalBoundaryMeasureData (α := α) D μ) :
    B.toBoundaryMeasureLocalizationData.boundaryMeasureIntegral =
      B.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem toBoundaryMeasureLocalizationFields_boundaryMeasureIntegral
    (B : ProjectLocalBoundaryMeasureData (α := α) D μ) :
    B.toBoundaryMeasureLocalizationFields.boundaryMeasureIntegral =
      B.boundaryMeasureIntegral :=
  rfl

/-- The project-local adapter supplies the boundary finite-sum localization. -/
theorem boundaryMeasureIntegral_eq_partitionSum
    (B : ProjectLocalBoundaryMeasureData (α := α) D μ) :
    B.boundaryMeasureIntegral =
      selectedBoundaryPieceSum D.activeCharts D.localPieces
        D.boundaryPartitionTerm :=
  B.toBoundaryMeasureLocalizationData.boundaryMeasureIntegral_eq_partitionSum

/-- The project-local represented boundary integral localizes to the partition sum. -/
theorem globalBoundaryIntegral_eq_partitionSum
    (B : ProjectLocalBoundaryMeasureData (α := α) D μ) :
    D.globalBoundaryIntegral =
      selectedBoundaryPieceSum D.activeCharts D.localPieces
        D.boundaryPartitionTerm :=
  B.globalBoundaryIntegral_eq_boundaryMeasureIntegral.trans
    B.boundaryMeasureIntegral_eq_partitionSum

end ProjectLocalBoundaryMeasureData

section M8BoundaryMeasure

universe b

variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {D : ProjectLocalGlobalStokesData I omega M BoundaryPiece}

namespace ProjectLocalBoundaryMeasureData

/--
Project-local boundary data as the M8 boundary-measure package.

The two alignment hypotheses state that the project-local active charts and
pieces are exactly the selected M8 boundary family.  The measure, set-integral,
and a.e. reconstruction facts remain the fields of `B`.
-/
def toM8BoundaryMeasureData
    (B : ProjectLocalBoundaryMeasureData (α := α) D μ)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces : D.localPieces = targetImages.boundaryPieces) :
    M8BoundaryMeasureData I omega selectedPartition targetImages where
  boundaryPartitionTerm := D.boundaryPartitionTerm
  globalBoundaryIntegral := D.globalBoundaryIntegral
  boundaryMeasureIntegral := B.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    B.globalBoundaryIntegral_eq_boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_partitionSum := by
    simpa [hactive, hpieces] using B.boundaryMeasureIntegral_eq_partitionSum

@[simp]
theorem toM8BoundaryMeasureData_boundaryPartitionTerm
    (B : ProjectLocalBoundaryMeasureData (α := α) D μ)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces : D.localPieces = targetImages.boundaryPieces) :
    (B.toM8BoundaryMeasureData
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      hactive hpieces).boundaryPartitionTerm =
      D.boundaryPartitionTerm :=
  rfl

@[simp]
theorem toM8BoundaryMeasureData_globalBoundaryIntegral
    (B : ProjectLocalBoundaryMeasureData (α := α) D μ)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces : D.localPieces = targetImages.boundaryPieces) :
    (B.toM8BoundaryMeasureData
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      hactive hpieces).globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

@[simp]
theorem toM8BoundaryMeasureData_boundaryMeasureIntegral
    (B : ProjectLocalBoundaryMeasureData (α := α) D μ)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces : D.localPieces = targetImages.boundaryPieces) :
    (B.toM8BoundaryMeasureData
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      hactive hpieces).boundaryMeasureIntegral =
      B.boundaryMeasureIntegral :=
  rfl

/-- Projection theorem for the M8 boundary finite-sum field. -/
theorem toM8BoundaryMeasureData_boundaryMeasureIntegral_eq_partitionSum
    (B : ProjectLocalBoundaryMeasureData (α := α) D μ)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces : D.localPieces = targetImages.boundaryPieces) :
    (B.toM8BoundaryMeasureData
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      hactive hpieces).boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces D.boundaryPartitionTerm :=
  (B.toM8BoundaryMeasureData
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    hactive hpieces).boundaryMeasureIntegral_eq_partitionSum

end ProjectLocalBoundaryMeasureData

namespace ProjectLocalGlobalStokesData

/--
Direct M8 boundary adapter from already-built
`BoundaryMeasureLocalizationData` over a project-local package.
-/
def m8BoundaryMeasureDataOfBoundaryMeasureLocalizationData
    (D : ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (B :
      BoundaryMeasureLocalizationData μ D.activeCharts D.localPieces
        D.boundaryPartitionTerm)
    (hmeasure : D.globalBoundaryIntegral = B.boundaryMeasureIntegral)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces : D.localPieces = targetImages.boundaryPieces) :
    M8BoundaryMeasureData I omega selectedPartition targetImages where
  boundaryPartitionTerm := D.boundaryPartitionTerm
  globalBoundaryIntegral := D.globalBoundaryIntegral
  boundaryMeasureIntegral := B.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := hmeasure
  boundaryMeasureIntegral_eq_partitionSum := by
    simpa [hactive, hpieces] using B.boundaryMeasureIntegral_eq_partitionSum

@[simp]
theorem m8BoundaryMeasureDataOfBoundaryMeasureLocalizationData_boundaryMeasureIntegral
    (D : ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (B :
      BoundaryMeasureLocalizationData μ D.activeCharts D.localPieces
        D.boundaryPartitionTerm)
    (hmeasure : D.globalBoundaryIntegral = B.boundaryMeasureIntegral)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces : D.localPieces = targetImages.boundaryPieces) :
    (D.m8BoundaryMeasureDataOfBoundaryMeasureLocalizationData
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      B hmeasure hactive hpieces).boundaryMeasureIntegral =
      B.boundaryMeasureIntegral :=
  rfl

end ProjectLocalGlobalStokesData

end M8BoundaryMeasure

end ProjectLocalBoundaryMeasure

end Stokes

end
