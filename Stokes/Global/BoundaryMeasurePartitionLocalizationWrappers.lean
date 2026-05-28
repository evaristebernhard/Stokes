import Stokes.Global.BoundaryTargetSelectedBoxAlignment

/-!
# Boundary measure partition localization wrappers

This file is a thin bookkeeping layer for the boundary-measure route.  It
does not prove any new measure reconstruction theorem: the genuine a.e.
indicator reconstruction, set-integral identities, and integrability facts
remain explicit fields of the existing records.  The lemmas here expose those
fields in the selected-boundary-piece shapes used by later M8 constructors.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryMeasurePartitionLocalizationWrappers

universe u w c p a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {Piece : Type p}
variable {α : Type a} [MeasurableSpace α]
variable {μ : Measure α}

namespace BoundaryMeasurePartitionData

variable (P : BoundaryMeasurePartitionData Chart Piece)

@[simp]
theorem boundaryPartitionSum_eq_selectedBoundaryPieceSum :
    P.boundaryPartitionSum =
      selectedBoundaryPieceSum P.activeCharts P.boundaryPieces
        P.boundaryPartitionTerm := by
  rfl

/-- Expanded finite-sum form of the selected boundary partition data. -/
theorem boundaryPartitionSum_expanded :
    P.boundaryPartitionSum =
      Finset.sum P.activeCharts fun x =>
        Finset.sum (P.boundaryPieces x) fun q =>
          P.boundaryPartitionTerm x q := by
  rfl

/--
Rewrite a boundary partition sum after identifying active charts and boundary
pieces with a downstream selected family.
-/
theorem boundaryPartitionSum_rewrite
    {activeCharts : Finset Chart}
    {boundaryPieces : Chart → Finset Piece}
    (hactive : P.activeCharts = activeCharts)
    (hpieces : P.boundaryPieces = boundaryPieces) :
    P.boundaryPartitionSum =
      selectedBoundaryPieceSum activeCharts boundaryPieces
        P.boundaryPartitionTerm := by
  subst activeCharts
  subst boundaryPieces
  rfl

/--
Rewrite an indicator reconstruction after identifying active charts and
boundary pieces with a downstream selected family.
-/
theorem boundaryMeasureIndicatorSum_rewrite
    {activeCharts : Finset Chart}
    {boundaryPieces : Chart → Finset Piece}
    (hactive : P.activeCharts = activeCharts)
    (hpieces : P.boundaryPieces = boundaryPieces)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real) :
    boundaryMeasureIndicatorSum P.activeCharts P.boundaryPieces
        boundaryPieceSet boundaryPieceIntegrand =
      boundaryMeasureIndicatorSum activeCharts boundaryPieces
        boundaryPieceSet boundaryPieceIntegrand := by
  subst activeCharts
  subst boundaryPieces
  rfl

end BoundaryMeasurePartitionData

namespace BoundaryCompactMeasureFields

variable {activeCharts : Finset Chart}
variable {boundaryPieces : Chart → Finset Piece}
variable {boundaryPartitionTerm : Chart → Piece → Real}
variable
    (D :
      BoundaryCompactMeasureFields μ activeCharts boundaryPieces
        boundaryPartitionTerm)

@[simp]
theorem pieceIndicator_eq_boundaryMeasurePieceIndicator
    (x : Chart) (q : Piece) :
    D.pieceIndicator x q =
      boundaryMeasurePieceIndicator D.boundaryPieceSet
        D.boundaryPieceIntegrand x q := by
  rfl

/-- The compact-field integrand is a.e. the selected sum of its piece indicators. -/
theorem boundaryIntegrand_ae_eq_pieceIndicatorSum :
    D.boundaryIntegrand =ᵐ[μ]
      boundaryMeasurePieceSum activeCharts boundaryPieces
        D.pieceIndicator := by
  simpa [pieceIndicator, boundaryMeasureIndicatorSum] using
    D.boundaryIntegrand_ae_eq_indicatorSum

/-- Active boundary support sets are measurable, in selected-piece form. -/
theorem selectedPieceSet_measurable
    {x : Chart} (hx : x ∈ activeCharts)
    {q : Piece} (hq : q ∈ boundaryPieces x) :
    MeasurableSet (D.boundaryPieceSet x q) :=
  D.boundaryPieceSet_measurable x hx q hq

/-- Active unlocalized boundary-piece integrands are set-integrable. -/
theorem selectedPiece_integrableOn
    {x : Chart} (hx : x ∈ activeCharts)
    {q : Piece} (hq : q ∈ boundaryPieces x) :
    IntegrableOn (D.boundaryPieceIntegrand x q)
      (D.boundaryPieceSet x q) μ :=
  D.boundaryPieceIntegrableOn x hx q hq

/-- Active indicator-localized boundary pieces are integrable. -/
theorem selectedPieceIndicator_integrable
    {x : Chart} (hx : x ∈ activeCharts)
    {q : Piece} (hq : q ∈ boundaryPieces x) :
    Integrable (D.pieceIndicator x q) μ :=
  D.pieceIndicator_integrable hx hq

/-- Set-integral orientation of the active partition-term equality. -/
theorem selectedPiece_setIntegral_eq_boundaryPartitionTerm
    {x : Chart} (hx : x ∈ activeCharts)
    {q : Piece} (hq : q ∈ boundaryPieces x) :
    (∫ y in D.boundaryPieceSet x q,
        D.boundaryPieceIntegrand x q y ∂μ) =
      boundaryPartitionTerm x q :=
  (D.boundaryPartitionTerm_eq_setIntegral x hx q hq).symm

/-- Indicator-integral orientation of the active partition-term equality. -/
theorem selectedPiece_indicatorIntegral_eq_boundaryPartitionTerm
    {x : Chart} (hx : x ∈ activeCharts)
    {q : Piece} (hq : q ∈ boundaryPieces x) :
    (∫ y, D.pieceIndicator x q y ∂μ) =
      boundaryPartitionTerm x q :=
  (D.boundaryPartitionTerm_eq_indicatorIntegral (x := x) hx (q := q) hq).symm

@[simp]
theorem toBoundaryMeasureLocalizationData_boundaryIntegrand :
    D.toBoundaryMeasureLocalizationData.boundaryIntegrand =
      D.boundaryIntegrand := by
  rfl

@[simp]
theorem toBoundaryMeasureLocalizationData_boundaryPieceSet :
    D.toBoundaryMeasureLocalizationData.boundaryPieceSet =
      D.boundaryPieceSet := by
  rfl

@[simp]
theorem toBoundaryMeasureLocalizationData_boundaryPieceIntegrand :
    D.toBoundaryMeasureLocalizationData.boundaryPieceIntegrand =
      D.boundaryPieceIntegrand := by
  rfl

@[simp]
theorem toBoundaryMeasureLocalizationData_pieceFunction
    (x : Chart) (q : Piece) :
    D.toBoundaryMeasureLocalizationData.pieceFunction x q =
      D.pieceIndicator x q := by
  rfl

/-- The localization data produced from compact fields has the same piece sum. -/
theorem toBoundaryMeasureLocalizationData_ae_eq_pieceFunctionSum :
    D.toBoundaryMeasureLocalizationData.boundaryIntegrand =ᵐ[μ]
      boundaryMeasurePieceSum activeCharts boundaryPieces
        D.toBoundaryMeasureLocalizationData.pieceFunction := by
  simpa [toBoundaryMeasureLocalizationData_pieceFunction] using
    D.boundaryIntegrand_ae_eq_pieceIndicatorSum

/-- Compact fields supply the selected finite-sum boundary-measure equality. -/
theorem boundaryMeasureIntegral_eq_selectedPieceSum_expanded :
    D.boundaryMeasureIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun q =>
          boundaryPartitionTerm x q := by
  simpa [selectedBoundaryPieceSum] using
    D.boundaryMeasureIntegral_eq_partitionSum

end BoundaryCompactMeasureFields

namespace BoundaryMeasureLocalizationData

variable {activeCharts : Finset Chart}
variable {boundaryPieces : Chart → Finset Piece}
variable {boundaryPartitionTerm : Chart → Piece → Real}
variable
    (D :
      BoundaryMeasureLocalizationData μ activeCharts boundaryPieces
        boundaryPartitionTerm)

@[simp]
theorem pieceFunction_eq_boundaryMeasurePieceIndicator
    (x : Chart) (q : Piece) :
    D.pieceFunction x q =
      boundaryMeasurePieceIndicator D.boundaryPieceSet
        D.boundaryPieceIntegrand x q := by
  rfl

/-- The recorded boundary integrand is a.e. the selected sum of `pieceFunction`. -/
theorem boundaryIntegrand_ae_eq_pieceFunctionSum :
    D.boundaryIntegrand =ᵐ[μ]
      boundaryMeasurePieceSum activeCharts boundaryPieces
        D.pieceFunction := by
  simpa [pieceFunction, boundaryMeasureIndicatorSum] using
    D.boundaryIntegrand_ae_eq_indicatorSum

/-- Active selected boundary-piece functions are integrable. -/
theorem pieceFunction_integrable
    {x : Chart} (hx : x ∈ activeCharts)
    {q : Piece} (hq : q ∈ boundaryPieces x) :
    Integrable (D.pieceFunction x q) μ := by
  simpa [pieceFunction] using
    D.boundaryPieceIntegrable x hx q hq

/-- Partition-term orientation of the active piece integral equality. -/
theorem boundaryPartitionTerm_eq_pieceFunctionIntegral
    {x : Chart} (hx : x ∈ activeCharts)
    {q : Piece} (hq : q ∈ boundaryPieces x) :
    boundaryPartitionTerm x q =
      ∫ y, D.pieceFunction x q y ∂μ := by
  simpa [pieceFunction] using
    D.boundaryPartitionTerm_eq_integral x hx q hq

/-- Integral orientation of the active piece integral equality. -/
theorem pieceFunctionIntegral_eq_boundaryPartitionTerm
    {x : Chart} (hx : x ∈ activeCharts)
    {q : Piece} (hq : q ∈ boundaryPieces x) :
    (∫ y, D.pieceFunction x q y ∂μ) =
      boundaryPartitionTerm x q :=
  (D.boundaryPartitionTerm_eq_pieceFunctionIntegral hx hq).symm

/-- Expanded finite-sum form of the boundary-measure localization equality. -/
theorem boundaryMeasureIntegral_eq_pieceFunctionSum_expanded :
    D.boundaryMeasureIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun q =>
          boundaryPartitionTerm x q := by
  simpa [selectedBoundaryPieceSum] using
    D.boundaryMeasureIntegral_eq_partitionSum

end BoundaryMeasureLocalizationData

section M8PartitionWrappers

variable {BoundaryPiece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {globalBoundaryIntegral : Real}

namespace BoundaryMeasurePartitionToM8Data

variable
    (D :
      BoundaryMeasurePartitionToM8Data
        (α := α) I omega selectedPartition targetImages μ
        globalBoundaryIntegral)

/-- Active-chart membership rewritten to the selected partition. -/
theorem boundary_active_mem_iff {x : M} :
    x ∈ D.boundaryPartition.activeCharts ↔ x ∈ selectedPartition.active := by
  rw [D.boundary_active]

/-- Boundary-piece membership rewritten to the selected target-image family. -/
theorem boundary_piece_mem_iff {x : M} {q : BoundaryPiece} :
    q ∈ D.boundaryPartition.boundaryPieces x ↔
      q ∈ targetImages.boundaryPieces x := by
  rw [D.boundary_pieces]

/-- Selected-shape measurability projected from partition-to-M8 data. -/
theorem selectedBoundaryPieceSet_measurable
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ targetImages.boundaryPieces x) :
    MeasurableSet (D.boundaryPieceSet x q) :=
  D.boundaryPieceSet_measurable x
    (by simpa [D.boundary_active] using hx) q
    (by simpa [D.boundary_pieces] using hq)

/-- Selected-shape `IntegrableOn` projected from partition-to-M8 data. -/
theorem selectedBoundaryPieceIntegrableOn
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ targetImages.boundaryPieces x) :
    IntegrableOn (D.boundaryPieceIntegrand x q)
      (D.boundaryPieceSet x q) μ :=
  D.boundaryPieceIntegrableOn x
    (by simpa [D.boundary_active] using hx) q
    (by simpa [D.boundary_pieces] using hq)

/-- Selected-shape set-integral equality projected from partition-to-M8 data. -/
theorem selectedBoundaryPartitionTerm_eq_setIntegral
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ targetImages.boundaryPieces x) :
    D.boundaryPartition.boundaryPartitionTerm x q =
      ∫ y in D.boundaryPieceSet x q,
        D.boundaryPieceIntegrand x q y ∂μ :=
  D.boundaryPartitionTerm_eq_setIntegral x
    (by simpa [D.boundary_active] using hx) q
    (by simpa [D.boundary_pieces] using hq)

/-- Selected-shape a.e. indicator reconstruction projected from partition-to-M8 data. -/
theorem boundaryIntegrand_ae_eq_selectedIndicatorSum :
    D.boundaryIntegrand =ᵐ[μ]
      boundaryMeasureIndicatorSum selectedPartition.active
        targetImages.boundaryPieces D.boundaryPieceSet
        D.boundaryPieceIntegrand := by
  simpa [D.boundary_active, D.boundary_pieces] using
    D.boundaryIntegrand_ae_eq_indicatorSum

/-- Selected-shape partition sum for the native partition object. -/
theorem boundaryPartition_boundaryPartitionSum_eq_selected :
    D.boundaryPartition.boundaryPartitionSum =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces
        D.boundaryPartition.boundaryPartitionTerm :=
  D.boundaryPartition.boundaryPartitionSum_rewrite
    D.boundary_active D.boundary_pieces

end BoundaryMeasurePartitionToM8Data

end M8PartitionWrappers

section CanonicalTargetCompactSupportWrappers

variable [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
variable [IsFiniteMeasureOnCompacts μ]
variable {BoundaryPiece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
variable
    {D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}

namespace CanonicalBoundaryTargetCompactSupportInput

variable (B : CanonicalBoundaryTargetCompactSupportInput (α := α) D μ)

/--
Canonical target compact-support input as the general boundary partition-to-M8
builder data.  This keeps the target-image selected indices and the analytic
measure fields in one reusable package.
-/
def toBoundaryMeasurePartitionToM8Data :
    BoundaryMeasurePartitionToM8Data
      (α := α) I omega selectedPartition D.targetImages μ
      B.globalBoundaryIntegral where
  boundaryPartition := D.toSelectedBoundaryMeasurePartitionData
  boundary_active := rfl
  boundary_pieces := rfl
  boundaryIntegrand := B.boundaryIntegrand
  boundaryPieceSet := B.boundaryPieceSet
  boundaryPieceIntegrand := B.boundaryPieceIntegrand
  boundaryMeasureIntegral := B.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    B.globalBoundaryIntegral_eq_boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_integral :=
    B.boundaryMeasureIntegral_eq_integral
  boundaryPieceSet_measurable := B.boundaryPieceSet_measurable
  boundaryPieceIntegrableOn := fun x hx q hq =>
    (B.boundaryPieceCompact x hx q hq).integrableOn (B.boundaryPieceSet x q)
  boundaryPartitionTerm_eq_setIntegral :=
    B.boundaryPartitionTerm_eq_setIntegral
  boundaryIntegrand_ae_eq_indicatorSum :=
    B.boundaryIntegrand_ae_eq_indicatorSum

@[simp]
theorem toBoundaryMeasurePartitionToM8Data_boundaryMeasureIntegral :
    B.toBoundaryMeasurePartitionToM8Data.boundaryMeasureIntegral =
      B.boundaryMeasureIntegral := by
  rfl

@[simp]
theorem toBoundaryMeasurePartitionToM8Data_globalBoundaryIntegral_eq :
    B.toBoundaryMeasurePartitionToM8Data.globalBoundaryIntegral_eq_boundaryMeasureIntegral =
      B.globalBoundaryIntegral_eq_boundaryMeasureIntegral := by
  rfl

@[simp]
theorem toBoundaryMeasurePartitionToM8Data_boundaryPartition_active :
    B.toBoundaryMeasurePartitionToM8Data.boundaryPartition.activeCharts =
      selectedPartition.active := by
  rfl

@[simp]
theorem toBoundaryMeasurePartitionToM8Data_boundaryPartition_pieces :
    B.toBoundaryMeasurePartitionToM8Data.boundaryPartition.boundaryPieces =
      D.targetImages.boundaryPieces := by
  rfl

/-- Canonical selected boundary-piece support measurability. -/
theorem selectedBoundaryPieceSet_measurable
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    MeasurableSet (B.boundaryPieceSet x q) :=
  B.boundaryPieceSet_measurable x hx q hq

/-- Canonical selected boundary-piece `IntegrableOn`, derived from compact support. -/
theorem selectedBoundaryPieceIntegrableOn
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    IntegrableOn (B.boundaryPieceIntegrand x q)
      (B.boundaryPieceSet x q) μ :=
  (B.boundaryPieceCompact x hx q hq).integrableOn (B.boundaryPieceSet x q)

/-- Canonical selected boundary-piece set-integral equality. -/
theorem selectedBoundaryPartitionTerm_eq_setIntegral
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    D.assembly.boundaryPartitionTerm x q =
      ∫ y in B.boundaryPieceSet x q,
        B.boundaryPieceIntegrand x q y ∂μ :=
  B.boundaryPartitionTerm_eq_setIntegral x hx q hq

/-- Canonical selected boundary-piece indicator integrability. -/
theorem selectedBoundaryPieceFunction_integrable
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    Integrable (B.canonicalBoundaryLocalizationData.pieceFunction x q) μ :=
  B.canonicalBoundaryLocalizationData.pieceFunction_integrable hx hq

/-- Canonical selected boundary-piece integral equality. -/
theorem selectedBoundaryPieceFunction_integral_eq_partitionTerm
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    (∫ y, B.canonicalBoundaryLocalizationData.pieceFunction x q y ∂μ) =
      D.assembly.boundaryPartitionTerm x q :=
  B.canonicalBoundaryLocalizationData
    |>.pieceFunctionIntegral_eq_boundaryPartitionTerm hx hq

/-- Canonical a.e. reconstruction in `pieceFunction` finite-sum form. -/
theorem selectedBoundaryIntegrand_ae_eq_pieceFunctionSum :
    B.boundaryIntegrand =ᵐ[μ]
      boundaryMeasurePieceSum selectedPartition.active
        D.targetImages.boundaryPieces
        B.canonicalBoundaryLocalizationData.pieceFunction := by
  simpa using
    B.canonicalBoundaryLocalizationData.boundaryIntegrand_ae_eq_pieceFunctionSum

/-- Canonical boundary measure localization, expanded as the selected finite sum. -/
theorem selectedBoundaryMeasureIntegral_eq_expandedSum :
    B.boundaryMeasureIntegral =
      Finset.sum selectedPartition.active fun x =>
        Finset.sum (D.targetImages.boundaryPieces x) fun q =>
          D.assembly.boundaryPartitionTerm x q := by
  simpa [selectedBoundaryPieceSum] using
    B.canonicalBoundaryMeasureIntegral_eq_partitionSum

/-- Canonical represented global boundary integral, expanded as the selected sum. -/
theorem selectedGlobalBoundaryIntegral_eq_expandedSum :
    B.globalBoundaryIntegral =
      Finset.sum selectedPartition.active fun x =>
        Finset.sum (D.targetImages.boundaryPieces x) fun q =>
          D.assembly.boundaryPartitionTerm x q := by
  exact B.globalBoundaryIntegral_eq_boundaryMeasureIntegral.trans
    B.selectedBoundaryMeasureIntegral_eq_expandedSum

/--
The boundary partition-to-M8 route obtained from the canonical input carries
the same selected finite-sum boundary measure equality.
-/
theorem toBoundaryMeasurePartitionToM8Data_boundaryMeasureIntegral_eq_partitionSum :
    B.toBoundaryMeasurePartitionToM8Data.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        D.targetImages.boundaryPieces D.assembly.boundaryPartitionTerm := by
  simpa using
    B.toBoundaryMeasurePartitionToM8Data.boundaryMeasureIntegral_eq_partitionSum

/--
The M8 boundary package produced through the general partition-to-M8 builder
has the same boundary finite-sum field as the canonical route.
-/
theorem toBoundaryMeasurePartitionToM8Data_toM8BoundaryMeasureData_partitionSum :
    B.toBoundaryMeasurePartitionToM8Data.toM8BoundaryMeasureData.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        D.targetImages.boundaryPieces D.assembly.boundaryPartitionTerm := by
  simpa using
    B.toBoundaryMeasurePartitionToM8Data
      |>.toM8BoundaryMeasureData_boundaryMeasureIntegral_eq_partitionSum

end CanonicalBoundaryTargetCompactSupportInput

end CanonicalTargetCompactSupportWrappers

end BoundaryMeasurePartitionLocalizationWrappers

end Stokes

end
