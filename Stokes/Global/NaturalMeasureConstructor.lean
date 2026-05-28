import Stokes.Global.NaturalStatement
import Stokes.Global.BoundaryMeasureLocalization

/-!
# Natural measure-level global Stokes constructor

This file is a thin M7-facing wrapper around the current natural global Stokes
input.  The genuine bulk and boundary measure localization constructors are
not separate modules yet, so this file records the needed measure-localization
facts as small field packages.

The wrapper keeps the existing `NaturalGlobalStokesInput` as the bookkeeping
source of local Stokes, cancellation, chart-change, and reconstruction data,
then adds:

* a bulk measure integral identified with the represented global bulk integral;
* a boundary measure integral identified with the represented global boundary
  integral.

The resulting theorem exposes both the current represented-integral Stokes
statement and the measure-integral version.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section MeasureLocalizationFields

universe u v w c i b p

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Fieldized bulk measure-localization data.

This is the placeholder for the eventual
`BulkIntegralLocalizationConstructor` layer.  It records an intermediate bulk
measure integral and the two equalities needed to recover the existing bulk
finite-sum reconstruction theorem.
-/
structure BulkMeasureLocalizationFields {k : Nat}
    {I : ModelWithCorners Real E H} {omega : ManifoldForm I M k}
    {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}
    (R : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece) where
  /-- The genuine bulk measure integral represented by the localization data. -/
  bulkMeasureIntegral : Real
  /-- The represented global bulk integral agrees with the measure integral. -/
  globalBulkIntegral_eq_bulkMeasureIntegral :
    R.globalBulkIntegral = bulkMeasureIntegral
  /-- The bulk measure integral is reconstructed from the finite local terms. -/
  bulkMeasureIntegral_eq_localBulkSum :
    bulkMeasureIntegral = BulkIntegralReconstructionData.localBulkSum R

namespace BulkMeasureLocalizationFields

variable {k : Nat}
variable {I : ModelWithCorners Real E H} {omega : ManifoldForm I M k}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}
variable {R : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece}

/-- Build the fieldized package from an explicit bulk measure integral. -/
def ofBulkMeasureEq
    (bulkMeasureIntegral : Real)
    (hmeasure : R.globalBulkIntegral = bulkMeasureIntegral)
    (hlocal :
      bulkMeasureIntegral = BulkIntegralReconstructionData.localBulkSum R) :
    BulkMeasureLocalizationFields R where
  bulkMeasureIntegral := bulkMeasureIntegral
  globalBulkIntegral_eq_bulkMeasureIntegral := hmeasure
  bulkMeasureIntegral_eq_localBulkSum := hlocal

/-- Build the fieldized package directly from the final finite-sum equality. -/
def ofEq
    (h : R.globalBulkIntegral = BulkIntegralReconstructionData.localBulkSum R) :
    BulkMeasureLocalizationFields R where
  bulkMeasureIntegral := R.globalBulkIntegral
  globalBulkIntegral_eq_bulkMeasureIntegral := rfl
  bulkMeasureIntegral_eq_localBulkSum := h

/-- The bulk localization fields recover the usual bulk reconstruction theorem. -/
theorem globalBulkIntegral_eq_localBulkSum
    (B : BulkMeasureLocalizationFields R) :
    R.globalBulkIntegral = BulkIntegralReconstructionData.localBulkSum R :=
  B.globalBulkIntegral_eq_bulkMeasureIntegral.trans
    B.bulkMeasureIntegral_eq_localBulkSum

/-- Expanded finite-sum form of the recovered bulk reconstruction theorem. -/
theorem globalBulkIntegral_eq_localBulkSum_expanded
    (B : BulkMeasureLocalizationFields R) :
    R.globalBulkIntegral =
      (Finset.sum R.activeCharts fun x =>
          Finset.sum (R.interiorPieces x) fun q => R.interiorBulkTerm x q) +
        Finset.sum R.activeCharts fun x =>
          Finset.sum (R.boundaryPieces x) fun q => R.boundaryBulkTerm x q := by
  simpa [BulkIntegralReconstructionData.localBulkSum,
    BulkIntegralReconstructionData.interiorBulkSum,
    BulkIntegralReconstructionData.boundaryBulkSum] using
    B.globalBulkIntegral_eq_localBulkSum

end BulkMeasureLocalizationFields

/--
Fieldized boundary measure-localization data.

This is the placeholder for the eventual `BoundaryMeasureLocalization` layer.
It is intentionally aligned with `BoundaryIntegralPartitionReconstructionData`,
but keeps the name and shape close to the natural measure-level theorem.
-/
structure BoundaryMeasureLocalizationFields {Chart : Type c} {Piece : Type p}
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart -> Finset Piece)
    (boundaryPartitionTerm : Chart -> Piece -> Real)
    (globalBoundaryIntegral : Real) where
  /-- The genuine boundary measure integral represented by the localization data. -/
  boundaryMeasureIntegral : Real
  /-- The represented global boundary integral agrees with the measure integral. -/
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :
    globalBoundaryIntegral = boundaryMeasureIntegral
  /-- The boundary measure integral is reconstructed from finite partition terms. -/
  boundaryMeasureIntegral_eq_partitionSum :
    boundaryMeasureIntegral =
      selectedBoundaryPieceSum activeCharts boundaryPieces boundaryPartitionTerm

namespace BoundaryMeasureLocalizationFields

variable {Chart : Type c} {Piece : Type p}
variable {activeCharts : Finset Chart}
variable {boundaryPieces : Chart -> Finset Piece}
variable {boundaryPartitionTerm : Chart -> Piece -> Real}
variable {globalBoundaryIntegral : Real}

/-- Build the fieldized package from an explicit boundary measure integral. -/
def ofBoundaryMeasureEq
    (boundaryMeasureIntegral : Real)
    (hmeasure : globalBoundaryIntegral = boundaryMeasureIntegral)
    (hpartition :
      boundaryMeasureIntegral =
        selectedBoundaryPieceSum activeCharts boundaryPieces boundaryPartitionTerm) :
    BoundaryMeasureLocalizationFields activeCharts boundaryPieces
      boundaryPartitionTerm globalBoundaryIntegral where
  boundaryMeasureIntegral := boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := hmeasure
  boundaryMeasureIntegral_eq_partitionSum := hpartition

/-- Build the fieldized package directly from the final finite-sum equality. -/
def ofEq
    (h :
      globalBoundaryIntegral =
        selectedBoundaryPieceSum activeCharts boundaryPieces boundaryPartitionTerm) :
    BoundaryMeasureLocalizationFields activeCharts boundaryPieces
      boundaryPartitionTerm globalBoundaryIntegral where
  boundaryMeasureIntegral := globalBoundaryIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := rfl
  boundaryMeasureIntegral_eq_partitionSum := h

/-- Convert the fieldized boundary package to the existing partition reconstruction data. -/
def toBoundaryIntegralPartitionReconstructionData
    (B :
      BoundaryMeasureLocalizationFields activeCharts boundaryPieces
        boundaryPartitionTerm globalBoundaryIntegral) :
    BoundaryIntegralPartitionReconstructionData activeCharts boundaryPieces
      boundaryPartitionTerm globalBoundaryIntegral :=
  BoundaryIntegralPartitionReconstructionData.ofBoundaryMeasureEq
    B.boundaryMeasureIntegral
    B.globalBoundaryIntegral_eq_boundaryMeasureIntegral
    B.boundaryMeasureIntegral_eq_partitionSum

/-- Forget the intermediate measure integral and keep the core finite-sum package. -/
def toBoundaryIntegralReconstructionData
    (B :
      BoundaryMeasureLocalizationFields activeCharts boundaryPieces
        boundaryPartitionTerm globalBoundaryIntegral) :
    BoundaryIntegralReconstructionData activeCharts boundaryPieces
      boundaryPartitionTerm globalBoundaryIntegral :=
  B.toBoundaryIntegralPartitionReconstructionData
    |>.toBoundaryIntegralReconstructionData

/-- The boundary localization fields recover the usual boundary reconstruction theorem. -/
theorem globalBoundaryIntegral_eq_partitionSum
    (B :
      BoundaryMeasureLocalizationFields activeCharts boundaryPieces
        boundaryPartitionTerm globalBoundaryIntegral) :
    globalBoundaryIntegral =
      selectedBoundaryPieceSum activeCharts boundaryPieces boundaryPartitionTerm :=
  B.globalBoundaryIntegral_eq_boundaryMeasureIntegral.trans
    B.boundaryMeasureIntegral_eq_partitionSum

/-- Expanded finite-sum form of the recovered boundary reconstruction theorem. -/
theorem globalBoundaryIntegral_eq_partitionSum_expanded
    (B :
      BoundaryMeasureLocalizationFields activeCharts boundaryPieces
        boundaryPartitionTerm globalBoundaryIntegral) :
    globalBoundaryIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun q => boundaryPartitionTerm x q := by
  simpa [selectedBoundaryPieceSum] using B.globalBoundaryIntegral_eq_partitionSum

end BoundaryMeasureLocalizationFields

namespace BoundaryMeasureLocalizationData

universe a

variable {α : Type a} [MeasurableSpace α]
variable {Chart : Type c} {Piece : Type p}
variable {μ : MeasureTheory.Measure α}
variable {activeCharts : Finset Chart}
variable {boundaryPieces : Chart -> Finset Piece}
variable {boundaryPartitionTerm : Chart -> Piece -> Real}

/--
Forget the analytic integrand fields of `BoundaryMeasureLocalizationData`,
keeping only the measure integral and its selected finite-sum localization.
-/
def toBoundaryMeasureLocalizationFields
    (D :
      BoundaryMeasureLocalizationData μ activeCharts boundaryPieces
        boundaryPartitionTerm)
    (globalBoundaryIntegral : Real)
    (hmeasure : globalBoundaryIntegral = D.boundaryMeasureIntegral) :
    BoundaryMeasureLocalizationFields activeCharts boundaryPieces
      boundaryPartitionTerm globalBoundaryIntegral where
  boundaryMeasureIntegral := D.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := hmeasure
  boundaryMeasureIntegral_eq_partitionSum :=
    D.boundaryMeasureIntegral_eq_selectedBoundaryPieceSum

@[simp]
theorem toBoundaryMeasureLocalizationFields_boundaryMeasureIntegral
    (D :
      BoundaryMeasureLocalizationData μ activeCharts boundaryPieces
        boundaryPartitionTerm)
    (globalBoundaryIntegral : Real)
    (hmeasure : globalBoundaryIntegral = D.boundaryMeasureIntegral) :
    BoundaryMeasureLocalizationFields.boundaryMeasureIntegral
        (D.toBoundaryMeasureLocalizationFields globalBoundaryIntegral hmeasure) =
      D.boundaryMeasureIntegral :=
  rfl

end BoundaryMeasureLocalizationData

end MeasureLocalizationFields

section NaturalMeasureConstructor

universe u w i b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Natural measure-level Stokes input.

The large natural global input is kept as one field.  The two additional
measure-localization packages expose the intended genuine bulk and boundary
measure integrals without forcing downstream users to restate the low-level
reconstruction fields at this wrapper boundary.
-/
structure NaturalMeasureStokesInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (InteriorPiece : Type i) (BoundaryPiece : Type b) where
  /-- Existing natural global package supplying reconstruction and local data. -/
  naturalInput : NaturalGlobalStokesInput I omega InteriorPiece BoundaryPiece
  /-- Bulk measure localization for the represented global bulk integral. -/
  bulkLocalization :
    BulkMeasureLocalizationFields naturalInput.bulkReconstruction
  /-- Boundary measure localization for the represented global boundary integral. -/
  boundaryLocalization :
    BoundaryMeasureLocalizationFields
      naturalInput.bulkReconstruction.activeCharts
      naturalInput.bulkReconstruction.boundaryPieces
      naturalInput.boundaryPartitionTerm
      naturalInput.globalBoundaryIntegral

namespace NaturalMeasureStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {InteriorPiece : Type i} {BoundaryPiece : Type b}

/-- Forget the measure-localization fields and recover the current natural input. -/
abbrev toNaturalGlobalStokesInput
    (D : NaturalMeasureStokesInput I omega InteriorPiece BoundaryPiece) :
    NaturalGlobalStokesInput I omega InteriorPiece BoundaryPiece :=
  D.naturalInput

/-- The selected mixed input carried by the underlying natural package. -/
abbrev selectedMixedInput
    (D : NaturalMeasureStokesInput I omega InteriorPiece BoundaryPiece) :
    SelectedMixedGlobalInput I omega InteriorPiece BoundaryPiece :=
  D.naturalInput.selectedMixedInput

/-- The final global data carried by the underlying natural package. -/
abbrev toGlobalStokesData
    (D : NaturalMeasureStokesInput I omega InteriorPiece BoundaryPiece) :
    GlobalStokesData I omega M InteriorPiece BoundaryPiece :=
  D.naturalInput.toGlobalStokesData

@[simp]
theorem toNaturalGlobalStokesInput_eq
    (D : NaturalMeasureStokesInput I omega InteriorPiece BoundaryPiece) :
    D.toNaturalGlobalStokesInput = D.naturalInput :=
  rfl

@[simp]
theorem selectedMixedInput_eq
    (D : NaturalMeasureStokesInput I omega InteriorPiece BoundaryPiece) :
    D.selectedMixedInput = D.naturalInput.selectedMixedInput :=
  rfl

@[simp]
theorem toGlobalStokesData_globalBulkIntegral
    (D : NaturalMeasureStokesInput I omega InteriorPiece BoundaryPiece) :
    D.toGlobalStokesData.globalBulkIntegral =
      D.naturalInput.bulkReconstruction.globalBulkIntegral :=
  rfl

@[simp]
theorem toGlobalStokesData_globalBoundaryIntegral
    (D : NaturalMeasureStokesInput I omega InteriorPiece BoundaryPiece) :
    D.toGlobalStokesData.globalBoundaryIntegral =
      D.naturalInput.globalBoundaryIntegral :=
  rfl

/-- Boundary measure localization as the existing partition reconstruction package. -/
abbrev boundaryIntegralPartitionReconstructionData
    (D : NaturalMeasureStokesInput I omega InteriorPiece BoundaryPiece) :
    BoundaryIntegralPartitionReconstructionData
      D.naturalInput.bulkReconstruction.activeCharts
      D.naturalInput.bulkReconstruction.boundaryPieces
      D.naturalInput.boundaryPartitionTerm
      D.naturalInput.globalBoundaryIntegral :=
  D.boundaryLocalization.toBoundaryIntegralPartitionReconstructionData

/-- Boundary measure localization as the core boundary reconstruction package. -/
abbrev boundaryIntegralReconstructionData
    (D : NaturalMeasureStokesInput I omega InteriorPiece BoundaryPiece) :
    BoundaryIntegralReconstructionData
      D.naturalInput.bulkReconstruction.activeCharts
      D.naturalInput.bulkReconstruction.boundaryPieces
      D.naturalInput.boundaryPartitionTerm
      D.naturalInput.globalBoundaryIntegral :=
  D.boundaryLocalization.toBoundaryIntegralReconstructionData

/-- Current represented-integral Stokes theorem for the underlying natural input. -/
theorem global_stokes
    (D : NaturalMeasureStokesInput I omega InteriorPiece BoundaryPiece) :
    D.naturalInput.bulkReconstruction.globalBulkIntegral =
      D.naturalInput.globalBoundaryIntegral :=
  D.naturalInput.stokes

/-- The bulk measure integral equals the represented boundary integral. -/
theorem bulkMeasureIntegral_eq_globalBoundaryIntegral
    (D : NaturalMeasureStokesInput I omega InteriorPiece BoundaryPiece) :
    D.bulkLocalization.bulkMeasureIntegral =
      D.naturalInput.globalBoundaryIntegral := by
  calc
    D.bulkLocalization.bulkMeasureIntegral =
        D.naturalInput.bulkReconstruction.globalBulkIntegral :=
      D.bulkLocalization.globalBulkIntegral_eq_bulkMeasureIntegral.symm
    _ = D.naturalInput.globalBoundaryIntegral := D.global_stokes

/-- The represented bulk integral equals the boundary measure integral. -/
theorem globalBulkIntegral_eq_boundaryMeasureIntegral
    (D : NaturalMeasureStokesInput I omega InteriorPiece BoundaryPiece) :
    D.naturalInput.bulkReconstruction.globalBulkIntegral =
      D.boundaryLocalization.boundaryMeasureIntegral := by
  calc
    D.naturalInput.bulkReconstruction.globalBulkIntegral =
        D.naturalInput.globalBoundaryIntegral := D.global_stokes
    _ = D.boundaryLocalization.boundaryMeasureIntegral :=
      D.boundaryLocalization.globalBoundaryIntegral_eq_boundaryMeasureIntegral

/-- Measure-level Stokes theorem: the bulk and boundary measure integrals agree. -/
theorem stokes
    (D : NaturalMeasureStokesInput I omega InteriorPiece BoundaryPiece) :
    D.bulkLocalization.bulkMeasureIntegral =
      D.boundaryLocalization.boundaryMeasureIntegral := by
  calc
    D.bulkLocalization.bulkMeasureIntegral =
        D.naturalInput.globalBoundaryIntegral :=
      D.bulkMeasureIntegral_eq_globalBoundaryIntegral
    _ = D.boundaryLocalization.boundaryMeasureIntegral :=
      D.boundaryLocalization.globalBoundaryIntegral_eq_boundaryMeasureIntegral

end NaturalMeasureStokesInput

/-- Blueprint-facing represented-integral wrapper for the measure-level input. -/
theorem naturalMeasureGlobalStokes
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
    {omega : ManifoldForm I M n}
    {InteriorPiece : Type i} {BoundaryPiece : Type b}
    (D : NaturalMeasureStokesInput I omega InteriorPiece BoundaryPiece) :
    D.naturalInput.bulkReconstruction.globalBulkIntegral =
      D.naturalInput.globalBoundaryIntegral :=
  D.global_stokes

/-- Blueprint-facing measure-level natural global Stokes wrapper. -/
theorem naturalMeasureStokes
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
    {omega : ManifoldForm I M n}
    {InteriorPiece : Type i} {BoundaryPiece : Type b}
    (D : NaturalMeasureStokesInput I omega InteriorPiece BoundaryPiece) :
    D.bulkLocalization.bulkMeasureIntegral =
      D.boundaryLocalization.boundaryMeasureIntegral :=
  D.stokes

end NaturalMeasureConstructor

end Stokes

end
