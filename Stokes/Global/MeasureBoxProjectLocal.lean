import Stokes.Global.BulkIntegralLocalizationConstructor

/-!
# Project-local adapter for measure-box terms

This module adds a project-local-facing wrapper for the measure-box comparison
fields used by `MeasureBoxAPI`.

The wrapper deliberately keeps the real analytic comparisons explicit.  A
caller supplies the measure-local box integral attached to each active local
piece, proves that the scalar measure-local term is that box integral, and
proves that the existing project-local bulk wrapper is the same box integral.
The adapter then produces the `MeasureBoxAPI` consumed by
`BulkIntegralLocalizationInput`.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section MeasureBoxProjectLocal

universe u w ιu cb pb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type ιu}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {BoundaryChart : Type cb} {BoundaryPiece : Type pb}

/--
Project-local-facing measure-box comparison data.

The `*MeasureBoxIntegral` fields are the caller's chosen measure-local box
integrals.  The equality fields are intentionally explicit: they are exactly
where later analytic code reconciles the concrete measure integral definition
with the existing project-local bulk wrappers.
-/
structure ProjectLocalMeasureBoxAPI
    {interior : LocalizedInteriorPieces (ι := ι) I ω}
    {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
    (measureTerms : BulkMeasureLocalizationTermFields interior boundary) where
  /-- Measure-local box integral for an interior localized piece. -/
  interiorMeasureBoxIntegral : ι → Real
  /-- Measure-local box integral for a boundary-chart bulk piece. -/
  boundaryMeasureBoxIntegral : BoundaryChart → BoundaryPiece → Real
  /-- Active interior scalar measure terms are the corresponding box integrals. -/
  interiorMeasureTerm_eq_measureBoxIntegral :
    ∀ i, i ∈ interior.active →
      measureTerms.interiorMeasureTerm i = interiorMeasureBoxIntegral i
  /-- Active boundary scalar measure terms are the corresponding box integrals. -/
  boundaryMeasureTerm_eq_measureBoxIntegral :
    ∀ x, x ∈ boundary.activeCharts →
      ∀ q, q ∈ boundary.boundaryPieces x →
        measureTerms.boundaryMeasureTerm x q =
          boundaryMeasureBoxIntegral x q
  /--
  Active interior project-local bulk terms are the chosen measure-box
  integrals.
  -/
  interiorProjectLocalBulkTerm_eq_measureBoxIntegral :
    ∀ i, i ∈ interior.active →
      interior.bulkTerm i = interiorMeasureBoxIntegral i
  /--
  Active boundary-chart project-local bulk terms are the chosen measure-box
  integrals.
  -/
  boundaryProjectLocalBulkTerm_eq_measureBoxIntegral :
    ∀ x, x ∈ boundary.activeCharts →
      ∀ q, q ∈ boundary.boundaryPieces x →
        BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
          boundaryMeasureBoxIntegral x q

namespace ProjectLocalMeasureBoxAPI

variable {interior : LocalizedInteriorPieces (ι := ι) I ω}
variable {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
variable {measureTerms : BulkMeasureLocalizationTermFields interior boundary}

/-- Interior measure-local terms agree with the existing project-local bulk terms. -/
theorem interiorMeasureTerm_eq_projectLocalBulkTerm
    (D : ProjectLocalMeasureBoxAPI measureTerms) {i : ι}
    (hi : i ∈ interior.active) :
    measureTerms.interiorMeasureTerm i = interior.bulkTerm i := by
  calc
    measureTerms.interiorMeasureTerm i = D.interiorMeasureBoxIntegral i :=
      D.interiorMeasureTerm_eq_measureBoxIntegral i hi
    _ = interior.bulkTerm i :=
      (D.interiorProjectLocalBulkTerm_eq_measureBoxIntegral i hi).symm

/--
Boundary-chart measure-local terms agree with the existing project-local bulk
terms.
-/
theorem boundaryMeasureTerm_eq_projectLocalBulkTerm
    (D : ProjectLocalMeasureBoxAPI measureTerms) {x : BoundaryChart}
    (hx : x ∈ boundary.activeCharts) {q : BoundaryPiece}
    (hq : q ∈ boundary.boundaryPieces x) :
    measureTerms.boundaryMeasureTerm x q =
      BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q := by
  calc
    measureTerms.boundaryMeasureTerm x q =
        D.boundaryMeasureBoxIntegral x q :=
      D.boundaryMeasureTerm_eq_measureBoxIntegral x hx q hq
    _ = BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q :=
      (D.boundaryProjectLocalBulkTerm_eq_measureBoxIntegral x hx q hq).symm

/--
Forget the named measure-box integrals and expose the direct
measure-term/project-local equality package from `MeasureBoxAPI.lean`.
-/
def toMeasureLocalBoxTermAPI
    (D : ProjectLocalMeasureBoxAPI measureTerms) :
    MeasureLocalBoxTermAPI measureTerms where
  interiorMeasureTerm_eq_boxTerm := by
    intro i hi
    exact D.interiorMeasureTerm_eq_projectLocalBulkTerm hi
  boundaryMeasureTerm_eq_boxTerm := by
    intro x hx q hq
    exact D.boundaryMeasureTerm_eq_projectLocalBulkTerm hx hq

/-- Turn project-local measure-box data into the constructor-level `MeasureBoxAPI`. -/
def toMeasureBoxAPI
    (D : ProjectLocalMeasureBoxAPI measureTerms)
    (integrandAE : BulkIntegrandAELocalFields measureTerms) :
    MeasureBoxAPI integrandAE :=
  D.toMeasureLocalBoxTermAPI.toMeasureBoxAPI integrandAE

/-- The project-local measure-box adapter supplies the bulk localization equality. -/
theorem bulkIntegralLocalizes
    (D : ProjectLocalMeasureBoxAPI measureTerms) :
    measureTerms.globalBulkIntegral =
      (Finset.sum interior.active fun i => interior.bulkTerm i) +
        BoundaryPieceFamilyInput.boundaryBulkSum boundary :=
  D.toMeasureLocalBoxTermAPI.bulkIntegralLocalizes

/-- Directly construct the existing partition input from project-local box data. -/
def toBulkIntegralPartitionInput
    (D : ProjectLocalMeasureBoxAPI measureTerms) :
    BulkIntegralPartitionInput (ι := ι)
      (I := I) (ω := ω) (BoundaryChart := BoundaryChart)
      (BoundaryPiece := BoundaryPiece) :=
  D.toMeasureLocalBoxTermAPI.toBulkIntegralPartitionInput

/--
Construct `BulkIntegralLocalizationInput` from project-local measure-box
identifications and the remaining analytic packages.
-/
def toBulkIntegralLocalizationInput
    (D : ProjectLocalMeasureBoxAPI measureTerms)
    (integrandAE : BulkIntegrandAELocalFields measureTerms)
    (integrability : CompactSupportIntegrability integrandAE) :
    BulkIntegralLocalizationInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece) where
  interior := interior
  boundary := boundary
  measureTerms := measureTerms
  integrandAE := integrandAE
  integrability := integrability
  measureBoxAPI := D.toMeasureBoxAPI integrandAE

@[simp]
theorem toBulkIntegralPartitionInput_globalBulkIntegral
    (D : ProjectLocalMeasureBoxAPI measureTerms) :
    D.toBulkIntegralPartitionInput.globalBulkIntegral =
      measureTerms.globalBulkIntegral :=
  rfl

@[simp]
theorem toBulkIntegralLocalizationInput_measureTerms
    (D : ProjectLocalMeasureBoxAPI measureTerms)
    (integrandAE : BulkIntegrandAELocalFields measureTerms)
    (integrability : CompactSupportIntegrability integrandAE) :
    (D.toBulkIntegralLocalizationInput integrandAE integrability).measureTerms =
      measureTerms :=
  rfl

@[simp]
theorem toBulkIntegralLocalizationInput_measureBoxAPI
    (D : ProjectLocalMeasureBoxAPI measureTerms)
    (integrandAE : BulkIntegrandAELocalFields measureTerms)
    (integrability : CompactSupportIntegrability integrandAE) :
    (D.toBulkIntegralLocalizationInput integrandAE integrability).measureBoxAPI =
      D.toMeasureBoxAPI integrandAE :=
  rfl

/--
Constructor for the common case where the caller already has direct
measure-term/project-local equalities.
-/
def ofMeasureTermEqProjectLocal
    (hinterior :
      ∀ i, i ∈ interior.active →
        measureTerms.interiorMeasureTerm i = interior.bulkTerm i)
    (hboundary :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          measureTerms.boundaryMeasureTerm x q =
            BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q) :
    ProjectLocalMeasureBoxAPI measureTerms where
  interiorMeasureBoxIntegral := fun i => interior.bulkTerm i
  boundaryMeasureBoxIntegral :=
    fun x q => BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q
  interiorMeasureTerm_eq_measureBoxIntegral := hinterior
  boundaryMeasureTerm_eq_measureBoxIntegral := hboundary
  interiorProjectLocalBulkTerm_eq_measureBoxIntegral := by
    intro i _hi
    rfl
  boundaryProjectLocalBulkTerm_eq_measureBoxIntegral := by
    intro x _hx q _hq
    rfl

end ProjectLocalMeasureBoxAPI

/--
Bundled project-local-facing input for the bulk localization constructor.

This is the direct handoff shape for callers that have already built
`measureTerms`, `integrandAE`, and `integrability`, but want to provide the
measure-box/project-local comparisons in the explicit project-local form above.
-/
structure ProjectLocalBulkIntegralLocalizationInput where
  /-- Localized partition-of-unity interior pieces. -/
  interior : LocalizedInteriorPieces (ι := ι) I ω
  /-- Boundary-chart bulk pieces. -/
  boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece
  /-- Measure-local finite-sum terms. -/
  measureTerms : BulkMeasureLocalizationTermFields interior boundary
  /-- A.e. replacement fields for local bulk integrands. -/
  integrandAE : BulkIntegrandAELocalFields measureTerms
  /-- Compact-support integrability fields. -/
  integrability : CompactSupportIntegrability integrandAE
  /-- Project-local-facing measure-box comparison fields. -/
  projectLocalMeasureBoxAPI : ProjectLocalMeasureBoxAPI measureTerms

namespace ProjectLocalBulkIntegralLocalizationInput

/-- Convert the bundled project-local-facing input to `BulkIntegralLocalizationInput`. -/
def toBulkIntegralLocalizationInput
    (D : ProjectLocalBulkIntegralLocalizationInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    BulkIntegralLocalizationInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece) :=
  D.projectLocalMeasureBoxAPI.toBulkIntegralLocalizationInput
    D.integrandAE D.integrability

@[simp]
theorem toBulkIntegralLocalizationInput_interior
    (D : ProjectLocalBulkIntegralLocalizationInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.toBulkIntegralLocalizationInput.interior = D.interior :=
  rfl

@[simp]
theorem toBulkIntegralLocalizationInput_boundary
    (D : ProjectLocalBulkIntegralLocalizationInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.toBulkIntegralLocalizationInput.boundary = D.boundary :=
  rfl

@[simp]
theorem toBulkIntegralLocalizationInput_measureTerms
    (D : ProjectLocalBulkIntegralLocalizationInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.toBulkIntegralLocalizationInput.measureTerms = D.measureTerms :=
  rfl

/-- The bundled input supplies the exact bulk localization equality. -/
theorem bulkIntegralLocalizes
    (D : ProjectLocalBulkIntegralLocalizationInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.measureTerms.globalBulkIntegral =
      (Finset.sum D.interior.active fun i => D.interior.bulkTerm i) +
        BoundaryPieceFamilyInput.boundaryBulkSum D.boundary :=
  D.toBulkIntegralLocalizationInput.bulkIntegralLocalizes

/-- Construct the existing partition input from the bundled project-local input. -/
def toBulkIntegralPartitionInput
    (D : ProjectLocalBulkIntegralLocalizationInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    BulkIntegralPartitionInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece) :=
  D.toBulkIntegralLocalizationInput.toBulkIntegralPartitionInput

@[simp]
theorem toBulkIntegralPartitionInput_globalBulkIntegral
    (D : ProjectLocalBulkIntegralLocalizationInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.toBulkIntegralPartitionInput.globalBulkIntegral =
      D.measureTerms.globalBulkIntegral :=
  rfl

end ProjectLocalBulkIntegralLocalizationInput

end MeasureBoxProjectLocal

end Stokes

end
