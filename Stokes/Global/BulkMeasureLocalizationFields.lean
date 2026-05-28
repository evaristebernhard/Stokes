import Stokes.Global.BulkIntegralPartitionReconstruction
import Stokes.Global.BulkIntegralLocalizationConstructor
import Stokes.Global.MeasureIntegralLocalization

/-!
# Bulk measure localization fields

This file gives a pure measure-theoretic field package for filling
`BulkIntegralPartitionInput.bulkIntegralLocalizes`.

The package records:

* a global bulk integrand `F`,
* interior and boundary local integrand terms,
* localization boxes for those terms,
* measurability and `IntegrableOn` hypotheses for the boxes,
* an a.e. equality of `F` with the finite sum of indicator-localized terms,
* identifications of the local set integrals with the project-local bulk terms.

The analytic step is intentionally independent of the manifold geometry: it is
just finite additivity of Bochner integrals over measurable localization sets.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section PureMeasureBulk

universe a i c p

variable {α : Type a} [MeasurableSpace α]
variable {ι : Type i} {BoundaryChart : Type c} {BoundaryPiece : Type p}

/-- Finite sum of indicator-localized interior bulk terms. -/
def bulkMeasureInteriorIndicatorSum
    (activeInterior : Finset ι)
    (interiorBox : ι → Set α)
    (interiorLocalTerm : ι → α → Real) : α → Real :=
  fun y =>
    Finset.sum activeInterior fun i =>
      (interiorBox i).indicator (interiorLocalTerm i) y

/-- Finite sum of indicator-localized boundary-chart bulk terms. -/
def bulkMeasureBoundaryIndicatorSum
    (activeBoundaryCharts : Finset BoundaryChart)
    (boundaryPieces : BoundaryChart → Finset BoundaryPiece)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real) :
    α → Real :=
  fun y =>
    Finset.sum activeBoundaryCharts fun x =>
      Finset.sum (boundaryPieces x) fun q =>
        (boundaryBox x q).indicator (boundaryLocalTerm x q) y

/--
Finite sum of all indicator-localized bulk terms, split into interior and
boundary-chart families.
-/
def bulkMeasureIndicatorSum
    (activeInterior : Finset ι)
    (activeBoundaryCharts : Finset BoundaryChart)
    (boundaryPieces : BoundaryChart → Finset BoundaryPiece)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real) :
    α → Real :=
  fun y =>
    bulkMeasureInteriorIndicatorSum activeInterior interiorBox
        interiorLocalTerm y +
      bulkMeasureBoundaryIndicatorSum activeBoundaryCharts boundaryPieces
        boundaryBox boundaryLocalTerm y

/--
Pure finite-sum localization for a bulk measure integral, split into interior
and boundary-chart families.

This is the measure-theoretic lemma used by
`BulkIntegralPartitionInput.BulkMeasureLocalizationFields` below.
-/
theorem integral_eq_bulkMeasureSetIntegralSum_of_ae_eq_indicatorSum
    (μ : Measure α)
    (activeInterior : Finset ι)
    (activeBoundaryCharts : Finset BoundaryChart)
    (boundaryPieces : BoundaryChart → Finset BoundaryPiece)
    (F : α → Real)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real)
    (hInteriorMeasurable :
      ∀ i, i ∈ activeInterior → MeasurableSet (interiorBox i))
    (hBoundaryMeasurable :
      ∀ x, x ∈ activeBoundaryCharts →
        ∀ q, q ∈ boundaryPieces x → MeasurableSet (boundaryBox x q))
    (hInteriorIntegrable :
      ∀ i, i ∈ activeInterior →
        IntegrableOn (interiorLocalTerm i) (interiorBox i) μ)
    (hBoundaryIntegrable :
      ∀ x, x ∈ activeBoundaryCharts →
        ∀ q, q ∈ boundaryPieces x →
          IntegrableOn (boundaryLocalTerm x q) (boundaryBox x q) μ)
    (hF :
      F =ᵐ[μ]
        bulkMeasureIndicatorSum activeInterior activeBoundaryCharts
          boundaryPieces interiorBox boundaryBox interiorLocalTerm
          boundaryLocalTerm) :
    (∫ y, F y ∂μ) =
      (Finset.sum activeInterior fun i =>
        ∫ y in interiorBox i, interiorLocalTerm i y ∂μ) +
        Finset.sum activeBoundaryCharts fun x =>
          Finset.sum (boundaryPieces x) fun q =>
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ := by
  have hInteriorIndicatorIntegrable :
      ∀ i, i ∈ activeInterior →
        Integrable ((interiorBox i).indicator (interiorLocalTerm i)) μ := by
    intro i hi
    exact (hInteriorIntegrable i hi).integrable_indicator
      (hInteriorMeasurable i hi)
  have hBoundaryIndicatorIntegrable :
      ∀ x, x ∈ activeBoundaryCharts →
        ∀ q, q ∈ boundaryPieces x →
          Integrable
            ((boundaryBox x q).indicator (boundaryLocalTerm x q)) μ := by
    intro x hx q hq
    exact (hBoundaryIntegrable x hx q hq).integrable_indicator
      (hBoundaryMeasurable x hx q hq)
  have hInteriorSumIntegrable :
      Integrable
        (bulkMeasureInteriorIndicatorSum activeInterior interiorBox
          interiorLocalTerm) μ := by
    simpa [bulkMeasureInteriorIndicatorSum] using
      integrable_finset_sum activeInterior hInteriorIndicatorIntegrable
  have hBoundarySumIntegrable :
      Integrable
        (bulkMeasureBoundaryIndicatorSum activeBoundaryCharts boundaryPieces
          boundaryBox boundaryLocalTerm) μ := by
    simpa [bulkMeasureBoundaryIndicatorSum] using
      integrable_finset_sum activeBoundaryCharts fun x hx =>
        integrable_finset_sum (boundaryPieces x) fun q hq =>
          hBoundaryIndicatorIntegrable x hx q hq
  have hInteriorIntegral :
      (∫ y,
        bulkMeasureInteriorIndicatorSum activeInterior interiorBox
          interiorLocalTerm y ∂μ) =
        Finset.sum activeInterior fun i =>
          ∫ y in interiorBox i, interiorLocalTerm i y ∂μ := by
    calc
      (∫ y,
          bulkMeasureInteriorIndicatorSum activeInterior interiorBox
            interiorLocalTerm y ∂μ) =
          Finset.sum activeInterior fun i =>
            ∫ y, (interiorBox i).indicator (interiorLocalTerm i) y ∂μ := by
        simpa [bulkMeasureInteriorIndicatorSum] using
          integral_finset_sum activeInterior hInteriorIndicatorIntegrable
      _ =
          Finset.sum activeInterior fun i =>
            ∫ y in interiorBox i, interiorLocalTerm i y ∂μ := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [integral_indicator (hInteriorMeasurable i hi)]
  have hBoundaryIntegral :
      (∫ y,
        bulkMeasureBoundaryIndicatorSum activeBoundaryCharts boundaryPieces
          boundaryBox boundaryLocalTerm y ∂μ) =
        Finset.sum activeBoundaryCharts fun x =>
          Finset.sum (boundaryPieces x) fun q =>
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ := by
    calc
      (∫ y,
          bulkMeasureBoundaryIndicatorSum activeBoundaryCharts boundaryPieces
            boundaryBox boundaryLocalTerm y ∂μ) =
          Finset.sum activeBoundaryCharts fun x =>
            ∫ y,
              (Finset.sum (boundaryPieces x) fun q =>
                (boundaryBox x q).indicator (boundaryLocalTerm x q) y) ∂μ := by
        simpa [bulkMeasureBoundaryIndicatorSum] using
          integral_finset_sum activeBoundaryCharts fun x hx =>
            integrable_finset_sum (boundaryPieces x) fun q hq =>
              hBoundaryIndicatorIntegrable x hx q hq
      _ =
          Finset.sum activeBoundaryCharts fun x =>
            Finset.sum (boundaryPieces x) fun q =>
              ∫ y, (boundaryBox x q).indicator
                (boundaryLocalTerm x q) y ∂μ := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        exact integral_finset_sum (boundaryPieces x) fun q hq =>
          hBoundaryIndicatorIntegrable x hx q hq
      _ =
          Finset.sum activeBoundaryCharts fun x =>
            Finset.sum (boundaryPieces x) fun q =>
              ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        refine Finset.sum_congr rfl ?_
        intro q hq
        rw [integral_indicator (hBoundaryMeasurable x hx q hq)]
  calc
    (∫ y, F y ∂μ) =
        ∫ y,
          bulkMeasureIndicatorSum activeInterior activeBoundaryCharts
            boundaryPieces interiorBox boundaryBox interiorLocalTerm
            boundaryLocalTerm y ∂μ :=
      integral_congr_ae hF
    _ =
        ∫ y,
          bulkMeasureInteriorIndicatorSum activeInterior interiorBox
              interiorLocalTerm y +
            bulkMeasureBoundaryIndicatorSum activeBoundaryCharts boundaryPieces
              boundaryBox boundaryLocalTerm y ∂μ := by
      rfl
    _ =
        (∫ y,
          bulkMeasureInteriorIndicatorSum activeInterior interiorBox
            interiorLocalTerm y ∂μ) +
          ∫ y,
            bulkMeasureBoundaryIndicatorSum activeBoundaryCharts boundaryPieces
              boundaryBox boundaryLocalTerm y ∂μ := by
      exact integral_add hInteriorSumIntegrable hBoundarySumIntegrable
    _ =
        (Finset.sum activeInterior fun i =>
          ∫ y in interiorBox i, interiorLocalTerm i y ∂μ) +
          Finset.sum activeBoundaryCharts fun x =>
            Finset.sum (boundaryPieces x) fun q =>
              ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ := by
      rw [hInteriorIntegral, hBoundaryIntegral]

end PureMeasureBulk

section PartitionMeasureFields

universe u w i c p a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type i}
variable {α : Type a} [MeasurableSpace α]
variable {BoundaryChart : Type c} {BoundaryPiece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

namespace BulkIntegralPartitionInput

/--
Measure-theoretic field package that supplies
`BulkIntegralPartitionInput.bulkIntegralLocalizes`.

The fields are deliberately phrased only in terms of a measure space, boxes,
local integrand terms, and a.e. equality of `F` with the finite localized sum.
The final local-term equalities identify the resulting set integrals with the
already recorded project-local bulk terms.
-/
structure BulkMeasureLocalizationFields
    (μ : Measure α)
    (interior : LocalizedInteriorPieces (ι := ι) I ω)
    (boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece)
    (globalBulkIntegral : Real) where
  /-- Global bulk integrand represented by `globalBulkIntegral`. -/
  F : α → Real
  /-- Interior local bulk integrand terms. -/
  interiorLocalTerm : ι → α → Real
  /-- Boundary-chart local bulk integrand terms. -/
  boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real
  /-- Localization box for each interior term. -/
  interiorBox : ι → Set α
  /-- Localization box for each boundary-chart term. -/
  boundaryBox : BoundaryChart → BoundaryPiece → Set α
  /-- The represented global bulk integral is the integral of `F`. -/
  globalBulkIntegral_eq_integral :
    globalBulkIntegral = ∫ y, F y ∂μ
  /-- Measurability of every active interior localization box. -/
  interiorBox_measurable :
    ∀ i, i ∈ interior.active → MeasurableSet (interiorBox i)
  /-- Measurability of every active boundary-piece localization box. -/
  boundaryBox_measurable :
    ∀ x, x ∈ boundary.activeCharts →
      ∀ q, q ∈ boundary.boundaryPieces x → MeasurableSet (boundaryBox x q)
  /-- Integrability of every active interior local term on its box. -/
  interiorIntegrableOn :
    ∀ i, i ∈ interior.active →
      IntegrableOn (interiorLocalTerm i) (interiorBox i) μ
  /-- Integrability of every active boundary local term on its box. -/
  boundaryIntegrableOn :
    ∀ x, x ∈ boundary.activeCharts →
      ∀ q, q ∈ boundary.boundaryPieces x →
        IntegrableOn (boundaryLocalTerm x q) (boundaryBox x q) μ
  /-- Each active interior set integral is the recorded project-local bulk term. -/
  interiorBulkTerm_eq_integral :
    ∀ i, i ∈ interior.active →
      interior.bulkTerm i = ∫ y in interiorBox i, interiorLocalTerm i y ∂μ
  /-- Each active boundary set integral is the recorded project-local bulk term. -/
  boundaryBulkTerm_eq_integral :
    ∀ x, x ∈ boundary.activeCharts →
      ∀ q, q ∈ boundary.boundaryPieces x →
        BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
          ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ
  /-- A.e. reconstruction of `F` from the finite indicator-localized terms. -/
  F_ae_eq_indicatorSum :
    F =ᵐ[μ]
      bulkMeasureIndicatorSum interior.active boundary.activeCharts
        boundary.boundaryPieces interiorBox boundaryBox interiorLocalTerm
        boundaryLocalTerm

namespace BulkMeasureLocalizationFields

variable {μ : Measure α}
variable {interior : LocalizedInteriorPieces (ι := ι) I ω}
variable {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
variable {globalBulkIntegral : Real}

/-- Integral form of the pure measure localization theorem for the field pack. -/
theorem integral_eq_local_setIntegral_sum
    (D :
      BulkMeasureLocalizationFields (α := α) μ interior boundary
        globalBulkIntegral) :
    (∫ y, D.F y ∂μ) =
      (Finset.sum interior.active fun i =>
        ∫ y in D.interiorBox i, D.interiorLocalTerm i y ∂μ) +
        Finset.sum boundary.activeCharts fun x =>
          Finset.sum (boundary.boundaryPieces x) fun q =>
            ∫ y in D.boundaryBox x q, D.boundaryLocalTerm x q y ∂μ :=
  integral_eq_bulkMeasureSetIntegralSum_of_ae_eq_indicatorSum μ
    interior.active boundary.activeCharts boundary.boundaryPieces D.F
    D.interiorBox D.boundaryBox D.interiorLocalTerm D.boundaryLocalTerm
    D.interiorBox_measurable D.boundaryBox_measurable D.interiorIntegrableOn
    D.boundaryIntegrableOn D.F_ae_eq_indicatorSum

/--
The measure fields fill the exact
`BulkIntegralPartitionInput.bulkIntegralLocalizes` equality.
-/
theorem bulkIntegralLocalizes
    (D :
      BulkMeasureLocalizationFields (α := α) μ interior boundary
        globalBulkIntegral) :
    globalBulkIntegral =
      (Finset.sum interior.active fun i => interior.bulkTerm i) +
        BoundaryPieceFamilyInput.boundaryBulkSum boundary := by
  calc
    globalBulkIntegral = ∫ y, D.F y ∂μ :=
      D.globalBulkIntegral_eq_integral
    _ =
        (Finset.sum interior.active fun i =>
          ∫ y in D.interiorBox i, D.interiorLocalTerm i y ∂μ) +
          Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              ∫ y in D.boundaryBox x q, D.boundaryLocalTerm x q y ∂μ :=
      D.integral_eq_local_setIntegral_sum
    _ =
        (Finset.sum interior.active fun i => interior.bulkTerm i) +
          Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q := by
      have hinterior :
          (Finset.sum interior.active fun i =>
            ∫ y in D.interiorBox i, D.interiorLocalTerm i y ∂μ) =
            Finset.sum interior.active fun i => interior.bulkTerm i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact (D.interiorBulkTerm_eq_integral i hi).symm
      have hboundary :
          (Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              ∫ y in D.boundaryBox x q,
                D.boundaryLocalTerm x q y ∂μ) =
            Finset.sum boundary.activeCharts fun x =>
              Finset.sum (boundary.boundaryPieces x) fun q =>
                BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        refine Finset.sum_congr rfl ?_
        intro q hq
        exact (D.boundaryBulkTerm_eq_integral x hx q hq).symm
      rw [hinterior, hboundary]
    _ =
        (Finset.sum interior.active fun i => interior.bulkTerm i) +
          BoundaryPieceFamilyInput.boundaryBulkSum boundary := by
      rfl

/--
Construct `BulkIntegralPartitionInput` from the pure measure-localization
field package.
-/
def toBulkIntegralPartitionInput
    (D :
      BulkMeasureLocalizationFields (α := α) μ interior boundary
        globalBulkIntegral) :
    BulkIntegralPartitionInput (ι := ι)
      (I := I) (ω := ω) (BoundaryChart := BoundaryChart)
      (BoundaryPiece := BoundaryPiece) where
  interior := interior
  boundary := boundary
  globalBulkIntegral := globalBulkIntegral
  bulkIntegralLocalizes := D.bulkIntegralLocalizes

@[simp]
theorem toBulkIntegralPartitionInput_globalBulkIntegral
    (D :
      BulkMeasureLocalizationFields (α := α) μ interior boundary
        globalBulkIntegral) :
    D.toBulkIntegralPartitionInput.globalBulkIntegral = globalBulkIntegral :=
  rfl

end BulkMeasureLocalizationFields

end BulkIntegralPartitionInput

section ConstructorInputBridge

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type i}
variable {BoundaryChart : Type c} {BoundaryPiece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/--
Bundled input for the bulk measure-localization constructor.

This is a thin adapter around `BulkIntegralLocalizationInput`, kept in this
measure-localization file so assembly code can hand off the four analytic
packages by name:

* `measureTerms`,
* `integrandAE`,
* `integrability`,
* `measureBoxAPI`.
-/
structure BulkMeasureLocalizationConstructorFields where
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
  /-- Box-identification fields connecting analytic terms to project-local boxes. -/
  measureBoxAPI : MeasureBoxAPI integrandAE

namespace BulkMeasureLocalizationConstructorFields

/--
Forget the local wrapper and produce the constructor input consumed by
`BulkIntegralLocalizationConstructor`.
-/
def toBulkIntegralLocalizationInput
    (D : BulkMeasureLocalizationConstructorFields
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    BulkIntegralLocalizationInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece) where
  interior := D.interior
  boundary := D.boundary
  measureTerms := D.measureTerms
  integrandAE := D.integrandAE
  integrability := D.integrability
  measureBoxAPI := D.measureBoxAPI

@[simp]
theorem toBulkIntegralLocalizationInput_interior
    (D : BulkMeasureLocalizationConstructorFields
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.toBulkIntegralLocalizationInput.interior = D.interior :=
  rfl

@[simp]
theorem toBulkIntegralLocalizationInput_boundary
    (D : BulkMeasureLocalizationConstructorFields
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.toBulkIntegralLocalizationInput.boundary = D.boundary :=
  rfl

@[simp]
theorem toBulkIntegralLocalizationInput_measureTerms
    (D : BulkMeasureLocalizationConstructorFields
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.toBulkIntegralLocalizationInput.measureTerms = D.measureTerms :=
  rfl

@[simp]
theorem toBulkIntegralLocalizationInput_integrandAE
    (D : BulkMeasureLocalizationConstructorFields
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.toBulkIntegralLocalizationInput.integrandAE = D.integrandAE :=
  rfl

@[simp]
theorem toBulkIntegralLocalizationInput_integrability
    (D : BulkMeasureLocalizationConstructorFields
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.toBulkIntegralLocalizationInput.integrability = D.integrability :=
  rfl

@[simp]
theorem toBulkIntegralLocalizationInput_measureBoxAPI
    (D : BulkMeasureLocalizationConstructorFields
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.toBulkIntegralLocalizationInput.measureBoxAPI = D.measureBoxAPI :=
  rfl

/-- The bundled fields supply the exact bulk localization equality. -/
theorem bulkIntegralLocalizes
    (D : BulkMeasureLocalizationConstructorFields
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.measureTerms.globalBulkIntegral =
      (Finset.sum D.interior.active fun i => D.interior.bulkTerm i) +
        BoundaryPieceFamilyInput.boundaryBulkSum D.boundary :=
  D.toBulkIntegralLocalizationInput.bulkIntegralLocalizes

/-- Construct the existing partition input from the bundled fields. -/
def toBulkIntegralPartitionInput
    (D : BulkMeasureLocalizationConstructorFields
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    BulkIntegralPartitionInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece) :=
  D.toBulkIntegralLocalizationInput.toBulkIntegralPartitionInput

/-- Construct the existing bulk reconstruction package from the bundled fields. -/
def toBulkIntegralReconstructionData
    (D : BulkMeasureLocalizationConstructorFields
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    BulkIntegralReconstructionData I ω (ι ⊕ BoundaryChart) Unit BoundaryPiece :=
  D.toBulkIntegralLocalizationInput.toBulkIntegralReconstructionData

/--
Construct the natural-measure bulk localization fields from the bundled
constructor fields.
-/
def toBulkMeasureLocalizationFields
    (D : BulkMeasureLocalizationConstructorFields
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    BulkMeasureLocalizationFields D.toBulkIntegralReconstructionData :=
  D.toBulkIntegralLocalizationInput.toBulkMeasureLocalizationFields

@[simp]
theorem toBulkIntegralPartitionInput_globalBulkIntegral
    (D : BulkMeasureLocalizationConstructorFields
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.toBulkIntegralPartitionInput.globalBulkIntegral =
      D.measureTerms.globalBulkIntegral :=
  rfl

@[simp]
theorem toBulkIntegralReconstructionData_globalBulkIntegral
    (D : BulkMeasureLocalizationConstructorFields
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.toBulkIntegralReconstructionData.globalBulkIntegral =
      D.measureTerms.globalBulkIntegral :=
  rfl

@[simp]
theorem toBulkMeasureLocalizationFields_bulkMeasureIntegral
    (D : BulkMeasureLocalizationConstructorFields
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.toBulkMeasureLocalizationFields.bulkMeasureIntegral =
      D.measureTerms.bulkMeasureIntegral :=
  rfl

end BulkMeasureLocalizationConstructorFields

end ConstructorInputBridge

end PartitionMeasureFields

end Stokes

end
