import Stokes.Global.IntegralReconstruction
import Stokes.Global.LocalizedInteriorPieces
import Stokes.Global.BoundaryPieceFamilyConstructor

/-!
# Bulk integral reconstruction from partition-local terms

This file packages the finite local bulk terms that should feed the global
bulk-integral reconstruction layer.  The analytic measure-additivity statement
is still an explicit field, named `bulkIntegralLocalizes`; the rest is finite
bookkeeping that converts separate interior and boundary families into the
existing `BulkIntegralReconstructionData` API.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkIntegralPartitionReconstruction

universe u v w ci cb pi pb

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- Finite sum of the recorded interior bulk terms. -/
def splitInteriorBulkSum {InteriorChart : Type ci} {InteriorPiece : Type pi}
    (activeInteriorCharts : Finset InteriorChart)
    (interiorPieces : InteriorChart → Finset InteriorPiece)
    (interiorBulkTerm : InteriorChart → InteriorPiece → Real) : Real :=
  Finset.sum activeInteriorCharts fun x =>
    Finset.sum (interiorPieces x) fun q => interiorBulkTerm x q

/-- Finite sum of the recorded boundary-chart bulk terms. -/
def splitBoundaryBulkSum {BoundaryChart : Type cb} {BoundaryPiece : Type pb}
    (activeBoundaryCharts : Finset BoundaryChart)
    (boundaryPieces : BoundaryChart → Finset BoundaryPiece)
    (boundaryBulkTerm : BoundaryChart → BoundaryPiece → Real) : Real :=
  Finset.sum activeBoundaryCharts fun x =>
    Finset.sum (boundaryPieces x) fun q => boundaryBulkTerm x q

/-- Total finite split bulk sum, before packaging both sides under one chart type. -/
def splitBulkSum {InteriorChart : Type ci} {BoundaryChart : Type cb}
    {InteriorPiece : Type pi} {BoundaryPiece : Type pb}
    (activeInteriorCharts : Finset InteriorChart)
    (interiorPieces : InteriorChart → Finset InteriorPiece)
    (interiorBulkTerm : InteriorChart → InteriorPiece → Real)
    (activeBoundaryCharts : Finset BoundaryChart)
    (boundaryPieces : BoundaryChart → Finset BoundaryPiece)
    (boundaryBulkTerm : BoundaryChart → BoundaryPiece → Real) : Real :=
  splitInteriorBulkSum activeInteriorCharts interiorPieces interiorBulkTerm +
    splitBoundaryBulkSum activeBoundaryCharts boundaryPieces boundaryBulkTerm

/--
Split bulk reconstruction input.

The two families may use different chart labels and different local-piece
types.  They are combined into one `Sum`-indexed chart family when converted to
`BulkIntegralReconstructionData`.
-/
structure SplitBulkIntegralReconstructionInput {k : Nat}
    (I : ModelWithCorners Real E H) (ω : ManifoldForm I M k)
    (InteriorChart : Type ci) (BoundaryChart : Type cb)
    (InteriorPiece : Type pi) (BoundaryPiece : Type pb) where
  /-- Finite chart labels for the localized interior bulk terms. -/
  activeInteriorCharts : Finset InteriorChart
  /-- Interior local pieces assigned to an interior chart label. -/
  interiorPieces : InteriorChart → Finset InteriorPiece
  /-- Finite chart labels for boundary-chart bulk terms. -/
  activeBoundaryCharts : Finset BoundaryChart
  /-- Boundary-chart local pieces assigned to a boundary chart label. -/
  boundaryPieces : BoundaryChart → Finset BoundaryPiece
  /-- Bulk contribution of an interior local piece. -/
  interiorBulkTerm : InteriorChart → InteriorPiece → Real
  /-- Bulk contribution of a boundary-chart local piece. -/
  boundaryBulkTerm : BoundaryChart → BoundaryPiece → Real
  /-- The global bulk integral represented by these local terms. -/
  globalBulkIntegral : Real
  /--
  Analytic localization/additivity input: the global bulk integral is the sum of
  the finite localized interior and boundary bulk terms.
  -/
  bulkIntegralLocalizes :
    globalBulkIntegral =
      splitBulkSum activeInteriorCharts interiorPieces interiorBulkTerm
        activeBoundaryCharts boundaryPieces boundaryBulkTerm

namespace SplitBulkIntegralReconstructionInput

variable {k : Nat} {I : ModelWithCorners Real E H}
variable {ω : ManifoldForm I M k}
variable {InteriorChart : Type ci} {BoundaryChart : Type cb}
variable {InteriorPiece : Type pi} {BoundaryPiece : Type pb}

/-- The combined chart labels used by `BulkIntegralReconstructionData`. -/
def activeCharts
    (D :
      SplitBulkIntegralReconstructionInput I ω InteriorChart BoundaryChart
        InteriorPiece BoundaryPiece) :
    Finset (InteriorChart ⊕ BoundaryChart) :=
  D.activeInteriorCharts.disjSum D.activeBoundaryCharts

/-- Interior pieces, extended by the empty family on boundary chart labels. -/
def combinedInteriorPieces
    (D :
      SplitBulkIntegralReconstructionInput I ω InteriorChart BoundaryChart
        InteriorPiece BoundaryPiece) :
    InteriorChart ⊕ BoundaryChart → Finset InteriorPiece
  | Sum.inl x => D.interiorPieces x
  | Sum.inr _ => ∅

/-- Boundary pieces, extended by the empty family on interior chart labels. -/
def combinedBoundaryPieces
    (D :
      SplitBulkIntegralReconstructionInput I ω InteriorChart BoundaryChart
        InteriorPiece BoundaryPiece) :
    InteriorChart ⊕ BoundaryChart → Finset BoundaryPiece
  | Sum.inl _ => ∅
  | Sum.inr x => D.boundaryPieces x

/-- Interior bulk terms, extended by `0` on boundary chart labels. -/
def combinedInteriorBulkTerm
    (D :
      SplitBulkIntegralReconstructionInput I ω InteriorChart BoundaryChart
        InteriorPiece BoundaryPiece) :
    InteriorChart ⊕ BoundaryChart → InteriorPiece → Real
  | Sum.inl x, q => D.interiorBulkTerm x q
  | Sum.inr _, _ => 0

/-- Boundary bulk terms, extended by `0` on interior chart labels. -/
def combinedBoundaryBulkTerm
    (D :
      SplitBulkIntegralReconstructionInput I ω InteriorChart BoundaryChart
        InteriorPiece BoundaryPiece) :
    InteriorChart ⊕ BoundaryChart → BoundaryPiece → Real
  | Sum.inl _, _ => 0
  | Sum.inr x, q => D.boundaryBulkTerm x q

/-- The interior part of the combined chart sum is the original interior sum. -/
theorem combinedInteriorBulkSum_eq
    (D :
      SplitBulkIntegralReconstructionInput I ω InteriorChart BoundaryChart
        InteriorPiece BoundaryPiece) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.combinedInteriorPieces x) fun q =>
          D.combinedInteriorBulkTerm x q) =
      splitInteriorBulkSum D.activeInteriorCharts D.interiorPieces
        D.interiorBulkTerm := by
  simp [activeCharts, combinedInteriorPieces, combinedInteriorBulkTerm,
    splitInteriorBulkSum]

/-- The boundary part of the combined chart sum is the original boundary sum. -/
theorem combinedBoundaryBulkSum_eq
    (D :
      SplitBulkIntegralReconstructionInput I ω InteriorChart BoundaryChart
        InteriorPiece BoundaryPiece) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.combinedBoundaryPieces x) fun q =>
          D.combinedBoundaryBulkTerm x q) =
      splitBoundaryBulkSum D.activeBoundaryCharts D.boundaryPieces
        D.boundaryBulkTerm := by
  simp [activeCharts, combinedBoundaryPieces, combinedBoundaryBulkTerm,
    splitBoundaryBulkSum]

/--
The local bulk sum of the combined chart package is exactly the split interior
plus boundary bulk sum.
-/
theorem combinedLocalBulkSum_eq_splitBulkSum
    (D :
      SplitBulkIntegralReconstructionInput I ω InteriorChart BoundaryChart
        InteriorPiece BoundaryPiece) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.combinedInteriorPieces x) fun q =>
          D.combinedInteriorBulkTerm x q) +
      (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.combinedBoundaryPieces x) fun q =>
          D.combinedBoundaryBulkTerm x q) =
      splitBulkSum D.activeInteriorCharts D.interiorPieces D.interiorBulkTerm
        D.activeBoundaryCharts D.boundaryPieces D.boundaryBulkTerm := by
  rw [D.combinedInteriorBulkSum_eq, D.combinedBoundaryBulkSum_eq, splitBulkSum]

/--
Convert split finite bulk terms into the existing bulk reconstruction package.
-/
def toBulkIntegralReconstructionData
    (D :
      SplitBulkIntegralReconstructionInput I ω InteriorChart BoundaryChart
        InteriorPiece BoundaryPiece) :
    BulkIntegralReconstructionData I ω (InteriorChart ⊕ BoundaryChart)
      InteriorPiece BoundaryPiece where
  activeCharts := D.activeCharts
  interiorPieces := D.combinedInteriorPieces
  boundaryPieces := D.combinedBoundaryPieces
  interiorBulkTerm := D.combinedInteriorBulkTerm
  boundaryBulkTerm := D.combinedBoundaryBulkTerm
  globalBulkIntegral := D.globalBulkIntegral
  globalBulkIntegral_eq_localBulkSum := by
    rw [D.combinedLocalBulkSum_eq_splitBulkSum]
    exact D.bulkIntegralLocalizes

@[simp]
theorem toBulkIntegralReconstructionData_globalBulkIntegral
    (D :
      SplitBulkIntegralReconstructionInput I ω InteriorChart BoundaryChart
        InteriorPiece BoundaryPiece) :
    D.toBulkIntegralReconstructionData.globalBulkIntegral =
      D.globalBulkIntegral :=
  rfl

/-- The converted reconstruction package keeps the stated localization sum. -/
theorem toBulkIntegralReconstructionData_globalBulkIntegral_eq_splitBulkSum
    (D :
      SplitBulkIntegralReconstructionInput I ω InteriorChart BoundaryChart
        InteriorPiece BoundaryPiece) :
    D.toBulkIntegralReconstructionData.globalBulkIntegral =
      splitBulkSum D.activeInteriorCharts D.interiorPieces D.interiorBulkTerm
        D.activeBoundaryCharts D.boundaryPieces D.boundaryBulkTerm :=
  D.bulkIntegralLocalizes

end SplitBulkIntegralReconstructionInput

section LocalizedInteriorBoundaryInput

universe ιu

variable {ι : Type ιu}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {BoundaryChart : Type cb} {BoundaryPiece : Type pb}

/--
Natural bulk-reconstruction input from localized interior pieces and a finite
boundary-piece family.

The actual global measure-additivity theorem is recorded as
`bulkIntegralLocalizes`; all other fields are finite data already present in the
local piece packages.
-/
structure BulkIntegralPartitionInput where
  /-- Localized partition-of-unity interior pieces. -/
  interior : LocalizedInteriorPieces (ι := ι) I ω
  /-- Boundary-chart bulk pieces. -/
  boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece
  /-- The global bulk integral represented by these finite local terms. -/
  globalBulkIntegral : Real
  /--
  Global bulk localization/additivity over the chosen finite interior and
  boundary pieces.
  -/
  bulkIntegralLocalizes :
    globalBulkIntegral =
      (Finset.sum interior.active fun i => interior.bulkTerm i) +
        BoundaryPieceFamilyInput.boundaryBulkSum boundary

namespace BulkIntegralPartitionInput

/-- View localized interior pieces as singleton-fiber split bulk terms. -/
def toSplitBulkIntegralReconstructionInput
    (D : BulkIntegralPartitionInput (ι := ι)
      (I := I) (ω := ω) (BoundaryChart := BoundaryChart)
      (BoundaryPiece := BoundaryPiece)) :
    SplitBulkIntegralReconstructionInput I ω ι BoundaryChart Unit BoundaryPiece where
  activeInteriorCharts := D.interior.active
  interiorPieces := fun _ => {()}
  activeBoundaryCharts := D.boundary.activeCharts
  boundaryPieces := D.boundary.boundaryPieces
  interiorBulkTerm := fun i _ => D.interior.bulkTerm i
  boundaryBulkTerm := BoundaryPieceFamilyInput.boundaryBulkTerm D.boundary
  globalBulkIntegral := D.globalBulkIntegral
  bulkIntegralLocalizes := by
    simpa [splitBulkSum, splitInteriorBulkSum, splitBoundaryBulkSum,
      BoundaryPieceFamilyInput.boundaryBulkSum] using D.bulkIntegralLocalizes

/--
Constructor for `BulkIntegralReconstructionData` from localized interior pieces
and finite boundary bulk terms.
-/
def toBulkIntegralReconstructionData
    (D : BulkIntegralPartitionInput (ι := ι)
      (I := I) (ω := ω) (BoundaryChart := BoundaryChart)
      (BoundaryPiece := BoundaryPiece)) :
    BulkIntegralReconstructionData I ω (ι ⊕ BoundaryChart) Unit BoundaryPiece :=
  D.toSplitBulkIntegralReconstructionInput.toBulkIntegralReconstructionData

@[simp]
theorem toBulkIntegralReconstructionData_globalBulkIntegral
    (D : BulkIntegralPartitionInput (ι := ι)
      (I := I) (ω := ω) (BoundaryChart := BoundaryChart)
      (BoundaryPiece := BoundaryPiece)) :
    D.toBulkIntegralReconstructionData.globalBulkIntegral =
      D.globalBulkIntegral :=
  rfl

/-- Expanded localization theorem supplied by `bulkIntegralLocalizes`. -/
theorem globalBulkIntegral_eq_localized_bulk_sum
    (D : BulkIntegralPartitionInput (ι := ι)
      (I := I) (ω := ω) (BoundaryChart := BoundaryChart)
      (BoundaryPiece := BoundaryPiece)) :
    D.globalBulkIntegral =
      (Finset.sum D.interior.active fun i => D.interior.bulkTerm i) +
        BoundaryPieceFamilyInput.boundaryBulkSum D.boundary :=
  D.bulkIntegralLocalizes

/--
The `BulkIntegralReconstructionData` produced by the constructor has the same
expanded localized bulk-sum theorem.
-/
theorem toBulkIntegralReconstructionData_globalBulkIntegral_eq_localized_bulk_sum
    (D : BulkIntegralPartitionInput (ι := ι)
      (I := I) (ω := ω) (BoundaryChart := BoundaryChart)
      (BoundaryPiece := BoundaryPiece)) :
    D.toBulkIntegralReconstructionData.globalBulkIntegral =
      (Finset.sum D.interior.active fun i => D.interior.bulkTerm i) +
        BoundaryPieceFamilyInput.boundaryBulkSum D.boundary :=
  D.bulkIntegralLocalizes

/--
The package-local finite sum in the generated `BulkIntegralReconstructionData`
is the original localized interior sum plus the boundary-piece bulk sum.
-/
theorem localBulkSum_toBulkIntegralReconstructionData
    (D : BulkIntegralPartitionInput (ι := ι)
      (I := I) (ω := ω) (BoundaryChart := BoundaryChart)
      (BoundaryPiece := BoundaryPiece)) :
    BulkIntegralReconstructionData.localBulkSum
        D.toBulkIntegralReconstructionData =
      (Finset.sum D.interior.active fun i => D.interior.bulkTerm i) +
        BoundaryPieceFamilyInput.boundaryBulkSum D.boundary := by
  rw [← D.toBulkIntegralReconstructionData_globalBulkIntegral_eq_localized_bulk_sum]
  exact D.toBulkIntegralReconstructionData.globalBulkIntegral_eq_localBulkSum'.symm

section MeasureReconstruction

universe a

variable {α : Type a} [MeasurableSpace α]
variable {μ : Measure α}

/--
Measure-level reconstruction of the `bulkIntegralLocalizes` field.

This is the exact analytic content behind the finite bookkeeping package:
if the represented global bulk integrand `F` is a.e. the finite sum of the
indicator-localized interior and boundary local integrands, the local terms are
integrable on their selected boxes, and the resulting set integrals are the
already-recorded project-local bulk terms, then the represented global bulk
integral is the finite selected local bulk sum.
-/
theorem bulkIntegralLocalizes_of_measure_indicator_reconstruction
    (interior : LocalizedInteriorPieces (ι := ι) I ω)
    (boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece)
    (globalBulkIntegral : Real)
    (F : α → Real)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (hglobal : globalBulkIntegral = ∫ y, F y ∂μ)
    (hInteriorMeasurable :
      ∀ i, i ∈ interior.active → MeasurableSet (interiorBox i))
    (hBoundaryMeasurable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x → MeasurableSet (boundaryBox x q))
    (hInteriorIntegrable :
      ∀ i, i ∈ interior.active →
        IntegrableOn (interiorLocalTerm i) (interiorBox i) μ)
    (hBoundaryIntegrable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          IntegrableOn (boundaryLocalTerm x q) (boundaryBox x q) μ)
    (hInteriorBulkTerm :
      ∀ i, i ∈ interior.active →
        interior.bulkTerm i = ∫ y in interiorBox i, interiorLocalTerm i y ∂μ)
    (hBoundaryBulkTerm :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ)
    (hF :
      F =ᵐ[μ] fun y =>
        (Finset.sum interior.active fun i =>
          (interiorBox i).indicator (interiorLocalTerm i) y) +
          Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              (boundaryBox x q).indicator (boundaryLocalTerm x q) y) :
    globalBulkIntegral =
      (Finset.sum interior.active fun i => interior.bulkTerm i) +
        BoundaryPieceFamilyInput.boundaryBulkSum boundary := by
  have hInteriorIndicatorIntegrable :
      ∀ i, i ∈ interior.active →
        Integrable ((interiorBox i).indicator (interiorLocalTerm i)) μ := by
    intro i hi
    exact (hInteriorIntegrable i hi).integrable_indicator
      (hInteriorMeasurable i hi)
  have hBoundaryIndicatorIntegrable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          Integrable
            ((boundaryBox x q).indicator (boundaryLocalTerm x q)) μ := by
    intro x hx q hq
    exact (hBoundaryIntegrable x hx q hq).integrable_indicator
      (hBoundaryMeasurable x hx q hq)
  have hInteriorSumIntegrable :
      Integrable
        (fun y =>
          Finset.sum interior.active fun i =>
            (interiorBox i).indicator (interiorLocalTerm i) y) μ := by
    simpa [Finset.sum_apply] using
      integrable_finset_sum interior.active hInteriorIndicatorIntegrable
  have hBoundarySumIntegrable :
      Integrable
        (fun y =>
          Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              (boundaryBox x q).indicator (boundaryLocalTerm x q) y) μ := by
    simpa [Finset.sum_apply] using
      integrable_finset_sum boundary.activeCharts fun x hx =>
        integrable_finset_sum (boundary.boundaryPieces x) fun q hq =>
          hBoundaryIndicatorIntegrable x hx q hq
  have hInteriorIntegral :
      (∫ y,
        (Finset.sum interior.active fun i =>
          (interiorBox i).indicator (interiorLocalTerm i) y) ∂μ) =
        Finset.sum interior.active fun i =>
          ∫ y in interiorBox i, interiorLocalTerm i y ∂μ := by
    calc
      (∫ y,
        (Finset.sum interior.active fun i =>
          (interiorBox i).indicator (interiorLocalTerm i) y) ∂μ) =
          Finset.sum interior.active fun i =>
            ∫ y, (interiorBox i).indicator (interiorLocalTerm i) y ∂μ := by
        simpa [Finset.sum_apply] using
          integral_finset_sum interior.active hInteriorIndicatorIntegrable
      _ =
          Finset.sum interior.active fun i =>
            ∫ y in interiorBox i, interiorLocalTerm i y ∂μ := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [integral_indicator (hInteriorMeasurable i hi)]
  have hBoundaryIntegral :
      (∫ y,
        (Finset.sum boundary.activeCharts fun x =>
          Finset.sum (boundary.boundaryPieces x) fun q =>
            (boundaryBox x q).indicator (boundaryLocalTerm x q) y) ∂μ) =
        Finset.sum boundary.activeCharts fun x =>
          Finset.sum (boundary.boundaryPieces x) fun q =>
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ := by
    calc
      (∫ y,
        (Finset.sum boundary.activeCharts fun x =>
          Finset.sum (boundary.boundaryPieces x) fun q =>
            (boundaryBox x q).indicator (boundaryLocalTerm x q) y) ∂μ) =
          Finset.sum boundary.activeCharts fun x =>
            ∫ y,
              (Finset.sum (boundary.boundaryPieces x) fun q =>
                (boundaryBox x q).indicator (boundaryLocalTerm x q) y) ∂μ := by
        simpa [Finset.sum_apply] using
          integral_finset_sum boundary.activeCharts fun x hx =>
            integrable_finset_sum (boundary.boundaryPieces x) fun q hq =>
              hBoundaryIndicatorIntegrable x hx q hq
      _ =
          Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              ∫ y, (boundaryBox x q).indicator
                (boundaryLocalTerm x q) y ∂μ := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        exact integral_finset_sum (boundary.boundaryPieces x) fun q hq =>
          hBoundaryIndicatorIntegrable x hx q hq
      _ =
          Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        refine Finset.sum_congr rfl ?_
        intro q hq
        rw [integral_indicator (hBoundaryMeasurable x hx q hq)]
  have hSetIntegralSum :
      (∫ y, F y ∂μ) =
        (Finset.sum interior.active fun i =>
          ∫ y in interiorBox i, interiorLocalTerm i y ∂μ) +
          Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ := by
    calc
      (∫ y, F y ∂μ) =
          ∫ y,
            ((Finset.sum interior.active fun i =>
                (interiorBox i).indicator (interiorLocalTerm i) y) +
              Finset.sum boundary.activeCharts fun x =>
                Finset.sum (boundary.boundaryPieces x) fun q =>
                  (boundaryBox x q).indicator (boundaryLocalTerm x q) y) ∂μ :=
        integral_congr_ae hF
      _ =
          (∫ y,
            (Finset.sum interior.active fun i =>
              (interiorBox i).indicator (interiorLocalTerm i) y) ∂μ) +
            ∫ y,
              (Finset.sum boundary.activeCharts fun x =>
                Finset.sum (boundary.boundaryPieces x) fun q =>
                  (boundaryBox x q).indicator (boundaryLocalTerm x q) y) ∂μ := by
        exact integral_add hInteriorSumIntegrable hBoundarySumIntegrable
      _ =
          (Finset.sum interior.active fun i =>
            ∫ y in interiorBox i, interiorLocalTerm i y ∂μ) +
            Finset.sum boundary.activeCharts fun x =>
              Finset.sum (boundary.boundaryPieces x) fun q =>
                ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ := by
        rw [hInteriorIntegral, hBoundaryIntegral]
  calc
    globalBulkIntegral = ∫ y, F y ∂μ := hglobal
    _ =
        (Finset.sum interior.active fun i =>
          ∫ y in interiorBox i, interiorLocalTerm i y ∂μ) +
          Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ :=
      hSetIntegralSum
    _ =
        (Finset.sum interior.active fun i => interior.bulkTerm i) +
          Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q := by
      have hInterior :
          (Finset.sum interior.active fun i =>
            ∫ y in interiorBox i, interiorLocalTerm i y ∂μ) =
            Finset.sum interior.active fun i => interior.bulkTerm i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact (hInteriorBulkTerm i hi).symm
      have hBoundary :
          (Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ) =
            Finset.sum boundary.activeCharts fun x =>
              Finset.sum (boundary.boundaryPieces x) fun q =>
                BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        refine Finset.sum_congr rfl ?_
        intro q hq
        exact (hBoundaryBulkTerm x hx q hq).symm
      rw [hInterior, hBoundary]
    _ =
        (Finset.sum interior.active fun i => interior.bulkTerm i) +
          BoundaryPieceFamilyInput.boundaryBulkSum boundary := by
      rfl

/--
Constructor for `BulkIntegralPartitionInput` from the explicit measure
reconstruction hypotheses of
`bulkIntegralLocalizes_of_measure_indicator_reconstruction`.
-/
def ofMeasureIndicatorReconstruction
    (interior : LocalizedInteriorPieces (ι := ι) I ω)
    (boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece)
    (globalBulkIntegral : Real)
    (F : α → Real)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (hglobal : globalBulkIntegral = ∫ y, F y ∂μ)
    (hInteriorMeasurable :
      ∀ i, i ∈ interior.active → MeasurableSet (interiorBox i))
    (hBoundaryMeasurable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x → MeasurableSet (boundaryBox x q))
    (hInteriorIntegrable :
      ∀ i, i ∈ interior.active →
        IntegrableOn (interiorLocalTerm i) (interiorBox i) μ)
    (hBoundaryIntegrable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          IntegrableOn (boundaryLocalTerm x q) (boundaryBox x q) μ)
    (hInteriorBulkTerm :
      ∀ i, i ∈ interior.active →
        interior.bulkTerm i = ∫ y in interiorBox i, interiorLocalTerm i y ∂μ)
    (hBoundaryBulkTerm :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ)
    (hF :
      F =ᵐ[μ] fun y =>
        (Finset.sum interior.active fun i =>
          (interiorBox i).indicator (interiorLocalTerm i) y) +
          Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              (boundaryBox x q).indicator (boundaryLocalTerm x q) y) :
    BulkIntegralPartitionInput (ι := ι)
      (I := I) (ω := ω) (BoundaryChart := BoundaryChart)
      (BoundaryPiece := BoundaryPiece) where
  interior := interior
  boundary := boundary
  globalBulkIntegral := globalBulkIntegral
  bulkIntegralLocalizes :=
    bulkIntegralLocalizes_of_measure_indicator_reconstruction
      (μ := μ) interior boundary globalBulkIntegral F interiorLocalTerm
      boundaryLocalTerm interiorBox boundaryBox hglobal hInteriorMeasurable
      hBoundaryMeasurable hInteriorIntegrable hBoundaryIntegrable
      hInteriorBulkTerm hBoundaryBulkTerm hF

@[simp]
theorem ofMeasureIndicatorReconstruction_globalBulkIntegral
    (interior : LocalizedInteriorPieces (ι := ι) I ω)
    (boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece)
    (globalBulkIntegral : Real)
    (F : α → Real)
    (interiorLocalTerm : ι → α → Real)
    (boundaryLocalTerm : BoundaryChart → BoundaryPiece → α → Real)
    (interiorBox : ι → Set α)
    (boundaryBox : BoundaryChart → BoundaryPiece → Set α)
    (hglobal : globalBulkIntegral = ∫ y, F y ∂μ)
    (hInteriorMeasurable :
      ∀ i, i ∈ interior.active → MeasurableSet (interiorBox i))
    (hBoundaryMeasurable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x → MeasurableSet (boundaryBox x q))
    (hInteriorIntegrable :
      ∀ i, i ∈ interior.active →
        IntegrableOn (interiorLocalTerm i) (interiorBox i) μ)
    (hBoundaryIntegrable :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          IntegrableOn (boundaryLocalTerm x q) (boundaryBox x q) μ)
    (hInteriorBulkTerm :
      ∀ i, i ∈ interior.active →
        interior.bulkTerm i = ∫ y in interiorBox i, interiorLocalTerm i y ∂μ)
    (hBoundaryBulkTerm :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ)
    (hF :
      F =ᵐ[μ] fun y =>
        (Finset.sum interior.active fun i =>
          (interiorBox i).indicator (interiorLocalTerm i) y) +
          Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              (boundaryBox x q).indicator (boundaryLocalTerm x q) y) :
    (ofMeasureIndicatorReconstruction
      (μ := μ) interior boundary globalBulkIntegral F interiorLocalTerm
      boundaryLocalTerm interiorBox boundaryBox hglobal hInteriorMeasurable
      hBoundaryMeasurable hInteriorIntegrable hBoundaryIntegrable
      hInteriorBulkTerm hBoundaryBulkTerm hF).globalBulkIntegral =
        globalBulkIntegral :=
  rfl

end MeasureReconstruction

end BulkIntegralPartitionInput

end LocalizedInteriorBoundaryInput

end BulkIntegralPartitionReconstruction

end Stokes

end
