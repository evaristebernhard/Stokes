import Stokes.HalfSpace.Faces
import Stokes.Global.BulkIntegrandAE
import Stokes.Global.BulkIntegralPartitionReconstruction

/-!
# Measurability wrappers for coordinate boxes

This module records small project-local names for the measurable sets that
show up in the measure-localization layer: closed coordinate boxes, boundary
face domains, and the half-space support box used to remove artificial faces.
All analytic content is delegated to mathlib's Borel measurability API.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace Stokes

universe u w ιu cb pb

/-- Closed order boxes are measurable in spaces where closed intervals are
Borel-measurable. -/
theorem measurableSet_Icc_box {E : Type u} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [Preorder E] [OrderClosedTopology E] (a b : E) :
    MeasurableSet (Set.Icc a b) :=
  measurableSet_Icc

/-- A coordinate face domain is a measurable closed box. -/
theorem measurableSet_faceDomain {n : Nat} (i : Fin (n + 1))
    (a b : Fin (n + 1) → Real) :
    MeasurableSet (faceDomain i a b) := by
  simp [faceDomain]

/-- The lower zero face domain is a measurable closed box. -/
theorem measurableSet_lowerZeroFaceDomain {n : Nat}
    (a b : Fin (n + 1) → Real) :
    MeasurableSet (lowerZeroFaceDomain a b) := by
  simpa [lowerZeroFaceDomain] using
    (measurableSet_faceDomain (0 : Fin (n + 1)) a b)

/-- The half-space support box used by selected boundary boxes is measurable. -/
theorem measurableSet_halfSpaceSupportBox {n : Nat}
    (a b : Fin (n + 1) → Real) :
    MeasurableSet (halfSpaceSupportBox a b) := by
  classical
  have h0lower : MeasurableSet {y : Fin (n + 1) → Real | a 0 ≤ y 0} := by
    exact measurableSet_le measurable_const
      (continuous_apply (0 : Fin (n + 1))).measurable
  have h0upper : MeasurableSet {y : Fin (n + 1) → Real | y 0 < b 0} := by
    exact measurableSet_lt (continuous_apply (0 : Fin (n + 1))).measurable
      measurable_const
  have hsucc :
      ∀ i : Fin n,
        MeasurableSet {y : Fin (n + 1) → Real |
          a i.succ < y i.succ ∧ y i.succ < b i.succ} := by
    intro i
    have hlower : MeasurableSet {y : Fin (n + 1) → Real | a i.succ < y i.succ} := by
      exact measurableSet_lt measurable_const (continuous_apply i.succ).measurable
    have hupper : MeasurableSet {y : Fin (n + 1) → Real | y i.succ < b i.succ} := by
      exact measurableSet_lt (continuous_apply i.succ).measurable measurable_const
    simpa [Set.setOf_and] using hlower.inter hupper
  have hall :
      MeasurableSet {y : Fin (n + 1) → Real |
        ∀ i : Fin n, a i.succ < y i.succ ∧ y i.succ < b i.succ} := by
    simpa [Set.setOf_forall] using (MeasurableSet.iInter hsucc)
  simpa [halfSpaceSupportBox, Set.setOf_and] using
    h0lower.inter (h0upper.inter hall)

section MeasureBoxTermIdentifications

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type ιu}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {BoundaryChart : Type cb} {BoundaryPiece : Type pb}

/--
Measure-local terms for the bulk localization proof.

This is the scalar output expected from the pure measure-localization layer
before those scalar terms are identified with the project-local box terms.
-/
structure BulkMeasureLocalizationTermFields
    (interior : LocalizedInteriorPieces (ι := ι) I ω)
    (boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece) where
  /-- The represented global bulk integral. -/
  globalBulkIntegral : Real
  /-- The measure-theoretic bulk integral used as the localization source. -/
  bulkMeasureIntegral : Real
  /-- Measure-local term for one active localized interior piece. -/
  interiorMeasureTerm : ι → Real
  /-- Measure-local term for one active boundary-chart piece. -/
  boundaryMeasureTerm : BoundaryChart → BoundaryPiece → Real
  /-- The represented global bulk integral agrees with the measure integral. -/
  globalBulkIntegral_eq_bulkMeasureIntegral :
    globalBulkIntegral = bulkMeasureIntegral
  /-- The measure integral is the finite sum of the localized measure terms. -/
  bulkMeasureIntegral_eq_measureSum :
    bulkMeasureIntegral =
      (Finset.sum interior.active fun i => interiorMeasureTerm i) +
        Finset.sum boundary.activeCharts fun x =>
          Finset.sum (boundary.boundaryPieces x) fun q =>
            boundaryMeasureTerm x q

/--
A.e. bulk-integrand replacement fields for local bulk terms.

The equality fields are the local integral consequences that identify
measure-local terms with the corresponding integrand-local terms.
-/
structure BulkIntegrandAELocalFields
    {interior : LocalizedInteriorPieces (ι := ι) I ω}
    {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
    (measureTerms : BulkMeasureLocalizationTermFields interior boundary) where
  /-- Chartwise a.e. equality package for the combined chart labels. -/
  aeData : BulkIntegrandAEData I ω (ι ⊕ BoundaryChart)
  /-- The a.e. package uses the combined active interior and boundary labels. -/
  aeData_active :
    aeData.activeCharts = interior.active.disjSum boundary.activeCharts
  /-- Integrand-local term for one active localized interior piece. -/
  interiorIntegrandTerm : ι → Real
  /-- Integrand-local term for one active boundary-chart piece. -/
  boundaryIntegrandTerm : BoundaryChart → BoundaryPiece → Real
  /-- The measure-local interior term equals the corresponding integrand-local term. -/
  interiorMeasureTerm_eq_integrandTerm :
    ∀ i, i ∈ interior.active →
      measureTerms.interiorMeasureTerm i = interiorIntegrandTerm i
  /-- The measure-local boundary term equals the corresponding integrand-local term. -/
  boundaryMeasureTerm_eq_integrandTerm :
    ∀ x, x ∈ boundary.activeCharts →
      ∀ q, q ∈ boundary.boundaryPieces x →
        measureTerms.boundaryMeasureTerm x q = boundaryIntegrandTerm x q

/--
Compact-support integrability fields for the bulk localization proof.

The fields are phrased using the chartwise scalar bulk integrands from
`BulkIntegrandAE.lean`, so later analytic workers can instantiate them without
changing the constructor layer.
-/
structure CompactSupportIntegrability
    {interior : LocalizedInteriorPieces (ι := ι) I ω}
    {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
    {measureTerms : BulkMeasureLocalizationTermFields interior boundary}
    (ae : BulkIntegrandAELocalFields measureTerms) where
  /-- Integrability of each active localized interior bulk integrand. -/
  interiorIntegrable :
    ∀ i, i ∈ interior.active →
      Integrable
        (bulkIntegrand I (interior.piece i).sourceChart
          (interior.piece i).targetChart (interior.piece i).localizedForm)
        (ae.aeData.measure (interior.piece i).sourceChart
          (interior.piece i).targetChart)
  /-- Integrability of each active boundary-chart bulk integrand. -/
  boundaryIntegrable :
    ∀ x, x ∈ boundary.activeCharts →
      ∀ q, q ∈ boundary.boundaryPieces x →
        Integrable
          (bulkIntegrand I (boundary.sourceChart x q)
            (boundary.boundarySourceChart x q) ω)
          (ae.aeData.measure (boundary.sourceChart x q)
            (boundary.boundarySourceChart x q))

/--
Box-identification fields for local bulk terms.

This is the constructor-facing bridge from analytic local terms to the
project-local box terms already recorded by `LocalizedInteriorPieces` and
`BoundaryPieceFamilyInput`.
-/
structure MeasureBoxAPI
    {interior : LocalizedInteriorPieces (ι := ι) I ω}
    {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
    {measureTerms : BulkMeasureLocalizationTermFields interior boundary}
    (ae : BulkIntegrandAELocalFields measureTerms) where
  /-- Interior integrand terms agree with the existing project-local bulk terms. -/
  interiorIntegrandTerm_eq_boxTerm :
    ∀ i, i ∈ interior.active →
      ae.interiorIntegrandTerm i = interior.bulkTerm i
  /-- Boundary integrand terms agree with the existing project-local bulk terms. -/
  boundaryIntegrandTerm_eq_boxTerm :
    ∀ x, x ∈ boundary.activeCharts →
      ∀ q, q ∈ boundary.boundaryPieces x →
        ae.boundaryIntegrandTerm x q =
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q

/--
Explicit measure-box identification package.

This is the small analytic handoff that remains after the pure measure
localization theorem has produced scalar local measure terms: every active
measure-local box term must be identified with the project-local bulk term
already used by the global Stokes assembly.
-/
structure MeasureLocalBoxTermAPI
    {interior : LocalizedInteriorPieces (ι := ι) I ω}
    {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
    (measureTerms : BulkMeasureLocalizationTermFields interior boundary) where
  /-- Active interior measure-local terms are the recorded project-local box terms. -/
  interiorMeasureTerm_eq_boxTerm :
    ∀ i, i ∈ interior.active →
      measureTerms.interiorMeasureTerm i = interior.bulkTerm i
  /-- Active boundary-piece measure-local terms are the recorded project-local box terms. -/
  boundaryMeasureTerm_eq_boxTerm :
    ∀ x, x ∈ boundary.activeCharts →
      ∀ q, q ∈ boundary.boundaryPieces x →
        measureTerms.boundaryMeasureTerm x q =
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q

namespace MeasureLocalBoxTermAPI

variable {interior : LocalizedInteriorPieces (ι := ι) I ω}
variable {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
variable {measureTerms : BulkMeasureLocalizationTermFields interior boundary}

/-- Named projection for interior measure-box/project-local identification. -/
theorem interior_eq
    (D : MeasureLocalBoxTermAPI measureTerms) {i : ι}
    (hi : i ∈ interior.active) :
    measureTerms.interiorMeasureTerm i = interior.bulkTerm i :=
  D.interiorMeasureTerm_eq_boxTerm i hi

/-- Named projection for boundary measure-box/project-local identification. -/
theorem boundary_eq
    (D : MeasureLocalBoxTermAPI measureTerms) {x : BoundaryChart}
    (hx : x ∈ boundary.activeCharts) {q : BoundaryPiece}
    (hq : q ∈ boundary.boundaryPieces x) :
    measureTerms.boundaryMeasureTerm x q =
      BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q :=
  D.boundaryMeasureTerm_eq_boxTerm x hx q hq

/--
The direct measure-box identifications fill the bulk-localization equality,
without routing through the intermediate integrand-local terms.
-/
theorem bulkIntegralLocalizes
    (D : MeasureLocalBoxTermAPI measureTerms) :
    measureTerms.globalBulkIntegral =
      (Finset.sum interior.active fun i => interior.bulkTerm i) +
        BoundaryPieceFamilyInput.boundaryBulkSum boundary := by
  calc
    measureTerms.globalBulkIntegral = measureTerms.bulkMeasureIntegral :=
      measureTerms.globalBulkIntegral_eq_bulkMeasureIntegral
    _ =
        (Finset.sum interior.active fun i => measureTerms.interiorMeasureTerm i) +
          Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              measureTerms.boundaryMeasureTerm x q :=
      measureTerms.bulkMeasureIntegral_eq_measureSum
    _ =
        (Finset.sum interior.active fun i => interior.bulkTerm i) +
          Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q := by
      have hinterior :
          (Finset.sum interior.active fun i => measureTerms.interiorMeasureTerm i) =
            Finset.sum interior.active fun i => interior.bulkTerm i :=
        Finset.sum_congr rfl fun i hi => D.interior_eq hi
      have hboundary :
          (Finset.sum boundary.activeCharts fun x =>
              Finset.sum (boundary.boundaryPieces x) fun q =>
                measureTerms.boundaryMeasureTerm x q) =
            Finset.sum boundary.activeCharts fun x =>
              Finset.sum (boundary.boundaryPieces x) fun q =>
                BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q :=
        Finset.sum_congr rfl fun x hx =>
          Finset.sum_congr rfl fun q hq => D.boundary_eq hx hq
      rw [hinterior, hboundary]
    _ =
        (Finset.sum interior.active fun i => interior.bulkTerm i) +
          BoundaryPieceFamilyInput.boundaryBulkSum boundary := by
      rfl

/--
Turn direct measure-box identifications into the constructor-level
`MeasureBoxAPI` by using the a.e. package's equality between measure-local and
integrand-local terms.
-/
def toMeasureBoxAPI
    (D : MeasureLocalBoxTermAPI measureTerms)
    (ae : BulkIntegrandAELocalFields measureTerms) :
    MeasureBoxAPI ae where
  interiorIntegrandTerm_eq_boxTerm := by
    intro i hi
    calc
      ae.interiorIntegrandTerm i = measureTerms.interiorMeasureTerm i :=
        (ae.interiorMeasureTerm_eq_integrandTerm i hi).symm
      _ = interior.bulkTerm i := D.interior_eq hi
  boundaryIntegrandTerm_eq_boxTerm := by
    intro x hx q hq
    calc
      ae.boundaryIntegrandTerm x q = measureTerms.boundaryMeasureTerm x q :=
        (ae.boundaryMeasureTerm_eq_integrandTerm x hx q hq).symm
      _ = BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q :=
        D.boundary_eq hx hq

/-- Directly construct the existing partition input from measure-box terms. -/
def toBulkIntegralPartitionInput
    (D : MeasureLocalBoxTermAPI measureTerms) :
    BulkIntegralPartitionInput (ι := ι)
      (I := I) (ω := ω) (BoundaryChart := BoundaryChart)
      (BoundaryPiece := BoundaryPiece) where
  interior := interior
  boundary := boundary
  globalBulkIntegral := measureTerms.globalBulkIntegral
  bulkIntegralLocalizes := D.bulkIntegralLocalizes

@[simp]
theorem toBulkIntegralPartitionInput_globalBulkIntegral
    (D : MeasureLocalBoxTermAPI measureTerms) :
    D.toBulkIntegralPartitionInput.globalBulkIntegral =
      measureTerms.globalBulkIntegral :=
  rfl

end MeasureLocalBoxTermAPI

namespace MeasureBoxAPI

variable {interior : LocalizedInteriorPieces (ι := ι) I ω}
variable {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
variable {measureTerms : BulkMeasureLocalizationTermFields interior boundary}
variable {ae : BulkIntegrandAELocalFields measureTerms}

/--
The constructor-level `MeasureBoxAPI`, together with the a.e. local-term
replacement fields, also gives direct interior measure-box/project-local
identification.
-/
theorem interiorMeasureTerm_eq_boxTerm
    (D : MeasureBoxAPI ae) {i : ι} (hi : i ∈ interior.active) :
    measureTerms.interiorMeasureTerm i = interior.bulkTerm i := by
  calc
    measureTerms.interiorMeasureTerm i = ae.interiorIntegrandTerm i :=
      ae.interiorMeasureTerm_eq_integrandTerm i hi
    _ = interior.bulkTerm i := D.interiorIntegrandTerm_eq_boxTerm i hi

/--
The constructor-level `MeasureBoxAPI`, together with the a.e. local-term
replacement fields, also gives direct boundary measure-box/project-local
identification.
-/
theorem boundaryMeasureTerm_eq_boxTerm
    (D : MeasureBoxAPI ae) {x : BoundaryChart}
    (hx : x ∈ boundary.activeCharts) {q : BoundaryPiece}
    (hq : q ∈ boundary.boundaryPieces x) :
    measureTerms.boundaryMeasureTerm x q =
      BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q := by
  calc
    measureTerms.boundaryMeasureTerm x q = ae.boundaryIntegrandTerm x q :=
      ae.boundaryMeasureTerm_eq_integrandTerm x hx q hq
    _ = BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q :=
      D.boundaryIntegrandTerm_eq_boxTerm x hx q hq

/-- Forget a constructor-level `MeasureBoxAPI` to direct measure-box data. -/
def toMeasureLocalBoxTermAPI
    (D : MeasureBoxAPI ae) :
    MeasureLocalBoxTermAPI measureTerms where
  interiorMeasureTerm_eq_boxTerm := by
    intro i hi
    exact D.interiorMeasureTerm_eq_boxTerm hi
  boundaryMeasureTerm_eq_boxTerm := by
    intro x hx q hq
    exact D.boundaryMeasureTerm_eq_boxTerm hx hq

end MeasureBoxAPI

end MeasureBoxTermIdentifications

end Stokes

end
