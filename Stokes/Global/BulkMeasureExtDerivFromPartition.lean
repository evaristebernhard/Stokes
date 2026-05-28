import Stokes.Global.BulkCompactSupportIntegrabilityToMeasure
import Stokes.Global.BulkIntegrandAEFromPartition
import Stokes.Global.BulkMeasurePartitionLocalizationWrappers

/-!
# Bulk measure data from partition exterior derivatives

This file is the first constructive bridge from the partition/ext-derivative
route to the selected bulk-measure package.

The current project has two complementary APIs:

* `BulkIntegrandAEFromPartitionData`, which records the genuine chartwise
  exterior-derivative a.e. comparison coming from partition reconstruction;
* `BulkMeasureFromPartitionData`, which is the selected-partition measure
  package consumed downstream by M8/global builders.

The definitions below fix the canonical scalar integrand shape for the latter:
each local scalar term is the chartwise `bulkIntegrand` of the corresponding
localized interior or boundary piece, and the global scalar integrand is their
selected finite sum.  The remaining measure-theoretic facts (measurable boxes,
compact support, support-in-box, and set-integral identifications) are kept as
fields of `SelectedPartitionBulkMeasureExtDerivInput`; no measure theorem is
asserted without proof.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section SelectedPartitionBulkMeasureExtDeriv

universe u w b ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {P : SelectedBoxPartitionOfUnity I omega}
variable {boundary : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {μ : Measure (Fin (n + 1) → Real)}
variable [IsFiniteMeasureOnCompacts μ]

/--
The canonical scalar bulk integrand for one selected interior chart piece.

It is exactly the top-degree exterior derivative of the localized form in the
piece's source/target chart pair.
-/
def selectedPartitionInteriorBulkScalarTerm
    (localized : LocalizedInteriorM8Fields I omega P) :
    M → (Fin (n + 1) → Real) → Real :=
  fun i =>
    let piece := localized.localizedInterior.piece i
    bulkIntegrand I piece.sourceChart piece.targetChart piece.localizedForm

/--
The canonical scalar bulk integrand for one selected boundary source piece.

The boundary bulk side is computed in the source chart and shared boundary
source chart carried by `BoundaryPieceFamilyInput`.
-/
def selectedPartitionBoundaryBulkScalarTerm
    (boundary : BoundaryPieceFamilyInput I omega M BoundaryPiece) :
    M → BoundaryPiece → (Fin (n + 1) → Real) → Real :=
  fun x q =>
    bulkIntegrand I (boundary.sourceChart x q) (boundary.boundarySourceChart x q)
      omega

/--
The selected finite-sum scalar bulk integrand induced by the localized
interior pieces and boundary source pieces.
-/
def selectedPartitionBulkScalarIntegrand
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundary : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (localized : LocalizedInteriorM8Fields I omega P) :
    (Fin (n + 1) → Real) → Real :=
  bulkMeasureUnlocalizedSum P.active P.active boundary.boundaryPieces
    (selectedPartitionInteriorBulkScalarTerm localized)
    (selectedPartitionBoundaryBulkScalarTerm boundary)

@[simp]
theorem selectedPartitionBulkScalarIntegrand_eq_unlocalizedSum
    (localized : LocalizedInteriorM8Fields I omega P) :
    selectedPartitionBulkScalarIntegrand P boundary localized =
      bulkMeasureUnlocalizedSum P.active P.active boundary.boundaryPieces
        (selectedPartitionInteriorBulkScalarTerm localized)
        (selectedPartitionBoundaryBulkScalarTerm boundary) :=
  rfl

theorem selectedPartitionBulkScalarIntegrand_pointwise_eq_unlocalizedSum
    (localized : LocalizedInteriorM8Fields I omega P)
    (y : Fin (n + 1) → Real) :
    selectedPartitionBulkScalarIntegrand P boundary localized y =
      bulkMeasureUnlocalizedSum P.active P.active boundary.boundaryPieces
        (selectedPartitionInteriorBulkScalarTerm localized)
        (selectedPartitionBoundaryBulkScalarTerm boundary) y :=
  rfl

/--
Minimal input that turns partition/ext-derivative data into selected bulk
measure data.

The `extDerivAE` field is the real exterior-derivative reconstruction side.
The remaining fields are exactly the measure hypotheses still needed to produce
`BulkMeasureFromPartitionData` with the canonical scalar integrands above.
-/
structure SelectedPartitionBulkMeasureExtDerivInput
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundary : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (μ : Measure (Fin (n + 1) → Real)) where
  /-- Localized interior package aligned with the selected partition. -/
  localized : LocalizedInteriorM8Fields I omega P
  /-- Boundary source pieces use the same selected active charts. -/
  boundary_active : boundary.activeCharts = P.active
  /-- Scalar measure terms used by the ext-derivative/bulk localization route. -/
  measureTerms :
    BulkMeasureLocalizationTermFields localized.localizedInterior boundary
  /-- Partition exterior-derivative a.e. reconstruction for these selected pieces. -/
  extDerivAE :
    BulkIntegrandAEFromPartitionData
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      P boundary localized measureTerms
  /-- Compact support and continuity of the canonical scalar local terms. -/
  compactSupport :
    BulkLocalTermCompactSupportData
      (α := Fin (n + 1) → Real)
      localized.localizedInterior boundary
      (selectedPartitionInteriorBulkScalarTerm localized)
      (selectedPartitionBoundaryBulkScalarTerm boundary)
  /-- Localization box for each selected interior scalar term. -/
  interiorBox : M → Set (Fin (n + 1) → Real)
  /-- Localization box for each selected boundary scalar term. -/
  boundaryBox : M → BoundaryPiece → Set (Fin (n + 1) → Real)
  /-- The represented global bulk integral is the integral of the canonical sum. -/
  globalBulkIntegral_eq_integral :
    measureTerms.globalBulkIntegral =
      ∫ y, selectedPartitionBulkScalarIntegrand P boundary localized y ∂μ
  /-- Measurability of selected interior boxes. -/
  interiorBox_measurable :
    ∀ i, i ∈ P.active → MeasurableSet (interiorBox i)
  /-- Measurability of selected boundary boxes. -/
  boundaryBox_measurable :
    ∀ x, x ∈ P.active →
      ∀ q, q ∈ boundary.boundaryPieces x → MeasurableSet (boundaryBox x q)
  /-- Canonical interior scalar terms vanish outside their selected boxes. -/
  interior_eq_zero_off_box :
    ∀ i, i ∈ P.active →
      ∀ y, y ∉ interiorBox i →
        selectedPartitionInteriorBulkScalarTerm localized i y = 0
  /-- Canonical boundary scalar terms vanish outside their selected boxes. -/
  boundary_eq_zero_off_box :
    ∀ x, x ∈ P.active →
      ∀ q, q ∈ boundary.boundaryPieces x →
        ∀ y, y ∉ boundaryBox x q →
          selectedPartitionBoundaryBulkScalarTerm boundary x q y = 0
  /-- Interior set integrals are the recorded localized bulk terms. -/
  interiorBulkTerm_eq_integral :
    ∀ i, i ∈ P.active →
      localized.localizedInterior.bulkTerm i =
        ∫ y in interiorBox i,
          selectedPartitionInteriorBulkScalarTerm localized i y ∂μ
  /-- Boundary set integrals are the recorded boundary bulk terms. -/
  boundaryBulkTerm_eq_integral :
    ∀ x, x ∈ P.active →
      ∀ q, q ∈ boundary.boundaryPieces x →
        BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
          ∫ y in boundaryBox x q,
            selectedPartitionBoundaryBulkScalarTerm boundary x q y ∂μ

namespace SelectedPartitionBulkMeasureExtDerivInput

variable
    (D :
      SelectedPartitionBulkMeasureExtDerivInput
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        P boundary μ)

/-- The canonical interior scalar local term carried by the input. -/
def interiorLocalTerm
    (D :
      SelectedPartitionBulkMeasureExtDerivInput
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        P boundary μ) :
    M → (Fin (n + 1) → Real) → Real :=
  selectedPartitionInteriorBulkScalarTerm D.localized

/-- The canonical boundary scalar local term carried by the input. -/
def boundaryLocalTerm
    (_D :
      SelectedPartitionBulkMeasureExtDerivInput
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        P boundary μ) :
    M → BoundaryPiece → (Fin (n + 1) → Real) → Real :=
  selectedPartitionBoundaryBulkScalarTerm boundary

/-- The canonical global scalar bulk integrand carried by the input. -/
def F
    (D :
      SelectedPartitionBulkMeasureExtDerivInput
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        P boundary μ) :
    (Fin (n + 1) → Real) → Real :=
  selectedPartitionBulkScalarIntegrand P boundary D.localized

omit [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem interiorLocalTerm_eq :
    D.interiorLocalTerm =
      selectedPartitionInteriorBulkScalarTerm D.localized :=
  rfl

omit [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem boundaryLocalTerm_eq :
    D.boundaryLocalTerm =
      selectedPartitionBoundaryBulkScalarTerm boundary :=
  rfl

omit [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem F_eq :
    D.F = selectedPartitionBulkScalarIntegrand P boundary D.localized :=
  rfl

omit [IsFiniteMeasureOnCompacts μ] in
/--
The selected finite-sum reconstruction for the canonical scalar integrand.

This is pointwise by construction; the analytic work is in showing that this
canonical finite sum represents the intended global integral.
-/
theorem F_eq_partitionUnlocalizedSum
    (y : Fin (n + 1) → Real) :
    D.F y =
      bulkMeasureUnlocalizedSum P.active P.active boundary.boundaryPieces
        D.interiorLocalTerm D.boundaryLocalTerm y :=
  rfl

/-- Expose the partition exterior-derivative a.e. local fields. -/
def toBulkIntegrandAELocalFields :
    BulkIntegrandAELocalFields D.measureTerms :=
  D.extDerivAE.toBulkIntegrandAELocalFields

omit [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem toBulkIntegrandAELocalFields_aeData :
    D.toBulkIntegrandAELocalFields.aeData =
      D.extDerivAE.toBulkIntegrandAEData :=
  rfl

omit [IsFiniteMeasureOnCompacts μ] in
/-- The ext-derivative route gives the chartwise a.e. bulk-integrand equality. -/
theorem extDerivAE_ae_eq_global (x0 x1 : M) :
    bulkIntegrand I x0 x1
        (localizedFormSum I D.extDerivAE.reconstruction.activeCharts
          D.extDerivAE.localizedEventually.coefficient omega) =ᵐ[D.extDerivAE.measure x0 x1]
      bulkIntegrand I x0 x1 omega :=
  D.extDerivAE.ae_eq_global x0 x1

/--
Construct the selected-partition bulk measure package from the ext-derivative
input and the explicit measure hypotheses.
-/
def toBulkMeasureFromPartitionData :
    BulkMeasureFromPartitionData
      (α := Fin (n + 1) → Real) (μ := μ)
      P boundary D.measureTerms.globalBulkIntegral :=
  D.compactSupport.toBulkMeasureFromPartitionData
    (P := P) (localized := D.localized) (boundary := boundary)
    (globalBulkIntegral := D.measureTerms.globalBulkIntegral)
    D.boundary_active D.F D.interiorBox D.boundaryBox
    D.globalBulkIntegral_eq_integral
    D.interiorBox_measurable D.boundaryBox_measurable
    D.interior_eq_zero_off_box D.boundary_eq_zero_off_box
    D.interiorBulkTerm_eq_integral D.boundaryBulkTerm_eq_integral
    D.F_eq_partitionUnlocalizedSum

/-- The resulting compact-support bulk-measure package. -/
def toCompactSupportBulkMeasureData :
    CompactSupportBulkMeasureData
      (α := Fin (n + 1) → Real) (μ := μ)
      D.localized.localizedInterior boundary D.measureTerms.globalBulkIntegral :=
  D.toBulkMeasureFromPartitionData.toCompactSupportBulkMeasureData

omit [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem toBulkMeasureFromPartitionData_F :
    D.toBulkMeasureFromPartitionData.F = D.F :=
  rfl

omit [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem toBulkMeasureFromPartitionData_interiorLocalTerm :
    D.toBulkMeasureFromPartitionData.interiorLocalTerm =
      D.interiorLocalTerm :=
  rfl

omit [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem toBulkMeasureFromPartitionData_boundaryLocalTerm :
    D.toBulkMeasureFromPartitionData.boundaryLocalTerm =
      D.boundaryLocalTerm :=
  rfl

omit [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem toBulkMeasureFromPartitionData_interiorBox :
    D.toBulkMeasureFromPartitionData.interiorBox = D.interiorBox :=
  rfl

omit [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem toBulkMeasureFromPartitionData_boundaryBox :
    D.toBulkMeasureFromPartitionData.boundaryBox = D.boundaryBox :=
  rfl

/--
The constructed measure package gives the selected finite set-integral
reconstruction of the represented bulk integral.
-/
theorem globalBulkIntegral_eq_selected_local_setIntegral_sum :
    D.measureTerms.globalBulkIntegral =
      (Finset.sum P.active fun i =>
        ∫ y in D.interiorBox i, D.interiorLocalTerm i y ∂μ) +
        Finset.sum P.active fun x =>
          Finset.sum (boundary.boundaryPieces x) fun q =>
            ∫ y in D.boundaryBox x q, D.boundaryLocalTerm x q y ∂μ := by
  simpa [interiorLocalTerm, boundaryLocalTerm] using
    D.toBulkMeasureFromPartitionData.selected_globalBulkIntegral_eq_local_setIntegral_sum

end SelectedPartitionBulkMeasureExtDerivInput

end SelectedPartitionBulkMeasureExtDeriv

end Stokes

end
