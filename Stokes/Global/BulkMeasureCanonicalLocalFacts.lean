import Stokes.Global.BulkMeasureExtDerivFromPartition
import Stokes.Global.MeasureBoxAPI

/-!
# Local facts for canonical selected bulk-measure pieces

This file isolates the local, non-integral facts needed by
`SelectedPartitionBulkMeasureExtDerivInput` for the canonical scalar bulk
pieces.

The support and measurability fields are proved from existing selected-box
data:

* interior pieces use the `LocalizedSupportControl` carried by
  `LocalizedInteriorPiece`;
* boundary pieces use the source `boundaryChartSelectedBox` carried by
  `BoundaryPieceFamilyInput`;
* compact-support/integrability is routed through the existing
  `BulkLocalTermCompactSupportData` package.

The local set-integral identifications and the global represented-integral
identity are intentionally not proved here.  They remain explicit inputs to the
final constructor at the bottom of the file.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkMeasureCanonicalLocalFacts

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

section SupportOfBulkIntegrand

/-- The exterior derivative of a model form is zero off the form's topological support. -/
theorem extDeriv_eq_zero_of_notMem_tsupport
    {ω : ModelForm (Fin (n + 1) → Real) n} {y : Fin (n + 1) → Real}
    (hy : y ∉ tsupport ω) :
    extDeriv ω y = 0 := by
  ext v
  simp [extDeriv, fderiv_of_notMem_tsupport Real hy,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply]

/--
The scalar top-degree bulk integrand is supported in the topological support of
the transition-pullback chart representative.
-/
theorem bulkIntegrand_eq_zero_of_notMem_tsupport
    (x0 x1 : M) (ω : ManifoldForm I M n)
    {y : Fin (n + 1) → Real}
    (hy : y ∉ tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω)) :
    bulkIntegrand I x0 x1 ω y = 0 := by
  have hzero :
      extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y = 0 :=
    extDeriv_eq_zero_of_notMem_tsupport
      (ω := ManifoldForm.transitionPullbackInChart I x0 x1 ω) hy
  simpa [bulkIntegrand] using congrArg (fun η => η (standardTopFrame n)) hzero

/-- Support containment for the scalar top-degree bulk integrand. -/
theorem bulkIntegrand_support_subset_tsupport
    (x0 x1 : M) (ω : ManifoldForm I M n) :
    Function.support (bulkIntegrand I x0 x1 ω) ⊆
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) := by
  intro y hy
  by_contra hnot
  exact hy (bulkIntegrand_eq_zero_of_notMem_tsupport
    (I := I) (x0 := x0) (x1 := x1) ω hnot)

/--
If the transition-pullback representative is topologically supported in a box,
then its canonical scalar bulk integrand vanishes off that box.
-/
theorem bulkIntegrand_eq_zero_off_of_tsupport_subset
    {s : Set (Fin (n + 1) → Real)}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ s)
    {y : Fin (n + 1) → Real} (hy : y ∉ s) :
    bulkIntegrand I x0 x1 ω y = 0 :=
  bulkIntegrand_eq_zero_of_notMem_tsupport
    (I := I) (x0 := x0) (x1 := x1) ω fun hyt => hy (hsupp hyt)

end SupportOfBulkIntegrand

/-- The canonical interior localization box attached to a selected interior piece. -/
def selectedPartitionInteriorCanonicalBox
    (localized : LocalizedInteriorM8Fields I omega P)
    (i : M) : Set (Fin (n + 1) → Real) :=
  Set.Icc (localized.localizedInterior.piece i).lowerCorner
    (localized.localizedInterior.piece i).upperCorner

/-- The canonical boundary localization box attached to a selected boundary piece. -/
def selectedPartitionBoundaryCanonicalBox
    (boundary : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (x : M) (q : BoundaryPiece) : Set (Fin (n + 1) → Real) :=
  halfSpaceSupportBox (boundary.sourceLowerCorner x q) (boundary.sourceUpperCorner x q)

namespace LocalizedInteriorPiece

variable {ρ : M → M → Real} {i : M}

/--
The canonical scalar bulk integrand of a localized interior piece vanishes off
its selected coordinate box.
-/
theorem bulkIntegrand_eq_zero_off_selectedBox
    (D : LocalizedInteriorPiece I omega ρ i)
    {y : Fin (n + 1) → Real}
    (hy : y ∉ Set.Icc D.lowerCorner D.upperCorner) :
    bulkIntegrand I D.sourceChart D.targetChart D.localizedForm y = 0 := by
  have hsupp :
      tsupport
          (ManifoldForm.transitionPullbackInChart I D.sourceChart D.targetChart
            D.localizedForm) ⊆
        Set.Icc D.lowerCorner D.upperCorner := by
    simpa [LocalizedInteriorPiece.localizedForm] using
      D.supportControl.localized_tsupport_subset
  exact bulkIntegrand_eq_zero_off_of_tsupport_subset
    (I := I) (x0 := D.sourceChart) (x1 := D.targetChart)
    (ω := D.localizedForm) hsupp hy

end LocalizedInteriorPiece

namespace BoundaryPieceFamilyInput

/--
The canonical scalar bulk integrand of a boundary source piece vanishes off the
source half-space support box.
-/
theorem boundaryBulkIntegrand_eq_zero_off_sourceBox
    (D : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    {x : M} (hx : x ∈ D.activeCharts)
    {q : BoundaryPiece} (hq : q ∈ D.boundaryPieces x)
    {y : Fin (n + 1) → Real}
    (hy : y ∉ halfSpaceSupportBox (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)) :
    bulkIntegrand I (D.sourceChart x q) (D.boundarySourceChart x q) omega y = 0 := by
  exact bulkIntegrand_eq_zero_off_of_tsupport_subset
    (I := I) (x0 := D.sourceChart x q) (x1 := D.boundarySourceChart x q)
    (ω := omega) (D.sourceSelectedBox hx hq).tsupport_subset hy

end BoundaryPieceFamilyInput

/--
Local support, measurability, and compact-support data for the canonical scalar
bulk pieces associated to a selected partition.

This deliberately does not contain any set-integral identities: those are the
remaining measure-local facts and must be supplied by the caller.
-/
structure SelectedPartitionBulkCanonicalLocalFacts
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundary : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (localized : LocalizedInteriorM8Fields I omega P) where
  /-- Boundary source pieces use the same selected active chart set. -/
  boundary_active : boundary.activeCharts = P.active
  /-- Compact support and continuity of the canonical scalar local terms. -/
  compactSupport :
    BulkLocalTermCompactSupportData
      (α := Fin (n + 1) → Real)
      localized.localizedInterior boundary
      (selectedPartitionInteriorBulkScalarTerm localized)
      (selectedPartitionBoundaryBulkScalarTerm boundary)

namespace SelectedPartitionBulkCanonicalLocalFacts

variable {localized : LocalizedInteriorM8Fields I omega P}

/-- Interior canonical boxes, in the exact shape expected downstream. -/
def interiorBox
    (_D :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized)
    (i : M) : Set (Fin (n + 1) → Real) :=
  selectedPartitionInteriorCanonicalBox localized i

/-- Boundary canonical boxes, in the exact shape expected downstream. -/
def boundaryBox
    (_D :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized)
    (x : M) (q : BoundaryPiece) : Set (Fin (n + 1) → Real) :=
  selectedPartitionBoundaryCanonicalBox boundary x q

@[simp]
theorem interiorBox_eq
    (D :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized)
    (i : M) :
    D.interiorBox i =
      Set.Icc (localized.localizedInterior.piece i).lowerCorner
        (localized.localizedInterior.piece i).upperCorner :=
  rfl

@[simp]
theorem boundaryBox_eq
    (D :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized)
    (x : M) (q : BoundaryPiece) :
    D.boundaryBox x q =
      halfSpaceSupportBox (boundary.sourceLowerCorner x q)
        (boundary.sourceUpperCorner x q) :=
  rfl

/-- Measurability of the selected interior coordinate boxes. -/
theorem interiorBox_measurable
    (D :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized)
    (i : M) (_hi : i ∈ P.active) :
    MeasurableSet (D.interiorBox i) := by
  simp [interiorBox, selectedPartitionInteriorCanonicalBox,
    (measurableSet_Icc_box
      (E := Fin (n + 1) → Real)
      (localized.localizedInterior.piece i).lowerCorner
      (localized.localizedInterior.piece i).upperCorner)]

/-- Measurability of the selected boundary half-space support boxes. -/
theorem boundaryBox_measurable
    (D :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized)
    (x : M) (_hx : x ∈ P.active)
    (q : BoundaryPiece) (_hq : q ∈ boundary.boundaryPieces x) :
    MeasurableSet (D.boundaryBox x q) := by
  simpa [boundaryBox, selectedPartitionBoundaryCanonicalBox] using
    (measurableSet_halfSpaceSupportBox
      (boundary.sourceLowerCorner x q) (boundary.sourceUpperCorner x q))

/-- Interior canonical scalar terms vanish off their canonical selected boxes. -/
theorem interior_eq_zero_off_box
    (D :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized)
    (i : M) (_hi : i ∈ P.active)
    {y : Fin (n + 1) → Real} (hy : y ∉ D.interiorBox i) :
    selectedPartitionInteriorBulkScalarTerm localized i y = 0 := by
  simpa [selectedPartitionInteriorBulkScalarTerm, interiorBox,
    selectedPartitionInteriorCanonicalBox] using
    (localized.localizedInterior.piece i).bulkIntegrand_eq_zero_off_selectedBox
      (I := I) (omega := omega) (hy := hy)

/-- Boundary canonical scalar terms vanish off their canonical source boxes. -/
theorem boundary_eq_zero_off_box
    (D :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized)
    (x : M) (hx : x ∈ P.active)
    (q : BoundaryPiece) (hq : q ∈ boundary.boundaryPieces x)
    {y : Fin (n + 1) → Real} (hy : y ∉ D.boundaryBox x q) :
    selectedPartitionBoundaryBulkScalarTerm boundary x q y = 0 := by
  have hx_boundary : x ∈ boundary.activeCharts := by
    simpa [D.boundary_active] using hx
  simpa [selectedPartitionBoundaryBulkScalarTerm, boundaryBox,
    selectedPartitionBoundaryCanonicalBox] using
    boundary.boundaryBulkIntegrand_eq_zero_off_sourceBox
      (I := I) (omega := omega) hx_boundary hq (hy := hy)

/-- Compact-support package for an active interior canonical scalar term. -/
def interiorCompactSupport
    (D :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized)
    (i : M) (hi : i ∈ P.active) :
    CompactSupportIntegrabilityData
      (selectedPartitionInteriorBulkScalarTerm localized i) :=
  D.compactSupport.interiorCompactSupport i (localized.mem_localized_active hi)

/-- Compact-support package for an active boundary canonical scalar term. -/
def boundaryCompactSupport
    (D :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized)
    (x : M) (hx : x ∈ P.active)
    (q : BoundaryPiece) (hq : q ∈ boundary.boundaryPieces x) :
    CompactSupportIntegrabilityData
      (selectedPartitionBoundaryBulkScalarTerm boundary x q) :=
  D.compactSupport.boundaryCompactSupport x
    (by simpa [D.boundary_active] using hx) q hq

/-- Integrability of an active interior canonical scalar term on its canonical box. -/
theorem interiorIntegrableOn
    (D :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized)
    (i : M) (hi : i ∈ P.active) :
    IntegrableOn
      (selectedPartitionInteriorBulkScalarTerm localized i)
      (D.interiorBox i) μ :=
  (D.interiorCompactSupport i hi).integrableOn (D.interiorBox i)

/-- Integrability of an active boundary canonical scalar term on its canonical box. -/
theorem boundaryIntegrableOn
    (D :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized)
    (x : M) (hx : x ∈ P.active)
    (q : BoundaryPiece) (hq : q ∈ boundary.boundaryPieces x) :
    IntegrableOn
      (selectedPartitionBoundaryBulkScalarTerm boundary x q)
      (D.boundaryBox x q) μ :=
  (D.boundaryCompactSupport x hx q hq).integrableOn (D.boundaryBox x q)

/--
Construct the full selected-partition bulk ext-derivative input from canonical
local facts plus the remaining integral-identification fields.
-/
def toSelectedPartitionBulkMeasureExtDerivInput
    (D :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized)
    (measureTerms :
      BulkMeasureLocalizationTermFields localized.localizedInterior boundary)
    (extDerivAE :
      BulkIntegrandAEFromPartitionData
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        P boundary localized measureTerms)
    (globalBulkIntegral_eq_integral :
      measureTerms.globalBulkIntegral =
        ∫ y, selectedPartitionBulkScalarIntegrand P boundary localized y ∂μ)
    (interiorBulkTerm_eq_integral :
      ∀ i, i ∈ P.active →
        localized.localizedInterior.bulkTerm i =
          ∫ y in D.interiorBox i,
            selectedPartitionInteriorBulkScalarTerm localized i y ∂μ)
    (boundaryBulkTerm_eq_integral :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x →
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in D.boundaryBox x q,
              selectedPartitionBoundaryBulkScalarTerm boundary x q y ∂μ) :
    SelectedPartitionBulkMeasureExtDerivInput
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      P boundary μ where
  localized := localized
  boundary_active := D.boundary_active
  measureTerms := measureTerms
  extDerivAE := extDerivAE
  compactSupport := D.compactSupport
  interiorBox := D.interiorBox
  boundaryBox := D.boundaryBox
  globalBulkIntegral_eq_integral := globalBulkIntegral_eq_integral
  interiorBox_measurable := D.interiorBox_measurable
  boundaryBox_measurable := D.boundaryBox_measurable
  interior_eq_zero_off_box := by
    intro i hi y hy
    exact D.interior_eq_zero_off_box i hi hy
  boundary_eq_zero_off_box := by
    intro x hx q hq y hy
    exact D.boundary_eq_zero_off_box x hx q hq hy
  interiorBulkTerm_eq_integral := interiorBulkTerm_eq_integral
  boundaryBulkTerm_eq_integral := boundaryBulkTerm_eq_integral

omit [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem toSelectedPartitionBulkMeasureExtDerivInput_interiorBox
    (D :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized)
    (measureTerms :
      BulkMeasureLocalizationTermFields localized.localizedInterior boundary)
    (extDerivAE :
      BulkIntegrandAEFromPartitionData
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        P boundary localized measureTerms)
    (globalBulkIntegral_eq_integral :
      measureTerms.globalBulkIntegral =
        ∫ y, selectedPartitionBulkScalarIntegrand P boundary localized y ∂μ)
    (interiorBulkTerm_eq_integral :
      ∀ i, i ∈ P.active →
        localized.localizedInterior.bulkTerm i =
          ∫ y in D.interiorBox i,
            selectedPartitionInteriorBulkScalarTerm localized i y ∂μ)
    (boundaryBulkTerm_eq_integral :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x →
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in D.boundaryBox x q,
              selectedPartitionBoundaryBulkScalarTerm boundary x q y ∂μ) :
    (D.toSelectedPartitionBulkMeasureExtDerivInput
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      measureTerms extDerivAE globalBulkIntegral_eq_integral
      interiorBulkTerm_eq_integral boundaryBulkTerm_eq_integral).interiorBox =
      D.interiorBox :=
  rfl

omit [IsFiniteMeasureOnCompacts μ] in
@[simp]
theorem toSelectedPartitionBulkMeasureExtDerivInput_boundaryBox
    (D :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized)
    (measureTerms :
      BulkMeasureLocalizationTermFields localized.localizedInterior boundary)
    (extDerivAE :
      BulkIntegrandAEFromPartitionData
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        P boundary localized measureTerms)
    (globalBulkIntegral_eq_integral :
      measureTerms.globalBulkIntegral =
        ∫ y, selectedPartitionBulkScalarIntegrand P boundary localized y ∂μ)
    (interiorBulkTerm_eq_integral :
      ∀ i, i ∈ P.active →
        localized.localizedInterior.bulkTerm i =
          ∫ y in D.interiorBox i,
            selectedPartitionInteriorBulkScalarTerm localized i y ∂μ)
    (boundaryBulkTerm_eq_integral :
      ∀ x, x ∈ P.active →
        ∀ q, q ∈ boundary.boundaryPieces x →
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in D.boundaryBox x q,
              selectedPartitionBoundaryBulkScalarTerm boundary x q y ∂μ) :
    (D.toSelectedPartitionBulkMeasureExtDerivInput
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      measureTerms extDerivAE globalBulkIntegral_eq_integral
      interiorBulkTerm_eq_integral boundaryBulkTerm_eq_integral).boundaryBox =
      D.boundaryBox :=
  rfl

end SelectedPartitionBulkCanonicalLocalFacts

end BulkMeasureCanonicalLocalFacts

end Stokes

end
