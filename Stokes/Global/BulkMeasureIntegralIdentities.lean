import Stokes.Global.CanonicalPiecesFromLocalFacts
import Stokes.Global.MeasureBoxProjectLocal

/-!
# Bulk measure integral identities

This file reduces the remaining bulk integral fields in
`SelectedPartitionBulkMeasureExtDerivInput`.

The global field

```lean
measureTerms.globalBulkIntegral =
  ∫ y, selectedPartitionBulkScalarIntegrand P boundary localized y ∂μ
```

is not an independent analytic fact once we have:

* localization of the represented bulk integral as the finite sum of project
  local bulk terms;
* local set-integral identities for each canonical interior and boundary
  scalar term.

The local identities remain real work.  For the interior pieces, with the
Lebesgue/volume measure, the equality is definitionally the existing
`projectInteriorBulkIntegral`.  For boundary pieces the project-local bulk term
is definitionally the integral over the closed source box `Icc a b`; the current
canonical M8 box is `halfSpaceSupportBox a b`, so the remaining honest
obligation is the set-integral transfer from `Icc` to that half-space support
box.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkMeasureIntegralIdentities

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
variable {localized : LocalizedInteriorM8Fields I omega P}
variable {μ : Measure (Fin (n + 1) → Real)}
variable [IsFiniteMeasureOnCompacts μ]

/--
Local set-integral identities for the canonical selected bulk scalar terms.

This record deliberately contains only the two local fields.  The global
represented-integral field is proved below from finite-sum localization plus a
bulk-localization equality already available from the existing measure-box API.
-/
structure SelectedPartitionBulkLocalSetIntegralIdentities
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundary : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (localized : LocalizedInteriorM8Fields I omega P)
    (μ : Measure (Fin (n + 1) → Real)) where
  /-- Non-integral local facts: boxes, measurability, support, compact support. -/
  localFacts :
    SelectedPartitionBulkCanonicalLocalFacts P boundary localized
  /-- Interior set integrals are the recorded project-local bulk terms. -/
  interiorBulkTerm_eq_integral :
    ∀ i, i ∈ P.active →
      localized.localizedInterior.bulkTerm i =
        ∫ y in localFacts.interiorBox i,
          selectedPartitionInteriorBulkScalarTerm localized i y ∂μ
  /-- Boundary set integrals are the recorded project-local bulk terms. -/
  boundaryBulkTerm_eq_integral :
    ∀ x, x ∈ P.active →
      ∀ q, q ∈ boundary.boundaryPieces x →
        BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
          ∫ y in localFacts.boundaryBox x q,
            selectedPartitionBoundaryBulkScalarTerm boundary x q y ∂μ

namespace SelectedPartitionBulkLocalSetIntegralIdentities

variable
    (D : SelectedPartitionBulkLocalSetIntegralIdentities
      (P := P) (boundary := boundary) localized μ)

/-- Interior canonical scalar terms have support in their selected boxes. -/
theorem interior_support_subset_box
    (i : M) (hi : i ∈ P.active) :
    Function.support (selectedPartitionInteriorBulkScalarTerm localized i) ⊆
      (SelectedPartitionBulkLocalSetIntegralIdentities.localFacts D).interiorBox i :=
  support_subset_of_eq_zero_off fun _y hy =>
    D.localFacts.interior_eq_zero_off_box i hi hy

/-- Boundary canonical scalar terms have support in their selected boxes. -/
theorem boundary_support_subset_box
    (x : M) (hx : x ∈ P.active)
    (q : BoundaryPiece) (hq : q ∈ boundary.boundaryPieces x) :
    Function.support (selectedPartitionBoundaryBulkScalarTerm boundary x q) ⊆
      (SelectedPartitionBulkLocalSetIntegralIdentities.localFacts D).boundaryBox x q :=
  support_subset_of_eq_zero_off fun _y hy =>
    D.localFacts.boundary_eq_zero_off_box x hx q hq hy

/--
The canonical selected bulk scalar integrand is a.e. the corresponding
indicator-localized finite sum.
-/
theorem selected_F_ae_eq_indicatorSum :
    selectedPartitionBulkScalarIntegrand P boundary localized =ᵐ[μ]
      bulkMeasureIndicatorSum P.active P.active boundary.boundaryPieces
        (SelectedPartitionBulkLocalSetIntegralIdentities.localFacts D).interiorBox
        (SelectedPartitionBulkLocalSetIntegralIdentities.localFacts D).boundaryBox
        (selectedPartitionInteriorBulkScalarTerm localized)
        (selectedPartitionBoundaryBulkScalarTerm boundary) :=
  bulkMeasureUnlocalizedSum_ae_eq_indicatorSum_of_support_subset
    (μ := μ) P.active P.active boundary.boundaryPieces
    (SelectedPartitionBulkLocalSetIntegralIdentities.localFacts D).interiorBox
    (SelectedPartitionBulkLocalSetIntegralIdentities.localFacts D).boundaryBox
    (selectedPartitionInteriorBulkScalarTerm localized)
    (selectedPartitionBoundaryBulkScalarTerm boundary)
    D.interior_support_subset_box D.boundary_support_subset_box

/--
Finite-additivity of the canonical selected bulk scalar integral, rewritten as
the local set integrals over the selected boxes.
-/
theorem integral_eq_local_setIntegral_sum :
    (∫ y, selectedPartitionBulkScalarIntegrand P boundary localized y ∂μ) =
      (Finset.sum P.active fun i =>
        ∫ y in (SelectedPartitionBulkLocalSetIntegralIdentities.localFacts D).interiorBox i,
          selectedPartitionInteriorBulkScalarTerm localized i y ∂μ) +
        Finset.sum P.active fun x =>
          Finset.sum (boundary.boundaryPieces x) fun q =>
            ∫ y in (SelectedPartitionBulkLocalSetIntegralIdentities.localFacts D).boundaryBox x q,
              selectedPartitionBoundaryBulkScalarTerm boundary x q y ∂μ :=
  integral_eq_bulkMeasureSetIntegralSum_of_ae_eq_indicatorSum μ
    P.active P.active boundary.boundaryPieces
    (selectedPartitionBulkScalarIntegrand P boundary localized)
    (SelectedPartitionBulkLocalSetIntegralIdentities.localFacts D).interiorBox
    (SelectedPartitionBulkLocalSetIntegralIdentities.localFacts D).boundaryBox
    (selectedPartitionInteriorBulkScalarTerm localized)
    (selectedPartitionBoundaryBulkScalarTerm boundary)
    D.localFacts.interiorBox_measurable
    D.localFacts.boundaryBox_measurable
    D.localFacts.interiorIntegrableOn
    D.localFacts.boundaryIntegrableOn
    D.selected_F_ae_eq_indicatorSum

/--
If the represented global bulk integral is already localized as the selected
finite sum of project-local bulk terms, the global integral field follows from
the local set-integral identities.
-/
theorem globalBulkIntegral_eq_integral_of_selectedLocalSum
    (D : SelectedPartitionBulkLocalSetIntegralIdentities
      (P := P) (boundary := boundary) localized μ)
    {measureTerms :
      BulkMeasureLocalizationTermFields localized.localizedInterior boundary}
    (hglobal :
      measureTerms.globalBulkIntegral =
        (Finset.sum P.active fun i =>
          localized.localizedInterior.bulkTerm i) +
          Finset.sum P.active fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q) :
    measureTerms.globalBulkIntegral =
      ∫ y, selectedPartitionBulkScalarIntegrand P boundary localized y ∂μ := by
  let LF := SelectedPartitionBulkLocalSetIntegralIdentities.localFacts D
  calc
    measureTerms.globalBulkIntegral =
        (Finset.sum P.active fun i =>
          localized.localizedInterior.bulkTerm i) +
          Finset.sum P.active fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q := hglobal
    _ =
        (Finset.sum P.active fun i =>
          ∫ y in LF.interiorBox i,
            selectedPartitionInteriorBulkScalarTerm localized i y ∂μ) +
          Finset.sum P.active fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              ∫ y in LF.boundaryBox x q,
                selectedPartitionBoundaryBulkScalarTerm boundary x q y ∂μ := by
      congr 1
      · exact Finset.sum_congr rfl fun i hi =>
          SelectedPartitionBulkLocalSetIntegralIdentities.interiorBulkTerm_eq_integral D i hi
      · refine Finset.sum_congr rfl ?_
        intro x hx
        exact Finset.sum_congr rfl fun q hq =>
          SelectedPartitionBulkLocalSetIntegralIdentities.boundaryBulkTerm_eq_integral D x hx q hq
    _ = ∫ y, selectedPartitionBulkScalarIntegrand P boundary localized y ∂μ :=
      (SelectedPartitionBulkLocalSetIntegralIdentities.integral_eq_local_setIntegral_sum D).symm

/--
Variant consuming the existing localized-active/boundary-active sum shape.
-/
theorem globalBulkIntegral_eq_integral_of_localizedLocalSum
    (D : SelectedPartitionBulkLocalSetIntegralIdentities
      (P := P) (boundary := boundary) localized μ)
    {measureTerms :
      BulkMeasureLocalizationTermFields localized.localizedInterior boundary}
    (hglobal :
      measureTerms.globalBulkIntegral =
        (Finset.sum localized.localizedInterior.active fun i =>
          localized.localizedInterior.bulkTerm i) +
          BoundaryPieceFamilyInput.boundaryBulkSum boundary) :
    measureTerms.globalBulkIntegral =
      ∫ y, selectedPartitionBulkScalarIntegrand P boundary localized y ∂μ := by
  apply SelectedPartitionBulkLocalSetIntegralIdentities.globalBulkIntegral_eq_integral_of_selectedLocalSum D
  simpa [localized.localized_active, D.localFacts.boundary_active,
    BoundaryPieceFamilyInput.boundaryBulkSum] using hglobal

/--
The existing measure-box/project-local API supplies the global represented
integral field once the two local set-integral identities are known.
-/
theorem globalBulkIntegral_eq_integral_of_measureLocalBoxTermAPI
    (D : SelectedPartitionBulkLocalSetIntegralIdentities
      (P := P) (boundary := boundary) localized μ)
    {measureTerms :
      BulkMeasureLocalizationTermFields localized.localizedInterior boundary}
    (boxAPI : MeasureLocalBoxTermAPI measureTerms) :
    measureTerms.globalBulkIntegral =
      ∫ y, selectedPartitionBulkScalarIntegrand P boundary localized y ∂μ :=
  SelectedPartitionBulkLocalSetIntegralIdentities.globalBulkIntegral_eq_integral_of_localizedLocalSum D
    boxAPI.bulkIntegralLocalizes

/--
Constructor for `SelectedPartitionBulkMeasureExtDerivInput` with the global
integral field derived from a selected local-sum equality.
-/
def toSelectedPartitionBulkMeasureExtDerivInputOfSelectedLocalSum
    (D : SelectedPartitionBulkLocalSetIntegralIdentities
      (P := P) (boundary := boundary) localized μ)
    (measureTerms :
      BulkMeasureLocalizationTermFields localized.localizedInterior boundary)
    (extDerivAE :
      BulkIntegrandAEFromPartitionData
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        P boundary localized measureTerms)
    (hglobal :
      measureTerms.globalBulkIntegral =
        (Finset.sum P.active fun i =>
          localized.localizedInterior.bulkTerm i) +
          Finset.sum P.active fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q) :
    SelectedPartitionBulkMeasureExtDerivInput
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      P boundary μ :=
  D.localFacts.toSelectedPartitionBulkMeasureExtDerivInput
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    measureTerms extDerivAE
    (SelectedPartitionBulkLocalSetIntegralIdentities.globalBulkIntegral_eq_integral_of_selectedLocalSum
      D hglobal)
    D.interiorBulkTerm_eq_integral D.boundaryBulkTerm_eq_integral

/--
Constructor for `SelectedPartitionBulkMeasureExtDerivInput` using the existing
measure-local box/project-local equality API to derive the global field.
-/
def toSelectedPartitionBulkMeasureExtDerivInputOfMeasureLocalBoxTermAPI
    (D : SelectedPartitionBulkLocalSetIntegralIdentities
      (P := P) (boundary := boundary) localized μ)
    (measureTerms :
      BulkMeasureLocalizationTermFields localized.localizedInterior boundary)
    (extDerivAE :
      BulkIntegrandAEFromPartitionData
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        P boundary localized measureTerms)
    (boxAPI : MeasureLocalBoxTermAPI measureTerms) :
    SelectedPartitionBulkMeasureExtDerivInput
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      P boundary μ :=
  D.toSelectedPartitionBulkMeasureExtDerivInputOfSelectedLocalSum
    measureTerms extDerivAE
    (by
      simpa [localized.localized_active, D.localFacts.boundary_active,
        BoundaryPieceFamilyInput.boundaryBulkSum] using
        boxAPI.bulkIntegralLocalizes)

end SelectedPartitionBulkLocalSetIntegralIdentities

section VolumeLocalIdentities

variable
    (localFacts :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized)

/--
For the volume measure, the interior local identity is exactly the definition
of `projectInteriorBulkIntegral` and the canonical scalar bulk integrand.
-/
theorem selectedPartitionInteriorBulkTerm_eq_volume_integral
    (i : M) (_hi : i ∈ P.active) :
    localized.localizedInterior.bulkTerm i =
      ∫ y in localFacts.interiorBox i,
        selectedPartitionInteriorBulkScalarTerm localized i y := by
  simp [LocalizedInteriorPieces.bulkTerm, projectInteriorBulkIntegral,
    selectedPartitionInteriorBulkScalarTerm,
    SelectedPartitionBulkCanonicalLocalFacts.interiorBox,
    selectedPartitionInteriorCanonicalBox, bulkIntegrand]

/--
The same interior local identity, transported to any measure definitionally
equal to volume.
-/
theorem selectedPartitionInteriorBulkTerm_eq_integral_of_measure_eq_volume
    (hμ : μ = volume)
    (i : M) (hi : i ∈ P.active) :
    localized.localizedInterior.bulkTerm i =
      ∫ y in localFacts.interiorBox i,
        selectedPartitionInteriorBulkScalarTerm localized i y ∂μ := by
  subst hμ
  simpa using
    selectedPartitionInteriorBulkTerm_eq_volume_integral
      (P := P) (boundary := boundary) (localized := localized)
      localFacts i hi

/--
For boundary pieces, the project-local bulk term is definitionally the integral
over the closed source box `Icc a b`.
-/
theorem selectedPartitionBoundaryBulkTerm_eq_volume_Icc_integral
    (x : M) (q : BoundaryPiece) :
    BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
      ∫ y in Set.Icc (boundary.sourceLowerCorner x q)
          (boundary.sourceUpperCorner x q),
        selectedPartitionBoundaryBulkScalarTerm boundary x q y := by
  simp [BoundaryPieceFamilyInput.boundaryBulkTerm, projectLocalBulkIntegral,
    halfSpaceLocalTransitionBulkIntegral, halfSpaceLocalBulkIntegral,
    selectedPartitionBoundaryBulkScalarTerm, bulkIntegrand]

/--
The remaining honest boundary transfer from the closed source box to the
canonical half-space support box.
-/
structure SelectedBoundaryIccToHalfSpaceIntegralTransfer
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundary : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (localized : LocalizedInteriorM8Fields I omega P)
    (localFacts :
      SelectedPartitionBulkCanonicalLocalFacts
        (P := P) (boundary := boundary) localized)
    (μ : Measure (Fin (n + 1) → Real)) where
  /--
  The closed-box project-local integral agrees with the canonical selected
  half-space-support-box integral.
  -/
  boundary_Icc_integral_eq_canonicalBox_integral :
    ∀ x, x ∈ P.active →
      ∀ q, q ∈ boundary.boundaryPieces x →
        (∫ y in Set.Icc (boundary.sourceLowerCorner x q)
            (boundary.sourceUpperCorner x q),
          selectedPartitionBoundaryBulkScalarTerm boundary x q y ∂μ) =
          ∫ y in localFacts.boundaryBox x q,
            selectedPartitionBoundaryBulkScalarTerm boundary x q y ∂μ

namespace SelectedBoundaryIccToHalfSpaceIntegralTransfer

variable
    (T :
      SelectedBoundaryIccToHalfSpaceIntegralTransfer
        (P := P) (boundary := boundary) (localized := localized)
        localFacts μ)

/--
The boundary local set-integral identity follows from the `Icc` project-local
definition plus the transfer to the canonical half-space support box.
-/
theorem boundaryBulkTerm_eq_integral_of_measure_eq_volume
    (T :
      SelectedBoundaryIccToHalfSpaceIntegralTransfer
        (P := P) (boundary := boundary) (localized := localized)
        localFacts μ)
    (hμ : μ = volume)
    (x : M) (hx : x ∈ P.active)
    (q : BoundaryPiece) (hq : q ∈ boundary.boundaryPieces x) :
    BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
      ∫ y in localFacts.boundaryBox x q,
        selectedPartitionBoundaryBulkScalarTerm boundary x q y ∂μ := by
  subst hμ
  calc
    BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
        ∫ y in Set.Icc (boundary.sourceLowerCorner x q)
            (boundary.sourceUpperCorner x q),
          selectedPartitionBoundaryBulkScalarTerm boundary x q y := by
      exact selectedPartitionBoundaryBulkTerm_eq_volume_Icc_integral
        (I := I) (omega := omega) (boundary := boundary) x q
    _ =
        ∫ y in localFacts.boundaryBox x q,
          selectedPartitionBoundaryBulkScalarTerm boundary x q y :=
      SelectedBoundaryIccToHalfSpaceIntegralTransfer.boundary_Icc_integral_eq_canonicalBox_integral
        T x hx q hq

/--
Volume-facing constructor for the two local set-integral identities.  Interior
is definitional; boundary is reduced to the explicit `Icc`-to-half-space-box
transfer field above.
-/
def toLocalSetIntegralIdentitiesOfMeasureEqVolume
    (T :
      SelectedBoundaryIccToHalfSpaceIntegralTransfer
        (P := P) (boundary := boundary) (localized := localized)
        localFacts μ)
    (hμ : μ = volume) :
    SelectedPartitionBulkLocalSetIntegralIdentities
      (P := P) (boundary := boundary) localized μ where
  localFacts := localFacts
  interiorBulkTerm_eq_integral := by
    intro i hi
    exact selectedPartitionInteriorBulkTerm_eq_integral_of_measure_eq_volume
      (P := P) (boundary := boundary) (localized := localized)
      (μ := μ) localFacts hμ i hi
  boundaryBulkTerm_eq_integral := by
    intro x hx q hq
    exact SelectedBoundaryIccToHalfSpaceIntegralTransfer.boundaryBulkTerm_eq_integral_of_measure_eq_volume
      localFacts T hμ x hx q hq

end SelectedBoundaryIccToHalfSpaceIntegralTransfer

end VolumeLocalIdentities

end BulkMeasureIntegralIdentities

end Stokes

end
