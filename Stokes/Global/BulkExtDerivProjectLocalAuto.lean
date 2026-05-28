import Stokes.Global.MeasureLocalBoxTermAuto

/-!
# Project-local automatic bulk exterior-derivative a.e. inputs

This module removes one bookkeeping layer from the bulk exterior-derivative
route.  When the measure-local terms are the canonical project-local box terms
from `BulkMeasureLocalizationTermFields.ofProjectLocalBoxTerms`, the local
measure/integrand term equalities in `BulkIntegrandAEFromPartitionData` are
definitionally true.

The genuine analytic work is deliberately still explicit: callers must still
provide the partition-local eventual equality package, reconstruction data, and
a.e. support of the selected chartwise measures.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkExtDerivProjectLocalAuto

universe u w cb pb ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryChart : Type cb} {BoundaryPiece : Type pb}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {P : SelectedBoxPartitionOfUnity I omega}
variable {boundary : BoundaryPieceFamilyInput I omega BoundaryChart BoundaryPiece}
variable {localized : LocalizedInteriorM8Fields I omega P}

namespace BulkIntegrandAEFromPartitionData

/--
Constructor for the canonical project-local measure terms.

The local scalar terms are chosen to be the already-recorded project-local bulk
terms, so the measure-local/integrand-local comparison fields are `rfl`.  This
does not prove the partition exterior-derivative a.e. theorem; the
`localizedEventually`, `reconstruction`, and `hmeasureSupport` fields remain
the caller's analytic input.
-/
def ofProjectLocalBoxTerms
    (localizedEventually :
      PartitionLocalizedEventuallyFields I omega (M ⊕ BoundaryChart))
    (reconstruction :
      PartitionReconstructionData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (localizedEventually_active :
      localizedEventually.activeCharts =
        selectedPartitionBulkActive P boundary)
    (localizedEventually_coefficient :
      localizedEventually.coefficient =
        selectedPartitionBulkCoefficient
          (BoundaryChart := BoundaryChart) P)
    (localizedEventually_active_eq_reconstruction :
      localizedEventually.activeCharts = reconstruction.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1),
        y ∈ localizedEventually.chartSupport x0 x1) :
    BulkIntegrandAEFromPartitionData
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      P boundary localized
      (BulkMeasureLocalizationTermFields.ofProjectLocalBoxTerms
        localized.localizedInterior boundary) where
  localizedEventually := localizedEventually
  reconstruction := reconstruction
  localizedEventually_active := localizedEventually_active
  localizedEventually_coefficient := localizedEventually_coefficient
  localizedEventually_active_eq_reconstruction :=
    localizedEventually_active_eq_reconstruction
  measure := measure
  hmeasureSupport := hmeasureSupport
  interiorIntegrandTerm := fun i => localized.localizedInterior.bulkTerm i
  boundaryIntegrandTerm := fun x q =>
    BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q
  interiorMeasureTerm_eq_integrandTerm := by
    intro i _hi
    rfl
  boundaryMeasureTerm_eq_integrandTerm := by
    intro x _hx q _hq
    rfl

@[simp]
theorem ofProjectLocalBoxTerms_interiorIntegrandTerm
    (localizedEventually :
      PartitionLocalizedEventuallyFields I omega (M ⊕ BoundaryChart))
    (reconstruction :
      PartitionReconstructionData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (localizedEventually_active :
      localizedEventually.activeCharts =
        selectedPartitionBulkActive P boundary)
    (localizedEventually_coefficient :
      localizedEventually.coefficient =
        selectedPartitionBulkCoefficient
          (BoundaryChart := BoundaryChart) P)
    (localizedEventually_active_eq_reconstruction :
      localizedEventually.activeCharts = reconstruction.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1),
        y ∈ localizedEventually.chartSupport x0 x1) :
    (ofProjectLocalBoxTerms
      (P := P) (boundary := boundary) (localized := localized)
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      localizedEventually reconstruction localizedEventually_active
      localizedEventually_coefficient localizedEventually_active_eq_reconstruction
      measure hmeasureSupport).interiorIntegrandTerm =
      fun i => localized.localizedInterior.bulkTerm i := by
  rfl

@[simp]
theorem ofProjectLocalBoxTerms_boundaryIntegrandTerm
    (localizedEventually :
      PartitionLocalizedEventuallyFields I omega (M ⊕ BoundaryChart))
    (reconstruction :
      PartitionReconstructionData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (localizedEventually_active :
      localizedEventually.activeCharts =
        selectedPartitionBulkActive P boundary)
    (localizedEventually_coefficient :
      localizedEventually.coefficient =
        selectedPartitionBulkCoefficient
          (BoundaryChart := BoundaryChart) P)
    (localizedEventually_active_eq_reconstruction :
      localizedEventually.activeCharts = reconstruction.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1),
        y ∈ localizedEventually.chartSupport x0 x1) :
    (ofProjectLocalBoxTerms
      (P := P) (boundary := boundary) (localized := localized)
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      localizedEventually reconstruction localizedEventually_active
      localizedEventually_coefficient localizedEventually_active_eq_reconstruction
      measure hmeasureSupport).boundaryIntegrandTerm =
      fun x q => BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q := by
  rfl

end BulkIntegrandAEFromPartitionData

/--
Theorem-facing bulk a.e. input for the canonical project-local measure-term
choice.

Compared with `BulkIntegrandAEFromPartitionData`, this record removes the
manual `interiorIntegrandTerm`, `boundaryIntegrandTerm`, and their local
measure-term equality fields.  Those are fixed by the canonical
`ofProjectLocalBoxTerms` choice.  The true exterior-derivative a.e. and support
content remains as fields.
-/
structure BulkIntegrandAEProjectLocalAutoInput
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundary : BoundaryPieceFamilyInput I omega BoundaryChart BoundaryPiece)
    (localized : LocalizedInteriorM8Fields I omega P) where
  /-- Partition-local equality package on the combined interior/boundary labels. -/
  localizedEventually :
    PartitionLocalizedEventuallyFields I omega (M ⊕ BoundaryChart)
  /-- Reconstruction fields with the same combined chart labels. -/
  reconstruction :
    PartitionReconstructionData I omega (M ⊕ BoundaryChart)
      ExtInteriorPiece ExtBoundaryPiece
  /-- The eventual-equality package uses the selected combined active labels. -/
  localizedEventually_active :
    localizedEventually.activeCharts = selectedPartitionBulkActive P boundary
  /-- The eventual-equality package uses the selected combined coefficients. -/
  localizedEventually_coefficient :
    localizedEventually.coefficient =
      selectedPartitionBulkCoefficient
        (BoundaryChart := BoundaryChart) P
  /-- The eventual-equality and reconstruction packages use the same active labels. -/
  localizedEventually_active_eq_reconstruction :
    localizedEventually.activeCharts = reconstruction.activeCharts
  /-- Chartwise measure used for the scalar bulk integrand comparison. -/
  measure : M → M → Measure (Fin (n + 1) → Real)
  /-- The chosen measures are a.e. supported where the local equality is known. -/
  hmeasureSupport :
    ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1),
      y ∈ localizedEventually.chartSupport x0 x1

namespace BulkIntegrandAEProjectLocalAutoInput

variable
    (D :
      BulkIntegrandAEProjectLocalAutoInput
        (BoundaryChart := BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece P boundary localized)

/-- Canonical measure-local terms induced by project-local box terms. -/
def measureTerms
    (_D :
      BulkIntegrandAEProjectLocalAutoInput
        (BoundaryChart := BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece P boundary localized) :
    BulkMeasureLocalizationTermFields
      localized.localizedInterior boundary :=
  BulkMeasureLocalizationTermFields.ofProjectLocalBoxTerms
    localized.localizedInterior boundary

/-- Forget the reduced project-local-auto input to the existing a.e. package. -/
def toBulkIntegrandAEFromPartitionData
    (D :
      BulkIntegrandAEProjectLocalAutoInput
        (BoundaryChart := BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece P boundary localized) :
    BulkIntegrandAEFromPartitionData
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      P boundary localized D.measureTerms :=
  BulkIntegrandAEFromPartitionData.ofProjectLocalBoxTerms
    (P := P) (boundary := boundary) (localized := localized)
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    D.localizedEventually D.reconstruction D.localizedEventually_active
    D.localizedEventually_coefficient
    D.localizedEventually_active_eq_reconstruction
    D.measure D.hmeasureSupport

/-- Expose the corresponding local a.e. replacement fields. -/
def toBulkIntegrandAELocalFields
    (D :
      BulkIntegrandAEProjectLocalAutoInput
        (BoundaryChart := BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece P boundary localized) :
    BulkIntegrandAELocalFields D.measureTerms :=
  D.toBulkIntegrandAEFromPartitionData.toBulkIntegrandAELocalFields

@[simp]
theorem toBulkIntegrandAEFromPartitionData_localizedEventually :
    D.toBulkIntegrandAEFromPartitionData.localizedEventually =
      D.localizedEventually := by
  rfl

@[simp]
theorem toBulkIntegrandAEFromPartitionData_reconstruction :
    D.toBulkIntegrandAEFromPartitionData.reconstruction =
      D.reconstruction := by
  rfl

@[simp]
theorem toBulkIntegrandAEFromPartitionData_measure :
    D.toBulkIntegrandAEFromPartitionData.measure = D.measure := by
  rfl

@[simp]
theorem toBulkIntegrandAEFromPartitionData_interiorIntegrandTerm :
    D.toBulkIntegrandAEFromPartitionData.interiorIntegrandTerm =
      fun i => localized.localizedInterior.bulkTerm i := by
  rfl

@[simp]
theorem toBulkIntegrandAEFromPartitionData_boundaryIntegrandTerm :
    D.toBulkIntegrandAEFromPartitionData.boundaryIntegrandTerm =
      fun x q => BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q := by
  rfl

@[simp]
theorem toBulkIntegrandAELocalFields_aeData :
    D.toBulkIntegrandAELocalFields.aeData =
      D.toBulkIntegrandAEFromPartitionData.toBulkIntegrandAEData := by
  rfl

@[simp]
theorem toBulkIntegrandAELocalFields_interiorIntegrandTerm :
    D.toBulkIntegrandAELocalFields.interiorIntegrandTerm =
      fun i => localized.localizedInterior.bulkTerm i := by
  rfl

@[simp]
theorem toBulkIntegrandAELocalFields_boundaryIntegrandTerm :
    D.toBulkIntegrandAELocalFields.boundaryIntegrandTerm =
      fun x q => BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q := by
  rfl

end BulkIntegrandAEProjectLocalAutoInput

end BulkExtDerivProjectLocalAuto

end Stokes

end
