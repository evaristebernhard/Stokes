import Stokes.Global.BulkLocalTermCompactSupportConstructor
import Stokes.Global.BulkExtDerivSelectedAlignmentAuto
import Stokes.Global.SelectedReconstructionSourceAuto

/-!
# Canonical bulk local facts from exterior-derivative sources

This module connects the canonical bulk-local-facts layer to the existing
exterior-derivative reconstruction routes.

`SelectedPartitionBulkCanonicalLocalFacts` itself is deliberately local: it
only needs the boundary active-set alignment and the canonical compact-support
constructor.  The exterior-derivative sources matter because the same caller
usually also needs the matching project-local measure terms and
`BulkIntegrandAEFromPartitionData`.  The bundle records below keep those three
objects synchronized without introducing new measure theory.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkCanonicalLocalFactsFromExtDerivAuto

universe u w ei eb b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {P : SelectedBoxPartitionOfUnity I omega}
variable {boundary : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {localized : LocalizedInteriorM8Fields I omega P}

namespace SelectedPartitionBulkCanonicalLocalFacts

/--
Canonical local facts from the single genuinely local active-set alignment.

This is a named wrapper around `ofCanonicalCompactSupport`, useful for routes
whose main source data is exterior-derivative or reconstruction data.
-/
def ofBoundaryActive
    (localized : LocalizedInteriorM8Fields I omega P)
    (boundary_active : boundary.activeCharts = P.active) :
    SelectedPartitionBulkCanonicalLocalFacts
      (P := P) (boundary := boundary) localized :=
  ofCanonicalCompactSupport localized boundary_active

@[simp]
theorem ofBoundaryActive_boundary_active
    (localized : LocalizedInteriorM8Fields I omega P)
    (boundary_active : boundary.activeCharts = P.active) :
    (ofBoundaryActive
      (P := P) (boundary := boundary) localized boundary_active).boundary_active =
      boundary_active :=
  rfl

/--
Local facts associated to an already-built project-local bulk a.e. input.

The a.e. input fixes the reconstruction and project-local exterior-derivative
side; the local canonical support facts still only need the boundary active
alignment.
-/
def ofBulkIntegrandAEProjectLocalAutoInput
    (_D :
      BulkIntegrandAEProjectLocalAutoInput
        (BoundaryChart := M)
        ExtInteriorPiece ExtBoundaryPiece P boundary localized)
    (boundary_active : boundary.activeCharts = P.active) :
    SelectedPartitionBulkCanonicalLocalFacts
      (P := P) (boundary := boundary) localized :=
  ofBoundaryActive localized boundary_active

/--
Local facts attached to a selected-partition exterior-derivative constructor.

The constructor is kept as an argument so callers can use one source object for
both the local facts here and the bulk a.e. constructor below.
-/
def ofPartitionExtDerivConstructorData
    (_D :
      PartitionExtDerivConstructorData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (boundary_active : boundary.activeCharts = P.active) :
    SelectedPartitionBulkCanonicalLocalFacts
      (P := P) (boundary := boundary) localized :=
  ofBoundaryActive localized boundary_active

/--
Local facts attached to raw selected-partition reconstruction data.

The active/support hypotheses are intentionally accepted in the same shape as
the bulk a.e. route, even though the local compact-support facts themselves
only consume `boundary_active`.
-/
def ofSelectedPartitionReconstructionData
    (_R :
      PartitionReconstructionData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (_hactive : selectedPartitionBulkActive P boundary = _R.activeCharts)
    (_homegaSupport : ManifoldForm.support I omega ⊆ P.K)
    (boundary_active : boundary.activeCharts = P.active) :
    SelectedPartitionBulkCanonicalLocalFacts
      (P := P) (boundary := boundary) localized :=
  ofBoundaryActive localized boundary_active

end SelectedPartitionBulkCanonicalLocalFacts

/--
Synchronized canonical bulk data generated from a selected-partition
exterior-derivative constructor.

This record removes the common mismatch where callers build `bulkLocalFacts`,
`measureTerms`, and `extDerivAE` from slightly different intermediate data.
-/
structure BulkCanonicalLocalFactsExtDerivConstructorRoute
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundary : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (localized : LocalizedInteriorM8Fields I omega P) where
  /-- Boundary source pieces use the selected active chart set. -/
  boundary_active : boundary.activeCharts = P.active
  /-- Selected-partition exterior-derivative constructor data. -/
  extDerivConstructor :
    PartitionExtDerivConstructorData I omega (M ⊕ M)
      ExtInteriorPiece ExtBoundaryPiece
  /-- The selected compact support controls the original form. -/
  omegaSupport_subset_selected : ManifoldForm.support I omega ⊆ P.K
  /-- The constructor's local-eventual source is the canonical selected one. -/
  localizedEventually_eq_selected :
    extDerivConstructor.localizedEventually =
      P.bulkSelectedLocalizedEventually
        (BoundaryChart := M) boundary omegaSupport_subset_selected
  /-- Chartwise measure used by the a.e. comparison. -/
  measure : M -> M -> Measure (Fin (n + 1) -> Real)

namespace BulkCanonicalLocalFactsExtDerivConstructorRoute

variable
    (D :
      BulkCanonicalLocalFactsExtDerivConstructorRoute
        ExtInteriorPiece ExtBoundaryPiece P boundary localized)

/-- Canonical local facts generated from the route's active-set alignment. -/
def localFacts :
    SelectedPartitionBulkCanonicalLocalFacts
      (P := P) (boundary := boundary) localized :=
  SelectedPartitionBulkCanonicalLocalFacts.ofPartitionExtDerivConstructorData
    (P := P) (boundary := boundary) (localized := localized)
    D.extDerivConstructor D.boundary_active

@[simp]
theorem localFacts_boundary_active :
    D.localFacts.boundary_active = D.boundary_active :=
  rfl

/-- Canonical project-local measure terms matching the route's local facts. -/
def measureTerms :
    BulkMeasureLocalizationTermFields localized.localizedInterior boundary :=
  let _boundaryActive := D.boundary_active
  BulkMeasureLocalizationTermFields.ofProjectLocalBoxTerms
    localized.localizedInterior boundary

@[simp]
theorem measureTerms_interiorMeasureTerm (i : M) :
    D.measureTerms.interiorMeasureTerm i =
      localized.localizedInterior.bulkTerm i :=
  rfl

@[simp]
theorem measureTerms_boundaryMeasureTerm (x : M) (q : BoundaryPiece) :
    D.measureTerms.boundaryMeasureTerm x q =
      BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q :=
  rfl

/-- The automatically available project-local box API for the canonical terms. -/
def measureBox :
    MeasureLocalBoxTermAPI D.measureTerms :=
  BulkMeasureLocalizationTermFields.projectLocalBoxTermAPI
    localized.localizedInterior boundary

/--
Project-local automatic bulk a.e. input generated from the same constructor
that indexes the local facts.
-/
def extDerivAEProjectLocal :
    BulkIntegrandAEProjectLocalAutoInput
      (BoundaryChart := M)
      ExtInteriorPiece ExtBoundaryPiece P boundary localized :=
  BulkIntegrandAEProjectLocalAutoInput.ofSelectedPartitionExtDerivConstructorData
    (P := P) (boundary := boundary) (localized := localized)
    D.extDerivConstructor D.omegaSupport_subset_selected
    D.localizedEventually_eq_selected D.measure

@[simp]
theorem extDerivAEProjectLocal_reconstruction :
    D.extDerivAEProjectLocal.reconstruction =
      D.extDerivConstructor.toPartitionReconstructionData :=
  rfl

@[simp]
theorem extDerivAEProjectLocal_measure :
    D.extDerivAEProjectLocal.measure = D.measure :=
  rfl

/-- The full bulk a.e. package with canonical project-local measure terms. -/
def extDerivAE :
    BulkIntegrandAEFromPartitionData
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      P boundary localized D.measureTerms :=
  D.extDerivAEProjectLocal.toBulkIntegrandAEFromPartitionData

@[simp]
theorem extDerivAE_localizedEventually :
    D.extDerivAE.localizedEventually =
      D.extDerivConstructor.localizedEventually :=
  rfl

@[simp]
theorem extDerivAE_reconstruction :
    D.extDerivAE.reconstruction =
      D.extDerivConstructor.toPartitionReconstructionData :=
  rfl

/-- Selected reconstruction source generated by the same route. -/
def selectedReconstructionSource :
    SelectedPartitionReconstructionSource I omega P boundary
      ExtInteriorPiece ExtBoundaryPiece :=
  SelectedPartitionReconstructionSource.ofBulkIntegrandAEProjectLocalAutoInput
    (P := P) (boundary := boundary) (localized := localized)
    D.extDerivAEProjectLocal

@[simp]
theorem selectedReconstructionSource_reconstruction :
    D.selectedReconstructionSource.reconstruction =
      D.extDerivConstructor.toPartitionReconstructionData :=
  rfl

end BulkCanonicalLocalFactsExtDerivConstructorRoute

/--
Synchronized canonical bulk data generated from selected-partition
reconstruction data.

Compared with `BulkCanonicalLocalFactsExtDerivConstructorRoute`, this is the
shorter route when the caller has not separately named the selected
`PartitionExtDerivConstructorData`; it is built internally from the selected
partition and support containment.
-/
structure BulkCanonicalLocalFactsReconstructionRoute
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundary : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (localized : LocalizedInteriorM8Fields I omega P) where
  /-- Boundary source pieces use the selected active chart set. -/
  boundary_active : boundary.activeCharts = P.active
  /-- Reconstruction fields on the selected combined labels. -/
  reconstruction :
    PartitionReconstructionData I omega (M ⊕ M)
      ExtInteriorPiece ExtBoundaryPiece
  /-- The reconstruction labels are exactly the selected bulk labels. -/
  reconstruction_active :
    selectedPartitionBulkActive P boundary = reconstruction.activeCharts
  /-- The selected compact support controls the original form. -/
  omegaSupport_subset_selected : ManifoldForm.support I omega ⊆ P.K
  /-- Chartwise measure used by the a.e. comparison. -/
  measure : M -> M -> Measure (Fin (n + 1) -> Real)

namespace BulkCanonicalLocalFactsReconstructionRoute

variable
    (D :
      BulkCanonicalLocalFactsReconstructionRoute
        ExtInteriorPiece ExtBoundaryPiece P boundary localized)

/-- Canonical selected exterior-derivative constructor generated from the route. -/
def extDerivConstructor :
    PartitionExtDerivConstructorData I omega (M ⊕ M)
      ExtInteriorPiece ExtBoundaryPiece :=
  PartitionExtDerivConstructorData.ofSelectedPartitionReconstructionData
    (P := P) (boundary := boundary)
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    D.reconstruction D.reconstruction_active
    D.omegaSupport_subset_selected

@[simp]
theorem extDerivConstructor_reconstruction :
    D.extDerivConstructor.toPartitionReconstructionData =
      D.reconstruction :=
  rfl

/-- Forget the reconstruction route to the constructor-indexed route. -/
def toExtDerivConstructorRoute :
    BulkCanonicalLocalFactsExtDerivConstructorRoute
      ExtInteriorPiece ExtBoundaryPiece P boundary localized where
  boundary_active := D.boundary_active
  extDerivConstructor := D.extDerivConstructor
  omegaSupport_subset_selected := D.omegaSupport_subset_selected
  localizedEventually_eq_selected := by
    rfl
  measure := D.measure

/-- Canonical local facts generated from the reconstruction route. -/
def localFacts :
    SelectedPartitionBulkCanonicalLocalFacts
      (P := P) (boundary := boundary) localized :=
  D.toExtDerivConstructorRoute.localFacts

@[simp]
theorem localFacts_boundary_active :
    D.localFacts.boundary_active = D.boundary_active :=
  rfl

/-- Canonical project-local measure terms matching the route's local facts. -/
def measureTerms :
    BulkMeasureLocalizationTermFields localized.localizedInterior boundary :=
  BulkCanonicalLocalFactsExtDerivConstructorRoute.measureTerms
    D.toExtDerivConstructorRoute

@[simp]
theorem measureTerms_eq :
    D.measureTerms =
      BulkMeasureLocalizationTermFields.ofProjectLocalBoxTerms
        localized.localizedInterior boundary :=
  rfl

/-- The automatically available project-local box API for the canonical terms. -/
def measureBox :
    MeasureLocalBoxTermAPI D.measureTerms :=
  BulkCanonicalLocalFactsExtDerivConstructorRoute.measureBox
    D.toExtDerivConstructorRoute

/-- Project-local automatic bulk a.e. input generated from reconstruction data. -/
def extDerivAEProjectLocal :
    BulkIntegrandAEProjectLocalAutoInput
      (BoundaryChart := M)
      ExtInteriorPiece ExtBoundaryPiece P boundary localized :=
  BulkCanonicalLocalFactsExtDerivConstructorRoute.extDerivAEProjectLocal
    D.toExtDerivConstructorRoute

@[simp]
theorem extDerivAEProjectLocal_reconstruction :
    D.extDerivAEProjectLocal.reconstruction =
      D.reconstruction :=
  rfl

@[simp]
theorem extDerivAEProjectLocal_measure :
    D.extDerivAEProjectLocal.measure = D.measure :=
  rfl

/-- The full bulk a.e. package with canonical project-local measure terms. -/
def extDerivAE :
    BulkIntegrandAEFromPartitionData
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      P boundary localized D.measureTerms :=
  BulkCanonicalLocalFactsExtDerivConstructorRoute.extDerivAE
    D.toExtDerivConstructorRoute

@[simp]
theorem extDerivAE_reconstruction :
    D.extDerivAE.reconstruction =
      D.reconstruction :=
  rfl

/-- Selected reconstruction source generated from the same reconstruction route. -/
def selectedReconstructionSource :
    SelectedPartitionReconstructionSource I omega P boundary
      ExtInteriorPiece ExtBoundaryPiece :=
  BulkCanonicalLocalFactsExtDerivConstructorRoute.selectedReconstructionSource
    D.toExtDerivConstructorRoute

@[simp]
theorem selectedReconstructionSource_reconstruction :
    D.selectedReconstructionSource.reconstruction =
      D.reconstruction :=
  rfl

end BulkCanonicalLocalFactsReconstructionRoute

end BulkCanonicalLocalFactsFromExtDerivAuto

end Stokes

end
