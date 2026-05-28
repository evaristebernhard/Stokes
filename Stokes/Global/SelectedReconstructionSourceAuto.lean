import Stokes.Global.NaturalCompactSupportEndpointConcrete

/-!
# Selected reconstruction sources for compact-support endpoints

This file isolates the last selected-reconstruction bookkeeping input:

`selectedPartitionBulkActive P boundary = reconstruction.activeCharts`.

The equality is still real data when the reconstruction is arbitrary, but many
callers get it from a more structured selected-partition source.  The records
and projections below package that origin so endpoint constructors no longer
need a loose `reconstruction_active` argument.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section SelectedReconstructionSourceAuto

universe u w cb pb ei eb b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryChart : Type cb} {BoundaryPiece : Type pb}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {P : SelectedBoxPartitionOfUnity I omega}
variable {boundary : BoundaryPieceFamilyInput I omega BoundaryChart BoundaryPiece}
variable {localized : LocalizedInteriorM8Fields I omega P}

/--
Selected reconstruction source.

This is the smallest stable package for the active-set compatibility of a
global reconstruction with the selected interior charts plus boundary charts.
It lets higher endpoint constructors accept a source of the reconstruction
instead of a loose equality proof.
-/
structure SelectedPartitionReconstructionSource
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundary : BoundaryPieceFamilyInput I omega BoundaryChart BoundaryPiece)
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb) where
  /-- Reconstruction fields on the selected interior/boundary labels. -/
  reconstruction :
    PartitionReconstructionData I omega (M ⊕ BoundaryChart)
      ExtInteriorPiece ExtBoundaryPiece
  /-- The reconstruction labels are exactly the selected bulk labels. -/
  active_eq :
    selectedPartitionBulkActive P boundary = reconstruction.activeCharts

namespace SelectedPartitionReconstructionSource

variable
    (S :
      SelectedPartitionReconstructionSource I omega P boundary
        ExtInteriorPiece ExtBoundaryPiece)

@[simp]
theorem selectedPartitionBulkActive_eq_activeCharts :
    selectedPartitionBulkActive P boundary = S.reconstruction.activeCharts :=
  S.active_eq

/-- Constructor from raw reconstruction data and its active-set compatibility. -/
def ofPartitionReconstructionData
    (R :
      PartitionReconstructionData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hactive : selectedPartitionBulkActive P boundary = R.activeCharts) :
    SelectedPartitionReconstructionSource I omega P boundary
      ExtInteriorPiece ExtBoundaryPiece where
  reconstruction := R
  active_eq := hactive

@[simp]
theorem ofPartitionReconstructionData_reconstruction
    (R :
      PartitionReconstructionData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hactive : selectedPartitionBulkActive P boundary = R.activeCharts) :
    (ofPartitionReconstructionData
      (I := I) (omega := omega) (P := P) (boundary := boundary)
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      R hactive).reconstruction = R := by
  rfl

/--
Source extracted from a selected partition exterior-derivative constructor.

The active-set equality is projected from the fact that the constructor's
localized-eventual package is the canonical selected-partition package.
-/
def ofSelectedPartitionExtDerivConstructorData
    (D :
      PartitionExtDerivConstructorData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (homegaSupport : ManifoldForm.support I omega ⊆ P.K)
    (hselected :
      D.localizedEventually =
        P.bulkSelectedLocalizedEventually
          (BoundaryChart := BoundaryChart) boundary homegaSupport) :
    SelectedPartitionReconstructionSource I omega P boundary
      ExtInteriorPiece ExtBoundaryPiece where
  reconstruction := D.toPartitionReconstructionData
  active_eq := by
    have hD :
        D.extDerivOnSupport.activeCharts =
          selectedPartitionBulkActive P boundary :=
      D.extDerivOnSupport_activeCharts_eq_selected_of_localizedEventually
        (P := P) (boundary := boundary) homegaSupport hselected
    simpa [PartitionExtDerivConstructorData.toPartitionReconstructionData]
      using hD.symm

@[simp]
theorem ofSelectedPartitionExtDerivConstructorData_reconstruction
    (D :
      PartitionExtDerivConstructorData I omega (M ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (homegaSupport : ManifoldForm.support I omega ⊆ P.K)
    (hselected :
      D.localizedEventually =
        P.bulkSelectedLocalizedEventually
          (BoundaryChart := BoundaryChart) boundary homegaSupport) :
    (ofSelectedPartitionExtDerivConstructorData
      (I := I) (omega := omega) (P := P) (boundary := boundary)
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      D homegaSupport hselected).reconstruction =
      D.toPartitionReconstructionData := by
  rfl

/--
Source extracted from an already assembled project-local automatic bulk input.

This is useful when the caller has constructed the a.e. bulk package first:
the selected active-set equality is stored in that package's localized-eventual
alignment fields.
-/
def ofBulkIntegrandAEProjectLocalAutoInput
    (D :
      BulkIntegrandAEProjectLocalAutoInput
        (BoundaryChart := BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece P boundary localized) :
    SelectedPartitionReconstructionSource I omega P boundary
      ExtInteriorPiece ExtBoundaryPiece where
  reconstruction := D.reconstruction
  active_eq := by
    calc
      selectedPartitionBulkActive P boundary =
          D.localizedEventually.activeCharts := D.localizedEventually_active.symm
      _ = D.reconstruction.activeCharts :=
          D.localizedEventually_active_eq_reconstruction

@[simp]
theorem ofBulkIntegrandAEProjectLocalAutoInput_reconstruction
    (D :
      BulkIntegrandAEProjectLocalAutoInput
        (BoundaryChart := BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece P boundary localized) :
    (ofBulkIntegrandAEProjectLocalAutoInput
      (I := I) (omega := omega) (P := P) (boundary := boundary)
      (localized := localized)
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      D).reconstruction = D.reconstruction := by
  rfl

/-- Support-local ext-derivative data generated from the selected source. -/
def toExtDerivOnSupportData
    (homegaSupport : ManifoldForm.support I omega ⊆ P.K) :
    ExtDerivOnSupportData I omega (M ⊕ BoundaryChart)
      ExtInteriorPiece ExtBoundaryPiece :=
  ExtDerivOnSupportData.ofSelectedPartitionReconstructionData
    (P := P) (boundary := boundary)
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    S.reconstruction S.active_eq homegaSupport

@[simp]
theorem toExtDerivOnSupportData_activeCharts
    (homegaSupport : ManifoldForm.support I omega ⊆ P.K) :
    (S.toExtDerivOnSupportData homegaSupport).activeCharts =
      selectedPartitionBulkActive P boundary := by
  simp [toExtDerivOnSupportData]

/-- Selected partition exterior-derivative constructor generated from the source. -/
def toPartitionExtDerivConstructorData
    (homegaSupport : ManifoldForm.support I omega ⊆ P.K) :
    PartitionExtDerivConstructorData I omega (M ⊕ BoundaryChart)
      ExtInteriorPiece ExtBoundaryPiece :=
  PartitionExtDerivConstructorData.ofSelectedPartitionReconstructionData
    (P := P) (boundary := boundary)
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    S.reconstruction S.active_eq homegaSupport

@[simp]
theorem toPartitionExtDerivConstructorData_reconstruction
    (homegaSupport : ManifoldForm.support I omega ⊆ P.K) :
    (S.toPartitionExtDerivConstructorData homegaSupport).toPartitionReconstructionData =
      S.reconstruction := by
  rfl

/-- Project-local automatic bulk a.e. input generated from the source. -/
def toBulkIntegrandAEProjectLocalAutoInput
    (localized : LocalizedInteriorM8Fields I omega P)
    (homegaSupport : ManifoldForm.support I omega ⊆ P.K)
    (measure : M -> M -> Measure (Fin (n + 1) -> Real)) :
    BulkIntegrandAEProjectLocalAutoInput
      (BoundaryChart := BoundaryChart)
      ExtInteriorPiece ExtBoundaryPiece P boundary localized :=
  BulkIntegrandAEProjectLocalAutoInput.ofSelectedPartitionReconstructionData
    (P := P) (boundary := boundary) (localized := localized)
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    S.reconstruction S.active_eq homegaSupport measure

@[simp]
theorem toBulkIntegrandAEProjectLocalAutoInput_reconstruction
    (localized : LocalizedInteriorM8Fields I omega P)
    (homegaSupport : ManifoldForm.support I omega ⊆ P.K)
    (measure : M -> M -> Measure (Fin (n + 1) -> Real)) :
    (S.toBulkIntegrandAEProjectLocalAutoInput
      localized homegaSupport measure).reconstruction =
      S.reconstruction := by
  rfl

@[simp]
theorem toBulkIntegrandAEProjectLocalAutoInput_measure
    (localized : LocalizedInteriorM8Fields I omega P)
    (homegaSupport : ManifoldForm.support I omega ⊆ P.K)
    (measure : M -> M -> Measure (Fin (n + 1) -> Real)) :
    (S.toBulkIntegrandAEProjectLocalAutoInput
      localized homegaSupport measure).measure =
      measure := by
  rfl

end SelectedPartitionReconstructionSource

section EndpointSource

variable {BoundaryPiece' : Type b}
variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]

/--
Compact-support endpoint base sources whose selected reconstruction is supplied
as a single source package rather than as `reconstruction` plus a loose active
equality.
-/
structure NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece' : Type b)
    (rho : SmoothPartitionOfUnity M I M univ)
    (mu : Measure (Fin (n + 1) -> Real))
    [IsFiniteMeasureOnCompacts mu]
    [IsManifold I 1 M] where
  /-- Compactly supported smooth input form. -/
  formData : CompactlySupportedSmoothFormData I omega
  /-- Finite active chart selection over the support. -/
  selection :
    CompactSupportFiniteActiveSelection
      (I := I) rho formData.supportSet formData.isCompact_supportSet omega
  /-- Smooth selected compact boxes. -/
  smoothness :
    ActiveCompactBoxSmoothness selection.finiteActive
      selection.supportData.box omega
  /-- Oriented boundary-chart atlas. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Unified boundary source-shrink and project-local data. -/
  boundaryUnified :
    BoundarySourceAlignmentUnifiedData
      (I := I) (omega := omega)
      (selectedPartition := selection.selectedBoxPartitionOfUnity smoothness)
      (orientedBoundaryAtlas := orientedBoundaryAtlas)
      (BoundaryPiece := BoundaryPiece')
  /-- Localized interior pieces for the selected partition. -/
  localized :
    LocalizedInteriorM8Fields I omega
      (selection.selectedBoxPartitionOfUnity smoothness)
  /-- Selected reconstruction source; this packages `reconstruction_active`. -/
  reconstructionSource :
    SelectedPartitionReconstructionSource I omega
      (selection.selectedBoxPartitionOfUnity smoothness)
      boundaryUnified.toM8TargetImageInput.targetImages
      ExtInteriorPiece ExtBoundaryPiece
  /-- Chartwise measure used by the a.e. bulk comparison. -/
  extDerivMeasure : M -> M -> Measure (Fin (n + 1) -> Real)
  /-- The original form support is contained in the selected compact support set. -/
  omegaSupport_subset_selected :
    ManifoldForm.support I omega ⊆
      (selection.selectedBoxPartitionOfUnity smoothness).K
  /-- Local canonical bulk facts. -/
  bulkLocalFacts :
    SelectedPartitionBulkCanonicalLocalFacts
      (selection.selectedBoxPartitionOfUnity smoothness)
      boundaryUnified.toM8TargetImageInput.targetImages localized
  /-- The selected bulk measure is the ambient volume measure. -/
  measure_eq_volume : mu = volume
  /-- Canonical lower-face continuity for the unified project-local data. -/
  boundaryFaceContinuity :
    ProjectLocalBoundaryCanonicalFaceContinuityData
      boundaryUnified.toProjectLocalGlobalStokesData
  /-- Selected-target chart-change data for the unified project-local data. -/
  boundaryChartChange :
    BoundaryChartChangeSelectedFamilyData
      boundaryUnified.toProjectLocalGlobalStokesData

namespace NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources

variable
    (S :
      NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece' rho mu)

/-- The selected partition determined by the compact-support source fields. -/
abbrev selectedPartition : SelectedBoxPartitionOfUnity I omega :=
  S.selection.selectedBoxPartitionOfUnity S.smoothness

/-- The reconstruction carried by the selected source. -/
abbrev reconstruction :
    PartitionReconstructionData I omega (M ⊕ M)
      ExtInteriorPiece ExtBoundaryPiece :=
  S.reconstructionSource.reconstruction

/-- Stable projection for the packaged active-set equality. -/
theorem reconstruction_active :
    selectedPartitionBulkActive S.selectedPartition
        S.boundaryUnified.toM8TargetImageInput.targetImages =
      S.reconstruction.activeCharts :=
  S.reconstructionSource.active_eq

/--
Forget the source package to the previous endpoint base record.

This is the main handoff for existing endpoint APIs: all fields are unchanged,
but `reconstruction_active` is projected from `reconstructionSource`.
-/
def toSelectedReconstructionBaseSources :
    NaturalCompactSupportEndpointSelectedReconstructionBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece' rho mu where
  formData := S.formData
  selection := S.selection
  smoothness := S.smoothness
  orientedBoundaryAtlas := S.orientedBoundaryAtlas
  boundaryUnified := S.boundaryUnified
  localized := S.localized
  reconstruction := S.reconstruction
  reconstruction_active := S.reconstruction_active
  extDerivMeasure := S.extDerivMeasure
  omegaSupport_subset_selected := S.omegaSupport_subset_selected
  bulkLocalFacts := S.bulkLocalFacts
  measure_eq_volume := S.measure_eq_volume
  boundaryFaceContinuity := S.boundaryFaceContinuity
  boundaryChartChange := S.boundaryChartChange

@[simp]
theorem toSelectedReconstructionBaseSources_reconstruction :
    S.toSelectedReconstructionBaseSources.reconstruction =
      S.reconstruction := by
  rfl

@[simp]
theorem toSelectedReconstructionBaseSources_extDerivMeasure :
    S.toSelectedReconstructionBaseSources.extDerivMeasure =
      S.extDerivMeasure := by
  rfl

/-- Bulk a.e. input generated from the packaged selected reconstruction source. -/
def extDerivAE :
    BulkIntegrandAEProjectLocalAutoInput
      (BoundaryChart := M)
      ExtInteriorPiece ExtBoundaryPiece S.selectedPartition
      S.boundaryUnified.toM8TargetImageInput.targetImages S.localized :=
  S.reconstructionSource.toBulkIntegrandAEProjectLocalAutoInput
    S.localized S.omegaSupport_subset_selected S.extDerivMeasure

@[simp]
theorem extDerivAE_eq_previous :
    S.extDerivAE =
      S.toSelectedReconstructionBaseSources.extDerivAE := by
  rfl

/-- The previous auto-selected endpoint base generated after forgetting the source. -/
abbrev autoSelectedBaseSources :
    NaturalCompactSupportEndpointAutoSelectedBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece' rho mu :=
  (S.toSelectedReconstructionBaseSources.toUnifiedBaseSources).toAutoSelectedBaseSources

/-- Selected/compact endpoint sources, still using the existing artificial route. -/
def toSelectedCompactSources
    (compactSelection :
      EndpointCompactSelectionArtificialAlignment S.autoSelectedBaseSources) :
    NaturalCompactSupportEndpointSelectedCompactSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece' rho mu where
  base := S.toSelectedReconstructionBaseSources
  compactSelection := compactSelection

@[simp]
theorem toSelectedCompactSources_base
    (compactSelection :
      EndpointCompactSelectionArtificialAlignment S.autoSelectedBaseSources) :
    (S.toSelectedCompactSources compactSelection).base =
      S.toSelectedReconstructionBaseSources := by
  rfl

/--
Endpoint theorem from the source-packaged selected reconstruction and the
existing compact-selection artificial alignment.
-/
theorem stokes_ofCompactSelection
    (compactSelection :
      EndpointCompactSelectionArtificialAlignment S.autoSelectedBaseSources) :
    (S.toSelectedCompactSources compactSelection).measureLocalization.bulkMeasureIntegral =
      ((S.toSelectedCompactSources compactSelection).measureLocalization).boundaryMeasureIntegral :=
  (S.toSelectedCompactSources compactSelection).stokes

end NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources

end EndpointSource

end SelectedReconstructionSourceAuto

end Stokes

end
