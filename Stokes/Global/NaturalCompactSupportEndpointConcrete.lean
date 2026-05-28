import Stokes.Global.NaturalCompactSupportEndpointUnified
import Stokes.Global.BulkExtDerivFromExtDerivConstructor
import Stokes.Global.BulkExtDerivSelectedAlignmentAuto
import Stokes.Global.NaturalEndpointArtificialAuto
import Stokes.Global.ArtificialFromCompactSelectionAuto

/-!
# More concrete compact-support endpoint sources

This module removes two large theorem-facing fields from the unified endpoint
source record:

* `extDerivAE`;
* `artificial`.

The exterior-derivative a.e. input is constructed from existing
`ExtDerivOnSupportData` plus selected-partition support containment.  The
artificial-face field is constructed from the existing support-zero and
cancellation routes.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportEndpointConcrete

universe u w b ei eb f d g

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]

/--
Unified endpoint base sources whose bulk a.e. package is generated from
`ExtDerivOnSupportData`.

This still exposes the real alignment and support hypotheses that are not yet
proved automatically.  It removes the need to hand-build
`BulkIntegrandAEProjectLocalAutoInput`.
-/
structure NaturalCompactSupportEndpointExtDerivBaseSources
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
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
      (BoundaryPiece := BoundaryPiece)
  /-- Localized interior pieces for the selected partition. -/
  localized :
    LocalizedInteriorM8Fields I omega
      (selection.selectedBoxPartitionOfUnity smoothness)
  /-- Existing support-local exterior-derivative reconstruction data. -/
  extDerivOnSupport :
    ExtDerivOnSupportData I omega (M ⊕ M)
      ExtInteriorPiece ExtBoundaryPiece
  /-- The selected bulk labels agree with the reconstruction labels. -/
  extDerivActive :
    selectedPartitionBulkActive
        (selection.selectedBoxPartitionOfUnity smoothness)
        boundaryUnified.toM8TargetImageInput.targetImages =
      extDerivOnSupport.activeCharts
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

namespace NaturalCompactSupportEndpointExtDerivBaseSources

variable
    (S :
      NaturalCompactSupportEndpointExtDerivBaseSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)

/-- The selected partition determined by the compact-support source fields. -/
abbrev selectedPartition : SelectedBoxPartitionOfUnity I omega :=
  S.selection.selectedBoxPartitionOfUnity S.smoothness

/-- Bulk a.e. input generated from support-local ext-derivative reconstruction. -/
def extDerivAE :
    BulkIntegrandAEProjectLocalAutoInput
      (BoundaryChart := M)
      ExtInteriorPiece ExtBoundaryPiece S.selectedPartition
      S.boundaryUnified.toM8TargetImageInput.targetImages S.localized :=
  BulkIntegrandAEProjectLocalAutoInput.ofExtDerivOnSupportDataSelectedPartition
    (P := S.selectedPartition)
    (boundary := S.boundaryUnified.toM8TargetImageInput.targetImages)
    (localized := S.localized)
    S.extDerivOnSupport S.extDerivActive S.extDerivMeasure
    S.omegaSupport_subset_selected

@[simp]
theorem extDerivAE_reconstruction :
    S.extDerivAE.reconstruction =
      S.extDerivOnSupport.toPartitionReconstructionData := by
  rfl

@[simp]
theorem extDerivAE_measure :
    S.extDerivAE.measure = S.extDerivMeasure := by
  rfl

/-- Forget the concrete bulk source route to the unified endpoint base sources. -/
def toUnifiedBaseSources :
    NaturalCompactSupportEndpointUnifiedBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu where
  formData := S.formData
  selection := S.selection
  smoothness := S.smoothness
  orientedBoundaryAtlas := S.orientedBoundaryAtlas
  boundaryUnified := S.boundaryUnified
  localized := S.localized
  extDerivAE := S.extDerivAE
  bulkLocalFacts := S.bulkLocalFacts
  measure_eq_volume := S.measure_eq_volume
  boundaryFaceContinuity := S.boundaryFaceContinuity
  boundaryChartChange := S.boundaryChartChange

@[simp]
theorem toUnifiedBaseSources_extDerivAE :
    S.toUnifiedBaseSources.extDerivAE = S.extDerivAE := by
  rfl

@[simp]
theorem toUnifiedBaseSources_boundaryUnified :
    S.toUnifiedBaseSources.boundaryUnified = S.boundaryUnified := by
  rfl

end NaturalCompactSupportEndpointExtDerivBaseSources

/--
Unified endpoint base sources whose bulk a.e. package is generated from a
selected-partition reconstruction package.

Compared with `NaturalCompactSupportEndpointExtDerivBaseSources`, this record
does not ask for `ExtDerivOnSupportData`.  The support-local ext-derivative
data and selected active/coefficient alignment are generated from the selected
partition constructor.
-/
structure NaturalCompactSupportEndpointSelectedReconstructionBaseSources
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
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
      (BoundaryPiece := BoundaryPiece)
  /-- Localized interior pieces for the selected partition. -/
  localized :
    LocalizedInteriorM8Fields I omega
      (selection.selectedBoxPartitionOfUnity smoothness)
  /-- Existing global bulk/boundary reconstruction data. -/
  reconstruction :
    PartitionReconstructionData I omega (M ⊕ M)
      ExtInteriorPiece ExtBoundaryPiece
  /-- The reconstruction package uses the selected combined labels. -/
  reconstruction_active :
    selectedPartitionBulkActive
        (selection.selectedBoxPartitionOfUnity smoothness)
        boundaryUnified.toM8TargetImageInput.targetImages =
      reconstruction.activeCharts
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

namespace NaturalCompactSupportEndpointSelectedReconstructionBaseSources

variable
    (S :
      NaturalCompactSupportEndpointSelectedReconstructionBaseSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)

/-- The selected partition determined by the compact-support source fields. -/
abbrev selectedPartition : SelectedBoxPartitionOfUnity I omega :=
  S.selection.selectedBoxPartitionOfUnity S.smoothness

/-- Bulk a.e. input generated from selected reconstruction data. -/
def extDerivAE :
    BulkIntegrandAEProjectLocalAutoInput
      (BoundaryChart := M)
      ExtInteriorPiece ExtBoundaryPiece S.selectedPartition
      S.boundaryUnified.toM8TargetImageInput.targetImages S.localized :=
  BulkIntegrandAEProjectLocalAutoInput.ofSelectedPartitionReconstructionData
    (P := S.selectedPartition)
    (boundary := S.boundaryUnified.toM8TargetImageInput.targetImages)
    (localized := S.localized)
    S.reconstruction S.reconstruction_active
    S.omegaSupport_subset_selected S.extDerivMeasure

@[simp]
theorem extDerivAE_reconstruction :
    S.extDerivAE.reconstruction = S.reconstruction := by
  rfl

/-- Forget selected reconstruction sources to the previous ext-deriv base record. -/
def toExtDerivBaseSources :
    NaturalCompactSupportEndpointExtDerivBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu where
  formData := S.formData
  selection := S.selection
  smoothness := S.smoothness
  orientedBoundaryAtlas := S.orientedBoundaryAtlas
  boundaryUnified := S.boundaryUnified
  localized := S.localized
  extDerivOnSupport :=
    ExtDerivOnSupportData.ofSelectedPartitionReconstructionData
      (P := S.selectedPartition)
      (boundary := S.boundaryUnified.toM8TargetImageInput.targetImages)
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      S.reconstruction S.reconstruction_active S.omegaSupport_subset_selected
  extDerivActive := by
    simp
  extDerivMeasure := S.extDerivMeasure
  omegaSupport_subset_selected := S.omegaSupport_subset_selected
  bulkLocalFacts := S.bulkLocalFacts
  measure_eq_volume := S.measure_eq_volume
  boundaryFaceContinuity := S.boundaryFaceContinuity
  boundaryChartChange := S.boundaryChartChange

@[simp]
theorem toExtDerivBaseSources_extDerivAE :
    S.toExtDerivBaseSources.extDerivAE = S.extDerivAE := by
  rfl

/-- Forget selected reconstruction sources to the unified endpoint base sources. -/
def toUnifiedBaseSources :
    NaturalCompactSupportEndpointUnifiedBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  S.toExtDerivBaseSources.toUnifiedBaseSources

end NaturalCompactSupportEndpointSelectedReconstructionBaseSources

/--
Full endpoint source data generated from concrete bulk reconstruction and
strict support of artificial faces.
-/
structure NaturalCompactSupportEndpointStrictSupportSources
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (rho : SmoothPartitionOfUnity M I M univ)
    (mu : Measure (Fin (n + 1) -> Real))
    [IsFiniteMeasureOnCompacts mu]
    [IsManifold I 1 M] where
  /-- All endpoint inputs before artificial-face cancellation. -/
  base :
    NaturalCompactSupportEndpointExtDerivBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu
  /-- Strict support for localized interior representatives. -/
  strictSupport_subset_interiorBox :
    ∀ x, x ∈ base.toUnifiedBaseSources.toBaseInput.selectedPartition.active ->
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (base.toUnifiedBaseSources.toBaseInput.separatedMeasure
              |>.toM8MeasureLocalizationData
              |>.localizedInterior.piece x).sourceChart
            (base.toUnifiedBaseSources.toBaseInput.separatedMeasure
              |>.toM8MeasureLocalizationData
              |>.localizedInterior.piece x).targetChart
            (base.toUnifiedBaseSources.toBaseInput.separatedMeasure
              |>.toM8MeasureLocalizationData
              |>.localizedInterior.piece x).localizedForm) ⊆
        boxInteriorSupportBox
          (base.toUnifiedBaseSources.toBaseInput.separatedMeasure
            |>.toM8MeasureLocalizationData
            |>.localizedInterior.piece x).lowerCorner
          (base.toUnifiedBaseSources.toBaseInput.separatedMeasure
            |>.toM8MeasureLocalizationData
            |>.localizedInterior.piece x).upperCorner

namespace NaturalCompactSupportEndpointStrictSupportSources

variable
    (S :
      NaturalCompactSupportEndpointStrictSupportSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)

/-- The assembled M8 measure-localization data for the concrete endpoint. -/
abbrev measureLocalization :
    M8MeasureLocalizationData I omega
      S.base.toUnifiedBaseSources.toBaseInput.selectedPartition
      S.base.toUnifiedBaseSources.toBaseInput.targetImageInput.targetImages :=
  S.base.toUnifiedBaseSources.toBaseInput.separatedMeasure.toM8MeasureLocalizationData

/-- The previous unified endpoint source record, with artificial fields generated. -/
def toUnifiedSources :
    NaturalCompactSupportEndpointUnifiedSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu where
  base := S.base.toUnifiedBaseSources
  artificial :=
    S.base.toUnifiedBaseSources.toAutoSelectedBaseSources
      |>.artificialOfStrictCompactSupportBoxBuffer
        S.strictSupport_subset_interiorBox

/-- Endpoint theorem with bulk a.e. and artificial-face fields generated internally. -/
theorem stokes :
    S.measureLocalization.bulkMeasureIntegral =
      S.measureLocalization.boundaryMeasureIntegral :=
  S.toUnifiedSources.stokes

end NaturalCompactSupportEndpointStrictSupportSources

/--
Full endpoint source data generated from the two concrete routes now available:

* the bulk exterior-derivative a.e. package comes from selected reconstruction;
* artificial-face cancellation comes from compact selected chart boxes plus
  localized-piece/strict-margin alignment.

This is the current shortest endpoint source: callers no longer supply either
`ExtDerivOnSupportData` or a raw `strictSupport_subset_interiorBox` theorem.
-/
structure NaturalCompactSupportEndpointSelectedCompactSources
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (rho : SmoothPartitionOfUnity M I M univ)
    (mu : Measure (Fin (n + 1) -> Real))
    [IsFiniteMeasureOnCompacts mu]
    [IsManifold I 1 M] where
  /-- All endpoint inputs before artificial-face cancellation, with bulk
  exterior derivative generated from selected reconstruction data. -/
  base :
    NaturalCompactSupportEndpointSelectedReconstructionBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu
  /-- Compact-selection alignment used to generate artificial-face
  cancellation for the assembled endpoint measure data. -/
  compactSelection :
    EndpointCompactSelectionArtificialAlignment
      base.toUnifiedBaseSources.toAutoSelectedBaseSources

namespace NaturalCompactSupportEndpointSelectedCompactSources

variable
    (S :
      NaturalCompactSupportEndpointSelectedCompactSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)

/-- The assembled M8 measure-localization data for the selected/compact endpoint. -/
abbrev measureLocalization :
    M8MeasureLocalizationData I omega
      S.base.toUnifiedBaseSources.toBaseInput.selectedPartition
      S.base.toUnifiedBaseSources.toBaseInput.targetImageInput.targetImages :=
  S.base.toUnifiedBaseSources.toBaseInput.separatedMeasure.toM8MeasureLocalizationData

/-- Artificial-face fields generated from compact selected chart boxes. -/
def artificial :
    M8ArtificialFaceFields I omega BoundaryPiece
      S.base.toUnifiedBaseSources.toBaseInput.selectedPartition
      S.base.toUnifiedBaseSources.toBaseInput.targetImageInput.targetImages
      S.measureLocalization :=
  S.base.toUnifiedBaseSources.toAutoSelectedBaseSources
    |>.artificialOfCompactSelection S.compactSelection

@[simp]
theorem artificial_active :
    S.artificial.artificialFaces.activeCharts =
      S.base.toUnifiedBaseSources.toBaseInput.selectedPartition.active :=
  EndpointCompactSelectionArtificialAlignment.toM8ArtificialFaceFields_active
    S.compactSelection

/-- The previous unified endpoint source record, with both generated fields. -/
def toUnifiedSources :
    NaturalCompactSupportEndpointUnifiedSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu where
  base := S.base.toUnifiedBaseSources
  artificial := S.artificial

@[simp]
theorem toUnifiedSources_base :
    S.toUnifiedSources.base = S.base.toUnifiedBaseSources := by
  rfl

@[simp]
theorem toUnifiedSources_artificial :
    S.toUnifiedSources.artificial = S.artificial := by
  rfl

/--
Endpoint theorem with bulk a.e. and artificial-face fields generated from
selected reconstruction plus compact selected chart boxes.
-/
theorem stokes :
    S.measureLocalization.bulkMeasureIntegral =
      S.measureLocalization.boundaryMeasureIntegral :=
  S.toUnifiedSources.stokes

end NaturalCompactSupportEndpointSelectedCompactSources

end NaturalCompactSupportEndpointConcrete

end Stokes

end
