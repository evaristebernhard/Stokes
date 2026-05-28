import Stokes.Global.NaturalCompactSupportEndpointConcrete

/-!
# Selected compact-support endpoint automation

This file gives a direct caller-facing route from selected reconstruction data
and compact-selection artificial-face alignment to the current compact-support
endpoint theorem.

The main reduction is ergonomic but real: callers no longer need to separately
materialize the selected endpoint source record, the bulk a.e. field, and the
artificial-face field.  The selected reconstruction active equality remains the
honest reconstruction compatibility hypothesis.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportEndpointSelectedAuto

universe u w b ei eb

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

namespace NaturalCompactSupportEndpointSelectedReconstructionBaseSources

variable
    (S :
      NaturalCompactSupportEndpointSelectedReconstructionBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu)

/-- The auto-selected endpoint base generated from the selected reconstruction route. -/
abbrev autoSelectedBaseSources :
    NaturalCompactSupportEndpointAutoSelectedBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  S.toUnifiedBaseSources.toAutoSelectedBaseSources

/-- The assembled M8 measure-localization data for this selected endpoint base. -/
abbrev measureLocalization :
    M8MeasureLocalizationData I omega
      S.toUnifiedBaseSources.toBaseInput.selectedPartition
      S.toUnifiedBaseSources.toBaseInput.targetImageInput.targetImages :=
  S.toUnifiedBaseSources.toBaseInput.separatedMeasure.toM8MeasureLocalizationData

/--
The selected partition exterior-derivative constructor used internally by
`S.extDerivAE`.
-/
def selectedPartitionExtDerivConstructor :
    PartitionExtDerivConstructorData I omega (M ⊕ M)
      ExtInteriorPiece ExtBoundaryPiece :=
  PartitionExtDerivConstructorData.ofSelectedPartitionReconstructionData
    (P := S.selectedPartition)
    (boundary := S.boundaryUnified.toM8TargetImageInput.targetImages)
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    S.reconstruction S.reconstruction_active S.omegaSupport_subset_selected

@[simp]
theorem selectedPartitionExtDerivConstructor_reconstruction :
    S.selectedPartitionExtDerivConstructor.toPartitionReconstructionData =
      S.reconstruction := by
  rfl

@[simp]
theorem selectedPartitionExtDerivConstructor_extDerivOnSupport_activeCharts :
    S.selectedPartitionExtDerivConstructor.extDerivOnSupport.activeCharts =
      selectedPartitionBulkActive S.selectedPartition
        S.boundaryUnified.toM8TargetImageInput.targetImages := by
  simp [selectedPartitionExtDerivConstructor,
    PartitionExtDerivConstructorData
      .ofSelectedPartitionReconstructionData_extDerivOnSupport_activeCharts
        (P := S.selectedPartition)
        (boundary := S.boundaryUnified.toM8TargetImageInput.targetImages)
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        S.reconstruction S.reconstruction_active S.omegaSupport_subset_selected]

/--
The bulk a.e. input generated through the explicit selected constructor.
This exposes the active-equality -> constructor -> bulk-a.e. path as a stable
API without asking callers for a separate constructor field.
-/
def extDerivAEFromSelectedConstructor :
    BulkIntegrandAEProjectLocalAutoInput
      (BoundaryChart := M)
      ExtInteriorPiece ExtBoundaryPiece S.selectedPartition
      S.boundaryUnified.toM8TargetImageInput.targetImages S.localized :=
  BulkIntegrandAEProjectLocalAutoInput.ofSelectedPartitionExtDerivConstructorData
    (P := S.selectedPartition)
    (boundary := S.boundaryUnified.toM8TargetImageInput.targetImages)
    (localized := S.localized)
    S.selectedPartitionExtDerivConstructor
    S.omegaSupport_subset_selected rfl S.extDerivMeasure

@[simp]
theorem extDerivAEFromSelectedConstructor_eq :
    S.extDerivAEFromSelectedConstructor = S.extDerivAE := by
  rfl

/-- Selected compact endpoint sources generated from base data and compact alignment. -/
def toSelectedCompactSources
    (alignment :
      EndpointCompactSelectionArtificialAlignment S.autoSelectedBaseSources) :
    NaturalCompactSupportEndpointSelectedCompactSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu where
  base := S
  compactSelection := alignment

@[simp]
theorem toSelectedCompactSources_base
    (alignment :
      EndpointCompactSelectionArtificialAlignment S.autoSelectedBaseSources) :
    (S.toSelectedCompactSources alignment).base = S := by
  rfl

@[simp]
theorem toSelectedCompactSources_compactSelection
    (alignment :
      EndpointCompactSelectionArtificialAlignment S.autoSelectedBaseSources) :
    (S.toSelectedCompactSources alignment).compactSelection = alignment := by
  rfl

/-- Artificial-face fields generated directly from compact selected boxes. -/
def artificialOfCompactSelection
    (alignment :
      EndpointCompactSelectionArtificialAlignment S.autoSelectedBaseSources) :
    M8ArtificialFaceFields I omega BoundaryPiece
      S.toUnifiedBaseSources.toBaseInput.selectedPartition
      S.toUnifiedBaseSources.toBaseInput.targetImageInput.targetImages
      S.measureLocalization :=
  (S.toSelectedCompactSources alignment).artificial

@[simp]
theorem artificialOfCompactSelection_active
    (alignment :
      EndpointCompactSelectionArtificialAlignment S.autoSelectedBaseSources) :
    (S.artificialOfCompactSelection alignment).artificialFaces.activeCharts =
      S.toUnifiedBaseSources.toBaseInput.selectedPartition.active := by
  exact (S.toSelectedCompactSources alignment).artificial_active

/--
Unified endpoint sources generated from selected reconstruction plus compact
selected chart-box artificial-face alignment.
-/
def toUnifiedSourcesOfCompactSelection
    (alignment :
      EndpointCompactSelectionArtificialAlignment S.autoSelectedBaseSources) :
    NaturalCompactSupportEndpointUnifiedSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  (S.toSelectedCompactSources alignment).toUnifiedSources

@[simp]
theorem toUnifiedSourcesOfCompactSelection_base
    (alignment :
      EndpointCompactSelectionArtificialAlignment S.autoSelectedBaseSources) :
    (S.toUnifiedSourcesOfCompactSelection alignment).base =
      S.toUnifiedBaseSources := by
  rfl

@[simp]
theorem toUnifiedSourcesOfCompactSelection_artificial
    (alignment :
      EndpointCompactSelectionArtificialAlignment S.autoSelectedBaseSources) :
    (S.toUnifiedSourcesOfCompactSelection alignment).artificial =
      S.artificialOfCompactSelection alignment := by
  rfl

/--
Endpoint theorem directly from selected reconstruction data and compact
selected chart-box artificial alignment.
-/
theorem stokes_ofCompactSelection
    (alignment :
      EndpointCompactSelectionArtificialAlignment S.autoSelectedBaseSources) :
    S.measureLocalization.bulkMeasureIntegral =
      S.measureLocalization.boundaryMeasureIntegral :=
  (S.toSelectedCompactSources alignment).stokes

end NaturalCompactSupportEndpointSelectedReconstructionBaseSources

namespace NaturalCompactSupportEndpointSelectedCompactSources

variable
    (S :
      NaturalCompactSupportEndpointSelectedCompactSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu)

/-- Stable projection for the generated bulk a.e. input. -/
def bulkExtDerivAE :
    BulkIntegrandAEProjectLocalAutoInput
      (BoundaryChart := M)
      ExtInteriorPiece ExtBoundaryPiece S.base.selectedPartition
      S.base.boundaryUnified.toM8TargetImageInput.targetImages S.base.localized :=
  S.base.extDerivAE

@[simp]
theorem bulkExtDerivAE_reconstruction :
    S.bulkExtDerivAE.reconstruction = S.base.reconstruction := by
  rfl

@[simp]
theorem toUnifiedSources_base_extDerivAE :
    S.toUnifiedSources.base.extDerivAE = S.bulkExtDerivAE := by
  rfl

/-- Stable projection to the previous auto-selected endpoint source record. -/
def toAutoSelectedSources :
    NaturalCompactSupportEndpointAutoSelectedSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  S.toUnifiedSources.toAutoSelectedSources

@[simp]
theorem toAutoSelectedSources_artificial :
    S.toAutoSelectedSources.artificial = S.artificial := by
  rfl

/-- Direct endpoint theorem, stated through the stable bulk/artificial projections. -/
theorem stokes_fromGeneratedFields :
    S.measureLocalization.bulkMeasureIntegral =
      S.measureLocalization.boundaryMeasureIntegral :=
  S.stokes

end NaturalCompactSupportEndpointSelectedCompactSources

end NaturalCompactSupportEndpointSelectedAuto

end Stokes

end
