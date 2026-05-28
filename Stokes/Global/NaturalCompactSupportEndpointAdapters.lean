import Stokes.Global.NaturalCompactSupportCombinedEndpoint

/-!
# Compact-support endpoint adapters

This module is an audit/adapter layer for the current compact-support endpoint.
It deliberately does not import through `Stokes.Global` and does not change the
endpoint bus.

The remaining inputs are grouped by construction source:

* Worker A: compact-support form data, finite active selection, selected boxes,
  oriented boundary atlas, target-image input, and localized interior pieces.
* Worker B: canonical bulk exterior-derivative a.e. input, selected bulk local
  facts, and the volume-measure identification.
* Worker C: project-local boundary measure data, canonical face continuity,
  selected-target source alignment, and selected-target chart-change data.
* Worker D: artificial-face cancellation for the M8 localization produced by
  the previous sources.

All declarations below are small adapters or `rfl` projection checks.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportEndpointAdapters

universe u w b ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {ρ : SmoothPartitionOfUnity M I M univ}
variable {μ : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts μ]

/--
Endpoint base sources for the selected-target boundary route and the
project-local-auto bulk a.e. route.

The field order mirrors the source audit in the module docstring.  The record
stops before artificial-face cancellation, because that field depends on the
M8 measure localization assembled from these sources.
-/
structure NaturalCompactSupportEndpointAutoSelectedBaseSources
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (μ : Measure (Fin (n + 1) -> Real))
    [IsFiniteMeasureOnCompacts μ]
    [IsManifold I 1 M] where
  /-- Worker A: compactly supported smooth input form. -/
  formData : CompactlySupportedSmoothFormData I omega
  /-- Worker A: finite active chart selection over the support. -/
  selection :
    CompactSupportFiniteActiveSelection
      (I := I) ρ formData.supportSet formData.isCompact_supportSet omega
  /-- Worker A: smooth selected compact boxes. -/
  smoothness :
    ActiveCompactBoxSmoothness selection.finiteActive
      selection.supportData.box omega
  /-- Worker A: oriented boundary-chart atlas. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Worker A: selected target-image package. -/
  targetImageInput :
    M8TargetImageInput I omega
      (selection.selectedBoxPartitionOfUnity smoothness)
      orientedBoundaryAtlas BoundaryPiece
  /-- Worker A: localized interior pieces for the selected partition. -/
  localized :
    LocalizedInteriorM8Fields I omega
      (selection.selectedBoxPartitionOfUnity smoothness)
  /-- Worker B: project-local-auto exterior-derivative a.e. input. -/
  extDerivAE :
    BulkIntegrandAEProjectLocalAutoInput
      (BoundaryChart := M)
      ExtInteriorPiece ExtBoundaryPiece
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages localized
  /-- Worker B: local canonical bulk facts. -/
  bulkLocalFacts :
    SelectedPartitionBulkCanonicalLocalFacts
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages localized
  /-- Worker B: selected bulk measure is volume. -/
  measure_eq_volume : μ = volume
  /-- Worker C: project-local boundary package. -/
  boundaryProjectLocal :
    ProjectLocalGlobalStokesData I omega M BoundaryPiece
  /-- Worker C: remaining global boundary measure facts. -/
  boundaryGlobalMeasure :
    ProjectLocalBoundaryGlobalMeasureFacts boundaryProjectLocal
  /-- Worker C: canonical lower-face continuity data. -/
  boundaryFaceContinuity :
    ProjectLocalBoundaryCanonicalFaceContinuityData boundaryProjectLocal
  /-- Worker C: selected target-image/source alignment. -/
  boundarySourceAlignment :
    BoundarySourceTargetImageAlignmentFields
      targetImageInput boundaryProjectLocal
  /-- Worker C: selected-target chart-change data. -/
  boundaryChartChange :
    BoundaryChartChangeSelectedFamilyData boundaryProjectLocal

namespace NaturalCompactSupportEndpointAutoSelectedBaseSources

variable [IsManifold I 1 M]
variable
    (S :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece ρ μ)

/-- The selected partition determined by the compact-support source fields. -/
abbrev selectedPartition : SelectedBoxPartitionOfUnity I omega :=
  S.selection.selectedBoxPartitionOfUnity S.smoothness

/-- Worker C sources assembled into the canonical separated boundary route. -/
def boundaryRoute :
    BoundaryCanonicalRouteMeasureInput
      S.targetImageInput S.boundaryProjectLocal :=
  S.boundaryGlobalMeasure.toBoundaryCanonicalRouteMeasureInputOfSelected
    S.boundaryFaceContinuity
    S.boundarySourceAlignment.toBoundarySourceProjectLocalAlignment
    S.boundaryChartChange

@[simp]
theorem boundaryRoute_faceContinuity :
    S.boundaryRoute.faceContinuity = S.boundaryFaceContinuity := by
  rfl

@[simp]
theorem boundaryRoute_sourceAlignment :
    S.boundaryRoute.sourceAlignment =
      S.boundarySourceAlignment.toBoundarySourceProjectLocalAlignment := by
  rfl

/-- Base endpoint input with project-local-auto bulk a.e. data. -/
def toAutoBaseInput :
    NaturalCompactSupportBulkBoundarySeparatedAutoInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ where
  formData := S.formData
  selection := S.selection
  smoothness := S.smoothness
  orientedBoundaryAtlas := S.orientedBoundaryAtlas
  targetImageInput := S.targetImageInput
  localized := S.localized
  extDerivAE := S.extDerivAE
  bulkLocalFacts := S.bulkLocalFacts
  measure_eq_volume := S.measure_eq_volume
  boundaryProjectLocal := S.boundaryProjectLocal
  boundaryRoute := S.boundaryRoute

@[simp]
theorem toAutoBaseInput_formData :
    S.toAutoBaseInput.formData = S.formData := by
  rfl

@[simp]
theorem toAutoBaseInput_targetImageInput :
    S.toAutoBaseInput.targetImageInput = S.targetImageInput := by
  rfl

@[simp]
theorem toAutoBaseInput_localized :
    S.toAutoBaseInput.localized = S.localized := by
  rfl

@[simp]
theorem toAutoBaseInput_extDerivAE :
    S.toAutoBaseInput.extDerivAE = S.extDerivAE := by
  rfl

@[simp]
theorem toAutoBaseInput_boundaryProjectLocal :
    S.toAutoBaseInput.boundaryProjectLocal = S.boundaryProjectLocal := by
  rfl

@[simp]
theorem toAutoBaseInput_boundaryRoute :
    S.toAutoBaseInput.boundaryRoute = S.boundaryRoute := by
  rfl

/-- The non-auto base endpoint input obtained by forgetting the auto a.e. wrapper. -/
def toBaseInput :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ :=
  S.toAutoBaseInput.toBaseInput

@[simp]
theorem toBaseInput_extDerivAE :
    S.toBaseInput.extDerivAE =
      S.extDerivAE.toBulkIntegrandAEFromPartitionData := by
  rfl

@[simp]
theorem toBaseInput_boundaryRoute :
    S.toBaseInput.boundaryRoute = S.boundaryRoute := by
  rfl

@[simp]
theorem toBaseInput_separatedMeasure_boundaryMeasureIntegral :
    S.toBaseInput.separatedMeasure.toM8MeasureLocalizationData.boundaryMeasureIntegral =
      S.boundaryRoute.projectLocal.boundaryMeasureIntegral := by
  rfl

@[simp]
theorem toBaseInput_separatedMeasure_globalBulkIntegral :
    S.toBaseInput.separatedMeasure.toM8MeasureLocalizationData.globalBulkIntegral =
      S.toBaseInput.measureTerms.globalBulkIntegral := by
  rfl

end NaturalCompactSupportEndpointAutoSelectedBaseSources

/--
Full endpoint source audit, adding Worker D's artificial-face cancellation to
the grouped base sources.
-/
structure NaturalCompactSupportEndpointAutoSelectedSources
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (μ : Measure (Fin (n + 1) -> Real))
    [IsFiniteMeasureOnCompacts μ]
    [IsManifold I 1 M] where
  /-- Workers A/B/C: all endpoint inputs before artificial-face cancellation. -/
  base :
    NaturalCompactSupportEndpointAutoSelectedBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ
  /-- Worker D: artificial-face cancellation for the assembled M8 measure data. -/
  artificial :
    M8ArtificialFaceFields I omega BoundaryPiece
      base.toBaseInput.selectedPartition
      base.toBaseInput.targetImageInput.targetImages
      base.toBaseInput.separatedMeasure.toM8MeasureLocalizationData

namespace NaturalCompactSupportEndpointAutoSelectedSources

variable [IsManifold I 1 M]
variable
    (S :
      NaturalCompactSupportEndpointAutoSelectedSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece ρ μ)

/-- Assemble the audited sources into the auto endpoint input. -/
def toAutoStokesInput :
    NaturalCompactSupportBulkBoundarySeparatedAutoStokesInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ where
  base := S.base.toAutoBaseInput
  artificial := S.artificial

@[simp]
theorem toAutoStokesInput_base :
    S.toAutoStokesInput.base = S.base.toAutoBaseInput := by
  rfl

@[simp]
theorem toAutoStokesInput_artificial :
    S.toAutoStokesInput.artificial = S.artificial := by
  rfl

/-- Assemble the audited sources into the non-auto separated endpoint input. -/
def toSeparatedInput :
    NaturalCompactSupportBulkBoundarySeparatedInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ :=
  S.toAutoStokesInput.toSeparatedInput

@[simp]
theorem toSeparatedInput_base :
    S.toSeparatedInput.base = S.base.toBaseInput := by
  rfl

@[simp]
theorem toSeparatedInput_artificial :
    S.toSeparatedInput.artificial = S.artificial := by
  rfl

/-- Endpoint theorem routed through the audited grouped sources. -/
theorem stokes :
    S.base.toBaseInput.separatedMeasure.toM8MeasureLocalizationData.bulkMeasureIntegral =
      S.base.toBaseInput.separatedMeasure.toM8MeasureLocalizationData.boundaryMeasureIntegral :=
  S.toAutoStokesInput.stokes

end NaturalCompactSupportEndpointAutoSelectedSources

end NaturalCompactSupportEndpointAdapters

end Stokes

end
