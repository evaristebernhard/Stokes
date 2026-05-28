import Stokes.Global.NaturalCompactSupportEndpointAdapters
import Stokes.Global.BoundaryPartitionTermAlignmentAuto
import Stokes.Global.BoundarySourceAlignmentUnified

/-!
# Unified compact-support endpoint sources

This module removes two real boundary-side inputs from the current endpoint
source record.

Callers no longer provide:

* `ProjectLocalBoundaryGlobalMeasureFacts`;
* the six source-alignment equalities.

The global boundary-measure facts are reconstructed from canonical face
continuity plus selected chart-change/COV alignment, while source alignment is
definitional from `BoundarySourceAlignmentUnifiedData`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportEndpointUnified

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

/--
Endpoint base sources with unified boundary source data.

Compared with `NaturalCompactSupportEndpointAutoSelectedBaseSources`, this
record removes `boundaryGlobalMeasure`, `boundaryProjectLocal`,
`targetImageInput`, and `boundarySourceAlignment` as independent fields.  The
target-image input and project-local boundary data are projected from the same
unified boundary family; the global boundary-measure facts are proved from
face continuity and selected chart-change alignment.
-/
structure NaturalCompactSupportEndpointUnifiedBaseSources
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
  /-- Project-local-auto exterior-derivative a.e. input. -/
  extDerivAE :
    BulkIntegrandAEProjectLocalAutoInput
      (BoundaryChart := M)
      ExtInteriorPiece ExtBoundaryPiece
      (selection.selectedBoxPartitionOfUnity smoothness)
      boundaryUnified.toM8TargetImageInput.targetImages localized
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

namespace NaturalCompactSupportEndpointUnifiedBaseSources

variable [IsManifold I 1 M]
variable
    (S :
      NaturalCompactSupportEndpointUnifiedBaseSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)

/-- The selected partition determined by the compact-support source fields. -/
abbrev selectedPartition : SelectedBoxPartitionOfUnity I omega :=
  S.selection.selectedBoxPartitionOfUnity S.smoothness

/-- Target-image input projected from the unified boundary source data. -/
abbrev targetImageInput :
    M8TargetImageInput I omega S.selectedPartition
      S.orientedBoundaryAtlas BoundaryPiece :=
  S.boundaryUnified.toM8TargetImageInput

/-- Project-local boundary data projected from the unified boundary source data. -/
abbrev boundaryProjectLocal :
    ProjectLocalGlobalStokesData I omega M BoundaryPiece :=
  S.boundaryUnified.toProjectLocalGlobalStokesData

/-- Boundary global-measure facts reconstructed from chart-change alignment. -/
def boundaryGlobalMeasure :
    ProjectLocalBoundaryGlobalMeasureFacts S.boundaryProjectLocal :=
  S.boundaryFaceContinuity.toGlobalMeasureFactsOfSelected
    S.boundaryChartChange

/-- Source alignment is definitional from the unified boundary source data. -/
def boundarySourceAlignment :
    BoundarySourceTargetImageAlignmentFields
      S.targetImageInput S.boundaryProjectLocal :=
  S.boundaryUnified.toBoundarySourceTargetImageAlignmentFields

/-- Canonical separated boundary route, with measure facts and source alignment generated. -/
def boundaryRoute :
    BoundaryCanonicalRouteMeasureInput
      S.targetImageInput S.boundaryProjectLocal :=
  S.boundaryFaceContinuity.toBoundaryCanonicalRouteMeasureInputOfSelected
    S.boundaryUnified.toBoundarySourceProjectLocalAlignment
    S.boundaryChartChange

@[simp]
theorem boundaryRoute_projectLocal :
    S.boundaryRoute.projectLocal =
      S.boundaryGlobalMeasure.toProjectLocalBoundaryMeasureConstructorInput
        S.boundaryFaceContinuity
        S.boundaryChartChange.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral_selected := by
  rfl

@[simp]
theorem boundaryRoute_sourceAlignment :
    S.boundaryRoute.sourceAlignment =
      S.boundaryUnified.toBoundarySourceProjectLocalAlignment := by
  rfl

/-- Forget the unified boundary source route to the previous audited base-source record. -/
def toAutoSelectedBaseSources :
    NaturalCompactSupportEndpointAutoSelectedBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu where
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
  boundaryGlobalMeasure := S.boundaryGlobalMeasure
  boundaryFaceContinuity := S.boundaryFaceContinuity
  boundarySourceAlignment := S.boundarySourceAlignment
  boundaryChartChange := S.boundaryChartChange

@[simp]
theorem toAutoSelectedBaseSources_targetImageInput :
    S.toAutoSelectedBaseSources.targetImageInput = S.targetImageInput := by
  rfl

@[simp]
theorem toAutoSelectedBaseSources_boundaryGlobalMeasure :
    S.toAutoSelectedBaseSources.boundaryGlobalMeasure =
      S.boundaryGlobalMeasure := by
  rfl

@[simp]
theorem toAutoSelectedBaseSources_boundarySourceAlignment :
    S.toAutoSelectedBaseSources.boundarySourceAlignment =
      S.boundarySourceAlignment := by
  rfl

@[simp]
theorem toAutoSelectedBaseSources_boundaryRoute :
    S.toAutoSelectedBaseSources.boundaryRoute = S.boundaryRoute := by
  rfl

/-- Base endpoint input generated from unified boundary sources. -/
def toAutoBaseInput :
    NaturalCompactSupportBulkBoundarySeparatedAutoInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  S.toAutoSelectedBaseSources.toAutoBaseInput

/-- Non-auto base endpoint input generated from unified boundary sources. -/
def toBaseInput :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  S.toAutoSelectedBaseSources.toBaseInput

end NaturalCompactSupportEndpointUnifiedBaseSources

/--
Full endpoint sources with unified boundary data.

This record still keeps artificial-face cancellation explicit; that is the next
real endpoint field to discharge from adjacency/strict-support data.
-/
structure NaturalCompactSupportEndpointUnifiedSources
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
    NaturalCompactSupportEndpointUnifiedBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu
  /-- Artificial-face cancellation for the assembled M8 measure data. -/
  artificial :
    M8ArtificialFaceFields I omega BoundaryPiece
      base.toBaseInput.selectedPartition
      base.toBaseInput.targetImageInput.targetImages
      base.toBaseInput.separatedMeasure.toM8MeasureLocalizationData

namespace NaturalCompactSupportEndpointUnifiedSources

variable [IsManifold I 1 M]
variable
    (S :
      NaturalCompactSupportEndpointUnifiedSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)

/-- Forget the unified route to the previous audited endpoint source record. -/
def toAutoSelectedSources :
    NaturalCompactSupportEndpointAutoSelectedSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu where
  base := S.base.toAutoSelectedBaseSources
  artificial := S.artificial

/-- Assemble unified sources into the auto endpoint input. -/
def toAutoStokesInput :
    NaturalCompactSupportBulkBoundarySeparatedAutoStokesInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  S.toAutoSelectedSources.toAutoStokesInput

/-- Assemble unified sources into the non-auto separated endpoint input. -/
def toSeparatedInput :
    NaturalCompactSupportBulkBoundarySeparatedInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  S.toAutoSelectedSources.toSeparatedInput

/-- Endpoint theorem routed through unified boundary sources. -/
theorem stokes :
    S.base.toBaseInput.separatedMeasure.toM8MeasureLocalizationData.bulkMeasureIntegral =
      S.base.toBaseInput.separatedMeasure.toM8MeasureLocalizationData.boundaryMeasureIntegral :=
  S.toAutoStokesInput.stokes

end NaturalCompactSupportEndpointUnifiedSources

end NaturalCompactSupportEndpointUnified

end Stokes

end
