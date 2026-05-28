import Stokes.Global.MeasureLocalBoxTermAuto
import Stokes.Global.BulkExtDerivProjectLocalAuto
import Stokes.Global.NaturalCompactSupportSeparatedMeasures
import Stokes.Global.BoundaryCanonicalSeparatedGlue
import Stokes.Global.ProjectLocalBoundaryMeasureAuto
import Stokes.Global.BoundarySourceAlignmentAuto

/-!
# Combined compact-support endpoint with separated boundary measure

This module joins the latest reduced inputs:

* the bulk side uses canonical project-local box measure terms, so
  `MeasureLocalBoxTermAPI` is definitionally available;
* the boundary side uses the canonical lower-face route over `Fin n -> Real`;
* the two measure spaces are combined only at the M8 real-valued localization
  layer.

No analytic assertion is hidden here.  The remaining hard fields are still
visible: the exterior-derivative a.e. package, canonical bulk local facts,
canonical boundary route data, and artificial-face cancellation.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportCombinedEndpoint

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
Base data for the combined compact-support endpoint.

Compared with `NaturalCompactSupportBulkProjectLocalAutoCollapsedInput`, the
boundary measure route is now allowed to live on the lower-dimensional boundary
space `Fin n -> Real`.  Compared with `NaturalCompactSupportSeparatedMeasures`,
the bulk measure package is generated from the canonical project-local measure
terms rather than supplied by hand.
-/
structure NaturalCompactSupportBulkBoundarySeparatedBaseInput
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (μ : Measure (Fin (n + 1) -> Real))
    [IsFiniteMeasureOnCompacts μ]
    [IsManifold I 1 M] where
  /-- Compactly supported smooth input form. -/
  formData : CompactlySupportedSmoothFormData I omega
  /-- Compact-support finite active chart selection over `formData.supportSet`. -/
  selection :
    CompactSupportFiniteActiveSelection
      (I := I) ρ formData.supportSet formData.isCompact_supportSet omega
  /-- Smoothness data upgrading selected compact boxes to extended boxes. -/
  smoothness :
    ActiveCompactBoxSmoothness selection.finiteActive
      selection.supportData.box omega
  /-- Project-local oriented boundary chart atlas data. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Boundary target-image input over the selected partition. -/
  targetImageInput :
    M8TargetImageInput I omega
      (selection.selectedBoxPartitionOfUnity smoothness)
      orientedBoundaryAtlas BoundaryPiece
  /-- Localized interior package used by the canonical bulk route. -/
  localized :
    LocalizedInteriorM8Fields I omega
      (selection.selectedBoxPartitionOfUnity smoothness)
  /-- Exterior-derivative a.e. reconstruction for the canonical measure terms. -/
  extDerivAE :
    BulkIntegrandAEFromPartitionData
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages localized
      (BulkMeasureLocalizationTermFields.ofProjectLocalBoxTerms
        localized.localizedInterior targetImageInput.targetImages)
  /-- Local non-integral facts for canonical selected bulk pieces. -/
  bulkLocalFacts :
    SelectedPartitionBulkCanonicalLocalFacts
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages localized
  /-- The selected bulk measure is the ambient volume measure. -/
  measure_eq_volume : μ = volume
  /-- Project-local boundary package used by the canonical boundary route. -/
  boundaryProjectLocal :
    ProjectLocalGlobalStokesData I omega M BoundaryPiece
  /-- Boundary measure route over the lower-dimensional boundary coordinates. -/
  boundaryRoute :
    BoundaryCanonicalRouteMeasureInput targetImageInput boundaryProjectLocal

/--
Variant of the combined base input where the bulk exterior-derivative a.e.
package uses the canonical project-local measure terms implicitly.
-/
structure NaturalCompactSupportBulkBoundarySeparatedAutoInput
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (μ : Measure (Fin (n + 1) -> Real))
    [IsFiniteMeasureOnCompacts μ]
    [IsManifold I 1 M] where
  /-- Compactly supported smooth input form. -/
  formData : CompactlySupportedSmoothFormData I omega
  /-- Compact-support finite active chart selection over `formData.supportSet`. -/
  selection :
    CompactSupportFiniteActiveSelection
      (I := I) ρ formData.supportSet formData.isCompact_supportSet omega
  /-- Smoothness data upgrading selected compact boxes to extended boxes. -/
  smoothness :
    ActiveCompactBoxSmoothness selection.finiteActive
      selection.supportData.box omega
  /-- Project-local oriented boundary chart atlas data. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Boundary target-image input over the selected partition. -/
  targetImageInput :
    M8TargetImageInput I omega
      (selection.selectedBoxPartitionOfUnity smoothness)
      orientedBoundaryAtlas BoundaryPiece
  /-- Localized interior package used by the canonical bulk route. -/
  localized :
    LocalizedInteriorM8Fields I omega
      (selection.selectedBoxPartitionOfUnity smoothness)
  /-- Exterior-derivative a.e. input with canonical project-local measure terms. -/
  extDerivAE :
    BulkIntegrandAEProjectLocalAutoInput
      (BoundaryChart := M)
      ExtInteriorPiece ExtBoundaryPiece
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages localized
  /-- Local non-integral facts for canonical selected bulk pieces. -/
  bulkLocalFacts :
    SelectedPartitionBulkCanonicalLocalFacts
      (selection.selectedBoxPartitionOfUnity smoothness)
      targetImageInput.targetImages localized
  /-- The selected bulk measure is the ambient volume measure. -/
  measure_eq_volume : μ = volume
  /-- Project-local boundary package used by the canonical boundary route. -/
  boundaryProjectLocal :
    ProjectLocalGlobalStokesData I omega M BoundaryPiece
  /-- Boundary measure route over the lower-dimensional boundary coordinates. -/
  boundaryRoute :
    BoundaryCanonicalRouteMeasureInput targetImageInput boundaryProjectLocal

namespace NaturalCompactSupportBulkBoundarySeparatedAutoInput

variable [IsManifold I 1 M]
variable
    (D :
      NaturalCompactSupportBulkBoundarySeparatedAutoInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece ρ μ)

/-- The selected partition determined by the canonical support selection. -/
abbrev selectedPartition : SelectedBoxPartitionOfUnity I omega :=
  D.selection.selectedBoxPartitionOfUnity D.smoothness

/-- Forget the auto a.e. input to the base combined endpoint input. -/
def toBaseInput :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ where
  formData := D.formData
  selection := D.selection
  smoothness := D.smoothness
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  targetImageInput := D.targetImageInput
  localized := D.localized
  extDerivAE := D.extDerivAE.toBulkIntegrandAEFromPartitionData
  bulkLocalFacts := D.bulkLocalFacts
  measure_eq_volume := D.measure_eq_volume
  boundaryProjectLocal := D.boundaryProjectLocal
  boundaryRoute := D.boundaryRoute

@[simp]
theorem toBaseInput_extDerivAE :
    D.toBaseInput.extDerivAE =
      D.extDerivAE.toBulkIntegrandAEFromPartitionData :=
  rfl

@[simp]
theorem toBaseInput_boundaryRoute :
    D.toBaseInput.boundaryRoute = D.boundaryRoute :=
  rfl

end NaturalCompactSupportBulkBoundarySeparatedAutoInput

namespace NaturalCompactSupportBulkBoundarySeparatedBaseInput

variable [IsManifold I 1 M]
variable
    (D :
      NaturalCompactSupportBulkBoundarySeparatedBaseInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece ρ μ)

/-- The selected partition determined by the canonical support selection. -/
abbrev selectedPartition : SelectedBoxPartitionOfUnity I omega :=
  D.selection.selectedBoxPartitionOfUnity D.smoothness

/-- Canonical measure-local terms induced by project-local box terms. -/
def measureTerms :
    BulkMeasureLocalizationTermFields
      D.localized.localizedInterior D.targetImageInput.targetImages :=
  BulkMeasureLocalizationTermFields.ofProjectLocalBoxTerms
    D.localized.localizedInterior D.targetImageInput.targetImages

/-- The canonical project-local box terms provide the box-term API. -/
def measureBox : MeasureLocalBoxTermAPI D.measureTerms :=
  BulkMeasureLocalizationTermFields.projectLocalBoxTermAPI
    D.localized.localizedInterior D.targetImageInput.targetImages

@[simp]
theorem measureTerms_globalBulkIntegral :
    D.measureTerms.globalBulkIntegral =
      projectLocalBoxMeasureSum
        D.localized.localizedInterior D.targetImageInput.targetImages :=
  rfl

/--
The selected bulk ext-derivative input, with integral identities produced from
volume measure and the canonical project-local measure terms.
-/
def bulkExtDerivInput :
    SelectedPartitionBulkMeasureExtDerivInput
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      D.selectedPartition D.targetImageInput.targetImages μ :=
  selectedPartitionBulkExtDerivInputOfVolumeMeasureLocalBoxTermAPI
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    D.selectedPartition D.targetImageInput.targetImages D.localized
    D.bulkLocalFacts D.measureTerms D.extDerivAE
    D.measure_eq_volume D.measureBox

@[simp]
theorem bulkExtDerivInput_localized :
    D.bulkExtDerivInput.localized = D.localized :=
  rfl

@[simp]
theorem bulkExtDerivInput_measureTerms :
    D.bulkExtDerivInput.measureTerms = D.measureTerms :=
  rfl

/-- Bulk measure data over the ambient chart space. -/
def bulkMeasure :
    BulkMeasureFromPartitionData
      (α := Fin (n + 1) -> Real) (μ := μ)
      D.selectedPartition D.targetImageInput.targetImages
      D.measureTerms.globalBulkIntegral :=
  D.bulkExtDerivInput.toBulkMeasureFromPartitionData

/-- Boundary COV-backed measure input over lower-dimensional boundary charts. -/
def boundaryCOVInput :
    BoundaryMeasureFromTargetCOVInput
      (α := Fin n -> Real) D.targetImageInput
      (volume : Measure (Fin n -> Real)) :=
  D.boundaryRoute.toBoundaryMeasureFromTargetCOVInput

@[simp]
theorem boundaryCOVInput_boundaryMeasureIntegral :
    D.boundaryCOVInput.boundaryMeasureIntegral =
      D.boundaryRoute.projectLocal.boundaryMeasureIntegral :=
  rfl

/--
Separated measure localization: bulk over `Fin (n + 1) -> Real`, boundary over
`Fin n -> Real`.
-/
def separatedMeasure :
    SeparatedCompactSupportToM8MeasureData
      (AlphaBulk := Fin (n + 1) -> Real)
      (AlphaBoundary := Fin n -> Real)
      I omega D.selectedPartition D.targetImageInput.targetImages
      μ (volume : Measure (Fin n -> Real)) :=
  D.boundaryRoute.toSeparatedBoundaryMeasureData
    (AlphaBulk := Fin (n + 1) -> Real)
    (muBulk := μ)
    D.bulkMeasure

@[simp]
theorem separatedMeasure_globalBulkIntegral :
    D.separatedMeasure.globalBulkIntegral =
      D.measureTerms.globalBulkIntegral :=
  rfl

@[simp]
theorem separatedMeasure_boundaryMeasureIntegral :
    D.separatedMeasure.boundary.compactFields.boundaryMeasureIntegral =
      D.boundaryRoute.projectLocal.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem separatedMeasure_boundaryPartitionTerm :
    D.separatedMeasure.toM8MeasureLocalizationData.boundaryPartitionTerm =
      D.targetImageInput.assembly.boundaryPartitionTerm :=
  rfl

@[simp]
theorem separatedMeasure_bulkMeasureIntegral :
    D.separatedMeasure.toM8MeasureLocalizationData.bulkMeasureIntegral =
      D.measureTerms.globalBulkIntegral :=
  rfl

@[simp]
theorem separatedMeasure_m8_boundaryMeasureIntegral :
    D.separatedMeasure.toM8MeasureLocalizationData.boundaryMeasureIntegral =
      D.boundaryRoute.projectLocal.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem separatedMeasure_globalBoundaryIntegral :
    D.separatedMeasure.toM8MeasureLocalizationData.globalBoundaryIntegral =
      D.boundaryProjectLocal.globalBoundaryIntegral :=
  rfl

/-- The base input already proves the M8 bulk finite-sum reconstruction. -/
theorem separatedMeasure_bulkMeasureIntegral_eq_localBulkSum :
    D.separatedMeasure.toM8MeasureLocalizationData.bulkMeasureIntegral =
      (Finset.sum D.selectedPartition.active fun x =>
        Finset.sum ({()} : Finset Unit) fun _q =>
          D.localized.localizedInterior.bulkTerm x) +
        Finset.sum D.selectedPartition.active fun x =>
          Finset.sum (D.targetImageInput.targetImages.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm
              D.targetImageInput.targetImages x q := by
  simpa [bulkMeasure, separatedMeasure] using
    D.separatedMeasure.toM8MeasureLocalizationData_bulkMeasureIntegral_eq_localBulkSum

/-- The base input already proves the M8 boundary finite-sum reconstruction. -/
theorem separatedMeasure_boundaryMeasureIntegral_eq_partitionSum :
    D.separatedMeasure.toM8MeasureLocalizationData.boundaryMeasureIntegral =
      selectedBoundaryPieceSum D.selectedPartition.active
        D.targetImageInput.targetImages.boundaryPieces
        D.targetImageInput.assembly.boundaryPartitionTerm := by
  simpa [separatedMeasure] using
    D.separatedMeasure.toM8MeasureLocalizationData_boundaryMeasureIntegral_eq_partitionSum

end NaturalCompactSupportBulkBoundarySeparatedBaseInput

namespace NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

variable [IsManifold I 1 M]
variable
    (B :
      NaturalCompactSupportBulkProjectLocalAutoCollapsedInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece ρ μ)

/--
Reuse the existing bulk project-local-auto input as the bulk half of the new
separated boundary endpoint.

The old input contains an ambient boundary COV package for the same-measure
route; the new endpoint ignores that field and instead consumes the
lower-dimensional canonical `boundaryRoute`.
-/
def toBulkBoundarySeparatedBaseInput
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (boundaryRoute :
      BoundaryCanonicalRouteMeasureInput B.targetImageInput boundaryProjectLocal) :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ where
  formData := B.formData
  selection := B.selection
  smoothness := B.smoothness
  orientedBoundaryAtlas := B.orientedBoundaryAtlas
  targetImageInput := B.targetImageInput
  localized := B.localized
  extDerivAE := B.extDerivAE
  bulkLocalFacts := B.bulkLocalFacts
  measure_eq_volume := B.measure_eq_volume
  boundaryProjectLocal := boundaryProjectLocal
  boundaryRoute := boundaryRoute

@[simp]
theorem toBulkBoundarySeparatedBaseInput_targetImageInput
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (boundaryRoute :
      BoundaryCanonicalRouteMeasureInput B.targetImageInput boundaryProjectLocal) :
    (B.toBulkBoundarySeparatedBaseInput
      boundaryProjectLocal boundaryRoute).targetImageInput =
      B.targetImageInput :=
  rfl

@[simp]
theorem toBulkBoundarySeparatedBaseInput_boundaryRoute
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (boundaryRoute :
      BoundaryCanonicalRouteMeasureInput B.targetImageInput boundaryProjectLocal) :
    (B.toBulkBoundarySeparatedBaseInput
      boundaryProjectLocal boundaryRoute).boundaryRoute =
      boundaryRoute :=
  rfl

/--
Upgrade a bulk project-local-auto input to the combined base input from
global boundary measure facts and a selected-target chart-change family.
-/
def toBulkBoundarySeparatedBaseInputOfSelected
    [IsManifold I 1 M]
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts boundaryProjectLocal)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData boundaryProjectLocal)
    (sourceAlignment :
      BoundarySourceProjectLocalAlignment B.targetImageInput boundaryProjectLocal)
    (chartChange :
      BoundaryChartChangeSelectedFamilyData boundaryProjectLocal) :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ :=
  B.toBulkBoundarySeparatedBaseInput boundaryProjectLocal
    (globalMeasure.toBoundaryCanonicalRouteMeasureInputOfSelected
      faceContinuity sourceAlignment chartChange)

@[simp]
theorem toBulkBoundarySeparatedBaseInputOfSelected_boundaryRoute
    [IsManifold I 1 M]
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts boundaryProjectLocal)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData boundaryProjectLocal)
    (sourceAlignment :
      BoundarySourceProjectLocalAlignment B.targetImageInput boundaryProjectLocal)
    (chartChange :
      BoundaryChartChangeSelectedFamilyData boundaryProjectLocal) :
    (B.toBulkBoundarySeparatedBaseInputOfSelected
      boundaryProjectLocal globalMeasure faceContinuity sourceAlignment
      chartChange).boundaryRoute =
      globalMeasure.toBoundaryCanonicalRouteMeasureInputOfSelected
        faceContinuity sourceAlignment chartChange :=
  rfl

/-- Extended-target chart-change variant of the combined base constructor. -/
def toBulkBoundarySeparatedBaseInputOfExtended
    [IsManifold I 1 M]
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts boundaryProjectLocal)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData boundaryProjectLocal)
    (sourceAlignment :
      BoundarySourceProjectLocalAlignment B.targetImageInput boundaryProjectLocal)
    (chartChange :
      BoundaryChartChangeExtendedFamilyData boundaryProjectLocal) :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ :=
  B.toBulkBoundarySeparatedBaseInput boundaryProjectLocal
    (globalMeasure.toBoundaryCanonicalRouteMeasureInputOfExtended
      faceContinuity sourceAlignment chartChange)

/-- COV-family variant of the combined base constructor. -/
def toBulkBoundarySeparatedBaseInputOfCOV
    [IsManifold I 1 M]
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts boundaryProjectLocal)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData boundaryProjectLocal)
    (sourceAlignment :
      BoundarySourceProjectLocalAlignment B.targetImageInput boundaryProjectLocal)
    (covFamily :
      BoundaryChartChangeOfVariablesFamily I omega M BoundaryPiece)
    (compatibility :
      BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility
        covFamily boundaryProjectLocal) :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ :=
  B.toBulkBoundarySeparatedBaseInput boundaryProjectLocal
    (globalMeasure.toBoundaryCanonicalRouteMeasureInputOfCOV
      faceContinuity sourceAlignment covFamily compatibility)

/--
Selected-target variant using source-alignment fields stated directly against
`B.targetImageInput.targetImages`.
-/
def toBulkBoundarySeparatedBaseInputOfSelectedFields
    [IsManifold I 1 M]
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts boundaryProjectLocal)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData boundaryProjectLocal)
    (sourceAlignment :
      BoundarySourceTargetImageAlignmentFields
        B.targetImageInput boundaryProjectLocal)
    (chartChange :
      BoundaryChartChangeSelectedFamilyData boundaryProjectLocal) :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ :=
  B.toBulkBoundarySeparatedBaseInputOfSelected
    boundaryProjectLocal globalMeasure faceContinuity
    sourceAlignment.toBoundarySourceProjectLocalAlignment chartChange

/-- Extended-target variant using target-image-facing source-alignment fields. -/
def toBulkBoundarySeparatedBaseInputOfExtendedFields
    [IsManifold I 1 M]
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts boundaryProjectLocal)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData boundaryProjectLocal)
    (sourceAlignment :
      BoundarySourceTargetImageAlignmentFields
        B.targetImageInput boundaryProjectLocal)
    (chartChange :
      BoundaryChartChangeExtendedFamilyData boundaryProjectLocal) :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ :=
  B.toBulkBoundarySeparatedBaseInputOfExtended
    boundaryProjectLocal globalMeasure faceContinuity
    sourceAlignment.toBoundarySourceProjectLocalAlignment chartChange

/-- COV-family variant using target-image-facing source-alignment fields. -/
def toBulkBoundarySeparatedBaseInputOfCOVFields
    [IsManifold I 1 M]
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts boundaryProjectLocal)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData boundaryProjectLocal)
    (sourceAlignment :
      BoundarySourceTargetImageAlignmentFields
        B.targetImageInput boundaryProjectLocal)
    (covFamily :
      BoundaryChartChangeOfVariablesFamily I omega M BoundaryPiece)
    (compatibility :
      BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility
        covFamily boundaryProjectLocal) :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ :=
  B.toBulkBoundarySeparatedBaseInputOfCOV
    boundaryProjectLocal globalMeasure faceContinuity
    sourceAlignment.toBoundarySourceProjectLocalAlignment covFamily compatibility

/-- Support-finite selected-target variant of the combined base constructor. -/
def toBulkBoundarySeparatedBaseInputOfSupportFiniteSelected
    [IsManifold I 1 M]
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (supportFinite :
      ProjectLocalBoundarySupportFiniteMeasureFacts boundaryProjectLocal)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData boundaryProjectLocal)
    (sourceAlignment :
      BoundarySourceProjectLocalAlignment B.targetImageInput boundaryProjectLocal)
    (chartChange :
      BoundaryChartChangeSelectedFamilyData boundaryProjectLocal) :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ :=
  B.toBulkBoundarySeparatedBaseInput boundaryProjectLocal
    (supportFinite.toBoundaryCanonicalRouteMeasureInputOfSelected
      faceContinuity sourceAlignment chartChange)

end NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

/--
Combined compact-support Stokes input.

The base data constructs the separated measure localization automatically; the
only remaining endpoint-specific field is artificial-face cancellation for the
resulting M8 localization data.
-/
structure NaturalCompactSupportBulkBoundarySeparatedInput
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (μ : Measure (Fin (n + 1) -> Real))
    [IsFiniteMeasureOnCompacts μ]
    [IsManifold I 1 M] where
  /-- All bulk and boundary measure-route data. -/
  base :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ
  /-- Resolved artificial-face cancellation for the produced M8 measure data. -/
  artificial :
    M8ArtificialFaceFields I omega BoundaryPiece base.selectedPartition
      base.targetImageInput.targetImages
      base.separatedMeasure.toM8MeasureLocalizationData

/-- Auto-a.e. variant of the combined compact-support endpoint input. -/
structure NaturalCompactSupportBulkBoundarySeparatedAutoStokesInput
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (μ : Measure (Fin (n + 1) -> Real))
    [IsFiniteMeasureOnCompacts μ]
    [IsManifold I 1 M] where
  /-- Bulk and boundary route data with project-local-auto ext-derivative input. -/
  base :
    NaturalCompactSupportBulkBoundarySeparatedAutoInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ
  /-- Resolved artificial-face cancellation for the produced M8 measure data. -/
  artificial :
    M8ArtificialFaceFields I omega BoundaryPiece base.toBaseInput.selectedPartition
      base.toBaseInput.targetImageInput.targetImages
      base.toBaseInput.separatedMeasure.toM8MeasureLocalizationData

namespace NaturalCompactSupportBulkBoundarySeparatedInput

variable [IsManifold I 1 M]
variable
    (D :
      NaturalCompactSupportBulkBoundarySeparatedInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece ρ μ)

/-- Forget the combined wrapper to the separated-measures endpoint input. -/
def toSeparatedMeasuresInput :
    NaturalCompactSupportSeparatedMeasuresInput
      (AlphaBulk := Fin (n + 1) -> Real)
      (AlphaBoundary := Fin n -> Real)
      I omega BoundaryPiece μ (volume : Measure (Fin n -> Real)) where
  formData := D.base.formData
  orientedBoundaryAtlas := D.base.orientedBoundaryAtlas
  selectedPartition := D.base.selectedPartition
  selectedPartition_supportSet := rfl
  targetImageInput := D.base.targetImageInput
  measure := D.base.separatedMeasure
  target_boundaryPartitionTerm := rfl
  artificial := D.artificial

@[simp]
theorem toSeparatedMeasuresInput_measure :
    D.toSeparatedMeasuresInput.measure =
      D.base.separatedMeasure :=
  rfl

/--
Combined endpoint theorem.  This is the current shortest route that uses
project-local automatic bulk terms and lower-dimensional boundary measure data.
-/
theorem stokes :
    D.base.separatedMeasure.toM8MeasureLocalizationData.bulkMeasureIntegral =
      D.base.separatedMeasure.toM8MeasureLocalizationData.boundaryMeasureIntegral := by
  simpa [toSeparatedMeasuresInput] using
    D.toSeparatedMeasuresInput.stokes

/-- Same endpoint in the separated adapter's compact-support field names. -/
theorem stokes_compactSupportFields :
    D.base.separatedMeasure.globalBulkIntegral =
      D.base.separatedMeasure.boundary.compactFields.boundaryMeasureIntegral := by
  simpa [toSeparatedMeasuresInput] using
    D.toSeparatedMeasuresInput.stokes_compactSupportFields

end NaturalCompactSupportBulkBoundarySeparatedInput

namespace NaturalCompactSupportBulkBoundarySeparatedAutoStokesInput

variable [IsManifold I 1 M]
variable
    (D :
      NaturalCompactSupportBulkBoundarySeparatedAutoStokesInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece ρ μ)

/-- Forget the auto-a.e. endpoint to the base combined endpoint. -/
def toSeparatedInput :
    NaturalCompactSupportBulkBoundarySeparatedInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ where
  base := D.base.toBaseInput
  artificial := D.artificial

@[simp]
theorem toSeparatedInput_base :
    D.toSeparatedInput.base = D.base.toBaseInput :=
  rfl

/-- Stokes through the combined endpoint with project-local-auto bulk a.e. input. -/
theorem stokes :
    D.base.toBaseInput.separatedMeasure.toM8MeasureLocalizationData.bulkMeasureIntegral =
      D.base.toBaseInput.separatedMeasure.toM8MeasureLocalizationData.boundaryMeasureIntegral :=
  D.toSeparatedInput.stokes

end NaturalCompactSupportBulkBoundarySeparatedAutoStokesInput

namespace NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

variable [IsManifold I 1 M]
variable
    (B :
      NaturalCompactSupportBulkProjectLocalAutoCollapsedInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece ρ μ)

/-- Upgrade a bulk project-local-auto input to the combined separated endpoint. -/
def toBulkBoundarySeparatedInput
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (boundaryRoute :
      BoundaryCanonicalRouteMeasureInput B.targetImageInput boundaryProjectLocal)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece
        (B.toBulkBoundarySeparatedBaseInput
          boundaryProjectLocal boundaryRoute).selectedPartition
        (B.toBulkBoundarySeparatedBaseInput
          boundaryProjectLocal boundaryRoute).targetImageInput.targetImages
        ((B.toBulkBoundarySeparatedBaseInput
          boundaryProjectLocal boundaryRoute).separatedMeasure
            |>.toM8MeasureLocalizationData)) :
    NaturalCompactSupportBulkBoundarySeparatedInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ where
  base := B.toBulkBoundarySeparatedBaseInput
    boundaryProjectLocal boundaryRoute
  artificial := artificial

@[simp]
theorem toBulkBoundarySeparatedInput_base
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (boundaryRoute :
      BoundaryCanonicalRouteMeasureInput B.targetImageInput boundaryProjectLocal)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece
        (B.toBulkBoundarySeparatedBaseInput
          boundaryProjectLocal boundaryRoute).selectedPartition
        (B.toBulkBoundarySeparatedBaseInput
          boundaryProjectLocal boundaryRoute).targetImageInput.targetImages
        ((B.toBulkBoundarySeparatedBaseInput
          boundaryProjectLocal boundaryRoute).separatedMeasure
            |>.toM8MeasureLocalizationData)) :
    (B.toBulkBoundarySeparatedInput
      boundaryProjectLocal boundaryRoute artificial).base =
      B.toBulkBoundarySeparatedBaseInput boundaryProjectLocal boundaryRoute :=
  rfl

/--
Stokes through the combined endpoint, starting from the older bulk
project-local-auto input and a lower-dimensional canonical boundary route.
-/
theorem stokes_bulkBoundarySeparated
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (boundaryRoute :
      BoundaryCanonicalRouteMeasureInput B.targetImageInput boundaryProjectLocal)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece
        (B.toBulkBoundarySeparatedBaseInput
          boundaryProjectLocal boundaryRoute).selectedPartition
        (B.toBulkBoundarySeparatedBaseInput
          boundaryProjectLocal boundaryRoute).targetImageInput.targetImages
        ((B.toBulkBoundarySeparatedBaseInput
          boundaryProjectLocal boundaryRoute).separatedMeasure
            |>.toM8MeasureLocalizationData)) :
    ((B.toBulkBoundarySeparatedBaseInput
        boundaryProjectLocal boundaryRoute).separatedMeasure
        |>.toM8MeasureLocalizationData).bulkMeasureIntegral =
      ((B.toBulkBoundarySeparatedBaseInput
        boundaryProjectLocal boundaryRoute).separatedMeasure
        |>.toM8MeasureLocalizationData).boundaryMeasureIntegral :=
  (B.toBulkBoundarySeparatedInput
    boundaryProjectLocal boundaryRoute artificial).stokes

end NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

/--
Top-level combined compact-support wrapper from project-local bulk terms and
canonical lower-face boundary data.
-/
theorem naturalCompactSupportStokes_of_bulkBoundarySeparated
    [IsManifold I 1 M]
    (D :
      NaturalCompactSupportBulkBoundarySeparatedInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece ρ μ) :
    D.base.separatedMeasure.toM8MeasureLocalizationData.bulkMeasureIntegral =
      D.base.separatedMeasure.toM8MeasureLocalizationData.boundaryMeasureIntegral :=
  D.stokes

/-- Top-level combined wrapper in compact-support field names. -/
theorem naturalCompactSupportStokes_bulkBoundarySeparatedCompactSupportFields
    [IsManifold I 1 M]
    (D :
      NaturalCompactSupportBulkBoundarySeparatedInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece ρ μ) :
    D.base.separatedMeasure.globalBulkIntegral =
      D.base.separatedMeasure.boundary.compactFields.boundaryMeasureIntegral :=
  D.stokes_compactSupportFields

end NaturalCompactSupportCombinedEndpoint

end Stokes

end
