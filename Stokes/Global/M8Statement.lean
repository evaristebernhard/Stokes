import Stokes.Global.NaturalMeasureConstructor
import Stokes.Global.BoundaryPieceFamilyConstructor
import Stokes.Global.ArtificialFaceFieldReduction

/-!
# M8-facing global Stokes statement

This file gives a statement closer to the intended final global theorem than
`GlobalStokesPrototype`.  The input keeps only a small number of explicit
unfinished packages:

* measure localization for the bulk and boundary integrals;
* resolved artificial-face cancellation for localized interior pieces;
* target-image boundary data and its comparison with boundary partition terms.

The proof is still bookkeeping: the M8 input is projected to
`NaturalGlobalStokesInput`, then to the measure-level
`NaturalMeasureStokesInput`.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section M8Statement

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

/--
Fieldized measure-localization data for the M8 statement.

The selected partition supplies the active chart labels.  The interior side has
one singleton localized piece per active chart, and the boundary side is read
from the selected target-image family.
-/
structure M8MeasureLocalizationData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece) where
  /-- Localized partition-of-unity interior pieces. -/
  localizedInterior : LocalizedInteriorPieces (ι := M) I omega
  /-- The localized active set is the selected partition active set. -/
  localized_active :
    localizedInterior.active = selectedPartition.active
  /-- The localized coefficients are the selected partition coefficients. -/
  localized_coefficient :
    localizedInterior.coefficient =
      fun i x => selectedPartition.partition i x
  /-- The represented global bulk integral. -/
  globalBulkIntegral : Real
  /-- The genuine bulk measure integral represented by the localization data. -/
  bulkMeasureIntegral : Real
  /-- The represented bulk integral agrees with the bulk measure integral. -/
  globalBulkIntegral_eq_bulkMeasureIntegral :
    globalBulkIntegral = bulkMeasureIntegral
  /-- The bulk measure integral is reconstructed from localized local terms. -/
  bulkMeasureIntegral_eq_localBulkSum :
    bulkMeasureIntegral =
      (Finset.sum selectedPartition.active fun x =>
        Finset.sum ({()} : Finset Unit) fun _q =>
          localizedInterior.bulkTerm x) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (targetImages.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm targetImages x q
  /-- Boundary partition term after target-image transport and chart changes. -/
  boundaryPartitionTerm : M -> BoundaryPiece -> Real
  /-- The represented global boundary integral. -/
  globalBoundaryIntegral : Real
  /-- The genuine boundary measure integral. -/
  boundaryMeasureIntegral : Real
  /-- The represented boundary integral agrees with the boundary measure integral. -/
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :
    globalBoundaryIntegral = boundaryMeasureIntegral
  /-- The boundary measure integral is reconstructed from partition terms. -/
  boundaryMeasureIntegral_eq_partitionSum :
    boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm

namespace M8MeasureLocalizationData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

/-- The singleton interior-piece family exposed to the mixed constructor. -/
def interiorPieces
    (_D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    M -> Finset Unit :=
  fun _ => ({()} : Finset Unit)

/-- Localized interior bulk terms in the selected mixed-constructor shape. -/
def interiorBulkTerm
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    M -> Unit -> Real :=
  fun x _ => D.localizedInterior.bulkTerm x

/-- Localized artificial-boundary terms in the selected mixed-constructor shape. -/
def interiorBoundaryTerm
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    M -> Unit -> Real :=
  fun x _ => D.localizedInterior.artificialBoundaryTerm x

/-- Boundary bulk terms read from the selected target-image family. -/
def boundaryBulkTerm
    (_D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    M -> BoundaryPiece -> Real :=
  BoundaryPieceFamilyInput.boundaryBulkTerm targetImages

/-- Bulk reconstruction in the shape consumed by `NaturalGlobalStokesInput`. -/
def toBulkIntegralReconstructionData
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    BulkIntegralReconstructionData I omega M Unit BoundaryPiece where
  activeCharts := selectedPartition.active
  interiorPieces := interiorPieces D
  boundaryPieces := targetImages.boundaryPieces
  interiorBulkTerm := interiorBulkTerm D
  boundaryBulkTerm := boundaryBulkTerm D
  globalBulkIntegral := D.globalBulkIntegral
  globalBulkIntegral_eq_localBulkSum := by
    simpa [interiorPieces, interiorBulkTerm, boundaryBulkTerm] using
      D.globalBulkIntegral_eq_bulkMeasureIntegral.trans
        D.bulkMeasureIntegral_eq_localBulkSum

/-- Boundary measure localization in the package used by the natural measure layer. -/
def toBoundaryMeasureLocalizationFields
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    BoundaryMeasureLocalizationFields selectedPartition.active
      targetImages.boundaryPieces D.boundaryPartitionTerm
      D.globalBoundaryIntegral where
  boundaryMeasureIntegral := D.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    D.globalBoundaryIntegral_eq_boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_partitionSum :=
    D.boundaryMeasureIntegral_eq_partitionSum

/-- Boundary reconstruction after forgetting the intermediate measure integral. -/
def toBoundaryIntegralReconstructionData
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    BoundaryIntegralReconstructionData selectedPartition.active
      targetImages.boundaryPieces D.boundaryPartitionTerm
      D.globalBoundaryIntegral :=
  D.toBoundaryMeasureLocalizationFields.toBoundaryIntegralReconstructionData

/-- Bulk measure localization in the package used by the natural measure layer. -/
def toBulkMeasureLocalizationFields
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    BulkMeasureLocalizationFields D.toBulkIntegralReconstructionData where
  bulkMeasureIntegral := D.bulkMeasureIntegral
  globalBulkIntegral_eq_bulkMeasureIntegral :=
    D.globalBulkIntegral_eq_bulkMeasureIntegral
  bulkMeasureIntegral_eq_localBulkSum := by
    simpa [toBulkIntegralReconstructionData,
      BulkIntegralReconstructionData.localBulkSum,
      BulkIntegralReconstructionData.interiorBulkSum,
      BulkIntegralReconstructionData.boundaryBulkSum,
      interiorPieces, interiorBulkTerm, boundaryBulkTerm] using
      D.bulkMeasureIntegral_eq_localBulkSum

/-- Local Stokes for all localized singleton interior pieces. -/
def toMixedInteriorPackage
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    MixedInteriorPackage I omega M Unit selectedPartition.active
      (interiorPieces D) (interiorBulkTerm D) (interiorBoundaryTerm D) where
  localStokes := by
    intro x hx q _hq
    have hx' : x ∈ D.localizedInterior.active := by
      simpa [D.localized_active] using hx
    cases q
    simpa [interiorBulkTerm, interiorBoundaryTerm] using
      D.localizedInterior.localProjectEquality x hx'

@[simp]
theorem toBulkIntegralReconstructionData_activeCharts
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    D.toBulkIntegralReconstructionData.activeCharts =
      selectedPartition.active :=
  rfl

@[simp]
theorem toBulkIntegralReconstructionData_globalBulkIntegral
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    D.toBulkIntegralReconstructionData.globalBulkIntegral =
      D.globalBulkIntegral :=
  rfl

@[simp]
theorem toBulkMeasureLocalizationFields_bulkMeasureIntegral
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    D.toBulkMeasureLocalizationFields.bulkMeasureIntegral =
      D.bulkMeasureIntegral :=
  rfl

@[simp]
theorem toBoundaryMeasureLocalizationFields_boundaryMeasureIntegral
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    D.toBoundaryMeasureLocalizationFields.boundaryMeasureIntegral =
      D.boundaryMeasureIntegral :=
  rfl

end M8MeasureLocalizationData

/--
M8-facing input package for global Stokes.

Compared with `GlobalStokesPrototypeInput`, this keeps the final-facing data
visible and leaves only measure localization, resolved artificial faces, and
target-image boundary data explicit.
-/
structure M8GlobalStokesInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b) where
  /-- Compactly supported smooth input form. -/
  formData : CompactlySupportedSmoothFormData I omega
  /-- Explicit oriented boundary-chart atlas data. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Selected partition of unity and selected interior boxes. -/
  selectedPartition : SelectedBoxPartitionOfUnity I omega
  /-- The selected partition is controlled by the compact form-support set. -/
  selectedPartition_supportSet :
    selectedPartition.K = formData.supportSet
  /-- Boundary pieces carrying selected target-image data. -/
  targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece
  /-- Target-image data uses the selected active chart set. -/
  targetImages_active :
    targetImages.activeCharts = selectedPartition.active
  /-- Fieldized natural measure-localization data. -/
  measureLocalization :
    M8MeasureLocalizationData I omega selectedPartition targetImages
  /-- Resolved artificial-face data for localized singleton interior pieces. -/
  artificialFaces : ArtificialFaceResolvedData M Unit
  /-- Artificial-face data uses the selected active chart set. -/
  artificialFaces_active :
    artificialFaces.activeCharts = selectedPartition.active
  /-- Artificial-face data uses one singleton interior piece per selected chart. -/
  artificialFaces_pieces :
    artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit)
  /-- The resolved artificial-face term is the localized artificial-boundary term. -/
  artificialFaces_term :
    artificialFaces.interiorBoundaryTerm =
      measureLocalization.interiorBoundaryTerm
  /-- Source charts of target-image pieces belong to the explicit oriented atlas. -/
  targetImages_source_mem :
    ∀ x, x ∈ targetImages.activeCharts ->
      ∀ q, q ∈ targetImages.boundaryPieces x ->
        targetImages.sourceChart x q ∈ orientedBoundaryAtlas.charts
  /-- Boundary-source charts of target-image pieces belong to the oriented atlas. -/
  targetImages_boundarySource_mem :
    ∀ x, x ∈ targetImages.activeCharts ->
      ∀ q, q ∈ targetImages.boundaryPieces x ->
        targetImages.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts
  /-- Transported target-image terms agree with the boundary partition terms. -/
  targetBoundaryTerm_eq_partition :
    ∀ x, x ∈ selectedPartition.active ->
      ∀ q, q ∈ targetImages.boundaryPieces x ->
        BoundaryPieceFamilyInput.boundaryBoundaryTerm targetImages x q =
          measureLocalization.boundaryPartitionTerm x q

namespace M8GlobalStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {BoundaryPiece : Type b}

/-- Bulk reconstruction supplied by the M8 measure-localization package. -/
abbrev bulkReconstruction
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    BulkIntegralReconstructionData I omega M Unit BoundaryPiece :=
  D.measureLocalization.toBulkIntegralReconstructionData

/-- Boundary reconstruction supplied by the M8 measure-localization package. -/
abbrev boundaryReconstruction
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    BoundaryIntegralReconstructionData D.selectedPartition.active
      D.targetImages.boundaryPieces
      D.measureLocalization.boundaryPartitionTerm
      D.measureLocalization.globalBoundaryIntegral :=
  D.measureLocalization.toBoundaryIntegralReconstructionData

/-- Localized singleton interior pieces as a mixed interior package. -/
abbrev toMixedInteriorPackage
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    MixedInteriorPackage I omega M Unit D.selectedPartition.active
      (M8MeasureLocalizationData.interiorPieces D.measureLocalization)
      (M8MeasureLocalizationData.interiorBulkTerm D.measureLocalization)
      (M8MeasureLocalizationData.interiorBoundaryTerm D.measureLocalization) :=
  D.measureLocalization.toMixedInteriorPackage

/-- Boundary target-image data as a mixed boundary local-Stokes package. -/
def toMixedBoundaryPackage
    [IsManifold I 1 M]
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    MixedBoundaryPackage I omega M BoundaryPiece
      D.targetImages.activeCharts D.targetImages.boundaryPieces
      (BoundaryPieceFamilyInput.boundaryBulkTerm D.targetImages)
      (BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages) :=
  D.targetImages.toMixedBoundaryPackage_of_orientedAtlas
    D.orientedBoundaryAtlas D.targetImages_source_mem
    D.targetImages_boundarySource_mem

/-- Resolved artificial faces as the cancellation package for localized pieces. -/
def toArtificialBoundaryCancellationData
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    ArtificialBoundaryCancellationData M Unit :=
  D.artificialFaces.toArtificialBoundaryCancellationData

/-- Target-image-to-boundary-partition comparison as chart-change data. -/
def toChartChangeCancellationData
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    ChartChangeCancellationData M BoundaryPiece Real where
  activeCharts := D.selectedPartition.active
  boundaryPieces := D.targetImages.boundaryPieces
  oldBoundaryTerm := BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages
  newBoundaryTerm := D.measureLocalization.boundaryPartitionTerm
  term_eq := D.targetBoundaryTerm_eq_partition

/-- Convert M8 input to the current natural global Stokes package. -/
def toNaturalGlobalStokesInput
    [IsManifold I 1 M]
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    NaturalGlobalStokesInput I omega Unit BoundaryPiece where
  formData := D.formData
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  selectedPartition := D.selectedPartition
  selectedPartition_supportSet := D.selectedPartition_supportSet
  bulkReconstruction := D.bulkReconstruction
  boundaryPartitionTerm := D.measureLocalization.boundaryPartitionTerm
  globalBoundaryIntegral := D.measureLocalization.globalBoundaryIntegral
  boundaryReconstruction := D.boundaryReconstruction
  selectedPartition_active := rfl
  interiorBoundaryTerm :=
    M8MeasureLocalizationData.interiorBoundaryTerm D.measureLocalization
  boundaryBoundaryTerm :=
    BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages
  interiorPackage := D.toMixedInteriorPackage
  boundaryPackage := by
    simpa [bulkReconstruction,
      M8MeasureLocalizationData.toBulkIntegralReconstructionData,
      D.targetImages_active] using D.toMixedBoundaryPackage
  artificialCancellation := D.toArtificialBoundaryCancellationData
  artificialCancellation_active := by
    simpa [toArtificialBoundaryCancellationData, bulkReconstruction,
      M8MeasureLocalizationData.toBulkIntegralReconstructionData] using
      D.artificialFaces_active
  artificialCancellation_pieces := by
    simpa [toArtificialBoundaryCancellationData, bulkReconstruction,
      M8MeasureLocalizationData.toBulkIntegralReconstructionData,
      M8MeasureLocalizationData.interiorPieces] using
      D.artificialFaces_pieces
  artificialCancellation_term := by
    simpa [toArtificialBoundaryCancellationData] using
      D.artificialFaces_term
  chartChange := D.toChartChangeCancellationData
  chartChange_active := by
    simp [toChartChangeCancellationData, bulkReconstruction,
      M8MeasureLocalizationData.toBulkIntegralReconstructionData]
  chartChange_pieces := by
    simp [toChartChangeCancellationData, bulkReconstruction,
      M8MeasureLocalizationData.toBulkIntegralReconstructionData]
  chartChange_oldTerm := rfl
  chartChange_newTerm := rfl

/-- Convert M8 input to the current natural measure-level Stokes package. -/
def toNaturalMeasureStokesInput
    [IsManifold I 1 M]
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    NaturalMeasureStokesInput I omega Unit BoundaryPiece where
  naturalInput := D.toNaturalGlobalStokesInput
  bulkLocalization := by
    simpa [toNaturalGlobalStokesInput, bulkReconstruction] using
      D.measureLocalization.toBulkMeasureLocalizationFields
  boundaryLocalization := by
    simpa [toNaturalGlobalStokesInput, bulkReconstruction,
      M8MeasureLocalizationData.toBulkIntegralReconstructionData] using
      D.measureLocalization.toBoundaryMeasureLocalizationFields

@[simp]
theorem toNaturalGlobalStokesInput_bulkReconstruction
    [IsManifold I 1 M]
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    D.toNaturalGlobalStokesInput.bulkReconstruction =
      D.bulkReconstruction :=
  rfl

@[simp]
theorem toNaturalMeasureStokesInput_bulkMeasureIntegral
    [IsManifold I 1 M]
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    D.toNaturalMeasureStokesInput.bulkLocalization.bulkMeasureIntegral =
      D.measureLocalization.bulkMeasureIntegral :=
  rfl

@[simp]
theorem toNaturalMeasureStokesInput_boundaryMeasureIntegral
    [IsManifold I 1 M]
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    D.toNaturalMeasureStokesInput.boundaryLocalization.boundaryMeasureIntegral =
      D.measureLocalization.boundaryMeasureIntegral :=
  rfl

/-- Represented-integral Stokes theorem obtained from the natural global package. -/
theorem represented_stokes
    [IsManifold I 1 M]
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    D.measureLocalization.globalBulkIntegral =
      D.measureLocalization.globalBoundaryIntegral := by
  simpa [toNaturalMeasureStokesInput, toNaturalGlobalStokesInput,
    bulkReconstruction] using D.toNaturalMeasureStokesInput.global_stokes

/-- Measure-level Stokes theorem obtained from the natural measure package. -/
theorem stokes
    [IsManifold I 1 M]
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    D.measureLocalization.bulkMeasureIntegral =
      D.measureLocalization.boundaryMeasureIntegral := by
  simpa [toNaturalMeasureStokesInput,
    M8MeasureLocalizationData.toBulkMeasureLocalizationFields,
    M8MeasureLocalizationData.toBoundaryMeasureLocalizationFields] using
      D.toNaturalMeasureStokesInput.stokes

end M8GlobalStokesInput

/--
M8-facing global Stokes theorem.

The theorem is stated at the measure-integral level; the represented-integral
variant is `m8GlobalStokes_represented`.
-/
theorem m8GlobalStokes
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
    [IsManifold I 1 M]
    {omega : ManifoldForm I M n}
    {BoundaryPiece : Type b}
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    D.measureLocalization.bulkMeasureIntegral =
      D.measureLocalization.boundaryMeasureIntegral :=
  D.stokes

/-- Represented-integral version of the M8 wrapper. -/
theorem m8GlobalStokes_represented
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
    [IsManifold I 1 M]
    {omega : ManifoldForm I M n}
    {BoundaryPiece : Type b}
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    D.measureLocalization.globalBulkIntegral =
      D.measureLocalization.globalBoundaryIntegral :=
  D.represented_stokes

end M8Statement

end Stokes

end
