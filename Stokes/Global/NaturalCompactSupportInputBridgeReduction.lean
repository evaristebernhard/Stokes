import Stokes.Global.NaturalCompactSupportInputFromPartitionCover
import Stokes.Global.SupportControlledSelectedPartition
import Stokes.Global.LocalizedInteriorConstructorAlignment

/-!
# Bridge reduction for natural compact-support partition-cover inputs

This file records the current smaller constructor boundary for
`NaturalCompactSupportPartitionCoverResolvedInput`.

The resolved input in `NaturalCompactSupportInputFromPartitionCover` still has
three explicit bridge fields.  Two of them are no longer theorem-facing here:
the selected coordinate support and the base-form support bound are projected
from `NaturalCompactSupportPartitionConstructorData.selection`, and the
localized-piece alignment is projected from the localized chart-label alignment
stored on the bulk reconstruction.

The remaining coefficient-support bridge is stated in the support-controlled
partition language.  It is intentionally not a mega-facade: the fields below
are exactly the coordinate transport and active-index assignment facts still
needed to turn a cover-indexed support-controlled partition into the selected
`M`-indexed coefficient support consumed by the artificial-face constructor.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportInputBridgeReduction

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {Alpha : Type a} [TopologicalSpace Alpha] [MeasurableSpace Alpha]
variable [OpensMeasurableSpace Alpha] [T2Space Alpha]
variable {mu : Measure Alpha} [IsFiniteMeasureOnCompacts mu]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {rho : SmoothPartitionOfUnity M I M univ}
variable [IsManifold I 1 M]

/--
Bulk and boundary reconstruction data in the shape needed to construct the
compact-support M8 measure package.

This is only a scoreboard for measure reconstruction: callers still supply the
genuine bulk and boundary analytic facts, but downstream constructors no
longer take a raw `measure` field.
-/
structure NaturalCompactSupportBulkBoundaryReconstructionInput
    (partitionData :
      NaturalCompactSupportPartitionConstructorData I omega rho)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (targetImageInput :
      M8TargetImageInput I omega partitionData.selectedPartition
        orientedBoundaryAtlas BoundaryPiece)
    (mu : Measure Alpha) [IsFiniteMeasureOnCompacts mu] where
  /-- Represented global bulk integral. -/
  globalBulkIntegral : Real
  /-- Represented global boundary integral. -/
  globalBoundaryIntegral : Real
  /-- Selected compact-support bulk reconstruction. -/
  bulk :
    BulkMeasureFromPartitionData (α := Alpha) (μ := mu)
      partitionData.selectedPartition targetImageInput.targetImages
      globalBulkIntegral
  /-- Boundary scalar integrand. -/
  boundaryIntegrand : Alpha -> Real
  /-- Boundary piece support sets. -/
  boundaryPieceSet : M -> BoundaryPiece -> Set Alpha
  /-- Boundary piece scalar integrands. -/
  boundaryPieceIntegrand : M -> BoundaryPiece -> Alpha -> Real
  /-- Genuine boundary measure integral. -/
  boundaryMeasureIntegral : Real
  /-- The represented boundary integral agrees with the measure integral. -/
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :
    globalBoundaryIntegral = boundaryMeasureIntegral
  /-- The boundary measure integral is the integral of the scalar integrand. -/
  boundaryMeasureIntegral_eq_integral :
    boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂mu
  /-- Measurability of active boundary piece sets. -/
  boundaryPieceSet_measurable :
    forall x, x ∈ partitionData.selectedPartition.active ->
      forall q, q ∈ targetImageInput.targetImages.boundaryPieces x ->
        MeasurableSet (boundaryPieceSet x q)
  /-- Compact-support integrability for active boundary piece integrands. -/
  boundaryPieceCompactSupport :
    forall x, x ∈ partitionData.selectedPartition.active ->
      forall q, q ∈ targetImageInput.targetImages.boundaryPieces x ->
        CompactSupportIntegrabilityData (boundaryPieceIntegrand x q)
  /-- Active boundary geometric terms are the corresponding set integrals. -/
  boundaryBoundaryTerm_eq_setIntegral :
    forall x, x ∈ partitionData.selectedPartition.active ->
      forall q, q ∈ targetImageInput.targetImages.boundaryPieces x ->
        BoundaryPieceFamilyInput.boundaryBoundaryTerm
            targetImageInput.targetImages x q =
          ∫ y in boundaryPieceSet x q,
            boundaryPieceIntegrand x q y ∂mu
  /-- A.e. boundary reconstruction by the selected indicator sum. -/
  boundaryIntegrand_ae_eq_indicatorSum :
    boundaryIntegrand =ᵐ[mu]
      boundaryMeasureIndicatorSum partitionData.selectedPartition.active
        targetImageInput.targetImages.boundaryPieces boundaryPieceSet
        boundaryPieceIntegrand

namespace NaturalCompactSupportBulkBoundaryReconstructionInput

variable
    {partitionData :
      NaturalCompactSupportPartitionConstructorData I omega rho}
    {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
    {targetImageInput :
      M8TargetImageInput I omega partitionData.selectedPartition
        orientedBoundaryAtlas BoundaryPiece}

/-- The compact-support M8 measure package generated by reconstruction data. -/
def measure
    (R :
      NaturalCompactSupportBulkBoundaryReconstructionInput
        (Alpha := Alpha) partitionData orientedBoundaryAtlas
        targetImageInput mu) :
    CompactSupportToM8MeasureData I omega partitionData.selectedPartition
      targetImageInput.targetImages mu :=
  naturalCompactSupportMeasureOfBoundaryBoundaryReconstruction
    (Alpha := Alpha)
    partitionData orientedBoundaryAtlas targetImageInput R.bulk
    R.boundaryIntegrand R.boundaryPieceSet R.boundaryPieceIntegrand
    R.boundaryMeasureIntegral
    R.globalBoundaryIntegral_eq_boundaryMeasureIntegral
    R.boundaryMeasureIntegral_eq_integral R.boundaryPieceSet_measurable
    R.boundaryPieceCompactSupport R.boundaryBoundaryTerm_eq_setIntegral
    R.boundaryIntegrand_ae_eq_indicatorSum

@[simp]
theorem measure_boundaryPartitionTerm
    (R :
      NaturalCompactSupportBulkBoundaryReconstructionInput
        (Alpha := Alpha) partitionData orientedBoundaryAtlas
        targetImageInput mu) :
    targetImageInput.assembly.boundaryPartitionTerm =
      R.measure.boundaryPartitionTerm := by
  simp [measure, naturalCompactSupportMeasureOfBoundaryBoundaryReconstruction,
    M8TargetImageInput.compactSupportToM8MeasureDataOfBoundaryBoundaryTerm]

end NaturalCompactSupportBulkBoundaryReconstructionInput

namespace NaturalCompactSupportPartitionConstructorData

variable
    (D : NaturalCompactSupportPartitionConstructorData I omega rho)

/--
The base support-control field required by the resolved input is already part
of the finite-active selection data.
-/
theorem base_tsupport_subset_selectedCoordSupport :
    forall x, x ∈ D.selectedPartition.active ->
      tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
        D.selection.supportData.coordSupport x := by
  intro x hx
  exact D.selection.supportData.tsupport_subset_coordSupport x (by simpa using hx)

end NaturalCompactSupportPartitionConstructorData

/--
Support-controlled cover-to-selected coefficient bridge.

The cover-side partition is indexed by the mixed finite cover.  The selected
M8 route is indexed by active chart labels `x : M`.  The fields below are the
minimal current bridge facts that identify an active selected coefficient with
one cover coefficient and transport coordinate support through the assigned
chart.
-/
structure NaturalCompactSupportSelectedCoefficientSupportBridge
    (partitionData :
      NaturalCompactSupportPartitionConstructorData I omega rho)
    (chartBoxCover :
      CompactSupportChartCoverSelection I partitionData.supportSet)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measure :
      CompactSupportToM8MeasureData I omega partitionData.selectedPartition
        targetImages mu) where
  /-- Cover-indexed support-controlled partition subordinate to `chartBoxCover`. -/
  controlledPartition : SupportControlledSelectedPartition chartBoxCover
  /-- Active selected chart labels are assigned to cover indices. -/
  activeCoverIndex :
    forall x, x ∈ partitionData.selectedPartition.active ->
      chartBoxCover.CoverIndex
  /-- The assigned cover chart is the selected chart label. -/
  activeCoverIndex_chart :
    forall x, forall hx : x ∈ partitionData.selectedPartition.active,
      chartBoxCover.assignedChart (activeCoverIndex x hx) = x
  /-- The assigned cover coefficient is the selected partition coefficient. -/
  activeCoverIndex_partition :
    forall x, forall hx : x ∈ partitionData.selectedPartition.active,
      controlledPartition.partition (activeCoverIndex x hx) =
        partitionData.selectedPartition.partition x
  /-- Selected coordinate supports map back into the compact support set. -/
  coordSupport_preimage_subset_supportSet :
    forall x, x ∈ partitionData.selectedPartition.active ->
      forall y, y ∈ partitionData.selection.supportData.coordSupport x ->
        (extChartAt I x).symm y ∈ partitionData.supportSet
  /-- Selected coordinate supports lie in the selected chart target. -/
  coordSupport_subset_chartTarget :
    forall x, x ∈ partitionData.selectedPartition.active ->
      partitionData.selection.supportData.coordSupport x ⊆
        (extChartAt I x).target
  /--
  Coordinate topological support of every cover coefficient maps back to the
  manifold-side coefficient support.
  -/
  controlled_coefficient_tsupport_preimage_subset :
    forall j, forall y,
      y ∈ tsupport
          (ManifoldForm.transitionCoefficientInChart I
            (chartBoxCover.assignedChart j) (chartBoxCover.assignedChart j)
            (controlledPartition.partition j)) ->
        (extChartAt I (chartBoxCover.assignedChart j)).symm y ∈
          tsupport (controlledPartition.partition j)
  /--
  The assigned cover coordinate box is contained in the localized M8 piece box
  used by the measure package.
  -/
  assignedCoordinateBox_subset_localizedPiece :
    forall x, forall hx : x ∈ partitionData.selectedPartition.active,
      chartBoxCover.assignedCoordinateBox (activeCoverIndex x hx) ⊆
        boxInteriorSupportBox
          (measure.toM8MeasureLocalizationData.localizedInterior.piece x).lowerCorner
          (measure.toM8MeasureLocalizationData.localizedInterior.piece x).upperCorner

namespace NaturalCompactSupportSelectedCoefficientSupportBridge

variable
    {partitionData :
      NaturalCompactSupportPartitionConstructorData I omega rho}
    {chartBoxCover :
      CompactSupportChartCoverSelection I partitionData.supportSet}
    {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measure :
      CompactSupportToM8MeasureData I omega partitionData.selectedPartition
        targetImages mu}

/--
The support-controlled cover bridge supplies the exact coefficient-support
field still consumed by `NaturalCompactSupportPartitionCoverResolvedInput`.
-/
theorem coefficient_tsupport_subset_assignedBox
    (B :
      NaturalCompactSupportSelectedCoefficientSupportBridge
        (mu := mu) partitionData chartBoxCover targetImages measure) :
    forall x, x ∈ partitionData.selectedPartition.active ->
      tsupport
          (ManifoldForm.transitionCoefficientInChart I x x
            (partitionData.selectedPartition.partition x)) ∩
          partitionData.selection.supportData.coordSupport x ⊆
        boxInteriorSupportBox
          (measure.toM8MeasureLocalizationData.localizedInterior.piece x).lowerCorner
          (measure.toM8MeasureLocalizationData.localizedInterior.piece x).upperCorner := by
  intro x hx y hy
  rcases hy with ⟨hycoeff, hycoord⟩
  let j := B.activeCoverIndex x hx
  have hchart : chartBoxCover.assignedChart j = x :=
    B.activeCoverIndex_chart x hx
  have hpartition :
      B.controlledPartition.partition j =
        partitionData.selectedPartition.partition x :=
    B.activeCoverIndex_partition x hx
  have hcoordK :
      forall y, y ∈ partitionData.selection.supportData.coordSupport x ->
        (extChartAt I (chartBoxCover.assignedChart j)).symm y ∈
          partitionData.supportSet := by
    intro y hy
    simpa [hchart] using
      B.coordSupport_preimage_subset_supportSet x hx y hy
  have hcoordTarget :
      partitionData.selection.supportData.coordSupport x ⊆
        (extChartAt I (chartBoxCover.assignedChart j)).target := by
    simpa [hchart] using B.coordSupport_subset_chartTarget x hx
  have hyAssigned : y ∈ chartBoxCover.assignedCoordinateBox j := by
    refine
      B.controlledPartition
        |>.transitionCoefficient_inter_coordSupport_subset_assignedCoordinateBox
          (j := j)
          (coordSupport := partitionData.selection.supportData.coordSupport x)
          hcoordK hcoordTarget
          (B.controlled_coefficient_tsupport_preimage_subset j) ?_
    exact ⟨by simpa [j, hchart, hpartition] using hycoeff, hycoord⟩
  exact B.assignedCoordinateBox_subset_localizedPiece x hx hyAssigned

end NaturalCompactSupportSelectedCoefficientSupportBridge

/--
Reduced scoreboard for the resolved partition-cover input.

Compared with `NaturalCompactSupportPartitionCoverResolvedInput`, this record
does not ask callers for `measure`, `localizedPieceAlignment`, `coordSupport`,
or `base_tsupport_subset_coordSupport`.  The remaining coefficient support
obligation is expressed by the support-controlled cover bridge above.
-/
structure NaturalCompactSupportPartitionCoverBridgeReductionInput
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (rho : SmoothPartitionOfUnity M I M univ)
    (mu : Measure Alpha) [IsFiniteMeasureOnCompacts mu]
    [IsManifold I 1 M] where
  /-- Compact support, selected partition, and selected chart boxes. -/
  partitionData : NaturalCompactSupportPartitionConstructorData I omega rho
  /-- Finite chart-box cover of the compact support. -/
  chartBoxCover :
    CompactSupportChartCoverSelection I partitionData.supportSet
  /-- Project-local oriented boundary atlas. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Boundary target-image package over the selected partition. -/
  targetImageInput :
    M8TargetImageInput I omega partitionData.selectedPartition
      orientedBoundaryAtlas BoundaryPiece
  /-- Bulk and boundary reconstruction data generating the measure package. -/
  reconstruction :
    NaturalCompactSupportBulkBoundaryReconstructionInput
      (Alpha := Alpha) partitionData orientedBoundaryAtlas targetImageInput mu
  /-- Localized chart-label alignment for the bulk localized pieces. -/
  localizedChartAlignment :
    LocalizedInteriorM8ChartAlignment reconstruction.bulk.localized
  /-- Support-controlled bridge for the one remaining coefficient-support field. -/
  coefficientSupportBridge :
    NaturalCompactSupportSelectedCoefficientSupportBridge
      (mu := mu) partitionData chartBoxCover targetImageInput.targetImages
      reconstruction.measure

namespace NaturalCompactSupportPartitionCoverBridgeReductionInput

variable
    (D :
      NaturalCompactSupportPartitionCoverBridgeReductionInput
        (Alpha := Alpha) I omega BoundaryPiece rho mu)

/-- The selected partition determined by the reduced bridge input. -/
abbrev selectedPartition : SelectedBoxPartitionOfUnity I omega :=
  D.partitionData.selectedPartition

/-- The compact-support form data determined by the reduced bridge input. -/
abbrev formData : CompactlySupportedSmoothFormData I omega :=
  D.partitionData.formData

/-- The generated measure package. -/
abbrev measure :
    CompactSupportToM8MeasureData I omega D.selectedPartition
      D.targetImageInput.targetImages mu :=
  D.reconstruction.measure

/-- The localized-piece alignment projected from bulk chart-label alignment. -/
def localizedPieceAlignment :
    LocalizedInteriorPieceAlignment D.selectedPartition
      D.targetImageInput.targetImages D.measure.toM8MeasureLocalizationData :=
  D.measure.toLocalizedInteriorPieceAlignment D.localizedChartAlignment

/-- The generated coordinate-support family from the finite-active selection. -/
abbrev coordSupport : M -> Set (Fin (n + 1) -> Real) :=
  D.partitionData.selection.supportData.coordSupport

/-- The base support bound generated by the finite-active selection. -/
theorem base_tsupport_subset_coordSupport :
    forall x, x ∈ D.selectedPartition.active ->
      tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
        D.coordSupport x :=
  D.partitionData.base_tsupport_subset_selectedCoordSupport

/-- The coefficient support bound generated by the support-controlled bridge. -/
theorem coefficient_tsupport_subset_assignedBox :
    forall x, x ∈ D.selectedPartition.active ->
      tsupport
          (ManifoldForm.transitionCoefficientInChart I x x
            (D.selectedPartition.partition x)) ∩ D.coordSupport x ⊆
        boxInteriorSupportBox
          (D.measure.toM8MeasureLocalizationData.localizedInterior.piece x).lowerCorner
          (D.measure.toM8MeasureLocalizationData.localizedInterior.piece x).upperCorner :=
  D.coefficientSupportBridge.coefficient_tsupport_subset_assignedBox

/--
Convert the reduced bridge scoreboard into the existing resolved input.

The `artificial` field is still generated downstream by
`NaturalCompactSupportPartitionCoverResolvedInput.artificial`.
-/
def toResolvedInput :
    NaturalCompactSupportPartitionCoverResolvedInput
      (Alpha := Alpha) I omega BoundaryPiece rho mu where
  partitionData := D.partitionData
  chartBoxCover := D.chartBoxCover
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  targetImageInput := D.targetImageInput
  measure := D.measure
  target_boundaryPartitionTerm := D.reconstruction.measure_boundaryPartitionTerm
  localizedPieceAlignment := D.localizedPieceAlignment
  coordSupport := D.coordSupport
  base_tsupport_subset_coordSupport := D.base_tsupport_subset_coordSupport
  coefficient_tsupport_subset_assignedBox :=
    D.coefficient_tsupport_subset_assignedBox

@[simp]
theorem toResolvedInput_measure :
    D.toResolvedInput.measure = D.measure := by
  rfl

@[simp]
theorem toResolvedInput_coordSupport :
    D.toResolvedInput.coordSupport = D.coordSupport := by
  rfl

@[simp]
theorem toResolvedInput_localizedPieceAlignment :
    D.toResolvedInput.localizedPieceAlignment =
      D.localizedPieceAlignment := by
  rfl

/-- Direct endpoint input generated from the reduced bridge scoreboard. -/
def toNaturalCompactSupportStokesInput :
    NaturalCompactSupportStokesInput I omega BoundaryPiece mu :=
  D.toResolvedInput.toNaturalCompactSupportStokesInput

@[simp]
theorem toNaturalCompactSupportStokesInput_measure :
    D.toNaturalCompactSupportStokesInput.measure = D.measure := by
  rfl

@[simp]
theorem toNaturalCompactSupportStokesInput_artificial :
    D.toNaturalCompactSupportStokesInput.artificial =
      D.toResolvedInput.artificial := by
  rfl

/-- Natural compact-support Stokes from the reduced bridge input. -/
theorem stokes :
    D.measure.toM8MeasureLocalizationData.bulkMeasureIntegral =
      D.measure.toM8MeasureLocalizationData.boundaryMeasureIntegral :=
  D.toResolvedInput.stokes

end NaturalCompactSupportPartitionCoverBridgeReductionInput

end NaturalCompactSupportInputBridgeReduction

end Stokes

end
