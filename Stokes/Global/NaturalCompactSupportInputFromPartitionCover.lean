import Stokes.Global.BoundaryMeasureFromPartitionIdentity
import Stokes.Global.NaturalCompactSupportPartitionConstructorAuto
import Stokes.Global.InteriorAssignedBoxSupport
import Stokes.Global.CompactSupportChartCoverSelection

/-!
# Natural compact-support input from partition-cover data

This module records the current honest constructor boundary between a finite
chart-box cover/subordinate-partition stage and
`NaturalCompactSupportStokesInput`.

The cover and selected-partition constructor data identify the compact support
being localized.  The bulk and boundary measure reconstruction packages build
the `measure` field.  The artificial-face field is not supplied as a raw zero
or cancellation facade: it is generated from the support-control hypotheses
via `M8ArtificialFaceFields.ofAssignedInteriorBoxSupport`.

The remaining real gap is still visible in the input shape: turning a finite
chart-box cover plus a support-controlled partition into the selected
localized-piece alignment and coefficient support-control fields is not yet an
automatic theorem in the current API.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportInputFromPartitionCover

set_option linter.unusedSectionVars false

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
Measure field generated from the real bulk reconstruction package and the
boundary reconstruction proved for the geometric boundary term
`BoundaryPieceFamilyInput.boundaryBoundaryTerm`.
-/
def naturalCompactSupportMeasureOfBoundaryBoundaryReconstruction
    (partitionData :
      NaturalCompactSupportPartitionConstructorData I omega rho)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (targetImageInput :
      M8TargetImageInput I omega partitionData.selectedPartition
        orientedBoundaryAtlas BoundaryPiece)
    {globalBulkIntegral globalBoundaryIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData (α := Alpha) (μ := mu)
        partitionData.selectedPartition targetImageInput.targetImages
        globalBulkIntegral)
    (boundaryIntegrand : Alpha -> Real)
    (boundaryPieceSet : M -> BoundaryPiece -> Set Alpha)
    (boundaryPieceIntegrand : M -> BoundaryPiece -> Alpha -> Real)
    (boundaryMeasureIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂mu)
    (boundaryPieceSet_measurable :
      forall x, x ∈ partitionData.selectedPartition.active ->
        forall q, q ∈ targetImageInput.targetImages.boundaryPieces x ->
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceCompactSupport :
      forall x, x ∈ partitionData.selectedPartition.active ->
        forall q, q ∈ targetImageInput.targetImages.boundaryPieces x ->
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (boundaryBoundaryTerm_eq_setIntegral :
      forall x, x ∈ partitionData.selectedPartition.active ->
        forall q, q ∈ targetImageInput.targetImages.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBoundaryTerm
              targetImageInput.targetImages x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[mu]
        boundaryMeasureIndicatorSum partitionData.selectedPartition.active
          targetImageInput.targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand) :
    CompactSupportToM8MeasureData I omega partitionData.selectedPartition
      targetImageInput.targetImages mu :=
  targetImageInput.compactSupportToM8MeasureDataOfBoundaryBoundaryTerm
    (alpha := Alpha) (mu := mu)
    bulk boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral globalBoundaryIntegral_eq_boundaryMeasureIntegral
    boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
    boundaryPieceCompactSupport boundaryBoundaryTerm_eq_setIntegral
    boundaryIntegrand_ae_eq_indicatorSum

/--
Resolved partition-cover input.

This is the closest current builder data to a fully automatic
finite-cover-to-Stokes constructor.  It keeps the genuine missing bridges
visible:

* `localizedPieceAlignment`;
* `base_tsupport_subset_coordSupport`;
* `coefficient_tsupport_subset_assignedBox`.

Those are exactly the fields that should eventually be produced from the
finite chart-box cover and support-controlled partition.
-/
structure NaturalCompactSupportPartitionCoverResolvedInput
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (rho : SmoothPartitionOfUnity M I M univ)
    (mu : Measure Alpha) [IsFiniteMeasureOnCompacts mu] where
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
  /-- Compact-support measure package generated by reconstruction data. -/
  measure :
    CompactSupportToM8MeasureData I omega partitionData.selectedPartition
      targetImageInput.targetImages mu
  /-- The generated measure uses the target-image assembly boundary term. -/
  target_boundaryPartitionTerm :
    targetImageInput.assembly.boundaryPartitionTerm =
      measure.boundaryPartitionTerm
  /-- Localized pieces are in the selected `x/x` chart coordinates. -/
  localizedPieceAlignment :
    LocalizedInteriorPieceAlignment partitionData.selectedPartition
      targetImageInput.targetImages measure.toM8MeasureLocalizationData
  /-- Coordinate carrier used by the support-controlled partition argument. -/
  coordSupport : M -> Set (Fin (n + 1) -> Real)
  /-- Base chart representatives are carried by the selected coordinate carriers. -/
  base_tsupport_subset_coordSupport :
    forall x, x ∈ partitionData.selectedPartition.active ->
      tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
        coordSupport x
  /--
  The partition coefficient is supported, on the coordinate carrier, in the
  assigned localized-piece box.  This is the precise support-control bridge
  still expected from the finite chart-box cover and subordinate partition.
  -/
  coefficient_tsupport_subset_assignedBox :
    forall x, x ∈ partitionData.selectedPartition.active ->
      tsupport
          (ManifoldForm.transitionCoefficientInChart I x x
            (partitionData.selectedPartition.partition x)) ∩ coordSupport x ⊆
        boxInteriorSupportBox
          (measure.toM8MeasureLocalizationData.localizedInterior.piece x).lowerCorner
          (measure.toM8MeasureLocalizationData.localizedInterior.piece x).upperCorner

namespace NaturalCompactSupportPartitionCoverResolvedInput

variable
    (D :
      NaturalCompactSupportPartitionCoverResolvedInput
        (Alpha := Alpha) I omega BoundaryPiece rho mu)

/-- The selected partition determined by the partition-cover input. -/
abbrev selectedPartition : SelectedBoxPartitionOfUnity I omega :=
  D.partitionData.selectedPartition

/-- The compact-support form data determined by the partition-cover input. -/
abbrev formData : CompactlySupportedSmoothFormData I omega :=
  D.partitionData.formData

/-- The finite chart-box cover really covers the compact support. -/
theorem chartBoxCover_support_subset :
    D.partitionData.supportSet ⊆
      D.chartBoxCover.interiorCoverSet ∪ D.chartBoxCover.boundaryCoverSet :=
  D.chartBoxCover.support_subset_interior_union_boundary

/-- Artificial-face fields generated from assigned-box support control. -/
def artificial :
    M8ArtificialFaceFields I omega BoundaryPiece D.selectedPartition
      D.targetImageInput.targetImages
      D.measure.toM8MeasureLocalizationData :=
  M8ArtificialFaceFields.ofAssignedInteriorBoxSupport
    (BoundaryPiece := BoundaryPiece)
    (selectedPartition := D.selectedPartition)
    (targetImages := D.targetImageInput.targetImages)
    (measureLocalization := D.measure.toM8MeasureLocalizationData)
    D.localizedPieceAlignment D.base_tsupport_subset_coordSupport
    D.coefficient_tsupport_subset_assignedBox

/-- Convert resolved partition-cover data into the natural compact-support input. -/
def toNaturalCompactSupportStokesInput :
    NaturalCompactSupportStokesInput I omega BoundaryPiece mu where
  formData := D.formData
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  selectedPartition := D.selectedPartition
  selectedPartition_supportSet := D.partitionData.selectedPartition_supportSet
  targetImageInput := D.targetImageInput
  measure := D.measure
  target_boundaryPartitionTerm := D.target_boundaryPartitionTerm
  artificial := D.artificial

@[simp]
theorem toNaturalCompactSupportStokesInput_selectedPartition :
    D.toNaturalCompactSupportStokesInput.selectedPartition =
      D.selectedPartition := by
  rfl

@[simp]
theorem toNaturalCompactSupportStokesInput_measure :
    D.toNaturalCompactSupportStokesInput.measure = D.measure := by
  rfl

@[simp]
theorem toNaturalCompactSupportStokesInput_artificial :
    D.toNaturalCompactSupportStokesInput.artificial = D.artificial := by
  rfl

/--
Natural compact-support Stokes obtained from the resolved partition-cover input.
-/
theorem stokes :
    D.measure.toM8MeasureLocalizationData.bulkMeasureIntegral =
      D.measure.toM8MeasureLocalizationData.boundaryMeasureIntegral :=
  D.toNaturalCompactSupportStokesInput.stokes

end NaturalCompactSupportPartitionCoverResolvedInput

/--
Constructor from finite chart-box cover data, selected-partition constructor
data, bulk reconstruction, boundary reconstruction, and assigned-box support
control.

The `measure` and `artificial` fields of `NaturalCompactSupportStokesInput` are
both constructed here: callers do not supply raw M8 artificial cancellation or
artificial zero fields.
-/
def naturalCompactSupportPartitionCoverResolvedInputOfBoundaryReconstruction
    (partitionData :
      NaturalCompactSupportPartitionConstructorData I omega rho)
    (chartBoxCover :
      CompactSupportChartCoverSelection I partitionData.supportSet)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (targetImageInput :
      M8TargetImageInput I omega partitionData.selectedPartition
        orientedBoundaryAtlas BoundaryPiece)
    {globalBulkIntegral globalBoundaryIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData (α := Alpha) (μ := mu)
        partitionData.selectedPartition targetImageInput.targetImages
        globalBulkIntegral)
    (boundaryIntegrand : Alpha -> Real)
    (boundaryPieceSet : M -> BoundaryPiece -> Set Alpha)
    (boundaryPieceIntegrand : M -> BoundaryPiece -> Alpha -> Real)
    (boundaryMeasureIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂mu)
    (boundaryPieceSet_measurable :
      forall x, x ∈ partitionData.selectedPartition.active ->
        forall q, q ∈ targetImageInput.targetImages.boundaryPieces x ->
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceCompactSupport :
      forall x, x ∈ partitionData.selectedPartition.active ->
        forall q, q ∈ targetImageInput.targetImages.boundaryPieces x ->
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (boundaryBoundaryTerm_eq_setIntegral :
      forall x, x ∈ partitionData.selectedPartition.active ->
        forall q, q ∈ targetImageInput.targetImages.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBoundaryTerm
              targetImageInput.targetImages x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[mu]
        boundaryMeasureIndicatorSum partitionData.selectedPartition.active
          targetImageInput.targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand)
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment partitionData.selectedPartition
        targetImageInput.targetImages
        (naturalCompactSupportMeasureOfBoundaryBoundaryReconstruction
          partitionData orientedBoundaryAtlas targetImageInput bulk
          boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
          boundaryMeasureIntegral
          globalBoundaryIntegral_eq_boundaryMeasureIntegral
          boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
          boundaryPieceCompactSupport boundaryBoundaryTerm_eq_setIntegral
          boundaryIntegrand_ae_eq_indicatorSum).toM8MeasureLocalizationData)
    (coordSupport : M -> Set (Fin (n + 1) -> Real))
    (base_tsupport_subset_coordSupport :
      forall x, x ∈ partitionData.selectedPartition.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
          coordSupport x)
    (coefficient_tsupport_subset_assignedBox :
      forall x, x ∈ partitionData.selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I x x
              (partitionData.selectedPartition.partition x)) ∩ coordSupport x ⊆
          boxInteriorSupportBox
            ((naturalCompactSupportMeasureOfBoundaryBoundaryReconstruction
                partitionData orientedBoundaryAtlas targetImageInput bulk
                boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
                boundaryMeasureIntegral
                globalBoundaryIntegral_eq_boundaryMeasureIntegral
                boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
                boundaryPieceCompactSupport boundaryBoundaryTerm_eq_setIntegral
                boundaryIntegrand_ae_eq_indicatorSum)
              |>.toM8MeasureLocalizationData
              |>.localizedInterior
              |>.piece x).lowerCorner
            ((naturalCompactSupportMeasureOfBoundaryBoundaryReconstruction
                partitionData orientedBoundaryAtlas targetImageInput bulk
                boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
                boundaryMeasureIntegral
                globalBoundaryIntegral_eq_boundaryMeasureIntegral
                boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
                boundaryPieceCompactSupport boundaryBoundaryTerm_eq_setIntegral
                boundaryIntegrand_ae_eq_indicatorSum)
              |>.toM8MeasureLocalizationData
              |>.localizedInterior
              |>.piece x).upperCorner) :
    NaturalCompactSupportPartitionCoverResolvedInput
      (Alpha := Alpha) I omega BoundaryPiece rho mu :=
  let measure :=
    naturalCompactSupportMeasureOfBoundaryBoundaryReconstruction
      partitionData orientedBoundaryAtlas targetImageInput bulk
      boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
      boundaryMeasureIntegral globalBoundaryIntegral_eq_boundaryMeasureIntegral
      boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
      boundaryPieceCompactSupport boundaryBoundaryTerm_eq_setIntegral
      boundaryIntegrand_ae_eq_indicatorSum
  { partitionData := partitionData
    chartBoxCover := chartBoxCover
    orientedBoundaryAtlas := orientedBoundaryAtlas
    targetImageInput := targetImageInput
    measure := measure
    target_boundaryPartitionTerm := by
      simp [measure, naturalCompactSupportMeasureOfBoundaryBoundaryReconstruction,
        M8TargetImageInput.compactSupportToM8MeasureDataOfBoundaryBoundaryTerm]
    localizedPieceAlignment := localizedPieceAlignment
    coordSupport := coordSupport
    base_tsupport_subset_coordSupport := base_tsupport_subset_coordSupport
    coefficient_tsupport_subset_assignedBox :=
      coefficient_tsupport_subset_assignedBox }

@[simp]
theorem naturalCompactSupportPartitionCoverResolvedInputOfBoundaryReconstruction_measure
    (partitionData :
      NaturalCompactSupportPartitionConstructorData I omega rho)
    (chartBoxCover :
      CompactSupportChartCoverSelection I partitionData.supportSet)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (targetImageInput :
      M8TargetImageInput I omega partitionData.selectedPartition
        orientedBoundaryAtlas BoundaryPiece)
    {globalBulkIntegral globalBoundaryIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData (α := Alpha) (μ := mu)
        partitionData.selectedPartition targetImageInput.targetImages
        globalBulkIntegral)
    (boundaryIntegrand : Alpha -> Real)
    (boundaryPieceSet : M -> BoundaryPiece -> Set Alpha)
    (boundaryPieceIntegrand : M -> BoundaryPiece -> Alpha -> Real)
    (boundaryMeasureIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂mu)
    (boundaryPieceSet_measurable :
      forall x, x ∈ partitionData.selectedPartition.active ->
        forall q, q ∈ targetImageInput.targetImages.boundaryPieces x ->
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceCompactSupport :
      forall x, x ∈ partitionData.selectedPartition.active ->
        forall q, q ∈ targetImageInput.targetImages.boundaryPieces x ->
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (boundaryBoundaryTerm_eq_setIntegral :
      forall x, x ∈ partitionData.selectedPartition.active ->
        forall q, q ∈ targetImageInput.targetImages.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBoundaryTerm
              targetImageInput.targetImages x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[mu]
        boundaryMeasureIndicatorSum partitionData.selectedPartition.active
          targetImageInput.targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand)
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment partitionData.selectedPartition
        targetImageInput.targetImages
        (naturalCompactSupportMeasureOfBoundaryBoundaryReconstruction
          partitionData orientedBoundaryAtlas targetImageInput bulk
          boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
          boundaryMeasureIntegral
          globalBoundaryIntegral_eq_boundaryMeasureIntegral
          boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
          boundaryPieceCompactSupport boundaryBoundaryTerm_eq_setIntegral
          boundaryIntegrand_ae_eq_indicatorSum).toM8MeasureLocalizationData)
    (coordSupport : M -> Set (Fin (n + 1) -> Real))
    (base_tsupport_subset_coordSupport :
      forall x, x ∈ partitionData.selectedPartition.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
          coordSupport x)
    (coefficient_tsupport_subset_assignedBox :
      forall x, x ∈ partitionData.selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I x x
              (partitionData.selectedPartition.partition x)) ∩ coordSupport x ⊆
          boxInteriorSupportBox
            ((naturalCompactSupportMeasureOfBoundaryBoundaryReconstruction
                partitionData orientedBoundaryAtlas targetImageInput bulk
                boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
                boundaryMeasureIntegral
                globalBoundaryIntegral_eq_boundaryMeasureIntegral
                boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
                boundaryPieceCompactSupport boundaryBoundaryTerm_eq_setIntegral
                boundaryIntegrand_ae_eq_indicatorSum)
              |>.toM8MeasureLocalizationData
              |>.localizedInterior
              |>.piece x).lowerCorner
            ((naturalCompactSupportMeasureOfBoundaryBoundaryReconstruction
                partitionData orientedBoundaryAtlas targetImageInput bulk
                boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
                boundaryMeasureIntegral
                globalBoundaryIntegral_eq_boundaryMeasureIntegral
                boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
                boundaryPieceCompactSupport boundaryBoundaryTerm_eq_setIntegral
                boundaryIntegrand_ae_eq_indicatorSum)
              |>.toM8MeasureLocalizationData
              |>.localizedInterior
              |>.piece x).upperCorner) :
    (naturalCompactSupportPartitionCoverResolvedInputOfBoundaryReconstruction
      partitionData chartBoxCover orientedBoundaryAtlas targetImageInput bulk
      boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
      boundaryMeasureIntegral globalBoundaryIntegral_eq_boundaryMeasureIntegral
      boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
      boundaryPieceCompactSupport boundaryBoundaryTerm_eq_setIntegral
      boundaryIntegrand_ae_eq_indicatorSum localizedPieceAlignment
      coordSupport base_tsupport_subset_coordSupport
      coefficient_tsupport_subset_assignedBox).measure =
        naturalCompactSupportMeasureOfBoundaryBoundaryReconstruction
          partitionData orientedBoundaryAtlas targetImageInput bulk
          boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
          boundaryMeasureIntegral
          globalBoundaryIntegral_eq_boundaryMeasureIntegral
          boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
          boundaryPieceCompactSupport boundaryBoundaryTerm_eq_setIntegral
          boundaryIntegrand_ae_eq_indicatorSum := by
  rfl

/--
Direct endpoint constructor from partition-cover and reconstruction data.
-/
def naturalCompactSupportStokesInputOfPartitionCoverBoundaryReconstruction
    (partitionData :
      NaturalCompactSupportPartitionConstructorData I omega rho)
    (chartBoxCover :
      CompactSupportChartCoverSelection I partitionData.supportSet)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (targetImageInput :
      M8TargetImageInput I omega partitionData.selectedPartition
        orientedBoundaryAtlas BoundaryPiece)
    {globalBulkIntegral globalBoundaryIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData (α := Alpha) (μ := mu)
        partitionData.selectedPartition targetImageInput.targetImages
        globalBulkIntegral)
    (boundaryIntegrand : Alpha -> Real)
    (boundaryPieceSet : M -> BoundaryPiece -> Set Alpha)
    (boundaryPieceIntegrand : M -> BoundaryPiece -> Alpha -> Real)
    (boundaryMeasureIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂mu)
    (boundaryPieceSet_measurable :
      forall x, x ∈ partitionData.selectedPartition.active ->
        forall q, q ∈ targetImageInput.targetImages.boundaryPieces x ->
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceCompactSupport :
      forall x, x ∈ partitionData.selectedPartition.active ->
        forall q, q ∈ targetImageInput.targetImages.boundaryPieces x ->
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (boundaryBoundaryTerm_eq_setIntegral :
      forall x, x ∈ partitionData.selectedPartition.active ->
        forall q, q ∈ targetImageInput.targetImages.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBoundaryTerm
              targetImageInput.targetImages x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[mu]
        boundaryMeasureIndicatorSum partitionData.selectedPartition.active
          targetImageInput.targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand)
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment partitionData.selectedPartition
        targetImageInput.targetImages
        (naturalCompactSupportMeasureOfBoundaryBoundaryReconstruction
          partitionData orientedBoundaryAtlas targetImageInput bulk
          boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
          boundaryMeasureIntegral
          globalBoundaryIntegral_eq_boundaryMeasureIntegral
          boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
          boundaryPieceCompactSupport boundaryBoundaryTerm_eq_setIntegral
          boundaryIntegrand_ae_eq_indicatorSum).toM8MeasureLocalizationData)
    (coordSupport : M -> Set (Fin (n + 1) -> Real))
    (base_tsupport_subset_coordSupport :
      forall x, x ∈ partitionData.selectedPartition.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
          coordSupport x)
    (coefficient_tsupport_subset_assignedBox :
      forall x, x ∈ partitionData.selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I x x
              (partitionData.selectedPartition.partition x)) ∩ coordSupport x ⊆
          boxInteriorSupportBox
            ((naturalCompactSupportMeasureOfBoundaryBoundaryReconstruction
                partitionData orientedBoundaryAtlas targetImageInput bulk
                boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
                boundaryMeasureIntegral
                globalBoundaryIntegral_eq_boundaryMeasureIntegral
                boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
                boundaryPieceCompactSupport boundaryBoundaryTerm_eq_setIntegral
                boundaryIntegrand_ae_eq_indicatorSum)
              |>.toM8MeasureLocalizationData
              |>.localizedInterior
              |>.piece x).lowerCorner
            ((naturalCompactSupportMeasureOfBoundaryBoundaryReconstruction
                partitionData orientedBoundaryAtlas targetImageInput bulk
                boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
                boundaryMeasureIntegral
                globalBoundaryIntegral_eq_boundaryMeasureIntegral
                boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
                boundaryPieceCompactSupport boundaryBoundaryTerm_eq_setIntegral
                boundaryIntegrand_ae_eq_indicatorSum)
              |>.toM8MeasureLocalizationData
              |>.localizedInterior
              |>.piece x).upperCorner) :
    NaturalCompactSupportStokesInput I omega BoundaryPiece mu :=
  (naturalCompactSupportPartitionCoverResolvedInputOfBoundaryReconstruction
    partitionData chartBoxCover orientedBoundaryAtlas targetImageInput bulk
    boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral globalBoundaryIntegral_eq_boundaryMeasureIntegral
    boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
    boundaryPieceCompactSupport boundaryBoundaryTerm_eq_setIntegral
    boundaryIntegrand_ae_eq_indicatorSum localizedPieceAlignment coordSupport
    base_tsupport_subset_coordSupport
    coefficient_tsupport_subset_assignedBox).toNaturalCompactSupportStokesInput

end NaturalCompactSupportInputFromPartitionCover

end Stokes

end
