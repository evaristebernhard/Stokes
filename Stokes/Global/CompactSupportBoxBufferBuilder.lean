import Stokes.Global.ArtificialFaceBufferSupport
import Stokes.Global.NaturalCompactSupportBuilder

/-!
# Compact-support box-buffer builders

This file is the minimal placeholder-free bridge into
`CompactSupportBoxBuffer`.

The existing selected-box and localized-support APIs currently give support in
the selected closed box `Set.Icc a b`.  The artificial-face support-zero route
needs the stronger statement that the localized chart representative is
supported in the strict interior `boxInteriorSupportBox a b`.  This module does
not manufacture that missing geometric margin.  Instead it provides transparent
constructors once such a strict-interior statement, or the corresponding strict
coefficient-support statement for a localized piece, has been proved upstream.

The remaining real lemma for the chart-box selection layer is:

* choose buffered boxes so that each active localized chart representative has
  topological support contained in `boxInteriorSupportBox lower upper`, and
  align those boxes with the `LocalizedInteriorPieces` stored in the M8 measure
  localization package.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportBoxBufferBuilder

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]

namespace ManifoldForm

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {x0 x1 : M} {ρ : M → Real}
variable {a b : Fin (n + 1) → Real}

/--
Strict support control for the chart coefficient implies strict support control
for the localized transition-pullback representative.
-/
theorem transitionPullbackInChart_localizedForm_tsupport_subset_interiorBox_of_coefficient
    (hρ :
      tsupport (transitionCoefficientInChart I x0 x1 ρ) ⊆
        boxInteriorSupportBox a b) :
    tsupport
        (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
      boxInteriorSupportBox a b :=
  (transitionPullbackInChart_localizedForm_tsupport_subset_coefficient
    (I := I) x0 x1 ρ ω).trans hρ

end ManifoldForm

namespace LocalizedInteriorPiece

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {ρ : M → M → Real} {i : M}

/--
A localized interior piece has strict interior support if its transition-chart
coefficient has strict interior support.
-/
theorem transitionPullback_tsupport_subset_interiorBox_of_coefficient
    (D : LocalizedInteriorPiece I ω ρ i)
    (hρ :
      tsupport
          (ManifoldForm.transitionCoefficientInChart I D.sourceChart
            D.targetChart (ρ i)) ⊆
        boxInteriorSupportBox D.lowerCorner D.upperCorner) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I D.sourceChart D.targetChart
          D.localizedForm) ⊆
      boxInteriorSupportBox D.lowerCorner D.upperCorner := by
  simpa [LocalizedInteriorPiece.localizedForm] using
    ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_interiorBox_of_coefficient
      (I := I) (ω := ω) (x0 := D.sourceChart) (x1 := D.targetChart)
      (ρ := ρ i) (a := D.lowerCorner) (b := D.upperCorner) hρ

end LocalizedInteriorPiece

namespace CompactSupportBoxBuffer

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/--
Constructor from the exact strict-interior support field consumed by
`CompactSupportBoxBuffer`.
-/
def ofStrictSupportSubsetInteriorBox
    (strictSupport_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (measureLocalization.localizedInterior.piece x).sourceChart
              (measureLocalization.localizedInterior.piece x).targetChart
              (measureLocalization.localizedInterior.piece x).localizedForm) ⊆
          boxInteriorSupportBox
            (measureLocalization.localizedInterior.piece x).lowerCorner
            (measureLocalization.localizedInterior.piece x).upperCorner) :
    CompactSupportBoxBuffer I omega selectedPartition targetImages
      measureLocalization where
  strictSupport_subset_interiorBox := strictSupport_subset_interiorBox

@[simp]
theorem ofStrictSupportSubsetInteriorBox_support
    (strictSupport_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (measureLocalization.localizedInterior.piece x).sourceChart
              (measureLocalization.localizedInterior.piece x).targetChart
              (measureLocalization.localizedInterior.piece x).localizedForm) ⊆
          boxInteriorSupportBox
            (measureLocalization.localizedInterior.piece x).lowerCorner
            (measureLocalization.localizedInterior.piece x).upperCorner) :
    (ofStrictSupportSubsetInteriorBox
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      (measureLocalization := measureLocalization)
      strictSupport_subset_interiorBox).strictSupport_subset_interiorBox =
        strictSupport_subset_interiorBox :=
  rfl

/--
Transparent wrapper from the older selected support-zero geometry record to the
new compact-support buffer record.
-/
def ofSelectedPartitionSupportZeroGeometry
    (D :
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureLocalization) :
    CompactSupportBoxBuffer I omega selectedPartition targetImages
      measureLocalization :=
  ofStrictSupportSubsetInteriorBox D.support_subset_interiorBox

@[simp]
theorem ofSelectedPartitionSupportZeroGeometry_support
    (D :
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureLocalization) :
    (ofSelectedPartitionSupportZeroGeometry
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      (measureLocalization := measureLocalization)
      D).strictSupport_subset_interiorBox =
      D.support_subset_interiorBox :=
  rfl

/--
Build the compact-support buffer from strict support of the transition-chart
coefficients of the localized interior pieces.

This is often the most useful localized-support bridge: the existing
`LocalizedSupport` API already proves that a localized transition-pullback is
supported wherever its transition coefficient is supported.
-/
def ofLocalizedInteriorCoefficientBuffer
    (coefficient_tsupport_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (measureLocalization.localizedInterior.piece x).sourceChart
              (measureLocalization.localizedInterior.piece x).targetChart
              (measureLocalization.localizedInterior.coefficient x)) ⊆
          boxInteriorSupportBox
            (measureLocalization.localizedInterior.piece x).lowerCorner
            (measureLocalization.localizedInterior.piece x).upperCorner) :
    CompactSupportBoxBuffer I omega selectedPartition targetImages
      measureLocalization :=
  ofStrictSupportSubsetInteriorBox
    (fun x hx =>
      LocalizedInteriorPiece.transitionPullback_tsupport_subset_interiorBox_of_coefficient
        (measureLocalization.localizedInterior.piece x)
        (coefficient_tsupport_subset_interiorBox x hx))

end CompactSupportBoxBuffer

namespace SelectedPartitionSupportZeroGeometry

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/-- Forget selected support-zero geometry as the compact-support buffer record. -/
def toCompactSupportBoxBuffer
    (D :
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureLocalization) :
    CompactSupportBoxBuffer I omega selectedPartition targetImages
      measureLocalization :=
  CompactSupportBoxBuffer.ofSelectedPartitionSupportZeroGeometry D

@[simp]
theorem toCompactSupportBoxBuffer_support
    (D :
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureLocalization) :
    D.toCompactSupportBoxBuffer.strictSupport_subset_interiorBox =
      D.support_subset_interiorBox :=
  rfl

end SelectedPartitionSupportZeroGeometry

namespace M8ArtificialFaceFields

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/-- M8 artificial-face fields directly from the strict compact-support buffer input. -/
def ofStrictCompactSupportBoxBuffer
    (strictSupport_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (measureLocalization.localizedInterior.piece x).sourceChart
              (measureLocalization.localizedInterior.piece x).targetChart
              (measureLocalization.localizedInterior.piece x).localizedForm) ⊆
          boxInteriorSupportBox
            (measureLocalization.localizedInterior.piece x).lowerCorner
            (measureLocalization.localizedInterior.piece x).upperCorner) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  (CompactSupportBoxBuffer.ofStrictSupportSubsetInteriorBox
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureLocalization := measureLocalization)
    strictSupport_subset_interiorBox).toM8ArtificialFaceFields

/-- M8 artificial-face fields from strict coefficient support of localized pieces. -/
def ofLocalizedInteriorCoefficientBuffer
    (coefficient_tsupport_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (measureLocalization.localizedInterior.piece x).sourceChart
              (measureLocalization.localizedInterior.piece x).targetChart
              (measureLocalization.localizedInterior.coefficient x)) ⊆
          boxInteriorSupportBox
            (measureLocalization.localizedInterior.piece x).lowerCorner
            (measureLocalization.localizedInterior.piece x).upperCorner) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  (CompactSupportBoxBuffer.ofLocalizedInteriorCoefficientBuffer
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureLocalization := measureLocalization)
    coefficient_tsupport_subset_interiorBox).toM8ArtificialFaceFields

@[simp]
theorem ofStrictCompactSupportBoxBuffer_active
    (strictSupport_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (measureLocalization.localizedInterior.piece x).sourceChart
              (measureLocalization.localizedInterior.piece x).targetChart
              (measureLocalization.localizedInterior.piece x).localizedForm) ⊆
          boxInteriorSupportBox
            (measureLocalization.localizedInterior.piece x).lowerCorner
            (measureLocalization.localizedInterior.piece x).upperCorner) :
    (ofStrictCompactSupportBoxBuffer (BoundaryPiece := BoundaryPiece)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      (measureLocalization := measureLocalization)
      strictSupport_subset_interiorBox).artificialFaces.activeCharts =
        selectedPartition.active :=
  CompactSupportBoxBuffer.toM8ArtificialFaceFields_active
    (CompactSupportBoxBuffer.ofStrictSupportSubsetInteriorBox
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      (measureLocalization := measureLocalization)
      strictSupport_subset_interiorBox)

end M8ArtificialFaceFields

namespace M8CompactSupportArtificialFaceResolvedData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureResolved :
  M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages}

/--
Compact-support artificial-face resolved data directly from strict support of
the localized interior pieces.
-/
def ofStrictCompactSupportBoxBuffer
    (strictSupport_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (measureResolved.measureLocalization.localizedInterior.piece x).sourceChart
              (measureResolved.measureLocalization.localizedInterior.piece x).targetChart
              (measureResolved.measureLocalization.localizedInterior.piece x).localizedForm) ⊆
          boxInteriorSupportBox
            (measureResolved.measureLocalization.localizedInterior.piece x).lowerCorner
            (measureResolved.measureLocalization.localizedInterior.piece x).upperCorner) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  (CompactSupportBoxBuffer.ofStrictSupportSubsetInteriorBox
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureLocalization := measureResolved.measureLocalization)
    strictSupport_subset_interiorBox).toCompactSupportArtificialFaceResolvedData

/--
Compact-support artificial-face resolved data from strict coefficient support
of the localized interior pieces.
-/
def ofLocalizedInteriorCoefficientBuffer
    (coefficient_tsupport_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (measureResolved.measureLocalization.localizedInterior.piece x).sourceChart
              (measureResolved.measureLocalization.localizedInterior.piece x).targetChart
              (measureResolved.measureLocalization.localizedInterior.coefficient x)) ⊆
          boxInteriorSupportBox
            (measureResolved.measureLocalization.localizedInterior.piece x).lowerCorner
            (measureResolved.measureLocalization.localizedInterior.piece x).upperCorner) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  (CompactSupportBoxBuffer.ofLocalizedInteriorCoefficientBuffer
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureLocalization := measureResolved.measureLocalization)
    coefficient_tsupport_subset_interiorBox).toCompactSupportArtificialFaceResolvedData

end M8CompactSupportArtificialFaceResolvedData

namespace NaturalCompactSupportBuilderData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}

/--
Natural compact-support builder constructor where the artificial-face field is
generated from a compact-support box buffer.
-/
def ofPackagesWithCompactSupportBoxBuffer
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (localizedInterior :
      LocalizedInteriorM8Fields I omega selectedPartition)
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega selectedPartition
        targetImageInput.targetImages μ)
    (measure_localizedInterior :
      measure.toM8MeasureLocalizationData.localizedInterior =
        localizedInterior.localizedInterior)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measure.boundaryPartitionTerm)
    (buffer :
      CompactSupportBoxBuffer I omega selectedPartition
        targetImageInput.targetImages measure.toM8MeasureLocalizationData) :
    NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ :=
  ofPackages (α := α) (μ := μ) (I := I) (omega := omega)
    (BoundaryPiece := BoundaryPiece)
    formData orientedBoundaryAtlas selectedPartition
    selectedPartition_supportSet targetImageInput localizedInterior measure
    measure_localizedInterior target_boundaryPartitionTerm
    buffer.toM8ArtificialFaceFields

@[simp]
theorem ofPackagesWithCompactSupportBoxBuffer_artificial
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImageInput :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (localizedInterior :
      LocalizedInteriorM8Fields I omega selectedPartition)
    (measure :
      CompactSupportToM8MeasureData
        (α := α) I omega selectedPartition
        targetImageInput.targetImages μ)
    (measure_localizedInterior :
      measure.toM8MeasureLocalizationData.localizedInterior =
        localizedInterior.localizedInterior)
    (target_boundaryPartitionTerm :
      targetImageInput.assembly.boundaryPartitionTerm =
        measure.boundaryPartitionTerm)
    (buffer :
      CompactSupportBoxBuffer I omega selectedPartition
        targetImageInput.targetImages measure.toM8MeasureLocalizationData) :
    (ofPackagesWithCompactSupportBoxBuffer
      (α := α) (μ := μ) (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece)
      formData orientedBoundaryAtlas selectedPartition
      selectedPartition_supportSet targetImageInput localizedInterior measure
      measure_localizedInterior target_boundaryPartitionTerm buffer).artificial =
        buffer.toM8ArtificialFaceFields :=
  rfl

end NaturalCompactSupportBuilderData

end CompactSupportBoxBufferBuilder

end Stokes

end
