import Stokes.Global.NaturalCompactSupportPartitionConstructorAuto
import Stokes.Global.CompactActiveStrictOuterBoxFromLocalizedPiecesAuto
import Stokes.Global.ArtificialFaceFromStrictBufferAuto
import Stokes.Global.CanonicalCompactSupportEndpointFacade
import Stokes.Global.NaturalCompactSupportEndpointConstructorFieldsAuto

/-!
# End-to-end compact-support endpoint constructor

This module packages the current compact-support endpoint route one layer
higher.  The selected partition, compact-active boxes, support containment, and
finite-active data are generated from
`NaturalCompactSupportPartitionConstructorData`; callers then provide the still
real endpoint inputs: boundary/measure data, constructor chart-label alignment,
and strict localized-piece margins.

No new analysis is proved here.  The declarations compose the existing
partition constructor, localized-piece strict-buffer route, artificial-face
cancellation from strict buffers, and canonical integral facade.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCompactSupportEndpointEndToEndAuto

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

namespace NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources

variable
    (S :
      NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu)

/-- The endpoint measure-resolution package induced by the assembled endpoint. -/
def endpointMeasureResolved :
    M8CompactSupportMeasureResolvedData I omega
      S.endpointAutoBase.toBaseInput.selectedPartition
      S.endpointAutoBase.toBaseInput.targetImageInput.targetImages where
  measureLocalization := S.endpointMeasureLocalization

@[simp]
theorem endpointMeasureResolved_measureLocalization :
    S.endpointMeasureResolved.measureLocalization =
      S.endpointMeasureLocalization := by
  rfl

/--
Artificial-face cancellation generated from the localized-piece strict margins
used by the endpoint.  This is the explicit bridge through
`ArtificialFaceFromStrictBufferAuto`; the canonical theorem below uses the same
strict-buffer constructor route.
-/
def endpointArtificialFaceCancellationDataOfLocalizedPieceStrictMargins
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (pieceLower_lt_compactLower :
      forall x,
        x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner j <
            S.selection.compactActiveBoxData.lower x j)
    (compactUpper_lt_pieceUpper :
      forall x,
        x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          S.selection.compactActiveBoxData.upper x j <
            (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner j) :
    CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
      S.endpointAutoBase.toBaseInput.selectedPartition
      S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
      S.endpointMeasureResolved :=
  (S.endpointStrictBufferConstructorDataOfLocalizedPieceStrictMargins
    (S.endpointSelectedReconstructionBase.localizedPieceAlignmentOfM8ChartAlignment A)
    pieceLower_lt_compactLower compactUpper_lt_pieceUpper)
    |>.toCompactSupportArtificialFaceCancellationData
      (BoundaryPiece := BoundaryPiece)
      (measureResolved := S.endpointMeasureResolved)

/--
Canonical compact-support Stokes for a source-packaged endpoint, using only
constructor chart alignment and localized-piece strict margins.
-/
theorem canonical_stokes_ofM8ChartAlignmentAndLocalizedPieceStrictMargins
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (pieceLower_lt_compactLower :
      forall x,
        x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner j <
            S.selection.compactActiveBoxData.lower x j)
    (compactUpper_lt_pieceUpper :
      forall x,
        x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          S.selection.compactActiveBoxData.upper x j <
            (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner j) :
    S.canonicalIntegralInterface.stokesStatement := by
  have h :=
    S.stokes_ofM8ChartAlignmentAndLocalizedPieceStrictMargins A
      (S.endpointSelectedReconstructionBase.localizedPieceAlignmentOfM8ChartAlignment A)
      pieceLower_lt_compactLower compactUpper_lt_pieceUpper
  simpa [canonicalIntegralInterface, CanonicalIntegralInterface.stokesStatement] using h

/--
The same theorem with the endpoint conclusion displayed as the canonical
equality `manifoldExtDerivIntegral = boundaryFormIntegral`.
-/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndLocalizedPieceStrictMargins
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (pieceLower_lt_compactLower :
      forall x,
        x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner j <
            S.selection.compactActiveBoxData.lower x j)
    (compactUpper_lt_pieceUpper :
      forall x,
        x ∈ S.endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          S.selection.compactActiveBoxData.upper x j <
            (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner j) :
    S.canonicalIntegralInterface.manifoldExtDerivIntegral =
      S.canonicalIntegralInterface.boundaryFormIntegral := by
  simpa [CanonicalIntegralInterface.stokesStatement] using
    S.canonical_stokes_ofM8ChartAlignmentAndLocalizedPieceStrictMargins A
      pieceLower_lt_compactLower compactUpper_lt_pieceUpper

end NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources

/--
End-to-end endpoint source data after the compact-support partition constructor.

This record deliberately excludes fields that are already generated by
`NaturalCompactSupportPartitionConstructorData`: `formData`, finite-active
selection, smoothness, selected partition, and support containment.
-/
structure NaturalCompactSupportEndpointEndToEndSources
    (D : NaturalCompactSupportPartitionConstructorData I omega rho)
    (ExtInteriorPiece : Type ei)
    (ExtBoundaryPiece : Type eb)
    (BoundaryPiece : Type b)
    (mu : Measure (Fin (n + 1) -> Real))
    [IsFiniteMeasureOnCompacts mu]
    [IsManifold I 1 M] where
  /-- Oriented boundary-chart atlas used by the canonical boundary route. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Unified boundary source-shrink/project-local package. -/
  boundaryUnified :
    BoundarySourceAlignmentUnifiedData
      (I := I) (omega := omega)
      (selectedPartition := D.selectedPartition)
      (orientedBoundaryAtlas := orientedBoundaryAtlas)
      (BoundaryPiece := BoundaryPiece)
  /-- Localized interior pieces for the selected partition. -/
  localized : LocalizedInteriorM8Fields I omega D.selectedPartition
  /-- Selected reconstruction source; this packages the active-set equality. -/
  reconstructionSource :
    SelectedPartitionReconstructionSource I omega D.selectedPartition
      boundaryUnified.toM8TargetImageInput.targetImages
      ExtInteriorPiece ExtBoundaryPiece
  /-- Chartwise measure used by the bulk a.e. comparison. -/
  extDerivMeasure : M -> M -> Measure (Fin (n + 1) -> Real)
  /-- Canonical local bulk facts for the selected interior pieces. -/
  bulkLocalFacts :
    SelectedPartitionBulkCanonicalLocalFacts D.selectedPartition
      boundaryUnified.toM8TargetImageInput.targetImages localized
  /-- The selected bulk measure is the ambient volume measure. -/
  measure_eq_volume : mu = volume
  /-- Lower-face continuity for the canonical boundary route. -/
  boundaryFaceContinuity :
    ProjectLocalBoundaryCanonicalFaceContinuityData
      boundaryUnified.toProjectLocalGlobalStokesData
  /-- Selected-target chart-change data for the canonical boundary route. -/
  boundaryChartChange :
    BoundaryChartChangeSelectedFamilyData
      boundaryUnified.toProjectLocalGlobalStokesData

namespace NaturalCompactSupportEndpointEndToEndSources

variable {D : NaturalCompactSupportPartitionConstructorData I omega rho}

/-- The source-packaged compact-support endpoint generated from `D` and `E`. -/
def toSelectedReconstructionEndpointSource
    (E :
      NaturalCompactSupportEndpointEndToEndSources
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu) :
    NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources.ofPartitionConstructorData
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    (BoundaryPiece' := BoundaryPiece)
    (mu := mu)
    D E.orientedBoundaryAtlas E.boundaryUnified E.localized
    E.reconstructionSource E.extDerivMeasure E.bulkLocalFacts
    E.measure_eq_volume E.boundaryFaceContinuity E.boundaryChartChange

@[simp]
theorem toSelectedReconstructionEndpointSource_selectedPartition
    (E :
      NaturalCompactSupportEndpointEndToEndSources
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu) :
    (toSelectedReconstructionEndpointSource E).selectedPartition =
      D.selectedPartition := by
  rfl

@[simp]
theorem toSelectedReconstructionEndpointSource_localized
    (E :
      NaturalCompactSupportEndpointEndToEndSources
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu) :
    (toSelectedReconstructionEndpointSource E).localized =
      E.localized := by
  rfl

/-- The endpoint measure-localization data assembled from the end-to-end source. -/
abbrev endpointMeasureLocalization
    (E :
      NaturalCompactSupportEndpointEndToEndSources
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu) :
    M8MeasureLocalizationData I omega
      (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition
      (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.targetImageInput.targetImages :=
  (toSelectedReconstructionEndpointSource E).endpointMeasureLocalization

/-- The endpoint measure-resolution package assembled from the end-to-end source. -/
def endpointMeasureResolved
    (E :
      NaturalCompactSupportEndpointEndToEndSources
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu) :
    M8CompactSupportMeasureResolvedData I omega
      (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition
      (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.targetImageInput.targetImages :=
  (toSelectedReconstructionEndpointSource E).endpointMeasureResolved

/-- Canonical integral interface exposed by the assembled endpoint. -/
def canonicalIntegralInterface
    (E :
      NaturalCompactSupportEndpointEndToEndSources
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu) :
    CanonicalIntegralInterface I omega :=
  (toSelectedReconstructionEndpointSource E).canonicalIntegralInterface

@[simp]
theorem canonicalIntegralInterface_manifoldExtDerivIntegral
    (E :
      NaturalCompactSupportEndpointEndToEndSources
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu) :
    (canonicalIntegralInterface E).manifoldExtDerivIntegral =
      (endpointMeasureLocalization E).bulkMeasureIntegral := by
  rfl

@[simp]
theorem canonicalIntegralInterface_boundaryFormIntegral
    (E :
      NaturalCompactSupportEndpointEndToEndSources
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu) :
    (canonicalIntegralInterface E).boundaryFormIntegral =
      (endpointMeasureLocalization E).boundaryMeasureIntegral := by
  rfl

/--
Artificial-face cancellation generated from the end-to-end source, constructor
chart alignment, and localized-piece strict margins.
-/
def artificialFaceCancellationDataOfLocalizedPieceStrictMargins
    (E :
      NaturalCompactSupportEndpointEndToEndSources
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu)
    (A :
      LocalizedInteriorM8ChartAlignment
        (toSelectedReconstructionEndpointSource E).localized)
    (pieceLower_lt_compactLower :
      forall x,
        x ∈ (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          ((endpointMeasureLocalization E).localizedInterior.piece x).lowerCorner j <
            D.compactActiveBoxData.lower x j)
    (compactUpper_lt_pieceUpper :
      forall x,
        x ∈ (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          D.compactActiveBoxData.upper x j <
            ((endpointMeasureLocalization E).localizedInterior.piece x).upperCorner j) :
    CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
      ((toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition)
      ((toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.targetImageInput.targetImages)
      (endpointMeasureResolved E) :=
  (toSelectedReconstructionEndpointSource E)
    |>.endpointArtificialFaceCancellationDataOfLocalizedPieceStrictMargins A
      pieceLower_lt_compactLower compactUpper_lt_pieceUpper

/--
End-to-end canonical compact-support Stokes statement from the partition
constructor, endpoint source data, chart alignment, and localized-piece strict
margins.
-/
theorem canonical_stokes_ofM8ChartAlignmentAndLocalizedPieceStrictMargins
    (E :
      NaturalCompactSupportEndpointEndToEndSources
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu)
    (A :
      LocalizedInteriorM8ChartAlignment
        (toSelectedReconstructionEndpointSource E).localized)
    (pieceLower_lt_compactLower :
      forall x,
        x ∈ (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          ((endpointMeasureLocalization E).localizedInterior.piece x).lowerCorner j <
            D.compactActiveBoxData.lower x j)
    (compactUpper_lt_pieceUpper :
      forall x,
        x ∈ (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          D.compactActiveBoxData.upper x j <
            ((endpointMeasureLocalization E).localizedInterior.piece x).upperCorner j) :
    (canonicalIntegralInterface E).stokesStatement := by
  simpa [canonicalIntegralInterface] using
    (toSelectedReconstructionEndpointSource E)
      |>.canonical_stokes_ofM8ChartAlignmentAndLocalizedPieceStrictMargins A
        pieceLower_lt_compactLower compactUpper_lt_pieceUpper

/--
End-to-end canonical compact-support Stokes equality in theorem-facing form.
-/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndLocalizedPieceStrictMargins
    (E :
      NaturalCompactSupportEndpointEndToEndSources
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu)
    (A :
      LocalizedInteriorM8ChartAlignment
        (toSelectedReconstructionEndpointSource E).localized)
    (pieceLower_lt_compactLower :
      forall x,
        x ∈ (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          ((endpointMeasureLocalization E).localizedInterior.piece x).lowerCorner j <
            D.compactActiveBoxData.lower x j)
    (compactUpper_lt_pieceUpper :
      forall x,
        x ∈ (toSelectedReconstructionEndpointSource E).endpointAutoBase.toBaseInput.selectedPartition.active ->
        forall j : Fin (n + 1),
          D.compactActiveBoxData.upper x j <
            ((endpointMeasureLocalization E).localizedInterior.piece x).upperCorner j) :
    (canonicalIntegralInterface E).manifoldExtDerivIntegral =
      (canonicalIntegralInterface E).boundaryFormIntegral := by
  simpa [CanonicalIntegralInterface.stokesStatement] using
    canonical_stokes_ofM8ChartAlignmentAndLocalizedPieceStrictMargins E A
      pieceLower_lt_compactLower compactUpper_lt_pieceUpper

end NaturalCompactSupportEndpointEndToEndSources

end NaturalCompactSupportEndpointEndToEndAuto

end Stokes

end
