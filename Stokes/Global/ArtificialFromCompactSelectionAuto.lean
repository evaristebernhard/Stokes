import Stokes.Global.NaturalEndpointArtificialAuto
import Stokes.Global.SelectedPartitionCompactActiveAlignment
import Stokes.Global.LocalizedInteriorPieceAlignment

/-!
# Artificial-face data from compact-support chart-box selections

This module closes the compact-selection route to artificial-face support-zero
geometry.  The constructors below start with the selected compact chart boxes
coming from `CompactSupportFiniteActiveSelection` and `ActiveCompactBoxSmoothness`.
Given the remaining localized-piece chart alignment and strict outer margins,
they derive the endpoint strict-support field, the selected support-zero
geometry, and the artificial-face endpoint sources.

The proof is not a field-name adapter: it uses the active compact boxes to get
closed inner-box support for the localized representatives, then pushes that
support through the strict margin into the outer `boxInteriorSupportBox`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section ArtificialFromCompactSelectionAuto

universe u w b ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {ρ : SmoothPartitionOfUnity M I M univ}
variable {K : Set M} {hK : IsCompact K}
variable {μ : Measure (Fin (n + 1) → Real)}
variable [IsFiniteMeasureOnCompacts μ]
variable [IsManifold I 1 M]

namespace CompactSupportFiniteActiveSelection

variable
    (S : CompactSupportFiniteActiveSelection (I := I) ρ K hK omega)
    (smoothness : ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega)
variable {targetImages :
    BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
    M8MeasureLocalizationData I omega
      (S.selectedBoxPartitionOfUnity smoothness) targetImages}

/-- Strict-buffer alignment generated from compact selected boxes plus the
localized-piece chart alignment and strict outer-box margins. -/
def toCompactActiveBoxStrictBufferAlignmentOfLocalizedPiece
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization)
    (outer_lower_lt_selectedLower :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        ∀ j : Fin (n + 1),
          (measureLocalization.localizedInterior.piece x).lowerCorner j <
            (S.selectedBoxPartitionOfUnity smoothness).lower x j)
    (selectedUpper_lt_outer_upper :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        ∀ j : Fin (n + 1),
          (S.selectedBoxPartitionOfUnity smoothness).upper x j <
            (measureLocalization.localizedInterior.piece x).upperCorner j) :
    CompactActiveBoxStrictBufferAlignment S.compactActiveBoxData
      (S.selectedBoxPartitionOfUnity smoothness) targetImages
      measureLocalization :=
  (S.toCompactActiveSelectedPartitionAlignment smoothness)
    |>.toStrictBufferAlignmentOfSelectedPartitionPiece
      localizedPieceAlignment.piece_transitionPullback_eq
      outer_lower_lt_selectedLower
      selectedUpper_lt_outer_upper

/--
The strict support field consumed by artificial-face support-zero cancellation,
derived from compact active closed-box support and strict margins.
-/
theorem strictSupport_subset_interiorBox_ofLocalizedPiece
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization)
    (outer_lower_lt_selectedLower :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        ∀ j : Fin (n + 1),
          (measureLocalization.localizedInterior.piece x).lowerCorner j <
            (S.selectedBoxPartitionOfUnity smoothness).lower x j)
    (selectedUpper_lt_outer_upper :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        ∀ j : Fin (n + 1),
          (S.selectedBoxPartitionOfUnity smoothness).upper x j <
            (measureLocalization.localizedInterior.piece x).upperCorner j) :
    ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (measureLocalization.localizedInterior.piece x).sourceChart
            (measureLocalization.localizedInterior.piece x).targetChart
            (measureLocalization.localizedInterior.piece x).localizedForm) ⊆
        boxInteriorSupportBox
          (measureLocalization.localizedInterior.piece x).lowerCorner
          (measureLocalization.localizedInterior.piece x).upperCorner :=
  (S.toCompactActiveBoxStrictBufferAlignmentOfLocalizedPiece smoothness
    localizedPieceAlignment outer_lower_lt_selectedLower
    selectedUpper_lt_outer_upper)
      |>.toLocalizedInteriorFormInnerBoxBuffer
      |>.localized_tsupport_subset_interiorBox

/-- Compact-support box buffer produced directly from selected compact boxes. -/
def toCompactSupportBoxBufferOfLocalizedPiece
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization)
    (outer_lower_lt_selectedLower :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        ∀ j : Fin (n + 1),
          (measureLocalization.localizedInterior.piece x).lowerCorner j <
            (S.selectedBoxPartitionOfUnity smoothness).lower x j)
    (selectedUpper_lt_outer_upper :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        ∀ j : Fin (n + 1),
          (S.selectedBoxPartitionOfUnity smoothness).upper x j <
            (measureLocalization.localizedInterior.piece x).upperCorner j) :
    CompactSupportBoxBuffer I omega (S.selectedBoxPartitionOfUnity smoothness)
      targetImages measureLocalization :=
  (S.toCompactActiveBoxStrictBufferAlignmentOfLocalizedPiece smoothness
    localizedPieceAlignment outer_lower_lt_selectedLower
    selectedUpper_lt_outer_upper).toCompactSupportBoxBuffer

/-- Selected support-zero geometry produced from compact selected boxes. -/
def toSelectedPartitionSupportZeroGeometryOfLocalizedPiece
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization)
    (outer_lower_lt_selectedLower :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        ∀ j : Fin (n + 1),
          (measureLocalization.localizedInterior.piece x).lowerCorner j <
            (S.selectedBoxPartitionOfUnity smoothness).lower x j)
    (selectedUpper_lt_outer_upper :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        ∀ j : Fin (n + 1),
          (S.selectedBoxPartitionOfUnity smoothness).upper x j <
            (measureLocalization.localizedInterior.piece x).upperCorner j) :
    SelectedPartitionSupportZeroGeometry I omega
      (S.selectedBoxPartitionOfUnity smoothness) targetImages
      measureLocalization where
  support_subset_interiorBox :=
    S.strictSupport_subset_interiorBox_ofLocalizedPiece smoothness
      localizedPieceAlignment outer_lower_lt_selectedLower
      selectedUpper_lt_outer_upper

/-- M8 artificial-face fields produced from compact selected boxes. -/
def toM8ArtificialFaceFieldsOfLocalizedPiece
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization)
    (outer_lower_lt_selectedLower :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        ∀ j : Fin (n + 1),
          (measureLocalization.localizedInterior.piece x).lowerCorner j <
            (S.selectedBoxPartitionOfUnity smoothness).lower x j)
    (selectedUpper_lt_outer_upper :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        ∀ j : Fin (n + 1),
          (S.selectedBoxPartitionOfUnity smoothness).upper x j <
            (measureLocalization.localizedInterior.piece x).upperCorner j) :
    M8ArtificialFaceFields I omega BoundaryPiece
      (S.selectedBoxPartitionOfUnity smoothness) targetImages
      measureLocalization :=
  (S.toSelectedPartitionSupportZeroGeometryOfLocalizedPiece
    (BoundaryPiece := BoundaryPiece) smoothness localizedPieceAlignment
    outer_lower_lt_selectedLower selectedUpper_lt_outer_upper).toM8ArtificialFaceFields

@[simp]
theorem toM8ArtificialFaceFieldsOfLocalizedPiece_active
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureLocalization)
    (outer_lower_lt_selectedLower :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        ∀ j : Fin (n + 1),
          (measureLocalization.localizedInterior.piece x).lowerCorner j <
            (S.selectedBoxPartitionOfUnity smoothness).lower x j)
    (selectedUpper_lt_outer_upper :
      ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
        ∀ j : Fin (n + 1),
          (S.selectedBoxPartitionOfUnity smoothness).upper x j <
            (measureLocalization.localizedInterior.piece x).upperCorner j) :
    (S.toM8ArtificialFaceFieldsOfLocalizedPiece
      (BoundaryPiece := BoundaryPiece) smoothness localizedPieceAlignment
      outer_lower_lt_selectedLower
      selectedUpper_lt_outer_upper).artificialFaces.activeCharts =
        (S.selectedBoxPartitionOfUnity smoothness).active :=
  (S.toSelectedPartitionSupportZeroGeometryOfLocalizedPiece
    (BoundaryPiece := BoundaryPiece) smoothness localizedPieceAlignment
    outer_lower_lt_selectedLower selectedUpper_lt_outer_upper)
      |>.toM8ArtificialFaceFields_active

end CompactSupportFiniteActiveSelection

/--
Endpoint-local alignment data needed to derive artificial-face cancellation
from the compact-support selected chart boxes already stored in the endpoint
base sources.
-/
structure EndpointCompactSelectionArtificialAlignment
    (base :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ) where
  /-- The assembled endpoint localized pieces use the selected chart label. -/
  localizedPieceAlignment :
    LocalizedInteriorPieceAlignment base.toBaseInput.selectedPartition
      base.toBaseInput.targetImageInput.targetImages
      base.endpointMeasureLocalization
  /-- Endpoint outer lower corners sit strictly below the selected compact boxes. -/
  outer_lower_lt_selectedLower :
    ∀ x, x ∈ base.toBaseInput.selectedPartition.active →
      ∀ j : Fin (n + 1),
        (base.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner j <
          base.toBaseInput.selectedPartition.lower x j
  /-- Selected compact boxes sit strictly below the endpoint outer upper corners. -/
  selectedUpper_lt_outer_upper :
    ∀ x, x ∈ base.toBaseInput.selectedPartition.active →
      ∀ j : Fin (n + 1),
        base.toBaseInput.selectedPartition.upper x j <
          (base.endpointMeasureLocalization.localizedInterior.piece x).upperCorner j

namespace EndpointCompactSelectionArtificialAlignment

variable
    {base :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ}

/-- Strict support for endpoint artificial faces, derived from compact selection data. -/
theorem strictSupport_subset_interiorBox
    (A : EndpointCompactSelectionArtificialAlignment base) :
    ∀ x, x ∈ base.toBaseInput.selectedPartition.active →
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (base.endpointMeasureLocalization.localizedInterior.piece x).sourceChart
            (base.endpointMeasureLocalization.localizedInterior.piece x).targetChart
            (base.endpointMeasureLocalization.localizedInterior.piece x).localizedForm) ⊆
        boxInteriorSupportBox
          (base.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner
          (base.endpointMeasureLocalization.localizedInterior.piece x).upperCorner :=
  base.selection.strictSupport_subset_interiorBox_ofLocalizedPiece
    (BoundaryPiece := BoundaryPiece) base.smoothness A.localizedPieceAlignment
    A.outer_lower_lt_selectedLower A.selectedUpper_lt_outer_upper

/-- Endpoint selected support-zero geometry generated from compact selection data. -/
def toSelectedPartitionSupportZeroGeometry
    (A : EndpointCompactSelectionArtificialAlignment base) :
    SelectedPartitionSupportZeroGeometry I omega base.toBaseInput.selectedPartition
      base.toBaseInput.targetImageInput.targetImages
      base.endpointMeasureLocalization where
  support_subset_interiorBox := A.strictSupport_subset_interiorBox

/-- Endpoint compact-support buffer generated from compact selection data. -/
def toCompactSupportBoxBuffer
    (A : EndpointCompactSelectionArtificialAlignment base) :
    CompactSupportBoxBuffer I omega base.toBaseInput.selectedPartition
      base.toBaseInput.targetImageInput.targetImages
      base.endpointMeasureLocalization :=
  CompactSupportBoxBuffer.ofStrictSupportSubsetInteriorBox
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := base.toBaseInput.selectedPartition)
    (targetImages := base.toBaseInput.targetImageInput.targetImages)
    (measureLocalization := base.endpointMeasureLocalization)
    A.strictSupport_subset_interiorBox

/-- Endpoint artificial-face fields generated from compact selection data. -/
def toM8ArtificialFaceFields
    (A : EndpointCompactSelectionArtificialAlignment base) :
    M8ArtificialFaceFields I omega BoundaryPiece
      base.toBaseInput.selectedPartition
      base.toBaseInput.targetImageInput.targetImages
      base.endpointMeasureLocalization :=
  A.toSelectedPartitionSupportZeroGeometry.toM8ArtificialFaceFields

@[simp]
theorem toM8ArtificialFaceFields_active
    (A : EndpointCompactSelectionArtificialAlignment base) :
    A.toM8ArtificialFaceFields.artificialFaces.activeCharts =
      base.toBaseInput.selectedPartition.active :=
  A.toSelectedPartitionSupportZeroGeometry.toM8ArtificialFaceFields_active

end EndpointCompactSelectionArtificialAlignment

namespace NaturalCompactSupportEndpointAutoSelectedBaseSources

variable
    (base :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ)

/-- Endpoint artificial-face fields directly from compact selected chart boxes. -/
def artificialOfCompactSelection
    (alignment : EndpointCompactSelectionArtificialAlignment base) :
    M8ArtificialFaceFields I omega BoundaryPiece
      base.toBaseInput.selectedPartition
      base.toBaseInput.targetImageInput.targetImages
      base.endpointMeasureLocalization :=
  alignment.toM8ArtificialFaceFields

@[simp]
theorem artificialOfCompactSelection_active
    (alignment : EndpointCompactSelectionArtificialAlignment base) :
    (base.artificialOfCompactSelection alignment).artificialFaces.activeCharts =
      base.toBaseInput.selectedPartition.active :=
  alignment.toM8ArtificialFaceFields_active

end NaturalCompactSupportEndpointAutoSelectedBaseSources

namespace NaturalCompactSupportEndpointAutoSelectedSources

/--
Build full endpoint sources with artificial faces generated from compact-support
selected chart-box data.
-/
def ofBaseAndCompactSelectionAlignment
    (base :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ)
    (alignment : EndpointCompactSelectionArtificialAlignment base) :
    NaturalCompactSupportEndpointAutoSelectedSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ where
  base := base
  artificial := base.artificialOfCompactSelection alignment

@[simp]
theorem ofBaseAndCompactSelectionAlignment_artificial
    (base :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ)
    (alignment : EndpointCompactSelectionArtificialAlignment base) :
    (ofBaseAndCompactSelectionAlignment
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      base alignment).artificial =
        base.artificialOfCompactSelection alignment :=
  rfl

/-- Endpoint theorem using artificial faces generated from compact selection data. -/
theorem stokes_ofCompactSelectionAlignment
    (base :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ)
    (alignment : EndpointCompactSelectionArtificialAlignment base) :
    base.endpointMeasureLocalization.bulkMeasureIntegral =
      base.endpointMeasureLocalization.boundaryMeasureIntegral :=
  (ofBaseAndCompactSelectionAlignment
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    base alignment).stokes

end NaturalCompactSupportEndpointAutoSelectedSources

end ArtificialFromCompactSelectionAuto

end Stokes

end
