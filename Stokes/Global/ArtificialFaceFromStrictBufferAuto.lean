import Stokes.Global.ArtificialFaceCancellationFacade
import Stokes.Global.CompactActiveStrictBufferConstructorAuto

/-!
# Artificial-face cancellation from strict buffers

This file connects the compact-active strict-buffer constructors to the public
artificial-face cancellation facade.

The geometric content is the existing strict-buffer theorem:
`CompactActiveBoxStrictBufferAlignment` proves that active localized chart
representatives have topological support in the strict interior of the M8
localized boxes.  Once that support statement is available, the support-zero
artificial-face route already constructs the cancellation package.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section ArtificialFaceFromStrictBufferAuto

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureResolved :
  M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages}
variable {D : CompactActiveBoxData I omega}

namespace CompactSupportBoxBuffer

/--
Public artificial-face cancellation facade generated from a strict compact
support box buffer.
-/
def toCompactSupportArtificialFaceCancellationData
    (B :
      CompactSupportBoxBuffer I omega selectedPartition targetImages
        measureResolved.measureLocalization) :
    CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  CompactSupportArtificialFaceCancellationData.ofCompactSupportBoxBuffer
    (BoundaryPiece := BoundaryPiece) (measureResolved := measureResolved) B

@[simp]
theorem toCompactSupportArtificialFaceCancellationData_resolved
    (B :
      CompactSupportBoxBuffer I omega selectedPartition targetImages
        measureResolved.measureLocalization) :
    (B.toCompactSupportArtificialFaceCancellationData
      (BoundaryPiece := BoundaryPiece)
      (measureResolved := measureResolved)).toResolvedData =
        B.toCompactSupportArtificialFaceResolvedData := by
  rfl

end CompactSupportBoxBuffer

namespace CompactActiveBoxStrictBufferAlignment

/--
Artificial-face cancellation facade from compact-active strict-buffer
alignment.
-/
def toCompactSupportArtificialFaceCancellationData
    (A :
      CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
        measureResolved.measureLocalization) :
    CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  A.toCompactSupportBoxBuffer
    |>.toCompactSupportArtificialFaceCancellationData
      (BoundaryPiece := BoundaryPiece) (measureResolved := measureResolved)

/-- Compact-support resolved artificial-face data from strict-buffer alignment. -/
def toCompactSupportArtificialFaceResolvedData
    (A :
      CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
        measureResolved.measureLocalization) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  (A.toCompactSupportArtificialFaceCancellationData
    (BoundaryPiece := BoundaryPiece) (measureResolved := measureResolved))
    |>.toResolvedData

@[simp]
theorem toCompactSupportArtificialFaceCancellationData_resolved
    (A :
      CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
        measureResolved.measureLocalization) :
    (A.toCompactSupportArtificialFaceCancellationData
      (BoundaryPiece := BoundaryPiece)
      (measureResolved := measureResolved)).toResolvedData =
        A.toCompactSupportBoxBuffer.toCompactSupportArtificialFaceResolvedData := by
  rfl

@[simp]
theorem toCompactSupportArtificialFaceResolvedData_artificialFaces
    (A :
      CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
        measureResolved.measureLocalization) :
    (A.toCompactSupportArtificialFaceResolvedData
      (BoundaryPiece := BoundaryPiece)
      (measureResolved := measureResolved)).artificialFaces =
        A.toCompactSupportBoxBuffer.toM8ArtificialFaceFields.artificialFaces := by
  rfl

end CompactActiveBoxStrictBufferAlignment

namespace CompactActiveStrictBufferConstructorData

/--
Artificial-face cancellation facade from single-source strict-buffer
constructor data.
-/
def toCompactSupportArtificialFaceCancellationData
    (A :
      CompactActiveStrictBufferConstructorData D selectedPartition targetImages
        measureResolved.measureLocalization) :
    CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  A.toCompactActiveBoxStrictBufferAlignment
    |>.toCompactSupportArtificialFaceCancellationData
      (BoundaryPiece := BoundaryPiece) (measureResolved := measureResolved)

/--
Compact-support resolved artificial-face data from single-source strict-buffer
constructor data.
-/
def toCompactSupportArtificialFaceResolvedData
    (A :
      CompactActiveStrictBufferConstructorData D selectedPartition targetImages
        measureResolved.measureLocalization) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  (A.toCompactSupportArtificialFaceCancellationData
    (BoundaryPiece := BoundaryPiece) (measureResolved := measureResolved))
    |>.toResolvedData

@[simp]
theorem toCompactSupportArtificialFaceCancellationData_resolved
    (A :
      CompactActiveStrictBufferConstructorData D selectedPartition targetImages
        measureResolved.measureLocalization) :
    (A.toCompactSupportArtificialFaceCancellationData
      (BoundaryPiece := BoundaryPiece)
      (measureResolved := measureResolved)).toResolvedData =
        (A.toCompactActiveBoxStrictBufferAlignment
          |>.toCompactSupportArtificialFaceResolvedData
            (BoundaryPiece := BoundaryPiece)
            (measureResolved := measureResolved)) := by
  rfl

end CompactActiveStrictBufferConstructorData

namespace CompactSupportFiniteActiveSelection

variable {rho : SmoothPartitionOfUnity M I M univ}
variable {K : Set M} {hK : IsCompact K}
variable
    (S : CompactSupportFiniteActiveSelection
      (I := I) rho K hK omega)
    (smoothness :
      ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega)

/--
Artificial-face cancellation facade from a finite active compact-support
selection and named strict outer boxes around its compact active boxes.
-/
def artificialFaceCancellationOfStrictOuterBoxData
    {targetImages :
      BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureResolved :
      M8CompactSupportMeasureResolvedData I omega
        (S.selectedBoxPartitionOfUnity smoothness) targetImages}
    (outerBoxData :
      CompactActiveStrictOuterBoxData S.compactActiveBoxData)
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment (S.selectedBoxPartitionOfUnity smoothness)
        targetImages measureResolved.measureLocalization)
    (outerLower_eq_pieceLower :
      forall x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active ->
        outerBoxData.outerLower x =
          (measureResolved.measureLocalization.localizedInterior.piece x).lowerCorner)
    (outerUpper_eq_pieceUpper :
      forall x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active ->
        outerBoxData.outerUpper x =
          (measureResolved.measureLocalization.localizedInterior.piece x).upperCorner) :
    CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
      (S.selectedBoxPartitionOfUnity smoothness) targetImages measureResolved :=
  (S.toStrictBufferConstructorDataOfStrictOuterBoxData
    (BoundaryPiece := BoundaryPiece) smoothness outerBoxData
    localizedPieceAlignment outerLower_eq_pieceLower outerUpper_eq_pieceUpper)
    |>.toCompactSupportArtificialFaceCancellationData
      (BoundaryPiece := BoundaryPiece) (measureResolved := measureResolved)

end CompactSupportFiniteActiveSelection

namespace M8CompactSupportStokesInput

variable {formData : CompactlySupportedSmoothFormData I omega}

/--
Build compact-support M8 input using artificial-face cancellation generated
from compact-active strict-buffer alignment.
-/
def ofArtificialFaceStrictBufferAlignment
    (boundaryTargetResolved :
      M8CompactSupportBoundaryTargetResolvedData I omega formData
        selectedPartition targetImages measureResolved)
    (alignment :
      CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
        measureResolved.measureLocalization) :
    M8CompactSupportStokesInput I omega BoundaryPiece :=
  ofArtificialFaceCancellation
    (BoundaryPiece := BoundaryPiece)
    formData selectedPartition targetImages measureResolved
    (alignment.toCompactSupportArtificialFaceCancellationData
      (BoundaryPiece := BoundaryPiece) (measureResolved := measureResolved))
    boundaryTargetResolved

/--
Build compact-support M8 input using artificial-face cancellation generated
from single-source strict-buffer constructor data.
-/
def ofArtificialFaceStrictBufferConstructorData
    (boundaryTargetResolved :
      M8CompactSupportBoundaryTargetResolvedData I omega formData
        selectedPartition targetImages measureResolved)
    (constructorData :
      CompactActiveStrictBufferConstructorData D selectedPartition targetImages
        measureResolved.measureLocalization) :
    M8CompactSupportStokesInput I omega BoundaryPiece :=
  ofArtificialFaceCancellation
    (BoundaryPiece := BoundaryPiece)
    formData selectedPartition targetImages measureResolved
    (constructorData.toCompactSupportArtificialFaceCancellationData
      (BoundaryPiece := BoundaryPiece) (measureResolved := measureResolved))
    boundaryTargetResolved

@[simp]
theorem ofArtificialFaceStrictBufferConstructorData_artificialFaceResolved
    (boundaryTargetResolved :
      M8CompactSupportBoundaryTargetResolvedData I omega formData
        selectedPartition targetImages measureResolved)
    (constructorData :
      CompactActiveStrictBufferConstructorData D selectedPartition targetImages
        measureResolved.measureLocalization) :
    (ofArtificialFaceStrictBufferConstructorData
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      boundaryTargetResolved constructorData).artificialFaceResolved =
        ((constructorData.toCompactSupportArtificialFaceCancellationData
          (BoundaryPiece := BoundaryPiece) (measureResolved := measureResolved))
          |>.toResolvedData) := by
  rfl

/--
Compact-support M8 Stokes theorem with artificial faces constructed from
compact-active strict-buffer alignment.
-/
theorem stokes_ofArtificialFaceStrictBufferAlignment
    [IsManifold I 1 M]
    (boundaryTargetResolved :
      M8CompactSupportBoundaryTargetResolvedData I omega formData
        selectedPartition targetImages measureResolved)
    (alignment :
      CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
        measureResolved.measureLocalization) :
    measureResolved.measureLocalization.bulkMeasureIntegral =
      measureResolved.measureLocalization.boundaryMeasureIntegral :=
  (ofArtificialFaceStrictBufferAlignment
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    boundaryTargetResolved alignment).stokes

/--
Compact-support M8 Stokes theorem with artificial faces constructed from
single-source strict-buffer constructor data.
-/
theorem stokes_ofArtificialFaceStrictBufferConstructorData
    [IsManifold I 1 M]
    (boundaryTargetResolved :
      M8CompactSupportBoundaryTargetResolvedData I omega formData
        selectedPartition targetImages measureResolved)
    (constructorData :
      CompactActiveStrictBufferConstructorData D selectedPartition targetImages
        measureResolved.measureLocalization) :
    measureResolved.measureLocalization.bulkMeasureIntegral =
      measureResolved.measureLocalization.boundaryMeasureIntegral :=
  (ofArtificialFaceStrictBufferConstructorData
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    boundaryTargetResolved constructorData).stokes

end M8CompactSupportStokesInput

end ArtificialFaceFromStrictBufferAuto

end Stokes

end
