import Stokes.Global.ArtificialFaceAdjacencyToM8
import Stokes.Global.ArtificialFaceBufferSupport
import Stokes.Global.ArtificialFaceNaturalBuilder
import Stokes.Global.ArtificialFaceNaturalToM8

/-!
# Artificial-face cancellation facade

This file is a narrow public facade for the compact-support artificial-face
exit.  It does not prove a new cancellation theorem.  Instead it gives one
theorem-facing name for the existing routes:

* support-zero geometry or a compact-support box buffer;
* adjacent selected faces;
* overlap-pairing cancellation;
* already assembled M8 artificial-face fields.

The genuine geometric inputs remain in the lower files.  The point of this
facade is to keep global compact-support constructors from importing and
threading every artificial-face route separately.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section ArtificialFaceCancellationFacade

universe u w b f d g

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

/--
Public compact-support artificial-face cancellation package.

This is an alias for the existing natural builder, not a new semantic layer.
The facade name is intended for theorem statements that only need to know that
the artificial interior-boundary terms have been resolved.
-/
abbrev CompactSupportArtificialFaceCancellationData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureResolved :
      M8CompactSupportMeasureResolvedData I omega selectedPartition
        targetImages) :=
  NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
    selectedPartition targetImages measureResolved

namespace CompactSupportArtificialFaceCancellationData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureResolved :
  M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages}

/-- Expose the underlying M8 artificial-face fields. -/
def toM8ArtificialFaceFields
    (D :
      CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition targetImages
      measureResolved.measureLocalization :=
  NaturalCompactSupportArtificialFaceBuilderData.toM8ArtificialFaceFields D

/-- Expose the compact-support resolved artificial-face input. -/
def toResolvedData
    (D :
      CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  NaturalCompactSupportArtificialFaceBuilderData.toCompactSupportArtificialFaceResolvedData D

@[simp]
theorem toResolvedData_artificialFaces
    (D :
      CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    D.toResolvedData.artificialFaces = D.toM8ArtificialFaceFields.artificialFaces :=
  rfl

@[simp]
theorem toResolvedData_active
    (D :
      CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    D.toResolvedData.artificialFaces.activeCharts = selectedPartition.active :=
  D.toResolvedData.artificialFaces_active

@[simp]
theorem toResolvedData_pieces
    (D :
      CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    D.toResolvedData.artificialFaces.interiorPieces =
      fun _ : M => ({()} : Finset Unit) :=
  D.toResolvedData.artificialFaces_pieces

@[simp]
theorem toResolvedData_term
    (D :
      CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    D.toResolvedData.artificialFaces.interiorBoundaryTerm =
      measureResolved.measureLocalization.interiorBoundaryTerm :=
  D.toResolvedData.artificialFaces_term

/-- Build the facade from already assembled M8 artificial-face fields. -/
def ofFields
    (fields :
      M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
        targetImages measureResolved.measureLocalization) :
    CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  NaturalCompactSupportArtificialFaceBuilderData.ofFields fields

/-- Build the facade from route-independent natural artificial-face data. -/
def ofNaturalArtificialFaceData
    (D :
      M8NaturalArtificialFaceData I omega BoundaryPiece selectedPartition
        targetImages measureResolved.measureLocalization) :
    CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  ofFields D.fields

/-- Build the facade from selected support-zero geometry. -/
def ofSelectedPartitionSupportZeroGeometry
    (D :
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureResolved.measureLocalization) :
    CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  ofFields D.toM8ArtificialFaceFields

/-- Build the facade from a compact-support box buffer. -/
def ofCompactSupportBoxBuffer
    (D :
      CompactSupportBoxBuffer I omega selectedPartition targetImages
        measureResolved.measureLocalization) :
    CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  ofFields D.toM8ArtificialFaceFields

/-- Build the facade from selected support-zero local Stokes data. -/
def ofSelectedInteriorSupportZero
    (localStokesData : M -> InteriorLocalStokesData I omega)
    (support_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (localStokesData x).sourceChart
              (localStokesData x).targetChart omega) ⊆
          boxInteriorSupportBox
            (localStokesData x).lowerCorner
            (localStokesData x).upperCorner)
    (interiorBoundaryTerm_eq :
      forall x, x ∈ selectedPartition.active ->
        measureResolved.measureLocalization.interiorBoundaryTerm x () =
          (localStokesData x).artificialBoundaryTerm) :
    CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  NaturalCompactSupportArtificialFaceBuilderData.ofSelectedInteriorSupportZero
    (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureResolved := measureResolved)
    localStokesData support_subset_interiorBox interiorBoundaryTerm_eq

/-- Build the facade from M8-facing adjacent selected-face data. -/
def ofM8AdjacentSelectedFaceData
    {Face : Type f} {Geometry : Type g}
    (D :
      M8AdjacentSelectedFaceData I omega BoundaryPiece selectedPartition
        targetImages measureResolved.measureLocalization Face Geometry) :
    CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  ofFields D.toM8ArtificialFaceFields

/-- Build the facade from M8-facing overlap-pairing data. -/
def ofM8OverlapPairingFaceData
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D :
      M8OverlapPairingFaceData I omega BoundaryPiece selectedPartition
        targetImages measureResolved.measureLocalization Face FaceDimension
        Geometry) :
    CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  ofFields D.toM8ArtificialFaceFields

/-- Build the facade from raw adjacent selected-face data and M8 alignments. -/
def ofAdjacentSelectedFacesDataBoundaryTerm
    {Face : Type f} {Geometry : Type g}
    (D : AdjacentSelectedFacesData I omega M Unit Face Geometry)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces : D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.interiorPieces x ->
          measureResolved.measureLocalization.interiorBoundaryTerm x q =
            projectInteriorBoundaryIntegral I (D.sourceChart x q)
              (D.targetChart x q) omega (D.lowerCorner x q)
              (D.upperCorner x q)) :
    CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  NaturalCompactSupportArtificialFaceBuilderData.ofAdjacentSelectedFacesDataBoundaryTerm
    (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureResolved := measureResolved)
    D hactive hpieces hterm

/-- Build the facade from raw overlap-pairing data and M8 alignments. -/
def ofOverlapPairingDataBoundaryTerm
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D : ArtificialFaceOverlapPairingData M Unit Face FaceDimension Geometry)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces : D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.interiorPieces x ->
          measureResolved.measureLocalization.interiorBoundaryTerm x q =
            D.toArtificialFacePairingData.interiorBoundaryTerm x q) :
    CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  NaturalCompactSupportArtificialFaceBuilderData.ofOverlapPairingDataBoundaryTerm
    (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureResolved := measureResolved)
    D hactive hpieces hterm

end CompactSupportArtificialFaceCancellationData

namespace M8CompactSupportArtificialFaceResolvedData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureResolved :
  M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages}

/-- Compact-support resolved artificial-face data from the facade package. -/
def ofCancellationFacade
    (D :
      CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  D.toResolvedData

@[simp]
theorem ofCancellationFacade_artificialFaces
    (D :
      CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    (ofCancellationFacade (BoundaryPiece := BoundaryPiece)
      (measureResolved := measureResolved) D).artificialFaces =
        D.toM8ArtificialFaceFields.artificialFaces :=
  rfl

/-- Resolved artificial-face data from route-independent natural data. -/
def ofNaturalArtificialFaceData
    (D :
      M8NaturalArtificialFaceData I omega BoundaryPiece selectedPartition
        targetImages measureResolved.measureLocalization) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  (CompactSupportArtificialFaceCancellationData.ofNaturalArtificialFaceData
    (BoundaryPiece := BoundaryPiece) (measureResolved := measureResolved) D)
      |>.toResolvedData

end M8CompactSupportArtificialFaceResolvedData

namespace M8CompactSupportStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/--
Build compact-support M8 input from the artificial-face cancellation facade.

This keeps the theorem-facing constructor from mentioning the internal
`M8CompactSupportArtificialFaceResolvedData` projection.
-/
def ofArtificialFaceCancellation
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureResolved :
      M8CompactSupportMeasureResolvedData I omega selectedPartition
        targetImages)
    (artificial :
      CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
        selectedPartition targetImages measureResolved)
    (boundaryTargetResolved :
      M8CompactSupportBoundaryTargetResolvedData I omega formData
        selectedPartition targetImages measureResolved) :
    M8CompactSupportStokesInput I omega BoundaryPiece where
  formData := formData
  selectedPartition := selectedPartition
  targetImages := targetImages
  measureResolved := measureResolved
  artificialFaceResolved := artificial.toResolvedData
  boundaryTargetResolved := boundaryTargetResolved

@[simp]
theorem ofArtificialFaceCancellation_artificialFaceResolved
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureResolved :
      M8CompactSupportMeasureResolvedData I omega selectedPartition
        targetImages)
    (artificial :
      CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
        selectedPartition targetImages measureResolved)
    (boundaryTargetResolved :
      M8CompactSupportBoundaryTargetResolvedData I omega formData
        selectedPartition targetImages measureResolved) :
    (ofArtificialFaceCancellation (BoundaryPiece := BoundaryPiece)
      formData selectedPartition targetImages measureResolved artificial
      boundaryTargetResolved).artificialFaceResolved =
        artificial.toResolvedData :=
  rfl

/--
Compact-support M8 Stokes theorem using the artificial-face cancellation
facade as input.
-/
theorem stokes_ofArtificialFaceCancellation
    [IsManifold I 1 M]
    (formData : CompactlySupportedSmoothFormData I omega)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureResolved :
      M8CompactSupportMeasureResolvedData I omega selectedPartition
        targetImages)
    (artificial :
      CompactSupportArtificialFaceCancellationData I omega BoundaryPiece
        selectedPartition targetImages measureResolved)
    (boundaryTargetResolved :
      M8CompactSupportBoundaryTargetResolvedData I omega formData
        selectedPartition targetImages measureResolved) :
    measureResolved.measureLocalization.bulkMeasureIntegral =
      measureResolved.measureLocalization.boundaryMeasureIntegral :=
  (ofArtificialFaceCancellation (BoundaryPiece := BoundaryPiece)
    formData selectedPartition targetImages measureResolved artificial
    boundaryTargetResolved).stokes

end M8CompactSupportStokesInput

end ArtificialFaceCancellationFacade

end Stokes

end
