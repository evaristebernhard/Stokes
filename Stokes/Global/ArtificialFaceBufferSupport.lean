import Stokes.Global.ArtificialFaceSupportZeroGeometry

/-!
# Buffered compact support for artificial-face cancellation

This file provides the thin bridge from a chart-box buffer support package to
the existing support-zero artificial-face constructors.

The real geometric input is still the strict containment statement: every
active localized chart representative has topological support inside the strict
interior support box.  Once that is available, the existing
`ArtificialFaceSupportZeroGeometry` API turns it into the M8 artificial-face
fields and the compact-support-facing resolved package.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section ArtificialFaceBufferSupport

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

/--
Buffered compact-support data for the selected local boxes.

This is intentionally only the support fact consumed by artificial-face
cancellation.  A later chart-box selection layer can construct this record from
larger/smaller buffered boxes without changing the M8-facing API.
-/
structure CompactSupportBoxBuffer {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages) where
  /--
  Every active localized chart representative is supported in the strict
  interior of the selected auxiliary coordinate box.
  -/
  strictSupport_subset_interiorBox :
    forall x, x ∈ selectedPartition.active ->
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (measureLocalization.localizedInterior.piece x).sourceChart
            (measureLocalization.localizedInterior.piece x).targetChart
            (measureLocalization.localizedInterior.piece x).localizedForm) ⊆
        boxInteriorSupportBox
          (measureLocalization.localizedInterior.piece x).lowerCorner
          (measureLocalization.localizedInterior.piece x).upperCorner

namespace CompactSupportBoxBuffer

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/--
Forget the buffer packaging and expose the support-zero geometry package already
used by the artificial-face API.
-/
def toSelectedPartitionSupportZeroGeometry
    (D :
      CompactSupportBoxBuffer I omega selectedPartition targetImages
        measureLocalization) :
    SelectedPartitionSupportZeroGeometry I omega selectedPartition targetImages
      measureLocalization where
  support_subset_interiorBox := D.strictSupport_subset_interiorBox

@[simp]
theorem toSelectedPartitionSupportZeroGeometry_support_subset
    (D :
      CompactSupportBoxBuffer I omega selectedPartition targetImages
        measureLocalization) :
    D.toSelectedPartitionSupportZeroGeometry.support_subset_interiorBox =
      D.strictSupport_subset_interiorBox :=
  rfl

/-- M8 artificial-face fields generated from buffered strict support. -/
def toM8ArtificialFaceFields
    (D :
      CompactSupportBoxBuffer I omega selectedPartition targetImages
        measureLocalization) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  D.toSelectedPartitionSupportZeroGeometry.toM8ArtificialFaceFields

@[simp]
theorem toM8ArtificialFaceFields_artificialFaces
    (D :
      CompactSupportBoxBuffer I omega selectedPartition targetImages
        measureLocalization) :
    D.toM8ArtificialFaceFields.artificialFaces =
      D.toSelectedPartitionSupportZeroGeometry.toArtificialFaceResolvedData := by
  rfl

@[simp]
theorem toM8ArtificialFaceFields_active
    (D :
      CompactSupportBoxBuffer I omega selectedPartition targetImages
        measureLocalization) :
    D.toM8ArtificialFaceFields.artificialFaces.activeCharts =
      selectedPartition.active :=
  D.toM8ArtificialFaceFields.artificialFaces_active

@[simp]
theorem toM8ArtificialFaceFields_pieces
    (D :
      CompactSupportBoxBuffer I omega selectedPartition targetImages
        measureLocalization) :
    D.toM8ArtificialFaceFields.artificialFaces.interiorPieces =
      fun _ : M => ({()} : Finset Unit) :=
  D.toM8ArtificialFaceFields.artificialFaces_pieces

@[simp]
theorem toM8ArtificialFaceFields_term
    (D :
      CompactSupportBoxBuffer I omega selectedPartition targetImages
        measureLocalization) :
    D.toM8ArtificialFaceFields.artificialFaces.interiorBoundaryTerm =
      measureLocalization.interiorBoundaryTerm :=
  D.toM8ArtificialFaceFields.artificialFaces_term

/--
Compact-support-facing artificial-face resolved data generated from buffered
strict support.
-/
def toCompactSupportArtificialFaceResolvedData
    {measureResolved :
      M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages}
    (D :
      CompactSupportBoxBuffer I omega selectedPartition targetImages
        measureResolved.measureLocalization) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  D.toSelectedPartitionSupportZeroGeometry
    |>.toCompactSupportArtificialFaceResolvedData

@[simp]
theorem toCompactSupportArtificialFaceResolvedData_artificialFaces
    {measureResolved :
      M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages}
    (D :
      CompactSupportBoxBuffer I omega selectedPartition targetImages
        measureResolved.measureLocalization) :
    D.toCompactSupportArtificialFaceResolvedData.artificialFaces =
      D.toM8ArtificialFaceFields.artificialFaces :=
  rfl

end CompactSupportBoxBuffer

namespace M8ArtificialFaceFields

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/-- Constructor spelling for M8 artificial-face fields from a compact-support buffer. -/
def ofCompactSupportBoxBuffer
    (D :
      CompactSupportBoxBuffer I omega selectedPartition targetImages
        measureLocalization) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  D.toM8ArtificialFaceFields

@[simp]
theorem ofCompactSupportBoxBuffer_active
    (D :
      CompactSupportBoxBuffer I omega selectedPartition targetImages
        measureLocalization) :
    (ofCompactSupportBoxBuffer (BoundaryPiece := BoundaryPiece) D).artificialFaces.activeCharts =
      selectedPartition.active :=
  D.toM8ArtificialFaceFields_active

end M8ArtificialFaceFields

namespace M8CompactSupportArtificialFaceResolvedData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureResolved :
  M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages}

/--
Constructor spelling for compact-support artificial-face resolved data from a
compact-support buffer.
-/
def ofCompactSupportBoxBuffer
    (D :
      CompactSupportBoxBuffer I omega selectedPartition targetImages
        measureResolved.measureLocalization) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  D.toCompactSupportArtificialFaceResolvedData

@[simp]
theorem ofCompactSupportBoxBuffer_active
    (D :
      CompactSupportBoxBuffer I omega selectedPartition targetImages
        measureResolved.measureLocalization) :
    (ofCompactSupportBoxBuffer (BoundaryPiece := BoundaryPiece)
      (measureResolved := measureResolved) D).artificialFaces.activeCharts =
        selectedPartition.active :=
  D.toM8ArtificialFaceFields_active

end M8CompactSupportArtificialFaceResolvedData

end ArtificialFaceBufferSupport

end Stokes

end
