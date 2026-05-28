import Stokes.Global.ArtificialFaceSupportZeroToM8
import Stokes.Global.ArtificialFacePairingToM8

/-!
# Natural artificial-face packages for compact-support M8

This file gives a common compact-support-facing wrapper for the two current
routes that resolve artificial interior-boundary terms:

* strict support inside the selected interior box;
* pairing of artificial faces, either from overlap data or adjacent selected
  faces.

No new cancellation theorem is proved here.  The file only forgets which route
was used and exposes the `M8CompactSupportArtificialFaceResolvedData` package
needed by compact-support M8 and natural compact-support Stokes.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section ArtificialFaceNaturalToM8

universe u w b f d g

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

/--
Route-independent artificial-face package for the compact-support M8 theorem.

The field `fields` is the M8-facing artificial-face package.  It may have been
constructed by support-zero, overlap pairing, or adjacent selected-face pairing.
-/
structure M8NaturalArtificialFaceData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages) where
  /-- M8-facing artificial-face fields, with cancellation already resolved. -/
  fields :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization

namespace M8NaturalArtificialFaceData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/-- Resolved artificial-face data exposed by the route-independent package. -/
abbrev artificialFaces
    (D :
      M8NaturalArtificialFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization) :
    ArtificialFaceResolvedData M Unit :=
  D.fields.artificialFaces

@[simp]
theorem artificialFaces_active
    (D :
      M8NaturalArtificialFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization) :
    D.artificialFaces.activeCharts = selectedPartition.active :=
  D.fields.artificialFaces_active

@[simp]
theorem artificialFaces_pieces
    (D :
      M8NaturalArtificialFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization) :
    D.artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit) :=
  D.fields.artificialFaces_pieces

@[simp]
theorem artificialFaces_term
    (D :
      M8NaturalArtificialFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization) :
    D.artificialFaces.interiorBoundaryTerm =
      measureLocalization.interiorBoundaryTerm :=
  D.fields.artificialFaces_term

/-- Forget the route-independent package down to compact-support M8 input data. -/
def toCompactSupportArtificialFaceResolvedData
    {measureResolved :
      M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages}
    (D :
      M8NaturalArtificialFaceData I omega BoundaryPiece selectedPartition
        targetImages measureResolved.measureLocalization) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved where
  artificialFaces := D.fields.artificialFaces
  artificialFaces_active := D.fields.artificialFaces_active
  artificialFaces_pieces := D.fields.artificialFaces_pieces
  artificialFaces_term := D.fields.artificialFaces_term

@[simp]
theorem toCompactSupportArtificialFaceResolvedData_artificialFaces
    {measureResolved :
      M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages}
    (D :
      M8NaturalArtificialFaceData I omega BoundaryPiece selectedPartition
        targetImages measureResolved.measureLocalization) :
    D.toCompactSupportArtificialFaceResolvedData.artificialFaces =
      D.fields.artificialFaces :=
  rfl

/-- Constructor from an already-built M8 artificial-face field package. -/
def ofFields
    (fields :
      M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
        targetImages measureLocalization) :
    M8NaturalArtificialFaceData I omega BoundaryPiece selectedPartition
      targetImages measureLocalization where
  fields := fields

/-- Constructor from selected support-zero data. -/
def ofSupportZeroData
    (D :
      M8ArtificialFaceSupportZeroData I omega selectedPartition targetImages
        measureLocalization) :
    M8NaturalArtificialFaceData I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  ofFields D.toM8ArtificialFaceFields

/-- Constructor from overlap-pairing data and a global term-family equality. -/
def ofOverlapPairingData
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D : ArtificialFaceOverlapPairingData M Unit Face FaceDimension Geometry)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      D.toArtificialFacePairingData.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm) :
    M8NaturalArtificialFaceData I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  ofFields <|
    M8ArtificialFaceFields.ofOverlapPairingData D hactive hpieces hterm

/-- Constructor from overlap-pairing data and pointwise term alignment. -/
def ofOverlapPairingDataBoundaryTerm
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D : ArtificialFaceOverlapPairingData M Unit Face FaceDimension Geometry)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.interiorPieces x ->
          measureLocalization.interiorBoundaryTerm x q =
            D.toArtificialFacePairingData.interiorBoundaryTerm x q) :
    M8NaturalArtificialFaceData I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  ofFields <|
    M8ArtificialFaceFields.ofOverlapPairingDataBoundaryTerm D hactive hpieces
      hterm

/-- Constructor from adjacent selected-face data and a global term-family equality. -/
def ofAdjacentSelectedFacesData
    {Face : Type f} {Geometry : Type g}
    (D : AdjacentSelectedFacesData I omega M Unit Face Geometry)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      (fun x q =>
        projectInteriorBoundaryIntegral I (D.sourceChart x q)
          (D.targetChart x q) omega (D.lowerCorner x q)
          (D.upperCorner x q)) =
        measureLocalization.interiorBoundaryTerm) :
    M8NaturalArtificialFaceData I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  ofFields <|
    M8ArtificialFaceFields.ofAdjacentSelectedFacesData D hactive hpieces hterm

/-- Constructor from adjacent selected-face data and pointwise term alignment. -/
def ofAdjacentSelectedFacesDataBoundaryTerm
    {Face : Type f} {Geometry : Type g}
    (D : AdjacentSelectedFacesData I omega M Unit Face Geometry)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.interiorPieces x ->
          measureLocalization.interiorBoundaryTerm x q =
            projectInteriorBoundaryIntegral I (D.sourceChart x q)
              (D.targetChart x q) omega (D.lowerCorner x q)
              (D.upperCorner x q)) :
    M8NaturalArtificialFaceData I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  ofFields <|
    M8ArtificialFaceFields.ofAdjacentSelectedFacesDataBoundaryTerm D hactive
      hpieces hterm

end M8NaturalArtificialFaceData

end ArtificialFaceNaturalToM8

end Stokes

end
