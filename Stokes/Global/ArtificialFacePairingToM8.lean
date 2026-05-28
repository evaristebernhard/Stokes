import Stokes.Global.ArtificialFaceToM8

/-!
# Artificial-face pairing data for M8

This file provides direct M8-facing entry points for the two pairing routes
used to resolve artificial interior-boundary terms:

* overlap pairings of signed artificial faces;
* adjacent selected faces of local chart boxes.

The proofs are bookkeeping only.  The cancellation theorems are already proved
in the artificial-face pairing layers and exposed through
`M8ArtificialFaceFields`.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section ArtificialFacePairingToM8

universe u w b f d g

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Compatibility spelling for adjacent selected artificial-face data.

The core development names this structure `AdjacentSelectedFacesData`; this
alias gives downstream M8 constructors a name parallel to
`ArtificialFaceOverlapPairingData`.
-/
abbrev ArtificialFaceAdjacentSelectedFacesData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (Chart : Type w) (Piece : Type) (Face : Type f)
    (Geometry : Type g) :=
  AdjacentSelectedFacesData I omega Chart Piece Face Geometry

namespace M8ArtificialFaceFields

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {BoundaryPiece : Type b}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/--
Direct M8 constructor from overlap-pairing data whose recorded face-sum
boundary term is globally identified with the M8 interior-boundary term.
-/
def ofOverlapPairingData
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D : ArtificialFaceOverlapPairingData M Unit Face FaceDimension Geometry)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      D.toArtificialFacePairingData.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  ofOverlapPairing D hactive hpieces hterm

/--
Direct M8 constructor from overlap-pairing data for an external M8
interior-boundary term that agrees pointwise with the recorded face sums.
-/
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
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  ofOverlapPairingBoundaryTerm D hactive hpieces hterm

@[simp]
theorem ofOverlapPairingData_artificialFaces
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D : ArtificialFaceOverlapPairingData M Unit Face FaceDimension Geometry)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      D.toArtificialFacePairingData.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm) :
    (ofOverlapPairingData (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece) (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      (measureLocalization := measureLocalization)
      D hactive hpieces hterm).artificialFaces =
        ArtificialFaceResolvedData.ofOverlapPairing D :=
  rfl

@[simp]
theorem ofOverlapPairingDataBoundaryTerm_artificialFaces
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
    (ofOverlapPairingDataBoundaryTerm (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece) (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      (measureLocalization := measureLocalization)
      D hactive hpieces hterm).artificialFaces =
        ArtificialFaceResolvedData.ofOverlapPairingBoundaryTerm D
          measureLocalization.interiorBoundaryTerm hterm :=
  rfl

/--
Direct M8 constructor from adjacent selected-face data whose project-local
boundary term family is globally identified with the M8 interior-boundary term.
-/
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
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  ofAdjacentSelectedFaces D hactive hpieces hterm

/--
Direct M8 constructor from adjacent selected-face data for an external M8
interior-boundary term that agrees pointwise with the project-local boundary
terms.
-/
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
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  ofAdjacentSelectedFacesBoundaryTerm D hactive hpieces hterm

@[simp]
theorem ofAdjacentSelectedFacesData_artificialFaces
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
    (ofAdjacentSelectedFacesData (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece) (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      (measureLocalization := measureLocalization)
      D hactive hpieces hterm).artificialFaces =
        ArtificialFaceResolvedData.ofAdjacentSelectedFaces D :=
  rfl

@[simp]
theorem ofAdjacentSelectedFacesDataBoundaryTerm_artificialFaces
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
    (ofAdjacentSelectedFacesDataBoundaryTerm (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece) (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      (measureLocalization := measureLocalization)
      D hactive hpieces hterm).artificialFaces =
        ArtificialFaceResolvedData.ofAdjacentSelectedFacesBoundaryTerm D
          measureLocalization.interiorBoundaryTerm hterm :=
  rfl

end M8ArtificialFaceFields

namespace ArtificialFaceOverlapPairingData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {BoundaryPiece : Type b}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/--
Namespace method sending overlap-pairing data directly to the M8
artificial-face field package.
-/
def toM8ArtificialFaceFields
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D : ArtificialFaceOverlapPairingData M Unit Face FaceDimension Geometry)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      D.toArtificialFacePairingData.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  M8ArtificialFaceFields.ofOverlapPairingData D hactive hpieces hterm

/--
Namespace method for overlap-pairing data when the M8 term is supplied by a
pointwise equality to the recorded face sums.
-/
def toM8ArtificialFaceFieldsOfBoundaryTerm
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
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  M8ArtificialFaceFields.ofOverlapPairingDataBoundaryTerm D hactive hpieces
    hterm

end ArtificialFaceOverlapPairingData

namespace AdjacentSelectedFacesData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {BoundaryPiece : Type b}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/--
Namespace method sending adjacent selected-face data directly to the M8
artificial-face field package.
-/
def toM8ArtificialFaceFields
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
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  M8ArtificialFaceFields.ofAdjacentSelectedFacesData D hactive hpieces hterm

/--
Namespace method for adjacent selected-face data when the M8 term is supplied
by a pointwise equality to the project-local boundary terms.
-/
def toM8ArtificialFaceFieldsOfBoundaryTerm
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
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  M8ArtificialFaceFields.ofAdjacentSelectedFacesDataBoundaryTerm D hactive
    hpieces hterm

end AdjacentSelectedFacesData

end ArtificialFacePairingToM8

end Stokes

end
