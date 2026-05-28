import Stokes.Global.ArtificialFaceToM8
import Stokes.Global.ArtificialFacePairingToM8
import Stokes.Global.ArtificialFaceSupportZeroToM8

/-!
# Natural compact-support artificial-face builder

This file is a thin compact-support-facing adapter for the existing
artificial-face exits:

* raw `ArtificialFaceResolvedData` through `ArtificialFaceToM8`;
* selected support-zero data through `ArtificialFaceSupportZeroToM8`;
* overlap and adjacent-face pairing data through `ArtificialFacePairingToM8`.

The real support-zero or pairing geometry remains explicit input to those
routes.  This module only packages the resulting M8 artificial-face fields and
the compact-support-facing resolved artificial-face data.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section ArtificialFaceNaturalBuilder

universe u w b f d g

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

/--
Compact-support-facing artificial-face builder.

The measure package fixes the M8 localized artificial-boundary term.  The
builder stores the already aligned `M8ArtificialFaceFields`, then projects it
either as those M8 fields or as the
`M8CompactSupportArtificialFaceResolvedData` consumed by the compact-support
M8 statement.
-/
structure NaturalCompactSupportArtificialFaceBuilderData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureResolved :
      M8CompactSupportMeasureResolvedData I omega selectedPartition
        targetImages) where
  /-- Artificial-face cancellation already aligned with the M8 measure fields. -/
  artificial :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureResolved.measureLocalization

namespace NaturalCompactSupportArtificialFaceBuilderData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureResolved :
  M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages}

/-- Project the builder to the M8 artificial-face field package. -/
def toM8ArtificialFaceFields
    (D :
      NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureResolved.measureLocalization :=
  D.artificial

/-- Project the builder to the compact-support-facing resolved package. -/
def toCompactSupportArtificialFaceResolvedData
    (D :
      NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved where
  artificialFaces := D.artificial.artificialFaces
  artificialFaces_active := D.artificial.artificialFaces_active
  artificialFaces_pieces := D.artificial.artificialFaces_pieces
  artificialFaces_term := D.artificial.artificialFaces_term

@[simp]
theorem toM8ArtificialFaceFields_eq
    (D :
      NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    D.toM8ArtificialFaceFields = D.artificial :=
  rfl

@[simp]
theorem toCompactSupportArtificialFaceResolvedData_artificialFaces
    (D :
      NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    D.toCompactSupportArtificialFaceResolvedData.artificialFaces =
      D.artificial.artificialFaces :=
  rfl

@[simp]
theorem toCompactSupportArtificialFaceResolvedData_active
    (D :
      NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    D.toCompactSupportArtificialFaceResolvedData.artificialFaces.activeCharts =
      selectedPartition.active :=
  D.toCompactSupportArtificialFaceResolvedData.artificialFaces_active

@[simp]
theorem toCompactSupportArtificialFaceResolvedData_pieces
    (D :
      NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    D.toCompactSupportArtificialFaceResolvedData.artificialFaces.interiorPieces =
      fun _ : M => ({()} : Finset Unit) :=
  D.toCompactSupportArtificialFaceResolvedData.artificialFaces_pieces

@[simp]
theorem toCompactSupportArtificialFaceResolvedData_term
    (D :
      NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    D.toCompactSupportArtificialFaceResolvedData.artificialFaces.interiorBoundaryTerm =
      measureResolved.measureLocalization.interiorBoundaryTerm :=
  D.toCompactSupportArtificialFaceResolvedData.artificialFaces_term

/-- Build the natural artificial-face builder from an M8 field package. -/
def ofFields
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
        targetImages measureResolved.measureLocalization) :
    NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
      selectedPartition targetImages measureResolved where
  artificial := artificial

@[simp]
theorem ofFields_toM8ArtificialFaceFields
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
        targetImages measureResolved.measureLocalization) :
    (ofFields (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      (measureResolved := measureResolved) artificial).toM8ArtificialFaceFields =
        artificial :=
  rfl

/--
Builder constructor from already resolved artificial-face data.

This is the direct wrapper around `M8ArtificialFaceFields.ofResolved`; the
three alignment equalities remain explicit.
-/
def ofResolved
    (artificialFaces : ArtificialFaceResolvedData M Unit)
    (artificialFaces_active :
      artificialFaces.activeCharts = selectedPartition.active)
    (artificialFaces_pieces :
      artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (artificialFaces_term :
      artificialFaces.interiorBoundaryTerm =
        measureResolved.measureLocalization.interiorBoundaryTerm) :
    NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  ofFields
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureResolved := measureResolved)
    (M8ArtificialFaceFields.ofResolved
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      (measureLocalization := measureResolved.measureLocalization)
      artificialFaces artificialFaces_active artificialFaces_pieces
      artificialFaces_term)

/-- Builder constructor from selected support-zero data. -/
def ofSupportZeroData
    (D :
      M8ArtificialFaceSupportZeroData I omega selectedPartition targetImages
        measureResolved.measureLocalization) :
    NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  ofFields
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureResolved := measureResolved)
    D.toM8ArtificialFaceFields

/--
Builder constructor from selected support-zero local Stokes data.

The strict support containment and term alignment are the real geometric
inputs and stay visible here.
-/
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
    NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  ofSupportZeroData
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureResolved := measureResolved)
    (M8ArtificialFaceSupportZeroData.mk localStokesData
      support_subset_interiorBox interiorBoundaryTerm_eq)

/-- Builder constructor from overlap-pairing data with global term alignment. -/
def ofOverlapPairingData
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D : ArtificialFaceOverlapPairingData M Unit Face FaceDimension Geometry)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      D.toArtificialFacePairingData.interiorBoundaryTerm =
        measureResolved.measureLocalization.interiorBoundaryTerm) :
    NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  ofFields
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureResolved := measureResolved)
    (M8ArtificialFaceFields.ofOverlapPairingData
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      (measureLocalization := measureResolved.measureLocalization)
      D hactive hpieces hterm)

/--
Builder constructor from overlap-pairing data for the M8 localized boundary
term.
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
          measureResolved.measureLocalization.interiorBoundaryTerm x q =
            D.toArtificialFacePairingData.interiorBoundaryTerm x q) :
    NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  ofFields
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureResolved := measureResolved)
    (M8ArtificialFaceFields.ofOverlapPairingDataBoundaryTerm
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      (measureLocalization := measureResolved.measureLocalization)
      D hactive hpieces hterm)

/-- Builder constructor from adjacent selected-face data with global term alignment. -/
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
        measureResolved.measureLocalization.interiorBoundaryTerm) :
    NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  ofFields
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureResolved := measureResolved)
    (M8ArtificialFaceFields.ofAdjacentSelectedFacesData
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      (measureLocalization := measureResolved.measureLocalization)
      D hactive hpieces hterm)

/--
Builder constructor from adjacent selected-face data for the M8 localized
boundary term.
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
          measureResolved.measureLocalization.interiorBoundaryTerm x q =
            projectInteriorBoundaryIntegral I (D.sourceChart x q)
              (D.targetChart x q) omega (D.lowerCorner x q)
              (D.upperCorner x q)) :
    NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
      selectedPartition targetImages measureResolved :=
  ofFields
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureResolved := measureResolved)
    (M8ArtificialFaceFields.ofAdjacentSelectedFacesDataBoundaryTerm
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      (measureLocalization := measureResolved.measureLocalization)
      D hactive hpieces hterm)

end NaturalCompactSupportArtificialFaceBuilderData

namespace M8ArtificialFaceFields

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureResolved :
  M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages}

/-- Forget the natural compact-support artificial-face builder to M8 fields. -/
def ofNaturalCompactSupportBuilder
    (D :
      NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureResolved.measureLocalization :=
  D.toM8ArtificialFaceFields

@[simp]
theorem ofNaturalCompactSupportBuilder_artificialFaces
    (D :
      NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    (ofNaturalCompactSupportBuilder
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      (measureResolved := measureResolved) D).artificialFaces =
        D.artificial.artificialFaces :=
  rfl

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
Forget the natural compact-support artificial-face builder to the resolved
compact-support package.
-/
def ofNaturalBuilder
    (D :
      NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  D.toCompactSupportArtificialFaceResolvedData

/-- Compact-support resolved package from M8 artificial-face fields. -/
def ofM8ArtificialFaceFields
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
        targetImages measureResolved.measureLocalization) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  (NaturalCompactSupportArtificialFaceBuilderData.ofFields
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureResolved := measureResolved) artificial)
    |>.toCompactSupportArtificialFaceResolvedData

/-- Compact-support resolved package from already resolved artificial-face data. -/
def ofResolved
    (artificialFaces : ArtificialFaceResolvedData M Unit)
    (artificialFaces_active :
      artificialFaces.activeCharts = selectedPartition.active)
    (artificialFaces_pieces :
      artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (artificialFaces_term :
      artificialFaces.interiorBoundaryTerm =
        measureResolved.measureLocalization.interiorBoundaryTerm) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  (NaturalCompactSupportArtificialFaceBuilderData.ofResolved
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureResolved := measureResolved)
    artificialFaces artificialFaces_active artificialFaces_pieces
    artificialFaces_term)
    |>.toCompactSupportArtificialFaceResolvedData

/-- Compact-support resolved package from selected support-zero data. -/
def ofSupportZeroData
    (D :
      M8ArtificialFaceSupportZeroData I omega selectedPartition targetImages
        measureResolved.measureLocalization) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  (NaturalCompactSupportArtificialFaceBuilderData.ofSupportZeroData
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureResolved := measureResolved) D)
    |>.toCompactSupportArtificialFaceResolvedData

/-- Compact-support resolved package from overlap-pairing data. -/
def ofOverlapPairingData
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D : ArtificialFaceOverlapPairingData M Unit Face FaceDimension Geometry)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      D.toArtificialFacePairingData.interiorBoundaryTerm =
        measureResolved.measureLocalization.interiorBoundaryTerm) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  (NaturalCompactSupportArtificialFaceBuilderData.ofOverlapPairingData
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureResolved := measureResolved)
    D hactive hpieces hterm)
    |>.toCompactSupportArtificialFaceResolvedData

/-- Compact-support resolved package from overlap-pairing boundary-term data. -/
def ofOverlapPairingDataBoundaryTerm
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D : ArtificialFaceOverlapPairingData M Unit Face FaceDimension Geometry)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.interiorPieces x ->
          measureResolved.measureLocalization.interiorBoundaryTerm x q =
            D.toArtificialFacePairingData.interiorBoundaryTerm x q) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  (NaturalCompactSupportArtificialFaceBuilderData.ofOverlapPairingDataBoundaryTerm
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureResolved := measureResolved)
    D hactive hpieces hterm)
    |>.toCompactSupportArtificialFaceResolvedData

/-- Compact-support resolved package from adjacent selected-face data. -/
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
        measureResolved.measureLocalization.interiorBoundaryTerm) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  (NaturalCompactSupportArtificialFaceBuilderData.ofAdjacentSelectedFacesData
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureResolved := measureResolved)
    D hactive hpieces hterm)
    |>.toCompactSupportArtificialFaceResolvedData

/--
Compact-support resolved package from adjacent selected-face boundary-term
data.
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
          measureResolved.measureLocalization.interiorBoundaryTerm x q =
            projectInteriorBoundaryIntegral I (D.sourceChart x q)
              (D.targetChart x q) omega (D.lowerCorner x q)
              (D.upperCorner x q)) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  (NaturalCompactSupportArtificialFaceBuilderData.ofAdjacentSelectedFacesDataBoundaryTerm
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureResolved := measureResolved)
    D hactive hpieces hterm)
    |>.toCompactSupportArtificialFaceResolvedData

@[simp]
theorem ofNaturalBuilder_artificialFaces
    (D :
      NaturalCompactSupportArtificialFaceBuilderData I omega BoundaryPiece
        selectedPartition targetImages measureResolved) :
    (ofNaturalBuilder
      (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      (measureResolved := measureResolved) D).artificialFaces =
        D.artificial.artificialFaces :=
  rfl

end M8CompactSupportArtificialFaceResolvedData

end ArtificialFaceNaturalBuilder

end Stokes

end
