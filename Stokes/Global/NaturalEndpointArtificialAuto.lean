import Stokes.Global.NaturalCompactSupportEndpointAdapters
import Stokes.Global.CompactSupportBoxBufferBuilder
import Stokes.Global.ArtificialFaceAdjacencyToM8

/-!
# Artificial-face auto adapters for the compact-support endpoint

This module keeps the endpoint bus unchanged, but removes the need for callers
to manually assemble the endpoint field
`artificial : M8ArtificialFaceFields ...`.

Starting from the audited endpoint base sources, the constructors below build
that field from the existing artificial-face exits:

* strict support / compact-support box buffers;
* localized coefficient buffers;
* selected support-zero geometry;
* overlap-pairing cancellation data;
* adjacent selected-face cancellation data.

No new cancellation theorem is proved here.  The file only connects the
endpoint's assembled M8 measure-localization data to the already proved
artificial-face support-zero and pairing constructors.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalEndpointArtificialAuto

universe u w b ei eb f d g

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

namespace NaturalCompactSupportEndpointAutoSelectedBaseSources

variable
    (S :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)

/-- The M8 measure-localization data assembled by the endpoint base sources. -/
abbrev endpointMeasureLocalization :
    M8MeasureLocalizationData I omega S.toBaseInput.selectedPartition
      S.toBaseInput.targetImageInput.targetImages :=
  S.toBaseInput.separatedMeasure.toM8MeasureLocalizationData

/--
Endpoint artificial fields generated from a compact-support box buffer for the
assembled endpoint measure data.
-/
def artificialOfCompactSupportBoxBuffer
    (buffer :
      CompactSupportBoxBuffer I omega S.toBaseInput.selectedPartition
        S.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization) :
    M8ArtificialFaceFields I omega BoundaryPiece
      S.toBaseInput.selectedPartition
      S.toBaseInput.targetImageInput.targetImages
      S.endpointMeasureLocalization :=
  buffer.toM8ArtificialFaceFields

@[simp]
theorem artificialOfCompactSupportBoxBuffer_artificialFaces
    (buffer :
      CompactSupportBoxBuffer I omega S.toBaseInput.selectedPartition
        S.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization) :
    (S.artificialOfCompactSupportBoxBuffer buffer).artificialFaces =
      buffer.toM8ArtificialFaceFields.artificialFaces :=
  rfl

/--
Endpoint artificial fields generated directly from strict support of the
localized interior representatives in the endpoint measure localization.
-/
def artificialOfStrictCompactSupportBoxBuffer
    (strictSupport_subset_interiorBox :
      forall x, x ∈ S.toBaseInput.selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (S.endpointMeasureLocalization.localizedInterior.piece x).sourceChart
              (S.endpointMeasureLocalization.localizedInterior.piece x).targetChart
              (S.endpointMeasureLocalization.localizedInterior.piece x).localizedForm) ⊆
          boxInteriorSupportBox
            (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner
            (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner) :
    M8ArtificialFaceFields I omega BoundaryPiece
      S.toBaseInput.selectedPartition
      S.toBaseInput.targetImageInput.targetImages
      S.endpointMeasureLocalization :=
  M8ArtificialFaceFields.ofStrictCompactSupportBoxBuffer
    (BoundaryPiece := BoundaryPiece)
    (selectedPartition := S.toBaseInput.selectedPartition)
    (targetImages := S.toBaseInput.targetImageInput.targetImages)
    (measureLocalization := S.endpointMeasureLocalization)
    strictSupport_subset_interiorBox

@[simp]
theorem artificialOfStrictCompactSupportBoxBuffer_active
    (strictSupport_subset_interiorBox :
      forall x, x ∈ S.toBaseInput.selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (S.endpointMeasureLocalization.localizedInterior.piece x).sourceChart
              (S.endpointMeasureLocalization.localizedInterior.piece x).targetChart
              (S.endpointMeasureLocalization.localizedInterior.piece x).localizedForm) ⊆
          boxInteriorSupportBox
            (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner
            (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner) :
    (S.artificialOfStrictCompactSupportBoxBuffer
      strictSupport_subset_interiorBox).artificialFaces.activeCharts =
        S.toBaseInput.selectedPartition.active :=
  M8ArtificialFaceFields.ofStrictCompactSupportBoxBuffer_active
    (BoundaryPiece := BoundaryPiece)
    (selectedPartition := S.toBaseInput.selectedPartition)
    (targetImages := S.toBaseInput.targetImageInput.targetImages)
    (measureLocalization := S.endpointMeasureLocalization)
    strictSupport_subset_interiorBox

/--
Endpoint artificial fields generated from strict coefficient support of the
localized interior pieces in the endpoint measure localization.
-/
def artificialOfLocalizedInteriorCoefficientBuffer
    (coefficient_tsupport_subset_interiorBox :
      forall x, x ∈ S.toBaseInput.selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (S.endpointMeasureLocalization.localizedInterior.piece x).sourceChart
              (S.endpointMeasureLocalization.localizedInterior.piece x).targetChart
              (S.endpointMeasureLocalization.localizedInterior.coefficient x)) ⊆
          boxInteriorSupportBox
            (S.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner
            (S.endpointMeasureLocalization.localizedInterior.piece x).upperCorner) :
    M8ArtificialFaceFields I omega BoundaryPiece
      S.toBaseInput.selectedPartition
      S.toBaseInput.targetImageInput.targetImages
      S.endpointMeasureLocalization :=
  M8ArtificialFaceFields.ofLocalizedInteriorCoefficientBuffer
    (BoundaryPiece := BoundaryPiece)
    (selectedPartition := S.toBaseInput.selectedPartition)
    (targetImages := S.toBaseInput.targetImageInput.targetImages)
    (measureLocalization := S.endpointMeasureLocalization)
    coefficient_tsupport_subset_interiorBox

/--
Endpoint artificial fields generated from the selected support-zero geometry
record for the assembled endpoint measure data.
-/
def artificialOfSelectedPartitionSupportZeroGeometry
    (D :
      SelectedPartitionSupportZeroGeometry I omega S.toBaseInput.selectedPartition
        S.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization) :
    M8ArtificialFaceFields I omega BoundaryPiece
      S.toBaseInput.selectedPartition
      S.toBaseInput.targetImageInput.targetImages
      S.endpointMeasureLocalization :=
  D.toM8ArtificialFaceFields

/--
Endpoint artificial fields generated from overlap-pairing data whose recorded
boundary terms agree pointwise with the endpoint's assembled M8 term.
-/
def artificialOfOverlapPairingDataBoundaryTerm
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D : ArtificialFaceOverlapPairingData M Unit Face FaceDimension Geometry)
    (hactive : D.activeCharts = S.toBaseInput.selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.interiorPieces x ->
          S.endpointMeasureLocalization.interiorBoundaryTerm x q =
            D.toArtificialFacePairingData.interiorBoundaryTerm x q) :
    M8ArtificialFaceFields I omega BoundaryPiece
      S.toBaseInput.selectedPartition
      S.toBaseInput.targetImageInput.targetImages
      S.endpointMeasureLocalization :=
  M8ArtificialFaceFields.ofOverlapPairingDataBoundaryTerm
    (BoundaryPiece := BoundaryPiece)
    (selectedPartition := S.toBaseInput.selectedPartition)
    (targetImages := S.toBaseInput.targetImageInput.targetImages)
    (measureLocalization := S.endpointMeasureLocalization)
    D hactive hpieces hterm

@[simp]
theorem artificialOfOverlapPairingDataBoundaryTerm_artificialFaces
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D : ArtificialFaceOverlapPairingData M Unit Face FaceDimension Geometry)
    (hactive : D.activeCharts = S.toBaseInput.selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.interiorPieces x ->
          S.endpointMeasureLocalization.interiorBoundaryTerm x q =
            D.toArtificialFacePairingData.interiorBoundaryTerm x q) :
    (S.artificialOfOverlapPairingDataBoundaryTerm
      D hactive hpieces hterm).artificialFaces =
        ArtificialFaceResolvedData.ofOverlapPairingBoundaryTerm D
          S.endpointMeasureLocalization.interiorBoundaryTerm hterm :=
  rfl

/--
Endpoint artificial fields generated from adjacent selected-face data whose
project-local boundary terms agree pointwise with the endpoint's assembled M8
term.
-/
def artificialOfAdjacentSelectedFacesDataBoundaryTerm
    {Face : Type f} {Geometry : Type g}
    (D : AdjacentSelectedFacesData I omega M Unit Face Geometry)
    (hactive : D.activeCharts = S.toBaseInput.selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.interiorPieces x ->
          S.endpointMeasureLocalization.interiorBoundaryTerm x q =
            projectInteriorBoundaryIntegral I (D.sourceChart x q)
              (D.targetChart x q) omega (D.lowerCorner x q)
              (D.upperCorner x q)) :
    M8ArtificialFaceFields I omega BoundaryPiece
      S.toBaseInput.selectedPartition
      S.toBaseInput.targetImageInput.targetImages
      S.endpointMeasureLocalization :=
  M8ArtificialFaceFields.ofAdjacentSelectedFacesDataBoundaryTerm
    (BoundaryPiece := BoundaryPiece)
    (selectedPartition := S.toBaseInput.selectedPartition)
    (targetImages := S.toBaseInput.targetImageInput.targetImages)
    (measureLocalization := S.endpointMeasureLocalization)
    D hactive hpieces hterm

@[simp]
theorem artificialOfAdjacentSelectedFacesDataBoundaryTerm_artificialFaces
    {Face : Type f} {Geometry : Type g}
    (D : AdjacentSelectedFacesData I omega M Unit Face Geometry)
    (hactive : D.activeCharts = S.toBaseInput.selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.interiorPieces x ->
          S.endpointMeasureLocalization.interiorBoundaryTerm x q =
            projectInteriorBoundaryIntegral I (D.sourceChart x q)
              (D.targetChart x q) omega (D.lowerCorner x q)
              (D.upperCorner x q)) :
    (S.artificialOfAdjacentSelectedFacesDataBoundaryTerm
      D hactive hpieces hterm).artificialFaces =
        ArtificialFaceResolvedData.ofAdjacentSelectedFacesBoundaryTerm D
          S.endpointMeasureLocalization.interiorBoundaryTerm hterm :=
  rfl

/--
Endpoint artificial fields from selected-partition adjacent-face fields.

This is the fully concrete adjacency route: the face indices, pairing, opposite
coordinate faces, equal geometric faces, equal unsigned terms, and fixed-point
zero terms are passed to the existing selected-partition adjacency builder.
-/
def artificialOfSelectedAdjacentFaces
    {Face : Type f} {Geometry : Type g}
    (faceIndices : M -> Finset Face)
    (coordinateFace : M -> Face -> ArtificialCoordinateFace n)
    (geometricFace : M -> Face -> Geometry)
    (unsignedFaceTerm : M -> Face -> Real)
    (boundaryTerm_eq_faceSum :
      forall i, i ∈ S.toBaseInput.selectedPartition.active ->
        projectInteriorBoundaryIntegral I i i omega
            (S.toBaseInput.selectedPartition.lower i)
            (S.toBaseInput.selectedPartition.upper i) =
          Finset.sum (faceIndices i) fun f =>
            (coordinateFace i f).sign * unsignedFaceTerm i f)
    (pair : ArtificialFaceIndex M Unit Face -> ArtificialFaceIndex M Unit Face)
    (pair_mem :
      forall r,
        r ∈ artificialFaceIndexSet S.toBaseInput.selectedPartition.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          pair r ∈
            artificialFaceIndexSet S.toBaseInput.selectedPartition.active
              (fun _ : M => ({()} : Finset Unit))
              (fun i _ => faceIndices i))
    (pair_involutive :
      forall r,
        r ∈ artificialFaceIndexSet S.toBaseInput.selectedPartition.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          pair (pair r) = r)
    (paired_coordinateFace_opposite :
      forall r,
        r ∈ artificialFaceIndexSet S.toBaseInput.selectedPartition.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          coordinateFace (pair r).1.1 (pair r).2 =
            (coordinateFace r.1.1 r.2).opposite)
    (paired_geometricFace_eq :
      forall r,
        r ∈ artificialFaceIndexSet S.toBaseInput.selectedPartition.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          geometricFace r.1.1 r.2 = geometricFace (pair r).1.1 (pair r).2)
    (paired_unsignedFaceTerm_eq :
      forall r,
        r ∈ artificialFaceIndexSet S.toBaseInput.selectedPartition.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          artificialFaceTerm (fun i _ f => unsignedFaceTerm i f) r =
            artificialFaceTerm (fun i _ f => unsignedFaceTerm i f) (pair r))
    (fixed_terms_zero :
      forall r,
        r ∈ artificialFaceIndexSet S.toBaseInput.selectedPartition.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          pair r = r ->
            artificialFaceTerm
              (fun i _ f => (coordinateFace i f).sign * unsignedFaceTerm i f)
              r = 0)
    (hterm :
      forall x, x ∈ S.toBaseInput.selectedPartition.active ->
        S.endpointMeasureLocalization.interiorBoundaryTerm x () =
          projectInteriorBoundaryIntegral I x x omega
            (S.toBaseInput.selectedPartition.lower x)
            (S.toBaseInput.selectedPartition.upper x)) :
    M8ArtificialFaceFields I omega BoundaryPiece
      S.toBaseInput.selectedPartition
      S.toBaseInput.targetImageInput.targetImages
      S.endpointMeasureLocalization :=
  S.toBaseInput.selectedPartition.toM8ArtificialFaceFieldsOfAdjacentFaces
    (BoundaryPiece := BoundaryPiece)
    (selectedPartition := S.toBaseInput.selectedPartition)
    (targetImages := S.toBaseInput.targetImageInput.targetImages)
    (measureLocalization := S.endpointMeasureLocalization)
    rfl faceIndices coordinateFace geometricFace unsignedFaceTerm
    boundaryTerm_eq_faceSum pair pair_mem pair_involutive
    paired_coordinateFace_opposite paired_geometricFace_eq
    paired_unsignedFaceTerm_eq fixed_terms_zero hterm

end NaturalCompactSupportEndpointAutoSelectedBaseSources

namespace NaturalCompactSupportEndpointAutoSelectedSources

/--
Build full endpoint sources from base sources and a compact-support box buffer,
without asking the caller for `M8ArtificialFaceFields`.
-/
def ofBaseAndCompactSupportBoxBuffer
    (base :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)
    (buffer :
      CompactSupportBoxBuffer I omega base.toBaseInput.selectedPartition
        base.toBaseInput.targetImageInput.targetImages
        base.endpointMeasureLocalization) :
    NaturalCompactSupportEndpointAutoSelectedSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu where
  base := base
  artificial := base.artificialOfCompactSupportBoxBuffer buffer

@[simp]
theorem ofBaseAndCompactSupportBoxBuffer_artificial
    (base :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)
    (buffer :
      CompactSupportBoxBuffer I omega base.toBaseInput.selectedPartition
        base.toBaseInput.targetImageInput.targetImages
        base.endpointMeasureLocalization) :
    (ofBaseAndCompactSupportBoxBuffer base buffer).artificial =
      base.artificialOfCompactSupportBoxBuffer buffer :=
  rfl

/--
Build full endpoint sources directly from strict support of the localized
interior representatives in the endpoint measure localization.
-/
def ofBaseAndStrictCompactSupportBoxBuffer
    (base :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)
    (strictSupport_subset_interiorBox :
      forall x, x ∈ base.toBaseInput.selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (base.endpointMeasureLocalization.localizedInterior.piece x).sourceChart
              (base.endpointMeasureLocalization.localizedInterior.piece x).targetChart
              (base.endpointMeasureLocalization.localizedInterior.piece x).localizedForm) ⊆
          boxInteriorSupportBox
            (base.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner
            (base.endpointMeasureLocalization.localizedInterior.piece x).upperCorner) :
    NaturalCompactSupportEndpointAutoSelectedSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu where
  base := base
  artificial :=
    base.artificialOfStrictCompactSupportBoxBuffer
      strictSupport_subset_interiorBox

/--
Build full endpoint sources from strict coefficient support of localized
interior pieces.
-/
def ofBaseAndLocalizedInteriorCoefficientBuffer
    (base :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)
    (coefficient_tsupport_subset_interiorBox :
      forall x, x ∈ base.toBaseInput.selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (base.endpointMeasureLocalization.localizedInterior.piece x).sourceChart
              (base.endpointMeasureLocalization.localizedInterior.piece x).targetChart
              (base.endpointMeasureLocalization.localizedInterior.coefficient x)) ⊆
          boxInteriorSupportBox
            (base.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner
            (base.endpointMeasureLocalization.localizedInterior.piece x).upperCorner) :
    NaturalCompactSupportEndpointAutoSelectedSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu where
  base := base
  artificial :=
    base.artificialOfLocalizedInteriorCoefficientBuffer
      coefficient_tsupport_subset_interiorBox

/-- Build full endpoint sources from selected support-zero geometry. -/
def ofBaseAndSelectedPartitionSupportZeroGeometry
    (base :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)
    (D :
      SelectedPartitionSupportZeroGeometry I omega base.toBaseInput.selectedPartition
        base.toBaseInput.targetImageInput.targetImages
        base.endpointMeasureLocalization) :
    NaturalCompactSupportEndpointAutoSelectedSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu where
  base := base
  artificial := base.artificialOfSelectedPartitionSupportZeroGeometry D

/-- Build full endpoint sources from overlap-pairing cancellation data. -/
def ofBaseAndOverlapPairingDataBoundaryTerm
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (base :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)
    (D : ArtificialFaceOverlapPairingData M Unit Face FaceDimension Geometry)
    (hactive : D.activeCharts = base.toBaseInput.selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.interiorPieces x ->
          base.endpointMeasureLocalization.interiorBoundaryTerm x q =
            D.toArtificialFacePairingData.interiorBoundaryTerm x q) :
    NaturalCompactSupportEndpointAutoSelectedSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu where
  base := base
  artificial :=
    base.artificialOfOverlapPairingDataBoundaryTerm D hactive hpieces hterm

/-- Build full endpoint sources from adjacent selected-face cancellation data. -/
def ofBaseAndAdjacentSelectedFacesDataBoundaryTerm
    {Face : Type f} {Geometry : Type g}
    (base :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)
    (D : AdjacentSelectedFacesData I omega M Unit Face Geometry)
    (hactive : D.activeCharts = base.toBaseInput.selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.interiorPieces x ->
          base.endpointMeasureLocalization.interiorBoundaryTerm x q =
            projectInteriorBoundaryIntegral I (D.sourceChart x q)
              (D.targetChart x q) omega (D.lowerCorner x q)
              (D.upperCorner x q)) :
    NaturalCompactSupportEndpointAutoSelectedSources
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu where
  base := base
  artificial :=
    base.artificialOfAdjacentSelectedFacesDataBoundaryTerm
      D hactive hpieces hterm

/--
Endpoint theorem from strict support data, with artificial-face fields built
internally.
-/
theorem stokes_ofStrictCompactSupportBoxBuffer
    (base :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)
    (strictSupport_subset_interiorBox :
      forall x, x ∈ base.toBaseInput.selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (base.endpointMeasureLocalization.localizedInterior.piece x).sourceChart
              (base.endpointMeasureLocalization.localizedInterior.piece x).targetChart
              (base.endpointMeasureLocalization.localizedInterior.piece x).localizedForm) ⊆
          boxInteriorSupportBox
            (base.endpointMeasureLocalization.localizedInterior.piece x).lowerCorner
            (base.endpointMeasureLocalization.localizedInterior.piece x).upperCorner) :
    base.endpointMeasureLocalization.bulkMeasureIntegral =
      base.endpointMeasureLocalization.boundaryMeasureIntegral :=
  (ofBaseAndStrictCompactSupportBoxBuffer base
    strictSupport_subset_interiorBox).stokes

/--
Endpoint theorem from adjacent selected-face cancellation data, with
artificial-face fields built internally.
-/
theorem stokes_ofAdjacentSelectedFacesDataBoundaryTerm
    {Face : Type f} {Geometry : Type g}
    (base :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)
    (D : AdjacentSelectedFacesData I omega M Unit Face Geometry)
    (hactive : D.activeCharts = base.toBaseInput.selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.interiorPieces x ->
          base.endpointMeasureLocalization.interiorBoundaryTerm x q =
            projectInteriorBoundaryIntegral I (D.sourceChart x q)
              (D.targetChart x q) omega (D.lowerCorner x q)
              (D.upperCorner x q)) :
    base.endpointMeasureLocalization.bulkMeasureIntegral =
      base.endpointMeasureLocalization.boundaryMeasureIntegral :=
  (ofBaseAndAdjacentSelectedFacesDataBoundaryTerm
    base D hactive hpieces hterm).stokes

/--
Endpoint theorem from overlap-pairing cancellation data, with artificial-face
fields built internally.
-/
theorem stokes_ofOverlapPairingDataBoundaryTerm
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (base :
      NaturalCompactSupportEndpointAutoSelectedBaseSources
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)
    (D : ArtificialFaceOverlapPairingData M Unit Face FaceDimension Geometry)
    (hactive : D.activeCharts = base.toBaseInput.selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      forall x, x ∈ D.activeCharts ->
        forall q, q ∈ D.interiorPieces x ->
          base.endpointMeasureLocalization.interiorBoundaryTerm x q =
            D.toArtificialFacePairingData.interiorBoundaryTerm x q) :
    base.endpointMeasureLocalization.bulkMeasureIntegral =
      base.endpointMeasureLocalization.boundaryMeasureIntegral :=
  (ofBaseAndOverlapPairingDataBoundaryTerm
    base D hactive hpieces hterm).stokes

end NaturalCompactSupportEndpointAutoSelectedSources

end NaturalEndpointArtificialAuto

end Stokes

end
