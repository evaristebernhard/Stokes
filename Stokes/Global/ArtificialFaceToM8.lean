import Stokes.Global.M8Statement

/-!
# Artificial-face data for M8

This file is the M8-facing adapter for resolved artificial-face cancellation.
It packages the four `M8GlobalStokesInput.artificialFaces_*` fields together,
then supplies constructors from the already available artificial-face exits:

* pointwise/support-zero cancellation;
* overlap-pairing cancellation;
* adjacent-selected-face cancellation.

The constructions here are bookkeeping only.  The geometric and analytic work
stays in `ArtificialFaceFieldReduction` and its input modules.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section ArtificialFaceToM8

universe u w b f d g

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
The artificial-face part of an `M8GlobalStokesInput`.

This is exactly the resolved artificial-face package together with the three
alignment equalities required by `M8GlobalStokesInput`.  Keeping it separate
lets downstream constructors build the artificial-face fields in one step,
without restating the rest of the M8 input.
-/
structure M8ArtificialFaceFields {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages) where
  /-- Resolved artificial-face data for localized singleton interior pieces. -/
  artificialFaces : ArtificialFaceResolvedData M Unit
  /-- The resolved active charts are the selected partition active charts. -/
  artificialFaces_active :
    artificialFaces.activeCharts = selectedPartition.active
  /-- Each selected chart contributes a singleton interior piece. -/
  artificialFaces_pieces :
    artificialFaces.interiorPieces = fun _ : M => ({()} : Finset Unit)
  /-- The resolved artificial-boundary term is the M8 localized term. -/
  artificialFaces_term :
    artificialFaces.interiorBoundaryTerm =
      measureLocalization.interiorBoundaryTerm

namespace M8ArtificialFaceFields

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {BoundaryPiece : Type b}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/-- Build the M8 artificial-face fields from already resolved data. -/
def ofResolved
    (D : ArtificialFaceResolvedData M Unit)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      D.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization where
  artificialFaces := D
  artificialFaces_active := hactive
  artificialFaces_pieces := hpieces
  artificialFaces_term := hterm

@[simp]
theorem ofResolved_artificialFaces
    (D : ArtificialFaceResolvedData M Unit)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      D.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm) :
    (ofResolved (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      (measureLocalization := measureLocalization)
      D hactive hpieces hterm).artificialFaces = D :=
  rfl

/-- Build the M8 artificial-face fields from an existing cancellation package. -/
def ofCancellationData
    (C : ArtificialBoundaryCancellationData M Unit)
    (hactive : C.activeCharts = selectedPartition.active)
    (hpieces :
      C.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      C.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  ofResolved (ArtificialFaceResolvedData.ofCancellationData C)
    hactive hpieces hterm

/--
Pointwise-zero constructor for M8 artificial faces.

This is the direct target for a support-zero proof once it has been reduced to
the M8 localized artificial-boundary term.
-/
def ofBoundaryTermZero
    (hzero :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ ({()} : Finset Unit) ->
          measureLocalization.interiorBoundaryTerm x q = 0) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  ofResolved
    (ArtificialFaceResolvedData.of_forall_eq_zero selectedPartition.active
      (fun _ : M => ({()} : Finset Unit))
      measureLocalization.interiorBoundaryTerm hzero)
    rfl rfl rfl

/--
Support-zero constructor for M8 artificial faces.

The support-zero theorem may be proved using a local-Stokes data package whose
recorded artificial-boundary term is identified with the M8 localized term on
active singleton pieces.
-/
def ofInteriorSupportZeroBoundaryTerm
    (localStokesData : M -> Unit -> InteriorLocalStokesData I omega)
    (hsupp :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ ({()} : Finset Unit) ->
          tsupport
              (ManifoldForm.transitionPullbackInChart I
                (localStokesData x q).sourceChart
                (localStokesData x q).targetChart omega) ⊆
            boxInteriorSupportBox
              (localStokesData x q).lowerCorner
              (localStokesData x q).upperCorner)
    (hterm :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ ({()} : Finset Unit) ->
          measureLocalization.interiorBoundaryTerm x q =
            (localStokesData x q).artificialBoundaryTerm) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  ofBoundaryTermZero
    (by
      intro x hx q hq
      exact (hterm x hx q hq).trans
        ((localStokesData x q).artificialBoundaryTerm_eq_zero_of_tsupport_subset_interiorBox
          (hsupp x hx q hq)))

/--
Constructor from the existing fixed-form support-zero resolved-data exit.

Use this when the support-zero route has already produced an
`ArtificialFaceResolvedData` with the right term family.
-/
def ofInteriorSupportZeroResolved
    (localStokesData : M -> Unit -> InteriorLocalStokesData I omega)
    (hsupp :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ ({()} : Finset Unit) ->
          tsupport
              (ManifoldForm.transitionPullbackInChart I
                (localStokesData x q).sourceChart
                (localStokesData x q).targetChart omega) ⊆
            boxInteriorSupportBox
              (localStokesData x q).lowerCorner
              (localStokesData x q).upperCorner)
    (hterm :
      (fun x q => (localStokesData x q).artificialBoundaryTerm) =
        measureLocalization.interiorBoundaryTerm) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  ofResolved
    (ArtificialFaceResolvedData.ofInteriorSupportZero selectedPartition.active
      (fun _ : M => ({()} : Finset Unit)) localStokesData hsupp)
    rfl rfl hterm

/--
Overlap-pairing constructor for M8 artificial faces.

The overlap package supplies the cancellation.  The final argument identifies
its recorded face-sum boundary term with the M8 localized term on active
singleton pieces.
-/
def ofOverlapPairingBoundaryTerm
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D :
      ArtificialFaceOverlapPairingData M Unit Face FaceDimension Geometry)
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
  ofResolved
    (ArtificialFaceResolvedData.ofOverlapPairingBoundaryTerm D
      measureLocalization.interiorBoundaryTerm hterm)
    hactive hpieces rfl

/--
Overlap-pairing constructor when the resolved term family has already been
identified globally with the M8 localized term.
-/
def ofOverlapPairing
    {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}
    (D :
      ArtificialFaceOverlapPairingData M Unit Face FaceDimension Geometry)
    (hactive : D.activeCharts = selectedPartition.active)
    (hpieces :
      D.interiorPieces = fun _ : M => ({()} : Finset Unit))
    (hterm :
      D.toArtificialFacePairingData.interiorBoundaryTerm =
        measureLocalization.interiorBoundaryTerm) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  ofResolved (ArtificialFaceResolvedData.ofOverlapPairing D)
    hactive hpieces hterm

/--
Adjacent-selected-faces constructor for M8 artificial faces.

The adjacent-selected-face data cancels project-local artificial boundary
terms.  The final argument identifies those terms with the M8 localized
artificial-boundary term on active singleton pieces.
-/
def ofAdjacentSelectedFacesBoundaryTerm
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
  ofResolved
    (ArtificialFaceResolvedData.ofAdjacentSelectedFacesBoundaryTerm D
      measureLocalization.interiorBoundaryTerm hterm)
    hactive hpieces rfl

/--
Adjacent-selected-faces constructor when the resolved project-local term family
has already been identified globally with the M8 localized term.
-/
def ofAdjacentSelectedFaces
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
  ofResolved (ArtificialFaceResolvedData.ofAdjacentSelectedFaces D)
    hactive hpieces hterm

end M8ArtificialFaceFields

namespace M8GlobalStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {BoundaryPiece : Type b}

/-- Project the artificial-face part of an M8 input as a reusable field package. -/
def artificialFaceFields
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    M8ArtificialFaceFields I omega BoundaryPiece D.selectedPartition
      D.targetImages D.measureLocalization where
  artificialFaces := D.artificialFaces
  artificialFaces_active := D.artificialFaces_active
  artificialFaces_pieces := D.artificialFaces_pieces
  artificialFaces_term := D.artificialFaces_term

@[simp]
theorem artificialFaceFields_artificialFaces
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    D.artificialFaceFields.artificialFaces = D.artificialFaces :=
  rfl

/--
Constructor for `M8GlobalStokesInput` that takes the artificial-face fields as
one package.  This avoids manually filling `artificialFaces`,
`artificialFaces_active`, `artificialFaces_pieces`, and
`artificialFaces_term` in later M8 constructors.
-/
def ofArtificialFaceFields
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (targetImages_active :
      targetImages.activeCharts = selectedPartition.active)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
        targetImages measureLocalization)
    (targetImages_source_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.sourceChart x q ∈ orientedBoundaryAtlas.charts)
    (targetImages_boundarySource_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts)
    (targetBoundaryTerm_eq_partition :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBoundaryTerm targetImages x q =
            measureLocalization.boundaryPartitionTerm x q) :
    M8GlobalStokesInput I omega BoundaryPiece where
  formData := formData
  orientedBoundaryAtlas := orientedBoundaryAtlas
  selectedPartition := selectedPartition
  selectedPartition_supportSet := selectedPartition_supportSet
  targetImages := targetImages
  targetImages_active := targetImages_active
  measureLocalization := measureLocalization
  artificialFaces := artificial.artificialFaces
  artificialFaces_active := artificial.artificialFaces_active
  artificialFaces_pieces := artificial.artificialFaces_pieces
  artificialFaces_term := artificial.artificialFaces_term
  targetImages_source_mem := targetImages_source_mem
  targetImages_boundarySource_mem := targetImages_boundarySource_mem
  targetBoundaryTerm_eq_partition := targetBoundaryTerm_eq_partition

@[simp]
theorem ofArtificialFaceFields_artificialFaces
    (formData : CompactlySupportedSmoothFormData I omega)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (selectedPartition_supportSet :
      selectedPartition.K = formData.supportSet)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (targetImages_active :
      targetImages.activeCharts = selectedPartition.active)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
        targetImages measureLocalization)
    (targetImages_source_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.sourceChart x q ∈ orientedBoundaryAtlas.charts)
    (targetImages_boundarySource_mem :
      forall x, x ∈ targetImages.activeCharts ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          targetImages.boundarySourceChart x q ∈ orientedBoundaryAtlas.charts)
    (targetBoundaryTerm_eq_partition :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ targetImages.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBoundaryTerm targetImages x q =
            measureLocalization.boundaryPartitionTerm x q) :
    (ofArtificialFaceFields (I := I) (omega := omega)
      (BoundaryPiece := BoundaryPiece)
      formData orientedBoundaryAtlas selectedPartition
      selectedPartition_supportSet targetImages targetImages_active
      measureLocalization artificial targetImages_source_mem
      targetImages_boundarySource_mem
      targetBoundaryTerm_eq_partition).artificialFaces =
        artificial.artificialFaces :=
  rfl

end M8GlobalStokesInput

end ArtificialFaceToM8

end Stokes

end
