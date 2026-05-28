import Stokes.BoundaryChart.TargetBoxSourceShrinkIFT
import Stokes.BoundaryChart.ControlledTargetBoxFromIFTAuto
import Stokes.BoundaryChart.BoundaryTargetCoverMegaAuto
import Stokes.BoundaryChart.BoundarySourceUnifiedNaturalMegaAuto

/-!
# End-to-end IFT boundary-source packages

This file is a BoundaryChart-side integration layer for the current boundary
source route.

The inputs deliberately keep the genuine geometric and analytic facts as
fields of the existing lower-level structures:

* `BoundaryChartIFTTargetCoverMegaFamily` carries the selected source boxes,
  strict-derivative/local-openness data, compact-image target boxes, and
  orientation-generated surjectivity when callers use the orientation
  constructor.
* `BoundaryChartSourceShrinkOpenPartialHomeomorphFamily` carries the local
  inverse landing data for the shrunken source/target boxes.
* `BoundarySourceRouteFields` and `ControlledRouteFields` carry the M8-facing
  orientation/COV and project-local reconstruction fields.

The new end-to-end package only identifies these three routes as one coherent
boundary source route and then exposes the already-existing global-boundary
source inputs:

* `BoundarySourceUnifiedNaturalInput`;
* `ControlledBoundarySourceUnifiedNaturalInput`;
* the IFT wrappers obtained by forgetting to the local-openness route.

No new inverse-function theorem, compactness theorem, or change-of-variables
theorem is hidden here.  The remaining hard facts are still explicit fields,
but they are grouped into one reusable package.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedFintypeInType false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundarySourceIFTEndToEndMegaAuto

universe u w p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Piece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I ω}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/-! ## Pointwise projections from the IFT cover -/

namespace BoundaryChartIFTTargetCoverMegaFamily

variable (F : BoundaryChartIFTTargetCoverMegaFamily I ω M Piece)

/-- The source point used by the IFT/local-openness step on a local piece. -/
def sourcePoint (x : M) (q : Piece) : Fin n → Real :=
  (F.cover x).sourcePoint q

/-- The image point selected by the IFT/local-openness step. -/
def targetPoint (x : M) (q : Piece) : Fin n → Real :=
  (F.cover x).targetPoint q

@[simp]
theorem targetPoint_eq_transition_sourcePoint (x : M) (q : Piece) :
    F.targetPoint x q =
      boundaryChartTransition I (F.sourceChart x) (F.boundarySourceChart x)
        (F.sourcePoint x q) := by
  rfl

@[simp]
theorem localPieces_eq_cover_activePieces (x : M) :
    F.localPieces x = (F.cover x).activePieces := by
  rfl

/-- The selected source box contains the IFT source point. -/
theorem sourcePoint_mem
    (x : M) (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    F.sourcePoint x q ∈
      lowerZeroFaceDomain ((F.cover x).sourceLowerCorner q)
        ((F.cover x).sourceUpperCorner q) :=
  (F.cover x).sourcePoint_mem q hq

/-- The selected source box is a neighborhood of the IFT source point. -/
theorem source_mem_nhds
    (x : M) (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    lowerZeroFaceDomain ((F.cover x).sourceLowerCorner q)
        ((F.cover x).sourceUpperCorner q) ∈ 𝓝 (F.sourcePoint x q) :=
  (F.cover x).source_mem_nhds q hq

/-- Strict Frechet derivative supplied by the IFT cover. -/
theorem hasStrictFDerivAt
    (x : M) (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    HasStrictFDerivAt
      (boundaryChartTransition I (F.sourceChart x) (F.boundarySourceChart x))
      (boundaryChartTransitionTangentMap I (F.sourceChart x)
        (F.boundarySourceChart x) (F.sourcePoint x q))
      (F.sourcePoint x q) :=
  (F.cover x).hasStrictFDerivAt q hq

/-- Surjectivity of the tangential map supplied by the IFT cover. -/
theorem tangentMap_surjective
    (x : M) (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    (boundaryChartTransitionTangentMap I (F.sourceChart x)
      (F.boundarySourceChart x) (F.sourcePoint x q)).range = ⊤ :=
  (F.cover x).tangentMap_surjective q hq

/-- Local-openness neighborhood of the image point, derived inside the IFT cover. -/
theorem image_mem_nhds
    (x : M) (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    (boundaryChartTransition I (F.sourceChart x) (F.boundarySourceChart x)) ''
        lowerZeroFaceDomain ((F.cover x).sourceLowerCorner q)
          ((F.cover x).sourceUpperCorner q) ∈ 𝓝 (F.targetPoint x q) :=
  (F.cover x).image_mem_nhds q hq

/-- The IFT image point lies in the selected target box. -/
theorem targetPoint_mem
    (x : M) (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    F.targetPoint x q ∈
      lowerZeroFaceDomain ((F.cover x).targetLowerCorner q)
        ((F.cover x).targetUpperCorner q) :=
  (F.cover x).targetPoint_mem q hq

/-- The selected target box is contained in the transition image of the source box. -/
theorem targetBox_subset_image
    (x : M) (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    boundaryChartInverseImageBoxSelection I (F.sourceChart x)
      (F.boundarySourceChart x)
      ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q)
      ((F.cover x).targetLowerCorner q) ((F.cover x).targetUpperCorner q) :=
  (F.cover x).targetBox_subset_image q hq

/-- Compact-image containment for the selected source and target boxes. -/
theorem compactImage
    (x : M) (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    boundaryChartCompactImageBoxSelection I (F.sourceChart x)
      (F.boundarySourceChart x)
      ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q)
      ((F.cover x).targetLowerCorner q) ((F.cover x).targetUpperCorner q) :=
  (F.cover x).compactImage q hq

/-- Selected source boundary box on one active IFT piece. -/
theorem sourceSelectedBox_on
    (x : M) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    boundaryChartSelectedBox I (F.sourceChart x) (F.boundarySourceChart x) ω
      ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q) :=
  F.sourceSelectedBox x hx q hq

/-- Selected target boundary box on one active IFT piece. -/
theorem targetSelectedBox_on
    (x : M) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ (F.cover x).activePieces) :
    boundaryChartSelectedBox I (F.boundarySourceChart x)
      (F.boundaryTargetChart x q) ω
      ((F.cover x).targetLowerCorner q) ((F.cover x).targetUpperCorner q) :=
  F.targetSelectedBox x hx q hq

/-! ## Source-shrink projections -/

variable (G : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I ω M Piece)

/-- The local-homeomorphism data selected by the source-shrink route. -/
def sourceShrinkData (x : M) (q : Piece) :
    BoundaryChartSourceShrinkOpenPartialHomeomorphData I
      (G.sourceChart x q) (G.boundarySourceChart x q)
      (G.ambientSourceLowerCorner x q) (G.ambientSourceUpperCorner x q)
      (G.ambientTargetLowerCorner x q) (G.ambientTargetUpperCorner x q)
      (G.sourcePoint x q) (G.targetPoint x q) :=
  G.shrinkData x q

@[simp]
theorem sourceShrink_sourceLowerCorner (x : M) (q : Piece) :
    G.sourceLowerCorner x q = (sourceShrinkData G x q).sourceLowerCorner := by
  rfl

@[simp]
theorem sourceShrink_sourceUpperCorner (x : M) (q : Piece) :
    G.sourceUpperCorner x q = (sourceShrinkData G x q).sourceUpperCorner := by
  rfl

@[simp]
theorem sourceShrink_targetLowerCorner (x : M) (q : Piece) :
    G.targetLowerCorner x q = (sourceShrinkData G x q).targetLowerCorner := by
  rfl

@[simp]
theorem sourceShrink_targetUpperCorner (x : M) (q : Piece) :
    G.targetUpperCorner x q = (sourceShrinkData G x q).targetUpperCorner := by
  rfl

/-- The source point lies in the shrunken source box. -/
theorem sourceShrink_sourcePoint_mem (x : M) (q : Piece) :
    G.sourcePoint x q ∈
      lowerZeroFaceDomain (G.sourceLowerCorner x q) (G.sourceUpperCorner x q) := by
  simpa [sourceShrinkData, BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.sourceLowerCorner,
    BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.sourceUpperCorner] using
    (G.shrinkData x q).sourcePoint_mem

/-- The target point lies in the shrunken target box. -/
theorem sourceShrink_targetPoint_mem (x : M) (q : Piece) :
    G.targetPoint x q ∈
      lowerZeroFaceDomain (G.targetLowerCorner x q) (G.targetUpperCorner x q) := by
  simpa [sourceShrinkData, BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.targetLowerCorner,
    BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.targetUpperCorner] using
    (G.shrinkData x q).targetPoint_mem

/-- The shrunken source box lies in the source of the local homeomorphism. -/
theorem sourceShrink_sourceBox_subset_localSource (x : M) (q : Piece) :
    lowerZeroFaceDomain (G.sourceLowerCorner x q) (G.sourceUpperCorner x q) ⊆
      (G.shrinkData x q).localHomeomorph.source := by
  simpa [BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.sourceLowerCorner,
    BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.sourceUpperCorner] using
    (G.shrinkData x q).sourceBox_subset_localSource

/-- The shrunken target box lies in the target of the local homeomorphism. -/
theorem sourceShrink_targetBox_subset_localTarget (x : M) (q : Piece) :
    lowerZeroFaceDomain (G.targetLowerCorner x q) (G.targetUpperCorner x q) ⊆
      (G.shrinkData x q).localHomeomorph.target := by
  simpa [BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.targetLowerCorner,
    BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.targetUpperCorner] using
    (G.shrinkData x q).targetBox_subset_localTarget

/-- The local homeomorphism agrees with the boundary chart transition on the source box. -/
theorem sourceShrink_localHomeomorph_eq_transition
    (x : M) (q : Piece)
    (z : Fin n → Real)
    (hz : z ∈ lowerZeroFaceDomain (G.sourceLowerCorner x q)
      (G.sourceUpperCorner x q)) :
    boundaryChartTransition I (G.sourceChart x q) (G.boundarySourceChart x q) z =
      (G.shrinkData x q).localHomeomorph z := by
  simpa [BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.sourceLowerCorner,
    BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.sourceUpperCorner] using
    (G.shrinkData x q).localHomeomorph_eq_transition z hz

/-- The chart transition maps the shrunken source box into the shrunken target box. -/
theorem sourceShrink_mapsTo_target (x : M) (q : Piece) :
    MapsTo (boundaryChartTransition I (G.sourceChart x q) (G.boundarySourceChart x q))
      (lowerZeroFaceDomain (G.sourceLowerCorner x q) (G.sourceUpperCorner x q))
      (lowerZeroFaceDomain (G.targetLowerCorner x q) (G.targetUpperCorner x q)) := by
  simpa [BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.sourceLowerCorner,
    BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.sourceUpperCorner,
    BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.targetLowerCorner,
    BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.targetUpperCorner] using
    (G.shrinkData x q).mapsTo_target

/-- The local inverse lands back in the shrunken source box. -/
theorem sourceShrink_inverse_mapsTo_source (x : M) (q : Piece) :
    MapsTo (G.shrinkData x q).localHomeomorph.symm
      (lowerZeroFaceDomain (G.targetLowerCorner x q) (G.targetUpperCorner x q))
      (lowerZeroFaceDomain (G.sourceLowerCorner x q) (G.sourceUpperCorner x q)) := by
  simpa [BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.sourceLowerCorner,
    BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.sourceUpperCorner,
    BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.targetLowerCorner,
    BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.targetUpperCorner] using
    (G.shrinkData x q).inverse_mapsTo_source

/-! ## Coherence between IFT route and source-shrink route -/

/--
Optional audit equalities saying that the source-shrink presentation lands on
the same chart/piece/source boxes as the IFT cover presentation.

The end-to-end route below only needs the two high-level package equalities,
but these lower-level equalities are often the most convenient way to build
those package equalities from a chart-box selection procedure.
-/
structure SourceShrinkLandingData
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω M Piece)
    (G : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I ω M Piece) where
  /-- Active charts agree. -/
  activeCharts_eq : G.activeCharts = F.activeCharts
  /-- Local pieces agree with the IFT cover pieces. -/
  localPieces_eq : ∀ x, G.localPieces x = (F.cover x).activePieces
  /-- Source chart labels agree. -/
  sourceChart_eq : ∀ x q, G.sourceChart x q = F.sourceChart x
  /-- Boundary-source chart labels agree. -/
  boundarySourceChart_eq : ∀ x q, G.boundarySourceChart x q = F.boundarySourceChart x
  /-- Boundary-target chart labels agree. -/
  boundaryTargetChart_eq : ∀ x q, G.boundaryTargetChart x q = F.boundaryTargetChart x q
  /-- Source lower corners agree. -/
  sourceLowerCorner_eq :
    ∀ x q, G.sourceLowerCorner x q = (F.cover x).sourceLowerCorner q
  /-- Source upper corners agree. -/
  sourceUpperCorner_eq :
    ∀ x q, G.sourceUpperCorner x q = (F.cover x).sourceUpperCorner q
  /-- Target lower corners agree. -/
  targetLowerCorner_eq :
    ∀ x q, G.targetLowerCorner x q = (F.cover x).targetLowerCorner q
  /-- Target upper corners agree. -/
  targetUpperCorner_eq :
    ∀ x q, G.targetUpperCorner x q = (F.cover x).targetUpperCorner q
  /-- IFT/source-shrink source points agree. -/
  sourcePoint_eq : ∀ x q, G.sourcePoint x q = F.sourcePoint x q
  /-- IFT/source-shrink target points agree. -/
  targetPoint_eq : ∀ x q, G.targetPoint x q = F.targetPoint x q

namespace SourceShrinkLandingData

variable {F : BoundaryChartIFTTargetCoverMegaFamily I ω M Piece}
variable {G : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I ω M Piece}
@[simp]
theorem activeCharts_eq_iff
    (D : SourceShrinkLandingData F G) :
    G.activeCharts = F.activeCharts :=
  D.activeCharts_eq

@[simp]
theorem localPieces_eq_cover
    (D : SourceShrinkLandingData F G) (x : M) :
    G.localPieces x = (F.cover x).activePieces :=
  D.localPieces_eq x

theorem sourceChart_eq_cover
    (D : SourceShrinkLandingData F G) (x : M) (q : Piece) :
    G.sourceChart x q = F.sourceChart x :=
  D.sourceChart_eq x q

theorem boundarySourceChart_eq_cover
    (D : SourceShrinkLandingData F G) (x : M) (q : Piece) :
    G.boundarySourceChart x q = F.boundarySourceChart x :=
  D.boundarySourceChart_eq x q

theorem boundaryTargetChart_eq_cover
    (D : SourceShrinkLandingData F G) (x : M) (q : Piece) :
    G.boundaryTargetChart x q = F.boundaryTargetChart x q :=
  D.boundaryTargetChart_eq x q

theorem sourceLowerCorner_eq_cover
    (D : SourceShrinkLandingData F G) (x : M) (q : Piece) :
    G.sourceLowerCorner x q = (F.cover x).sourceLowerCorner q :=
  D.sourceLowerCorner_eq x q

theorem sourceUpperCorner_eq_cover
    (D : SourceShrinkLandingData F G) (x : M) (q : Piece) :
    G.sourceUpperCorner x q = (F.cover x).sourceUpperCorner q :=
  D.sourceUpperCorner_eq x q

theorem targetLowerCorner_eq_cover
    (D : SourceShrinkLandingData F G) (x : M) (q : Piece) :
    G.targetLowerCorner x q = (F.cover x).targetLowerCorner q :=
  D.targetLowerCorner_eq x q

theorem targetUpperCorner_eq_cover
    (D : SourceShrinkLandingData F G) (x : M) (q : Piece) :
    G.targetUpperCorner x q = (F.cover x).targetUpperCorner q :=
  D.targetUpperCorner_eq x q

theorem sourcePoint_eq_cover
    (D : SourceShrinkLandingData F G) (x : M) (q : Piece) :
    G.sourcePoint x q = F.sourcePoint x q :=
  D.sourcePoint_eq x q

theorem targetPoint_eq_cover
    (D : SourceShrinkLandingData F G) (x : M) (q : Piece) :
    G.targetPoint x q = F.targetPoint x q :=
  D.targetPoint_eq x q

end SourceShrinkLandingData

/--
End-to-end boundary-source route data for an IFT target cover.

The `sourceShrinkRouteFields` field builds the compatible unified
source package.  The `iftRouteFields` and `controlledRouteFields` fields are
the target-cover presentations used by the global route.  The equality fields
are the only bridge between the presentations; callers can prove them by
definitional alignment, by `SourceShrinkLandingData`, or by a later chart-box
selection constructor.
-/
structure BoundarySourceIFTEndToEndRouteData
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω M Piece)
    (G : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I ω M Piece)
    (selectedPartition : SelectedBoxPartitionOfUnity I ω)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M) where
  /-- Optional low-level landing equalities for auditing chart-box choices. -/
  landing : SourceShrinkLandingData F G
  /-- Source-shrink route fields producing the unified boundary-source package. -/
  sourceShrinkRouteFields :
    G.BoundarySourceUnifiedRouteFields selectedPartition orientedBoundaryAtlas
  /-- IFT/local-openness route fields for the same source pieces. -/
  iftRouteFields :
    F.BoundarySourceRouteFields selectedPartition orientedBoundaryAtlas
  /-- Controlled target route fields for the same source pieces. -/
  controlledRouteFields :
    F.ControlledRouteFields selectedPartition orientedBoundaryAtlas
  /-- The source-shrink package presents the same target-image input as the IFT route. -/
  ift_targetImageInput_eq :
    sourceShrinkRouteFields.toBoundarySourceAlignmentUnifiedData.toM8TargetImageInput =
      iftRouteFields.toM8TargetImageInput
  /-- The source-shrink package presents the same project-local data as the IFT route. -/
  ift_projectLocal_eq :
    sourceShrinkRouteFields.toBoundarySourceAlignmentUnifiedData.toProjectLocalGlobalStokesData =
      iftRouteFields.toProjectLocalGlobalStokesData
  /-- The source-shrink controlled input presents the same target-image input as the controlled route. -/
  controlled_targetImageInput_eq :
    sourceShrinkRouteFields.toBoundarySourceAlignmentUnifiedData.toM8BoundaryControlledTargetInput.toM8TargetImageInput =
      controlledRouteFields.toM8TargetImageInput
  /-- The source-shrink package presents the same project-local data as the controlled route. -/
  controlled_projectLocal_eq :
    sourceShrinkRouteFields.toBoundarySourceAlignmentUnifiedData.toProjectLocalGlobalStokesData =
      controlledRouteFields.toProjectLocalGlobalStokesData

namespace BoundarySourceIFTEndToEndRouteData

variable {F : BoundaryChartIFTTargetCoverMegaFamily I ω M Piece}
variable {G : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I ω M Piece}
variable (D : BoundarySourceIFTEndToEndRouteData F G selectedPartition orientedBoundaryAtlas)

/-- Unified boundary-source package generated by the source-shrink route. -/
def boundaryUnified :
    BoundarySourceAlignmentUnifiedData
      (I := I) (omega := ω)
      (selectedPartition := selectedPartition)
      (orientedBoundaryAtlas := orientedBoundaryAtlas)
      (BoundaryPiece := Piece) :=
  D.sourceShrinkRouteFields.toBoundarySourceAlignmentUnifiedData

/-- IFT target-image input from the target-cover route fields. -/
def iftM8TargetImageInput :
    M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  D.iftRouteFields.toM8TargetImageInput

/-- Controlled target-image input from the controlled target-cover route fields. -/
def controlledM8TargetImageInput :
    M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  D.controlledRouteFields.toM8TargetImageInput

/-- Controlled M8 boundary-target input from the controlled route. -/
def controlledM8BoundaryTargetInput :
    M8BoundaryControlledTargetInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  D.controlledRouteFields.toM8BoundaryControlledTargetInput

/-- Project-local data from the IFT route. -/
def iftProjectLocalGlobalStokesData :
    ProjectLocalGlobalStokesData I ω M Piece :=
  D.iftRouteFields.toProjectLocalGlobalStokesData

/-- Project-local data from the controlled route. -/
def controlledProjectLocalGlobalStokesData :
    ProjectLocalGlobalStokesData I ω M Piece :=
  D.controlledRouteFields.toProjectLocalGlobalStokesData

/-- IFT natural source input consumed by the global boundary-source route. -/
def toBoundarySourceUnifiedNaturalInput :
    BoundaryChartIFTTargetCoverMegaFamily.BoundarySourceUnifiedNaturalInput
      F selectedPartition orientedBoundaryAtlas where
  routeFields := D.iftRouteFields
  boundaryUnified := D.boundaryUnified
  targetImageInput_eq := D.ift_targetImageInput_eq
  projectLocal_eq := D.ift_projectLocal_eq

/-- Controlled IFT natural source input consumed by the global boundary-source route. -/
def toControlledBoundarySourceUnifiedNaturalInput :
    BoundaryChartIFTTargetCoverMegaFamily.ControlledBoundarySourceUnifiedNaturalInput
      F selectedPartition orientedBoundaryAtlas where
  controlledRouteFields := D.controlledRouteFields
  boundaryUnified := D.boundaryUnified
  targetImageInput_eq := D.controlled_targetImageInput_eq
  projectLocal_eq := D.controlled_projectLocal_eq

/-- The same natural source input, seen after forgetting IFT data to local-openness. -/
def toLocalOpennessBoundarySourceUnifiedNaturalInput :
    BoundaryChartLocalOpennessTargetCoverMegaFamily.BoundarySourceUnifiedNaturalInput
      F.toLocalOpennessMegaFamily selectedPartition orientedBoundaryAtlas :=
  D.toBoundarySourceUnifiedNaturalInput

/-- The same controlled source input, seen after forgetting IFT data to local-openness. -/
def toLocalOpennessControlledBoundarySourceUnifiedNaturalInput :
    BoundaryChartLocalOpennessTargetCoverMegaFamily.ControlledBoundarySourceUnifiedNaturalInput
      F.toLocalOpennessMegaFamily selectedPartition orientedBoundaryAtlas :=
  D.toControlledBoundarySourceUnifiedNaturalInput

@[simp]
theorem boundaryUnified_def :
    D.boundaryUnified =
      D.sourceShrinkRouteFields.toBoundarySourceAlignmentUnifiedData := by
  rfl

@[simp]
theorem toBoundarySourceUnifiedNaturalInput_routeFields :
    D.toBoundarySourceUnifiedNaturalInput.routeFields = D.iftRouteFields := by
  rfl

@[simp]
theorem toBoundarySourceUnifiedNaturalInput_boundaryUnified :
    D.toBoundarySourceUnifiedNaturalInput.boundaryUnified = D.boundaryUnified := by
  rfl

@[simp]
theorem toControlledBoundarySourceUnifiedNaturalInput_routeFields :
    D.toControlledBoundarySourceUnifiedNaturalInput.controlledRouteFields =
      D.controlledRouteFields := by
  rfl

@[simp]
theorem toControlledBoundarySourceUnifiedNaturalInput_boundaryUnified :
    D.toControlledBoundarySourceUnifiedNaturalInput.boundaryUnified =
      D.boundaryUnified := by
  rfl

@[simp]
theorem iftM8TargetImageInput_activeCharts :
    D.iftM8TargetImageInput.targetImages.activeCharts = F.activeCharts := by
  rfl

@[simp]
theorem iftM8TargetImageInput_boundaryPieces :
    D.iftM8TargetImageInput.targetImages.boundaryPieces =
      fun x => (F.cover x).activePieces := by
  rfl

@[simp]
theorem iftM8TargetImageInput_sourceChart :
    D.iftM8TargetImageInput.targetImages.sourceChart =
      fun x _ => F.sourceChart x := by
  rfl

@[simp]
theorem iftM8TargetImageInput_boundarySourceChart :
    D.iftM8TargetImageInput.targetImages.boundarySourceChart =
      fun x _ => F.boundarySourceChart x := by
  rfl

@[simp]
theorem iftM8TargetImageInput_sourceLowerCorner :
    D.iftM8TargetImageInput.targetImages.sourceLowerCorner =
      fun x q => (F.cover x).sourceLowerCorner q := by
  rfl

@[simp]
theorem iftM8TargetImageInput_sourceUpperCorner :
    D.iftM8TargetImageInput.targetImages.sourceUpperCorner =
      fun x q => (F.cover x).sourceUpperCorner q := by
  rfl

@[simp]
theorem controlledM8TargetImageInput_activeCharts :
    D.controlledM8TargetImageInput.targetImages.activeCharts = F.activeCharts := by
  rfl

@[simp]
theorem controlledM8TargetImageInput_boundaryPieces :
    D.controlledM8TargetImageInput.targetImages.boundaryPieces =
      fun x => (F.cover x).activePieces := by
  rfl

@[simp]
theorem controlledM8TargetImageInput_sourceChart :
    D.controlledM8TargetImageInput.targetImages.sourceChart =
      fun x _ => F.sourceChart x := by
  rfl

@[simp]
theorem controlledM8TargetImageInput_boundarySourceChart :
    D.controlledM8TargetImageInput.targetImages.boundarySourceChart =
      fun x _ => F.boundarySourceChart x := by
  rfl

@[simp]
theorem controlledM8BoundaryTargetInput_toM8TargetImageInput :
    D.controlledM8BoundaryTargetInput.toM8TargetImageInput =
      D.controlledM8TargetImageInput := by
  rfl

@[simp]
theorem boundaryUnified_toM8TargetImageInput_eq_ift :
    D.boundaryUnified.toM8TargetImageInput = D.iftM8TargetImageInput :=
  D.ift_targetImageInput_eq

@[simp]
theorem boundaryUnified_toProjectLocal_eq_ift :
    D.boundaryUnified.toProjectLocalGlobalStokesData =
      D.iftProjectLocalGlobalStokesData :=
  D.ift_projectLocal_eq

@[simp]
theorem boundaryUnified_controlled_toM8TargetImageInput_eq :
    D.boundaryUnified.toM8BoundaryControlledTargetInput.toM8TargetImageInput =
      D.controlledM8TargetImageInput :=
  D.controlled_targetImageInput_eq

@[simp]
theorem boundaryUnified_toProjectLocal_eq_controlled :
    D.boundaryUnified.toProjectLocalGlobalStokesData =
      D.controlledProjectLocalGlobalStokesData :=
  D.controlled_projectLocal_eq

/-- Source/project-local alignment from the IFT route. -/
def iftBoundarySourceProjectLocalAlignment :
    BoundarySourceProjectLocalAlignment D.iftM8TargetImageInput
      D.iftProjectLocalGlobalStokesData :=
  D.iftRouteFields.toBoundarySourceProjectLocalAlignment

/-- Source/project-local alignment from the controlled route. -/
def controlledBoundarySourceProjectLocalAlignment :
    BoundarySourceProjectLocalAlignment D.controlledM8TargetImageInput
      D.controlledProjectLocalGlobalStokesData :=
  D.controlledRouteFields.toBoundarySourceProjectLocalAlignment

/-- Boundary canonical route obtained from the IFT route fields. -/
def toIFTBoundaryCanonicalRouteMeasureInput
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        D.iftProjectLocalGlobalStokesData)
    (projectLocal :
      ProjectLocalBoundaryMeasureConstructorInput
        D.iftProjectLocalGlobalStokesData) :
    BoundaryCanonicalRouteMeasureInput D.iftM8TargetImageInput
      D.iftProjectLocalGlobalStokesData :=
  D.iftRouteFields.toBoundaryCanonicalRouteMeasureInput
    faceContinuity projectLocal

/-- Boundary canonical route obtained from the controlled route fields. -/
def toControlledBoundaryCanonicalRouteMeasureInput
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        D.controlledProjectLocalGlobalStokesData)
    (projectLocal :
      ProjectLocalBoundaryMeasureConstructorInput
        D.controlledProjectLocalGlobalStokesData) :
    BoundaryCanonicalRouteMeasureInput D.controlledM8TargetImageInput
      D.controlledProjectLocalGlobalStokesData :=
  D.controlledRouteFields.toBoundaryCanonicalRouteMeasureInput
    faceContinuity projectLocal

@[simp]
theorem toIFTBoundaryCanonicalRouteMeasureInput_sourceAlignment
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        D.iftProjectLocalGlobalStokesData)
    (projectLocal :
      ProjectLocalBoundaryMeasureConstructorInput
        D.iftProjectLocalGlobalStokesData) :
    (D.toIFTBoundaryCanonicalRouteMeasureInput faceContinuity projectLocal).sourceAlignment =
      D.iftBoundarySourceProjectLocalAlignment := by
  rfl

@[simp]
theorem toControlledBoundaryCanonicalRouteMeasureInput_sourceAlignment
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        D.controlledProjectLocalGlobalStokesData)
    (projectLocal :
      ProjectLocalBoundaryMeasureConstructorInput
        D.controlledProjectLocalGlobalStokesData) :
    (D.toControlledBoundaryCanonicalRouteMeasureInput faceContinuity projectLocal).sourceAlignment =
      D.controlledBoundarySourceProjectLocalAlignment := by
  rfl

/-- Project-local Stokes theorem exposed from the IFT route fields. -/
theorem iftProjectLocalStokes :
    D.iftRouteFields.globalBulkIntegral =
      D.iftRouteFields.globalBoundaryIntegral :=
  D.iftRouteFields.stokes

/-- Project-local Stokes theorem exposed from the controlled route fields. -/
theorem controlledProjectLocalStokes :
    D.controlledRouteFields.globalBulkIntegral =
      D.controlledRouteFields.globalBoundaryIntegral :=
  D.controlledRouteFields.stokes

/-- Natural endpoint input from the IFT end-to-end package. -/
def toNaturalBulkEndpointUnifiedInput
    {ρ : SmoothPartitionOfUnity M I M univ}
    {μ : Measure (Fin (n + 1) → Real)}
    [IsFiniteMeasureOnCompacts μ] [IsManifold I 1 M]
    {chartBoxes : NaturalFiniteActiveChartBoxSelectionData I ω ρ}
    (D :
      BoundarySourceIFTEndToEndRouteData F G chartBoxes.selectedPartition
        orientedBoundaryAtlas)
    (localized : LocalizedInteriorM8Fields I ω chartBoxes.selectedPartition)
    (measure_eq_volume : μ = volume)
    (boundaryFaceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        D.boundaryUnified.toProjectLocalGlobalStokesData)
    (boundaryChartChange :
      BoundaryChartChangeSelectedFamilyData
        D.boundaryUnified.toProjectLocalGlobalStokesData) :
    NaturalBulkEndpointUnifiedInput
      (I := I) (omega := ω) (rho := ρ)
      chartBoxes Piece μ :=
  D.toBoundarySourceUnifiedNaturalInput.toNaturalBulkEndpointUnifiedInput
    localized measure_eq_volume boundaryFaceContinuity boundaryChartChange

/-- Common endpoint data from the IFT end-to-end package. -/
def toNaturalBulkEndpointCommonData
    {ρ : SmoothPartitionOfUnity M I M univ}
    {μ : Measure (Fin (n + 1) → Real)}
    [IsFiniteMeasureOnCompacts μ] [IsManifold I 1 M]
    {chartBoxes : NaturalFiniteActiveChartBoxSelectionData I ω ρ}
    (D :
      BoundarySourceIFTEndToEndRouteData F G chartBoxes.selectedPartition
        orientedBoundaryAtlas)
    (localized : LocalizedInteriorM8Fields I ω chartBoxes.selectedPartition)
    (measure_eq_volume : μ = volume)
    (boundaryFaceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        D.boundaryUnified.toProjectLocalGlobalStokesData)
    (boundaryChartChange :
      BoundaryChartChangeSelectedFamilyData
        D.boundaryUnified.toProjectLocalGlobalStokesData) :
    NaturalBulkEndpointCommonData
      (I := I) (omega := ω) (rho := ρ)
      chartBoxes Piece μ :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.BoundarySourceUnifiedNaturalInput.toNaturalBulkEndpointCommonData
    D.toLocalOpennessBoundarySourceUnifiedNaturalInput localized measure_eq_volume
    boundaryFaceContinuity boundaryChartChange

/-- Natural endpoint input from the controlled IFT end-to-end package. -/
def toControlledNaturalBulkEndpointUnifiedInput
    {ρ : SmoothPartitionOfUnity M I M univ}
    {μ : Measure (Fin (n + 1) → Real)}
    [IsFiniteMeasureOnCompacts μ] [IsManifold I 1 M]
    {chartBoxes : NaturalFiniteActiveChartBoxSelectionData I ω ρ}
    (D :
      BoundarySourceIFTEndToEndRouteData F G chartBoxes.selectedPartition
        orientedBoundaryAtlas)
    (localized : LocalizedInteriorM8Fields I ω chartBoxes.selectedPartition)
    (measure_eq_volume : μ = volume)
    (boundaryFaceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        D.boundaryUnified.toProjectLocalGlobalStokesData)
    (boundaryChartChange :
      BoundaryChartChangeSelectedFamilyData
        D.boundaryUnified.toProjectLocalGlobalStokesData) :
    NaturalBulkEndpointUnifiedInput
      (I := I) (omega := ω) (rho := ρ)
      chartBoxes Piece μ :=
  D.toControlledBoundarySourceUnifiedNaturalInput.toNaturalBulkEndpointUnifiedInput
    localized measure_eq_volume boundaryFaceContinuity boundaryChartChange

@[simp]
theorem toNaturalBulkEndpointUnifiedInput_boundaryUnified
    {ρ : SmoothPartitionOfUnity M I M univ}
    {μ : Measure (Fin (n + 1) → Real)}
    [IsFiniteMeasureOnCompacts μ] [IsManifold I 1 M]
    {chartBoxes : NaturalFiniteActiveChartBoxSelectionData I ω ρ}
    (D :
      BoundarySourceIFTEndToEndRouteData F G chartBoxes.selectedPartition
        orientedBoundaryAtlas)
    (localized : LocalizedInteriorM8Fields I ω chartBoxes.selectedPartition)
    (measure_eq_volume : μ = volume)
    (boundaryFaceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        D.boundaryUnified.toProjectLocalGlobalStokesData)
    (boundaryChartChange :
      BoundaryChartChangeSelectedFamilyData
        D.boundaryUnified.toProjectLocalGlobalStokesData) :
    (D.toNaturalBulkEndpointUnifiedInput localized measure_eq_volume
      boundaryFaceContinuity boundaryChartChange).boundaryUnified =
      D.boundaryUnified := by
  rfl

@[simp]
theorem toControlledNaturalBulkEndpointUnifiedInput_boundaryUnified
    {ρ : SmoothPartitionOfUnity M I M univ}
    {μ : Measure (Fin (n + 1) → Real)}
    [IsFiniteMeasureOnCompacts μ] [IsManifold I 1 M]
    {chartBoxes : NaturalFiniteActiveChartBoxSelectionData I ω ρ}
    (D :
      BoundarySourceIFTEndToEndRouteData F G chartBoxes.selectedPartition
        orientedBoundaryAtlas)
    (localized : LocalizedInteriorM8Fields I ω chartBoxes.selectedPartition)
    (measure_eq_volume : μ = volume)
    (boundaryFaceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        D.boundaryUnified.toProjectLocalGlobalStokesData)
    (boundaryChartChange :
      BoundaryChartChangeSelectedFamilyData
        D.boundaryUnified.toProjectLocalGlobalStokesData) :
    (D.toControlledNaturalBulkEndpointUnifiedInput localized measure_eq_volume
      boundaryFaceContinuity boundaryChartChange).boundaryUnified =
      D.boundaryUnified := by
  rfl

end BoundarySourceIFTEndToEndRouteData

end BoundaryChartIFTTargetCoverMegaFamily

end BoundarySourceIFTEndToEndMegaAuto

end Stokes

end
