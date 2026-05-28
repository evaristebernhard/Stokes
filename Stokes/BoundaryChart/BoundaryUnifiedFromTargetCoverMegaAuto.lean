import Stokes.BoundaryChart.BoundaryTargetCoverMegaAuto
import Stokes.Global.BoundaryControlledTargetToM8Auto
import Stokes.Global.BoundarySourceAlignmentConstructors

/-!
# Boundary target-cover families as M8/source-alignment input

This module is the integration-side bridge from the boundary-chart target-cover
families to the M8 and boundary-source alignment APIs.

The existing `BoundaryTargetCoverMegaAuto` file builds resolved target-image
families from local-openness/IFT covers.  The definitions here package the
remaining global fields together with those families, then expose:

* direct `M8TargetImageResolvedInput` / `M8TargetImageInput` wrappers;
* project-local source data whose fields are definitionally aligned with the
  target-image source fields;
* controlled-target wrappers when the caller has selected later target boxes;
* parallel local-openness and IFT entry points.

No new analytic theorem is hidden here.  The hard facts remain fields:
source-extended boxes, boundary partition endpoint equalities, project-local
Stokes, chart-change cancellation, and measure reconstruction.
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

section BoundaryUnifiedFromTargetCoverMegaAuto

universe u w p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Piece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I ω}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/-! ## Local-openness target-cover route -/

namespace BoundaryChartLocalOpennessTargetCoverMegaFamily

variable (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω M Piece)

/-- M8 resolved target-image input obtained from a local-openness mega family. -/
def toM8ResolvedInputOfFields
    (fields : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    M8TargetImageResolvedInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  fields.toM8ResolvedInput

/-- M8 target-image input obtained from a local-openness mega family. -/
def toM8TargetImageInputOfFields
    (fields : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  fields.toM8TargetImageInput

@[simp]
theorem toM8ResolvedInputOfFields_family
    (fields : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    (toM8ResolvedInputOfFields F fields).family =
      F.toTargetImageResolvedFamily :=
  rfl

@[simp]
theorem toM8ResolvedInputOfFields_boundaryPartitionTerm
    (fields : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    (toM8ResolvedInputOfFields F fields).boundaryPartitionTerm =
      fields.boundaryPartitionTerm :=
  rfl

@[simp]
theorem toM8TargetImageInputOfFields_assembly
    (fields : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    (toM8TargetImageInputOfFields F fields).assembly =
      (toM8ResolvedInputOfFields F fields).toAssemblyInput :=
  rfl

@[simp]
theorem toM8TargetImageInputOfFields_targetImages_activeCharts
    (fields : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    (toM8TargetImageInputOfFields F fields).targetImages.activeCharts =
      F.activeCharts :=
  rfl

@[simp]
theorem toM8TargetImageInputOfFields_targetImages_boundaryPieces
    (fields : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    (toM8TargetImageInputOfFields F fields).targetImages.boundaryPieces =
      fun x => (F.cover x).activePieces :=
  rfl

@[simp]
theorem toM8TargetImageInputOfFields_targetImages_sourceChart
    (fields : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    (toM8TargetImageInputOfFields F fields).targetImages.sourceChart =
      fun x _ => F.sourceChart x :=
  rfl

@[simp]
theorem toM8TargetImageInputOfFields_targetImages_boundarySourceChart
    (fields : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    (toM8TargetImageInputOfFields F fields).targetImages.boundarySourceChart =
      fun x _ => F.boundarySourceChart x :=
  rfl

@[simp]
theorem toM8TargetImageInputOfFields_targetImages_sourceLowerCorner
    (fields : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    (toM8TargetImageInputOfFields F fields).targetImages.sourceLowerCorner =
      fun x q => (F.cover x).sourceLowerCorner q :=
  rfl

@[simp]
theorem toM8TargetImageInputOfFields_targetImages_sourceUpperCorner
    (fields : M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    (toM8TargetImageInputOfFields F fields).targetImages.sourceUpperCorner =
      fun x q => (F.cover x).sourceUpperCorner q :=
  rfl

/--
Boundary source route fields over a local-openness target-cover family.

The first field is the M8 assembly data produced by the target-cover route. The
remaining fields are exactly the project-local Stokes/reconstruction facts
needed to align the same source pieces with boundary measure routes.
-/
structure BoundarySourceRouteFields
    (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω M Piece)
    (selectedPartition : SelectedBoxPartitionOfUnity I ω)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M) where
  /-- M8 fields attached to the resolved target-image family. -/
  m8Fields : M8ResolvedFields F selectedPartition orientedBoundaryAtlas
  /-- Global bulk integral represented by these boundary-source pieces. -/
  globalBulkIntegral : Real
  /-- Global boundary integral represented by these boundary-source pieces. -/
  globalBoundaryIntegral : Real
  /-- Bulk reconstruction from the project-local source boxes. -/
  globalBulkIntegral_eq_projectLocalSum :
    globalBulkIntegral =
      Finset.sum F.activeCharts fun x =>
        Finset.sum ((F.cover x).activePieces) fun q =>
          projectLocalBulkIntegral I (F.sourceChart x) (F.boundarySourceChart x) ω
            ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q)
  /-- Project-local Stokes on every active boundary-source piece. -/
  localProjectStokes :
    ∀ x, x ∈ F.activeCharts →
      ∀ q, q ∈ (F.cover x).activePieces →
        projectLocalBulkIntegral I (F.sourceChart x) (F.boundarySourceChart x) ω
            ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q) =
          projectLocalBoundaryIntegral I (F.sourceChart x) (F.boundarySourceChart x) ω
            ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q)
  /-- Boundary chart-change cancellation into the shared M8 partition term. -/
  chartChangeCancellation :
    (Finset.sum F.activeCharts fun x =>
        Finset.sum ((F.cover x).activePieces) fun q =>
          projectLocalBoundaryIntegral I (F.sourceChart x) (F.boundarySourceChart x) ω
            ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q)) =
      Finset.sum F.activeCharts fun x =>
        Finset.sum ((F.cover x).activePieces) fun q =>
          m8Fields.boundaryPartitionTerm x q
  /-- Boundary reconstruction from the shared M8 partition term. -/
  globalBoundaryIntegral_eq_boundaryPartitionSum :
    globalBoundaryIntegral =
      Finset.sum F.activeCharts fun x =>
        Finset.sum ((F.cover x).activePieces) fun q =>
          m8Fields.boundaryPartitionTerm x q

namespace BoundarySourceRouteFields

variable {F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω M Piece}
variable (D : BoundarySourceRouteFields F selectedPartition orientedBoundaryAtlas)

/-- The resolved target-image package carried by the route fields. -/
def toM8ResolvedInput :
    M8TargetImageResolvedInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  D.m8Fields.toM8ResolvedInput

/-- The M8 target-image package carried by the route fields. -/
def toM8TargetImageInput :
    M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  D.m8Fields.toM8TargetImageInput

/-- Project-local constructor data whose source fields are the cover family. -/
def toProjectLocalConstructorData :
    ProjectLocalConstructorData I ω M Piece where
  activeCharts := F.activeCharts
  localPieces := fun x => (F.cover x).activePieces
  sourceChart := fun x _ => F.sourceChart x
  targetChart := fun x _ => F.boundarySourceChart x
  lowerCorner := fun x q => (F.cover x).sourceLowerCorner q
  upperCorner := fun x q => (F.cover x).sourceUpperCorner q
  boundaryPartitionTerm := D.m8Fields.boundaryPartitionTerm
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral
  globalBulkIntegral_eq_projectLocalSum :=
    D.globalBulkIntegral_eq_projectLocalSum
  localProjectStokes := D.localProjectStokes
  chartChangeCancellation := D.chartChangeCancellation
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    D.globalBoundaryIntegral_eq_boundaryPartitionSum

/-- Final project-local package induced by the local-openness route fields. -/
def toProjectLocalGlobalStokesData :
    ProjectLocalGlobalStokesData I ω M Piece :=
  D.toProjectLocalConstructorData.toProjectLocalGlobalStokesData

@[simp]
theorem toM8ResolvedInput_family :
    D.toM8ResolvedInput.family = F.toTargetImageResolvedFamily :=
  rfl

@[simp]
theorem toM8ResolvedInput_boundaryPartitionTerm :
    D.toM8ResolvedInput.boundaryPartitionTerm =
      D.m8Fields.boundaryPartitionTerm :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_activeCharts :
    D.toM8TargetImageInput.targetImages.activeCharts = F.activeCharts :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundaryPieces :
    D.toM8TargetImageInput.targetImages.boundaryPieces =
      fun x => (F.cover x).activePieces :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceChart :
    D.toM8TargetImageInput.targetImages.sourceChart =
      fun x _ => F.sourceChart x :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundarySourceChart :
    D.toM8TargetImageInput.targetImages.boundarySourceChart =
      fun x _ => F.boundarySourceChart x :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceLowerCorner :
    D.toM8TargetImageInput.targetImages.sourceLowerCorner =
      fun x q => (F.cover x).sourceLowerCorner q :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceUpperCorner :
    D.toM8TargetImageInput.targetImages.sourceUpperCorner =
      fun x q => (F.cover x).sourceUpperCorner q :=
  rfl

@[simp]
theorem toProjectLocalConstructorData_activeCharts :
    D.toProjectLocalConstructorData.activeCharts = F.activeCharts :=
  rfl

@[simp]
theorem toProjectLocalConstructorData_localPieces :
    D.toProjectLocalConstructorData.localPieces =
      fun x => (F.cover x).activePieces :=
  rfl

@[simp]
theorem toProjectLocalConstructorData_sourceChart :
    D.toProjectLocalConstructorData.sourceChart =
      fun x _ => F.sourceChart x :=
  rfl

@[simp]
theorem toProjectLocalConstructorData_targetChart :
    D.toProjectLocalConstructorData.targetChart =
      fun x _ => F.boundarySourceChart x :=
  rfl

@[simp]
theorem toProjectLocalConstructorData_lowerCorner :
    D.toProjectLocalConstructorData.lowerCorner =
      fun x q => (F.cover x).sourceLowerCorner q :=
  rfl

@[simp]
theorem toProjectLocalConstructorData_upperCorner :
    D.toProjectLocalConstructorData.upperCorner =
      fun x q => (F.cover x).sourceUpperCorner q :=
  rfl

@[simp]
theorem toProjectLocalConstructorData_boundaryPartitionTerm :
    D.toProjectLocalConstructorData.boundaryPartitionTerm =
      D.m8Fields.boundaryPartitionTerm :=
  rfl

/--
Source-alignment fields between the project-local package and the M8
target-image package.  Every equality is definitional because both packages are
projected from the same target-cover family.
-/
def toBoundarySourceTargetImageAlignmentFields :
    BoundarySourceTargetImageAlignmentFields D.toM8TargetImageInput
      D.toProjectLocalGlobalStokesData where
  activeCharts_eq_targetImages := rfl
  localPieces_eq_targetImages := fun _ => rfl
  sourceChart_eq_targetImages := fun _ _ => rfl
  targetChart_eq_targetImages := fun _ _ => rfl
  lowerCorner_eq_targetImages := fun _ _ => rfl
  upperCorner_eq_targetImages := fun _ _ => rfl

/-- Source/project-local alignment generated from the target-cover route. -/
def toBoundarySourceProjectLocalAlignment :
    BoundarySourceProjectLocalAlignment D.toM8TargetImageInput
      D.toProjectLocalGlobalStokesData :=
  D.toBoundarySourceTargetImageAlignmentFields.toBoundarySourceProjectLocalAlignment

/-- Canonical boundary route from local-openness target-cover route fields. -/
def toBoundaryCanonicalRouteMeasureInput
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        D.toProjectLocalGlobalStokesData)
    (projectLocal :
      ProjectLocalBoundaryMeasureConstructorInput
        D.toProjectLocalGlobalStokesData) :
    BoundaryCanonicalRouteMeasureInput D.toM8TargetImageInput
      D.toProjectLocalGlobalStokesData :=
  BoundaryCanonicalRouteMeasureInput.ofTargetImageAlignmentFields
    faceContinuity projectLocal D.toBoundarySourceTargetImageAlignmentFields

@[simp]
theorem toBoundarySourceProjectLocalAlignment_localPieces_eq
    (x : M) :
    D.toBoundarySourceProjectLocalAlignment.localPieces_eq x =
      D.toBoundarySourceTargetImageAlignmentFields.localPieces_eq_targetImages x :=
  rfl

@[simp]
theorem toBoundaryCanonicalRouteMeasureInput_sourceAlignment
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        D.toProjectLocalGlobalStokesData)
    (projectLocal :
      ProjectLocalBoundaryMeasureConstructorInput
        D.toProjectLocalGlobalStokesData) :
    (D.toBoundaryCanonicalRouteMeasureInput faceContinuity projectLocal).sourceAlignment =
      D.toBoundarySourceProjectLocalAlignment :=
  rfl

/-- Project-local Stokes theorem exposed from the target-cover route fields. -/
theorem stokes :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  D.toProjectLocalConstructorData.stokes

end BoundarySourceRouteFields

/-! ### Controlled-target local-openness route -/

/--
Controlled target-image family induced by a local-openness target-cover family,
once later controlled target boxes have been selected for every chart/piece.
-/
def toControlledTargetImageFamily
    (targetSet : M → Piece → Set (Fin n → Real))
    (controlledTarget :
      ∀ x q,
        BoundaryChartControlledTargetBoxSelectionData I
          (F.sourceChart x) (F.boundarySourceChart x)
          ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q)
          ((F.cover x).targetLowerCorner q) ((F.cover x).targetUpperCorner q)
          ((F.cover x).targetPoint q) (targetSet x q))
    (controlledTargetSelectedBox :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ (F.cover x).activePieces →
          boundaryChartSelectedBox I (F.boundarySourceChart x)
            (F.boundaryTargetChart x q) ω
            ((controlledTarget x q).laterLowerCorner)
            ((controlledTarget x q).laterUpperCorner)) :
    BoundaryChartControlledTargetImageFamily I ω M Piece where
  activeCharts := F.activeCharts
  localPieces := fun x => (F.cover x).activePieces
  sourceChart := fun x _ => F.sourceChart x
  boundarySourceChart := fun x _ => F.boundarySourceChart x
  boundaryTargetChart := F.boundaryTargetChart
  sourceLowerCorner := fun x q => (F.cover x).sourceLowerCorner q
  sourceUpperCorner := fun x q => (F.cover x).sourceUpperCorner q
  selectedTargetLowerCorner := fun x q => (F.cover x).targetLowerCorner q
  selectedTargetUpperCorner := fun x q => (F.cover x).targetUpperCorner q
  targetPoint := fun x q => (F.cover x).targetPoint q
  targetSet := targetSet
  controlledTarget := controlledTarget
  sourceSelectedBox := F.sourceSelectedBox
  targetSelectedBox := controlledTargetSelectedBox

@[simp]
theorem toControlledTargetImageFamily_activeCharts
    (targetSet : M → Piece → Set (Fin n → Real))
    (controlledTarget :
      ∀ x q,
        BoundaryChartControlledTargetBoxSelectionData I
          (F.sourceChart x) (F.boundarySourceChart x)
          ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q)
          ((F.cover x).targetLowerCorner q) ((F.cover x).targetUpperCorner q)
          ((F.cover x).targetPoint q) (targetSet x q))
    (controlledTargetSelectedBox :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ (F.cover x).activePieces →
          boundaryChartSelectedBox I (F.boundarySourceChart x)
            (F.boundaryTargetChart x q) ω
            ((controlledTarget x q).laterLowerCorner)
            ((controlledTarget x q).laterUpperCorner)) :
    (F.toControlledTargetImageFamily targetSet controlledTarget
      controlledTargetSelectedBox).activeCharts = F.activeCharts :=
  rfl

@[simp]
theorem toControlledTargetImageFamily_localPieces
    (targetSet : M → Piece → Set (Fin n → Real))
    (controlledTarget :
      ∀ x q,
        BoundaryChartControlledTargetBoxSelectionData I
          (F.sourceChart x) (F.boundarySourceChart x)
          ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q)
          ((F.cover x).targetLowerCorner q) ((F.cover x).targetUpperCorner q)
          ((F.cover x).targetPoint q) (targetSet x q))
    (controlledTargetSelectedBox :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ (F.cover x).activePieces →
          boundaryChartSelectedBox I (F.boundarySourceChart x)
            (F.boundaryTargetChart x q) ω
            ((controlledTarget x q).laterLowerCorner)
            ((controlledTarget x q).laterUpperCorner)) :
    (F.toControlledTargetImageFamily targetSet controlledTarget
      controlledTargetSelectedBox).localPieces =
        fun x => (F.cover x).activePieces :=
  rfl

/--
Controlled route fields over a local-openness target-cover family.  This is the
stronger package used when downstream code wants an
`M8BoundaryControlledTargetInput` rather than a plain target-image input.
-/
structure ControlledRouteFields
    (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω M Piece)
    (selectedPartition : SelectedBoxPartitionOfUnity I ω)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M) where
  /-- Target-side sets containing the controlled later target boxes. -/
  targetSet : M → Piece → Set (Fin n → Real)
  /-- Controlled later target selected for every chart/piece. -/
  controlledTarget :
    ∀ x q,
      BoundaryChartControlledTargetBoxSelectionData I
        (F.sourceChart x) (F.boundarySourceChart x)
        ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q)
        ((F.cover x).targetLowerCorner q) ((F.cover x).targetUpperCorner q)
        ((F.cover x).targetPoint q) (targetSet x q)
  /-- Selected auxiliary boxes for the controlled later target boxes. -/
  controlledTargetSelectedBox :
    ∀ x, x ∈ F.activeCharts →
      ∀ q, q ∈ (F.cover x).activePieces →
        boundaryChartSelectedBox I (F.boundarySourceChart x)
          (F.boundaryTargetChart x q) ω
          ((controlledTarget x q).laterLowerCorner)
          ((controlledTarget x q).laterUpperCorner)
  /-- M8 assembly fields for the controlled target-image family. -/
  m8Fields :
    BoundaryChartControlledTargetImageFamily.M8ResolvedFields
      (F.toControlledTargetImageFamily targetSet controlledTarget
        controlledTargetSelectedBox)
      selectedPartition orientedBoundaryAtlas
  /-- Global bulk integral represented by the source pieces. -/
  globalBulkIntegral : Real
  /-- Global boundary integral represented by the source pieces. -/
  globalBoundaryIntegral : Real
  /-- Bulk reconstruction from the same source boxes. -/
  globalBulkIntegral_eq_projectLocalSum :
    globalBulkIntegral =
      Finset.sum F.activeCharts fun x =>
        Finset.sum ((F.cover x).activePieces) fun q =>
          projectLocalBulkIntegral I (F.sourceChart x) (F.boundarySourceChart x) ω
            ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q)
  /-- Project-local Stokes on the source boxes. -/
  localProjectStokes :
    ∀ x, x ∈ F.activeCharts →
      ∀ q, q ∈ (F.cover x).activePieces →
        projectLocalBulkIntegral I (F.sourceChart x) (F.boundarySourceChart x) ω
            ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q) =
          projectLocalBoundaryIntegral I (F.sourceChart x) (F.boundarySourceChart x) ω
            ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q)
  /-- Boundary chart-change cancellation into the controlled M8 partition term. -/
  chartChangeCancellation :
    (Finset.sum F.activeCharts fun x =>
        Finset.sum ((F.cover x).activePieces) fun q =>
          projectLocalBoundaryIntegral I (F.sourceChart x) (F.boundarySourceChart x) ω
            ((F.cover x).sourceLowerCorner q) ((F.cover x).sourceUpperCorner q)) =
      Finset.sum F.activeCharts fun x =>
        Finset.sum ((F.cover x).activePieces) fun q =>
          m8Fields.boundaryPartitionTerm x q
  /-- Boundary reconstruction from the controlled M8 partition term. -/
  globalBoundaryIntegral_eq_boundaryPartitionSum :
    globalBoundaryIntegral =
      Finset.sum F.activeCharts fun x =>
        Finset.sum ((F.cover x).activePieces) fun q =>
          m8Fields.boundaryPartitionTerm x q

namespace ControlledRouteFields

variable {F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω M Piece}
variable (D : ControlledRouteFields F selectedPartition orientedBoundaryAtlas)

/-- Controlled target-image family determined by the route fields. -/
def controlledFamily :
    BoundaryChartControlledTargetImageFamily I ω M Piece :=
  F.toControlledTargetImageFamily D.targetSet D.controlledTarget
    D.controlledTargetSelectedBox

/-- Controlled target input in the exact M8 shape. -/
def toM8BoundaryControlledTargetInput :
    M8BoundaryControlledTargetInput I ω selectedPartition
      orientedBoundaryAtlas Piece where
  family := D.controlledFamily
  fields := D.m8Fields

/-- The plain M8 target-image input behind the controlled input. -/
def toM8TargetImageInput :
    M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  D.toM8BoundaryControlledTargetInput.toM8TargetImageInput

/-- Project-local constructor data aligned with the controlled target-image input. -/
def toProjectLocalConstructorData :
    ProjectLocalConstructorData I ω M Piece where
  activeCharts := F.activeCharts
  localPieces := fun x => (F.cover x).activePieces
  sourceChart := fun x _ => F.sourceChart x
  targetChart := fun x _ => F.boundarySourceChart x
  lowerCorner := fun x q => (F.cover x).sourceLowerCorner q
  upperCorner := fun x q => (F.cover x).sourceUpperCorner q
  boundaryPartitionTerm := D.m8Fields.boundaryPartitionTerm
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral
  globalBulkIntegral_eq_projectLocalSum :=
    D.globalBulkIntegral_eq_projectLocalSum
  localProjectStokes := D.localProjectStokes
  chartChangeCancellation := D.chartChangeCancellation
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    D.globalBoundaryIntegral_eq_boundaryPartitionSum

/-- Final project-local package aligned with the controlled target input. -/
def toProjectLocalGlobalStokesData :
    ProjectLocalGlobalStokesData I ω M Piece :=
  D.toProjectLocalConstructorData.toProjectLocalGlobalStokesData

@[simp]
theorem controlledFamily_activeCharts :
    D.controlledFamily.activeCharts = F.activeCharts :=
  rfl

@[simp]
theorem controlledFamily_localPieces :
    D.controlledFamily.localPieces = fun x => (F.cover x).activePieces :=
  rfl

@[simp]
theorem toM8BoundaryControlledTargetInput_family :
    D.toM8BoundaryControlledTargetInput.family = D.controlledFamily :=
  rfl

@[simp]
theorem toM8BoundaryControlledTargetInput_fields :
    D.toM8BoundaryControlledTargetInput.fields = D.m8Fields :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_activeCharts :
    D.toM8TargetImageInput.targetImages.activeCharts = F.activeCharts :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundaryPieces :
    D.toM8TargetImageInput.targetImages.boundaryPieces =
      fun x => (F.cover x).activePieces :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceChart :
    D.toM8TargetImageInput.targetImages.sourceChart =
      fun x _ => F.sourceChart x :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundarySourceChart :
    D.toM8TargetImageInput.targetImages.boundarySourceChart =
      fun x _ => F.boundarySourceChart x :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceLowerCorner :
    D.toM8TargetImageInput.targetImages.sourceLowerCorner =
      fun x q => (F.cover x).sourceLowerCorner q :=
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceUpperCorner :
    D.toM8TargetImageInput.targetImages.sourceUpperCorner =
      fun x q => (F.cover x).sourceUpperCorner q :=
  rfl

@[simp]
theorem toProjectLocalConstructorData_boundaryPartitionTerm :
    D.toProjectLocalConstructorData.boundaryPartitionTerm =
      D.m8Fields.boundaryPartitionTerm :=
  rfl

/-- Source-alignment fields for the controlled target-cover route. -/
def toBoundarySourceTargetImageAlignmentFields :
    BoundarySourceTargetImageAlignmentFields D.toM8TargetImageInput
      D.toProjectLocalGlobalStokesData where
  activeCharts_eq_targetImages := rfl
  localPieces_eq_targetImages := fun _ => rfl
  sourceChart_eq_targetImages := fun _ _ => rfl
  targetChart_eq_targetImages := fun _ _ => rfl
  lowerCorner_eq_targetImages := fun _ _ => rfl
  upperCorner_eq_targetImages := fun _ _ => rfl

/-- Source/project-local alignment for the controlled target-cover route. -/
def toBoundarySourceProjectLocalAlignment :
    BoundarySourceProjectLocalAlignment D.toM8TargetImageInput
      D.toProjectLocalGlobalStokesData :=
  D.toBoundarySourceTargetImageAlignmentFields.toBoundarySourceProjectLocalAlignment

/-- Canonical boundary route from controlled local-openness target-cover data. -/
def toBoundaryCanonicalRouteMeasureInput
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        D.toProjectLocalGlobalStokesData)
    (projectLocal :
      ProjectLocalBoundaryMeasureConstructorInput
        D.toProjectLocalGlobalStokesData) :
    BoundaryCanonicalRouteMeasureInput D.toM8TargetImageInput
      D.toProjectLocalGlobalStokesData :=
  BoundaryCanonicalRouteMeasureInput.ofTargetImageAlignmentFields
    faceContinuity projectLocal D.toBoundarySourceTargetImageAlignmentFields

@[simp]
theorem toBoundaryCanonicalRouteMeasureInput_sourceAlignment
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        D.toProjectLocalGlobalStokesData)
    (projectLocal :
      ProjectLocalBoundaryMeasureConstructorInput
        D.toProjectLocalGlobalStokesData) :
    (D.toBoundaryCanonicalRouteMeasureInput faceContinuity projectLocal).sourceAlignment =
      D.toBoundarySourceProjectLocalAlignment :=
  rfl

/-- Project-local Stokes exposed from controlled target-cover route fields. -/
theorem stokes :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  D.toProjectLocalConstructorData.stokes

end ControlledRouteFields

end BoundaryChartLocalOpennessTargetCoverMegaFamily

/-! ## IFT target-cover route -/

namespace BoundaryChartIFTTargetCoverMegaFamily

variable (F : BoundaryChartIFTTargetCoverMegaFamily I ω M Piece)

/-- IFT route fields are local-openness route fields after forgetting IFT data. -/
abbrev BoundarySourceRouteFields
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω M Piece)
    (selectedPartition : SelectedBoxPartitionOfUnity I ω)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M) :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.BoundarySourceRouteFields
    F.toLocalOpennessMegaFamily selectedPartition orientedBoundaryAtlas

/-- IFT controlled route fields are the controlled local-openness route fields. -/
abbrev ControlledRouteFields
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω M Piece)
    (selectedPartition : SelectedBoxPartitionOfUnity I ω)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M) :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.ControlledRouteFields
    F.toLocalOpennessMegaFamily selectedPartition orientedBoundaryAtlas

/-- M8 resolved input from an IFT target-cover route package. -/
def toM8ResolvedInputOfBoundarySourceRouteFields
    (D : BoundarySourceRouteFields F selectedPartition orientedBoundaryAtlas) :
    M8TargetImageResolvedInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.BoundarySourceRouteFields.toM8ResolvedInput D

/-- M8 target-image input from an IFT target-cover route package. -/
def toM8TargetImageInputOfBoundarySourceRouteFields
    (D : BoundarySourceRouteFields F selectedPartition orientedBoundaryAtlas) :
    M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.BoundarySourceRouteFields.toM8TargetImageInput D

/-- Project-local data from an IFT target-cover route package. -/
def toProjectLocalGlobalStokesDataOfBoundarySourceRouteFields
    (D : BoundarySourceRouteFields F selectedPartition orientedBoundaryAtlas) :
    ProjectLocalGlobalStokesData I ω M Piece :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.BoundarySourceRouteFields.toProjectLocalGlobalStokesData D

/-- Source-alignment fields from an IFT target-cover route package. -/
def toBoundarySourceTargetImageAlignmentFieldsOfBoundarySourceRouteFields
    (D : BoundarySourceRouteFields F selectedPartition orientedBoundaryAtlas) :
    BoundarySourceTargetImageAlignmentFields
      (F.toM8TargetImageInputOfBoundarySourceRouteFields D)
      (F.toProjectLocalGlobalStokesDataOfBoundarySourceRouteFields D) :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.BoundarySourceRouteFields.toBoundarySourceTargetImageAlignmentFields D

/-- Canonical boundary route from IFT target-cover source fields. -/
def toBoundaryCanonicalRouteMeasureInputOfBoundarySourceRouteFields
    (D : BoundarySourceRouteFields F selectedPartition orientedBoundaryAtlas)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        (F.toProjectLocalGlobalStokesDataOfBoundarySourceRouteFields D))
    (projectLocal :
      ProjectLocalBoundaryMeasureConstructorInput
        (F.toProjectLocalGlobalStokesDataOfBoundarySourceRouteFields D)) :
    BoundaryCanonicalRouteMeasureInput
      (F.toM8TargetImageInputOfBoundarySourceRouteFields D)
      (F.toProjectLocalGlobalStokesDataOfBoundarySourceRouteFields D) :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.BoundarySourceRouteFields.toBoundaryCanonicalRouteMeasureInput
    D faceContinuity projectLocal

/-- Controlled M8 input from an IFT target-cover controlled route package. -/
def toM8BoundaryControlledTargetInputOfControlledRouteFields
    (D : ControlledRouteFields F selectedPartition orientedBoundaryAtlas) :
    M8BoundaryControlledTargetInput I ω selectedPartition
      orientedBoundaryAtlas Piece :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.ControlledRouteFields.toM8BoundaryControlledTargetInput D

/-- Plain M8 target-image input from an IFT controlled route package. -/
def toM8TargetImageInputOfControlledRouteFields
    (D : ControlledRouteFields F selectedPartition orientedBoundaryAtlas) :
    M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.ControlledRouteFields.toM8TargetImageInput D

/-- Project-local data from an IFT controlled route package. -/
def toProjectLocalGlobalStokesDataOfControlledRouteFields
    (D : ControlledRouteFields F selectedPartition orientedBoundaryAtlas) :
    ProjectLocalGlobalStokesData I ω M Piece :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.ControlledRouteFields.toProjectLocalGlobalStokesData D

/-- Source-alignment fields from an IFT controlled route package. -/
def toBoundarySourceTargetImageAlignmentFieldsOfControlledRouteFields
    (D : ControlledRouteFields F selectedPartition orientedBoundaryAtlas) :
    BoundarySourceTargetImageAlignmentFields
      (F.toM8TargetImageInputOfControlledRouteFields D)
      (F.toProjectLocalGlobalStokesDataOfControlledRouteFields D) :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.ControlledRouteFields.toBoundarySourceTargetImageAlignmentFields D

/-- Canonical boundary route from IFT controlled target-cover source fields. -/
def toBoundaryCanonicalRouteMeasureInputOfControlledRouteFields
    (D : ControlledRouteFields F selectedPartition orientedBoundaryAtlas)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        (F.toProjectLocalGlobalStokesDataOfControlledRouteFields D))
    (projectLocal :
      ProjectLocalBoundaryMeasureConstructorInput
        (F.toProjectLocalGlobalStokesDataOfControlledRouteFields D)) :
    BoundaryCanonicalRouteMeasureInput
      (F.toM8TargetImageInputOfControlledRouteFields D)
      (F.toProjectLocalGlobalStokesDataOfControlledRouteFields D) :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.ControlledRouteFields.toBoundaryCanonicalRouteMeasureInput
    D faceContinuity projectLocal

@[simp]
theorem toM8TargetImageInputOfBoundarySourceRouteFields_activeCharts
    (D : BoundarySourceRouteFields F selectedPartition orientedBoundaryAtlas) :
    (F.toM8TargetImageInputOfBoundarySourceRouteFields D).targetImages.activeCharts =
      F.activeCharts :=
  rfl

@[simp]
theorem toM8TargetImageInputOfBoundarySourceRouteFields_boundaryPieces
    (D : BoundarySourceRouteFields F selectedPartition orientedBoundaryAtlas) :
    (F.toM8TargetImageInputOfBoundarySourceRouteFields D).targetImages.boundaryPieces =
      fun x => (F.cover x).activePieces :=
  rfl

@[simp]
theorem toM8TargetImageInputOfControlledRouteFields_activeCharts
    (D : ControlledRouteFields F selectedPartition orientedBoundaryAtlas) :
    (F.toM8TargetImageInputOfControlledRouteFields D).targetImages.activeCharts =
      F.activeCharts :=
  rfl

@[simp]
theorem toM8BoundaryControlledTargetInputOfControlledRouteFields_family_activeCharts
    (D : ControlledRouteFields F selectedPartition orientedBoundaryAtlas) :
    (F.toM8BoundaryControlledTargetInputOfControlledRouteFields D).family.activeCharts =
      F.activeCharts :=
  rfl

end BoundaryChartIFTTargetCoverMegaFamily

end BoundaryUnifiedFromTargetCoverMegaAuto

end Stokes

end
