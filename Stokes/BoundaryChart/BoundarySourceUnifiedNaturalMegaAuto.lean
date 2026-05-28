import Stokes.BoundaryChart.BoundaryUnifiedFromTargetCoverMegaAuto
import Stokes.BoundaryChart.BoundaryTargetCoverMegaAuto
import Stokes.Global.BoundaryOrientationMegaAuto

/-!
# Natural boundary-source unified mega packages

This file pushes the target-cover side one step closer to the natural compact
support Stokes input.

The source-shrink route can build `BoundarySourceAlignmentUnifiedData` directly:
its family already has the shrunken source boxes, target boxes, selected boxes,
and local-homeomorphism data required by the M8 target-image API.  Local
openness / IFT cover families do not themselves contain that source-shrink
local-homeomorphism data, so the strongest honest package there records:

* the cover-family route fields already produced by
  `BoundaryUnifiedFromTargetCoverMegaAuto`;
* a compatible `BoundarySourceAlignmentUnifiedData`;
* the equality/projection data identifying the M8 target-image and
  project-local source packages.

Downstream endpoint code can now take a single cover-family package and project
the controlled target, M8 target-image input, project-local data, source
alignment, and `NaturalBulkEndpointUnifiedInput` / common data constructors.
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

section BoundarySourceUnifiedNaturalMegaAuto

universe u w p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Piece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/-! ## Source-shrink families: direct unified-data constructor -/

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphFamily

variable
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I ω M Piece)
variable {selectedPartition : SelectedBoxPartitionOfUnity I ω}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/--
The natural source-shrink route fields.

This is the exact data needed to make a `BoundarySourceAlignmentUnifiedData`.
It is deliberately close to that final structure, but keeps the source-shrink
family `F` visible so callers can recover the geometric origin of every field.
-/
structure BoundarySourceUnifiedRouteFields
    (F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I ω M Piece)
    (selectedPartition : SelectedBoxPartitionOfUnity I ω)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M) where
  /-- M8-resolved fields attached to the source-shrink family. -/
  m8Fields : F.M8ResolvedFields selectedPartition orientedBoundaryAtlas
  /-- Global bulk integral represented by the project-local source pieces. -/
  globalBulkIntegral : Real
  /-- Global boundary integral represented by the boundary partition terms. -/
  globalBoundaryIntegral : Real
  /-- Bulk reconstruction from the source-shrink pieces. -/
  globalBulkIntegral_eq_projectLocalSum :
    globalBulkIntegral =
      Finset.sum F.activeCharts fun x =>
        Finset.sum (F.localPieces x) fun q =>
          projectLocalBulkIntegral I (F.sourceChart x q)
            (F.boundarySourceChart x q) ω
            (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
  /-- Project-local Stokes on every active source-shrink piece. -/
  localProjectStokes :
    ∀ x, x ∈ F.activeCharts →
      ∀ q, q ∈ F.localPieces x →
        projectLocalBulkIntegral I (F.sourceChart x q)
            (F.boundarySourceChart x q) ω
            (F.sourceLowerCorner x q) (F.sourceUpperCorner x q) =
          projectLocalBoundaryIntegral I (F.sourceChart x q)
            (F.boundarySourceChart x q) ω
            (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
  /-- Boundary chart-change cancellation into the M8 boundary partition term. -/
  chartChangeCancellation :
    (Finset.sum F.activeCharts fun x =>
        Finset.sum (F.localPieces x) fun q =>
          projectLocalBoundaryIntegral I (F.sourceChart x q)
            (F.boundarySourceChart x q) ω
            (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)) =
      Finset.sum F.activeCharts fun x =>
        Finset.sum (F.localPieces x) fun q =>
          m8Fields.boundaryPartitionTerm x q
  /-- Boundary reconstruction from the shared M8 boundary partition term. -/
  globalBoundaryIntegral_eq_boundaryPartitionSum :
    globalBoundaryIntegral =
      Finset.sum F.activeCharts fun x =>
        Finset.sum (F.localPieces x) fun q =>
          m8Fields.boundaryPartitionTerm x q

namespace BoundarySourceUnifiedRouteFields

variable {F : BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I ω M Piece}
variable
    (D :
      BoundarySourceUnifiedRouteFields F selectedPartition orientedBoundaryAtlas)

/-- Direct construction of unified boundary-source data from source-shrink fields. -/
def toBoundarySourceAlignmentUnifiedData :
    BoundarySourceAlignmentUnifiedData
      (I := I) (omega := ω)
      (selectedPartition := selectedPartition)
      (orientedBoundaryAtlas := orientedBoundaryAtlas)
      (BoundaryPiece := Piece) where
  family := F
  m8Fields := D.m8Fields
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral
  globalBulkIntegral_eq_projectLocalSum :=
    D.globalBulkIntegral_eq_projectLocalSum
  localProjectStokes := D.localProjectStokes
  chartChangeCancellation := D.chartChangeCancellation
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    D.globalBoundaryIntegral_eq_boundaryPartitionSum

/-- M8 target-image input obtained from the source-shrink unified route. -/
def toM8TargetImageInput :
    M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  D.toBoundarySourceAlignmentUnifiedData.toM8TargetImageInput

/-- Controlled-target input obtained from the source-shrink unified route. -/
def toM8BoundaryControlledTargetInput :
    M8BoundaryControlledTargetInput I ω selectedPartition
      orientedBoundaryAtlas Piece :=
  D.toBoundarySourceAlignmentUnifiedData.toM8BoundaryControlledTargetInput

/-- Project-local Stokes package obtained from the source-shrink unified route. -/
def toProjectLocalGlobalStokesData :
    ProjectLocalGlobalStokesData I ω M Piece :=
  D.toBoundarySourceAlignmentUnifiedData.toProjectLocalGlobalStokesData

/-- Source/project-local alignment generated by the source-shrink unified route. -/
def toBoundarySourceProjectLocalAlignment :
    BoundarySourceProjectLocalAlignment D.toM8TargetImageInput
      D.toProjectLocalGlobalStokesData :=
  D.toBoundarySourceAlignmentUnifiedData.toBoundarySourceProjectLocalAlignment

@[simp]
theorem toBoundarySourceAlignmentUnifiedData_family :
    D.toBoundarySourceAlignmentUnifiedData.family = F := by
  rfl

@[simp]
theorem toBoundarySourceAlignmentUnifiedData_m8Fields :
    D.toBoundarySourceAlignmentUnifiedData.m8Fields = D.m8Fields := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_activeCharts :
    D.toM8TargetImageInput.targetImages.activeCharts = F.activeCharts := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundaryPieces :
    D.toM8TargetImageInput.targetImages.boundaryPieces = F.localPieces := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceChart :
    D.toM8TargetImageInput.targetImages.sourceChart = F.sourceChart := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundarySourceChart :
    D.toM8TargetImageInput.targetImages.boundarySourceChart =
      F.boundarySourceChart := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceLowerCorner :
    D.toM8TargetImageInput.targetImages.sourceLowerCorner =
      F.sourceLowerCorner := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceUpperCorner :
    D.toM8TargetImageInput.targetImages.sourceUpperCorner =
      F.sourceUpperCorner := by
  rfl

@[simp]
theorem toProjectLocalGlobalStokesData_activeCharts :
    D.toProjectLocalGlobalStokesData.activeCharts = F.activeCharts := by
  rfl

@[simp]
theorem toProjectLocalGlobalStokesData_localPieces :
    D.toProjectLocalGlobalStokesData.localPieces = F.localPieces := by
  rfl

@[simp]
theorem toProjectLocalGlobalStokesData_sourceChart :
    D.toProjectLocalGlobalStokesData.sourceChart = F.sourceChart := by
  rfl

@[simp]
theorem toProjectLocalGlobalStokesData_targetChart :
    D.toProjectLocalGlobalStokesData.targetChart = F.boundarySourceChart := by
  rfl

@[simp]
theorem toProjectLocalGlobalStokesData_lowerCorner :
    D.toProjectLocalGlobalStokesData.lowerCorner = F.sourceLowerCorner := by
  rfl

@[simp]
theorem toProjectLocalGlobalStokesData_upperCorner :
    D.toProjectLocalGlobalStokesData.upperCorner = F.sourceUpperCorner := by
  rfl

@[simp]
theorem toM8BoundaryControlledTargetInput_toM8TargetImageInput :
    D.toM8BoundaryControlledTargetInput.toM8TargetImageInput =
      D.toM8TargetImageInput := by
  rfl

end BoundarySourceUnifiedRouteFields

end BoundaryChartSourceShrinkOpenPartialHomeomorphFamily

/-! ## Local-openness cover families with compatible unified data -/

namespace BoundaryChartLocalOpennessTargetCoverMegaFamily

variable
    (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω M Piece)
variable {selectedPartition : SelectedBoxPartitionOfUnity I ω}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/--
Natural local-openness boundary-source package.

The route fields come directly from the local-openness cover family.  The
`boundaryUnified` field is the source-shrink/unified source chosen downstream;
the equalities assert that the unified source and the local-openness cover route
present the same M8 target-image input and the same project-local source data.
-/
structure BoundarySourceUnifiedNaturalInput
    (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω M Piece)
    (selectedPartition : SelectedBoxPartitionOfUnity I ω)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M) where
  /-- Local-openness cover route fields. -/
  routeFields : F.BoundarySourceRouteFields selectedPartition orientedBoundaryAtlas
  /-- Compatible unified source package, usually produced by a source-shrink route. -/
  boundaryUnified :
    BoundarySourceAlignmentUnifiedData
      (I := I) (omega := ω)
      (selectedPartition := selectedPartition)
      (orientedBoundaryAtlas := orientedBoundaryAtlas)
      (BoundaryPiece := Piece)
  /-- The unified source presents the same M8 target-image input. -/
  targetImageInput_eq :
    boundaryUnified.toM8TargetImageInput = routeFields.toM8TargetImageInput
  /-- The unified source presents the same project-local source data. -/
  projectLocal_eq :
    boundaryUnified.toProjectLocalGlobalStokesData =
      routeFields.toProjectLocalGlobalStokesData

namespace BoundarySourceUnifiedNaturalInput

variable {F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω M Piece}
variable
    (D :
      BoundarySourceUnifiedNaturalInput F selectedPartition orientedBoundaryAtlas)

/-- Route M8 target-image input from the local-openness cover fields. -/
def toM8TargetImageInput :
    M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  D.routeFields.toM8TargetImageInput

/-- Route M8 resolved input from the local-openness cover fields. -/
def toM8ResolvedInput :
    M8TargetImageResolvedInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  D.routeFields.toM8ResolvedInput

/-- Project-local data from the local-openness cover fields. -/
def toProjectLocalGlobalStokesData :
    ProjectLocalGlobalStokesData I ω M Piece :=
  D.routeFields.toProjectLocalGlobalStokesData

/-- Project-local constructor data from the local-openness cover fields. -/
def toProjectLocalConstructorData :
    ProjectLocalConstructorData I ω M Piece :=
  D.routeFields.toProjectLocalConstructorData

/-- Source-alignment fields generated from the local-openness cover fields. -/
def toBoundarySourceTargetImageAlignmentFields :
    BoundarySourceTargetImageAlignmentFields D.toM8TargetImageInput
      D.toProjectLocalGlobalStokesData :=
  D.routeFields.toBoundarySourceTargetImageAlignmentFields

/-- Source/project-local alignment generated from the local-openness cover fields. -/
def toBoundarySourceProjectLocalAlignment :
    BoundarySourceProjectLocalAlignment D.toM8TargetImageInput
      D.toProjectLocalGlobalStokesData :=
  D.routeFields.toBoundarySourceProjectLocalAlignment

/-- Controlled target input supplied by the compatible unified source. -/
def toM8BoundaryControlledTargetInput :
    M8BoundaryControlledTargetInput I ω selectedPartition
      orientedBoundaryAtlas Piece :=
  D.boundaryUnified.toM8BoundaryControlledTargetInput

/-- Boundary canonical route from the local-openness cover route fields. -/
def toBoundaryCanonicalRouteMeasureInput
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        D.toProjectLocalGlobalStokesData)
    (projectLocal :
      ProjectLocalBoundaryMeasureConstructorInput
        D.toProjectLocalGlobalStokesData) :
    BoundaryCanonicalRouteMeasureInput D.toM8TargetImageInput
      D.toProjectLocalGlobalStokesData :=
  D.routeFields.toBoundaryCanonicalRouteMeasureInput faceContinuity projectLocal

@[simp]
theorem toM8TargetImageInput_targetImages_activeCharts :
    D.toM8TargetImageInput.targetImages.activeCharts = F.activeCharts := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundaryPieces :
    D.toM8TargetImageInput.targetImages.boundaryPieces =
      fun x => (F.cover x).activePieces := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceChart :
    D.toM8TargetImageInput.targetImages.sourceChart =
      fun x _ => F.sourceChart x := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundarySourceChart :
    D.toM8TargetImageInput.targetImages.boundarySourceChart =
      fun x _ => F.boundarySourceChart x := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceLowerCorner :
    D.toM8TargetImageInput.targetImages.sourceLowerCorner =
      fun x q => (F.cover x).sourceLowerCorner q := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceUpperCorner :
    D.toM8TargetImageInput.targetImages.sourceUpperCorner =
      fun x q => (F.cover x).sourceUpperCorner q := by
  rfl

@[simp]
theorem toProjectLocalConstructorData_activeCharts :
    D.toProjectLocalConstructorData.activeCharts = F.activeCharts := by
  rfl

@[simp]
theorem toProjectLocalConstructorData_localPieces :
    D.toProjectLocalConstructorData.localPieces =
      fun x => (F.cover x).activePieces := by
  rfl

@[simp]
theorem toProjectLocalConstructorData_sourceChart :
    D.toProjectLocalConstructorData.sourceChart =
      fun x _ => F.sourceChart x := by
  rfl

@[simp]
theorem toProjectLocalConstructorData_targetChart :
    D.toProjectLocalConstructorData.targetChart =
      fun x _ => F.boundarySourceChart x := by
  rfl

@[simp]
theorem toProjectLocalConstructorData_lowerCorner :
    D.toProjectLocalConstructorData.lowerCorner =
      fun x q => (F.cover x).sourceLowerCorner q := by
  rfl

@[simp]
theorem toProjectLocalConstructorData_upperCorner :
    D.toProjectLocalConstructorData.upperCorner =
      fun x q => (F.cover x).sourceUpperCorner q := by
  rfl

@[simp]
theorem boundaryUnified_toM8TargetImageInput :
    D.boundaryUnified.toM8TargetImageInput = D.toM8TargetImageInput :=
  D.targetImageInput_eq

@[simp]
theorem boundaryUnified_toProjectLocalGlobalStokesData :
    D.boundaryUnified.toProjectLocalGlobalStokesData =
      D.toProjectLocalGlobalStokesData :=
  D.projectLocal_eq

@[simp]
theorem toM8BoundaryControlledTargetInput_toM8TargetImageInput :
    D.toM8BoundaryControlledTargetInput.toM8TargetImageInput =
      D.boundaryUnified.toM8TargetImageInput := by
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
      D.toBoundarySourceProjectLocalAlignment := by
  rfl

/-- Package the compatible unified source as a natural endpoint input. -/
def toNaturalBulkEndpointUnifiedInput
    {ρ : SmoothPartitionOfUnity M I M univ}
    {μ : Measure (Fin (n + 1) → Real)}
    [IsFiniteMeasureOnCompacts μ] [IsManifold I 1 M]
    {chartBoxes : NaturalFiniteActiveChartBoxSelectionData I ω ρ}
    (D :
      BoundarySourceUnifiedNaturalInput F chartBoxes.selectedPartition
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
  orientedBoundaryAtlas.toNaturalBulkEndpointUnifiedInput chartBoxes
    D.boundaryUnified localized measure_eq_volume
    boundaryFaceContinuity boundaryChartChange

/-- Common endpoint data projected from the natural local-openness package. -/
def toNaturalBulkEndpointCommonData
    {ρ : SmoothPartitionOfUnity M I M univ}
    {μ : Measure (Fin (n + 1) → Real)}
    [IsFiniteMeasureOnCompacts μ] [IsManifold I 1 M]
    {chartBoxes : NaturalFiniteActiveChartBoxSelectionData I ω ρ}
    (D :
      BoundarySourceUnifiedNaturalInput F chartBoxes.selectedPartition
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
  (D.toNaturalBulkEndpointUnifiedInput localized measure_eq_volume
    boundaryFaceContinuity boundaryChartChange).toCommonData

@[simp]
theorem toNaturalBulkEndpointUnifiedInput_boundaryUnified
    {ρ : SmoothPartitionOfUnity M I M univ}
    {μ : Measure (Fin (n + 1) → Real)}
    [IsFiniteMeasureOnCompacts μ] [IsManifold I 1 M]
    {chartBoxes : NaturalFiniteActiveChartBoxSelectionData I ω ρ}
    (D :
      BoundarySourceUnifiedNaturalInput F chartBoxes.selectedPartition
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
theorem toNaturalBulkEndpointCommonData_boundaryUnified
    {ρ : SmoothPartitionOfUnity M I M univ}
    {μ : Measure (Fin (n + 1) → Real)}
    [IsFiniteMeasureOnCompacts μ] [IsManifold I 1 M]
    {chartBoxes : NaturalFiniteActiveChartBoxSelectionData I ω ρ}
    (D :
      BoundarySourceUnifiedNaturalInput F chartBoxes.selectedPartition
        orientedBoundaryAtlas)
    (localized : LocalizedInteriorM8Fields I ω chartBoxes.selectedPartition)
    (measure_eq_volume : μ = volume)
    (boundaryFaceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        D.boundaryUnified.toProjectLocalGlobalStokesData)
    (boundaryChartChange :
      BoundaryChartChangeSelectedFamilyData
        D.boundaryUnified.toProjectLocalGlobalStokesData) :
    (D.toNaturalBulkEndpointCommonData localized measure_eq_volume
      boundaryFaceContinuity boundaryChartChange).boundaryUnified =
      D.boundaryUnified := by
  rfl

end BoundarySourceUnifiedNaturalInput

/-! ### Controlled-target cover fields with compatible unified data -/

/--
Controlled local-openness package with a compatible unified source.

This records the stronger controlled-target M8 fields produced directly from
the cover family while still exposing the unified source needed by the natural
endpoint route.
-/
structure ControlledBoundarySourceUnifiedNaturalInput
    (F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω M Piece)
    (selectedPartition : SelectedBoxPartitionOfUnity I ω)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M) where
  /-- Controlled route fields from the local-openness cover family. -/
  controlledRouteFields :
    F.ControlledRouteFields selectedPartition orientedBoundaryAtlas
  /-- Compatible unified source package. -/
  boundaryUnified :
    BoundarySourceAlignmentUnifiedData
      (I := I) (omega := ω)
      (selectedPartition := selectedPartition)
      (orientedBoundaryAtlas := orientedBoundaryAtlas)
      (BoundaryPiece := Piece)
  /-- The controlled route and unified source expose the same target-image input. -/
  targetImageInput_eq :
    boundaryUnified.toM8BoundaryControlledTargetInput.toM8TargetImageInput =
      controlledRouteFields.toM8TargetImageInput
  /-- The controlled route and unified source expose the same project-local data. -/
  projectLocal_eq :
    boundaryUnified.toProjectLocalGlobalStokesData =
      controlledRouteFields.toProjectLocalGlobalStokesData

namespace ControlledBoundarySourceUnifiedNaturalInput

variable {F : BoundaryChartLocalOpennessTargetCoverMegaFamily I ω M Piece}
variable
    (D :
      ControlledBoundarySourceUnifiedNaturalInput F selectedPartition
        orientedBoundaryAtlas)

/-- Controlled M8 input from the cover route. -/
def toControlledRouteM8BoundaryControlledTargetInput :
    M8BoundaryControlledTargetInput I ω selectedPartition
      orientedBoundaryAtlas Piece :=
  D.controlledRouteFields.toM8BoundaryControlledTargetInput

/-- Controlled M8 input from the compatible unified source. -/
def toUnifiedM8BoundaryControlledTargetInput :
    M8BoundaryControlledTargetInput I ω selectedPartition
      orientedBoundaryAtlas Piece :=
  D.boundaryUnified.toM8BoundaryControlledTargetInput

/-- M8 target-image input from the controlled cover route. -/
def toM8TargetImageInput :
    M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  D.controlledRouteFields.toM8TargetImageInput

/-- Project-local data from the controlled cover route. -/
def toProjectLocalGlobalStokesData :
    ProjectLocalGlobalStokesData I ω M Piece :=
  D.controlledRouteFields.toProjectLocalGlobalStokesData

/-- Source/project-local alignment from the controlled cover route. -/
def toBoundarySourceProjectLocalAlignment :
    BoundarySourceProjectLocalAlignment D.toM8TargetImageInput
      D.toProjectLocalGlobalStokesData :=
  D.controlledRouteFields.toBoundarySourceProjectLocalAlignment

@[simp]
theorem toM8TargetImageInput_targetImages_activeCharts :
    D.toM8TargetImageInput.targetImages.activeCharts = F.activeCharts := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundaryPieces :
    D.toM8TargetImageInput.targetImages.boundaryPieces =
      fun x => (F.cover x).activePieces := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceChart :
    D.toM8TargetImageInput.targetImages.sourceChart =
      fun x _ => F.sourceChart x := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundarySourceChart :
    D.toM8TargetImageInput.targetImages.boundarySourceChart =
      fun x _ => F.boundarySourceChart x := by
  rfl

@[simp]
theorem boundaryUnified_toM8BoundaryControlledTargetInput_toM8TargetImageInput :
    D.boundaryUnified.toM8BoundaryControlledTargetInput.toM8TargetImageInput =
      D.toM8TargetImageInput :=
  D.targetImageInput_eq

@[simp]
theorem boundaryUnified_toProjectLocalGlobalStokesData :
    D.boundaryUnified.toProjectLocalGlobalStokesData =
      D.toProjectLocalGlobalStokesData :=
  D.projectLocal_eq

/-- Package the controlled local-openness source as a natural endpoint input. -/
def toNaturalBulkEndpointUnifiedInput
    {ρ : SmoothPartitionOfUnity M I M univ}
    {μ : Measure (Fin (n + 1) → Real)}
    [IsFiniteMeasureOnCompacts μ] [IsManifold I 1 M]
    {chartBoxes : NaturalFiniteActiveChartBoxSelectionData I ω ρ}
    (D :
      ControlledBoundarySourceUnifiedNaturalInput F chartBoxes.selectedPartition
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
  orientedBoundaryAtlas.toNaturalBulkEndpointUnifiedInput chartBoxes
    D.boundaryUnified localized measure_eq_volume
    boundaryFaceContinuity boundaryChartChange

@[simp]
theorem toNaturalBulkEndpointUnifiedInput_boundaryUnified
    {ρ : SmoothPartitionOfUnity M I M univ}
    {μ : Measure (Fin (n + 1) → Real)}
    [IsFiniteMeasureOnCompacts μ] [IsManifold I 1 M]
    {chartBoxes : NaturalFiniteActiveChartBoxSelectionData I ω ρ}
    (D :
      ControlledBoundarySourceUnifiedNaturalInput F chartBoxes.selectedPartition
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

end ControlledBoundarySourceUnifiedNaturalInput

end BoundaryChartLocalOpennessTargetCoverMegaFamily

/-! ## IFT cover families: parallel package through local-openness forgetting -/

namespace BoundaryChartIFTTargetCoverMegaFamily

variable
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω M Piece)
variable {selectedPartition : SelectedBoxPartitionOfUnity I ω}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/-- IFT natural source package, implemented by forgetting to local-openness. -/
abbrev BoundarySourceUnifiedNaturalInput
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω M Piece)
    (selectedPartition : SelectedBoxPartitionOfUnity I ω)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M) :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.BoundarySourceUnifiedNaturalInput
    F.toLocalOpennessMegaFamily selectedPartition orientedBoundaryAtlas

/-- IFT controlled natural source package, implemented by forgetting to local-openness. -/
abbrev ControlledBoundarySourceUnifiedNaturalInput
    (F : BoundaryChartIFTTargetCoverMegaFamily I ω M Piece)
    (selectedPartition : SelectedBoxPartitionOfUnity I ω)
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M) :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.ControlledBoundarySourceUnifiedNaturalInput
    F.toLocalOpennessMegaFamily selectedPartition orientedBoundaryAtlas

namespace BoundarySourceUnifiedNaturalInput

variable {F : BoundaryChartIFTTargetCoverMegaFamily I ω M Piece}
variable
    (D :
      BoundarySourceUnifiedNaturalInput F selectedPartition orientedBoundaryAtlas)

/-- M8 target-image input from the IFT cover route. -/
def toM8TargetImageInput :
    M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.BoundarySourceUnifiedNaturalInput.toM8TargetImageInput D

/-- Project-local data from the IFT cover route. -/
def toProjectLocalGlobalStokesData :
    ProjectLocalGlobalStokesData I ω M Piece :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.BoundarySourceUnifiedNaturalInput.toProjectLocalGlobalStokesData D

/-- Source/project-local alignment from the IFT cover route. -/
def toBoundarySourceProjectLocalAlignment :
    BoundarySourceProjectLocalAlignment D.toM8TargetImageInput
      D.toProjectLocalGlobalStokesData :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.BoundarySourceUnifiedNaturalInput.toBoundarySourceProjectLocalAlignment D

@[simp]
theorem toM8TargetImageInput_targetImages_activeCharts :
    D.toM8TargetImageInput.targetImages.activeCharts = F.activeCharts := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundaryPieces :
    D.toM8TargetImageInput.targetImages.boundaryPieces =
      fun x => (F.cover x).activePieces := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceChart :
    D.toM8TargetImageInput.targetImages.sourceChart =
      fun x _ => F.sourceChart x := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundarySourceChart :
    D.toM8TargetImageInput.targetImages.boundarySourceChart =
      fun x _ => F.boundarySourceChart x := by
  rfl

/-- Package the IFT source as a natural endpoint input. -/
def toNaturalBulkEndpointUnifiedInput
    {ρ : SmoothPartitionOfUnity M I M univ}
    {μ : Measure (Fin (n + 1) → Real)}
    [IsFiniteMeasureOnCompacts μ] [IsManifold I 1 M]
    {chartBoxes : NaturalFiniteActiveChartBoxSelectionData I ω ρ}
    (D :
      BoundarySourceUnifiedNaturalInput F chartBoxes.selectedPartition
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
  BoundaryChartLocalOpennessTargetCoverMegaFamily.BoundarySourceUnifiedNaturalInput.toNaturalBulkEndpointUnifiedInput
    D localized measure_eq_volume boundaryFaceContinuity boundaryChartChange

@[simp]
theorem toNaturalBulkEndpointUnifiedInput_boundaryUnified
    {ρ : SmoothPartitionOfUnity M I M univ}
    {μ : Measure (Fin (n + 1) → Real)}
    [IsFiniteMeasureOnCompacts μ] [IsManifold I 1 M]
    {chartBoxes : NaturalFiniteActiveChartBoxSelectionData I ω ρ}
    (D :
      BoundarySourceUnifiedNaturalInput F chartBoxes.selectedPartition
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

end BoundarySourceUnifiedNaturalInput

namespace ControlledBoundarySourceUnifiedNaturalInput

variable {F : BoundaryChartIFTTargetCoverMegaFamily I ω M Piece}
variable
    (D :
      ControlledBoundarySourceUnifiedNaturalInput F selectedPartition
        orientedBoundaryAtlas)

/-- Controlled M8 input from the IFT cover route. -/
def toControlledRouteM8BoundaryControlledTargetInput :
    M8BoundaryControlledTargetInput I ω selectedPartition
      orientedBoundaryAtlas Piece :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.ControlledBoundarySourceUnifiedNaturalInput.toControlledRouteM8BoundaryControlledTargetInput D

/-- M8 target-image input from the IFT controlled route. -/
def toM8TargetImageInput :
    M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas Piece :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.ControlledBoundarySourceUnifiedNaturalInput.toM8TargetImageInput D

/-- Project-local data from the IFT controlled route. -/
def toProjectLocalGlobalStokesData :
    ProjectLocalGlobalStokesData I ω M Piece :=
  BoundaryChartLocalOpennessTargetCoverMegaFamily.ControlledBoundarySourceUnifiedNaturalInput.toProjectLocalGlobalStokesData D

@[simp]
theorem toM8TargetImageInput_targetImages_activeCharts :
    D.toM8TargetImageInput.targetImages.activeCharts = F.activeCharts := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundaryPieces :
    D.toM8TargetImageInput.targetImages.boundaryPieces =
      fun x => (F.cover x).activePieces := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_sourceChart :
    D.toM8TargetImageInput.targetImages.sourceChart =
      fun x _ => F.sourceChart x := by
  rfl

@[simp]
theorem toM8TargetImageInput_targetImages_boundarySourceChart :
    D.toM8TargetImageInput.targetImages.boundarySourceChart =
      fun x _ => F.boundarySourceChart x := by
  rfl

/-- Package the controlled IFT source as a natural endpoint input. -/
def toNaturalBulkEndpointUnifiedInput
    {ρ : SmoothPartitionOfUnity M I M univ}
    {μ : Measure (Fin (n + 1) → Real)}
    [IsFiniteMeasureOnCompacts μ] [IsManifold I 1 M]
    {chartBoxes : NaturalFiniteActiveChartBoxSelectionData I ω ρ}
    (D :
      ControlledBoundarySourceUnifiedNaturalInput F chartBoxes.selectedPartition
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
  BoundaryChartLocalOpennessTargetCoverMegaFamily.ControlledBoundarySourceUnifiedNaturalInput.toNaturalBulkEndpointUnifiedInput
    D localized measure_eq_volume boundaryFaceContinuity boundaryChartChange

@[simp]
theorem toNaturalBulkEndpointUnifiedInput_boundaryUnified
    {ρ : SmoothPartitionOfUnity M I M univ}
    {μ : Measure (Fin (n + 1) → Real)}
    [IsFiniteMeasureOnCompacts μ] [IsManifold I 1 M]
    {chartBoxes : NaturalFiniteActiveChartBoxSelectionData I ω ρ}
    (D :
      ControlledBoundarySourceUnifiedNaturalInput F chartBoxes.selectedPartition
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

end ControlledBoundarySourceUnifiedNaturalInput

end BoundaryChartIFTTargetCoverMegaFamily

end BoundarySourceUnifiedNaturalMegaAuto

end Stokes

end
