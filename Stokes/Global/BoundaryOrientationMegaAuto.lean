import Stokes.Global
import Stokes.Global.BoundaryUnifiedMegaRouteAuto
import Stokes.Global.NaturalCompactSupportRouteMegaAuto
import Stokes.Global.OrientationBridgeToM8
import Stokes.Global.BoundaryControlledTargetOrientationEndpointAuto
import Stokes.BoundaryChart.OrientationAtlasBoundarySign

/-!
# Mega orientation bridge for boundary routes

This file is a theorem-facing orientation adapter for the current compact
support Stokes route.  It does not create new orientation facts.  The two
things it does are:

* project already-packaged `BoundaryChartOrientedAtlas` membership fields into
  `M8TargetOrientationFields`, boundary-sign data, and boundary mega routes;
* provide constructor packages whose only extra data are the orientation bridge
  fields that are still not produced automatically by mathlib.

The public mathematical content remains in the imported boundary-chart
orientation modules.  This module keeps endpoint code from reopening the
controlled-target or source-shrink records just to recover the same atlas,
membership, boundary-sign, and Stokes-route projections.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryOrientationMegaAuto

universe u v w b ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/-! ## Oriented-atlas projections to target-orientation fields -/

namespace BoundaryChartOrientedAtlas

variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}

/-- Repackage an M8 target-image input as the orientation fields consumed by
`M8GlobalStokesInput`. -/
def toTargetOrientationFieldsOfM8TargetImageInput
    (A : BoundaryChartOrientedAtlas I M)
    (T : M8TargetImageInput I omega selectedPartition A BoundaryPiece) :
    M8TargetOrientationFields I omega BoundaryPiece T.targetImages where
  orientedBoundaryAtlas := A
  source_mem := T.targetImages_source_mem
  boundarySource_mem := T.targetImages_boundarySource_mem

@[simp]
theorem toTargetOrientationFieldsOfM8TargetImageInput_orientedBoundaryAtlas
    (A : BoundaryChartOrientedAtlas I M)
    (T : M8TargetImageInput I omega selectedPartition A BoundaryPiece) :
    (A.toTargetOrientationFieldsOfM8TargetImageInput T).orientedBoundaryAtlas =
      A := by
  rfl

theorem toTargetOrientationFieldsOfM8TargetImageInput_source_mem
    (A : BoundaryChartOrientedAtlas I M)
    (T : M8TargetImageInput I omega selectedPartition A BoundaryPiece) :
    forall x, x ∈ T.targetImages.activeCharts ->
      forall q, q ∈ T.targetImages.boundaryPieces x ->
        T.targetImages.sourceChart x q ∈
          (A.toTargetOrientationFieldsOfM8TargetImageInput T).orientedBoundaryAtlas.charts := by
  intro x hx q hq
  simpa using T.targetImages_source_mem x hx q hq

theorem toTargetOrientationFieldsOfM8TargetImageInput_boundarySource_mem
    (A : BoundaryChartOrientedAtlas I M)
    (T : M8TargetImageInput I omega selectedPartition A BoundaryPiece) :
    forall x, x ∈ T.targetImages.activeCharts ->
      forall q, q ∈ T.targetImages.boundaryPieces x ->
        T.targetImages.boundarySourceChart x q ∈
          (A.toTargetOrientationFieldsOfM8TargetImageInput T).orientedBoundaryAtlas.charts := by
  intro x hx q hq
  simpa using T.targetImages_boundarySource_mem x hx q hq

end BoundaryChartOrientedAtlas

/-! ## Natural endpoint constructors with explicit orientation source -/

namespace BoundaryChartOrientedAtlas

variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]

/-- Constructor for `NaturalBulkEndpointUnifiedInput` that makes the oriented
atlas the first-class source of orientation data.  The remaining fields are
exactly the existing natural endpoint fields. -/
def toNaturalBulkEndpointUnifiedInput
    (A : BoundaryChartOrientedAtlas I M)
    (D : NaturalFiniteActiveChartBoxSelectionData I omega rho)
    (boundaryUnified :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := D.selectedPartition)
        (orientedBoundaryAtlas := A)
        (BoundaryPiece := BoundaryPiece))
    (localized : LocalizedInteriorM8Fields I omega D.selectedPartition)
    (measure_eq_volume : mu = volume)
    (boundaryFaceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        boundaryUnified.toProjectLocalGlobalStokesData)
    (boundaryChartChange :
      BoundaryChartChangeSelectedFamilyData
        boundaryUnified.toProjectLocalGlobalStokesData) :
    NaturalBulkEndpointUnifiedInput
      (I := I) (omega := omega) (rho := rho)
      D BoundaryPiece mu where
  orientedBoundaryAtlas := A
  boundaryUnified := boundaryUnified
  localized := localized
  measure_eq_volume := measure_eq_volume
  boundaryFaceContinuity := boundaryFaceContinuity
  boundaryChartChange := boundaryChartChange

/-- Common endpoint package produced from an oriented atlas and unified
boundary source data. -/
def toNaturalBulkEndpointCommonData
    (A : BoundaryChartOrientedAtlas I M)
    (D : NaturalFiniteActiveChartBoxSelectionData I omega rho)
    (boundaryUnified :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := D.selectedPartition)
        (orientedBoundaryAtlas := A)
        (BoundaryPiece := BoundaryPiece))
    (localized : LocalizedInteriorM8Fields I omega D.selectedPartition)
    (measure_eq_volume : mu = volume)
    (boundaryFaceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        boundaryUnified.toProjectLocalGlobalStokesData)
    (boundaryChartChange :
      BoundaryChartChangeSelectedFamilyData
        boundaryUnified.toProjectLocalGlobalStokesData) :
    NaturalBulkEndpointCommonData
      (I := I) (omega := omega) (rho := rho)
      D BoundaryPiece mu :=
  (A.toNaturalBulkEndpointUnifiedInput D boundaryUnified localized
    measure_eq_volume boundaryFaceContinuity boundaryChartChange).toCommonData

@[simp]
theorem toNaturalBulkEndpointUnifiedInput_orientedBoundaryAtlas
    (A : BoundaryChartOrientedAtlas I M)
    (D : NaturalFiniteActiveChartBoxSelectionData I omega rho)
    (boundaryUnified :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := D.selectedPartition)
        (orientedBoundaryAtlas := A)
        (BoundaryPiece := BoundaryPiece))
    (localized : LocalizedInteriorM8Fields I omega D.selectedPartition)
    (measure_eq_volume : mu = volume)
    (boundaryFaceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        boundaryUnified.toProjectLocalGlobalStokesData)
    (boundaryChartChange :
      BoundaryChartChangeSelectedFamilyData
        boundaryUnified.toProjectLocalGlobalStokesData) :
    (A.toNaturalBulkEndpointUnifiedInput D boundaryUnified localized
      measure_eq_volume boundaryFaceContinuity boundaryChartChange).orientedBoundaryAtlas =
      A := by
  rfl

@[simp]
theorem toNaturalBulkEndpointUnifiedInput_boundaryUnified
    (A : BoundaryChartOrientedAtlas I M)
    (D : NaturalFiniteActiveChartBoxSelectionData I omega rho)
    (boundaryUnified :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := D.selectedPartition)
        (orientedBoundaryAtlas := A)
        (BoundaryPiece := BoundaryPiece))
    (localized : LocalizedInteriorM8Fields I omega D.selectedPartition)
    (measure_eq_volume : mu = volume)
    (boundaryFaceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        boundaryUnified.toProjectLocalGlobalStokesData)
    (boundaryChartChange :
      BoundaryChartChangeSelectedFamilyData
        boundaryUnified.toProjectLocalGlobalStokesData) :
    (A.toNaturalBulkEndpointUnifiedInput D boundaryUnified localized
      measure_eq_volume boundaryFaceContinuity boundaryChartChange).boundaryUnified =
      boundaryUnified := by
  rfl

@[simp]
theorem toNaturalBulkEndpointCommonData_orientedBoundaryAtlas
    (A : BoundaryChartOrientedAtlas I M)
    (D : NaturalFiniteActiveChartBoxSelectionData I omega rho)
    (boundaryUnified :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := D.selectedPartition)
        (orientedBoundaryAtlas := A)
        (BoundaryPiece := BoundaryPiece))
    (localized : LocalizedInteriorM8Fields I omega D.selectedPartition)
    (measure_eq_volume : mu = volume)
    (boundaryFaceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        boundaryUnified.toProjectLocalGlobalStokesData)
    (boundaryChartChange :
      BoundaryChartChangeSelectedFamilyData
        boundaryUnified.toProjectLocalGlobalStokesData) :
    (A.toNaturalBulkEndpointCommonData D boundaryUnified localized
      measure_eq_volume boundaryFaceContinuity boundaryChartChange).orientedBoundaryAtlas =
      A := by
  rfl

end BoundaryChartOrientedAtlas

/-! ## Mathlib orientation-bridge packages -/

/-- Data needed to use a future mathlib oriented-atlas bridge with the current
natural boundary route.  The bridge itself provides the project-local
`BoundaryChartOrientedAtlas`; all remaining fields are the non-orientation
endpoint data that are still independently constructed. -/
structure BoundaryMathlibAtlasNaturalMegaInput
    (Orient : Type v)
    (rho : SmoothPartitionOfUnity M I M univ)
    (D : NaturalFiniteActiveChartBoxSelectionData I omega rho)
    (BoundaryPiece : Type b)
    (mu : Measure (Fin (n + 1) -> Real))
    [IsFiniteMeasureOnCompacts mu]
    [IsManifold I 1 M] where
  bridge : BoundaryChartMathlibOrientedAtlasBridge I M Orient
  boundaryUnified :
    BoundarySourceAlignmentUnifiedData
      (I := I) (omega := omega)
      (selectedPartition := D.selectedPartition)
      (orientedBoundaryAtlas := bridge.toBoundaryChartOrientedAtlas)
      (BoundaryPiece := BoundaryPiece)
  localized : LocalizedInteriorM8Fields I omega D.selectedPartition
  measure_eq_volume : mu = volume
  boundaryFaceContinuity :
    ProjectLocalBoundaryCanonicalFaceContinuityData
      boundaryUnified.toProjectLocalGlobalStokesData
  boundaryChartChange :
    BoundaryChartChangeSelectedFamilyData
      boundaryUnified.toProjectLocalGlobalStokesData

namespace BoundaryMathlibAtlasNaturalMegaInput

variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]
variable {Orient : Type v}
variable {D : NaturalFiniteActiveChartBoxSelectionData I omega rho}
variable
    (B :
      BoundaryMathlibAtlasNaturalMegaInput
        (I := I) (omega := omega)
        Orient rho D BoundaryPiece mu)

/-- The project-local oriented atlas obtained from the mathlib-facing bridge. -/
abbrev orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M :=
  B.bridge.toBoundaryChartOrientedAtlas

/-- Pack the bridge data as the natural unified endpoint input. -/
def toNaturalBulkEndpointUnifiedInput :
    NaturalBulkEndpointUnifiedInput
      (I := I) (omega := omega) (rho := rho)
      D BoundaryPiece mu :=
  B.orientedBoundaryAtlas.toNaturalBulkEndpointUnifiedInput D
    B.boundaryUnified B.localized B.measure_eq_volume
    B.boundaryFaceContinuity B.boundaryChartChange

/-- Pack the bridge data as common endpoint data. -/
def toNaturalBulkEndpointCommonData :
    NaturalBulkEndpointCommonData
      (I := I) (omega := omega) (rho := rho)
      D BoundaryPiece mu :=
  B.toNaturalBulkEndpointUnifiedInput.toCommonData

/-- Global-measure mega route generated from bridge-driven common data. -/
def toBoundaryUnifiedGlobalMeasureMegaData :
    BoundarySourceAlignmentUnifiedData.BoundaryUnifiedGlobalMeasureMegaData
      B.boundaryUnified :=
  B.toNaturalBulkEndpointCommonData.toBoundaryUnifiedGlobalMeasureMegaData

/-- Support-finite mega route generated from bridge-driven common data. -/
def toBoundaryUnifiedSupportFiniteMegaData
    (supportFinite :
      ProjectLocalBoundarySupportFiniteMeasureFacts
        B.boundaryUnified.toProjectLocalGlobalStokesData) :
    BoundarySourceAlignmentUnifiedData.BoundaryUnifiedSupportFiniteMegaData
      B.boundaryUnified :=
  B.toNaturalBulkEndpointCommonData.toBoundaryUnifiedSupportFiniteMegaData
    supportFinite

/-- Canonical boundary route produced by the bridge-driven selected chart-change route. -/
def boundaryRouteOfSelectedChartChange :
    BoundaryCanonicalRouteMeasureInput
      B.boundaryUnified.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      B.boundaryUnified.toProjectLocalGlobalStokesData :=
  B.toNaturalBulkEndpointCommonData.boundaryRouteOfSelectedChartChange

@[simp]
theorem toNaturalBulkEndpointUnifiedInput_orientedBoundaryAtlas :
    B.toNaturalBulkEndpointUnifiedInput.orientedBoundaryAtlas =
      B.orientedBoundaryAtlas := by
  rfl

@[simp]
theorem toNaturalBulkEndpointUnifiedInput_boundaryUnified :
    B.toNaturalBulkEndpointUnifiedInput.boundaryUnified =
      B.boundaryUnified := by
  rfl

@[simp]
theorem toNaturalBulkEndpointCommonData_boundaryUnified :
    B.toNaturalBulkEndpointCommonData.boundaryUnified =
      B.boundaryUnified := by
  rfl

@[simp]
theorem toBoundaryUnifiedGlobalMeasureMegaData_faceContinuity :
    B.toBoundaryUnifiedGlobalMeasureMegaData.faceContinuity =
      B.boundaryFaceContinuity := by
  rfl

end BoundaryMathlibAtlasNaturalMegaInput

/-! ## Unified boundary-source orientation projections -/

namespace BoundarySourceAlignmentUnifiedData

variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
variable
    (U :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := selectedPartition)
        (orientedBoundaryAtlas := orientedBoundaryAtlas)
        (BoundaryPiece := BoundaryPiece))

/-- The controlled target input determined by a unified source, with its
orientation fields retained by the type. -/
abbrev controlledTargetInput :
    M8BoundaryControlledTargetInput I omega selectedPartition
      orientedBoundaryAtlas BoundaryPiece :=
  U.toM8BoundaryControlledTargetInput

/-- M8 target-image input determined by a unified source. -/
abbrev controlledTargetImageInput :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece :=
  U.controlledTargetInput.toM8TargetImageInput

/-- Orientation fields of the target-image family produced by the unified
source. -/
def targetOrientationFields :
    M8TargetOrientationFields I omega BoundaryPiece
      U.controlledTargetImageInput.targetImages where
  orientedBoundaryAtlas := orientedBoundaryAtlas
  source_mem := U.controlledTargetImageInput.targetImages_source_mem
  boundarySource_mem :=
    U.controlledTargetImageInput.targetImages_boundarySource_mem

/-- Boundary-atlas membership of the resolved target-image family in the
unified source. -/
def boundaryAtlasMembership :
    U.controlledTargetInput.toM8ResolvedInput.family.BoundaryAtlasMembership
      orientedBoundaryAtlas :=
  U.controlledTargetInput.toM8ResolvedInput.boundaryAtlasMembership

/-- Source/boundary-source membership as one local orientation package. -/
def sourceOrientationMembership
    (x : M) (hx : x ∈ U.family.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ U.family.localPieces x) :
    BoundaryChartOrientationMembership orientedBoundaryAtlas.charts
      (U.family.sourceChart x q) (U.family.boundarySourceChart x q) :=
  BoundaryChartOrientationMembership.of_mem
    (U.m8Fields.source_mem x hx q hq)
    (U.m8Fields.boundarySource_mem x hx q hq)

/-- Boundary-source/boundary-target membership as one local orientation package. -/
def boundaryPartitionOrientationMembership
    (x : M) (hx : x ∈ U.family.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ U.family.localPieces x) :
    BoundaryChartOrientationMembership orientedBoundaryAtlas.charts
      (U.family.boundarySourceChart x q) (U.family.boundaryTargetChart x q) :=
  BoundaryChartOrientationMembership.of_mem
    (U.m8Fields.boundarySource_mem x hx q hq)
    (U.m8Fields.boundaryTarget_mem x hx q hq)

/-- Boundary-sign data on the source selected box of an active unified boundary
piece. -/
def sourceSelectedBoundarySignData
    (x : M) (hx : x ∈ U.family.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ U.family.localPieces x) :
    BoundaryChartAtlasBoundarySignData I
      (U.family.sourceChart x q) (U.family.boundarySourceChart x q) omega
      (U.family.sourceLowerCorner x q) (U.family.sourceUpperCorner x q) :=
  orientedBoundaryAtlas.selectedBoxBoundarySignData
    (U.m8Fields.source_mem x hx q hq)
    (U.m8Fields.boundarySource_mem x hx q hq)
    (U.family.sourceSelectedBox x hx q hq)

/-- The selected source box of an active unified boundary piece is
orientation-compatible. -/
theorem sourceSelectedBox_orientationCompatibleOn
    (x : M) (hx : x ∈ U.family.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ U.family.localPieces x) :
    boundaryChartOrientationCompatibleOn I
      (U.family.sourceChart x q) (U.family.boundarySourceChart x q)
      (lowerZeroFaceDomain (U.family.sourceLowerCorner x q)
        (U.family.sourceUpperCorner x q)) :=
  (U.sourceSelectedBoundarySignData x hx q hq).orientationCompatibleOn

/-- Pointwise positive tangential Jacobian on the source selected box of an
active unified boundary piece. -/
theorem sourceSelectedBox_jacobian_pos
    (x : M) (hx : x ∈ U.family.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ U.family.localPieces x)
    {u : Fin n -> Real}
    (hu : u ∈ lowerZeroFaceDomain (U.family.sourceLowerCorner x q)
      (U.family.sourceUpperCorner x q)) :
    0 < boundaryChartTransitionJacobian I
      (U.family.sourceChart x q) (U.family.boundarySourceChart x q) u :=
  (U.sourceSelectedBoundarySignData x hx q hq).jacobian_pos hu

/-- Source selected boxes use the project half-space sign, i.e. the
outward-first induced boundary orientation sign. -/
theorem sourceSelectedBox_halfSpaceBoundarySign_eq_outwardFirst
    (x : M) (hx : x ∈ U.family.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ U.family.localPieces x) :
    halfSpaceBoundarySign n = outwardFirstBoundaryOrientationSign n :=
  (U.sourceSelectedBoundarySignData x hx q hq).boundarySign_eq_outwardFirst

@[simp]
theorem targetOrientationFields_orientedBoundaryAtlas :
    U.targetOrientationFields.orientedBoundaryAtlas =
      orientedBoundaryAtlas := by
  rfl

@[simp]
theorem sourceOrientationMembership_source_mem
    (x : M) (hx : x ∈ U.family.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ U.family.localPieces x) :
    (U.sourceOrientationMembership x hx q hq).source_mem =
      U.m8Fields.source_mem x hx q hq := by
  rfl

@[simp]
theorem sourceOrientationMembership_boundarySource_mem
    (x : M) (hx : x ∈ U.family.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ U.family.localPieces x) :
    (U.sourceOrientationMembership x hx q hq).boundarySource_mem =
      U.m8Fields.boundarySource_mem x hx q hq := by
  rfl

@[simp]
theorem boundaryPartitionOrientationMembership_source_mem
    (x : M) (hx : x ∈ U.family.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ U.family.localPieces x) :
    (U.boundaryPartitionOrientationMembership x hx q hq).source_mem =
      U.m8Fields.boundarySource_mem x hx q hq := by
  rfl

@[simp]
theorem boundaryPartitionOrientationMembership_boundarySource_mem
    (x : M) (hx : x ∈ U.family.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ U.family.localPieces x) :
    (U.boundaryPartitionOrientationMembership x hx q hq).boundarySource_mem =
      U.m8Fields.boundaryTarget_mem x hx q hq := by
  rfl

end BoundarySourceAlignmentUnifiedData

/-! ## Common and unified endpoint orientation route projections -/

namespace NaturalBulkEndpointCommonData

variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]
variable {D : NaturalFiniteActiveChartBoxSelectionData I omega rho}
variable
    (C :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        D BoundaryPiece mu)

/-- Target-orientation fields carried by common endpoint data. -/
def targetOrientationFields :
    M8TargetOrientationFields I omega BoundaryPiece
      C.boundaryUnified.controlledTargetImageInput.targetImages :=
  C.boundaryUnified.targetOrientationFields

/-- Boundary-sign data for an active boundary piece carried by common endpoint
data. -/
def sourceSelectedBoundarySignData
    (x : M) (hx : x ∈ C.boundaryUnified.family.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ C.boundaryUnified.family.localPieces x) :
    BoundaryChartAtlasBoundarySignData I
      (C.boundaryUnified.family.sourceChart x q)
      (C.boundaryUnified.family.boundarySourceChart x q) omega
      (C.boundaryUnified.family.sourceLowerCorner x q)
      (C.boundaryUnified.family.sourceUpperCorner x q) :=
  C.boundaryUnified.sourceSelectedBoundarySignData x hx q hq

/-- Canonical boundary route obtained from the selected chart-change route in
common data. -/
def boundaryRouteOfOrientation :
    BoundaryCanonicalRouteMeasureInput
      C.boundaryUnified.controlledTargetImageInput
      C.boundaryUnified.toProjectLocalGlobalStokesData :=
  C.boundaryRouteOfSelectedChartChange

/-- Boundary-only M8 measure data obtained from the orientation-backed common route. -/
def m8BoundaryMeasureDataOfOrientation :
    M8BoundaryMeasureData I omega D.selectedPartition
      C.boundaryUnified.controlledTargetImageInput.targetImages :=
  C.m8BoundaryMeasureDataOfSelectedChartChange

/-- Canonical compact-support boundary target input obtained from common
orientation data. -/
def canonicalBoundaryTargetInputOfOrientation :
    CanonicalBoundaryTargetCompactSupportInput
      (α := Fin n -> Real)
      C.boundaryUnified.controlledTargetImageInput
      (volume : Measure (Fin n -> Real)) :=
  C.canonicalBoundaryTargetInputOfSelectedChartChange

/-- Support-finite boundary route from common data and explicit support-finite
facts. -/
def boundaryRouteOfOrientationSupportFinite
    (supportFinite :
      ProjectLocalBoundarySupportFiniteMeasureFacts
        C.boundaryUnified.toProjectLocalGlobalStokesData) :
    BoundaryCanonicalRouteMeasureInput
      C.boundaryUnified.controlledTargetImageInput
      C.boundaryUnified.toProjectLocalGlobalStokesData :=
  BoundarySourceAlignmentUnifiedData.BoundaryUnifiedSupportFiniteMegaData.toBoundaryCanonicalRouteMeasureInput
    (C.toBoundaryUnifiedSupportFiniteMegaData supportFinite)

@[simp]
theorem targetOrientationFields_orientedBoundaryAtlas :
    C.targetOrientationFields.orientedBoundaryAtlas =
      C.orientedBoundaryAtlas := by
  rfl

@[simp]
theorem boundaryRouteOfOrientation_sourceAlignment :
    C.boundaryRouteOfOrientation.sourceAlignment =
      C.boundaryUnified.toControlledBoundaryCanonicalProjectLocalFields.sourceAlignment := by
  rfl

@[simp]
theorem m8BoundaryMeasureDataOfOrientation_boundaryPartitionTerm :
    C.m8BoundaryMeasureDataOfOrientation.boundaryPartitionTerm =
      C.boundaryUnified.controlledTargetImageInput.assembly.boundaryPartitionTerm := by
  rfl

@[simp]
theorem canonicalBoundaryTargetInputOfOrientation_boundaryMeasureIntegral :
    C.canonicalBoundaryTargetInputOfOrientation.boundaryMeasureIntegral =
      C.boundaryRouteOfOrientation.projectLocal.boundaryMeasureIntegral := by
  rfl

end NaturalBulkEndpointCommonData

namespace NaturalBulkEndpointUnifiedInput

variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]
variable {D : NaturalFiniteActiveChartBoxSelectionData I omega rho}
variable
    (P :
      NaturalBulkEndpointUnifiedInput
        (I := I) (omega := omega) (rho := rho)
        D BoundaryPiece mu)

/-- Target-orientation fields carried by a packaged unified endpoint input. -/
def targetOrientationFields :
    M8TargetOrientationFields I omega BoundaryPiece
      P.boundaryUnified.controlledTargetImageInput.targetImages :=
  P.toCommonData.targetOrientationFields

/-- Canonical boundary route obtained from the selected chart-change route. -/
def boundaryRouteOfOrientation :
    BoundaryCanonicalRouteMeasureInput
      P.boundaryUnified.controlledTargetImageInput
      P.boundaryUnified.toProjectLocalGlobalStokesData :=
  P.toCommonData.boundaryRouteOfOrientation

/-- Boundary-only M8 measure data generated by packaged orientation data. -/
def m8BoundaryMeasureDataOfOrientation :
    M8BoundaryMeasureData I omega D.selectedPartition
      P.boundaryUnified.controlledTargetImageInput.targetImages :=
  P.toCommonData.m8BoundaryMeasureDataOfOrientation

/-- Canonical compact-support boundary target input generated by packaged
orientation data. -/
def canonicalBoundaryTargetInputOfOrientation :
    CanonicalBoundaryTargetCompactSupportInput
      (α := Fin n -> Real)
      P.boundaryUnified.controlledTargetImageInput
      (volume : Measure (Fin n -> Real)) :=
  P.toCommonData.canonicalBoundaryTargetInputOfOrientation

/-- Support-finite boundary route from packaged orientation data. -/
def boundaryRouteOfOrientationSupportFinite
    (supportFinite :
      ProjectLocalBoundarySupportFiniteMeasureFacts
        P.boundaryUnified.toProjectLocalGlobalStokesData) :
    BoundaryCanonicalRouteMeasureInput
      P.boundaryUnified.controlledTargetImageInput
      P.boundaryUnified.toProjectLocalGlobalStokesData :=
  P.toCommonData.boundaryRouteOfOrientationSupportFinite supportFinite

@[simp]
theorem targetOrientationFields_orientedBoundaryAtlas :
    P.targetOrientationFields.orientedBoundaryAtlas =
      P.orientedBoundaryAtlas := by
  rfl

@[simp]
theorem boundaryRouteOfOrientation_sourceAlignment :
    P.boundaryRouteOfOrientation.sourceAlignment =
      P.boundaryUnified.toControlledBoundaryCanonicalProjectLocalFields.sourceAlignment := by
  rfl

end NaturalBulkEndpointUnifiedInput

/-! ## Compact-support mega-route orientation projections -/

namespace NaturalCompactSupportRouteMegaBase

variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]
variable
    (B :
      NaturalCompactSupportRouteMegaBase
        I omega rho BoundaryPiece mu)

/-- Target-orientation fields carried by the compact-support mega base. -/
def targetOrientationFields :
    M8TargetOrientationFields I omega BoundaryPiece
      B.boundaryUnified.controlledTargetImageInput.targetImages :=
  B.common.targetOrientationFields

/-- Canonical boundary route exposed through the orientation-backed mega base. -/
def boundaryRouteOfOrientation :
    BoundaryCanonicalRouteMeasureInput
      B.boundaryUnified.controlledTargetImageInput
      B.boundaryUnified.toProjectLocalGlobalStokesData :=
  B.common.boundaryRouteOfOrientation

/-- Support-finite boundary route exposed through the orientation-backed mega base. -/
def supportFiniteBoundaryRouteOfOrientation :
    BoundaryCanonicalRouteMeasureInput
      B.boundaryUnified.controlledTargetImageInput
      B.boundaryUnified.toProjectLocalGlobalStokesData :=
  B.common.boundaryRouteOfOrientationSupportFinite B.supportFinite

/-- Boundary-only M8 measure data exposed through the orientation-backed mega base. -/
def m8BoundaryMeasureDataOfOrientation :
    M8BoundaryMeasureData I omega B.selectedPartition
      B.boundaryUnified.controlledTargetImageInput.targetImages :=
  B.common.m8BoundaryMeasureDataOfOrientation

/-- Canonical compact-support target input exposed through the orientation-backed mega base. -/
def canonicalBoundaryTargetInputOfOrientation :
    CanonicalBoundaryTargetCompactSupportInput
      (α := Fin n -> Real)
      B.boundaryUnified.controlledTargetImageInput
      (volume : Measure (Fin n -> Real)) :=
  B.common.canonicalBoundaryTargetInputOfOrientation

@[simp]
theorem targetOrientationFields_orientedBoundaryAtlas :
    B.targetOrientationFields.orientedBoundaryAtlas =
      B.orientedBoundaryAtlas := by
  rfl

@[simp]
theorem boundaryRouteOfOrientation_sourceAlignment :
    B.boundaryRouteOfOrientation.sourceAlignment =
      B.boundaryUnified.toControlledBoundaryCanonicalProjectLocalFields.sourceAlignment := by
  rfl

@[simp]
theorem supportFiniteBoundaryRouteOfOrientation_sourceAlignment :
    B.supportFiniteBoundaryRouteOfOrientation.sourceAlignment =
      B.boundaryUnified.toControlledBoundaryCanonicalProjectLocalFields.sourceAlignment := by
  rfl

end NaturalCompactSupportRouteMegaBase

namespace NaturalCompactSupportExtDerivRouteMegaInput

variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]
variable
    (D :
      NaturalCompactSupportExtDerivRouteMegaInput
        I omega rho ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu)

/-- Target-orientation fields used by the ext-deriv compact-support mega route. -/
def targetOrientationFields :
    M8TargetOrientationFields I omega BoundaryPiece
      D.base.boundaryUnified.controlledTargetImageInput.targetImages :=
  D.base.targetOrientationFields

/-- Canonical boundary route used by the ext-deriv compact-support mega route. -/
def boundaryRouteOfOrientation :
    BoundaryCanonicalRouteMeasureInput
      D.base.boundaryUnified.controlledTargetImageInput
      D.base.boundaryUnified.toProjectLocalGlobalStokesData :=
  D.base.boundaryRouteOfOrientation

/-- Support-finite boundary route used by the ext-deriv compact-support mega route. -/
def supportFiniteBoundaryRouteOfOrientation :
    BoundaryCanonicalRouteMeasureInput
      D.base.boundaryUnified.controlledTargetImageInput
      D.base.boundaryUnified.toProjectLocalGlobalStokesData :=
  D.base.supportFiniteBoundaryRouteOfOrientation

@[simp]
theorem targetOrientationFields_orientedBoundaryAtlas :
    D.targetOrientationFields.orientedBoundaryAtlas =
      D.base.orientedBoundaryAtlas := by
  rfl

/-- Stokes statement for the ext-deriv route, named as an orientation-backed wrapper. -/
theorem canonical_stokes_ofOrientationMega :
    D.canonicalIntegralInterface.stokesStatement :=
  D.canonical_stokes

/-- Equality form of the ext-deriv route Stokes theorem, named as an
orientation-backed wrapper. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofOrientationMega :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.canonicalIntegralInterface.boundaryFormIntegral :=
  D.manifoldExtDerivIntegral_eq_boundaryFormIntegral

end NaturalCompactSupportExtDerivRouteMegaInput

namespace NaturalCompactSupportReconstructionRouteMegaInput

variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]
variable
    (D :
      NaturalCompactSupportReconstructionRouteMegaInput
        I omega rho ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu)

/-- Target-orientation fields used by the reconstruction compact-support mega route. -/
def targetOrientationFields :
    M8TargetOrientationFields I omega BoundaryPiece
      D.base.boundaryUnified.controlledTargetImageInput.targetImages :=
  D.base.targetOrientationFields

/-- Canonical boundary route used by the reconstruction compact-support mega route. -/
def boundaryRouteOfOrientation :
    BoundaryCanonicalRouteMeasureInput
      D.base.boundaryUnified.controlledTargetImageInput
      D.base.boundaryUnified.toProjectLocalGlobalStokesData :=
  D.base.boundaryRouteOfOrientation

/-- Support-finite boundary route used by the reconstruction compact-support mega route. -/
def supportFiniteBoundaryRouteOfOrientation :
    BoundaryCanonicalRouteMeasureInput
      D.base.boundaryUnified.controlledTargetImageInput
      D.base.boundaryUnified.toProjectLocalGlobalStokesData :=
  D.base.supportFiniteBoundaryRouteOfOrientation

@[simp]
theorem targetOrientationFields_orientedBoundaryAtlas :
    D.targetOrientationFields.orientedBoundaryAtlas =
      D.base.orientedBoundaryAtlas := by
  rfl

/-- Stokes statement for the reconstruction route, named as an
orientation-backed wrapper. -/
theorem canonical_stokes_ofOrientationMega :
    D.canonicalIntegralInterface.stokesStatement :=
  D.canonical_stokes

/-- Equality form of the reconstruction route Stokes theorem, named as an
orientation-backed wrapper. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofOrientationMega :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.canonicalIntegralInterface.boundaryFormIntegral :=
  D.manifoldExtDerivIntegral_eq_boundaryFormIntegral

end NaturalCompactSupportReconstructionRouteMegaInput

end BoundaryOrientationMegaAuto

end Stokes

end
