import Stokes.Global.BoundaryCanonicalRouteFromUnifiedSupportFiniteAuto
import Stokes.Global.BoundaryUnifiedToEndpointBaseAuto
import Stokes.Global.NaturalBulkEndpointCommonFromUnifiedAuto

/-!
# Mega routes from unified boundary data

This module aggregates the high-use projections from
`BoundarySourceAlignmentUnifiedData`.

There are two route shapes:

* a global-measure route, carrying explicit
  `ProjectLocalBoundaryGlobalMeasureFacts`;
* a support-finite route, carrying
  `ProjectLocalBoundarySupportFiniteMeasureFacts` and exposing the induced
  global-measure view.

The code below is intentionally a plumbing layer: it does not invent new
mathematical assumptions.  It packages the existing controlled-target input,
project-local data, canonical boundary route, boundary M8 measure data, and
collapsed endpoint theorem wrappers behind one surface.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryUnifiedMegaRouteAuto

universe u w b ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

namespace BoundarySourceAlignmentUnifiedData

variable
    (U :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := selectedPartition)
        (orientedBoundaryAtlas := orientedBoundaryAtlas)
        (BoundaryPiece := BoundaryPiece))

/-- One-stop global-measure boundary route package over unified boundary data. -/
structure BoundaryUnifiedGlobalMeasureMegaData where
  /-- Global boundary measure reconstruction facts for the unified project-local package. -/
  globalMeasure :
    ProjectLocalBoundaryGlobalMeasureFacts U.toProjectLocalGlobalStokesData
  /-- Canonical lower-face continuity/integrability facts. -/
  faceContinuity :
    ProjectLocalBoundaryCanonicalFaceContinuityData
      U.toProjectLocalGlobalStokesData

/-- One-stop support-finite boundary route package over unified boundary data. -/
structure BoundaryUnifiedSupportFiniteMegaData where
  /-- Support-finite reconstruction facts for the unified project-local package. -/
  supportFinite :
    ProjectLocalBoundarySupportFiniteMeasureFacts
      U.toProjectLocalGlobalStokesData
  /-- Canonical lower-face continuity/integrability facts. -/
  faceContinuity :
    ProjectLocalBoundaryCanonicalFaceContinuityData
      U.toProjectLocalGlobalStokesData

namespace BoundaryUnifiedGlobalMeasureMegaData

variable
    {U :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := selectedPartition)
        (orientedBoundaryAtlas := orientedBoundaryAtlas)
        (BoundaryPiece := BoundaryPiece)}
    (D : BoundaryUnifiedGlobalMeasureMegaData U)

/-- The project-local data determined by the unified source. -/
abbrev boundaryProjectLocal
    (_D : BoundaryUnifiedGlobalMeasureMegaData U) :
    ProjectLocalGlobalStokesData I omega M BoundaryPiece :=
  U.toProjectLocalGlobalStokesData

/-- The controlled target input determined by the unified source. -/
abbrev controlledTargetInput
    (_D : BoundaryUnifiedGlobalMeasureMegaData U) :
    M8BoundaryControlledTargetInput I omega selectedPartition
      orientedBoundaryAtlas BoundaryPiece :=
  U.toM8BoundaryControlledTargetInput

/-- The M8 target-image input determined by the unified source. -/
abbrev targetImageInput
    (_D : BoundaryUnifiedGlobalMeasureMegaData U) :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece :=
  U.toM8BoundaryControlledTargetInput.toM8TargetImageInput

/-- The source/project-local fields determined by the unified source. -/
abbrev projectLocalFields
    (_D : BoundaryUnifiedGlobalMeasureMegaData U) :
    M8BoundaryControlledTargetInput.BoundaryCanonicalProjectLocalFields
      U.toM8BoundaryControlledTargetInput
      (P := U.toProjectLocalGlobalStokesData) :=
  U.toControlledBoundaryCanonicalProjectLocalFields

/-- Natural global controlled-target input generated from the mega package. -/
def toNaturalGlobalInput
    (D : BoundaryUnifiedGlobalMeasureMegaData U) :
    BoundaryCanonicalTargetNaturalGlobalInput
      U.toM8BoundaryControlledTargetInput
      U.toProjectLocalGlobalStokesData :=
  U.toBoundaryCanonicalTargetNaturalGlobalInput
    D.globalMeasure D.faceContinuity

/-- Canonical boundary route generated from explicit global-measure facts. -/
def toBoundaryCanonicalRouteMeasureInput
    (D : BoundaryUnifiedGlobalMeasureMegaData U)
    [IsManifold I 1 M] :
    BoundaryCanonicalRouteMeasureInput
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      U.toProjectLocalGlobalStokesData :=
  U.toBoundaryCanonicalRouteMeasureInputOfUnifiedGlobal
    D.globalMeasure D.faceContinuity

/-- Same canonical route, explicitly routed through the controlled M8 input. -/
def toBoundaryCanonicalRouteMeasureInputViaControlledM8
    (D : BoundaryUnifiedGlobalMeasureMegaData U)
    [IsManifold I 1 M] :
    BoundaryCanonicalRouteMeasureInput
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      U.toProjectLocalGlobalStokesData :=
  U.toBoundaryCanonicalRouteMeasureInputOfControlledM8
    D.globalMeasure D.faceContinuity

/-- Canonical compact-support boundary target input generated by the route. -/
def toCanonicalBoundaryTargetCompactSupportInput
    (D : BoundaryUnifiedGlobalMeasureMegaData U)
    [IsManifold I 1 M] :
    CanonicalBoundaryTargetCompactSupportInput
      (α := Fin n -> Real)
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      (volume : Measure (Fin n -> Real)) :=
  U.toCanonicalBoundaryTargetCompactSupportInputOfUnifiedGlobal
    D.globalMeasure D.faceContinuity

/-- Boundary-only M8 measure data generated by the route. -/
def toM8BoundaryMeasureData
    (D : BoundaryUnifiedGlobalMeasureMegaData U)
    [IsManifold I 1 M] :
    M8BoundaryMeasureData I omega selectedPartition
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.targetImages :=
  U.toM8BoundaryMeasureDataOfUnifiedGlobal
    D.globalMeasure D.faceContinuity

@[simp]
theorem toNaturalGlobalInput_projectLocalFields :
    (toNaturalGlobalInput D).projectLocalFields =
      U.toControlledBoundaryCanonicalProjectLocalFields := by
  rfl

@[simp]
theorem toNaturalGlobalInput_globalMeasure :
    (toNaturalGlobalInput D).globalMeasure = D.globalMeasure := by
  rfl

@[simp]
theorem toNaturalGlobalInput_faceContinuity :
    (toNaturalGlobalInput D).faceContinuity = D.faceContinuity := by
  rfl

@[simp]
theorem toBoundaryCanonicalRouteMeasureInput_sourceAlignment
    [IsManifold I 1 M] :
    (toBoundaryCanonicalRouteMeasureInput D).sourceAlignment =
      U.toControlledBoundaryCanonicalProjectLocalFields.sourceAlignment := by
  rfl

@[simp]
theorem toBoundaryCanonicalRouteMeasureInput_faceContinuity
    [IsManifold I 1 M] :
    (toBoundaryCanonicalRouteMeasureInput D).faceContinuity =
      D.faceContinuity := by
  rfl

@[simp]
theorem toBoundaryCanonicalRouteMeasureInputViaControlledM8_sourceAlignment
    [IsManifold I 1 M] :
    (toBoundaryCanonicalRouteMeasureInputViaControlledM8 D).sourceAlignment =
      U.toControlledBoundaryCanonicalProjectLocalFields.sourceAlignment := by
  rfl

@[simp]
theorem toCanonicalBoundaryTargetCompactSupportInput_boundaryMeasureIntegral
    [IsManifold I 1 M] :
    (toCanonicalBoundaryTargetCompactSupportInput D).boundaryMeasureIntegral =
      (toBoundaryCanonicalRouteMeasureInput D).projectLocal.boundaryMeasureIntegral := by
  rfl

@[simp]
theorem toM8BoundaryMeasureData_boundaryPartitionTerm
    [IsManifold I 1 M] :
    (toM8BoundaryMeasureData D).boundaryPartitionTerm =
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.assembly.boundaryPartitionTerm := by
  rfl

@[simp]
theorem toM8BoundaryMeasureData_boundaryMeasureIntegral
    [IsManifold I 1 M] :
    (toM8BoundaryMeasureData D).boundaryMeasureIntegral =
      (toBoundaryCanonicalRouteMeasureInput D).projectLocal.boundaryMeasureIntegral := by
  rfl

end BoundaryUnifiedGlobalMeasureMegaData

namespace BoundaryUnifiedSupportFiniteMegaData

variable
    {U :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := selectedPartition)
        (orientedBoundaryAtlas := orientedBoundaryAtlas)
        (BoundaryPiece := BoundaryPiece)}
    (D : BoundaryUnifiedSupportFiniteMegaData U)

/-- Forget support-finite data to the global-measure mega package. -/
def toGlobalMeasureMegaData
    (D : BoundaryUnifiedSupportFiniteMegaData U) :
    BoundaryUnifiedGlobalMeasureMegaData U where
  globalMeasure := D.supportFinite.toGlobalMeasureFacts
  faceContinuity := D.faceContinuity

/-- The project-local data determined by the unified source. -/
abbrev boundaryProjectLocal
    (_D : BoundaryUnifiedSupportFiniteMegaData U) :
    ProjectLocalGlobalStokesData I omega M BoundaryPiece :=
  U.toProjectLocalGlobalStokesData

/-- The controlled target input determined by the unified source. -/
abbrev controlledTargetInput
    (_D : BoundaryUnifiedSupportFiniteMegaData U) :
    M8BoundaryControlledTargetInput I omega selectedPartition
      orientedBoundaryAtlas BoundaryPiece :=
  U.toM8BoundaryControlledTargetInput

/-- The M8 target-image input determined by the unified source. -/
abbrev targetImageInput
    (_D : BoundaryUnifiedSupportFiniteMegaData U) :
    M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
      BoundaryPiece :=
  U.toM8BoundaryControlledTargetInput.toM8TargetImageInput

/-- The source/project-local fields determined by the unified source. -/
abbrev projectLocalFields
    (_D : BoundaryUnifiedSupportFiniteMegaData U) :
    M8BoundaryControlledTargetInput.BoundaryCanonicalProjectLocalFields
      U.toM8BoundaryControlledTargetInput
      (P := U.toProjectLocalGlobalStokesData) :=
  U.toControlledBoundaryCanonicalProjectLocalFields

/-- Natural support-finite controlled-target input generated from the package. -/
def toNaturalSupportFiniteInput
    (D : BoundaryUnifiedSupportFiniteMegaData U) :
    BoundaryCanonicalTargetNaturalSupportFiniteInput
      U.toM8BoundaryControlledTargetInput
      U.toProjectLocalGlobalStokesData :=
  U.toBoundaryCanonicalTargetNaturalSupportFiniteInput
    D.supportFinite D.faceContinuity

/-- Natural global controlled-target input induced by support-finite data. -/
def toNaturalGlobalInput
    (D : BoundaryUnifiedSupportFiniteMegaData U) :
    BoundaryCanonicalTargetNaturalGlobalInput
      U.toM8BoundaryControlledTargetInput
      U.toProjectLocalGlobalStokesData :=
  BoundaryUnifiedGlobalMeasureMegaData.toNaturalGlobalInput
    (toGlobalMeasureMegaData D)

/-- Focused support-finite route package from the imported API. -/
def toSupportFiniteRouteData
    (D : BoundaryUnifiedSupportFiniteMegaData U) :
    BoundaryCanonicalRouteFromUnifiedSupportFiniteData U where
  supportFinite := D.supportFinite
  faceContinuity := D.faceContinuity

/-- Canonical boundary route generated directly from support-finite facts. -/
def toBoundaryCanonicalRouteMeasureInput
    (D : BoundaryUnifiedSupportFiniteMegaData U)
    [IsManifold I 1 M] :
    BoundaryCanonicalRouteMeasureInput
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      U.toProjectLocalGlobalStokesData :=
  U.toBoundaryCanonicalRouteMeasureInputOfUnifiedSupportFinite
    D.supportFinite D.faceContinuity

/-- Global-measure view of the support-finite canonical route. -/
def toGlobalBoundaryCanonicalRouteMeasureInput
    (D : BoundaryUnifiedSupportFiniteMegaData U)
    [IsManifold I 1 M] :
    BoundaryCanonicalRouteMeasureInput
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      U.toProjectLocalGlobalStokesData :=
  BoundaryUnifiedGlobalMeasureMegaData.toBoundaryCanonicalRouteMeasureInput
    (toGlobalMeasureMegaData D)

/-- Same support-finite route, explicitly routed through controlled M8 input. -/
def toBoundaryCanonicalRouteMeasureInputViaControlledM8
    (D : BoundaryUnifiedSupportFiniteMegaData U)
    [IsManifold I 1 M] :
    BoundaryCanonicalRouteMeasureInput
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      U.toProjectLocalGlobalStokesData :=
  U.toBoundaryCanonicalRouteMeasureInputOfControlledM8SupportFinite
    D.supportFinite D.faceContinuity

/-- Canonical compact-support target input from support-finite data. -/
def toCanonicalBoundaryTargetCompactSupportInput
    (D : BoundaryUnifiedSupportFiniteMegaData U)
    [IsManifold I 1 M] :
    CanonicalBoundaryTargetCompactSupportInput
      (α := Fin n -> Real)
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      (volume : Measure (Fin n -> Real)) :=
  U.toCanonicalBoundaryTargetCompactSupportInputOfUnifiedSupportFinite
    D.supportFinite D.faceContinuity

/-- Boundary-only M8 measure data from support-finite data. -/
def toM8BoundaryMeasureData
    (D : BoundaryUnifiedSupportFiniteMegaData U)
    [IsManifold I 1 M] :
    M8BoundaryMeasureData I omega selectedPartition
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.targetImages :=
  U.toM8BoundaryMeasureDataOfUnifiedSupportFinite
    D.supportFinite D.faceContinuity

/-- Boundary-only M8 measure data through the global-measure view. -/
def toGlobalM8BoundaryMeasureData
    (D : BoundaryUnifiedSupportFiniteMegaData U)
    [IsManifold I 1 M] :
    M8BoundaryMeasureData I omega selectedPartition
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.targetImages :=
  BoundaryUnifiedGlobalMeasureMegaData.toM8BoundaryMeasureData
    (toGlobalMeasureMegaData D)

@[simp]
theorem toGlobalMeasureMegaData_globalMeasure :
    (toGlobalMeasureMegaData D).globalMeasure =
      D.supportFinite.toGlobalMeasureFacts := by
  rfl

@[simp]
theorem toGlobalMeasureMegaData_faceContinuity :
    (toGlobalMeasureMegaData D).faceContinuity = D.faceContinuity := by
  rfl

@[simp]
theorem toNaturalSupportFiniteInput_projectLocalFields :
    (toNaturalSupportFiniteInput D).projectLocalFields =
      U.toControlledBoundaryCanonicalProjectLocalFields := by
  rfl

@[simp]
theorem toNaturalSupportFiniteInput_supportFinite :
    (toNaturalSupportFiniteInput D).supportFinite = D.supportFinite := by
  rfl

@[simp]
theorem toNaturalSupportFiniteInput_faceContinuity :
    (toNaturalSupportFiniteInput D).faceContinuity = D.faceContinuity := by
  rfl

@[simp]
theorem toNaturalGlobalInput_globalMeasure :
    (toNaturalGlobalInput D).globalMeasure =
      D.supportFinite.toGlobalMeasureFacts := by
  rfl

@[simp]
theorem toSupportFiniteRouteData_supportFinite :
    (toSupportFiniteRouteData D).supportFinite = D.supportFinite := by
  rfl

@[simp]
theorem toSupportFiniteRouteData_faceContinuity :
    (toSupportFiniteRouteData D).faceContinuity = D.faceContinuity := by
  rfl

@[simp]
theorem toBoundaryCanonicalRouteMeasureInput_sourceAlignment
    [IsManifold I 1 M] :
    (toBoundaryCanonicalRouteMeasureInput D).sourceAlignment =
      U.toControlledBoundaryCanonicalProjectLocalFields.sourceAlignment := by
  rfl

@[simp]
theorem toBoundaryCanonicalRouteMeasureInput_faceContinuity
    [IsManifold I 1 M] :
    (toBoundaryCanonicalRouteMeasureInput D).faceContinuity =
      D.faceContinuity := by
  rfl

@[simp]
theorem toBoundaryCanonicalRouteMeasureInputViaControlledM8_sourceAlignment
    [IsManifold I 1 M] :
    (toBoundaryCanonicalRouteMeasureInputViaControlledM8 D).sourceAlignment =
      U.toControlledBoundaryCanonicalProjectLocalFields.sourceAlignment := by
  rfl

@[simp]
theorem toCanonicalBoundaryTargetCompactSupportInput_boundaryMeasureIntegral
    [IsManifold I 1 M] :
    (toCanonicalBoundaryTargetCompactSupportInput D).boundaryMeasureIntegral =
      (toBoundaryCanonicalRouteMeasureInput D).projectLocal.boundaryMeasureIntegral := by
  rfl

@[simp]
theorem toM8BoundaryMeasureData_boundaryPartitionTerm
    [IsManifold I 1 M] :
    (toM8BoundaryMeasureData D).boundaryPartitionTerm =
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.assembly.boundaryPartitionTerm := by
  rfl

@[simp]
theorem toM8BoundaryMeasureData_boundaryMeasureIntegral
    [IsManifold I 1 M] :
    (toM8BoundaryMeasureData D).boundaryMeasureIntegral =
      (toBoundaryCanonicalRouteMeasureInput D).projectLocal.boundaryMeasureIntegral := by
  rfl

end BoundaryUnifiedSupportFiniteMegaData

end BoundarySourceAlignmentUnifiedData

namespace NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]
variable
    (B :
      NaturalCompactSupportBulkProjectLocalAutoCollapsedInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)

/-- Collapsed endpoint mega package for the explicit global-measure route. -/
structure BoundaryUnifiedGlobalMeasureMegaEndpointData where
  /-- Unified boundary source-alignment and controlled-target data. -/
  unified :
    BoundarySourceAlignmentUnifiedData
      (I := I) (omega := omega)
      (selectedPartition := B.selectedPartition)
      (orientedBoundaryAtlas := B.orientedBoundaryAtlas)
      (BoundaryPiece := BoundaryPiece)
  /-- Target-image alignment between the endpoint input and `unified`. -/
  targetImageAlignment :
    BoundaryUnifiedEndpointTargetImageAlignment B unified
  /-- Explicit global-measure route data over `unified`. -/
  globalRoute :
    BoundarySourceAlignmentUnifiedData.BoundaryUnifiedGlobalMeasureMegaData
      unified

/-- Collapsed endpoint mega package for the support-finite route. -/
structure BoundaryUnifiedSupportFiniteMegaEndpointData where
  /-- Unified boundary source-alignment and controlled-target data. -/
  unified :
    BoundarySourceAlignmentUnifiedData
      (I := I) (omega := omega)
      (selectedPartition := B.selectedPartition)
      (orientedBoundaryAtlas := B.orientedBoundaryAtlas)
      (BoundaryPiece := BoundaryPiece)
  /-- Target-image alignment between the endpoint input and `unified`. -/
  targetImageAlignment :
    BoundaryUnifiedEndpointTargetImageAlignment B unified
  /-- Support-finite route data over `unified`. -/
  supportFiniteRoute :
    BoundarySourceAlignmentUnifiedData.BoundaryUnifiedSupportFiniteMegaData
      unified

namespace BoundaryUnifiedGlobalMeasureMegaEndpointData

variable
    {B :
      NaturalCompactSupportBulkProjectLocalAutoCollapsedInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu}

/-- Endpoint global-measure package from the mega endpoint data. -/
def toBoundaryUnifiedEndpointGlobalMeasureData
    (D : BoundaryUnifiedGlobalMeasureMegaEndpointData B) :
    BoundaryUnifiedEndpointGlobalMeasureData B where
  unified := D.unified
  targetImageAlignment := D.targetImageAlignment
  globalMeasure := D.globalRoute.globalMeasure
  faceContinuity := D.globalRoute.faceContinuity

/-- Canonical boundary route, rewritten to the endpoint target-image input. -/
def boundaryRoute
    (D : BoundaryUnifiedGlobalMeasureMegaEndpointData B) :
    BoundaryCanonicalRouteMeasureInput B.targetImageInput
      D.unified.toProjectLocalGlobalStokesData := by
  simpa [D.targetImageAlignment.targetImageInput_eq] using
    BoundarySourceAlignmentUnifiedData.BoundaryUnifiedGlobalMeasureMegaData.toBoundaryCanonicalRouteMeasureInput
      D.globalRoute

/-- Canonical compact-support boundary target package over the endpoint target. -/
def toCanonicalBoundaryTargetCompactSupportInput
    (D : BoundaryUnifiedGlobalMeasureMegaEndpointData B) :
    CanonicalBoundaryTargetCompactSupportInput
      (α := Fin n -> Real) B.targetImageInput
      (volume : Measure (Fin n -> Real)) := by
  simpa [D.targetImageAlignment.targetImageInput_eq] using
    BoundarySourceAlignmentUnifiedData.BoundaryUnifiedGlobalMeasureMegaData.toCanonicalBoundaryTargetCompactSupportInput
      D.globalRoute

/-- Boundary-only M8 measure data over the endpoint target-image input. -/
def toM8BoundaryMeasureData
    (D : BoundaryUnifiedGlobalMeasureMegaEndpointData B) :
    M8BoundaryMeasureData I omega B.selectedPartition
      B.targetImageInput.targetImages := by
  simpa [D.targetImageAlignment.targetImageInput_eq] using
    BoundarySourceAlignmentUnifiedData.BoundaryUnifiedGlobalMeasureMegaData.toM8BoundaryMeasureData
      D.globalRoute

/-- Compact-support separated-boundary base input generated from the package. -/
def toBulkBoundarySeparatedBaseInput
    (D : BoundaryUnifiedGlobalMeasureMegaEndpointData B) :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  D.toBoundaryUnifiedEndpointGlobalMeasureData.toBulkBoundarySeparatedBaseInput

/-- Canonical interface for the endpoint generated from the package. -/
def canonicalIntegralInterface
    (D : BoundaryUnifiedGlobalMeasureMegaEndpointData B) :
    CanonicalIntegralInterface I omega :=
  D.toBoundaryUnifiedEndpointGlobalMeasureData.canonicalIntegralInterface

/-- Full separated-boundary input after artificial-face cancellation is supplied. -/
def toBulkBoundarySeparatedInput
    (D : BoundaryUnifiedGlobalMeasureMegaEndpointData B)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece
        D.toBulkBoundarySeparatedBaseInput.selectedPartition
        D.toBulkBoundarySeparatedBaseInput.targetImageInput.targetImages
        D.toBulkBoundarySeparatedBaseInput.separatedMeasure.toM8MeasureLocalizationData) :
    NaturalCompactSupportBulkBoundarySeparatedInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  D.toBoundaryUnifiedEndpointGlobalMeasureData.toBulkBoundarySeparatedInput
    artificial

@[simp]
theorem toBoundaryUnifiedEndpointGlobalMeasureData_unified
    (D : BoundaryUnifiedGlobalMeasureMegaEndpointData B) :
    D.toBoundaryUnifiedEndpointGlobalMeasureData.unified = D.unified := by
  rfl

@[simp]
theorem toBoundaryUnifiedEndpointGlobalMeasureData_globalMeasure
    (D : BoundaryUnifiedGlobalMeasureMegaEndpointData B) :
    D.toBoundaryUnifiedEndpointGlobalMeasureData.globalMeasure =
      D.globalRoute.globalMeasure := by
  rfl

@[simp]
theorem toBoundaryUnifiedEndpointGlobalMeasureData_faceContinuity
    (D : BoundaryUnifiedGlobalMeasureMegaEndpointData B) :
    D.toBoundaryUnifiedEndpointGlobalMeasureData.faceContinuity =
      D.globalRoute.faceContinuity := by
  rfl

@[simp]
theorem toBulkBoundarySeparatedBaseInput_targetImageInput
    (D : BoundaryUnifiedGlobalMeasureMegaEndpointData B) :
    D.toBulkBoundarySeparatedBaseInput.targetImageInput =
      B.targetImageInput := by
  rfl

@[simp]
theorem toBulkBoundarySeparatedBaseInput_boundaryProjectLocal
    (D : BoundaryUnifiedGlobalMeasureMegaEndpointData B) :
    D.toBulkBoundarySeparatedBaseInput.boundaryProjectLocal =
      D.unified.toProjectLocalGlobalStokesData := by
  rfl

@[simp]
theorem canonicalIntegralInterface_manifoldExtDerivIntegral
    (D : BoundaryUnifiedGlobalMeasureMegaEndpointData B) :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.toBulkBoundarySeparatedBaseInput.separatedMeasure.toM8MeasureLocalizationData.bulkMeasureIntegral := by
  rfl

@[simp]
theorem canonicalIntegralInterface_boundaryFormIntegral
    (D : BoundaryUnifiedGlobalMeasureMegaEndpointData B) :
    D.canonicalIntegralInterface.boundaryFormIntegral =
      D.toBulkBoundarySeparatedBaseInput.separatedMeasure.toM8MeasureLocalizationData.boundaryMeasureIntegral := by
  rfl

/-- Stokes for the collapsed endpoint generated from global-measure mega data. -/
theorem canonical_stokes
    (D : BoundaryUnifiedGlobalMeasureMegaEndpointData B)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece
        D.toBulkBoundarySeparatedBaseInput.selectedPartition
        D.toBulkBoundarySeparatedBaseInput.targetImageInput.targetImages
        D.toBulkBoundarySeparatedBaseInput.separatedMeasure.toM8MeasureLocalizationData) :
    D.canonicalIntegralInterface.stokesStatement := by
  simpa [canonicalIntegralInterface, toBulkBoundarySeparatedBaseInput]
    using
      D.toBoundaryUnifiedEndpointGlobalMeasureData.canonical_stokes
        artificial

/-- Equality form of the global-measure mega endpoint theorem. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral
    (D : BoundaryUnifiedGlobalMeasureMegaEndpointData B)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece
        D.toBulkBoundarySeparatedBaseInput.selectedPartition
        D.toBulkBoundarySeparatedBaseInput.targetImageInput.targetImages
        D.toBulkBoundarySeparatedBaseInput.separatedMeasure.toM8MeasureLocalizationData) :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.canonicalIntegralInterface.boundaryFormIntegral := by
  simpa [CanonicalIntegralInterface.stokesStatement] using
    D.canonical_stokes artificial

end BoundaryUnifiedGlobalMeasureMegaEndpointData

namespace BoundaryUnifiedSupportFiniteMegaEndpointData

variable
    {B :
      NaturalCompactSupportBulkProjectLocalAutoCollapsedInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu}

/-- Endpoint support-finite package from the mega endpoint data. -/
def toBoundaryUnifiedEndpointSupportFiniteData
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B) :
    BoundaryUnifiedEndpointSupportFiniteData B where
  unified := D.unified
  targetImageAlignment := D.targetImageAlignment
  supportFinite := D.supportFiniteRoute.supportFinite
  faceContinuity := D.supportFiniteRoute.faceContinuity

/-- Endpoint global-measure package obtained by forgetting support-finite data. -/
def toBoundaryUnifiedEndpointGlobalMeasureData
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B) :
    BoundaryUnifiedEndpointGlobalMeasureData B :=
  D.toBoundaryUnifiedEndpointSupportFiniteData.toGlobalMeasureData

/-- Global-measure mega endpoint data obtained by forgetting support-finite data. -/
def toGlobalMeasureMegaEndpointData
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B) :
    BoundaryUnifiedGlobalMeasureMegaEndpointData B where
  unified := D.unified
  targetImageAlignment := D.targetImageAlignment
  globalRoute :=
    BoundarySourceAlignmentUnifiedData.BoundaryUnifiedSupportFiniteMegaData.toGlobalMeasureMegaData
      D.supportFiniteRoute

/-- Canonical boundary route, rewritten to the endpoint target-image input. -/
def boundaryRoute
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B) :
    BoundaryCanonicalRouteMeasureInput B.targetImageInput
      D.unified.toProjectLocalGlobalStokesData := by
  simpa [D.targetImageAlignment.targetImageInput_eq] using
    BoundarySourceAlignmentUnifiedData.BoundaryUnifiedSupportFiniteMegaData.toBoundaryCanonicalRouteMeasureInput
      D.supportFiniteRoute

/-- Global-measure view of the canonical boundary route over the endpoint target. -/
def globalBoundaryRoute
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B) :
    BoundaryCanonicalRouteMeasureInput B.targetImageInput
      D.unified.toProjectLocalGlobalStokesData := by
  simpa [D.targetImageAlignment.targetImageInput_eq] using
    BoundarySourceAlignmentUnifiedData.BoundaryUnifiedSupportFiniteMegaData.toGlobalBoundaryCanonicalRouteMeasureInput
      D.supportFiniteRoute

/-- Canonical compact-support boundary target package over the endpoint target. -/
def toCanonicalBoundaryTargetCompactSupportInput
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B) :
    CanonicalBoundaryTargetCompactSupportInput
      (α := Fin n -> Real) B.targetImageInput
      (volume : Measure (Fin n -> Real)) := by
  simpa [D.targetImageAlignment.targetImageInput_eq] using
    BoundarySourceAlignmentUnifiedData.BoundaryUnifiedSupportFiniteMegaData.toCanonicalBoundaryTargetCompactSupportInput
      D.supportFiniteRoute

/-- Boundary-only M8 measure data over the endpoint target-image input. -/
def toM8BoundaryMeasureData
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B) :
    M8BoundaryMeasureData I omega B.selectedPartition
      B.targetImageInput.targetImages := by
  simpa [D.targetImageAlignment.targetImageInput_eq] using
    BoundarySourceAlignmentUnifiedData.BoundaryUnifiedSupportFiniteMegaData.toM8BoundaryMeasureData
      D.supportFiniteRoute

/-- Global-measure view of the boundary-only M8 measure data over the endpoint target. -/
def toGlobalM8BoundaryMeasureData
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B) :
    M8BoundaryMeasureData I omega B.selectedPartition
      B.targetImageInput.targetImages := by
  simpa [D.targetImageAlignment.targetImageInput_eq] using
    BoundarySourceAlignmentUnifiedData.BoundaryUnifiedSupportFiniteMegaData.toGlobalM8BoundaryMeasureData
      D.supportFiniteRoute

/-- Compact-support separated-boundary base input generated from support-finite data. -/
def toBulkBoundarySeparatedBaseInput
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B) :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  D.toBoundaryUnifiedEndpointSupportFiniteData.toBulkBoundarySeparatedBaseInput

/-- Canonical interface for the endpoint generated from support-finite data. -/
def canonicalIntegralInterface
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B) :
    CanonicalIntegralInterface I omega :=
  D.toBoundaryUnifiedEndpointSupportFiniteData.canonicalIntegralInterface

/-- Full separated-boundary input after artificial-face cancellation is supplied. -/
def toBulkBoundarySeparatedInput
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece
        D.toBulkBoundarySeparatedBaseInput.selectedPartition
        D.toBulkBoundarySeparatedBaseInput.targetImageInput.targetImages
        D.toBulkBoundarySeparatedBaseInput.separatedMeasure.toM8MeasureLocalizationData) :
    NaturalCompactSupportBulkBoundarySeparatedInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  D.toBoundaryUnifiedEndpointSupportFiniteData.toGlobalMeasureData
    |>.toBulkBoundarySeparatedInput artificial

@[simp]
theorem toBoundaryUnifiedEndpointSupportFiniteData_supportFinite
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B) :
    D.toBoundaryUnifiedEndpointSupportFiniteData.supportFinite =
      D.supportFiniteRoute.supportFinite := by
  rfl

@[simp]
theorem toBoundaryUnifiedEndpointSupportFiniteData_faceContinuity
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B) :
    D.toBoundaryUnifiedEndpointSupportFiniteData.faceContinuity =
      D.supportFiniteRoute.faceContinuity := by
  rfl

@[simp]
theorem toBoundaryUnifiedEndpointGlobalMeasureData_globalMeasure
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B) :
    D.toBoundaryUnifiedEndpointGlobalMeasureData.globalMeasure =
      D.supportFiniteRoute.supportFinite.toGlobalMeasureFacts := by
  rfl

@[simp]
theorem toBulkBoundarySeparatedBaseInput_targetImageInput
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B) :
    D.toBulkBoundarySeparatedBaseInput.targetImageInput =
      B.targetImageInput := by
  rfl

@[simp]
theorem toBulkBoundarySeparatedBaseInput_boundaryProjectLocal
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B) :
    D.toBulkBoundarySeparatedBaseInput.boundaryProjectLocal =
      D.unified.toProjectLocalGlobalStokesData := by
  rfl

@[simp]
theorem canonicalIntegralInterface_manifoldExtDerivIntegral
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B) :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.toBulkBoundarySeparatedBaseInput.separatedMeasure.toM8MeasureLocalizationData.bulkMeasureIntegral := by
  rfl

@[simp]
theorem canonicalIntegralInterface_boundaryFormIntegral
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B) :
    D.canonicalIntegralInterface.boundaryFormIntegral =
      D.toBulkBoundarySeparatedBaseInput.separatedMeasure.toM8MeasureLocalizationData.boundaryMeasureIntegral := by
  rfl

/-- Stokes for the collapsed endpoint generated from support-finite mega data. -/
theorem canonical_stokes
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece
        D.toBulkBoundarySeparatedBaseInput.selectedPartition
        D.toBulkBoundarySeparatedBaseInput.targetImageInput.targetImages
        D.toBulkBoundarySeparatedBaseInput.separatedMeasure.toM8MeasureLocalizationData) :
    D.canonicalIntegralInterface.stokesStatement := by
  simpa [canonicalIntegralInterface, toBulkBoundarySeparatedBaseInput]
    using
      D.toBoundaryUnifiedEndpointSupportFiniteData.canonical_stokes
        artificial

/-- Equality form of the support-finite mega endpoint theorem. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral
    (D : BoundaryUnifiedSupportFiniteMegaEndpointData B)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece
        D.toBulkBoundarySeparatedBaseInput.selectedPartition
        D.toBulkBoundarySeparatedBaseInput.targetImageInput.targetImages
        D.toBulkBoundarySeparatedBaseInput.separatedMeasure.toM8MeasureLocalizationData) :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.canonicalIntegralInterface.boundaryFormIntegral := by
  simpa [CanonicalIntegralInterface.stokesStatement] using
    D.canonical_stokes artificial

end BoundaryUnifiedSupportFiniteMegaEndpointData

end NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

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

/-- Global measure facts generated from common-data face continuity and selected chart changes. -/
def globalMeasureOfSelectedChartChange :
    ProjectLocalBoundaryGlobalMeasureFacts
      C.boundaryUnified.toProjectLocalGlobalStokesData :=
  C.boundaryFaceContinuity.toGlobalMeasureFactsOfSelected
    C.boundaryChartChange

/-- Global-measure mega route package generated from common endpoint data. -/
def toBoundaryUnifiedGlobalMeasureMegaData :
    BoundarySourceAlignmentUnifiedData.BoundaryUnifiedGlobalMeasureMegaData
      C.boundaryUnified where
  globalMeasure := C.globalMeasureOfSelectedChartChange
  faceContinuity := C.boundaryFaceContinuity

/-- Support-finite mega route package generated from common endpoint data and
explicit support-finite facts. -/
def toBoundaryUnifiedSupportFiniteMegaData
    (supportFinite :
      ProjectLocalBoundarySupportFiniteMeasureFacts
        C.boundaryUnified.toProjectLocalGlobalStokesData) :
    BoundarySourceAlignmentUnifiedData.BoundaryUnifiedSupportFiniteMegaData
      C.boundaryUnified where
  supportFinite := supportFinite
  faceContinuity := C.boundaryFaceContinuity

@[simp]
theorem toBoundaryUnifiedGlobalMeasureMegaData_globalMeasure :
    C.toBoundaryUnifiedGlobalMeasureMegaData.globalMeasure =
      C.globalMeasureOfSelectedChartChange := by
  rfl

@[simp]
theorem toBoundaryUnifiedGlobalMeasureMegaData_faceContinuity :
    C.toBoundaryUnifiedGlobalMeasureMegaData.faceContinuity =
      C.boundaryFaceContinuity := by
  rfl

@[simp]
theorem toBoundaryUnifiedSupportFiniteMegaData_supportFinite
    (supportFinite :
      ProjectLocalBoundarySupportFiniteMeasureFacts
        C.boundaryUnified.toProjectLocalGlobalStokesData) :
    (C.toBoundaryUnifiedSupportFiniteMegaData supportFinite).supportFinite =
      supportFinite := by
  rfl

@[simp]
theorem toBoundaryUnifiedSupportFiniteMegaData_faceContinuity
    (supportFinite :
      ProjectLocalBoundarySupportFiniteMeasureFacts
        C.boundaryUnified.toProjectLocalGlobalStokesData) :
    (C.toBoundaryUnifiedSupportFiniteMegaData supportFinite).faceContinuity =
      C.boundaryFaceContinuity := by
  rfl

/-- Canonical boundary route generated from common data. -/
def boundaryRouteOfSelectedChartChange :
    BoundaryCanonicalRouteMeasureInput
      C.boundaryUnified.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      C.boundaryUnified.toProjectLocalGlobalStokesData :=
  BoundarySourceAlignmentUnifiedData.BoundaryUnifiedGlobalMeasureMegaData.toBoundaryCanonicalRouteMeasureInput
    C.toBoundaryUnifiedGlobalMeasureMegaData

/-- Boundary-only M8 measure data generated from common data. -/
def m8BoundaryMeasureDataOfSelectedChartChange :
    M8BoundaryMeasureData I omega D.selectedPartition
      C.boundaryUnified.toM8BoundaryControlledTargetInput.toM8TargetImageInput.targetImages :=
  BoundarySourceAlignmentUnifiedData.BoundaryUnifiedGlobalMeasureMegaData.toM8BoundaryMeasureData
    C.toBoundaryUnifiedGlobalMeasureMegaData

/-- Canonical compact-support boundary target input generated from common data. -/
def canonicalBoundaryTargetInputOfSelectedChartChange :
    CanonicalBoundaryTargetCompactSupportInput
      (α := Fin n -> Real)
      C.boundaryUnified.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      (volume : Measure (Fin n -> Real)) :=
  BoundarySourceAlignmentUnifiedData.BoundaryUnifiedGlobalMeasureMegaData.toCanonicalBoundaryTargetCompactSupportInput
    C.toBoundaryUnifiedGlobalMeasureMegaData

@[simp]
theorem boundaryRouteOfSelectedChartChange_sourceAlignment :
    C.boundaryRouteOfSelectedChartChange.sourceAlignment =
      C.boundaryUnified.toControlledBoundaryCanonicalProjectLocalFields.sourceAlignment := by
  rfl

/-- Boundary/measure endpoint input from common data and an ext-deriv route,
with a mega-route spelling. -/
def boundaryMeasureInputOfExtDerivRouteMega
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
      (I := I) (omega := omega) (rho := rho)
      D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu :=
  C.boundaryMeasureInputOfExtDerivRoute R

/-- Boundary/measure endpoint input from common data and a reconstruction route,
with a mega-route spelling. -/
def boundaryMeasureInputOfReconstructionRouteMega
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
      (I := I) (omega := omega) (rho := rho)
      D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu :=
  C.boundaryMeasureInputOfReconstructionRoute R

@[simp]
theorem boundaryMeasureInputOfExtDerivRouteMega_reconstructionSource
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (C.boundaryMeasureInputOfExtDerivRouteMega R).reconstructionSource =
      R.selectedReconstructionSource := by
  rfl

@[simp]
theorem boundaryMeasureInputOfExtDerivRouteMega_extDerivMeasure
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (C.boundaryMeasureInputOfExtDerivRouteMega R).extDerivMeasure =
      R.measure := by
  rfl

@[simp]
theorem boundaryMeasureInputOfExtDerivRouteMega_bulkLocalFacts
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (C.boundaryMeasureInputOfExtDerivRouteMega R).bulkLocalFacts =
      R.localFacts := by
  rfl

@[simp]
theorem boundaryMeasureInputOfReconstructionRouteMega_reconstructionSource
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (C.boundaryMeasureInputOfReconstructionRouteMega R).reconstructionSource =
      R.selectedReconstructionSource := by
  rfl

@[simp]
theorem boundaryMeasureInputOfReconstructionRouteMega_extDerivMeasure
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (C.boundaryMeasureInputOfReconstructionRouteMega R).extDerivMeasure =
      R.measure := by
  rfl

@[simp]
theorem boundaryMeasureInputOfReconstructionRouteMega_bulkLocalFacts
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (C.boundaryMeasureInputOfReconstructionRouteMega R).bulkLocalFacts =
      R.localFacts := by
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

/-- Global-measure mega route generated from a packaged unified endpoint input. -/
def toBoundaryUnifiedGlobalMeasureMegaData :
    BoundarySourceAlignmentUnifiedData.BoundaryUnifiedGlobalMeasureMegaData
      P.boundaryUnified :=
  P.toCommonData.toBoundaryUnifiedGlobalMeasureMegaData

/-- Support-finite mega route generated from a packaged unified endpoint input. -/
def toBoundaryUnifiedSupportFiniteMegaData
    (supportFinite :
      ProjectLocalBoundarySupportFiniteMeasureFacts
        P.boundaryUnified.toProjectLocalGlobalStokesData) :
    BoundarySourceAlignmentUnifiedData.BoundaryUnifiedSupportFiniteMegaData
      P.boundaryUnified :=
  P.toCommonData.toBoundaryUnifiedSupportFiniteMegaData supportFinite

/-- Canonical boundary route generated from packaged selected chart-change data. -/
def boundaryRouteOfSelectedChartChange :
    BoundaryCanonicalRouteMeasureInput
      P.boundaryUnified.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      P.boundaryUnified.toProjectLocalGlobalStokesData :=
  P.toCommonData.boundaryRouteOfSelectedChartChange

/-- Boundary-only M8 measure data generated from packaged selected chart-change data. -/
def m8BoundaryMeasureDataOfSelectedChartChange :
    M8BoundaryMeasureData I omega D.selectedPartition
      P.boundaryUnified.toM8BoundaryControlledTargetInput.toM8TargetImageInput.targetImages :=
  P.toCommonData.m8BoundaryMeasureDataOfSelectedChartChange

/-- Natural endpoint input from a packaged unified input and an ext-deriv route. -/
def naturalEndpointInputOfExtDerivRouteMega
    (R : P.toCommonData.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    NaturalCompactSupportEndpointNaturalInput
      I omega rho ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu :=
  D.naturalEndpointInputOfExtDerivRoute P.toCommonData R

/-- Natural endpoint input from a packaged unified input and a reconstruction route. -/
def naturalEndpointInputOfReconstructionRouteMega
    (R : P.toCommonData.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    NaturalCompactSupportEndpointNaturalInput
      I omega rho ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu :=
  D.naturalEndpointInputOfReconstructionRoute P.toCommonData R

@[simp]
theorem toBoundaryUnifiedGlobalMeasureMegaData_faceContinuity :
    P.toBoundaryUnifiedGlobalMeasureMegaData.faceContinuity =
      P.boundaryFaceContinuity := by
  rfl

@[simp]
theorem boundaryRouteOfSelectedChartChange_sourceAlignment :
    P.boundaryRouteOfSelectedChartChange.sourceAlignment =
      P.boundaryUnified.toControlledBoundaryCanonicalProjectLocalFields.sourceAlignment := by
  rfl

@[simp]
theorem naturalEndpointInputOfExtDerivRouteMega_chartBoxes
    (R : P.toCommonData.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (P.naturalEndpointInputOfExtDerivRouteMega R).chartBoxes = D := by
  rfl

@[simp]
theorem naturalEndpointInputOfExtDerivRouteMega_boundaryMeasure
    (R : P.toCommonData.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (P.naturalEndpointInputOfExtDerivRouteMega R).boundaryMeasure =
      P.toCommonData.boundaryMeasureInputOfExtDerivRouteMega R := by
  rfl

@[simp]
theorem naturalEndpointInputOfReconstructionRouteMega_chartBoxes
    (R : P.toCommonData.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (P.naturalEndpointInputOfReconstructionRouteMega R).chartBoxes = D := by
  rfl

@[simp]
theorem naturalEndpointInputOfReconstructionRouteMega_boundaryMeasure
    (R : P.toCommonData.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (P.naturalEndpointInputOfReconstructionRouteMega R).boundaryMeasure =
      P.toCommonData.boundaryMeasureInputOfReconstructionRouteMega R := by
  rfl

end NaturalBulkEndpointUnifiedInput

end BoundaryUnifiedMegaRouteAuto

end Stokes

end
