import Stokes.Global.BoundaryUnifiedCanonicalTargetRouteAuto
import Stokes.Global.BoundaryUnifiedToEndpointBaseAuto

/-!
# Support-finite canonical boundary routes from unified boundary data

This module keeps the support-finite boundary route in one package.

`BoundarySourceAlignmentUnifiedData` already determines the controlled target
family, the project-local boundary data, and the source alignment.  The only
remaining measure-side inputs for the support-finite route are the
support-finite reconstruction facts and canonical face continuity.  The records
below expose the canonical route, compact-support target package, boundary M8
measure data, and endpoint theorem wrappers from exactly those inputs.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryCanonicalRouteFromUnifiedSupportFiniteAuto

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

/-- One-stop support-finite canonical route data for a unified boundary source
package. -/
structure BoundaryCanonicalRouteFromUnifiedSupportFiniteData where
  /-- Support-finite boundary reconstruction facts for the unified project-local package. -/
  supportFinite :
    ProjectLocalBoundarySupportFiniteMeasureFacts
      U.toProjectLocalGlobalStokesData
  /-- Canonical lower-face continuity/integrability facts. -/
  faceContinuity :
    ProjectLocalBoundaryCanonicalFaceContinuityData
      U.toProjectLocalGlobalStokesData

namespace BoundaryCanonicalRouteFromUnifiedSupportFiniteData

variable
    {U :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := selectedPartition)
        (orientedBoundaryAtlas := orientedBoundaryAtlas)
        (BoundaryPiece := BoundaryPiece)}
    (D : BoundaryCanonicalRouteFromUnifiedSupportFiniteData U)

/-- The global-measure facts obtained by forgetting support-finite support data. -/
def globalMeasure :
    ProjectLocalBoundaryGlobalMeasureFacts U.toProjectLocalGlobalStokesData :=
  D.supportFinite.toGlobalMeasureFacts

/-- Natural controlled-target input in support-finite form. -/
def toNaturalSupportFiniteInput :
    BoundaryCanonicalTargetNaturalSupportFiniteInput
      U.toM8BoundaryControlledTargetInput
      U.toProjectLocalGlobalStokesData :=
  U.toBoundaryCanonicalTargetNaturalSupportFiniteInput
    D.supportFinite D.faceContinuity

/-- Natural controlled-target input after forgetting support-finite data to
global measure facts. -/
def toNaturalGlobalInput :
    BoundaryCanonicalTargetNaturalGlobalInput
      U.toM8BoundaryControlledTargetInput
      U.toProjectLocalGlobalStokesData :=
  U.toBoundaryCanonicalTargetNaturalGlobalInput
    D.globalMeasure D.faceContinuity

/-- Canonical boundary route from support-finite facts and unified source data. -/
def toBoundaryCanonicalRouteMeasureInput
    [IsManifold I 1 M] :
    BoundaryCanonicalRouteMeasureInput
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      U.toProjectLocalGlobalStokesData :=
  U.toBoundaryCanonicalRouteMeasureInputOfUnifiedSupportFinite
    D.supportFinite D.faceContinuity

/-- Canonical boundary route through the global-measure view of the same
support-finite data. -/
def toGlobalBoundaryCanonicalRouteMeasureInput
    [IsManifold I 1 M] :
    BoundaryCanonicalRouteMeasureInput
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      U.toProjectLocalGlobalStokesData :=
  U.toBoundaryCanonicalRouteMeasureInputOfUnifiedGlobal
    D.globalMeasure D.faceContinuity

/-- Canonical compact-support boundary target package from support-finite
unified data. -/
def toCanonicalBoundaryTargetCompactSupportInput
    [IsManifold I 1 M] :
    CanonicalBoundaryTargetCompactSupportInput
      (α := Fin n -> Real)
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      (volume : Measure (Fin n -> Real)) :=
  U.toCanonicalBoundaryTargetCompactSupportInputOfUnifiedSupportFinite
    D.supportFinite D.faceContinuity

/-- Boundary-only M8 measure data from support-finite unified data. -/
def toM8BoundaryMeasureData
    [IsManifold I 1 M] :
    M8BoundaryMeasureData I omega selectedPartition
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.targetImages :=
  U.toM8BoundaryMeasureDataOfUnifiedSupportFinite
    D.supportFinite D.faceContinuity

@[simp]
theorem toNaturalSupportFiniteInput_supportFinite :
    D.toNaturalSupportFiniteInput.supportFinite = D.supportFinite := by
  rfl

@[simp]
theorem toNaturalSupportFiniteInput_faceContinuity :
    D.toNaturalSupportFiniteInput.faceContinuity = D.faceContinuity := by
  rfl

@[simp]
theorem toNaturalGlobalInput_globalMeasure :
    D.toNaturalGlobalInput.globalMeasure = D.globalMeasure := by
  rfl

@[simp]
theorem toBoundaryCanonicalRouteMeasureInput_sourceAlignment
    [IsManifold I 1 M] :
    D.toBoundaryCanonicalRouteMeasureInput.sourceAlignment =
      U.toControlledBoundaryCanonicalProjectLocalFields.sourceAlignment := by
  rfl

@[simp]
theorem toGlobalBoundaryCanonicalRouteMeasureInput_sourceAlignment
    [IsManifold I 1 M] :
    D.toGlobalBoundaryCanonicalRouteMeasureInput.sourceAlignment =
      U.toControlledBoundaryCanonicalProjectLocalFields.sourceAlignment := by
  rfl

@[simp]
theorem toM8BoundaryMeasureData_boundaryPartitionTerm
    [IsManifold I 1 M] :
    D.toM8BoundaryMeasureData.boundaryPartitionTerm =
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.assembly.boundaryPartitionTerm := by
  rfl

@[simp]
theorem toM8BoundaryMeasureData_boundaryMeasureIntegral
    [IsManifold I 1 M] :
    D.toM8BoundaryMeasureData.boundaryMeasureIntegral =
      D.toBoundaryCanonicalRouteMeasureInput.projectLocal.boundaryMeasureIntegral := by
  rfl

end BoundaryCanonicalRouteFromUnifiedSupportFiniteData

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

/-- Endpoint-facing support-finite package from unified boundary data.

This is the theorem-facing counterpart of
`BoundarySourceAlignmentUnifiedData.BoundaryCanonicalRouteFromUnifiedSupportFiniteData`:
it also carries the target-image equality needed to reinterpret the unified
boundary route as the boundary route of the collapsed endpoint input `B`. -/
structure BoundaryCanonicalUnifiedSupportFiniteEndpointData where
  /-- Unified boundary source-alignment and controlled-target data. -/
  unified :
    BoundarySourceAlignmentUnifiedData
      (I := I) (omega := omega)
      (selectedPartition := B.selectedPartition)
      (orientedBoundaryAtlas := B.orientedBoundaryAtlas)
      (BoundaryPiece := BoundaryPiece)
  /-- Alignment between `B.targetImageInput` and the target-image input
  generated by `unified`. -/
  targetImageAlignment :
    BoundaryUnifiedEndpointTargetImageAlignment B unified
  /-- Support-finite boundary measure reconstruction facts. -/
  supportFinite :
    ProjectLocalBoundarySupportFiniteMeasureFacts
      unified.toProjectLocalGlobalStokesData
  /-- Canonical lower-face continuity/integrability facts. -/
  faceContinuity :
    ProjectLocalBoundaryCanonicalFaceContinuityData
      unified.toProjectLocalGlobalStokesData

namespace BoundaryCanonicalUnifiedSupportFiniteEndpointData

variable
    {B :
      NaturalCompactSupportBulkProjectLocalAutoCollapsedInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu}
    (D : BoundaryCanonicalUnifiedSupportFiniteEndpointData B)

/-- Boundary-route data over the unified source package. -/
def toUnifiedSupportFiniteRouteData :
    BoundarySourceAlignmentUnifiedData.BoundaryCanonicalRouteFromUnifiedSupportFiniteData
      D.unified where
  supportFinite := D.supportFinite
  faceContinuity := D.faceContinuity

/-- Existing endpoint support-finite package generated from the compact route data. -/
def toBoundaryUnifiedEndpointSupportFiniteData :
    BoundaryUnifiedEndpointSupportFiniteData B where
  unified := D.unified
  targetImageAlignment := D.targetImageAlignment
  supportFinite := D.supportFinite
  faceContinuity := D.faceContinuity

/-- Existing endpoint global-measure package obtained by forgetting the
support-finite support facts. -/
def toBoundaryUnifiedEndpointGlobalMeasureData :
    BoundaryUnifiedEndpointGlobalMeasureData B :=
  D.toBoundaryUnifiedEndpointSupportFiniteData.toGlobalMeasureData

/-- The support-finite canonical route, rewritten to the endpoint target-image input. -/
def toBoundaryCanonicalRouteMeasureInput :
    BoundaryCanonicalRouteMeasureInput B.targetImageInput
      D.unified.toProjectLocalGlobalStokesData := by
  simpa [D.targetImageAlignment.targetImageInput_eq] using
    D.toUnifiedSupportFiniteRouteData.toBoundaryCanonicalRouteMeasureInput

/-- The global-measure view of the same support-finite route, rewritten to the
endpoint target-image input. -/
def toGlobalBoundaryCanonicalRouteMeasureInput :
    BoundaryCanonicalRouteMeasureInput B.targetImageInput
      D.unified.toProjectLocalGlobalStokesData := by
  simpa [D.targetImageAlignment.targetImageInput_eq] using
    D.toUnifiedSupportFiniteRouteData.toGlobalBoundaryCanonicalRouteMeasureInput

/-- Compact-support boundary target package for the endpoint target-image input. -/
def toCanonicalBoundaryTargetCompactSupportInput :
    CanonicalBoundaryTargetCompactSupportInput
      (α := Fin n -> Real) B.targetImageInput
      (volume : Measure (Fin n -> Real)) := by
  simpa [D.targetImageAlignment.targetImageInput_eq] using
    D.toUnifiedSupportFiniteRouteData.toCanonicalBoundaryTargetCompactSupportInput

/-- Boundary-only M8 measure data for the endpoint target-image input. -/
def toM8BoundaryMeasureData :
    M8BoundaryMeasureData I omega B.selectedPartition
      B.targetImageInput.targetImages := by
  simpa [D.targetImageAlignment.targetImageInput_eq] using
    D.toUnifiedSupportFiniteRouteData.toM8BoundaryMeasureData

/-- Compact-support separated-boundary base input generated from the
support-finite unified route. -/
def toBulkBoundarySeparatedBaseInput :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  D.toBoundaryUnifiedEndpointSupportFiniteData.toBulkBoundarySeparatedBaseInput

/-- Canonical interface for the endpoint generated from support-finite unified
boundary data. -/
def canonicalIntegralInterface :
    CanonicalIntegralInterface I omega :=
  D.toBoundaryUnifiedEndpointSupportFiniteData.canonicalIntegralInterface

/-- Full separated-boundary Stokes input generated from support-finite unified
boundary data, once artificial-face cancellation is supplied. -/
def toBulkBoundarySeparatedInput
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece
        D.toBulkBoundarySeparatedBaseInput.selectedPartition
        D.toBulkBoundarySeparatedBaseInput.targetImageInput.targetImages
        D.toBulkBoundarySeparatedBaseInput.separatedMeasure.toM8MeasureLocalizationData) :
    NaturalCompactSupportBulkBoundarySeparatedInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  D.toBoundaryUnifiedEndpointSupportFiniteData.toGlobalMeasureData.toBulkBoundarySeparatedInput
    artificial

@[simp]
theorem toBoundaryUnifiedEndpointSupportFiniteData_supportFinite :
    D.toBoundaryUnifiedEndpointSupportFiniteData.supportFinite =
      D.supportFinite := by
  rfl

@[simp]
theorem toBoundaryUnifiedEndpointSupportFiniteData_faceContinuity :
    D.toBoundaryUnifiedEndpointSupportFiniteData.faceContinuity =
      D.faceContinuity := by
  rfl

@[simp]
theorem toBulkBoundarySeparatedBaseInput_targetImageInput :
    D.toBulkBoundarySeparatedBaseInput.targetImageInput =
      B.targetImageInput := by
  rfl

@[simp]
theorem toBulkBoundarySeparatedBaseInput_boundaryProjectLocal :
    D.toBulkBoundarySeparatedBaseInput.boundaryProjectLocal =
      D.unified.toProjectLocalGlobalStokesData := by
  rfl

@[simp]
theorem canonicalIntegralInterface_manifoldExtDerivIntegral :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.toBulkBoundarySeparatedBaseInput.separatedMeasure.toM8MeasureLocalizationData.bulkMeasureIntegral := by
  rfl

@[simp]
theorem canonicalIntegralInterface_boundaryFormIntegral :
    D.canonicalIntegralInterface.boundaryFormIntegral =
      D.toBulkBoundarySeparatedBaseInput.separatedMeasure.toM8MeasureLocalizationData.boundaryMeasureIntegral := by
  rfl

/-- Stokes for the endpoint generated from support-finite unified boundary
data, stated in canonical interface form. -/
theorem canonical_stokes
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece
        D.toBulkBoundarySeparatedBaseInput.selectedPartition
        D.toBulkBoundarySeparatedBaseInput.targetImageInput.targetImages
        D.toBulkBoundarySeparatedBaseInput.separatedMeasure.toM8MeasureLocalizationData) :
    D.canonicalIntegralInterface.stokesStatement := by
  simpa [canonicalIntegralInterface, toBulkBoundarySeparatedBaseInput]
    using D.toBoundaryUnifiedEndpointSupportFiniteData.canonical_stokes
      artificial

/-- Equality form of the support-finite unified endpoint theorem. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece
        D.toBulkBoundarySeparatedBaseInput.selectedPartition
        D.toBulkBoundarySeparatedBaseInput.targetImageInput.targetImages
        D.toBulkBoundarySeparatedBaseInput.separatedMeasure.toM8MeasureLocalizationData) :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.canonicalIntegralInterface.boundaryFormIntegral := by
  simpa [canonicalIntegralInterface, toBulkBoundarySeparatedBaseInput]
    using
      D.toBoundaryUnifiedEndpointSupportFiniteData.manifoldExtDerivIntegral_eq_boundaryFormIntegral
        artificial

end BoundaryCanonicalUnifiedSupportFiniteEndpointData

end NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

end BoundaryCanonicalRouteFromUnifiedSupportFiniteAuto

end Stokes

end
