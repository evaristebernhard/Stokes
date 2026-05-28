import Stokes.Global.BoundaryUnifiedToControlledM8InputAuto
import Stokes.Global.BoundaryCanonicalTargetNaturalInputAuto

/-!
# Unified boundary data to canonical boundary target natural inputs

This module folds the controlled-target boundary route back into the unified
boundary source package.

`BoundarySourceAlignmentUnifiedData` already has the source-shrink family, its
M8 resolved fields, and the project-local source alignment.  Earlier modules
can view that data as an `M8BoundaryControlledTargetInput`, while the natural
canonical-target route asks for that controlled input plus project-local
face/measure facts.  The adapters below expose the natural records directly
from the unified data, so endpoint code does not have to assemble the
controlled M8 package by hand.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryUnifiedCanonicalTargetRouteAuto

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
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

/-- Unified boundary source data as the natural controlled-target input with
explicit global project-local measure facts. -/
def toBoundaryCanonicalTargetNaturalGlobalInput
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts U.toProjectLocalGlobalStokesData)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    BoundaryCanonicalTargetNaturalGlobalInput
      U.toM8BoundaryControlledTargetInput
      U.toProjectLocalGlobalStokesData where
  projectLocalFields := U.toControlledBoundaryCanonicalProjectLocalFields
  globalMeasure := globalMeasure
  faceContinuity := faceContinuity

/-- Unified boundary source data as the natural controlled-target input with
support-finite project-local measure facts. -/
def toBoundaryCanonicalTargetNaturalSupportFiniteInput
    (supportFinite :
      ProjectLocalBoundarySupportFiniteMeasureFacts
        U.toProjectLocalGlobalStokesData)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    BoundaryCanonicalTargetNaturalSupportFiniteInput
      U.toM8BoundaryControlledTargetInput
      U.toProjectLocalGlobalStokesData where
  projectLocalFields := U.toControlledBoundaryCanonicalProjectLocalFields
  supportFinite := supportFinite
  faceContinuity := faceContinuity

/-- Unified boundary source data as the natural controlled-target input whose
global measure facts are generated from canonical face continuity. -/
def toBoundaryCanonicalTargetNaturalFaceInput
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    BoundaryCanonicalTargetNaturalFaceInput
      U.toM8BoundaryControlledTargetInput
      U.toProjectLocalGlobalStokesData where
  projectLocalFields := U.toControlledBoundaryCanonicalProjectLocalFields
  faceContinuity := faceContinuity

@[simp]
theorem toBoundaryCanonicalTargetNaturalGlobalInput_projectLocalFields
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts U.toProjectLocalGlobalStokesData)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    (U.toBoundaryCanonicalTargetNaturalGlobalInput
      globalMeasure faceContinuity).projectLocalFields =
      U.toControlledBoundaryCanonicalProjectLocalFields := by
  rfl

@[simp]
theorem toBoundaryCanonicalTargetNaturalSupportFiniteInput_projectLocalFields
    (supportFinite :
      ProjectLocalBoundarySupportFiniteMeasureFacts
        U.toProjectLocalGlobalStokesData)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    (U.toBoundaryCanonicalTargetNaturalSupportFiniteInput
      supportFinite faceContinuity).projectLocalFields =
      U.toControlledBoundaryCanonicalProjectLocalFields := by
  rfl

@[simp]
theorem toBoundaryCanonicalTargetNaturalFaceInput_projectLocalFields
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    (U.toBoundaryCanonicalTargetNaturalFaceInput faceContinuity).projectLocalFields =
      U.toControlledBoundaryCanonicalProjectLocalFields := by
  rfl

/-- Canonical boundary route from unified data and explicit global measure
facts, without exposing the controlled M8 input. -/
def toBoundaryCanonicalRouteMeasureInputOfUnifiedGlobal
    [IsManifold I 1 M]
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts U.toProjectLocalGlobalStokesData)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    BoundaryCanonicalRouteMeasureInput
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      U.toProjectLocalGlobalStokesData :=
  (U.toBoundaryCanonicalTargetNaturalGlobalInput
    globalMeasure faceContinuity).toBoundaryCanonicalRouteMeasureInput

/-- Canonical boundary route from unified data and support-finite measure
facts, without exposing the controlled M8 input. -/
def toBoundaryCanonicalRouteMeasureInputOfUnifiedSupportFinite
    [IsManifold I 1 M]
    (supportFinite :
      ProjectLocalBoundarySupportFiniteMeasureFacts
        U.toProjectLocalGlobalStokesData)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    BoundaryCanonicalRouteMeasureInput
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      U.toProjectLocalGlobalStokesData :=
  (U.toBoundaryCanonicalTargetNaturalSupportFiniteInput
    supportFinite faceContinuity).toBoundaryCanonicalRouteMeasureInput

/-- Canonical boundary route from unified data and face-continuity facts alone. -/
def toBoundaryCanonicalRouteMeasureInputOfUnifiedFace
    [IsManifold I 1 M]
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    BoundaryCanonicalRouteMeasureInput
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      U.toProjectLocalGlobalStokesData :=
  (U.toBoundaryCanonicalTargetNaturalFaceInput
    faceContinuity).toBoundaryCanonicalRouteMeasureInput

/-- Canonical compact-support boundary target package from unified data and
explicit global measure facts. -/
def toCanonicalBoundaryTargetCompactSupportInputOfUnifiedGlobal
    [IsManifold I 1 M]
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts U.toProjectLocalGlobalStokesData)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    CanonicalBoundaryTargetCompactSupportInput
      (α := Fin n -> Real)
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      (volume : Measure (Fin n -> Real)) :=
  (U.toBoundaryCanonicalTargetNaturalGlobalInput
    globalMeasure faceContinuity).toCanonicalBoundaryTargetCompactSupportInput

/-- Canonical compact-support boundary target package from unified data and
support-finite measure facts. -/
def toCanonicalBoundaryTargetCompactSupportInputOfUnifiedSupportFinite
    [IsManifold I 1 M]
    (supportFinite :
      ProjectLocalBoundarySupportFiniteMeasureFacts
        U.toProjectLocalGlobalStokesData)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    CanonicalBoundaryTargetCompactSupportInput
      (α := Fin n -> Real)
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      (volume : Measure (Fin n -> Real)) :=
  (U.toBoundaryCanonicalTargetNaturalSupportFiniteInput
    supportFinite faceContinuity).toCanonicalBoundaryTargetCompactSupportInput

/-- Canonical compact-support boundary target package from unified data and
face-continuity facts alone. -/
def toCanonicalBoundaryTargetCompactSupportInputOfUnifiedFace
    [IsManifold I 1 M]
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    CanonicalBoundaryTargetCompactSupportInput
      (α := Fin n -> Real)
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      (volume : Measure (Fin n -> Real)) :=
  (U.toBoundaryCanonicalTargetNaturalFaceInput
    faceContinuity).toCanonicalBoundaryTargetCompactSupportInput

/-- Boundary-only M8 measure data from unified data and explicit global
measure facts. -/
def toM8BoundaryMeasureDataOfUnifiedGlobal
    [IsManifold I 1 M]
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts U.toProjectLocalGlobalStokesData)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    M8BoundaryMeasureData I omega selectedPartition
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.targetImages :=
  (U.toBoundaryCanonicalTargetNaturalGlobalInput
    globalMeasure faceContinuity).toM8BoundaryMeasureData

/-- Boundary-only M8 measure data from unified data and support-finite measure
facts. -/
def toM8BoundaryMeasureDataOfUnifiedSupportFinite
    [IsManifold I 1 M]
    (supportFinite :
      ProjectLocalBoundarySupportFiniteMeasureFacts
        U.toProjectLocalGlobalStokesData)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    M8BoundaryMeasureData I omega selectedPartition
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.targetImages :=
  (U.toBoundaryCanonicalTargetNaturalSupportFiniteInput
    supportFinite faceContinuity).toM8BoundaryMeasureData

/-- Boundary-only M8 measure data from unified data and face-continuity facts
alone. -/
def toM8BoundaryMeasureDataOfUnifiedFace
    [IsManifold I 1 M]
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    M8BoundaryMeasureData I omega selectedPartition
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.targetImages :=
  (U.toBoundaryCanonicalTargetNaturalFaceInput
    faceContinuity).toM8BoundaryMeasureData

@[simp]
theorem toBoundaryCanonicalRouteMeasureInputOfUnifiedGlobal_sourceAlignment
    [IsManifold I 1 M]
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts U.toProjectLocalGlobalStokesData)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    (U.toBoundaryCanonicalRouteMeasureInputOfUnifiedGlobal
      globalMeasure faceContinuity).sourceAlignment =
      U.toControlledBoundaryCanonicalProjectLocalFields.sourceAlignment := by
  rfl

@[simp]
theorem toBoundaryCanonicalRouteMeasureInputOfUnifiedFace_sourceAlignment
    [IsManifold I 1 M]
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    (U.toBoundaryCanonicalRouteMeasureInputOfUnifiedFace
      faceContinuity).sourceAlignment =
      U.toControlledBoundaryCanonicalProjectLocalFields.sourceAlignment := by
  rfl

@[simp]
theorem toM8BoundaryMeasureDataOfUnifiedGlobal_boundaryPartitionTerm
    [IsManifold I 1 M]
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts U.toProjectLocalGlobalStokesData)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    (U.toM8BoundaryMeasureDataOfUnifiedGlobal
      globalMeasure faceContinuity).boundaryPartitionTerm =
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.assembly.boundaryPartitionTerm := by
  rfl

@[simp]
theorem toM8BoundaryMeasureDataOfUnifiedFace_boundaryPartitionTerm
    [IsManifold I 1 M]
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    (U.toM8BoundaryMeasureDataOfUnifiedFace faceContinuity).boundaryPartitionTerm =
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.assembly.boundaryPartitionTerm := by
  rfl

end BoundarySourceAlignmentUnifiedData

end BoundaryUnifiedCanonicalTargetRouteAuto

end Stokes

end
