import Stokes.Global.BoundarySourceAlignmentUnified
import Stokes.Global.BoundaryControlledTargetOrientationEndpointAuto
import Stokes.Global.BoundaryCanonicalTargetFromControlledCOVAuto

/-!
# Unified boundary source data as controlled M8 input

This module bridges the source-shrink boundary package to the newer controlled
target-box route.

`BoundarySourceAlignmentUnifiedData` already stores a source-shrink family and
its M8-resolved fields.  `BoundaryControlledTargetToM8Auto` can view the same
source-shrink data as a controlled target-image family.  The declarations below
package that conversion so endpoint code can ask for one unified boundary
source package instead of manually assembling the controlled target family and
its M8 fields.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryUnifiedToControlledM8InputAuto

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

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.M8ResolvedFields

variable
    {F :
      BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega M
        BoundaryPiece}

/-- View source-shrink M8 fields as controlled-target M8 fields.

The controlled family is induced by `F.toControlledTargetImageFamily`, whose
resolved target-image family is definitionally the same as `F`'s resolved
target-image family.  Thus all global M8 fields can be reused directly.
-/
def toControlledM8ResolvedFields
    (D :
      M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    BoundaryChartControlledTargetImageFamily.M8ResolvedFields
      F.toControlledTargetImageFamily selectedPartition orientedBoundaryAtlas where
  sourceExtendedBox := by
    intro x hx q hq
    simpa [BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.toControlledTargetImageFamily_resolvedFamily]
      using D.sourceExtendedBox x hx q hq
  partitionTargetChart := D.partitionTargetChart
  partitionTargetBox := by
    intro x q
    simpa [BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.toControlledTargetImageFamily_resolvedFamily]
      using D.partitionTargetBox x q
  partitionSelectedBox := by
    intro x hx q hq
    simpa [BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.toControlledTargetImageFamily_resolvedFamily]
      using D.partitionSelectedBox x hx q hq
  boundaryPartitionTerm := D.boundaryPartitionTerm
  boundaryPartitionTerm_eq := by
    intro x hx q hq
    simpa [BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.toControlledTargetImageFamily_resolvedFamily]
      using D.boundaryPartitionTerm_eq x hx q hq
  active_eq := by
    simpa [BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.toControlledTargetImageFamily_resolvedFamily]
      using D.active_eq
  source_mem := by
    intro x hx q hq
    simpa [BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.toControlledTargetImageFamily_resolvedFamily]
      using D.source_mem x hx q hq
  boundarySource_mem := by
    intro x hx q hq
    simpa [BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.toControlledTargetImageFamily_resolvedFamily]
      using D.boundarySource_mem x hx q hq
  boundaryTarget_mem := by
    intro x hx q hq
    simpa [BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.toControlledTargetImageFamily_resolvedFamily]
      using D.boundaryTarget_mem x hx q hq

@[simp]
theorem toControlledM8ResolvedFields_boundaryPartitionTerm
    (D :
      M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    D.toControlledM8ResolvedFields.boundaryPartitionTerm =
      D.boundaryPartitionTerm :=
  rfl

@[simp]
theorem toControlledM8ResolvedFields_active_eq
    (D :
      M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    D.toControlledM8ResolvedFields.active_eq = D.active_eq := by
  rfl

@[simp]
theorem toControlledM8ResolvedFields_toM8TargetImageInput
    (D :
      M8ResolvedFields F selectedPartition orientedBoundaryAtlas) :
    D.toControlledM8ResolvedFields.toM8TargetImageInput =
      D.toM8TargetImageInput := by
  rfl

end BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.M8ResolvedFields

namespace BoundarySourceAlignmentUnifiedData

variable
    (U :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := selectedPartition)
        (orientedBoundaryAtlas := orientedBoundaryAtlas)
        (BoundaryPiece := BoundaryPiece))

/-- Controlled target-image family induced from the unified source-shrink
family. -/
def toControlledTargetImageFamily :
    BoundaryChartControlledTargetImageFamily I omega M BoundaryPiece :=
  U.family.toControlledTargetImageFamily

/-- Controlled M8-resolved fields induced from the unified source-shrink M8
fields. -/
def toControlledM8ResolvedFields :
    BoundaryChartControlledTargetImageFamily.M8ResolvedFields
      U.toControlledTargetImageFamily selectedPartition orientedBoundaryAtlas :=
  U.m8Fields.toControlledM8ResolvedFields

/-- Unified source-alignment data as one controlled-target M8 input. -/
def toM8BoundaryControlledTargetInput :
    M8BoundaryControlledTargetInput I omega selectedPartition
      orientedBoundaryAtlas BoundaryPiece where
  family := U.toControlledTargetImageFamily
  fields := U.toControlledM8ResolvedFields

@[simp]
theorem toM8BoundaryControlledTargetInput_family :
    U.toM8BoundaryControlledTargetInput.family =
      U.toControlledTargetImageFamily :=
  rfl

@[simp]
theorem toM8BoundaryControlledTargetInput_fields :
    U.toM8BoundaryControlledTargetInput.fields =
      U.toControlledM8ResolvedFields :=
  rfl

@[simp]
theorem toM8BoundaryControlledTargetInput_toM8TargetImageInput :
    U.toM8BoundaryControlledTargetInput.toM8TargetImageInput =
      U.toM8TargetImageInput := by
  rfl

/-- Project-local alignment fields for the controlled M8 input obtained from
unified source data. -/
def toControlledBoundaryCanonicalProjectLocalFields :
    M8BoundaryControlledTargetInput.BoundaryCanonicalProjectLocalFields
      U.toM8BoundaryControlledTargetInput
      (P := U.toProjectLocalGlobalStokesData) where
  sourceAlignment := by
    simpa [toM8BoundaryControlledTargetInput]
      using U.toBoundarySourceProjectLocalAlignment
  boundaryPartitionTerm_eq_controlled := by
    intro x q
    rfl

/-- Canonical boundary route from unified data through the controlled-target
M8 input. -/
def toBoundaryCanonicalRouteMeasureInputOfControlledM8
    [IsManifold I 1 M]
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts U.toProjectLocalGlobalStokesData)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData) :
    BoundaryCanonicalRouteMeasureInput
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput
      U.toProjectLocalGlobalStokesData :=
  M8BoundaryControlledTargetInput.BoundaryCanonicalProjectLocalFields.toBoundaryCanonicalRouteMeasureInputOfGlobalMeasure
      U.toM8BoundaryControlledTargetInput
      U.toControlledBoundaryCanonicalProjectLocalFields
      globalMeasure faceContinuity

/-- Support-finite canonical boundary route from unified data through the
controlled-target M8 input. -/
def toBoundaryCanonicalRouteMeasureInputOfControlledM8SupportFinite
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
  M8BoundaryControlledTargetInput.BoundaryCanonicalProjectLocalFields.toBoundaryCanonicalRouteMeasureInputOfSupportFinite
      U.toM8BoundaryControlledTargetInput
      U.toControlledBoundaryCanonicalProjectLocalFields
      supportFinite faceContinuity

end BoundarySourceAlignmentUnifiedData

namespace NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

section Endpoint

variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]

/-- Endpoint base input from a unified boundary source package, routed through
the controlled-target M8 input. -/
def toBulkBoundarySeparatedBaseInputOfControlledM8
    (B :
      NaturalCompactSupportBulkProjectLocalAutoCollapsedInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece rho mu)
    (U :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := B.selectedPartition)
        (orientedBoundaryAtlas := B.orientedBoundaryAtlas)
        (BoundaryPiece := BoundaryPiece))
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts U.toProjectLocalGlobalStokesData)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        U.toProjectLocalGlobalStokesData)
    (targetImageInput_eq :
      B.targetImageInput =
        U.toM8BoundaryControlledTargetInput.toM8TargetImageInput) :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu :=
  B.toBulkBoundarySeparatedBaseInputOfControlledTargetOrientationMembership
    U.toProjectLocalGlobalStokesData globalMeasure faceContinuity
    U.toM8BoundaryControlledTargetInput.family
    U.toM8BoundaryControlledTargetInput.fields
    rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    targetImageInput_eq

end Endpoint

end NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

end BoundaryUnifiedToControlledM8InputAuto

end Stokes

end
