import Stokes.Global.BulkCanonicalLocalFactsFromExtDerivAuto
import Stokes.Global.NaturalCompactSupportEndpointNaturalInputAuto
import Stokes.Global.NaturalCompactSupportPartitionConstructorAuto
import Stokes.Global.BulkExtDerivProjectLocalAuto

/-!
# Natural bulk data from exterior-derivative routes

This module connects the synchronized bulk routes from
`BulkCanonicalLocalFactsFromExtDerivAuto` to the natural compact-support
endpoint input.

The declarations here do not prove new measure theorems.  They remove repeated
endpoint plumbing: once an exterior-derivative constructor route, or a raw
reconstruction route, has produced the synchronized `localFacts`,
`measureTerms`, `extDerivAE`, and selected reconstruction source, the natural
boundary/measure input can be assembled without separately passing
`bulkLocalFacts`, `reconstructionSource`, or the chartwise measure.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalBulkFromExtDerivRouteAuto

universe u w b ei eb

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

/--
The non-bulk endpoint data left after a natural finite-active chart-box
selection has fixed the selected partition.

Bulk reconstruction, bulk local facts, and the exterior-derivative chartwise
measure are intentionally absent: they are supplied below by the synchronized
bulk routes.
-/
structure NaturalBulkEndpointCommonData
    (D : NaturalFiniteActiveChartBoxSelectionData I omega rho)
    (BoundaryPiece : Type b)
    (mu : Measure (Fin (n + 1) -> Real))
    [IsFiniteMeasureOnCompacts mu]
    [IsManifold I 1 M] where
  /-- Oriented boundary-chart atlas used by the canonical boundary route. -/
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  /-- Unified boundary source-shrink/project-local package. -/
  boundaryUnified :
    BoundarySourceAlignmentUnifiedData
      (I := I) (omega := omega)
      (selectedPartition := D.selectedPartition)
      (orientedBoundaryAtlas := orientedBoundaryAtlas)
      (BoundaryPiece := BoundaryPiece)
  /-- Localized interior pieces for the selected partition. -/
  localized : LocalizedInteriorM8Fields I omega D.selectedPartition
  /-- The selected bulk measure is the ambient volume measure. -/
  measure_eq_volume : mu = volume
  /-- Lower-face continuity for the canonical boundary route. -/
  boundaryFaceContinuity :
    ProjectLocalBoundaryCanonicalFaceContinuityData
      boundaryUnified.toProjectLocalGlobalStokesData
  /-- Selected-target chart-change data for the canonical boundary route. -/
  boundaryChartChange :
    BoundaryChartChangeSelectedFamilyData
      boundaryUnified.toProjectLocalGlobalStokesData

namespace NaturalBulkEndpointCommonData

variable {D : NaturalFiniteActiveChartBoxSelectionData I omega rho}
variable
    (C :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        D BoundaryPiece mu)

/-- Boundary pieces induced by the unified boundary source data. -/
abbrev targetImages :
    BoundaryPieceFamilyInput I omega M BoundaryPiece :=
  C.boundaryUnified.toM8TargetImageInput.targetImages

/-- Constructor-indexed synchronized bulk route specialized to `C`. -/
abbrev ExtDerivConstructorRoute :=
  BulkCanonicalLocalFactsExtDerivConstructorRoute
    ExtInteriorPiece ExtBoundaryPiece D.selectedPartition C.targetImages
    C.localized

/-- Reconstruction-indexed synchronized bulk route specialized to `C`. -/
abbrev ReconstructionRoute :=
  BulkCanonicalLocalFactsReconstructionRoute
    ExtInteriorPiece ExtBoundaryPiece D.selectedPartition C.targetImages
    C.localized

/-- Natural boundary/measure input generated from an ext-deriv constructor route. -/
def toBoundaryMeasureInputOfExtDerivConstructorRoute
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
      (I := I) (omega := omega) (rho := rho)
      D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu where
  orientedBoundaryAtlas := C.orientedBoundaryAtlas
  boundaryUnified := C.boundaryUnified
  localized := C.localized
  reconstructionSource := R.selectedReconstructionSource
  extDerivMeasure := R.measure
  bulkLocalFacts := R.localFacts
  measure_eq_volume := C.measure_eq_volume
  boundaryFaceContinuity := C.boundaryFaceContinuity
  boundaryChartChange := C.boundaryChartChange

@[simp]
theorem toBoundaryMeasureInputOfExtDerivConstructorRoute_reconstructionSource
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (C.toBoundaryMeasureInputOfExtDerivConstructorRoute R).reconstructionSource =
      R.selectedReconstructionSource := by
  rfl

@[simp]
theorem toBoundaryMeasureInputOfExtDerivConstructorRoute_extDerivMeasure
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (C.toBoundaryMeasureInputOfExtDerivConstructorRoute R).extDerivMeasure =
      R.measure := by
  rfl

@[simp]
theorem toBoundaryMeasureInputOfExtDerivConstructorRoute_bulkLocalFacts
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (C.toBoundaryMeasureInputOfExtDerivConstructorRoute R).bulkLocalFacts =
      R.localFacts := by
  rfl

/-- Natural boundary/measure input generated from a reconstruction route. -/
def toBoundaryMeasureInputOfReconstructionRoute
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
      (I := I) (omega := omega) (rho := rho)
      D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu :=
  C.toBoundaryMeasureInputOfExtDerivConstructorRoute
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    R.toExtDerivConstructorRoute

@[simp]
theorem toBoundaryMeasureInputOfReconstructionRoute_reconstructionSource
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (C.toBoundaryMeasureInputOfReconstructionRoute R).reconstructionSource =
      R.selectedReconstructionSource := by
  rfl

@[simp]
theorem toBoundaryMeasureInputOfReconstructionRoute_extDerivMeasure
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (C.toBoundaryMeasureInputOfReconstructionRoute R).extDerivMeasure =
      R.measure := by
  rfl

@[simp]
theorem toBoundaryMeasureInputOfReconstructionRoute_bulkLocalFacts
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (C.toBoundaryMeasureInputOfReconstructionRoute R).bulkLocalFacts =
      R.localFacts := by
  rfl

end NaturalBulkEndpointCommonData

namespace NaturalFiniteActiveChartBoxSelectionData

variable
    (D : NaturalFiniteActiveChartBoxSelectionData I omega rho)
    (C :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        D BoundaryPiece mu)

/-- Fully packaged natural endpoint input from an ext-deriv constructor route. -/
def toNaturalEndpointInputOfExtDerivConstructorRoute
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    NaturalCompactSupportEndpointNaturalInput
      I omega rho ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu where
  chartBoxes := D
  boundaryMeasure :=
    C.toBoundaryMeasureInputOfExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      R

@[simp]
theorem toNaturalEndpointInputOfExtDerivConstructorRoute_chartBoxes
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (D.toNaturalEndpointInputOfExtDerivConstructorRoute C R).chartBoxes = D := by
  rfl

@[simp]
theorem toNaturalEndpointInputOfExtDerivConstructorRoute_boundaryMeasure
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (D.toNaturalEndpointInputOfExtDerivConstructorRoute C R).boundaryMeasure =
      C.toBoundaryMeasureInputOfExtDerivConstructorRoute R := by
  rfl

/-- Fully packaged natural endpoint input from a reconstruction route. -/
def toNaturalEndpointInputOfReconstructionRoute
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    NaturalCompactSupportEndpointNaturalInput
      I omega rho ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu where
  chartBoxes := D
  boundaryMeasure :=
    C.toBoundaryMeasureInputOfReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      R

@[simp]
theorem toNaturalEndpointInputOfReconstructionRoute_chartBoxes
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (D.toNaturalEndpointInputOfReconstructionRoute C R).chartBoxes = D := by
  rfl

@[simp]
theorem toNaturalEndpointInputOfReconstructionRoute_boundaryMeasure
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (D.toNaturalEndpointInputOfReconstructionRoute C R).boundaryMeasure =
      C.toBoundaryMeasureInputOfReconstructionRoute R := by
  rfl

end NaturalFiniteActiveChartBoxSelectionData

end NaturalBulkFromExtDerivRouteAuto

end Stokes

end
