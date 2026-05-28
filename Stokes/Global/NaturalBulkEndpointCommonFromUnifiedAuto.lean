import Stokes.Global.NaturalBulkFromExtDerivRouteAuto
import Stokes.Global.BulkBoundaryActiveAlignmentAuto
import Stokes.Global.BoundaryUnifiedCanonicalTargetRouteAuto

/-!
# Natural bulk endpoint common data from unified boundary input

This module gives a named constructor for the common endpoint data used by the
natural bulk/ext-deriv routes.  The data is already present once a finite active
chart-box selection has fixed the selected partition and the boundary side is
given by `BoundarySourceAlignmentUnifiedData`; the declarations below keep that
assembly out of theorem-facing code.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalBulkEndpointCommonFromUnifiedAuto

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

namespace NaturalBulkEndpointCommonData

variable {D : NaturalFiniteActiveChartBoxSelectionData I omega rho}

/-- Build the reusable common endpoint package from the natural unified
boundary data. -/
def ofUnified
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (boundaryUnified :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := D.selectedPartition)
        (orientedBoundaryAtlas := orientedBoundaryAtlas)
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
      D BoundaryPiece mu where
  orientedBoundaryAtlas := orientedBoundaryAtlas
  boundaryUnified := boundaryUnified
  localized := localized
  measure_eq_volume := measure_eq_volume
  boundaryFaceContinuity := boundaryFaceContinuity
  boundaryChartChange := boundaryChartChange

@[simp]
theorem ofUnified_orientedBoundaryAtlas
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (boundaryUnified :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := D.selectedPartition)
        (orientedBoundaryAtlas := orientedBoundaryAtlas)
        (BoundaryPiece := BoundaryPiece))
    (localized : LocalizedInteriorM8Fields I omega D.selectedPartition)
    (measure_eq_volume : mu = volume)
    (boundaryFaceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        boundaryUnified.toProjectLocalGlobalStokesData)
    (boundaryChartChange :
      BoundaryChartChangeSelectedFamilyData
        boundaryUnified.toProjectLocalGlobalStokesData) :
    (ofUnified
      (I := I) (omega := omega) (rho := rho) (BoundaryPiece := BoundaryPiece)
      (D := D) (mu := mu)
      orientedBoundaryAtlas boundaryUnified localized measure_eq_volume
      boundaryFaceContinuity boundaryChartChange).orientedBoundaryAtlas =
      orientedBoundaryAtlas := by
  rfl

@[simp]
theorem ofUnified_boundaryUnified
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (boundaryUnified :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := D.selectedPartition)
        (orientedBoundaryAtlas := orientedBoundaryAtlas)
        (BoundaryPiece := BoundaryPiece))
    (localized : LocalizedInteriorM8Fields I omega D.selectedPartition)
    (measure_eq_volume : mu = volume)
    (boundaryFaceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        boundaryUnified.toProjectLocalGlobalStokesData)
    (boundaryChartChange :
      BoundaryChartChangeSelectedFamilyData
        boundaryUnified.toProjectLocalGlobalStokesData) :
    (ofUnified
      (I := I) (omega := omega) (rho := rho) (BoundaryPiece := BoundaryPiece)
      (D := D) (mu := mu)
      orientedBoundaryAtlas boundaryUnified localized measure_eq_volume
      boundaryFaceContinuity boundaryChartChange).boundaryUnified =
      boundaryUnified := by
  rfl

@[simp]
theorem ofUnified_localized
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (boundaryUnified :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := D.selectedPartition)
        (orientedBoundaryAtlas := orientedBoundaryAtlas)
        (BoundaryPiece := BoundaryPiece))
    (localized : LocalizedInteriorM8Fields I omega D.selectedPartition)
    (measure_eq_volume : mu = volume)
    (boundaryFaceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        boundaryUnified.toProjectLocalGlobalStokesData)
    (boundaryChartChange :
      BoundaryChartChangeSelectedFamilyData
        boundaryUnified.toProjectLocalGlobalStokesData) :
    (ofUnified
      (I := I) (omega := omega) (rho := rho) (BoundaryPiece := BoundaryPiece)
      (D := D) (mu := mu)
      orientedBoundaryAtlas boundaryUnified localized measure_eq_volume
      boundaryFaceContinuity boundaryChartChange).localized =
      localized := by
  rfl

@[simp]
theorem ofUnified_measure_eq_volume
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (boundaryUnified :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := D.selectedPartition)
        (orientedBoundaryAtlas := orientedBoundaryAtlas)
        (BoundaryPiece := BoundaryPiece))
    (localized : LocalizedInteriorM8Fields I omega D.selectedPartition)
    (measure_eq_volume : mu = volume)
    (boundaryFaceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData
        boundaryUnified.toProjectLocalGlobalStokesData)
    (boundaryChartChange :
      BoundaryChartChangeSelectedFamilyData
        boundaryUnified.toProjectLocalGlobalStokesData) :
    (ofUnified
      (I := I) (omega := omega) (rho := rho) (BoundaryPiece := BoundaryPiece)
      (D := D) (mu := mu)
      orientedBoundaryAtlas boundaryUnified localized measure_eq_volume
      boundaryFaceContinuity boundaryChartChange).measure_eq_volume =
      measure_eq_volume := by
  rfl

/-- Theorem-facing spelling of the boundary/measure input generated by an
ext-deriv constructor route. -/
def boundaryMeasureInputOfExtDerivRoute
    (C :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        D BoundaryPiece mu)
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
      (I := I) (omega := omega) (rho := rho)
      D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu :=
  C.toBoundaryMeasureInputOfExtDerivConstructorRoute R

/-- Theorem-facing spelling of the boundary/measure input generated by a
reconstruction route. -/
def boundaryMeasureInputOfReconstructionRoute
    (C :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        D BoundaryPiece mu)
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
      (I := I) (omega := omega) (rho := rho)
      D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu :=
  C.toBoundaryMeasureInputOfReconstructionRoute R

@[simp]
theorem boundaryMeasureInputOfExtDerivRoute_reconstructionSource
    (C :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        D BoundaryPiece mu)
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (C.boundaryMeasureInputOfExtDerivRoute R).reconstructionSource =
      R.selectedReconstructionSource := by
  rfl

@[simp]
theorem boundaryMeasureInputOfExtDerivRoute_bulkLocalFacts
    (C :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        D BoundaryPiece mu)
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (C.boundaryMeasureInputOfExtDerivRoute R).bulkLocalFacts =
      R.localFacts := by
  rfl

@[simp]
theorem boundaryMeasureInputOfReconstructionRoute_reconstructionSource
    (C :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        D BoundaryPiece mu)
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (C.boundaryMeasureInputOfReconstructionRoute R).reconstructionSource =
      R.selectedReconstructionSource := by
  rfl

@[simp]
theorem boundaryMeasureInputOfReconstructionRoute_bulkLocalFacts
    (C :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        D BoundaryPiece mu)
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (C.boundaryMeasureInputOfReconstructionRoute R).bulkLocalFacts =
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

/-- Theorem-facing spelling of the full natural endpoint input generated by an
ext-deriv constructor route and common endpoint data. -/
def naturalEndpointInputOfExtDerivRoute
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    NaturalCompactSupportEndpointNaturalInput
      I omega rho ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu :=
  D.toNaturalEndpointInputOfExtDerivConstructorRoute C R

/-- Theorem-facing spelling of the full natural endpoint input generated by a
reconstruction route and common endpoint data. -/
def naturalEndpointInputOfReconstructionRoute
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    NaturalCompactSupportEndpointNaturalInput
      I omega rho ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu :=
  D.toNaturalEndpointInputOfReconstructionRoute C R

@[simp]
theorem naturalEndpointInputOfExtDerivRoute_boundaryMeasure
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (D.naturalEndpointInputOfExtDerivRoute C R).boundaryMeasure =
      C.boundaryMeasureInputOfExtDerivRoute R := by
  rfl

@[simp]
theorem naturalEndpointInputOfExtDerivRoute_reconstructionSource
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (D.naturalEndpointInputOfExtDerivRoute C R).boundaryMeasure.reconstructionSource =
      R.selectedReconstructionSource := by
  rfl

@[simp]
theorem naturalEndpointInputOfExtDerivRoute_bulkLocalFacts
    (R : C.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (D.naturalEndpointInputOfExtDerivRoute C R).boundaryMeasure.bulkLocalFacts =
      R.localFacts := by
  rfl

@[simp]
theorem naturalEndpointInputOfReconstructionRoute_boundaryMeasure
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (D.naturalEndpointInputOfReconstructionRoute C R).boundaryMeasure =
      C.boundaryMeasureInputOfReconstructionRoute R := by
  rfl

@[simp]
theorem naturalEndpointInputOfReconstructionRoute_reconstructionSource
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (D.naturalEndpointInputOfReconstructionRoute C R).boundaryMeasure.reconstructionSource =
      R.selectedReconstructionSource := by
  rfl

@[simp]
theorem naturalEndpointInputOfReconstructionRoute_bulkLocalFacts
    (R : C.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (D.naturalEndpointInputOfReconstructionRoute C R).boundaryMeasure.bulkLocalFacts =
      R.localFacts := by
  rfl

end NaturalFiniteActiveChartBoxSelectionData

/-- A compact input object for callers that want to pass the unified boundary
data once and then project the common endpoint package. -/
structure NaturalBulkEndpointUnifiedInput
    (D : NaturalFiniteActiveChartBoxSelectionData I omega rho)
    (BoundaryPiece : Type b)
    (mu : Measure (Fin (n + 1) -> Real))
    [IsFiniteMeasureOnCompacts mu]
    [IsManifold I 1 M] where
  orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M
  boundaryUnified :
    BoundarySourceAlignmentUnifiedData
      (I := I) (omega := omega)
      (selectedPartition := D.selectedPartition)
      (orientedBoundaryAtlas := orientedBoundaryAtlas)
      (BoundaryPiece := BoundaryPiece)
  localized : LocalizedInteriorM8Fields I omega D.selectedPartition
  measure_eq_volume : mu = volume
  boundaryFaceContinuity :
    ProjectLocalBoundaryCanonicalFaceContinuityData
      boundaryUnified.toProjectLocalGlobalStokesData
  boundaryChartChange :
    BoundaryChartChangeSelectedFamilyData
      boundaryUnified.toProjectLocalGlobalStokesData

namespace NaturalBulkEndpointUnifiedInput

variable {D : NaturalFiniteActiveChartBoxSelectionData I omega rho}
variable
    (P :
      NaturalBulkEndpointUnifiedInput
        (I := I) (omega := omega) (rho := rho)
        D BoundaryPiece mu)

/-- Convert the unified input package to the common endpoint data consumed by
the route constructors. -/
def toCommonData :
    NaturalBulkEndpointCommonData
      (I := I) (omega := omega) (rho := rho)
      D BoundaryPiece mu :=
  NaturalBulkEndpointCommonData.ofUnified
    (I := I) (omega := omega) (rho := rho) (BoundaryPiece := BoundaryPiece)
    (D := D) (mu := mu)
    P.orientedBoundaryAtlas P.boundaryUnified P.localized
    P.measure_eq_volume P.boundaryFaceContinuity P.boundaryChartChange

@[simp]
theorem toCommonData_boundaryUnified :
    P.toCommonData.boundaryUnified = P.boundaryUnified := by
  rfl

@[simp]
theorem toCommonData_localized :
    P.toCommonData.localized = P.localized := by
  rfl

/-- Boundary/measure endpoint input from a packaged unified input and an
ext-deriv constructor route. -/
def boundaryMeasureInputOfExtDerivRoute
    (R : P.toCommonData.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
      (I := I) (omega := omega) (rho := rho)
      D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu :=
  P.toCommonData.boundaryMeasureInputOfExtDerivRoute R

/-- Boundary/measure endpoint input from a packaged unified input and a
reconstruction route. -/
def boundaryMeasureInputOfReconstructionRoute
    (R : P.toCommonData.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
      (I := I) (omega := omega) (rho := rho)
      D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu :=
  P.toCommonData.boundaryMeasureInputOfReconstructionRoute R

@[simp]
theorem boundaryMeasureInputOfExtDerivRoute_reconstructionSource
    (R : P.toCommonData.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (P.boundaryMeasureInputOfExtDerivRoute R).reconstructionSource =
      R.selectedReconstructionSource := by
  rfl

@[simp]
theorem boundaryMeasureInputOfExtDerivRoute_bulkLocalFacts
    (R : P.toCommonData.ExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (P.boundaryMeasureInputOfExtDerivRoute R).bulkLocalFacts =
      R.localFacts := by
  rfl

@[simp]
theorem boundaryMeasureInputOfReconstructionRoute_reconstructionSource
    (R : P.toCommonData.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (P.boundaryMeasureInputOfReconstructionRoute R).reconstructionSource =
      R.selectedReconstructionSource := by
  rfl

@[simp]
theorem boundaryMeasureInputOfReconstructionRoute_bulkLocalFacts
    (R : P.toCommonData.ReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)) :
    (P.boundaryMeasureInputOfReconstructionRoute R).bulkLocalFacts =
      R.localFacts := by
  rfl

end NaturalBulkEndpointUnifiedInput

end NaturalBulkEndpointCommonFromUnifiedAuto

end Stokes

end
