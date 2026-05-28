import Stokes.Global.CoverIndexedZeroCompactRelativeNaturalTheorem
import Stokes.Global.CoverIndexedZeroTargetBoxNaturalFields

/-!
# Target-box package for the relative compact-support zero endpoint

This file isolates the target-side inputs still exposed by
`compactSupportRepresentedStokesZeroCompact_of_globalSupport_relative`.

The package below is intentionally small: it stores the selected target-box
data together with exactly the two endpoint-facing fields that existing
compact-image and target-neighborhood constructors can produce:

* the selected target `Icc` is contained in the chosen chart target;
* the target chart coordinate image of the global compact support is contained
  in the selected target `Icc`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactRelativeTargetBox

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {muBulk : Measure (Fin (n + 1) → Real)}

/--
The target-box fields needed by the relative compact-support zero endpoint.

This is not a new geometric assumption layer: the constructors below build the
last two fields from the already existing target-box-neighborhood and
compact-coordinate-image packages.
-/
structure CoverIndexedZeroCompactRelativeTargetBoxData
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega) where
  /-- Selected target charts and target boxes for boundary indices. -/
  targetBox :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega
  /-- The transition-support target chart agrees with the selected target box. -/
  targetChart_eq :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      transitionSupportData.targetChart i = targetBox.targetChart i
  /-- The selected target `Icc` lies in the selected target chart target. -/
  targetBox_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
        (extChartAt I (targetBox.targetChart i)).target
  /-- The target-chart coordinate image of `K` lies in the selected target box. -/
  coordinateImage_subset_targetBox :
    targetBox.TargetChartCoordinateImageSubsetIccField

namespace CoverIndexedZeroCompactRelativeTargetBoxData

variable
    {transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega}

/-- Build the relative endpoint target-box package from compact-coordinate-box
selections and target-box neighborhoods. -/
def ofTargetBoxNeighborhoodsAndCompactCoordinateBoxSelections
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (targetChart_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        transitionSupportData.targetChart i = targetBox.targetChart i)
    (nbrs : CoverIndexedBoundaryTargetBoxNeighborhoods targetBox)
    (box :
      {x : M // x ∈ C.boundaryCenters} →
        CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (box_K_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (box i).K = chartCoordinateImage I (targetBox.targetChart i) K)
    (box_lower_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (box i).a = targetBox.targetLower i)
    (box_upper_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (box i).b = targetBox.targetUpper i) :
    CoverIndexedZeroCompactRelativeTargetBoxData
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData := by
  have hfields :
      (∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target) ∧
        targetBox.TargetChartCoordinateImageSubsetIccField :=
    targetBox.naturalFields_of_targetBoxNeighborhoods_and_compactCoordinateBoxSelections
      nbrs box box_K_eq box_lower_eq box_upper_eq
  exact {
    targetBox := targetBox
    targetChart_eq := targetChart_eq
    targetBox_subset_target := hfields.1
    coordinateImage_subset_targetBox := hfields.2
  }

/-- `ChartCompactImage` spelling of
`ofTargetBoxNeighborhoodsAndCompactCoordinateBoxSelections`. -/
def ofTargetBoxNeighborhoodsAndChartCompactImages
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (targetChart_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        transitionSupportData.targetChart i = targetBox.targetChart i)
    (nbrs : CoverIndexedBoundaryTargetBoxNeighborhoods targetBox)
    (image :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartCompactImage I (targetBox.targetChart i))
    (image_K_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (image i).K = K)
    (box_lower_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (image i).box.a = targetBox.targetLower i)
    (box_upper_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (image i).box.b = targetBox.targetUpper i) :
    CoverIndexedZeroCompactRelativeTargetBoxData
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData := by
  have hfields :
      (∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target) ∧
        targetBox.TargetChartCoordinateImageSubsetIccField :=
    targetBox.naturalFields_of_targetBoxNeighborhoods_and_chartCompactImages
      nbrs image image_K_eq box_lower_eq box_upper_eq
  exact {
    targetBox := targetBox
    targetChart_eq := targetChart_eq
    targetBox_subset_target := hfields.1
    coordinateImage_subset_targetBox := hfields.2
  }

/-- Relative compact-support zero endpoint with the target-box fields supplied
by `CoverIndexedZeroCompactRelativeTargetBoxData`. -/
theorem compactSupportRepresentedStokesZeroCompact_of_globalSupport_relative_targetBoxData
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P omega)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (measure_eq_volume :
      muBulk = (volume : Measure (Fin (n + 1) → Real)))
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (sourceNeighborhood :
      CoverIndexedCompactSupportNeighborhoodDataInfty.BoundaryNeighborhoodSubsetTransitionSource
        (I := I) (K := K) neighborhoodData transitionSupportData)
    (targetData :
      CoverIndexedZeroCompactRelativeTargetBoxData
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData)
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (targetData.targetBox.targetChart i)).source)
    (homegaSupport : ManifoldForm.support I omega ⊆ K)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y,
          P.coverIndexBoundaryTargetZeroPieceSum
            targetData.targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real))) :
    (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) neighborhoodData measure_eq_volume).globalIntegral =
        globalBoundaryIntegral ∧
      transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        globalBoundaryIntegral := by
  exact
    compactSupportRepresentedStokesZeroCompact_of_globalSupport_relative
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)
      carrierData neighborhoodData measure_eq_volume transitionSupportData
      sourceNeighborhood
      targetData.targetBox targetData.targetChart_eq
      targetData.targetBox_subset_target
      hK hsource homegaSupport
      targetData.coordinateImage_subset_targetBox
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral

end CoverIndexedZeroCompactRelativeTargetBoxData

end CoverIndexedZeroCompactRelativeTargetBox

end Stokes

end
