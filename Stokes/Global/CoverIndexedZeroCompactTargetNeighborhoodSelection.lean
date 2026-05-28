import Stokes.Global.CoverIndexedZeroCompactGeometryConstructors

/-!
# Target chart-box neighborhood selection for compact zero endpoints

This file gives the target-side analogue of the source shrink packages:
if each selected boundary target box has an open chart-box neighborhood

`Icc (targetLower i) (targetUpper i) ⊆ V i ⊆ (extChartAt I (targetChart i)).target`,

then those per-index choices assemble into
`CoverIndexedBoundaryTargetBoxNeighborhoods`.

The point is deliberately modest.  We do not prove chart-transition `MapsTo`
facts here; we only expose the target chart-domain containment layer in the
shape consumed by the relative compact-support zero endpoint.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactTargetNeighborhoodSelection

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryTargetBoxNeighborhoods

variable {D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega}

/-- Build target-box neighborhoods from per-index chart-box open
neighborhoods in the selected target charts.

This is a natural-name wrapper around
`CoverIndexedBoundaryTargetBoxNeighborhoods.ofChartBoxOpenNeighborhoods`,
kept in the compact-zero namespace so downstream endpoint constructors do not
need to remember where the generic box-neighborhood API lives. -/
def ofTargetChartBoxOpenNeighborhoods
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          (extChartAt I (D.targetChart i)).target
          (D.targetLower i) (D.targetUpper i)) :
    CoverIndexedBoundaryTargetBoxNeighborhoods D :=
  CoverIndexedBoundaryTargetBoxNeighborhoods.ofChartBoxOpenNeighborhoods
    (D := D) nbr

@[simp]
theorem ofTargetChartBoxOpenNeighborhoods_targetNeighborhood
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          (extChartAt I (D.targetChart i)).target
          (D.targetLower i) (D.targetUpper i))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    (ofTargetChartBoxOpenNeighborhoods (D := D) nbr).targetNeighborhood i =
      (nbr i).neighborhood :=
  rfl

@[simp]
theorem ofTargetChartBoxOpenNeighborhoods_targetNeighborhood_open
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          (extChartAt I (D.targetChart i)).target
          (D.targetLower i) (D.targetUpper i))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    (ofTargetChartBoxOpenNeighborhoods
      (D := D) nbr).targetNeighborhood_open i =
      (nbr i).isOpen_neighborhood :=
  rfl

/-- Projection from the natural target-neighborhood constructor: the selected
target `Icc` lies in the chosen target-side neighborhood. -/
theorem ofTargetChartBoxOpenNeighborhoods_targetIcc_subset_neighborhood
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          (extChartAt I (D.targetChart i)).target
          (D.targetLower i) (D.targetUpper i))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    Icc (D.targetLower i) (D.targetUpper i) ⊆
      (ofTargetChartBoxOpenNeighborhoods (D := D) nbr).targetNeighborhood i :=
  (nbr i).Icc_subset_neighborhood

/-- Projection from the natural target-neighborhood constructor: the chosen
target-side neighborhood lies in the selected target chart target. -/
theorem ofTargetChartBoxOpenNeighborhoods_targetNeighborhood_subset_target
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          (extChartAt I (D.targetChart i)).target
          (D.targetLower i) (D.targetUpper i))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    (ofTargetChartBoxOpenNeighborhoods (D := D) nbr).targetNeighborhood i ⊆
      (extChartAt I (D.targetChart i)).target :=
  (nbr i).neighborhood_subset_target

/-- Per-index target chart-box neighborhoods imply the endpoint-facing
target-chart-domain field. -/
theorem targetBox_subset_target_of_targetChartBoxOpenNeighborhoods
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          (extChartAt I (D.targetChart i)).target
          (D.targetLower i) (D.targetUpper i)) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (D.targetLower i) (D.targetUpper i) ⊆
        (extChartAt I (D.targetChart i)).target :=
  targetBox_subset_target
    (ofTargetChartBoxOpenNeighborhoods (D := D) nbr)

/-- Direct constructor from raw open subsets in the target chart coordinates. -/
def ofTargetOpenSubsets
    (targetNeighborhood :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (targetNeighborhood_open :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen (targetNeighborhood i))
    (targetIcc_subset_neighborhood :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.targetLower i) (D.targetUpper i) ⊆ targetNeighborhood i)
    (targetNeighborhood_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        targetNeighborhood i ⊆ (extChartAt I (D.targetChart i)).target) :
    CoverIndexedBoundaryTargetBoxNeighborhoods D where
  targetNeighborhood := targetNeighborhood
  targetNeighborhood_open := targetNeighborhood_open
  targetIcc_subset_neighborhood := targetIcc_subset_neighborhood
  targetNeighborhood_subset_target := targetNeighborhood_subset_target

/-- Turn raw open subsets into per-index `ChartBoxOpenNeighborhood`s. -/
def targetChartBoxOpenNeighborhoodsOfOpenSubsets
    (targetNeighborhood :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (targetNeighborhood_open :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen (targetNeighborhood i))
    (targetIcc_subset_neighborhood :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.targetLower i) (D.targetUpper i) ⊆ targetNeighborhood i)
    (targetNeighborhood_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        targetNeighborhood i ⊆ (extChartAt I (D.targetChart i)).target) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      ChartBoxOpenNeighborhood
        (extChartAt I (D.targetChart i)).target
        (D.targetLower i) (D.targetUpper i) := fun i => {
  neighborhood := targetNeighborhood i
  isOpen_neighborhood := targetNeighborhood_open i
  Icc_subset_neighborhood := targetIcc_subset_neighborhood i
  neighborhood_subset_target := targetNeighborhood_subset_target i
}

@[simp]
theorem targetChartBoxOpenNeighborhoodsOfOpenSubsets_neighborhood
    (targetNeighborhood :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (targetNeighborhood_open :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen (targetNeighborhood i))
    (targetIcc_subset_neighborhood :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.targetLower i) (D.targetUpper i) ⊆ targetNeighborhood i)
    (targetNeighborhood_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        targetNeighborhood i ⊆ (extChartAt I (D.targetChart i)).target)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    (targetChartBoxOpenNeighborhoodsOfOpenSubsets
      (D := D) targetNeighborhood targetNeighborhood_open
      targetIcc_subset_neighborhood targetNeighborhood_subset_target i
      ).neighborhood = targetNeighborhood i :=
  rfl

/-- The raw-open-subset constructor agrees with the chart-box-neighborhood
constructor after bundling those raw subsets index by index. -/
theorem ofTargetOpenSubsets_eq_ofTargetChartBoxOpenNeighborhoods
    (targetNeighborhood :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (targetNeighborhood_open :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen (targetNeighborhood i))
    (targetIcc_subset_neighborhood :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.targetLower i) (D.targetUpper i) ⊆ targetNeighborhood i)
    (targetNeighborhood_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        targetNeighborhood i ⊆ (extChartAt I (D.targetChart i)).target) :
    ofTargetOpenSubsets
        (D := D) targetNeighborhood targetNeighborhood_open
        targetIcc_subset_neighborhood targetNeighborhood_subset_target =
      ofTargetChartBoxOpenNeighborhoods
        (D := D)
        (targetChartBoxOpenNeighborhoodsOfOpenSubsets
          (D := D) targetNeighborhood targetNeighborhood_open
          targetIcc_subset_neighborhood targetNeighborhood_subset_target) :=
  rfl

end CoverIndexedBoundaryTargetBoxNeighborhoods

namespace CoverIndexedBoundaryTargetBoxData

variable (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)

/-- Target chart-box neighborhoods expose the target-chart-domain field,
directly in the namespace of the selected target-box package. -/
theorem targetBox_subset_target_of_targetChartBoxOpenNeighborhoods
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          (extChartAt I (D.targetChart i)).target
          (D.targetLower i) (D.targetUpper i)) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (D.targetLower i) (D.targetUpper i) ⊆
        (extChartAt I (D.targetChart i)).target :=
  CoverIndexedBoundaryTargetBoxNeighborhoods.targetBox_subset_target_of_targetChartBoxOpenNeighborhoods
    (D := D) nbr

/-- Raw open target-side coordinate neighborhoods expose the same
target-chart-domain field. -/
theorem targetBox_subset_target_of_targetOpenSubsets
    (targetNeighborhood :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (targetNeighborhood_open :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen (targetNeighborhood i))
    (targetIcc_subset_neighborhood :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.targetLower i) (D.targetUpper i) ⊆ targetNeighborhood i)
    (targetNeighborhood_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        targetNeighborhood i ⊆ (extChartAt I (D.targetChart i)).target) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (D.targetLower i) (D.targetUpper i) ⊆
        (extChartAt I (D.targetChart i)).target :=
  CoverIndexedBoundaryTargetBoxNeighborhoods.targetBox_subset_target
    (CoverIndexedBoundaryTargetBoxNeighborhoods.ofTargetOpenSubsets
      (D := D) targetNeighborhood targetNeighborhood_open
      targetIcc_subset_neighborhood targetNeighborhood_subset_target)

end CoverIndexedBoundaryTargetBoxData

namespace CoverIndexedZeroCompactRelativeTargetBoxData

variable
    {transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega}

/-- Relative target-box data from an already selected target box and per-index
target chart-box neighborhoods.  This removes the intermediate need to name a
`CoverIndexedBoundaryTargetBoxNeighborhoods` value. -/
def ofTargetBoxDataAndTargetChartBoxOpenNeighborhoods
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (targetChart_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        transitionSupportData.targetChart i = targetBox.targetChart i)
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          (extChartAt I (targetBox.targetChart i)).target
          (targetBox.targetLower i) (targetBox.targetUpper i))
    (coordinateImage_subset_targetBox :
      targetBox.TargetChartCoordinateImageSubsetIccField) :
    CoverIndexedZeroCompactRelativeTargetBoxData
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData :=
  CoverIndexedZeroCompactRelativeTargetBoxData.ofTargetBoxDataAndNeighborhoods
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    (transitionSupportData := transitionSupportData)
    targetBox targetChart_eq
    (CoverIndexedBoundaryTargetBoxNeighborhoods.ofTargetChartBoxOpenNeighborhoods
      (D := targetBox) nbr)
    coordinateImage_subset_targetBox

end CoverIndexedZeroCompactRelativeTargetBoxData

end CoverIndexedZeroCompactTargetNeighborhoodSelection

end Stokes

end
