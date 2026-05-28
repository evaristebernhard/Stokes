import Stokes.Global.CoverIndexedZeroCompactSourceShrinkSelection

/-!
# Inner/outer source-box selection for compact zero Stokes

This file packages the source-side shrink geometry in the form used by the
relative compact-support route:

`inner closed box ⊆ U ⊆ outer closed box ⊆ chart overlap`.

The genuinely analytic construction of a strict outer box from compactness and
local openness is still a later theorem.  The point here is to concentrate the
honest outer-box choice into a small structure and prove that it feeds the
existing source-shrink API without exposing low-level fields downstream.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section InnerOuterChartBox

universe u

variable {E : Type u} [TopologicalSpace E] [Preorder E]

namespace ChartBoxOpenNeighborhood

/-- Build a chart-box open neighborhood from an explicitly chosen open set. -/
def ofOpenSubset
    {target : Set E} {lower upper : E}
    (U : Set E)
    (hUopen : IsOpen U)
    (hbox : Icc lower upper ⊆ U)
    (hUtarget : U ⊆ target) :
    ChartBoxOpenNeighborhood target lower upper where
  neighborhood := U
  isOpen_neighborhood := hUopen
  Icc_subset_neighborhood := hbox
  neighborhood_subset_target := hUtarget

@[simp]
theorem ofOpenSubset_neighborhood
    {target : Set E} {lower upper : E}
    (U : Set E)
    (hUopen : IsOpen U)
    (hbox : Icc lower upper ⊆ U)
    (hUtarget : U ⊆ target) :
    (ofOpenSubset
      (target := target) (lower := lower) (upper := upper)
      U hUopen hbox hUtarget).neighborhood = U :=
  rfl

end ChartBoxOpenNeighborhood

/--
An explicitly chosen open neighborhood between an inner closed coordinate box
and an outer closed coordinate box.

The `target` field is deliberately separate from the outer box.  In the
boundary source application it is the source extended-chart target, while a
separate cover-indexed field records that the outer box lies in the
source-to-target chart overlap.
-/
structure InnerOuterChartBoxOpenSelection
    (target : Set E) (innerLower innerUpper outerLower outerUpper : E) where
  /-- The open set between the selected inner box and the outer box. -/
  neighborhood : Set E
  /-- The chosen intermediate set is open. -/
  isOpen_neighborhood : IsOpen neighborhood
  /-- The inner closed box lies in the chosen open neighborhood. -/
  inner_Icc_subset_neighborhood :
    Icc innerLower innerUpper ⊆ neighborhood
  /-- The chosen open neighborhood lies in the outer closed box. -/
  neighborhood_subset_outerBox :
    neighborhood ⊆ Icc outerLower outerUpper
  /-- The outer closed box lies in the ambient target. -/
  outerBox_subset_target :
    Icc outerLower outerUpper ⊆ target

namespace InnerOuterChartBoxOpenSelection

variable {target : Set E}
variable {innerLower innerUpper outerLower outerUpper : E}

/-- The chosen intermediate open set lies in the ambient target. -/
theorem neighborhood_subset_target
    (D :
      InnerOuterChartBoxOpenSelection
        target innerLower innerUpper outerLower outerUpper) :
    D.neighborhood ⊆ target :=
  D.neighborhood_subset_outerBox.trans D.outerBox_subset_target

/-- Forget the outer-box bookkeeping and keep the ordinary chart-box
neighborhood whose target is `outer box ∩ target`. -/
def toOuterBoxChartBoxOpenNeighborhood
    (D :
      InnerOuterChartBoxOpenSelection
        target innerLower innerUpper outerLower outerUpper) :
    ChartBoxOpenNeighborhood
      (Icc outerLower outerUpper ∩ target)
      innerLower innerUpper where
  neighborhood := D.neighborhood
  isOpen_neighborhood := D.isOpen_neighborhood
  Icc_subset_neighborhood := D.inner_Icc_subset_neighborhood
  neighborhood_subset_target := by
    intro y hy
    exact ⟨D.neighborhood_subset_outerBox hy, D.neighborhood_subset_target hy⟩

@[simp]
theorem toOuterBoxChartBoxOpenNeighborhood_neighborhood
    (D :
      InnerOuterChartBoxOpenSelection
        target innerLower innerUpper outerLower outerUpper) :
    D.toOuterBoxChartBoxOpenNeighborhood.neighborhood = D.neighborhood :=
  rfl

/-- Constructor in the natural `Icc_inner ⊆ U ⊆ Icc_outer ⊆ target` shape. -/
def ofOpenNeighborhood
    (U : Set E)
    (hUopen : IsOpen U)
    (hinner : Icc innerLower innerUpper ⊆ U)
    (hUouter : U ⊆ Icc outerLower outerUpper)
    (houterTarget : Icc outerLower outerUpper ⊆ target) :
    InnerOuterChartBoxOpenSelection
      target innerLower innerUpper outerLower outerUpper where
  neighborhood := U
  isOpen_neighborhood := hUopen
  inner_Icc_subset_neighborhood := hinner
  neighborhood_subset_outerBox := hUouter
  outerBox_subset_target := houterTarget

@[simp]
theorem ofOpenNeighborhood_neighborhood
    (U : Set E)
    (hUopen : IsOpen U)
    (hinner : Icc innerLower innerUpper ⊆ U)
    (hUouter : U ⊆ Icc outerLower outerUpper)
    (houterTarget : Icc outerLower outerUpper ⊆ target) :
    (ofOpenNeighborhood
      (target := target)
      (innerLower := innerLower) (innerUpper := innerUpper)
      (outerLower := outerLower) (outerUpper := outerUpper)
      U hUopen hinner hUouter houterTarget).neighborhood = U :=
  rfl

end InnerOuterChartBoxOpenSelection

end InnerOuterChartBox

section CoverIndexedInnerOuterSourceBoxSelection

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/--
Cover-indexed source-side inner/outer box data.

For each boundary chart index this stores an open set `U_i` satisfying

`Icc selected_i ⊆ U_i ⊆ Icc outer_i`,

with the outer box inside both the source chart target and the relevant
source-to-target chart overlap.
-/
structure CoverIndexedInnerOuterSourceBoxSelection
    (C : CompactSupportChartCoverSelection I K)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M) where
  /-- Lower corners of the outer source boxes. -/
  sourceLower :
    {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real
  /-- Upper corners of the outer source boxes. -/
  sourceUpper :
    {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real
  /-- Per-index open neighborhoods between selected and outer source boxes. -/
  sourceNeighborhood :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      InnerOuterChartBoxOpenSelection
        (extChartAt I (C.boundaryChart i.1)).target
        (C.boundaryLower i.1) (C.boundaryUpper i.1)
        (sourceLower i) (sourceUpper i)
  /-- The outer source boxes lie in the source-to-target chart overlap. -/
  sourceBox_subset_overlap :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (sourceLower i) (sourceUpper i) ⊆
        ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)

namespace CoverIndexedInnerOuterSourceBoxSelection

variable {targetChart : {x : M // x ∈ C.boundaryCenters} → M}
variable
    (D :
      CoverIndexedInnerOuterSourceBoxSelection
        (I := I) (K := K) C targetChart)

/-- The selected open neighborhoods lie in their outer source boxes. -/
theorem neighborhood_subset_outerSourceBox
    (i : {x : M // x ∈ C.boundaryCenters}) :
    (D.sourceNeighborhood i).neighborhood ⊆
      Icc (D.sourceLower i) (D.sourceUpper i) :=
  (D.sourceNeighborhood i).neighborhood_subset_outerBox

/-- The selected open neighborhoods lie in the source chart targets. -/
theorem neighborhood_subset_sourceTarget
    (i : {x : M // x ∈ C.boundaryCenters}) :
    (D.sourceNeighborhood i).neighborhood ⊆
      (extChartAt I (C.boundaryChart i.1)).target :=
  (D.sourceNeighborhood i).neighborhood_subset_target

/-- The selected open neighborhoods lie in the source-to-target chart overlap. -/
theorem neighborhood_subset_overlap
    (i : {x : M // x ∈ C.boundaryCenters}) :
    (D.sourceNeighborhood i).neighborhood ⊆
      ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i) :=
  (D.neighborhood_subset_outerSourceBox i).trans (D.sourceBox_subset_overlap i)

/-- Per-index `ChartBoxOpenNeighborhood`s in the exact shape consumed by the
existing source-shrink API. -/
def toSourceBoxChartBoxOpenNeighborhoods
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ChartBoxOpenNeighborhood
      (Icc (D.sourceLower i) (D.sourceUpper i) ∩
        (extChartAt I (C.boundaryChart i.1)).target)
      (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  (D.sourceNeighborhood i).toOuterBoxChartBoxOpenNeighborhood

@[simp]
theorem toSourceBoxChartBoxOpenNeighborhoods_neighborhood
    (i : {x : M // x ∈ C.boundaryCenters}) :
    (D.toSourceBoxChartBoxOpenNeighborhoods i).neighborhood =
      (D.sourceNeighborhood i).neighborhood :=
  rfl

/-- Ordinary boundary-box neighborhoods generated by the inner/outer source
selection. -/
def toBoundaryBoxNeighborhoods :
    CoverIndexedBoundaryBoxNeighborhoods (I := I) C :=
  CoverIndexedBoundaryBoxNeighborhoods.ofSourceBoxChartBoxOpenNeighborhoods
    (I := I) (K := K) (C := C)
    D.sourceLower D.sourceUpper D.toSourceBoxChartBoxOpenNeighborhoods

@[simp]
theorem toBoundaryBoxNeighborhoods_neighborhood :
    D.toBoundaryBoxNeighborhoods.neighborhood =
      fun i => (D.sourceNeighborhood i).neighborhood :=
  rfl

/-- The generated ordinary neighborhoods lie in the outer source boxes. -/
theorem toBoundaryBoxNeighborhoods_subset_outerSourceBox
    (i : {x : M // x ∈ C.boundaryCenters}) :
    D.toBoundaryBoxNeighborhoods.neighborhood i ⊆
      Icc (D.sourceLower i) (D.sourceUpper i) :=
  D.neighborhood_subset_outerSourceBox i

/-- Transition-neighborhood package generated by the inner/outer source
selection. -/
def toBoundaryTransitionBoxNeighborhoods :
    CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C targetChart :=
  CoverIndexedBoundaryTransitionBoxNeighborhoods.ofSourceBoxChartBoxOpenNeighborhoods
    (I := I) (K := K) (C := C)
    targetChart D.sourceLower D.sourceUpper
    D.toSourceBoxChartBoxOpenNeighborhoods D.sourceBox_subset_overlap

@[simp]
theorem toBoundaryTransitionBoxNeighborhoods_boundaryNeighborhood :
    D.toBoundaryTransitionBoxNeighborhoods.boundaryNeighborhood =
      fun i => (D.sourceNeighborhood i).neighborhood :=
  rfl

/-- The transition neighborhoods generated from inner/outer data lie in the
concrete chart-transition source. -/
theorem toBoundaryTransitionBoxNeighborhoods_subset_chartTransitionSource
    (i : {x : M // x ∈ C.boundaryCenters}) :
    D.toBoundaryTransitionBoxNeighborhoods.boundaryNeighborhood i ⊆
      ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (targetChart i) :=
  D.toBoundaryTransitionBoxNeighborhoods.boundaryNeighborhood_subset_chartTransitionSource
    (I := I) (K := K) (C := C) i

end CoverIndexedInnerOuterSourceBoxSelection

namespace CoverIndexedCompactSupportNeighborhoodDataInfty

variable
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)

/-- Build transition neighborhoods from inner/outer source-box data whose open
sets agree with the chosen `C^\infty` boundary neighborhoods. -/
def toBoundaryTransitionBoxNeighborhoodsOfInnerOuterSourceBox
    (D :
      CoverIndexedInnerOuterSourceBoxSelection
        (I := I) (K := K) C transitionSupportData.targetChart)
    (hneighborhood :
      neighborhoodData.boundaryNeighborhood =
        fun i => (D.sourceNeighborhood i).neighborhood) :
    CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C transitionSupportData.targetChart :=
  let _hneighborhood := hneighborhood
  D.toBoundaryTransitionBoxNeighborhoods

@[simp]
theorem toBoundaryTransitionBoxNeighborhoodsOfInnerOuterSourceBox_boundaryNeighborhood
    (D :
      CoverIndexedInnerOuterSourceBoxSelection
        (I := I) (K := K) C transitionSupportData.targetChart)
    (hneighborhood :
      neighborhoodData.boundaryNeighborhood =
        fun i => (D.sourceNeighborhood i).neighborhood) :
    (neighborhoodData.toBoundaryTransitionBoxNeighborhoodsOfInnerOuterSourceBox
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData D hneighborhood).boundaryNeighborhood =
        neighborhoodData.boundaryNeighborhood := by
  simp [toBoundaryTransitionBoxNeighborhoodsOfInnerOuterSourceBox,
    hneighborhood]

/-- Inner/outer source-box version of the transition-source field consumed by
the relative compact zero assembly. -/
theorem boundaryNeighborhoodSubsetTransitionSource_of_innerOuterSourceBox
    (D :
      CoverIndexedInnerOuterSourceBoxSelection
        (I := I) (K := K) C transitionSupportData.targetChart)
    (hneighborhood :
      neighborhoodData.boundaryNeighborhood =
        fun i => (D.sourceNeighborhood i).neighborhood) :
    BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (K := K) neighborhoodData transitionSupportData := by
  exact
    neighborhoodData.boundaryNeighborhoodSubsetTransitionSource_of_transitionBoxNeighborhoods
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData
      (neighborhoodData.toBoundaryTransitionBoxNeighborhoodsOfInnerOuterSourceBox
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData D hneighborhood)
      (by
        simp
          [toBoundaryTransitionBoxNeighborhoodsOfInnerOuterSourceBox,
            hneighborhood])

end CoverIndexedCompactSupportNeighborhoodDataInfty

end CoverIndexedInnerOuterSourceBoxSelection

end Stokes

end
