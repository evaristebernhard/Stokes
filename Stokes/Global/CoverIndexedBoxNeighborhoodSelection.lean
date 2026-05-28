import Stokes.Global.CoverIndexedLocalDataFromCompactSupport
import Stokes.Global.CoverIndexedBoundaryTargetSmoothnessConstructor

/-!
# Cover-indexed box neighborhoods

This file packages the open-neighborhood and chart-target containment facts
left over after compact-support chart-box selection.

The mathematical point is small but useful: once a selected closed coordinate
box is known to lie in an open set contained in a chart target, that open set is
exactly the smoothness neighborhood required by the local Stokes wrappers.  In
models with boundary the extended chart target is not automatically open in
ambient Euclidean coordinates, so the constructors below keep the open shrink
as explicit data when needed.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section GenericNeighborhood

universe u

variable {E : Type u} [TopologicalSpace E] [Preorder E]

/-- An open set between a closed coordinate box and an ambient target set. -/
structure ChartBoxOpenNeighborhood (target : Set E) (lower upper : E) where
  /-- The chosen open neighborhood. -/
  neighborhood : Set E
  /-- The chosen neighborhood is open. -/
  isOpen_neighborhood : IsOpen neighborhood
  /-- The closed coordinate box is contained in the chosen neighborhood. -/
  Icc_subset_neighborhood : Set.Icc lower upper ⊆ neighborhood
  /-- The chosen neighborhood is contained in the prescribed target set. -/
  neighborhood_subset_target : neighborhood ⊆ target

namespace ChartBoxOpenNeighborhood

variable {target : Set E} {lower upper : E}

/-- The open target itself is an admissible box neighborhood. -/
def ofOpenTarget
    (htarget : IsOpen target) (hbox : Set.Icc lower upper ⊆ target) :
    ChartBoxOpenNeighborhood target lower upper where
  neighborhood := target
  isOpen_neighborhood := htarget
  Icc_subset_neighborhood := hbox
  neighborhood_subset_target := subset_rfl

/-- Projection: the closed box lies in the ambient target. -/
theorem Icc_subset_target
    (N : ChartBoxOpenNeighborhood target lower upper) :
    Set.Icc lower upper ⊆ target :=
  N.Icc_subset_neighborhood.trans N.neighborhood_subset_target

end ChartBoxOpenNeighborhood

/-- Existence spelling of `ChartBoxOpenNeighborhood.ofOpenTarget`. -/
theorem exists_open_neighborhood_subset_of_Icc_subset_open
    {target : Set E} {lower upper : E}
    (htarget : IsOpen target) (hbox : Set.Icc lower upper ⊆ target) :
    ∃ U : Set E, IsOpen U ∧ Set.Icc lower upper ⊆ U ∧ U ⊆ target :=
  ⟨target, htarget, hbox, subset_rfl⟩

/-- Compact-set spelling of the same open-neighborhood selection.

The compactness hypothesis is often what chart-box selection produces, but for
this particular neighborhood layer the open target itself is enough. -/
theorem exists_open_neighborhood_subset_of_isCompact_Icc_subset_open
    {target : Set E} {lower upper : E}
    (_hcompact : IsCompact (Set.Icc lower upper))
    (htarget : IsOpen target) (hbox : Set.Icc lower upper ⊆ target) :
    ∃ U : Set E, IsOpen U ∧ Set.Icc lower upper ⊆ U ∧ U ⊆ target :=
  exists_open_neighborhood_subset_of_Icc_subset_open htarget hbox

end GenericNeighborhood

section ExtChartTargetNeighborhood

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E] [Preorder E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H}

/-- Chart-target version of the generic box-neighborhood constructor, available
when the extended chart target has been separately proved open. -/
def ChartBoxOpenNeighborhood.ofExtChartTarget
    (x : M) {lower upper : E}
    (hopen_target : IsOpen (extChartAt I x).target)
    (hbox : Set.Icc lower upper ⊆ (extChartAt I x).target) :
    ChartBoxOpenNeighborhood (extChartAt I x).target lower upper :=
  ChartBoxOpenNeighborhood.ofOpenTarget hopen_target hbox

/-- Existence spelling for an open neighborhood inside an extended chart target. -/
theorem exists_extChartAt_target_open_neighborhood
    (x : M) {lower upper : E}
    (hopen_target : IsOpen (extChartAt I x).target)
    (hbox : Set.Icc lower upper ⊆ (extChartAt I x).target) :
    ∃ U : Set E,
      IsOpen U ∧ Set.Icc lower upper ⊆ U ∧
        U ⊆ (extChartAt I x).target :=
  exists_open_neighborhood_subset_of_Icc_subset_open
    hopen_target hbox

end ExtChartTargetNeighborhood

section CoverIndexedBoxNeighborhoodSelection

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/-- Open neighborhoods for all selected interior coordinate boxes. -/
structure CoverIndexedInteriorBoxNeighborhoods
    (C : CompactSupportChartCoverSelection I K) where
  /-- Per-index open smoothness neighborhood. -/
  neighborhood :
    {x : M // x ∈ C.interiorCenters} → Set (Fin (n + 1) → Real)
  /-- The neighborhoods are open. -/
  neighborhood_open :
    ∀ i : {x : M // x ∈ C.interiorCenters}, IsOpen (neighborhood i)
  /-- Each selected closed box lies in its neighborhood. -/
  Icc_subset_neighborhood :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      Set.Icc (C.interiorLower i.1) (C.interiorUpper i.1) ⊆ neighborhood i
  /-- Each neighborhood lies in the source chart target. -/
  neighborhood_subset_target :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      neighborhood i ⊆ (extChartAt I (C.interiorChart i.1)).target

namespace CoverIndexedInteriorBoxNeighborhoods

/-- The selected interior closed box lies in the source chart target. -/
theorem Icc_subset_target
    (nbrs : CoverIndexedInteriorBoxNeighborhoods (I := I) C)
    (i : {x : M // x ∈ C.interiorCenters}) :
    Set.Icc (C.interiorLower i.1) (C.interiorUpper i.1) ⊆
      (extChartAt I (C.interiorChart i.1)).target :=
  (CoverIndexedInteriorBoxNeighborhoods.Icc_subset_neighborhood nbrs i).trans
    (nbrs.neighborhood_subset_target i)

/-- Choose the chart target itself as every interior smoothness neighborhood,
when those chart targets are known to be open. -/
def ofOpenChartTargets
    (C : CompactSupportChartCoverSelection I K)
    (hopen_target :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        IsOpen (extChartAt I (C.interiorChart i.1)).target) :
    CoverIndexedInteriorBoxNeighborhoods (I := I) C where
  neighborhood := fun i => (extChartAt I (C.interiorChart i.1)).target
  neighborhood_open := hopen_target
  Icc_subset_neighborhood := fun i => by
    intro y hy
    exact (C.interior_Icc_subset_domain i.1 i.2 hy).1
  neighborhood_subset_target := fun _ => subset_rfl

/-- Build interior compact-support local data from carrier fields plus packaged
open neighborhoods. -/
def toLocalData
    (nbrs : CoverIndexedInteriorBoxNeighborhoods (I := I) C)
    (coordSupport :
      {x : M // x ∈ C.interiorCenters} →
        Set (Fin (n + 1) → Real))
    (base_tsupport_subset :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.interiorChart i.1) (C.interiorChart i.1) omega) ⊆
          coordSupport i)
    (coord_mapsTo_support :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        ∀ y ∈ coordSupport i,
          (extChartAt I (C.interiorChart i.1)).symm y ∈ K)
    (coord_subset_target :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        coordSupport i ⊆ (extChartAt I (C.interiorChart i.1)).target)
    (localized_contDiffOn_top :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        ContDiffOn Real ⊤
          (ManifoldForm.transitionPullbackInChart I
            (C.interiorChart i.1) (C.interiorChart i.1)
            (P.coverIndexLocalizedForm omega (Sum.inl i)))
          (nbrs.neighborhood i)) :
    CoverIndexedInteriorLocalDataFromCompactSupport C P omega where
  coordSupport := coordSupport
  neighborhood := nbrs.neighborhood
  base_tsupport_subset := base_tsupport_subset
  coord_mapsTo_support := coord_mapsTo_support
  coord_subset_target := coord_subset_target
  neighborhood_open := nbrs.neighborhood_open
  Icc_subset_neighborhood := nbrs.Icc_subset_neighborhood
  neighborhood_subset_target := nbrs.neighborhood_subset_target
  localized_contDiffOn_top := localized_contDiffOn_top

end CoverIndexedInteriorBoxNeighborhoods

/-- Open neighborhoods for all selected boundary source boxes. -/
structure CoverIndexedBoundaryBoxNeighborhoods
    (C : CompactSupportChartCoverSelection I K) where
  /-- Per-index open smoothness neighborhood. -/
  neighborhood :
    {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real)
  /-- The neighborhoods are open. -/
  neighborhood_open :
    ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (neighborhood i)
  /-- Each selected closed boundary box lies in its neighborhood. -/
  Icc_subset_neighborhood :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆ neighborhood i
  /-- Each neighborhood lies in the source boundary chart target. -/
  neighborhood_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      neighborhood i ⊆ (extChartAt I (C.boundaryChart i.1)).target

namespace CoverIndexedBoundaryBoxNeighborhoods

variable (nbrs : CoverIndexedBoundaryBoxNeighborhoods (I := I) C)

/-- Boundary smoothness neighborhoods lie in the self-overlap domain. -/
theorem neighborhood_subset_overlap
    (i : {x : M // x ∈ C.boundaryCenters}) :
    nbrs.neighborhood i ⊆
      ManifoldForm.chartOverlap I (C.boundaryChart i.1) (C.boundaryChart i.1) :=
  ManifoldForm.subset_chartOverlap_self_of_subset_target
    (I := I) (x := C.boundaryChart i.1) (nbrs.neighborhood_subset_target i)

/-- The selected boundary closed box lies in the source chart target. -/
theorem Icc_subset_target
    (nbrs : CoverIndexedBoundaryBoxNeighborhoods (I := I) C)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
      (extChartAt I (C.boundaryChart i.1)).target :=
  (CoverIndexedBoundaryBoxNeighborhoods.Icc_subset_neighborhood nbrs i).trans
    (nbrs.neighborhood_subset_target i)

/-- Choose the chart target itself as every boundary smoothness neighborhood,
when those chart targets are known to be open. -/
def ofOpenChartTargets
    (C : CompactSupportChartCoverSelection I K)
    (hopen_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen (extChartAt I (C.boundaryChart i.1)).target) :
    CoverIndexedBoundaryBoxNeighborhoods (I := I) C where
  neighborhood := fun i => (extChartAt I (C.boundaryChart i.1)).target
  neighborhood_open := hopen_target
  Icc_subset_neighborhood := fun i => by
    intro y hy
    exact (C.boundary_Icc_subset_domain i.1 i.2 hy).1
  neighborhood_subset_target := fun _ => subset_rfl

/-- Build boundary compact-support local data from carrier fields plus packaged
open neighborhoods. -/
def toLocalData
    (nbrs : CoverIndexedBoundaryBoxNeighborhoods (I := I) C)
    (coordSupport :
      {x : M // x ∈ C.boundaryCenters} →
        Set (Fin (n + 1) → Real))
    (coord_compact :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsCompact (coordSupport i))
    (coord_subset_halfSpace :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, coordSupport i ⊆ upperHalfSpace n)
    (base_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1) omega) ⊆
          coordSupport i)
    (coord_mapsTo_support :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ∀ y ∈ coordSupport i,
          (extChartAt I (C.boundaryChart i.1)).symm y ∈ K)
    (coord_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        coordSupport i ⊆ (extChartAt I (C.boundaryChart i.1)).target) :
    CoverIndexedBoundaryLocalDataFromCompactSupport C P omega where
  coordSupport := coordSupport
  neighborhood := nbrs.neighborhood
  coord_compact := coord_compact
  coord_subset_halfSpace := coord_subset_halfSpace
  base_tsupport_subset := base_tsupport_subset
  coord_mapsTo_support := coord_mapsTo_support
  coord_subset_target := coord_subset_target
  neighborhood_open := nbrs.neighborhood_open
  Icc_subset_neighborhood := nbrs.Icc_subset_neighborhood
  neighborhood_subset_target := nbrs.neighborhood_subset_target

end CoverIndexedBoundaryBoxNeighborhoods

/-- Open neighborhoods for all selected boundary target boxes. -/
structure CoverIndexedBoundaryTargetBoxNeighborhoods
    (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega) where
  /-- Per-index open target-side smoothness neighborhood. -/
  targetNeighborhood :
    {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real)
  /-- The target-side neighborhoods are open. -/
  targetNeighborhood_open :
    ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (targetNeighborhood i)
  /-- Each selected target closed box lies in its target-side neighborhood. -/
  targetIcc_subset_neighborhood :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Set.Icc (D.targetLower i) (D.targetUpper i) ⊆ targetNeighborhood i
  /-- Each target-side neighborhood lies in the selected target chart target. -/
  targetNeighborhood_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      targetNeighborhood i ⊆ (extChartAt I (D.targetChart i)).target

namespace CoverIndexedBoundaryTargetBoxNeighborhoods

variable {D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega}

/-- The selected target boxes lie in their selected chart targets. -/
theorem targetBox_subset_target
    (nbrs : CoverIndexedBoundaryTargetBoxNeighborhoods D)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    Set.Icc (D.targetLower i) (D.targetUpper i) ⊆
      (extChartAt I (D.targetChart i)).target :=
  (CoverIndexedBoundaryTargetBoxNeighborhoods.targetIcc_subset_neighborhood nbrs i).trans
    (nbrs.targetNeighborhood_subset_target i)

/-- Choose the target chart target itself as every target-side neighborhood,
when those target chart targets are known to be open. -/
def ofOpenTargetSubsets
    (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (hopen_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen (extChartAt I (D.targetChart i)).target)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Set.Icc (D.targetLower i) (D.targetUpper i) ⊆
          (extChartAt I (D.targetChart i)).target) :
    CoverIndexedBoundaryTargetBoxNeighborhoods D where
  targetNeighborhood := fun i => (extChartAt I (D.targetChart i)).target
  targetNeighborhood_open := hopen_target
  targetIcc_subset_neighborhood := targetBox_subset_target
  targetNeighborhood_subset_target := fun _ => subset_rfl

/-- Target-chart `C^\infty` smoothness using the packaged target-box
containment. -/
theorem targetInChart_contDiffOn_infty_of_localizedChartwiseSmooth
    (nbrs : CoverIndexedBoundaryTargetBoxNeighborhoods D)
    (localizedChartwiseSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ManifoldForm.ChartwiseSmooth I
          (P.coverIndexLocalizedForm omega (Sum.inr i)))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.inChart I (D.targetChart i)
        (P.coverIndexLocalizedForm omega (Sum.inr i)))
      (Set.Icc (D.targetLower i) (D.targetUpper i)) :=
  D.targetInChart_contDiffOn_infty_of_localizedChartwiseSmooth
    localizedChartwiseSmooth
    (CoverIndexedBoundaryTargetBoxNeighborhoods.targetBox_subset_target nbrs) i

/-- Support/continuity data from target-box neighborhoods, localized
chartwise smoothness, and the remaining image-support theorem. -/
def toSupportContinuityDataOfLocalizedChartwiseSmooth
    (nbrs : CoverIndexedBoundaryTargetBoxNeighborhoods D)
    (localizedChartwiseSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ManifoldForm.ChartwiseSmooth I
          (P.coverIndexLocalizedForm omega (Sum.inr i)))
    (targetInChart_tsupport_subset_image :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (D.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          boundaryChartTransitionAmbientBoundaryImage I
            (C.boundaryChart i.1) (D.targetChart i)
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedBoundaryTargetSupportContinuityData
      (C := C) P omega D.targetChart D.targetLower D.targetUpper :=
  D.toSupportContinuityDataOfLocalizedChartwiseSmooth
    localizedChartwiseSmooth
    (CoverIndexedBoundaryTargetBoxNeighborhoods.targetBox_subset_target nbrs)
    targetInChart_tsupport_subset_image

end CoverIndexedBoundaryTargetBoxNeighborhoods

end CoverIndexedBoxNeighborhoodSelection

end Stokes

end
