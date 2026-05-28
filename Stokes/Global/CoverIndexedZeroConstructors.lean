import Stokes.Global.CoverIndexedCompactSupportBoxDataAssembly
import Stokes.Global.CoverIndexedZeroSupportFromGlobal

/-!
# Cover-indexed zero-extension constructors

This file is a practical adapter layer for the zero-extension route.

The represented compact-support endpoint still consumes the old smooth chart
representatives, because those are the objects used by the local Stokes
statements.  The zero-extended representatives are used only to remove the
manual target/overlap support hypotheses.  The bridge below says: if the old
representative is locally inside the concrete chart-transition source along its
topological support, then its support is contained in the zero-extended support;
the global compact-support theorem for the zero representative can then be
reused to fill the existing carrier and transition-support records.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section ZeroToOldSupport

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {k : Nat}
variable {I : ModelWithCorners Real E H}
variable {K : Set M}
variable {x0 x1 : M}
variable {omega : ManifoldForm I M k}
variable [IsManifold I 1 M]

namespace ManifoldForm

/-- If the old transition representative is locally inside the concrete
transition source at every point of its topological support, then its support is
contained in the support of the zero-extended representative. -/
theorem transitionPullbackInChart_tsupport_subset_zero_tsupport_of_source_mem_nhds
    (hsource :
      forall y,
        y ∈ tsupport (transitionPullbackInChart I x0 x1 omega) ->
          chartTransitionSource I x0 x1 ∈ 𝓝 y) :
    tsupport (transitionPullbackInChart I x0 x1 omega) ⊆
      tsupport (transitionPullbackInChartZero I x0 x1 omega) := by
  intro y hy
  by_contra hzero
  have hzeroEventually :
      transitionPullbackInChartZero I x0 x1 omega =ᶠ[𝓝 y]
        fun _ => 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hzero
  have heq :
      transitionPullbackInChartZero I x0 x1 omega =ᶠ[𝓝 y]
        transitionPullbackInChart I x0 x1 omega :=
    transitionPullbackInChartZero_eventuallyEq_transitionPullbackInChart_of_mem_nhds
      (I := I) (x0 := x0) (x1 := x1) (ω := omega) (y := y)
      (hsource y hy)
  have holdEventually :
      transitionPullbackInChart I x0 x1 omega =ᶠ[𝓝 y]
        fun _ => 0 :=
    heq.symm.trans hzeroEventually
  exact (notMem_tsupport_iff_eventuallyEq.mpr holdEventually) hy

/-- Open-neighborhood version of
`transitionPullbackInChart_tsupport_subset_zero_tsupport_of_source_mem_nhds`.
This is the form usually produced by chart-box domain selection. -/
theorem transitionPullbackInChart_tsupport_subset_zero_tsupport_of_open_subset_source
    {U : Set E} (hUopen : IsOpen U)
    (hsupp :
      tsupport (transitionPullbackInChart I x0 x1 omega) ⊆ U)
    (hUsource : U ⊆ chartTransitionSource I x0 x1) :
    tsupport (transitionPullbackInChart I x0 x1 omega) ⊆
      tsupport (transitionPullbackInChartZero I x0 x1 omega) :=
  transitionPullbackInChart_tsupport_subset_zero_tsupport_of_source_mem_nhds
    (I := I) (x0 := x0) (x1 := x1) (omega := omega)
    (by
      intro y hy
      exact mem_of_superset (hUopen.mem_nhds (hsupp hy)) hUsource)

/-- The zero-extension route gives the old transition representative a compact
coordinate-image support bound, provided the old support is locally inside the
transition source. -/
theorem transitionPullbackInChart_tsupport_subset_chartCoordinateImage_of_zero_source_mem_nhds
    (hK : IsCompact K)
    (hsourceK : K ⊆ (extChartAt I x0).source)
    (homega : support I omega ⊆ K)
    (hsource :
      forall y,
        y ∈ tsupport (transitionPullbackInChart I x0 x1 omega) ->
          chartTransitionSource I x0 x1 ∈ 𝓝 y) :
    tsupport (transitionPullbackInChart I x0 x1 omega) ⊆
      chartCoordinateImage I x0 K :=
  (transitionPullbackInChart_tsupport_subset_zero_tsupport_of_source_mem_nhds
    (I := I) (x0 := x0) (x1 := x1) (omega := omega)
    hsource).trans
    (transitionPullbackInChartZero_tsupport_subset_chartCoordinateImage
      (I := I) (K := K) (x0 := x0) (x1 := x1) (ω := omega)
      hK hsourceK homega)

/-- Open-neighborhood version of the compact coordinate-image support bound. -/
theorem transitionPullbackInChart_tsupport_subset_chartCoordinateImage_of_zero_open_source
    (hK : IsCompact K)
    (hsourceK : K ⊆ (extChartAt I x0).source)
    (homega : support I omega ⊆ K)
    {U : Set E} (hUopen : IsOpen U)
    (hsupp :
      tsupport (transitionPullbackInChart I x0 x1 omega) ⊆ U)
    (hUsource : U ⊆ chartTransitionSource I x0 x1) :
    tsupport (transitionPullbackInChart I x0 x1 omega) ⊆
      chartCoordinateImage I x0 K :=
  (transitionPullbackInChart_tsupport_subset_zero_tsupport_of_open_subset_source
    (I := I) (x0 := x0) (x1 := x1) (omega := omega)
    hUopen hsupp hUsource).trans
    (transitionPullbackInChartZero_tsupport_subset_chartCoordinateImage
      (I := I) (K := K) (x0 := x0) (x1 := x1) (ω := omega)
      hK hsourceK homega)

/-- Restrict the existing zero/old equality to any set contained in the
concrete transition source. -/
theorem transitionPullbackInChartZero_eqOn_transitionPullbackInChart_of_subset_source
    {s : Set E} (hs : s ⊆ chartTransitionSource I x0 x1) :
    EqOn (transitionPullbackInChartZero I x0 x1 omega)
      (transitionPullbackInChart I x0 x1 omega) s := by
  intro y hy
  exact
    transitionPullbackInChartZero_eq_transitionPullbackInChart_of_mem_source
      (I := I) (x0 := x0) (x1 := x1) (ω := omega) (y := y) (hs hy)

end ManifoldForm

end ZeroToOldSupport

section CoverIndexedZeroConstructors

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {omega : ManifoldForm I M n}
variable [IsManifold I 1 M]

namespace CoverIndexedInteriorCarrierSelection

/-- Build interior carriers from global manifold support using the
zero-extension support bridge.  Compared with the older constructor, this does
not ask for ordinary support of the total chart representative to be contained
in the chart target. -/
def ofGlobalManifoldSupportZeroSourceNeighborhood
    (hK : IsCompact K)
    (hsource :
      forall i : {x : M // x ∈ C.interiorCenters},
        K ⊆ (extChartAt I (C.interiorChart i.1)).source)
    (homega : ManifoldForm.support I omega ⊆ K)
    (hsource_nhds :
      forall i : {x : M // x ∈ C.interiorCenters},
        forall y,
          y ∈
          tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.interiorChart i.1) (C.interiorChart i.1) omega) ->
            ManifoldForm.chartTransitionSource I
              (C.interiorChart i.1) (C.interiorChart i.1) ∈ 𝓝 y) :
    CoverIndexedInteriorCarrierSelection (I := I) (K := K) C omega where
  support_isCompact := hK
  support_subset_chart_source := hsource
  base_tsupport_subset_chartCoordinateImage := by
    intro i
    exact
      ManifoldForm.transitionPullbackInChart_tsupport_subset_chartCoordinateImage_of_zero_source_mem_nhds
        (I := I) (K := K)
        (x0 := C.interiorChart i.1) (x1 := C.interiorChart i.1)
        (omega := omega) hK (hsource i) homega (hsource_nhds i)

/-- Open-neighborhood variant of
`ofGlobalManifoldSupportZeroSourceNeighborhood`. -/
def ofGlobalManifoldSupportZeroOpen
    (hK : IsCompact K)
    (hsource :
      forall i : {x : M // x ∈ C.interiorCenters},
        K ⊆ (extChartAt I (C.interiorChart i.1)).source)
    (homega : ManifoldForm.support I omega ⊆ K)
    (supportNeighborhood :
      {x : M // x ∈ C.interiorCenters} ->
        Set (Fin (n + 1) -> Real))
    (supportNeighborhood_open :
      forall i : {x : M // x ∈ C.interiorCenters},
        IsOpen (supportNeighborhood i))
    (base_tsupport_subset_neighborhood :
      forall i : {x : M // x ∈ C.interiorCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.interiorChart i.1) (C.interiorChart i.1) omega) ⊆
          supportNeighborhood i)
    (supportNeighborhood_subset_source :
      forall i : {x : M // x ∈ C.interiorCenters},
        supportNeighborhood i ⊆
          ManifoldForm.chartTransitionSource I
            (C.interiorChart i.1) (C.interiorChart i.1)) :
    CoverIndexedInteriorCarrierSelection (I := I) (K := K) C omega :=
  ofGlobalManifoldSupportZeroSourceNeighborhood
    (I := I) (K := K) (C := C) (omega := omega)
    hK hsource homega
    (by
      intro i y hy
      exact
        mem_of_superset
          (supportNeighborhood_open i |>.mem_nhds
            (base_tsupport_subset_neighborhood i hy))
          (supportNeighborhood_subset_source i))

end CoverIndexedInteriorCarrierSelection

namespace BoundaryChartCoordinateCarrier

variable {x : M}

/-- One boundary carrier from global manifold support using zero-extension
support transport. -/
def ofGlobalManifoldSupportZeroSourceNeighborhood
    (hK : IsCompact K)
    (hsource : K ⊆ (extChartAt I x).source)
    (hhalf : chartCoordinateImage I x K ⊆ upperHalfSpace n)
    (homega : ManifoldForm.support I omega ⊆ K)
    (hsource_nhds :
      forall y,
        y ∈ tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ->
          ManifoldForm.chartTransitionSource I x x ∈ 𝓝 y) :
    BoundaryChartCoordinateCarrier I K x omega :=
  ofGlobalChartCoordinateImage
    (I := I) (K := K) (x := x) (omega := omega)
    hK hsource hhalf
    (ManifoldForm.transitionPullbackInChart_tsupport_subset_chartCoordinateImage_of_zero_source_mem_nhds
      (I := I) (K := K) (x0 := x) (x1 := x) (omega := omega)
      hK hsource homega hsource_nhds)

end BoundaryChartCoordinateCarrier

namespace CoverIndexedBoundaryCarrierSelection

/-- Build boundary carriers from global manifold support using the
zero-extension support bridge.  The half-space condition remains genuine
boundary-chart geometry. -/
def ofGlobalManifoldSupportZeroSourceNeighborhood
    (hK : IsCompact K)
    (hsource :
      forall i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (hhalf :
      forall i : {x : M // x ∈ C.boundaryCenters},
        chartCoordinateImage I (C.boundaryChart i.1) K ⊆ upperHalfSpace n)
    (homega : ManifoldForm.support I omega ⊆ K)
    (hsource_nhds :
      forall i : {x : M // x ∈ C.boundaryCenters},
        forall y,
          y ∈
          tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1) omega) ->
            ManifoldForm.chartTransitionSource I
              (C.boundaryChart i.1) (C.boundaryChart i.1) ∈ 𝓝 y) :
    CoverIndexedBoundaryCarrierSelection (I := I) (K := K) C omega :=
  ofGlobalSupport
    (I := I) (K := K) (C := C) (omega := omega)
    hK hsource hhalf
    (by
      intro i
      exact
        ManifoldForm.transitionPullbackInChart_tsupport_subset_chartCoordinateImage_of_zero_source_mem_nhds
          (I := I) (K := K)
          (x0 := C.boundaryChart i.1) (x1 := C.boundaryChart i.1)
          (omega := omega) hK (hsource i) homega (hsource_nhds i))

/-- Open-neighborhood variant of
`ofGlobalManifoldSupportZeroSourceNeighborhood`. -/
def ofGlobalManifoldSupportZeroOpen
    (hK : IsCompact K)
    (hsource :
      forall i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (hhalf :
      forall i : {x : M // x ∈ C.boundaryCenters},
        chartCoordinateImage I (C.boundaryChart i.1) K ⊆ upperHalfSpace n)
    (homega : ManifoldForm.support I omega ⊆ K)
    (supportNeighborhood :
      {x : M // x ∈ C.boundaryCenters} ->
        Set (Fin (n + 1) -> Real))
    (supportNeighborhood_open :
      forall i : {x : M // x ∈ C.boundaryCenters},
        IsOpen (supportNeighborhood i))
    (base_tsupport_subset_neighborhood :
      forall i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1) omega) ⊆
          supportNeighborhood i)
    (supportNeighborhood_subset_source :
      forall i : {x : M // x ∈ C.boundaryCenters},
        supportNeighborhood i ⊆
          ManifoldForm.chartTransitionSource I
            (C.boundaryChart i.1) (C.boundaryChart i.1)) :
    CoverIndexedBoundaryCarrierSelection (I := I) (K := K) C omega :=
  ofGlobalManifoldSupportZeroSourceNeighborhood
    (I := I) (K := K) (C := C) (omega := omega)
    hK hsource hhalf homega
    (by
      intro i y hy
      exact
        mem_of_superset
          (supportNeighborhood_open i |>.mem_nhds
            (base_tsupport_subset_neighborhood i hy))
          (supportNeighborhood_subset_source i))

end CoverIndexedBoundaryCarrierSelection

namespace CoverIndexedCompactSupportCarrierData

/-- Direct constructor for the grouped carrier data from global manifold
support, via zero-extension support transport. -/
def ofGlobalManifoldSupportZeroSourceNeighborhood
    (hK : IsCompact K)
    (interior_source :
      forall i : {x : M // x ∈ C.interiorCenters},
        K ⊆ (extChartAt I (C.interiorChart i.1)).source)
    (boundary_source :
      forall i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (boundary_half :
      forall i : {x : M // x ∈ C.boundaryCenters},
        chartCoordinateImage I (C.boundaryChart i.1) K ⊆ upperHalfSpace n)
    (homega : ManifoldForm.support I omega ⊆ K)
    (interior_source_nhds :
      forall i : {x : M // x ∈ C.interiorCenters},
        forall y,
          y ∈
          tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.interiorChart i.1) (C.interiorChart i.1) omega) ->
            ManifoldForm.chartTransitionSource I
              (C.interiorChart i.1) (C.interiorChart i.1) ∈ 𝓝 y)
    (boundary_source_nhds :
      forall i : {x : M // x ∈ C.boundaryCenters},
        forall y,
          y ∈
          tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1) omega) ->
            ManifoldForm.chartTransitionSource I
              (C.boundaryChart i.1) (C.boundaryChart i.1) ∈ 𝓝 y) :
    CoverIndexedCompactSupportCarrierData
      (I := I) (K := K) C P omega :=
  ofCarrierSelections
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    (CoverIndexedInteriorCarrierSelection.ofGlobalManifoldSupportZeroSourceNeighborhood
      (I := I) (K := K) (C := C) (omega := omega)
      hK interior_source homega interior_source_nhds)
    (CoverIndexedBoundaryCarrierSelection.ofGlobalManifoldSupportZeroSourceNeighborhood
      (I := I) (K := K) (C := C) (omega := omega)
      hK boundary_source boundary_half homega boundary_source_nhds)

end CoverIndexedCompactSupportCarrierData

namespace CoverIndexedCompactSupportTransitionSupportData

/-- Source-to-target transition support data from global manifold support via
zero-extension support transport.  This removes the old manual ordinary
support-in-target/support-in-overlap hypotheses; the remaining source
neighborhood condition is the honest zero-to-old bridge for the endpoint's old
representative. -/
def ofChartCoordinateImageZeroSourceNeighborhood
    (targetChart : {x : M // x ∈ C.boundaryCenters} -> M)
    (sourceBox_subset_overlap :
      forall i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i))
    (hK : IsCompact K)
    (K_subset_source :
      forall i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (K_subset_target_source :
      forall i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (targetChart i)).source)
    (homega : ManifoldForm.support I omega ⊆ K)
    (source_nhds :
      forall i : {x : M // x ∈ C.boundaryCenters},
        forall y,
          y ∈
          tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) omega) ->
            ManifoldForm.chartTransitionSource I
              (C.boundaryChart i.1) (targetChart i) ∈ 𝓝 y) :
    CoverIndexedCompactSupportTransitionSupportData
      (I := I) (K := K) C P omega :=
  ofChartCoordinateImage
    (I := I) (K := K) (C := C) (P := P) (ω := omega)
    targetChart sourceBox_subset_overlap
    K_subset_source K_subset_target_source
    (by
      intro i
      exact
        ManifoldForm.transitionPullbackInChart_tsupport_subset_chartCoordinateImage_of_zero_source_mem_nhds
          (I := I) (K := K)
          (x0 := C.boundaryChart i.1) (x1 := targetChart i)
          (omega := omega) hK (K_subset_source i) homega (source_nhds i))

/-- Open-neighborhood variant of
`ofChartCoordinateImageZeroSourceNeighborhood`. -/
def ofChartCoordinateImageZeroOpen
    (targetChart : {x : M // x ∈ C.boundaryCenters} -> M)
    (sourceBox_subset_overlap :
      forall i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i))
    (hK : IsCompact K)
    (K_subset_source :
      forall i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (K_subset_target_source :
      forall i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (targetChart i)).source)
    (homega : ManifoldForm.support I omega ⊆ K)
    (supportNeighborhood :
      {x : M // x ∈ C.boundaryCenters} ->
        Set (Fin (n + 1) -> Real))
    (supportNeighborhood_open :
      forall i : {x : M // x ∈ C.boundaryCenters},
        IsOpen (supportNeighborhood i))
    (base_tsupport_subset_neighborhood :
      forall i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) omega) ⊆
          supportNeighborhood i)
    (supportNeighborhood_subset_source :
      forall i : {x : M // x ∈ C.boundaryCenters},
        supportNeighborhood i ⊆
          ManifoldForm.chartTransitionSource I
            (C.boundaryChart i.1) (targetChart i)) :
    CoverIndexedCompactSupportTransitionSupportData
      (I := I) (K := K) C P omega :=
  ofChartCoordinateImageZeroSourceNeighborhood
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    targetChart sourceBox_subset_overlap
    hK K_subset_source K_subset_target_source homega
    (by
      intro i y hy
      exact
        mem_of_superset
          (supportNeighborhood_open i |>.mem_nhds
            (base_tsupport_subset_neighborhood i hy))
          (supportNeighborhood_subset_source i))

/-- The zero-extended source-to-target base representative has coordinate-image
support from global manifold support alone. -/
theorem zero_base_tsupport_subset_transitionCoordSupport_of_globalManifoldSupport
    (targetChart : {x : M // x ∈ C.boundaryCenters} -> M)
    (hK : IsCompact K)
    (K_subset_source :
      forall i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (homega : ManifoldForm.support I omega ⊆ K)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (ManifoldForm.transitionPullbackInChartZero I
          (C.boundaryChart i.1) (targetChart i) omega) ⊆
      chartCoordinateImage I (C.boundaryChart i.1) K :=
  zero_base_tsupport_subset_chartCoordinateImage_of_globalManifoldSupport
    (I := I) (K := K) (C := C) (omega := omega)
    targetChart hK K_subset_source homega i

end CoverIndexedCompactSupportTransitionSupportData

namespace CoverIndexedCompactSupportNeighborhoodData

/-- Source boundary boxes lie in the concrete chart-transition source when the
boundary neighborhood provides chart-target containment and transition data
provides overlap containment. -/
theorem boundary_sourceBox_subset_chartTransitionSource
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodData
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
      ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i) := by
  intro y hy
  rw [ManifoldForm.chartTransitionSource_eq]
  exact
    ⟨CoverIndexedCompactSupportNeighborhoodData.boundary_neighborhood_subset_target
        neighborhoodData i
        (CoverIndexedCompactSupportNeighborhoodData.boundary_Icc_subset_neighborhood
          neighborhoodData i hy),
      transitionSupportData.sourceBox_subset_overlap i hy⟩

/-- On every selected source boundary box, the zero-extended transition
representative agrees with the old smooth representative. -/
theorem boundary_sourceBox_zero_eqOn_transitionPullbackInChart
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodData
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    EqOn
      (ManifoldForm.transitionPullbackInChartZero I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i) omega)
      (ManifoldForm.transitionPullbackInChart I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i) omega)
      (Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :=
  ManifoldForm.transitionPullbackInChartZero_eqOn_transitionPullbackInChart_of_subset_source
    (I := I)
    (x0 := C.boundaryChart i.1)
    (x1 := transitionSupportData.targetChart i)
    (omega := omega)
    (CoverIndexedCompactSupportNeighborhoodData.boundary_sourceBox_subset_chartTransitionSource
      neighborhoodData transitionSupportData i)

end CoverIndexedCompactSupportNeighborhoodData

end CoverIndexedZeroConstructors

end Stokes

end
