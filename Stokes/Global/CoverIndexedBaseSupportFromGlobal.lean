import Stokes.Global.CoverIndexedInteriorCarrierSelection
import Stokes.Global.CoverIndexedBoundaryCarrierSelection

/-!
# Base chart support from global manifold support

This file isolates the honest support bridge used by the compact-support
represented Stokes route.

The important point is that project chart representatives are total functions:
`PartialEquiv.symm` and the chart-transition maps have values outside their
geometric domains.  Therefore a global manifold-side support bound implies a
coordinate-image support bound only after the coordinate representative is known
to be supported in the relevant chart target and, for non-self transitions, in
the chart overlap.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section BaseSupportFromGlobal

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}

/-- If ordinary support is contained in a closed set, then topological support
is contained in the same closed set.  This local copy keeps the support bridge
independent of the carrier-selection namespace. -/
theorem base_tsupport_subset_of_support_subset_isClosed
    {X : Type*} [TopologicalSpace X] {A : Type*} [Zero A]
    {f : X -> A} {s : Set X}
    (hsclosed : IsClosed s) (hsupport : Function.support f ⊆ s) :
    tsupport f ⊆ s := by
  simpa [tsupport] using closure_minimal hsupport hsclosed

namespace ManifoldForm

/-- If a chart representative is nonzero at a coordinate point, then the
underlying manifold form is nonzero at the inverse-chart point. -/
theorem inChart_ne_zero_mapsTo_support
    {x : M} {y : Fin (n + 1) -> Real}
    (hy : inChart I x ω y ≠ 0) :
    (extChartAt I x).symm y ∈ support I ω := by
  rw [mem_support]
  intro hω
  apply hy
  unfold inChart
  rw [hω]
  ext v
  rfl

/-- Nonzero source-to-target transition representatives map, through the
target chart coordinate, to the global manifold-side support. -/
theorem transitionPullbackInChart_ne_zero_mapsTo_support_targetChart
    {x0 x1 : M} {y : Fin (n + 1) -> Real}
    (hy : transitionPullbackInChart I x0 x1 ω y ≠ 0) :
    (extChartAt I x1).symm (chartTransition I x0 x1 y) ∈ support I ω := by
  rw [mem_support]
  intro hω
  apply hy
  unfold transitionPullbackInChart inChart
  rw [hω]
  ext v
  rfl

/-- On a chart overlap, nonzero source-to-target transition representatives map
back to the global support through the source chart inverse. -/
theorem transitionPullbackInChart_ne_zero_mapsTo_support
    {x0 x1 : M} {y : Fin (n + 1) -> Real}
    (hyoverlap : y ∈ chartOverlap I x0 x1)
    (hy : transitionPullbackInChart I x0 x1 ω y ≠ 0) :
    (extChartAt I x0).symm y ∈ support I ω := by
  have htargetSupport :
      (extChartAt I x1).symm (chartTransition I x0 x1 y) ∈
        support I ω :=
    transitionPullbackInChart_ne_zero_mapsTo_support_targetChart
      (I := I) (x0 := x0) (x1 := x1) (ω := ω) hy
  have hleft :
      (extChartAt I x1).symm (chartTransition I x0 x1 y) =
        (extChartAt I x0).symm y := by
    simpa [chartTransition] using (extChartAt I x1).left_inv hyoverlap
  rwa [hleft] at htargetSupport

/-- Self-chart specialization: target membership supplies the self overlap. -/
theorem transitionPullbackInChart_self_ne_zero_mapsTo_support
    {x : M} {y : Fin (n + 1) -> Real}
    (hytarget : y ∈ (extChartAt I x).target)
    (hy : transitionPullbackInChart I x x ω y ≠ 0) :
    (extChartAt I x).symm y ∈ support I ω :=
  transitionPullbackInChart_ne_zero_mapsTo_support
    (I := I) (x0 := x) (x1 := x) (ω := ω)
    ((extChartAt I x).map_target hytarget) hy

/-- With a global support bound, a nonzero self-chart representative in the
chart target maps back into the compact support set. -/
theorem transitionPullbackInChart_self_ne_zero_mapsTo_of_support_subset
    {x : M} {y : Fin (n + 1) -> Real}
    (hωsupport : support I ω ⊆ K)
    (hytarget : y ∈ (extChartAt I x).target)
    (hy : transitionPullbackInChart I x x ω y ≠ 0) :
    (extChartAt I x).symm y ∈ K :=
  hωsupport
    (transitionPullbackInChart_self_ne_zero_mapsTo_support
      (I := I) (x := x) (ω := ω) hytarget hy)

/-- Ordinary support bridge before closing: on the genuine source of a
source-to-target transition, global manifold support gives coordinate-image
support. -/
theorem transitionPullbackInChart_support_inter_transitionSource_subset_chartCoordinateImage
    {x0 x1 : M}
    (hωsupport : support I ω ⊆ K) :
    Function.support (transitionPullbackInChart I x0 x1 ω) ∩
        ((extChartAt I x0).target ∩ chartOverlap I x0 x1) ⊆
      chartCoordinateImage I x0 K := by
  rintro y ⟨hy, hytarget, hyoverlap⟩
  have hyne :
      transitionPullbackInChart I x0 x1 ω y ≠ 0 := by
    simpa [Function.mem_support] using hy
  have hK : (extChartAt I x0).symm y ∈ K :=
    hωsupport
      (transitionPullbackInChart_ne_zero_mapsTo_support
        (I := I) (x0 := x0) (x1 := x1) (ω := ω) hyoverlap hyne)
  exact ⟨(extChartAt I x0).symm y, hK, (extChartAt I x0).right_inv hytarget⟩

/-- Ordinary support bridge in the convenient subset form.  The target and
overlap hypotheses are necessary because chart representatives are total
outside the geometric chart-transition source. -/
theorem transitionPullbackInChart_support_subset_chartCoordinateImage
    {x0 x1 : M}
    (htarget :
      Function.support (transitionPullbackInChart I x0 x1 ω) ⊆
        (extChartAt I x0).target)
    (hoverlap :
      Function.support (transitionPullbackInChart I x0 x1 ω) ⊆
        chartOverlap I x0 x1)
    (hωsupport : support I ω ⊆ K) :
    Function.support (transitionPullbackInChart I x0 x1 ω) ⊆
      chartCoordinateImage I x0 K := by
  intro y hy
  exact
    transitionPullbackInChart_support_inter_transitionSource_subset_chartCoordinateImage
      (I := I) (K := K) (ω := ω) (x0 := x0) (x1 := x1) hωsupport
      ⟨hy, htarget hy, hoverlap hy⟩

/-- Topological-support bridge from global manifold support to a coordinate
chart image.  Compactness and source containment make the coordinate image
closed, so the ordinary support bridge closes to `tsupport`. -/
theorem transitionPullbackInChart_tsupport_subset_chartCoordinateImage
    {x0 x1 : M}
    (hK : IsCompact K)
    (hsource : K ⊆ (extChartAt I x0).source)
    (htarget :
      Function.support (transitionPullbackInChart I x0 x1 ω) ⊆
        (extChartAt I x0).target)
    (hoverlap :
      Function.support (transitionPullbackInChart I x0 x1 ω) ⊆
        chartOverlap I x0 x1)
    (hωsupport : support I ω ⊆ K) :
    tsupport (transitionPullbackInChart I x0 x1 ω) ⊆
      chartCoordinateImage I x0 K :=
  base_tsupport_subset_of_support_subset_isClosed
    (isCompact_chartCoordinateImage_of_subset_source
      (I := I) (x := x0) hK hsource |>.isClosed)
    (transitionPullbackInChart_support_subset_chartCoordinateImage
      (I := I) (K := K) (ω := ω) htarget hoverlap hωsupport)

/-- Self-chart ordinary support bridge before closing. -/
theorem transitionPullbackInChart_self_support_inter_target_subset_chartCoordinateImage
    {x : M}
    (hωsupport : support I ω ⊆ K) :
    Function.support (transitionPullbackInChart I x x ω) ∩
        (extChartAt I x).target ⊆
      chartCoordinateImage I x K := by
  rintro y ⟨hy, hytarget⟩
  exact
    transitionPullbackInChart_support_inter_transitionSource_subset_chartCoordinateImage
      (I := I) (K := K) (ω := ω) (x0 := x) (x1 := x) hωsupport
      ⟨hy, hytarget, (extChartAt I x).map_target hytarget⟩

/-- Self-chart ordinary support bridge in subset form. -/
theorem transitionPullbackInChart_self_support_subset_chartCoordinateImage
    {x : M}
    (htarget :
      Function.support (transitionPullbackInChart I x x ω) ⊆
        (extChartAt I x).target)
    (hωsupport : support I ω ⊆ K) :
    Function.support (transitionPullbackInChart I x x ω) ⊆
      chartCoordinateImage I x K := by
  intro y hy
  exact
    transitionPullbackInChart_self_support_inter_target_subset_chartCoordinateImage
      (I := I) (K := K) (ω := ω) hωsupport ⟨hy, htarget hy⟩

/-- Self-chart topological support bridge, the main form consumed by compact
chart-carrier selection. -/
theorem transitionPullbackInChart_self_tsupport_subset_chartCoordinateImage
    {x : M}
    (hK : IsCompact K)
    (hsource : K ⊆ (extChartAt I x).source)
    (htarget :
      Function.support (transitionPullbackInChart I x x ω) ⊆
        (extChartAt I x).target)
    (hωsupport : support I ω ⊆ K) :
    tsupport (transitionPullbackInChart I x x ω) ⊆
      chartCoordinateImage I x K :=
  transitionPullbackInChart_tsupport_subset_chartCoordinateImage
    (I := I) (K := K) (ω := ω) (x0 := x) (x1 := x)
    hK hsource htarget
    (fun _ hy => (extChartAt I x).map_target (htarget hy))
    hωsupport

end ManifoldForm

namespace CoverIndexedInteriorCarrierSelection

variable {C : CompactSupportChartCoverSelection I K}
variable {omega : ManifoldForm I M n}

/-- Build the interior coordinate-carrier selection from a global
`ManifoldForm.support` bound, plus the unavoidable target-support fact for
the total self-chart representatives. -/
def ofGlobalManifoldSupport
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        K ⊆ (extChartAt I (C.interiorChart i.1)).source)
    (htarget :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        Function.support
            (ManifoldForm.transitionPullbackInChart I
              (C.interiorChart i.1) (C.interiorChart i.1) omega) ⊆
          (extChartAt I (C.interiorChart i.1)).target)
    (hωsupport : ManifoldForm.support I omega ⊆ K) :
    CoverIndexedInteriorCarrierSelection C omega :=
  ofSupportTargetMapsTo
    (I := I) (K := K) (C := C) (omega := omega)
    hK hsource htarget
    (by
      intro i y hytarget hyne
      exact
        ManifoldForm.transitionPullbackInChart_self_ne_zero_mapsTo_of_support_subset
          (I := I) (K := K) (ω := omega)
          hωsupport hytarget hyne)

/-- Direct access to the generated base-support field from global manifold
support. -/
theorem base_tsupport_subset_chartCoordinateImage_of_globalManifoldSupport
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        K ⊆ (extChartAt I (C.interiorChart i.1)).source)
    (htarget :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        Function.support
            (ManifoldForm.transitionPullbackInChart I
              (C.interiorChart i.1) (C.interiorChart i.1) omega) ⊆
          (extChartAt I (C.interiorChart i.1)).target)
    (hωsupport : ManifoldForm.support I omega ⊆ K)
    (i : {x : M // x ∈ C.interiorCenters}) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (C.interiorChart i.1) (C.interiorChart i.1) omega) ⊆
      chartCoordinateImage I (C.interiorChart i.1) K :=
  ManifoldForm.transitionPullbackInChart_self_tsupport_subset_chartCoordinateImage
    (I := I) (K := K) (ω := omega)
    hK (hsource i) (htarget i) hωsupport

end CoverIndexedInteriorCarrierSelection

namespace BoundaryChartCoordinateCarrier

variable {x : M}
variable {omega : ManifoldForm I M n}

/-- One boundary chart carrier obtained from the global support set itself,
with the base `tsupport` field generated from `ManifoldForm.support I omega ⊆ K`.
-/
def ofGlobalManifoldSupport
    (hK : IsCompact K)
    (hsource : K ⊆ (extChartAt I x).source)
    (hhalf : chartCoordinateImage I x K ⊆ upperHalfSpace n)
    (htarget :
      Function.support
          (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
        (extChartAt I x).target)
    (hωsupport : ManifoldForm.support I omega ⊆ K) :
    BoundaryChartCoordinateCarrier I K x omega :=
  ofGlobalChartCoordinateImage
    (I := I) (K := K) (x := x) (omega := omega)
    hK hsource hhalf
    (ManifoldForm.transitionPullbackInChart_self_tsupport_subset_chartCoordinateImage
      (I := I) (K := K) (ω := omega)
      hK hsource htarget hωsupport)

end BoundaryChartCoordinateCarrier

namespace CoverIndexedBoundaryCarrierSelection

variable {C : CompactSupportChartCoverSelection I K}
variable {omega : ManifoldForm I M n}

/-- Build the boundary coordinate-carrier family from global support, using
`chartCoordinateImage I (C.boundaryChart i) K` at every boundary index. -/
def ofGlobalManifoldSupport
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (hhalf :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        chartCoordinateImage I (C.boundaryChart i.1) K ⊆ upperHalfSpace n)
    (htarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Function.support
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1) omega) ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (hωsupport : ManifoldForm.support I omega ⊆ K) :
    CoverIndexedBoundaryCarrierSelection C omega :=
  ofGlobalSupport
    (I := I) (K := K) (C := C) (omega := omega)
    hK hsource hhalf
    (by
      intro i
      exact
        ManifoldForm.transitionPullbackInChart_self_tsupport_subset_chartCoordinateImage
          (I := I) (K := K) (ω := omega)
          hK (hsource i) (htarget i) hωsupport)

/-- Direct access to the generated boundary base-support field from global
manifold support. -/
theorem base_tsupport_subset_chartCoordinateImage_of_globalManifoldSupport
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (htarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Function.support
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1) omega) ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (hωsupport : ManifoldForm.support I omega ⊆ K)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1) omega) ⊆
      chartCoordinateImage I (C.boundaryChart i.1) K :=
  ManifoldForm.transitionPullbackInChart_self_tsupport_subset_chartCoordinateImage
    (I := I) (K := K) (ω := omega)
    hK (hsource i) (htarget i) hωsupport

end CoverIndexedBoundaryCarrierSelection

end BaseSupportFromGlobal

end Stokes

end
