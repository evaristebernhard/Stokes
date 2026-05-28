import Stokes.ManifoldFormZero
import Stokes.Global.CoverIndexedBaseSupportFromGlobal
import Stokes.Global.CoverIndexedTransitionSupportFromGlobal

/-!
# Zero-extended chart support from global compact support

This file is the zero-extension version of the support bridge in
`CoverIndexedBaseSupportFromGlobal` and
`CoverIndexedTransitionSupportFromGlobal`.

The old bridge needed explicit hypotheses saying that the total chart
representative was supported in the chart target and overlap.  For
`ManifoldForm.transitionPullbackInChartZero` those facts are definitional:
the representative is zero outside the concrete transition source.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ZeroSupportFromGlobal

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {k : Nat}
variable {I : ModelWithCorners Real E H}
variable {K : Set M}
variable {x0 x1 : M}
variable {ω : ManifoldForm I M k}
variable [IsManifold I 1 M]

namespace ManifoldForm

/-- A nonzero zero-extended transition representative lies in the concrete
transition source. -/
theorem transitionPullbackInChartZero_ne_zero_mem_source
    {y : E}
    (hy : transitionPullbackInChartZero I x0 x1 ω y ≠ 0) :
    y ∈ chartTransitionSource I x0 x1 := by
  have hysupp :
      y ∈ Function.support (transitionPullbackInChartZero I x0 x1 ω) := by
    simpa [Function.mem_support] using hy
  exact transitionPullbackInChartZero_support_subset_source
    (I := I) x0 x1 ω hysupp

/-- A nonzero zero-extended transition representative is also nonzero for the
ordinary transition representative. -/
theorem transitionPullbackInChart_ne_zero_of_zero_ne_zero
    {y : E}
    (hy : transitionPullbackInChartZero I x0 x1 ω y ≠ 0) :
    transitionPullbackInChart I x0 x1 ω y ≠ 0 := by
  have hsource :
      y ∈ chartTransitionSource I x0 x1 :=
    transitionPullbackInChartZero_ne_zero_mem_source
      (I := I) (x0 := x0) (x1 := x1) (ω := ω) hy
  intro hold
  apply hy
  rw [transitionPullbackInChartZero_eq_transitionPullbackInChart_of_mem_source
    (I := I) (x0 := x0) (x1 := x1) (ω := ω) hsource]
  exact hold

/-- Pointwise zero-extension support bridge: nonzero zero transition
representatives map back to the global manifold-side support. -/
theorem transitionPullbackInChartZero_ne_zero_mapsTo_support
    {y : E}
    (hy : transitionPullbackInChartZero I x0 x1 ω y ≠ 0) :
    (extChartAt I x0).symm y ∈ support I ω := by
  have hsource :
      y ∈ chartTransitionSource I x0 x1 :=
    transitionPullbackInChartZero_ne_zero_mem_source
      (I := I) (x0 := x0) (x1 := x1) (ω := ω) hy
  have hsource' :
      y ∈ (extChartAt I x0).target ∩ chartOverlap I x0 x1 := by
    simpa [chartTransitionSource_eq] using hsource
  have holdSupport :
      y ∈ Function.support (transitionPullbackInChart I x0 x1 ω) := by
    simpa [Function.mem_support] using
      (transitionPullbackInChart_ne_zero_of_zero_ne_zero
        (I := I) (x0 := x0) (x1 := x1) (ω := ω) hy)
  exact
    Stokes.transitionPullbackInChart_support_mapsTo_manifoldSupport_of_mem_overlap
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      hsource'.2 holdSupport

/-- With a global support bound, nonzero zero transition representatives map
back into the compact support set. -/
theorem transitionPullbackInChartZero_ne_zero_mapsTo_of_support_subset
    {y : E}
    (hωsupport : support I ω ⊆ K)
    (hy : transitionPullbackInChartZero I x0 x1 ω y ≠ 0) :
    (extChartAt I x0).symm y ∈ K :=
  hωsupport
    (transitionPullbackInChartZero_ne_zero_mapsTo_support
      (I := I) (x0 := x0) (x1 := x1) (ω := ω) hy)

/-- Ordinary support of the zero-extended transition representative is
contained in the coordinate image of the global support set. -/
theorem transitionPullbackInChartZero_support_subset_chartCoordinateImage
    (hωsupport : support I ω ⊆ K) :
    Function.support (transitionPullbackInChartZero I x0 x1 ω) ⊆
      chartCoordinateImage I x0 K := by
  intro y hy
  have hyne :
      transitionPullbackInChartZero I x0 x1 ω y ≠ 0 := by
    simpa [Function.mem_support] using hy
  have htarget :
      y ∈ (extChartAt I x0).target :=
    transitionPullbackInChartZero_support_subset_target
      (I := I) x0 x1 ω hy
  refine ⟨(extChartAt I x0).symm y,
    transitionPullbackInChartZero_ne_zero_mapsTo_of_support_subset
      (I := I) (K := K) (x0 := x0) (x1 := x1) (ω := ω)
      hωsupport hyne, ?_⟩
  exact (extChartAt I x0).right_inv htarget

/-- Topological support version of
`transitionPullbackInChartZero_support_subset_chartCoordinateImage`. -/
theorem transitionPullbackInChartZero_tsupport_subset_chartCoordinateImage_of_closed
    (hclosed : IsClosed (chartCoordinateImage I x0 K))
    (hωsupport : support I ω ⊆ K) :
    tsupport (transitionPullbackInChartZero I x0 x1 ω) ⊆
      chartCoordinateImage I x0 K := by
  simpa [tsupport] using
    closure_minimal
      (transitionPullbackInChartZero_support_subset_chartCoordinateImage
        (I := I) (K := K) (x0 := x0) (x1 := x1) (ω := ω)
        hωsupport)
      hclosed

/-- Compact-source version of the zero-extension topological support bridge. -/
theorem transitionPullbackInChartZero_tsupport_subset_chartCoordinateImage
    (hK : IsCompact K)
    (hsource : K ⊆ (extChartAt I x0).source)
    (hωsupport : support I ω ⊆ K) :
    tsupport (transitionPullbackInChartZero I x0 x1 ω) ⊆
      chartCoordinateImage I x0 K :=
  transitionPullbackInChartZero_tsupport_subset_chartCoordinateImage_of_closed
    (I := I) (K := K) (x0 := x0) (x1 := x1) (ω := ω)
    (isCompact_chartCoordinateImage_of_subset_source
      (I := I) (x := x0) hK hsource |>.isClosed)
    hωsupport

/-- Self-chart specialization for zero-extended representatives. -/
theorem transitionPullbackInChartZero_self_tsupport_subset_chartCoordinateImage
    {x : M}
    (hK : IsCompact K)
    (hsource : K ⊆ (extChartAt I x).source)
    (hωsupport : support I ω ⊆ K) :
    tsupport (transitionPullbackInChartZero I x x ω) ⊆
      chartCoordinateImage I x K :=
  transitionPullbackInChartZero_tsupport_subset_chartCoordinateImage
    (I := I) (K := K) (x0 := x) (x1 := x) (ω := ω)
    hK hsource hωsupport

end ManifoldForm

end ZeroSupportFromGlobal

section CoverIndexedZeroSupport

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

/-- Interior cover-indexed zero-support field generated from global manifold
support.  This is the zero-extension replacement for the old target-support
input in `ofGlobalManifoldSupport`. -/
theorem zero_base_tsupport_subset_chartCoordinateImage_of_globalManifoldSupport
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        K ⊆ (extChartAt I (C.interiorChart i.1)).source)
    (hωsupport : ManifoldForm.support I omega ⊆ K)
    (i : {x : M // x ∈ C.interiorCenters}) :
    tsupport
        (ManifoldForm.transitionPullbackInChartZero I
          (C.interiorChart i.1) (C.interiorChart i.1) omega) ⊆
      chartCoordinateImage I (C.interiorChart i.1) K :=
  ManifoldForm.transitionPullbackInChartZero_self_tsupport_subset_chartCoordinateImage
    (I := I) (K := K) (ω := omega)
    hK (hsource i) hωsupport

end CoverIndexedInteriorCarrierSelection

namespace BoundaryChartCoordinateCarrier

variable {x : M}

/-- One boundary chart zero-support field generated from global manifold
support. -/
theorem zero_base_tsupport_subset_chartCoordinateImage_of_globalManifoldSupport
    (hK : IsCompact K)
    (hsource : K ⊆ (extChartAt I x).source)
    (hωsupport : ManifoldForm.support I omega ⊆ K) :
    tsupport
        (ManifoldForm.transitionPullbackInChartZero I x x omega) ⊆
      chartCoordinateImage I x K :=
  ManifoldForm.transitionPullbackInChartZero_self_tsupport_subset_chartCoordinateImage
    (I := I) (K := K) (ω := omega)
    hK hsource hωsupport

end BoundaryChartCoordinateCarrier

namespace CoverIndexedBoundaryCarrierSelection

/-- Boundary cover-indexed zero-support field generated from global manifold
support.  The remaining half-space condition belongs to carrier geometry, not
to support transport. -/
theorem zero_base_tsupport_subset_chartCoordinateImage_of_globalManifoldSupport
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (hωsupport : ManifoldForm.support I omega ⊆ K)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (ManifoldForm.transitionPullbackInChartZero I
          (C.boundaryChart i.1) (C.boundaryChart i.1) omega) ⊆
      chartCoordinateImage I (C.boundaryChart i.1) K :=
  ManifoldForm.transitionPullbackInChartZero_self_tsupport_subset_chartCoordinateImage
    (I := I) (K := K) (ω := omega)
    hK (hsource i) hωsupport

end CoverIndexedBoundaryCarrierSelection

namespace CoverIndexedCompactSupportTransitionSupportData

/-- Source-to-target boundary transition zero-support fields generated from
global manifold support.  This is the field-level constructor needed by the
next assembly step; unlike the old nonzero bridge it has no manual
target/overlap support hypotheses. -/
theorem zero_base_tsupport_subset_chartCoordinateImage_of_globalManifoldSupport
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (hωsupport : ManifoldForm.support I omega ⊆ K)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (ManifoldForm.transitionPullbackInChartZero I
          (C.boundaryChart i.1) (targetChart i) omega) ⊆
      chartCoordinateImage I (C.boundaryChart i.1) K :=
  ManifoldForm.transitionPullbackInChartZero_tsupport_subset_chartCoordinateImage
    (I := I) (K := K)
    (x0 := C.boundaryChart i.1) (x1 := targetChart i) (ω := omega)
    hK (hsource i) hωsupport

end CoverIndexedCompactSupportTransitionSupportData

end CoverIndexedZeroSupport

end Stokes

end
