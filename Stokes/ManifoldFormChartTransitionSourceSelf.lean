import Stokes.ManifoldFormChartTransitionSourceSelfCore
import Stokes.Global.CoverIndexedZeroConstructors

/-!
# Self chart-transition source constructors

The low-level self-chart facts live in
`Stokes.ManifoldFormChartTransitionSourceSelfCore`.  This compatibility module
keeps the older cover-indexed constructor layer separate from that core API.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

universe uE uH uM

section ManifoldFormSelfSourceZeroBridge

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H}
variable {K : Set M}
variable {x : M}
variable {k : Nat}
variable {omega : ManifoldForm I M k}
variable [IsManifold I 1 M]

namespace ManifoldForm

/-- Self-chart specialization of the old-to-zero topological-support bridge,
with the source neighborhood condition generated from coordinate-image
containment. -/
theorem transitionPullbackInChart_self_tsupport_subset_zero_tsupport_of_tsupport_subset_chartCoordinateImage
    [I.Boundaryless]
    (hsource : K ⊆ (extChartAt I x).source)
    (hsupp :
      tsupport (transitionPullbackInChart I x x omega) ⊆
        chartCoordinateImage I x K) :
    tsupport (transitionPullbackInChart I x x omega) ⊆
      tsupport (transitionPullbackInChartZero I x x omega) :=
  transitionPullbackInChart_tsupport_subset_zero_tsupport_of_source_mem_nhds
    (I := I) (x0 := x) (x1 := x) (omega := omega)
    (transitionPullbackInChart_self_source_mem_nhds_of_tsupport_subset_chartCoordinateImage
      (I := I) (K := K) (x := x) (omega := omega) hsource hsupp)

end ManifoldForm

end ManifoldFormSelfSourceZeroBridge

section CoverIndexedSelfConstructors

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {omega : ManifoldForm I M n}
variable [IsManifold I 1 M]
variable [I.Boundaryless]

namespace CoverIndexedInteriorCarrierSelection

/-- Interior carrier constructor whose zero-extension source-neighborhood
condition is generated automatically in the self-chart case from the existing
coordinate-image support bound. -/
def ofGlobalManifoldSupportZeroSelf
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        K ⊆ (extChartAt I (C.interiorChart i.1)).source)
    (homega : ManifoldForm.support I omega ⊆ K)
    (base_tsupport_subset_chartCoordinateImage :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.interiorChart i.1) (C.interiorChart i.1) omega) ⊆
          chartCoordinateImage I (C.interiorChart i.1) K) :
    CoverIndexedInteriorCarrierSelection (I := I) (K := K) C omega :=
  ofGlobalManifoldSupportZeroSourceNeighborhood
    (I := I) (K := K) (C := C) (omega := omega)
    hK hsource homega
    (by
      intro i
      exact
        ManifoldForm.transitionPullbackInChart_self_source_mem_nhds_of_tsupport_subset_chartCoordinateImage
          (I := I) (K := K) (x := C.interiorChart i.1) (omega := omega)
          (hsource i) (base_tsupport_subset_chartCoordinateImage i))

end CoverIndexedInteriorCarrierSelection

namespace BoundaryChartCoordinateCarrier

variable {x : M}

/-- One boundary carrier with the self-chart source-neighborhood condition
generated from coordinate-image support. -/
def ofGlobalManifoldSupportZeroSelf
    (hK : IsCompact K)
    (hsource : K ⊆ (extChartAt I x).source)
    (hhalf : chartCoordinateImage I x K ⊆ upperHalfSpace n)
    (homega : ManifoldForm.support I omega ⊆ K)
    (base_tsupport_subset_chartCoordinateImage :
      tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
        chartCoordinateImage I x K) :
    BoundaryChartCoordinateCarrier I K x omega :=
  ofGlobalManifoldSupportZeroSourceNeighborhood
    (I := I) (K := K) (x := x) (omega := omega)
    hK hsource hhalf homega
    (ManifoldForm.transitionPullbackInChart_self_source_mem_nhds_of_tsupport_subset_chartCoordinateImage
      (I := I) (K := K) (x := x) (omega := omega)
      hsource base_tsupport_subset_chartCoordinateImage)

end BoundaryChartCoordinateCarrier

namespace CoverIndexedBoundaryCarrierSelection

/-- Boundary carrier family constructor whose zero-extension
source-neighborhood condition is automatic for self charts. -/
def ofGlobalManifoldSupportZeroSelf
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (hhalf :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        chartCoordinateImage I (C.boundaryChart i.1) K ⊆ upperHalfSpace n)
    (homega : ManifoldForm.support I omega ⊆ K)
    (base_tsupport_subset_chartCoordinateImage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1) omega) ⊆
          chartCoordinateImage I (C.boundaryChart i.1) K) :
    CoverIndexedBoundaryCarrierSelection (I := I) (K := K) C omega :=
  ofGlobalManifoldSupportZeroSourceNeighborhood
    (I := I) (K := K) (C := C) (omega := omega)
    hK hsource hhalf homega
    (by
      intro i
      exact
        ManifoldForm.transitionPullbackInChart_self_source_mem_nhds_of_tsupport_subset_chartCoordinateImage
          (I := I) (K := K) (x := C.boundaryChart i.1) (omega := omega)
          (hsource i) (base_tsupport_subset_chartCoordinateImage i))

end CoverIndexedBoundaryCarrierSelection

namespace CoverIndexedCompactSupportCarrierData

/-- Grouped carrier-data constructor with self-chart zero-extension
source-neighborhood obligations generated automatically from the existing
coordinate-image support fields. -/
def ofGlobalManifoldSupportZeroSelf
    (hK : IsCompact K)
    (interior_source :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        K ⊆ (extChartAt I (C.interiorChart i.1)).source)
    (boundary_source :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (boundary_half :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        chartCoordinateImage I (C.boundaryChart i.1) K ⊆ upperHalfSpace n)
    (homega : ManifoldForm.support I omega ⊆ K)
    (interior_base_tsupport_subset_chartCoordinateImage :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.interiorChart i.1) (C.interiorChart i.1) omega) ⊆
          chartCoordinateImage I (C.interiorChart i.1) K)
    (boundary_base_tsupport_subset_chartCoordinateImage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1) omega) ⊆
          chartCoordinateImage I (C.boundaryChart i.1) K) :
    CoverIndexedCompactSupportCarrierData
      (I := I) (K := K) C P omega :=
  ofGlobalManifoldSupportZeroSourceNeighborhood
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    hK interior_source boundary_source boundary_half homega
    (by
      intro i
      exact
        ManifoldForm.transitionPullbackInChart_self_source_mem_nhds_of_tsupport_subset_chartCoordinateImage
          (I := I) (K := K) (x := C.interiorChart i.1) (omega := omega)
          (interior_source i) (interior_base_tsupport_subset_chartCoordinateImage i))
    (by
      intro i
      exact
        ManifoldForm.transitionPullbackInChart_self_source_mem_nhds_of_tsupport_subset_chartCoordinateImage
          (I := I) (K := K) (x := C.boundaryChart i.1) (omega := omega)
          (boundary_source i) (boundary_base_tsupport_subset_chartCoordinateImage i))

end CoverIndexedCompactSupportCarrierData

namespace CoverIndexedCompactSupportTransitionSupportData

/-- Self-target specialization of the transition-support constructor.  The
source-box overlap field is reduced to target containment, and the
zero-extension source-neighborhood field is generated from coordinate-image
support. -/
def ofChartCoordinateImageZeroSelf
    (sourceBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (hK : IsCompact K)
    (K_subset_source :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (homega : ManifoldForm.support I omega ⊆ K)
    (base_tsupport_subset_chartCoordinateImage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1) omega) ⊆
          chartCoordinateImage I (C.boundaryChart i.1) K) :
    CoverIndexedCompactSupportTransitionSupportData
      (I := I) (K := K) C P omega :=
  ofChartCoordinateImageZeroSourceNeighborhood
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    (fun i => C.boundaryChart i.1)
    (by
      intro i y hy
      exact
        (extChartAt I (C.boundaryChart i.1)).map_target
          (sourceBox_subset_target i hy))
    hK K_subset_source K_subset_source homega
    (by
      intro i
      exact
        ManifoldForm.transitionPullbackInChart_self_source_mem_nhds_of_tsupport_subset_chartCoordinateImage
          (I := I) (K := K) (x := C.boundaryChart i.1) (omega := omega)
          (K_subset_source i) (base_tsupport_subset_chartCoordinateImage i))

end CoverIndexedCompactSupportTransitionSupportData

end CoverIndexedSelfConstructors

end Stokes

end
