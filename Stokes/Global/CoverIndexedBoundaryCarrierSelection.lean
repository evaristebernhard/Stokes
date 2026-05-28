import Stokes.Global.CoverIndexedLocalDataFromCompactSupport

/-!
# Boundary coordinate carriers for cover-indexed compact support

This file isolates the boundary carrier-selection step used by
`CoverIndexedBoundaryLocalDataFromCompactSupport`.

The main constructor is not a new Stokes theorem.  It records the point-set
fact needed before local half-space Stokes can be applied: a compact
manifold-side support contained in one boundary chart source has a compact
coordinate image; if that image lies in the half-space model and carries the
base chart representative, then it supplies all carrier fields required by the
cover-indexed boundary local-data package.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section BoundaryCarrierSelection

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {omega : ManifoldForm I M n}

/-- If a coordinate point is in the chart image of a source-contained set, then
the inverse chart point lies back in that set. -/
theorem chartCoordinateImage_symm_mem_of_subset_source
    {x : M} {S : Set M}
    (hsource : S ⊆ (extChartAt I x).source)
    {y : Fin (n + 1) -> Real}
    (hy : y ∈ chartCoordinateImage I x S) :
    (extChartAt I x).symm y ∈ S := by
  rcases hy with ⟨p, hp, rfl⟩
  have hsymm :
      (extChartAt I x).symm ((extChartAt I x) p) = p :=
    (extChartAt I x).left_inv (hsource hp)
  rw [hsymm]
  exact hp

/-- A single boundary coordinate carrier with exactly the five point-set fields
needed by `CoverIndexedBoundaryLocalDataFromCompactSupport`. -/
structure BoundaryChartCoordinateCarrier
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (K : Set M) (x : M) (omega : ManifoldForm I M n) where
  /-- Coordinate-side compact carrier. -/
  coordSupport : Set (Fin (n + 1) -> Real)
  /-- The carrier is compact. -/
  coord_compact : IsCompact coordSupport
  /-- Boundary carriers live in the half-space model. -/
  coord_subset_halfSpace : coordSupport ⊆ upperHalfSpace n
  /-- The base chart representative is carried by this coordinate support. -/
  base_tsupport_subset :
    tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆ coordSupport
  /-- The inverse chart sends the carrier back to the global compact support set. -/
  coord_mapsTo_support :
    ∀ y ∈ coordSupport, (extChartAt I x).symm y ∈ K
  /-- The carrier lies in the chart target, so chart inverses are genuine. -/
  coord_subset_target : coordSupport ⊆ (extChartAt I x).target

namespace BoundaryChartCoordinateCarrier

variable {x : M}

/-- Constructor from an explicit coordinate carrier and the five carrier facts. -/
def ofCarrier
    (coordSupport : Set (Fin (n + 1) -> Real))
    (hcompact : IsCompact coordSupport)
    (hhalf : coordSupport ⊆ upperHalfSpace n)
    (hbase :
      tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆ coordSupport)
    (hcoordK :
      ∀ y ∈ coordSupport, (extChartAt I x).symm y ∈ K)
    (htarget : coordSupport ⊆ (extChartAt I x).target) :
    BoundaryChartCoordinateCarrier I K x omega where
  coordSupport := coordSupport
  coord_compact := hcompact
  coord_subset_halfSpace := hhalf
  base_tsupport_subset := hbase
  coord_mapsTo_support := hcoordK
  coord_subset_target := htarget

/-- Constructor from a compact manifold-side support in a boundary chart source.

The coordinate carrier is `chartCoordinateImage I x S`.  Compactness,
`target` containment, and inverse-image membership are automatic; the genuine
remaining mathematical inputs are half-space containment of that coordinate
image and base representative support containment. -/
def ofChartCoordinateImage
    (S : Set M)
    (hcompact : IsCompact S)
    (hsource : S ⊆ (extChartAt I x).source)
    (hSK : S ⊆ K)
    (hhalf : chartCoordinateImage I x S ⊆ upperHalfSpace n)
    (hbase :
      tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
        chartCoordinateImage I x S) :
    BoundaryChartCoordinateCarrier I K x omega where
  coordSupport := chartCoordinateImage I x S
  coord_compact :=
    isCompact_chartCoordinateImage_of_subset_source hcompact hsource
  coord_subset_halfSpace := hhalf
  base_tsupport_subset := hbase
  coord_mapsTo_support := by
    intro y hy
    exact hSK (chartCoordinateImage_symm_mem_of_subset_source (I := I) hsource hy)
  coord_subset_target := chartCoordinateImage_subset_target hsource

/-- Global-support specialization: use the compact support set itself as the
manifold-side source support for one chart. -/
def ofGlobalChartCoordinateImage
    (hcompact : IsCompact K)
    (hsource : K ⊆ (extChartAt I x).source)
    (hhalf : chartCoordinateImage I x K ⊆ upperHalfSpace n)
    (hbase :
      tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
        chartCoordinateImage I x K) :
    BoundaryChartCoordinateCarrier I K x omega :=
  ofChartCoordinateImage
    (I := I) (K := K) (x := x) (omega := omega)
    K hcompact hsource (Subset.refl K) hhalf hbase

end BoundaryChartCoordinateCarrier

/-- Cover-indexed boundary carrier family: exactly the five carrier fields of
`CoverIndexedBoundaryLocalDataFromCompactSupport`, without the smoothness
neighborhood fields. -/
structure CoverIndexedBoundaryCarrierSelection
    (C : CompactSupportChartCoverSelection I K)
    (omega : ManifoldForm I M n) where
  /-- Coordinate carriers for selected boundary cover pieces. -/
  coordSupport :
    {x : M // x ∈ C.boundaryCenters} ->
      Set (Fin (n + 1) -> Real)
  /-- Boundary coordinate carriers are compact. -/
  coord_compact :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      IsCompact (coordSupport i)
  /-- Boundary coordinate carriers lie in the upper half-space. -/
  coord_subset_halfSpace :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      coordSupport i ⊆ upperHalfSpace n
  /-- Base boundary representatives are supported in the chosen carriers. -/
  base_tsupport_subset :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1) omega) ⊆
        coordSupport i
  /-- Boundary coordinate carriers map back into the compact support set. -/
  coord_mapsTo_support :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      ∀ y ∈ coordSupport i,
        (extChartAt I (C.boundaryChart i.1)).symm y ∈ K
  /-- Boundary coordinate carriers lie in their selected chart targets. -/
  coord_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      coordSupport i ⊆ (extChartAt I (C.boundaryChart i.1)).target

namespace CoverIndexedBoundaryCarrierSelection

/-- Project the carrier selected at one boundary index. -/
def chartCarrier
    (D : CoverIndexedBoundaryCarrierSelection C omega)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    BoundaryChartCoordinateCarrier I K (C.boundaryChart i.1) omega where
  coordSupport := D.coordSupport i
  coord_compact := D.coord_compact i
  coord_subset_halfSpace := D.coord_subset_halfSpace i
  base_tsupport_subset := D.base_tsupport_subset i
  coord_mapsTo_support := D.coord_mapsTo_support i
  coord_subset_target := D.coord_subset_target i

/-- Build a cover-indexed carrier family from already packaged one-chart
carriers. -/
def ofChartCarriers
    (carrier :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartCoordinateCarrier I K (C.boundaryChart i.1) omega) :
    CoverIndexedBoundaryCarrierSelection C omega where
  coordSupport := fun i => (carrier i).coordSupport
  coord_compact := fun i => (carrier i).coord_compact
  coord_subset_halfSpace := fun i => (carrier i).coord_subset_halfSpace
  base_tsupport_subset := fun i => (carrier i).base_tsupport_subset
  coord_mapsTo_support := fun i => (carrier i).coord_mapsTo_support
  coord_subset_target := fun i => (carrier i).coord_subset_target

/-- Build boundary carriers from compact manifold-side source supports, one for
each selected boundary cover index.

This is the useful compact-support constructor: it turns the geometric
selection of compact source supports into the five carrier fields consumed by
local half-space Stokes. -/
def ofSourceSupports
    (sourceSupport :
      {x : M // x ∈ C.boundaryCenters} -> Set M)
    (hcompact :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsCompact (sourceSupport i))
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        sourceSupport i ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (hSK :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        sourceSupport i ⊆ K)
    (hhalf :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        chartCoordinateImage I (C.boundaryChart i.1) (sourceSupport i) ⊆
          upperHalfSpace n)
    (hbase :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1) omega) ⊆
          chartCoordinateImage I (C.boundaryChart i.1) (sourceSupport i)) :
    CoverIndexedBoundaryCarrierSelection C omega :=
  ofChartCarriers
    (C := C) (K := K) (omega := omega)
    (fun i =>
      BoundaryChartCoordinateCarrier.ofChartCoordinateImage
        (I := I) (K := K) (x := C.boundaryChart i.1) (omega := omega)
        (sourceSupport i) (hcompact i) (hsource i) (hSK i)
        (hhalf i) (hbase i))

/-- Global-support version of `ofSourceSupports`: every boundary carrier is
the image of the same compact support set in its own chart.  This is often too
strong for a final manifold theorem, but it is a convenient exact specialization
for local tests and single-chart compact supports. -/
def ofGlobalSupport
    (hcompact : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (hhalf :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        chartCoordinateImage I (C.boundaryChart i.1) K ⊆ upperHalfSpace n)
    (hbase :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1) omega) ⊆
          chartCoordinateImage I (C.boundaryChart i.1) K) :
    CoverIndexedBoundaryCarrierSelection C omega :=
  ofSourceSupports
    (C := C) (K := K) (omega := omega)
    (fun _ => K)
    (fun _ => hcompact)
    hsource
    (fun _ => Subset.refl K)
    hhalf
    hbase

/-- Add smoothness neighborhoods to a boundary carrier family and obtain the
boundary local-data package expected by the compact-support represented route. -/
def toBoundaryLocalData
    (D : CoverIndexedBoundaryCarrierSelection C omega)
    (neighborhood :
      {x : M // x ∈ C.boundaryCenters} ->
        Set (Fin (n + 1) -> Real))
    (neighborhood_open :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen (neighborhood i))
    (Icc_subset_neighborhood :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          neighborhood i)
    (neighborhood_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhood i ⊆
          (extChartAt I (C.boundaryChart i.1)).target) :
    CoverIndexedBoundaryLocalDataFromCompactSupport C P omega where
  coordSupport := D.coordSupport
  neighborhood := neighborhood
  coord_compact := D.coord_compact
  coord_subset_halfSpace := D.coord_subset_halfSpace
  base_tsupport_subset := D.base_tsupport_subset
  coord_mapsTo_support := D.coord_mapsTo_support
  coord_subset_target := D.coord_subset_target
  neighborhood_open := neighborhood_open
  Icc_subset_neighborhood := Icc_subset_neighborhood
  neighborhood_subset_target := neighborhood_subset_target

@[simp]
theorem toBoundaryLocalData_coordSupport
    (D : CoverIndexedBoundaryCarrierSelection C omega)
    (neighborhood :
      {x : M // x ∈ C.boundaryCenters} ->
        Set (Fin (n + 1) -> Real))
    (neighborhood_open :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen (neighborhood i))
    (Icc_subset_neighborhood :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          neighborhood i)
    (neighborhood_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhood i ⊆
          (extChartAt I (C.boundaryChart i.1)).target) :
    (D.toBoundaryLocalData
        (P := P) neighborhood neighborhood_open
        Icc_subset_neighborhood neighborhood_subset_target).coordSupport =
      D.coordSupport :=
  rfl

/-- Carrier families directly generate the boundary assigned-box fields once a
smoothness neighborhood family is supplied. -/
def assignedFields
    (D : CoverIndexedBoundaryCarrierSelection C omega)
    (neighborhood :
      {x : M // x ∈ C.boundaryCenters} ->
        Set (Fin (n + 1) -> Real))
    (neighborhood_open :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsOpen (neighborhood i))
    (Icc_subset_neighborhood :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          neighborhood i)
    (neighborhood_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        neighborhood i ⊆
          (extChartAt I (C.boundaryChart i.1)).target) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      SupportControlledSelectedPartition.BoundaryAssignedBoxCoordSupportFields
        P i omega (D.coordSupport i) (neighborhood i) :=
  (D.toBoundaryLocalData
      (P := P) neighborhood neighborhood_open
      Icc_subset_neighborhood neighborhood_subset_target).assignedFields

end CoverIndexedBoundaryCarrierSelection

end BoundaryCarrierSelection

end Stokes

end
