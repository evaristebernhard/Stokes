import Stokes.Global.CoverIndexedLocalDataFromCompactSupport
import Stokes.Global.ChartCompactImage

/-!
# Interior coordinate carriers from compact support

This file isolates the interior carrier-selection step used by
`CoverIndexedInteriorLocalDataFromCompactSupport`.

For an interior chart-box cover piece the natural coordinate carrier is the
image of the compact manifold-side support set in that chart:

`chartCoordinateImage I (C.interiorChart i) K`.

With this choice, the easy geometric carrier fields are automatic:

* the carrier is compact;
* it lies in the extended-chart target;
* its inverse image under the chart lies back in `K`.

The remaining genuine analytic input is exactly the expected one: the base
chart representative has topological support contained in that coordinate
image.  The final constructor below packages these carrier facts into the
interior local-data record, leaving only the already-separate smooth
neighborhood fields explicit.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section InteriorCarrierSelection

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {omega : ManifoldForm I M n}

/-- If the ordinary support is contained in a closed set, so is `tsupport`. -/
theorem interiorCarrier_tsupport_subset_of_support_subset_isClosed
    {X : Type*} [TopologicalSpace X] {A : Type*} [Zero A]
    {f : X -> A} {s : Set X}
    (hsclosed : IsClosed s) (hsupport : Function.support f ⊆ s) :
    tsupport f ⊆ s := by
  simpa [tsupport] using closure_minimal hsupport hsclosed

/--
Pointwise chart-image support bridge.

If all nonzero points of a model-space function lie in the chart target and
the inverse-chart point lies in `K`, then the ordinary support is contained in
the coordinate image of `K`.
-/
theorem support_subset_chartCoordinateImage_of_support_subset_target_mapsTo
    {A : Type*} [Zero A] {x : M} {f : (Fin (n + 1) -> Real) -> A}
    (htarget : Function.support f ⊆ (extChartAt I x).target)
    (hpreimage :
      ∀ y ∈ (extChartAt I x).target,
        f y ≠ 0 -> (extChartAt I x).symm y ∈ K) :
    Function.support f ⊆ chartCoordinateImage I x K := by
  intro y hy
  have hytarget : y ∈ (extChartAt I x).target := htarget hy
  refine ⟨(extChartAt I x).symm y, hpreimage y hytarget ?_, ?_⟩
  · simpa [Function.mem_support] using hy
  · exact (extChartAt I x).right_inv hytarget

/--
Topological support version of
`support_subset_chartCoordinateImage_of_support_subset_target_mapsTo`.
-/
theorem tsupport_subset_chartCoordinateImage_of_support_subset_target_mapsTo
    {A : Type*} [Zero A] {x : M} {f : (Fin (n + 1) -> Real) -> A}
    (hK : IsCompact K)
    (hsource : K ⊆ (extChartAt I x).source)
    (htarget : Function.support f ⊆ (extChartAt I x).target)
    (hpreimage :
      ∀ y ∈ (extChartAt I x).target,
        f y ≠ 0 -> (extChartAt I x).symm y ∈ K) :
    tsupport f ⊆ chartCoordinateImage I x K := by
  exact
    interiorCarrier_tsupport_subset_of_support_subset_isClosed
      (isCompact_chartCoordinateImage_of_subset_source
        (I := I) (x := x) hK hsource |>.isClosed)
      (support_subset_chartCoordinateImage_of_support_subset_target_mapsTo
        (I := I) (K := K) htarget hpreimage)

/--
Interior carrier data obtained by using the compact support set itself as the
manifold-side source before passing to chart coordinates.

The field `base_tsupport_subset_chartCoordinateImage` is intentionally the
only nontrivial support input: it is the statement that the base chart
representative is actually carried by the chosen compact-support coordinate
image.
-/
structure CoverIndexedInteriorCarrierSelection
    (C : CompactSupportChartCoverSelection I K)
    (omega : ManifoldForm I M n) where
  /-- The manifold-side support set is compact. -/
  support_isCompact : IsCompact K
  /-- Every selected interior support set lies in the selected chart source. -/
  support_subset_chart_source :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      K ⊆ (extChartAt I (C.interiorChart i.1)).source
  /-- The base chart representative is supported in the compact coordinate image. -/
  base_tsupport_subset_chartCoordinateImage :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.interiorChart i.1) (C.interiorChart i.1) omega) ⊆
        chartCoordinateImage I (C.interiorChart i.1) K

namespace CoverIndexedInteriorCarrierSelection

/-- The generated coordinate carrier for an interior cover piece. -/
def coordSupport (_D : CoverIndexedInteriorCarrierSelection C omega) :
    {x : M // x ∈ C.interiorCenters} ->
      Set (Fin (n + 1) -> Real) :=
  fun i => chartCoordinateImage I (C.interiorChart i.1) K

/-- The generated coordinate carrier is compact. -/
theorem coord_compact
    (D : CoverIndexedInteriorCarrierSelection C omega)
    (i : {x : M // x ∈ C.interiorCenters}) :
    IsCompact (coordSupport D i) := by
  exact
    isCompact_chartCoordinateImage_of_subset_source
      (I := I) (x := C.interiorChart i.1)
      D.support_isCompact (D.support_subset_chart_source i)

/-- The base chart representative is supported in the generated carrier. -/
theorem base_tsupport_subset
    (D : CoverIndexedInteriorCarrierSelection C omega)
    (i : {x : M // x ∈ C.interiorCenters}) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (C.interiorChart i.1) (C.interiorChart i.1) omega) ⊆
      coordSupport D i :=
  D.base_tsupport_subset_chartCoordinateImage i

/-- Generated carriers map back to the compact support set. -/
theorem coord_mapsTo_support
    (D : CoverIndexedInteriorCarrierSelection C omega)
    (i : {x : M // x ∈ C.interiorCenters}) :
    ∀ y ∈ coordSupport D i,
      (extChartAt I (C.interiorChart i.1)).symm y ∈ K := by
  rintro y ⟨p, hpK, rfl⟩
  have hsource : p ∈ (extChartAt I (C.interiorChart i.1)).source :=
    D.support_subset_chart_source i hpK
  rw [(extChartAt I (C.interiorChart i.1)).left_inv hsource]
  exact hpK

/-- Generated carriers lie in the selected chart target. -/
theorem coord_subset_target
    (D : CoverIndexedInteriorCarrierSelection C omega)
    (i : {x : M // x ∈ C.interiorCenters}) :
    coordSupport D i ⊆
      (extChartAt I (C.interiorChart i.1)).target := by
  rintro y ⟨p, hpK, rfl⟩
  exact
    (extChartAt I (C.interiorChart i.1)).map_source
      (D.support_subset_chart_source i hpK)

/--
Constructor for `CoverIndexedInteriorCarrierSelection` from pointwise
support-in-chart facts.

This reduces the `tsupport` field to two lower-level obligations for each
interior chart representative:

* its ordinary support is inside the chart target;
* every nonzero target point maps back into `K`.
-/
def ofSupportTargetMapsTo
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
    (hpreimage :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        ∀ y ∈ (extChartAt I (C.interiorChart i.1)).target,
          ManifoldForm.transitionPullbackInChart I
              (C.interiorChart i.1) (C.interiorChart i.1) omega y ≠ 0 ->
            (extChartAt I (C.interiorChart i.1)).symm y ∈ K) :
    CoverIndexedInteriorCarrierSelection C omega where
  support_isCompact := hK
  support_subset_chart_source := hsource
  base_tsupport_subset_chartCoordinateImage := by
    intro i
    exact
      tsupport_subset_chartCoordinateImage_of_support_subset_target_mapsTo
        (I := I) (K := K) hK (hsource i) (htarget i) (hpreimage i)

/--
Fill the carrier fields of `CoverIndexedInteriorLocalDataFromCompactSupport`.

The remaining arguments are precisely the non-carrier fields of that record:
the smoothness neighborhood and the current legacy `ContDiffOn Real ⊤`
localized smoothness input.
-/
def toLocalData
    (D : CoverIndexedInteriorCarrierSelection C omega)
    (neighborhood :
      {x : M // x ∈ C.interiorCenters} ->
        Set (Fin (n + 1) -> Real))
    (neighborhood_open :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        IsOpen (neighborhood i))
    (Icc_subset_neighborhood :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        Set.Icc (C.interiorLower i.1) (C.interiorUpper i.1) ⊆
          neighborhood i)
    (neighborhood_subset_target :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        neighborhood i ⊆
          (extChartAt I (C.interiorChart i.1)).target)
    (localized_contDiffOn_top :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        ContDiffOn Real ⊤
          (ManifoldForm.transitionPullbackInChart I
            (C.interiorChart i.1) (C.interiorChart i.1)
            (P.coverIndexLocalizedForm omega (Sum.inl i)))
          (neighborhood i)) :
    CoverIndexedInteriorLocalDataFromCompactSupport C P omega where
  coordSupport := coordSupport D
  neighborhood := neighborhood
  base_tsupport_subset := base_tsupport_subset D
  coord_mapsTo_support := coord_mapsTo_support D
  coord_subset_target := coord_subset_target D
  neighborhood_open := neighborhood_open
  Icc_subset_neighborhood := Icc_subset_neighborhood
  neighborhood_subset_target := neighborhood_subset_target
  localized_contDiffOn_top := localized_contDiffOn_top

@[simp]
theorem toLocalData_coordSupport
    (D : CoverIndexedInteriorCarrierSelection C omega)
    (neighborhood :
      {x : M // x ∈ C.interiorCenters} ->
        Set (Fin (n + 1) -> Real))
    (neighborhood_open :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        IsOpen (neighborhood i))
    (Icc_subset_neighborhood :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        Set.Icc (C.interiorLower i.1) (C.interiorUpper i.1) ⊆
          neighborhood i)
    (neighborhood_subset_target :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        neighborhood i ⊆
          (extChartAt I (C.interiorChart i.1)).target)
    (localized_contDiffOn_top :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        ContDiffOn Real ⊤
          (ManifoldForm.transitionPullbackInChart I
            (C.interiorChart i.1) (C.interiorChart i.1)
            (P.coverIndexLocalizedForm omega (Sum.inl i)))
          (neighborhood i)) :
    (toLocalData (P := P) D neighborhood neighborhood_open
      Icc_subset_neighborhood neighborhood_subset_target
      localized_contDiffOn_top).coordSupport =
      coordSupport D :=
  rfl

end CoverIndexedInteriorCarrierSelection

end InteriorCarrierSelection

end Stokes

end
