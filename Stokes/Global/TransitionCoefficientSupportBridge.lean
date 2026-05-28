import Stokes.Global.SupportControlledSelectedPartition

/-!
# Support bridge for transition coefficients in charts

This file supplies the missing chart-coordinate support bridge for
`ManifoldForm.transitionCoefficientInChart`.  The key point is not specific to
interior or boundary boxes: on the chart-transition source, topological support
of the coordinate coefficient maps back to topological support of the original
manifold-side coefficient.  The final wrappers specialize this common bridge to
the strict interior support box and the half-space support box.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

namespace ManifoldForm

section TransitionCoefficientSupport

variable {x0 x1 : M} {ρ : M → Real}

/--
Algebraic support of a transition coefficient is contained in the preimage of
the algebraic support of the original manifold-side coefficient.
-/
theorem transitionCoefficientInChart_support_subset_preimage :
    Function.support (transitionCoefficientInChart I x0 x1 ρ) ⊆
      (fun y : Fin (n + 1) → Real =>
        (extChartAt I x1).symm (chartTransition I x0 x1 y)) ⁻¹'
        Function.support ρ := by
  intro y hy
  simpa [transitionCoefficientInChart] using hy

/--
On the concrete chart-transition source, algebraic support of the transition
coefficient maps back to algebraic support of the original coefficient in the
source chart.
-/
theorem transitionCoefficientInChart_support_mapsTo_support
    {y : Fin (n + 1) → Real}
    (_hytarget : y ∈ (extChartAt I x0).target)
    (hyoverlap : y ∈ chartOverlap I x0 x1)
    (hy :
      y ∈ Function.support (transitionCoefficientInChart I x0 x1 ρ)) :
    (extChartAt I x0).symm y ∈ Function.support ρ := by
  have hpre :
      (extChartAt I x1).symm (chartTransition I x0 x1 y) ∈
        Function.support ρ :=
    transitionCoefficientInChart_support_subset_preimage (I := I)
      (x0 := x0) (x1 := x1) (ρ := ρ) hy
  have hleft :
      (extChartAt I x1).symm (chartTransition I x0 x1 y) =
        (extChartAt I x0).symm y := by
    simpa [chartTransition] using (extChartAt I x1).left_inv hyoverlap
  rw [hleft] at hpre
  exact hpre

/--
Self-transition algebraic support bridge.  This is the form used by the
assigned-box local Stokes pipeline.
-/
theorem transitionCoefficientInChart_self_support_mapsTo_support
    {x : M} {ρ : M → Real} {y : Fin (n + 1) → Real}
    (hytarget : y ∈ (extChartAt I x).target)
    (hy :
      y ∈ Function.support (transitionCoefficientInChart I x x ρ)) :
    (extChartAt I x).symm y ∈ Function.support ρ := by
  exact transitionCoefficientInChart_support_mapsTo_support
    (I := I) (x0 := x) (x1 := x) (ρ := ρ)
    hytarget ((extChartAt I x).map_target hytarget) hy

/--
The coordinate map hidden in `transitionCoefficientInChart` is continuous at
points of the chart-transition source.
-/
theorem continuousAt_transitionCoefficientInChart_coordMap
    {y : Fin (n + 1) → Real}
    (hytarget : y ∈ (extChartAt I x0).target)
    (hyoverlap : y ∈ chartOverlap I x0 x1) :
    ContinuousAt
      (fun z : Fin (n + 1) → Real =>
        (extChartAt I x1).symm (chartTransition I x0 x1 z)) y := by
  have hsymm0 :
      ContinuousAt (extChartAt I x0).symm y :=
    continuousAt_extChartAt_symm'' (I := I) hytarget
  have hchart1 :
      ContinuousAt (extChartAt I x1) ((extChartAt I x0).symm y) :=
    continuousAt_extChartAt' (I := I) hyoverlap
  have htransition :
      ContinuousAt (chartTransition I x0 x1) y := by
    simpa [chartTransition] using hchart1.comp hsymm0
  have htransition_target :
      chartTransition I x0 x1 y ∈ (extChartAt I x1).target := by
    simpa [chartTransition] using (extChartAt I x1).map_source hyoverlap
  have hsymm1 :
      ContinuousAt (extChartAt I x1).symm (chartTransition I x0 x1 y) :=
    continuousAt_extChartAt_symm'' (I := I) htransition_target
  exact hsymm1.comp htransition

/--
On the chart-transition source, topological support of the transition
coefficient maps back to topological support of the original manifold-side
coefficient.
-/
theorem transitionCoefficientInChart_tsupport_mapsTo_tsupport
    {y : Fin (n + 1) → Real}
    (hytarget : y ∈ (extChartAt I x0).target)
    (hyoverlap : y ∈ chartOverlap I x0 x1)
    (hy :
      y ∈ tsupport (transitionCoefficientInChart I x0 x1 ρ)) :
    (extChartAt I x0).symm y ∈ tsupport ρ := by
  by_contra hnot
  have hcoord :
      ContinuousAt
        (fun z : Fin (n + 1) → Real =>
          (extChartAt I x1).symm (chartTransition I x0 x1 z)) y :=
    continuousAt_transitionCoefficientInChart_coordMap
      (I := I) (x0 := x0) (x1 := x1) hytarget hyoverlap
  have hleft :
      (extChartAt I x1).symm (chartTransition I x0 x1 y) =
        (extChartAt I x0).symm y := by
    simpa [chartTransition] using (extChartAt I x1).left_inv hyoverlap
  have hnot' :
      (extChartAt I x1).symm (chartTransition I x0 x1 y) ∉
        tsupport ρ := by
    rw [hleft]
    exact hnot
  have hρzero :
      ρ =ᶠ[𝓝 ((extChartAt I x1).symm (chartTransition I x0 x1 y))]
        fun _ => (0 : Real) :=
    notMem_tsupport_iff_eventuallyEq.mp hnot'
  have hcoefzero :
      transitionCoefficientInChart I x0 x1 ρ =ᶠ[𝓝 y]
        fun _ => (0 : Real) := by
    filter_upwards [hcoord.tendsto.eventually hρzero] with z hz
    simpa [transitionCoefficientInChart] using hz
  exact (notMem_tsupport_iff_eventuallyEq.mpr hcoefzero) hy

/--
Self-transition topological support bridge.  For a coordinate point in the
chart target, support of `transitionCoefficientInChart I x x ρ` maps back by
`(extChartAt I x).symm` into `tsupport ρ`.
-/
theorem transitionCoefficientInChart_self_tsupport_mapsTo_tsupport
    {x : M} {ρ : M → Real} {y : Fin (n + 1) → Real}
    (hytarget : y ∈ (extChartAt I x).target)
    (hy :
      y ∈ tsupport (transitionCoefficientInChart I x x ρ)) :
    (extChartAt I x).symm y ∈ tsupport ρ := by
  exact transitionCoefficientInChart_tsupport_mapsTo_tsupport
    (I := I) (x0 := x) (x1 := x) (ρ := ρ)
    hytarget ((extChartAt I x).map_target hytarget) hy

end TransitionCoefficientSupport

end ManifoldForm

section CoordinateBridge

variable {K : Set M}
variable {x : M} {ρ : M → Real}
variable {coordSupport box : Set (Fin (n + 1) → Real)}
variable {chartBoxNeighborhood : Set M}

/--
General coordinate support bridge with an arbitrary coordinate box.

If the coordinate carrier maps back into `K`, lies in the chart target, and the
manifold-side coefficient is supported on `K` inside a chart-box neighborhood,
then the chart-coordinate transition coefficient is supported in the assigned
coordinate box on that carrier.
-/
theorem transitionCoefficientInChart_self_tsupport_inter_coordSupport_subset_box
    (hcoordK :
      ∀ y ∈ coordSupport, (extChartAt I x).symm y ∈ K)
    (hcoordTarget : coordSupport ⊆ (extChartAt I x).target)
    (hρ :
      tsupport ρ ∩ K ⊆ chartBoxNeighborhood)
    (hbox :
      chartBoxNeighborhood ⊆
        {p | p ∈ (extChartAt I x).source ∧ (extChartAt I x) p ∈ box}) :
    tsupport (ManifoldForm.transitionCoefficientInChart I x x ρ) ∩
        coordSupport ⊆
      box := by
  rintro y ⟨hycoeff, hycoord⟩
  have hρsupp :
      (extChartAt I x).symm y ∈ tsupport ρ :=
    ManifoldForm.transitionCoefficientInChart_self_tsupport_mapsTo_tsupport
      (I := I) (x := x) (ρ := ρ) (y := y)
      (hcoordTarget hycoord) hycoeff
  have hmanifold :
      (extChartAt I x).symm y ∈ chartBoxNeighborhood :=
    hρ ⟨hρsupp, hcoordK y hycoord⟩
  have hboxmem :
      (extChartAt I x) ((extChartAt I x).symm y) ∈ box :=
    (hbox hmanifold).2
  rwa [(extChartAt I x).right_inv (hcoordTarget hycoord)] at hboxmem

/--
Interior wrapper for the general coordinate bridge.
-/
theorem transitionCoefficientInChart_self_tsupport_inter_coordSupport_subset_interiorBox
    {a b : Fin (n + 1) → Real}
    (hcoordK :
      ∀ y ∈ coordSupport, (extChartAt I x).symm y ∈ K)
    (hcoordTarget : coordSupport ⊆ (extChartAt I x).target)
    (hρ :
      tsupport ρ ∩ K ⊆ interiorChartBoxNeighborhood I x a b) :
    tsupport (ManifoldForm.transitionCoefficientInChart I x x ρ) ∩
        coordSupport ⊆
      boxInteriorSupportBox a b := by
  exact
    transitionCoefficientInChart_self_tsupport_inter_coordSupport_subset_box
      (I := I) (K := K) (x := x) (ρ := ρ)
      (coordSupport := coordSupport)
      (box := boxInteriorSupportBox a b)
      (chartBoxNeighborhood := interiorChartBoxNeighborhood I x a b)
      hcoordK hcoordTarget hρ (by
        intro p hp
        simpa [interiorChartBoxNeighborhood] using hp)

/--
Boundary wrapper for the general coordinate bridge.
-/
theorem transitionCoefficientInChart_self_tsupport_inter_coordSupport_subset_halfSpaceBox
    {a b : Fin (n + 1) → Real}
    (hcoordK :
      ∀ y ∈ coordSupport, (extChartAt I x).symm y ∈ K)
    (hcoordTarget : coordSupport ⊆ (extChartAt I x).target)
    (hρ :
      tsupport ρ ∩ K ⊆ boundaryChartBoxNeighborhood I x a b) :
    tsupport (ManifoldForm.transitionCoefficientInChart I x x ρ) ∩
        coordSupport ⊆
      halfSpaceSupportBox a b := by
  exact
    transitionCoefficientInChart_self_tsupport_inter_coordSupport_subset_box
      (I := I) (K := K) (x := x) (ρ := ρ)
      (coordSupport := coordSupport)
      (box := halfSpaceSupportBox a b)
      (chartBoxNeighborhood := boundaryChartBoxNeighborhood I x a b)
      hcoordK hcoordTarget hρ (by
        intro p hp
        simpa [boundaryChartBoxNeighborhood] using hp)

end CoordinateBridge

section SelectedPartitionWrappers

variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}

namespace SupportControlledSelectedPartition

/--
Selected-cover version of the generalized bridge for an arbitrary mixed cover
index.
-/
theorem transitionCoefficient_inter_coordSupport_subset_assignedCoordinateBox'
    (P : SupportControlledSelectedPartition C)
    (j : C.CoverIndex) {coordSupport : Set (Fin (n + 1) → Real)}
    (hcoordK :
      ∀ y ∈ coordSupport,
        (extChartAt I (C.assignedChart j)).symm y ∈ K)
    (hcoordTarget :
      coordSupport ⊆ (extChartAt I (C.assignedChart j)).target) :
    tsupport
          (ManifoldForm.transitionCoefficientInChart I
            (C.assignedChart j) (C.assignedChart j) (P.partition j)) ∩
        coordSupport ⊆
      C.assignedCoordinateBox j := by
  rcases j with i | i
  · simpa [CompactSupportChartCoverSelection.assignedChart,
      CompactSupportChartCoverSelection.assignedCoordinateBox,
      CompactSupportChartCoverSelection.assignedCoverSet] using
      transitionCoefficientInChart_self_tsupport_inter_coordSupport_subset_interiorBox
        (I := I) (K := K) (x := C.interiorChart i.1)
        (ρ := P.partition (Sum.inl i)) (coordSupport := coordSupport)
        (a := C.interiorLower i.1) (b := C.interiorUpper i.1)
        hcoordK hcoordTarget
        (by
          simpa [CompactSupportChartCoverSelection.assignedCoverSet] using
            P.tsupport_inter_subset_assigned (Sum.inl i))
  · simpa [CompactSupportChartCoverSelection.assignedChart,
      CompactSupportChartCoverSelection.assignedCoordinateBox,
      CompactSupportChartCoverSelection.assignedCoverSet] using
      transitionCoefficientInChart_self_tsupport_inter_coordSupport_subset_halfSpaceBox
        (I := I) (K := K) (x := C.boundaryChart i.1)
        (ρ := P.partition (Sum.inr i)) (coordSupport := coordSupport)
        (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
        hcoordK hcoordTarget
        (by
          simpa [CompactSupportChartCoverSelection.assignedCoverSet] using
            P.tsupport_inter_subset_assigned (Sum.inr i))

/--
Interior selected-cover wrapper in the exact assigned-box shape.
-/
theorem interior_transitionCoefficient_inter_coordSupport_subset_box'
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.interiorCenters})
    {coordSupport : Set (Fin (n + 1) → Real)}
    (hcoordK :
      ∀ y ∈ coordSupport,
        (extChartAt I (C.interiorChart i.1)).symm y ∈ K)
    (hcoordTarget :
      coordSupport ⊆ (extChartAt I (C.interiorChart i.1)).target) :
    tsupport
          (ManifoldForm.transitionCoefficientInChart I
            (C.interiorChart i.1) (C.interiorChart i.1)
            (P.partition (Sum.inl i))) ∩
        coordSupport ⊆
      boxInteriorSupportBox (C.interiorLower i.1) (C.interiorUpper i.1) := by
  simpa [CompactSupportChartCoverSelection.assignedChart,
    CompactSupportChartCoverSelection.assignedCoordinateBox] using
    P.transitionCoefficient_inter_coordSupport_subset_assignedCoordinateBox'
      (j := Sum.inl i) hcoordK hcoordTarget

/--
Boundary selected-cover wrapper in the exact assigned-box shape.
-/
theorem boundary_transitionCoefficient_inter_coordSupport_subset_box'
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters})
    {coordSupport : Set (Fin (n + 1) → Real)}
    (hcoordK :
      ∀ y ∈ coordSupport,
        (extChartAt I (C.boundaryChart i.1)).symm y ∈ K)
    (hcoordTarget :
      coordSupport ⊆ (extChartAt I (C.boundaryChart i.1)).target) :
    tsupport
          (ManifoldForm.transitionCoefficientInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1)
            (P.partition (Sum.inr i))) ∩
        coordSupport ⊆
      halfSpaceSupportBox (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  simpa [CompactSupportChartCoverSelection.assignedChart,
    CompactSupportChartCoverSelection.assignedCoordinateBox] using
    P.transitionCoefficient_inter_coordSupport_subset_assignedCoordinateBox'
      (j := Sum.inr i) hcoordK hcoordTarget

end SupportControlledSelectedPartition

end SelectedPartitionWrappers

end Stokes

end
