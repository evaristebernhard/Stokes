import Stokes.HalfSpace

/-!
# Interior chart boxes

This module starts the global/interior-chart API parallel to the boundary-chart
box-selection layer.  It intentionally records only the data needed by later
local Euclidean Stokes wrappers: a chart-overlap domain, a closed coordinate box
inside that domain, compact support inside the box, and optionally an ambient
open smoothness neighborhood.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section InteriorChart

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
The natural model-coordinate domain where the transition from an interior chart
`x0` to a comparison chart `x1` is meaningful: the `x0` chart target together
with the overlap with the `x1` chart source.
-/
def interiorChartDomain
    (I : ModelWithCorners Real E H) (x0 x1 : M) : Set E :=
  (extChartAt I x0).target ∩ ManifoldForm.chartOverlap I x0 x1

theorem interiorChartDomain_eq_chartTransitionSource
    (I : ModelWithCorners Real E H) (x0 x1 : M) :
    interiorChartDomain I x0 x1 =
      ManifoldForm.chartTransitionSource I x0 x1 := by
  rw [interiorChartDomain, ManifoldForm.chartTransitionSource_eq]

theorem interiorChartDomain_subset_target
    (I : ModelWithCorners Real E H) (x0 x1 : M) :
    interiorChartDomain I x0 x1 ⊆ (extChartAt I x0).target :=
  inter_subset_left

theorem interiorChartDomain_subset_overlap
    (I : ModelWithCorners Real E H) (x0 x1 : M) :
    interiorChartDomain I x0 x1 ⊆ ManifoldForm.chartOverlap I x0 x1 :=
  inter_subset_right

variable [Preorder E]

/--
A selected coordinate box for an interior chart transition.

It records the coordinate order on the closed box, the fact that the box lies
inside the natural chart-transition domain, and the compact-support condition
that later removes artificial box faces.
-/
def interiorChartSelectedBox
    (I : ModelWithCorners Real E H) (x0 x1 : M) (ω : ManifoldForm I M k)
    (a b : E) : Prop :=
  a ≤ b ∧ Set.Icc a b ⊆ interiorChartDomain I x0 x1 ∧
    tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ Set.Icc a b

theorem interiorChartSelectedBox.mk_of_subsets
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    {a b : E} (hle : a ≤ b)
    (htarget : Set.Icc a b ⊆ (extChartAt I x0).target)
    (hoverlap : Set.Icc a b ⊆ ManifoldForm.chartOverlap I x0 x1)
    (hsupp : tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      Set.Icc a b) :
    interiorChartSelectedBox I x0 x1 ω a b :=
  ⟨hle, fun _ hy => ⟨htarget hy, hoverlap hy⟩, hsupp⟩

theorem interiorChartSelectedBox.le
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    {a b : E} (hbox : interiorChartSelectedBox I x0 x1 ω a b) :
    a ≤ b :=
  hbox.1

theorem interiorChartSelectedBox.Icc_subset_domain
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    {a b : E} (hbox : interiorChartSelectedBox I x0 x1 ω a b) :
    Set.Icc a b ⊆ interiorChartDomain I x0 x1 :=
  hbox.2.1

theorem interiorChartSelectedBox.Icc_subset_target
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    {a b : E} (hbox : interiorChartSelectedBox I x0 x1 ω a b) :
    Set.Icc a b ⊆ (extChartAt I x0).target := fun _ hy =>
  interiorChartDomain_subset_target I x0 x1 (hbox.Icc_subset_domain hy)

theorem interiorChartSelectedBox.Icc_subset_overlap
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    {a b : E} (hbox : interiorChartSelectedBox I x0 x1 ω a b) :
    Set.Icc a b ⊆ ManifoldForm.chartOverlap I x0 x1 := fun _ hy =>
  interiorChartDomain_subset_overlap I x0 x1 (hbox.Icc_subset_domain hy)

theorem interiorChartSelectedBox.tsupport_subset
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    {a b : E} (hbox : interiorChartSelectedBox I x0 x1 ω a b) :
    tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ Set.Icc a b :=
  hbox.2.2

/--
A selected interior chart box together with an ambient open neighborhood on
which the transition-pullback representative is smooth.
-/
def interiorChartExtendedBox
    (I : ModelWithCorners Real E H) (x0 x1 : M) (ω : ManifoldForm I M k)
    (a b : E) : Prop :=
  interiorChartSelectedBox I x0 x1 ω a b ∧
    ∃ U : Set E,
      IsOpen U ∧ Set.Icc a b ⊆ U ∧
        ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U

theorem interiorChartExtendedBox.mk
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    {a b : E} (hselected : interiorChartSelectedBox I x0 x1 ω a b)
    {U : Set E} (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U)
    (hωU : ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    interiorChartExtendedBox I x0 x1 ω a b :=
  ⟨hselected, ⟨U, hU, hUbox, hωU⟩⟩

theorem interiorChartExtendedBox.mk_of_subsets
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    {a b : E} (hle : a ≤ b)
    (htarget : Set.Icc a b ⊆ (extChartAt I x0).target)
    (hoverlap : Set.Icc a b ⊆ ManifoldForm.chartOverlap I x0 x1)
    (hsupp : tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      Set.Icc a b)
    {U : Set E} (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U)
    (hωU : ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    interiorChartExtendedBox I x0 x1 ω a b :=
  interiorChartExtendedBox.mk
    (interiorChartSelectedBox.mk_of_subsets hle htarget hoverlap hsupp)
    hU hUbox hωU

theorem interiorChartExtendedBox.selectedBox
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    {a b : E} (hbox : interiorChartExtendedBox I x0 x1 ω a b) :
    interiorChartSelectedBox I x0 x1 ω a b :=
  hbox.1

theorem interiorChartExtendedBox.Icc_subset_domain
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    {a b : E} (hbox : interiorChartExtendedBox I x0 x1 ω a b) :
    Set.Icc a b ⊆ interiorChartDomain I x0 x1 :=
  hbox.selectedBox.Icc_subset_domain

theorem interiorChartExtendedBox.Icc_subset_target
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    {a b : E} (hbox : interiorChartExtendedBox I x0 x1 ω a b) :
    Set.Icc a b ⊆ (extChartAt I x0).target :=
  hbox.selectedBox.Icc_subset_target

theorem interiorChartExtendedBox.Icc_subset_overlap
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    {a b : E} (hbox : interiorChartExtendedBox I x0 x1 ω a b) :
    Set.Icc a b ⊆ ManifoldForm.chartOverlap I x0 x1 :=
  hbox.selectedBox.Icc_subset_overlap

theorem interiorChartExtendedBox.exists_smooth_nhds
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    {a b : E} (hbox : interiorChartExtendedBox I x0 x1 ω a b) :
    ∃ U : Set E,
      IsOpen U ∧ Set.Icc a b ⊆ U ∧
        ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U :=
  hbox.2

end InteriorChart

end Stokes

end
