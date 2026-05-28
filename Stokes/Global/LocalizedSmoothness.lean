import Stokes.Global.LocalizedSupport
import Stokes.Global.CompactActiveBoxes

/-!
# Smoothness bridges for localized manifold forms

This file supplies the analytic companion to `LocalizedSupport`: once the
transition coefficient and the base transition-pullback representative are
smooth on a coordinate neighborhood, the transition-pullback of the localized
form is smooth there as well.  The resulting package fills the smooth
neighborhood field required by `interiorChartExtendedBox`.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {k : Nat}

namespace ManifoldForm

variable (I : ModelWithCorners Real E H)

/--
Scalar multiplication preserves `ContDiffOn` for localized transition-pullback
representatives.
-/
theorem contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
    {x0 x1 : M} {ρ : M → Real} {ω : ManifoldForm I M k}
    {m : WithTop ℕ∞} {s : Set E}
    (hρ :
      ContDiffOn Real m (transitionCoefficientInChart I x0 x1 ρ) s)
    (hω :
      ContDiffOn Real m (transitionPullbackInChart I x0 x1 ω) s) :
    ContDiffOn Real m
      (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) s := by
  rw [transitionPullbackInChart_localizedForm]
  exact hρ.smul hω

/--
A smooth partition-of-unity coefficient is smooth when written in one extended
chart.
-/
theorem contDiffOn_coefficientInChart_smoothPartition [IsManifold I ⊤ M]
    (ρ : SmoothPartitionOfUnity M I M univ) (x0 i : M) {s : Set E}
    (hs : s ⊆ (extChartAt I x0).target) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (coefficientInChart I x0 (ρ i)) s := by
  have hsymm :
      ContMDiffOn 𝓘(Real, E) I ((⊤ : ℕ∞) : WithTop ℕ∞)
        (extChartAt I x0).symm s :=
    (contMDiffOn_extChartAt_symm
      (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) x0).mono hs
  have hcomp :
      ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        ((ρ i) ∘ (extChartAt I x0).symm) s :=
    ContMDiff.comp_contMDiffOn
      (I := 𝓘(Real, E)) (I' := I) (I'' := 𝓘(Real, Real))
      (f := (extChartAt I x0).symm) (g := ρ i)
      ((ρ i).contMDiff) hsymm
  simpa [coefficientInChart, Function.comp_def] using hcomp.contDiffOn

/--
A smooth partition-of-unity coefficient remains smooth in transition
coordinates on a chart-overlap set.
-/
theorem contDiffOn_transitionCoefficientInChart_smoothPartition [IsManifold I ⊤ M]
    (ρ : SmoothPartitionOfUnity M I M univ) (x0 x1 i : M) {s : Set E}
    (hstarget : s ⊆ (extChartAt I x0).target)
    (hsoverlap : s ⊆ chartOverlap I x0 x1) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (transitionCoefficientInChart I x0 x1 (ρ i)) s := by
  exact
    (contDiffOn_coefficientInChart_smoothPartition (I := I) ρ x0 i hstarget).congr
      (fun y hy =>
        transitionCoefficientInChart_eq_coefficientInChart_of_mem_overlap
          (I := I) (ρ := ρ i) (y := y) (hsoverlap hy))

end ManifoldForm

section LocalizedSmoothness

/--
Smoothness data for one localized chart representative.

The first two fields are the reusable hypotheses: the scalar coefficient written
in transition coordinates is smooth, and the base form's transition-pullback is
smooth.  The final field is the localized representative smoothness obtained
from the scalar-multiplication bridge above.
-/
structure LocalizedSmoothnessData
    (I : ModelWithCorners Real E H) (x0 x1 : M)
    (ρ : M → Real) (ω : ManifoldForm I M k) (U : Set E) where
  /-- Smoothness of the localized scalar coefficient in transition coordinates. -/
  coefficient_contDiffOn :
    ContDiffOn Real ⊤ (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) U
  /-- Smoothness of the base form's transition-pullback representative. -/
  base_contDiffOn :
    ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U
  /-- Smoothness of the localized form's transition-pullback representative. -/
  localized_contDiffOn :
    ContDiffOn Real ⊤
      (ManifoldForm.transitionPullbackInChart I x0 x1
        (ManifoldForm.localizedForm I ρ ω)) U

namespace LocalizedSmoothnessData

variable {I : ModelWithCorners Real E H} {x0 x1 : M}
variable {ρ : M → Real} {ω : ManifoldForm I M k} {U : Set E}

/--
Build localized smoothness data from smoothness of the coefficient and the base
transition-pullback representative.
-/
def ofContDiffOn
    (hρ :
      ContDiffOn Real ⊤ (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) U)
    (hω :
      ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    LocalizedSmoothnessData I x0 x1 ρ ω U where
  coefficient_contDiffOn := hρ
  base_contDiffOn := hω
  localized_contDiffOn :=
    ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
      (I := I) hρ hω

/--
Build localized smoothness data from a chartwise-smooth base form and a smooth
transition coefficient on a set contained in the relevant chart domain.
-/
def ofChartwiseSmooth [IsManifold I ⊤ M]
    (hρ :
      ContDiffOn Real ⊤ (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) U)
    (hω : ManifoldForm.ChartwiseSmooth I ω)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I x0 x1) :
    LocalizedSmoothnessData I x0 x1 ρ ω U :=
  ofContDiffOn hρ
    (hω.contDiffOn_transitionPullbackInChart_of_chartAPI
      (I := I) x0 x1 hUtarget hUoverlap)

variable [Preorder E]

/--
The existential smooth-neighborhood witness required by
`interiorChartExtendedBox`.
-/
theorem smoothNeighborhood {a b : E}
    (D : LocalizedSmoothnessData I x0 x1 ρ ω U)
    (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U) :
    ∃ V : Set E,
      IsOpen V ∧ Set.Icc a b ⊆ V ∧
        ContDiffOn Real ⊤
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω)) V :=
  ⟨U, hU, hUbox, D.localized_contDiffOn⟩

/--
Combine coefficient support control and localized smoothness data into the
extended interior chart box for the canonical localized form.
-/
theorem interiorChartExtendedBox
    {a b : E}
    (C : LocalizedSupportControl I x0 x1 ρ ω a b)
    (D : LocalizedSmoothnessData I x0 x1 ρ ω U)
    (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U) :
    Stokes.interiorChartExtendedBox I x0 x1
      (ManifoldForm.localizedForm I ρ ω) a b :=
  Stokes.interiorChartExtendedBox.mk C.interiorChartSelectedBox hU hUbox
    D.localized_contDiffOn

/--
Chartwise-smooth version: a smooth transition coefficient and a chartwise-smooth
base form provide the smoothness field of the localized extended box.
-/
theorem interiorChartExtendedBox_of_chartwiseSmooth [IsManifold I ⊤ M]
    {a b : E}
    (C : LocalizedSupportControl I x0 x1 ρ ω a b)
    (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U)
    (hρ :
      ContDiffOn Real ⊤ (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) U)
    (hω : ManifoldForm.ChartwiseSmooth I ω)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I x0 x1) :
    Stokes.interiorChartExtendedBox I x0 x1
      (ManifoldForm.localizedForm I ρ ω) a b :=
  interiorChartExtendedBox C
    (ofChartwiseSmooth hρ hω hUtarget hUoverlap) hU hUbox

end LocalizedSmoothnessData

end LocalizedSmoothness

namespace SelectedBoxPartitionOfUnity

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/--
Partition-localized chart representatives are smooth at the project-local
`⊤` level once the corresponding transition coefficient is smooth at that
level.  This is the shape consumed by current local-Stokes fields.
-/
theorem contDiffOn_transitionPullbackInChart_localizedForm_of_coefficient
    [IsManifold I ⊤ M]
    (P : SelectedBoxPartitionOfUnity I ω)
    (hω : ManifoldForm.ChartwiseSmooth I ω)
    {i : M} (_hi : i ∈ P.active) {U : Set (Fin (n + 1) → Real)}
    (hρU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I i i (P.partition i)) U)
    (hUtarget : U ⊆ (extChartAt I i).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I i i) :
    ContDiffOn Real ⊤
      (ManifoldForm.transitionPullbackInChart I i i
        (ManifoldForm.localizedForm I (P.partition i) ω)) U := by
  exact
    ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
      (I := I)
      hρU
      (hω.contDiffOn_transitionPullbackInChart_of_chartAPI
        (I := I) i i hUtarget hUoverlap)

/--
Automatic `C∞` version from the smoothness carried by mathlib's
`SmoothPartitionOfUnity`.  This is the mathematically natural partition
smoothness statement; note that `SmoothPartitionOfUnity` provides `↑∞`, while
some current local-Stokes fields still ask for the stronger project-local `⊤`.
-/
theorem contDiffOn_infty_transitionPullbackInChart_localizedForm [IsManifold I ⊤ M]
    (P : SelectedBoxPartitionOfUnity I ω)
    (hω : ManifoldForm.ChartwiseSmooth I ω)
    {i : M} (_hi : i ∈ P.active) {U : Set (Fin (n + 1) → Real)}
    (hUtarget : U ⊆ (extChartAt I i).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I i i) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.transitionPullbackInChart I i i
        (ManifoldForm.localizedForm I (P.partition i) ω)) U := by
  exact
    ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
      (I := I)
      (ManifoldForm.contDiffOn_transitionCoefficientInChart_smoothPartition
        (I := I) P.partition i i i hUtarget hUoverlap)
      ((hω.contDiffOn_transitionPullbackInChart_of_chartAPI
        (I := I) i i hUtarget hUoverlap).of_le le_top)

/--
Open-neighborhood wrapper for the current local-Stokes field shape.
-/
theorem contDiffOn_transitionPullbackInChart_localizedForm_of_isOpen
    [IsManifold I ⊤ M]
    (P : SelectedBoxPartitionOfUnity I ω)
    (hω : ManifoldForm.ChartwiseSmooth I ω)
    {i : M} (hi : i ∈ P.active) {U : Set (Fin (n + 1) → Real)}
    (_hU : IsOpen U)
    (hρU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I i i (P.partition i)) U)
    (hUtarget : U ⊆ (extChartAt I i).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I i i) :
    ContDiffOn Real ⊤
      (ManifoldForm.transitionPullbackInChart I i i
        (ManifoldForm.localizedForm I (P.partition i) ω)) U :=
  P.contDiffOn_transitionPullbackInChart_localizedForm_of_coefficient hω hi
    hρU hUtarget hUoverlap

end SelectedBoxPartitionOfUnity

namespace CompactActiveExtendedBoxData

variable [Preorder E]
variable {I : ModelWithCorners Real E H}
variable {ω : ManifoldForm I M k}

/--
The smoothness field for a compact active extended box transports to the
partition-localized representative once the corresponding transition
coefficient is smooth on the same recorded neighborhood.
-/
theorem contDiffOn_smoothSet_localizedForm_of_coefficient
    (D : CompactActiveExtendedBoxData I ω)
    {i : M} (hi : i ∈ D.boxData.finiteActive.active)
    (hρU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I i i
          (D.boxData.finiteActive.partition i)) (D.smoothSet i)) :
    ContDiffOn Real ⊤
      (ManifoldForm.transitionPullbackInChart I i i
        (ManifoldForm.localizedForm I
          (D.boxData.finiteActive.partition i) ω)) (D.smoothSet i) :=
  ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
    (I := I) hρU (D.contDiffOn_smoothSet i hi)

/--
Selected-partition phrasing of
`contDiffOn_smoothSet_localizedForm_of_coefficient` for the selected partition
canonically exposed by compact active extended boxes.
-/
theorem contDiffOn_smoothSet_selectedLocalizedForm_of_coefficient
    (D : CompactActiveExtendedBoxData I ω)
    {i : M} (hi : i ∈ D.toSelectedBoxPartitionOfUnity.active)
    (hρU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I i i
          (D.toSelectedBoxPartitionOfUnity.partition i)) (D.smoothSet i)) :
    ContDiffOn Real ⊤
      (ManifoldForm.transitionPullbackInChart I i i
        (ManifoldForm.localizedForm I
          (D.toSelectedBoxPartitionOfUnity.partition i) ω)) (D.smoothSet i) := by
  exact D.contDiffOn_smoothSet_localizedForm_of_coefficient
    (by simpa using hi) (by simpa using hρU)

end CompactActiveExtendedBoxData

end Stokes

end
