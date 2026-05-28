import Stokes.BoundaryChart.BoundaryAssignedBoxSupport
import Stokes.Global.LocalIntegral
import Stokes.HalfSpace.BoxInteriorStokes

/-!
# Relative-source wrappers for boundary finite-box local Stokes

This file records the boundary-chart wrapper shape needed by the relative
compact-support route.  The genuine relative half-space bottom layer is not yet
available in this workspace: the planned names
`HalfSpaceBoxInteriorStokesFields` and
`halfSpaceLocalStokes_compactSupport_of_interiorFields` are absent.

The theorems below are therefore deliberately honest wrappers around the
existing finite-box layer.  They replace the separated chart API hypotheses

* `U ⊆ (extChartAt I x0).target`,
* `U ⊆ ManifoldForm.chartOverlap I x0 x1`, and
* `Icc a b ⊆ boundaryChartDomain I x0 x1`

by a single source-contained neighborhood hypothesis
`U ⊆ ManifoldForm.chartTransitionSource I x0 x1`.  This is the strongest
ambient-open relative-source spelling currently provable from the existing
local Stokes API.
-/

noncomputable section

set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section RelativeSourceWrappers

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {ρ : M → Real}
variable {ω : ManifoldForm I M n}

/-- A set contained in the project chart-transition source is contained in the
source chart target. -/
theorem subset_extChartAt_target_of_subset_chartTransitionSource
    {U : Set (Fin (n + 1) → Real)}
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    U ⊆ (extChartAt I x0).target := by
  intro y hy
  have hysource := hUsource hy
  rw [ManifoldForm.chartTransitionSource_eq] at hysource
  exact hysource.1

/-- A set contained in the project chart-transition source is contained in the
chart overlap. -/
theorem subset_chartOverlap_of_subset_chartTransitionSource
    {U : Set (Fin (n + 1) → Real)}
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    U ⊆ ManifoldForm.chartOverlap I x0 x1 := by
  intro y hy
  have hysource := hUsource hy
  rw [ManifoldForm.chartTransitionSource_eq] at hysource
  exact hysource.2

/-- A box contained in the project chart-transition source is contained in the
boundary-chart domain used by the current finite-box layer. -/
theorem Icc_subset_boundaryChartDomain_of_subset_chartTransitionSource
    {a b : Fin (n + 1) → Real}
    (hboxSource : Set.Icc a b ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    Set.Icc a b ⊆ boundaryChartDomain I x0 x1 := by
  intro y hy
  simpa [boundaryChartDomain_eq_chartTransitionSource] using hboxSource hy

/-- Localized boundary compact-box data from a source-contained smooth
neighborhood and chartwise smoothness. -/
theorem exists_boundaryLocalizedBoxData_localStokes_of_relativeChartwiseSmooth
    [IsManifold I ⊤ M]
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hsupp :
      tsupport
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω)) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hKbox : K ⊆ halfSpaceSupportBox a b)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1)
    (hρU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) U)
    (hω : ManifoldForm.ChartwiseSmooth I ω) :
    ∃ D :
        BoundaryCompactBoxSelectionData I x0 x1
          (ManifoldForm.localizedForm I ρ ω),
      D.K = K ∧ D.a = a ∧ D.b = b ∧
        halfSpaceLocalBulkIntegral
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (ManifoldForm.localizedForm I ρ ω)) D.a D.b =
          outwardFirstBoundaryChartIntegral I x0 x1
            (ManifoldForm.localizedForm I ρ ω) D.a D.b := by
  exact
    exists_boundaryLocalizedBoxData_localStokes_of_chartwiseSmooth
      (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
      hK hhalf hsupp ha0 hle hKbox
      (Icc_subset_boundaryChartDomain_of_subset_chartTransitionSource
        (I := I) (x0 := x0) (x1 := x1) (hUbox.trans hUsource))
      hU hUbox hρU hω
      (subset_extChartAt_target_of_subset_chartTransitionSource
        (I := I) (x0 := x0) (x1 := x1) hUsource)
      (subset_chartOverlap_of_subset_chartTransitionSource
        (I := I) (x0 := x0) (x1 := x1) hUsource)

/-- Assigned-box boundary local Stokes data from a source-contained smooth
neighborhood and chartwise smoothness. -/
theorem exists_boundaryAssignedBoxData_localStokes_of_relativeChartwiseSmooth
    [IsManifold I ⊤ M]
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hbase :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hcoeff :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ∩ K ⊆
        halfSpaceSupportBox a b)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1)
    (hρU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) U)
    (hω : ManifoldForm.ChartwiseSmooth I ω) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) ⊆
        halfSpaceSupportBox a b ∧
      ∃ D :
          BoundaryCompactBoxSelectionData I x0 x1
            (ManifoldForm.localizedForm I ρ ω),
        D.K =
            tsupport
              (ManifoldForm.transitionPullbackInChart I x0 x1
                (ManifoldForm.localizedForm I ρ ω)) ∧
          D.a = a ∧ D.b = b ∧
          halfSpaceLocalBulkIntegral
              (ManifoldForm.transitionPullbackInChart I x0 x1
                (ManifoldForm.localizedForm I ρ ω)) D.a D.b =
            outwardFirstBoundaryChartIntegral I x0 x1
              (ManifoldForm.localizedForm I ρ ω) D.a D.b := by
  exact
    exists_boundaryAssignedBoxData_localStokes_of_chartwiseSmooth
      (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
      hK hhalf hbase ha0 hle hcoeff
      (Icc_subset_boundaryChartDomain_of_subset_chartTransitionSource
        (I := I) (x0 := x0) (x1 := x1) (hUbox.trans hUsource))
      hU hUbox hρU hω
      (subset_extChartAt_target_of_subset_chartTransitionSource
        (I := I) (x0 := x0) (x1 := x1) hUsource)
      (subset_chartOverlap_of_subset_chartTransitionSource
        (I := I) (x0 := x0) (x1 := x1) hUsource)

/-- Project-local assigned-box Stokes from a source-contained smooth
neighborhood and chartwise smoothness. -/
theorem boundaryAssignedBox_projectLocalStokes_of_relativeChartwiseSmooth
    [IsManifold I ⊤ M]
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hbase :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hcoeff :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ∩ K ⊆
        halfSpaceSupportBox a b)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1)
    (hρU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) U)
    (hω : ManifoldForm.ChartwiseSmooth I ω) :
    projectLocalBulkIntegral I x0 x1
        (ManifoldForm.localizedForm I ρ ω) a b =
      projectLocalBoundaryIntegral I x0 x1
        (ManifoldForm.localizedForm I ρ ω) a b := by
  rcases
    exists_boundaryAssignedBoxData_localStokes_of_relativeChartwiseSmooth
      (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
      hK hhalf hbase ha0 hle hcoeff hU hUbox hUsource hρU hω with
    ⟨_hsupp, D, _hDK, hDa, hDb, hstokes⟩
  simpa [projectLocalBulkIntegral, projectLocalBoundaryIntegral, hDa, hDb] using hstokes

end RelativeSourceWrappers

section InteriorFieldsWrappers

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {ρ : M → Real}
variable {ω : ManifoldForm I M n}

/--
Project-local assigned-box Stokes from the interior-box fields used by
`CubeStokes.stokes_on_box`.

This is the boundary-compatible entry point that does **not** require an
ambient-open smoothness neighborhood contained in the extended chart target.
The analytic burden is isolated in `HalfSpaceBoxInteriorStokesFields` for the
localized transition-pullback representative.
-/
theorem boundaryAssignedBox_projectLocalStokes_of_interiorFields
    {K : Set (Fin (n + 1) → Real)}
    (hbase :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (hcoeff :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ∩ K ⊆
        halfSpaceSupportBox a b)
    (D :
      HalfSpaceBoxInteriorStokesFields
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) a b) :
    projectLocalBulkIntegral I x0 x1
        (ManifoldForm.localizedForm I ρ ω) a b =
      projectLocalBoundaryIntegral I x0 x1
        (ManifoldForm.localizedForm I ρ ω) a b := by
  have hsupp :
      tsupport
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω)) ⊆
        halfSpaceSupportBox a b :=
    ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_halfSpaceSupportBox_of_coordSupport
      (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
      (a := a) (b := b) hbase hcoeff
  have hface :
      boxFaceCoeffTSupportInHalfSpaceBox
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) a b :=
    boxFaceCoeffTSupportInHalfSpaceBox_transitionPullback_of_tsupport_subset
      I x0 x1 (ManifoldForm.localizedForm I ρ ω) a b hsupp
  have hstokes :
      halfSpaceLocalBulkIntegral
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω)) a b =
        halfSpaceBoundarySign n *
          halfSpaceBoundaryTransitionFormIntegral I x0 x1
            (ManifoldForm.localizedForm I ρ ω) a b := by
    simpa [halfSpaceBoundaryTransitionFormIntegral] using
      halfSpaceLocalStokes_compactSupport_of_interiorFields
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) a b D hface
  simpa [projectLocalBulkIntegral, projectLocalBoundaryIntegral,
    halfSpaceLocalTransitionBulkIntegral,
    outwardFirstBoundaryChartIntegral_eq_halfSpaceBoundarySign_mul] using hstokes

end InteriorFieldsWrappers

end Stokes

end
