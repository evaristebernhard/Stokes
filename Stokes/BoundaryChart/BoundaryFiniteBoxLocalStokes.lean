import Stokes.BoundaryChart.BoundaryOpenBoxSelection
import Stokes.Global.LocalizedSmoothness

/-!
# Boundary finite-box local Stokes for localized pieces

This file is the boundary analogue of the finite-box localization step used in
the compact-support global proof.

The mathematical input is deliberately concrete: a localized boundary-chart
representative has compact topological support contained in a compact set `K`,
`K` lies in a selected half-space support box, and the closed ambient box lies
in the boundary chart domain.  From these facts we build the existing
`BoundaryCompactBoxSelectionData` and apply the half-space local Stokes theorem,
with the boundary term written in the outward-normal-first convention.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ρ : M → Real} {ω : ManifoldForm I M n}

/--
Localized boundary-piece local Stokes from an already selected support-control
box.

This is the direct form used after finite box/refinement arguments: the
localized representative's `tsupport` is carried by a compact set `K`, `K` is
inside the chosen half-space support box, and the closed box is admissible for
the boundary chart transition.  The conclusion returns the compact box data
for the localized form together with the outward-first local Stokes identity.
-/
theorem exists_boundaryLocalizedBoxData_localStokes_of_box_subset_domain
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hsupp :
      tsupport
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω)) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hKbox : K ⊆ halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hlocalizedU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) U) :
    ∃ D :
        BoundaryCompactBoxSelectionData I x0 x1
          (ManifoldForm.localizedForm I ρ ω),
      D.K = K ∧ D.a = a ∧ D.b = b ∧
        halfSpaceLocalBulkIntegral
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (ManifoldForm.localizedForm I ρ ω)) D.a D.b =
          outwardFirstBoundaryChartIntegral I x0 x1
            (ManifoldForm.localizedForm I ρ ω) D.a D.b :=
  exists_boundaryCompactBoxSelectionData_localStokes_of_isCompact_of_box_subset_domain
    (I := I) (x0 := x0) (x1 := x1)
    (ω := ManifoldForm.localizedForm I ρ ω)
    hK hhalf hsupp ha0 hle hKbox hdomain hU hUbox hlocalizedU

/--
`C^\infty` version of
`exists_boundaryLocalizedBoxData_localStokes_of_box_subset_domain`.
-/
theorem exists_boundaryLocalizedBoxData_localStokes_of_box_subset_domain_infty
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hsupp :
      tsupport
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω)) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hKbox : K ⊆ halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hlocalizedU :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) U) :
    ∃ D :
        BoundaryCompactBoxSelectionData I x0 x1
          (ManifoldForm.localizedForm I ρ ω),
      D.K = K ∧ D.a = a ∧ D.b = b ∧
        halfSpaceLocalBulkIntegral
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (ManifoldForm.localizedForm I ρ ω)) D.a D.b =
          outwardFirstBoundaryChartIntegral I x0 x1
            (ManifoldForm.localizedForm I ρ ω) D.a D.b :=
  exists_boundaryCompactBoxSelectionData_localStokes_of_isCompact_of_box_subset_domain_infty
    (I := I) (x0 := x0) (x1 := x1)
    (ω := ManifoldForm.localizedForm I ρ ω)
    hK hhalf hsupp ha0 hle hKbox hdomain hU hUbox hlocalizedU

/--
Same localized boundary local Stokes theorem, deriving localized smoothness
from smoothness of the transition coefficient and the base representative on
the same open box-neighborhood.
-/
theorem exists_boundaryLocalizedBoxData_localStokes_of_contDiffOn
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hsupp :
      tsupport
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω)) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hKbox : K ⊆ halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hρU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) U)
    (hωU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
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
    exists_boundaryLocalizedBoxData_localStokes_of_box_subset_domain
      (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
      hK hhalf hsupp ha0 hle hKbox hdomain hU hUbox
      (ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
        (I := I) hρU hωU)

/--
`C^\infty` localized boundary local Stokes theorem, deriving localized
smoothness from `C^\infty` coefficient and base representative smoothness.
-/
theorem exists_boundaryLocalizedBoxData_localStokes_of_contDiffOn_infty
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hsupp :
      tsupport
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω)) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hKbox : K ⊆ halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hρU :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) U)
    (hωU :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
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
    exists_boundaryLocalizedBoxData_localStokes_of_box_subset_domain_infty
      (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
      hK hhalf hsupp ha0 hle hKbox hdomain hU hUbox
      (ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
        (I := I) hρU hωU)

/--
Chartwise-smooth spelling for localized boundary pieces.  The base form is
smooth in charts, the coefficient is smooth on the box-neighborhood, and the
neighborhood lies in the relevant chart target and overlap; therefore the
localized piece satisfies the outward-first boundary local Stokes identity.
-/
theorem exists_boundaryLocalizedBoxData_localStokes_of_chartwiseSmooth
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
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hρU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) U)
    (hω : ManifoldForm.ChartwiseSmooth I ω)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I x0 x1) :
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
    exists_boundaryLocalizedBoxData_localStokes_of_contDiffOn
      (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
      hK hhalf hsupp ha0 hle hKbox hdomain hU hUbox hρU
      (hω.contDiffOn_transitionPullbackInChart_of_chartAPI
        (I := I) x0 x1 hUtarget hUoverlap)

end ManifoldBoundary

end Stokes

end
