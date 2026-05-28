import Stokes.Global.CoverIndexedLocalFieldsConstructor
import Stokes.Global.ChartwiseSmoothToLocal

/-!
# Boundary smoothness constructors for cover-indexed local fields

This file removes part of the repeated boundary smoothness plumbing in the
cover-indexed compact-support route.

The main reusable step is simple: once the selected partition coefficient is
smooth in boundary chart coordinates, chartwise smoothness of the base form
supplies the base representative smoothness, and the existing localized-form
smoothness bridge supplies the localized representative smoothness.

The main local-Stokes path now consumes the actual `C^\infty` level supplied by
mathlib's smooth partition API:

```
ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
```

Older analytic-top wrappers are kept separately where useful, but the
cover-indexed compact-support constructor no longer asks callers to manufacture
the stronger project-local `⊤ : WithTop ℕ∞` smoothness field.
-/

noncomputable section

set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section BoundarySmoothnessConstructor

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {omega : ManifoldForm I M n}
variable {P : SupportControlledSelectedPartition C}

namespace ManifoldForm

/--
Indexed version of the smooth-partition coefficient smoothness lemma.

Mathlib's `SmoothPartitionOfUnity` gives `C^\infty` coefficients, which is now
the level consumed by the compact-support local-Stokes packages.
-/
theorem contDiffOn_coefficientInChart_smoothPartition_indexed
    [IsManifold I ⊤ M]
    {ι : Type*} {S : Set M}
    (rho : SmoothPartitionOfUnity ι I M S) (x0 : M) (i : ι)
    {U : Set (Fin (n + 1) -> Real)}
    (hUtarget : U ⊆ (extChartAt I x0).target) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (coefficientInChart I x0 (rho i)) U := by
  have hsymm :
      ContMDiffOn 𝓘(Real, Fin (n + 1) -> Real) I
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (extChartAt I x0).symm U :=
    (contMDiffOn_extChartAt_symm
      (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) x0).mono hUtarget
  have hcomp :
      ContMDiffOn 𝓘(Real, Fin (n + 1) -> Real) 𝓘(Real, Real)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        ((rho i) ∘ (extChartAt I x0).symm) U :=
    ContMDiff.comp_contMDiffOn
      (I := 𝓘(Real, Fin (n + 1) -> Real)) (I' := I)
      (I'' := 𝓘(Real, Real))
      (f := (extChartAt I x0).symm) (g := rho i)
      ((rho i).contMDiff) hsymm
  simpa [coefficientInChart, Function.comp_def] using hcomp.contDiffOn

/--
Indexed smooth-partition transition-coefficient smoothness on a chart-overlap
set, again at the `C^\infty` level supplied by mathlib.
-/
theorem contDiffOn_transitionCoefficientInChart_smoothPartition_indexed
    [IsManifold I ⊤ M]
    {ι : Type*} {S : Set M}
    (rho : SmoothPartitionOfUnity ι I M S) (x0 x1 : M) (i : ι)
    {U : Set (Fin (n + 1) -> Real)}
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ chartOverlap I x0 x1) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (transitionCoefficientInChart I x0 x1 (rho i)) U := by
  exact
    (contDiffOn_coefficientInChart_smoothPartition_indexed
      (I := I) rho x0 i hUtarget).congr
      (fun y hy =>
        transitionCoefficientInChart_eq_coefficientInChart_of_mem_overlap
          (I := I) (ρ := rho i) (y := y) (hUoverlap hy))

end ManifoldForm

namespace SupportControlledSelectedPartition

/-- Boundary base-form smoothness from chartwise smoothness. -/
theorem boundaryFormSmooth_of_chartwiseSmooth
    [IsManifold I ⊤ M]
    (_P : SupportControlledSelectedPartition C)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (i : {x : M // x ∈ C.boundaryCenters})
    {U : Set (Fin (n + 1) -> Real)}
    (hUtarget : U ⊆ (extChartAt I (C.boundaryChart i.1)).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I (C.boundaryChart i.1) (C.boundaryChart i.1)) :
    ContDiffOn Real ⊤
      (ManifoldForm.transitionPullbackInChart I
        (C.boundaryChart i.1) (C.boundaryChart i.1) omega) U := by
  exact
    homega.contDiffOn_transitionPullbackInChart_of_chartAPI
      (I := I) (C.boundaryChart i.1) (C.boundaryChart i.1)
      hUtarget hUoverlap

/-- Boundary base-form `C^\infty` smoothness from chartwise smoothness. -/
theorem boundaryFormSmooth_infty_of_chartwiseSmooth
    [IsManifold I ⊤ M]
    (P : SupportControlledSelectedPartition C)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (i : {x : M // x ∈ C.boundaryCenters})
    {U : Set (Fin (n + 1) -> Real)}
    (hUtarget : U ⊆ (extChartAt I (C.boundaryChart i.1)).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I (C.boundaryChart i.1) (C.boundaryChart i.1)) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.transitionPullbackInChart I
        (C.boundaryChart i.1) (C.boundaryChart i.1) omega) U :=
  (P.boundaryFormSmooth_of_chartwiseSmooth
    (omega := omega) homega i hUtarget hUoverlap).of_le le_top

/--
Boundary coefficient smoothness at the `C^\infty` level coming directly from
the support-controlled smooth partition.
-/
theorem boundaryCoeffSmooth_infty
    [IsManifold I ⊤ M]
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters})
    {U : Set (Fin (n + 1) -> Real)}
    (hUtarget : U ⊆ (extChartAt I (C.boundaryChart i.1)).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I (C.boundaryChart i.1) (C.boundaryChart i.1)) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.transitionCoefficientInChart I
        (C.boundaryChart i.1) (C.boundaryChart i.1)
        (P.partition (Sum.inr i))) U := by
  exact
    ManifoldForm.contDiffOn_transitionCoefficientInChart_smoothPartition_indexed
      (I := I) P.partition (C.boundaryChart i.1) (C.boundaryChart i.1)
      (Sum.inr i) hUtarget hUoverlap

/--
Localized boundary representative smoothness from the two legacy analytic-top
smoothness hypotheses.
-/
theorem boundaryLocalizedFormSmooth_of_contDiffOn
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters})
    {U : Set (Fin (n + 1) -> Real)}
    (hcoeff :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.partition (Sum.inr i))) U)
    (hform :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1) omega) U) :
    ContDiffOn Real ⊤
      (ManifoldForm.transitionPullbackInChart I
        (C.boundaryChart i.1) (C.boundaryChart i.1)
        (ManifoldForm.localizedForm I (P.partition (Sum.inr i)) omega)) U := by
  exact
    ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
      (I := I) hcoeff hform

/--
Localized boundary representative smoothness from `C^\infty` coefficient and
base representative smoothness.
-/
theorem boundaryLocalizedFormSmooth_of_contDiffOn_infty
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters})
    {U : Set (Fin (n + 1) -> Real)}
    (hcoeff :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionCoefficientInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.partition (Sum.inr i))) U)
    (hform :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1) omega) U) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.transitionPullbackInChart I
        (C.boundaryChart i.1) (C.boundaryChart i.1)
        (ManifoldForm.localizedForm I (P.partition (Sum.inr i)) omega)) U := by
  exact
    ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
      (I := I) hcoeff hform

/--
Localized boundary representative smoothness from chartwise smoothness of the
base form and legacy analytic-top smoothness of the selected coefficient.
-/
theorem boundaryLocalizedFormSmooth_of_chartwiseSmooth
    [IsManifold I ⊤ M]
    (P : SupportControlledSelectedPartition C)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (i : {x : M // x ∈ C.boundaryCenters})
    {U : Set (Fin (n + 1) -> Real)}
    (hcoeff :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.partition (Sum.inr i))) U)
    (hUtarget : U ⊆ (extChartAt I (C.boundaryChart i.1)).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I (C.boundaryChart i.1) (C.boundaryChart i.1)) :
    ContDiffOn Real ⊤
      (ManifoldForm.transitionPullbackInChart I
        (C.boundaryChart i.1) (C.boundaryChart i.1)
        (ManifoldForm.localizedForm I (P.partition (Sum.inr i)) omega)) U := by
  exact
    P.boundaryLocalizedFormSmooth_of_contDiffOn (omega := omega) i hcoeff
      (P.boundaryFormSmooth_of_chartwiseSmooth
        (omega := omega) homega i hUtarget hUoverlap)

/--
`C^\infty` localized boundary smoothness obtained completely from the smooth
partition coefficient and chartwise smoothness of the base form.
-/
theorem boundaryLocalizedFormSmooth_infty_of_smoothPartition
    [IsManifold I ⊤ M]
    (P : SupportControlledSelectedPartition C)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (i : {x : M // x ∈ C.boundaryCenters})
    {U : Set (Fin (n + 1) -> Real)}
    (hUtarget : U ⊆ (extChartAt I (C.boundaryChart i.1)).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I (C.boundaryChart i.1) (C.boundaryChart i.1)) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.transitionPullbackInChart I
        (C.boundaryChart i.1) (C.boundaryChart i.1)
        (ManifoldForm.localizedForm I (P.partition (Sum.inr i)) omega)) U := by
  exact
    ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
      (I := I)
      (P.boundaryCoeffSmooth_infty i hUtarget hUoverlap)
      (P.boundaryFormSmooth_infty_of_chartwiseSmooth
        (omega := omega) homega i hUtarget hUoverlap)

end SupportControlledSelectedPartition

/--
Compatibility spelling for boundary smoothness data at the level provided
directly by mathlib's `SmoothPartitionOfUnity`.

The main downstream record `CoverIndexedBoundarySmoothnessFields` now has the
same `C^\infty` field shape.  This older name is kept as a precise, explicit
constructor target for code that wants to emphasize the mathlib smoothness
level.
-/
structure CoverIndexedBoundarySmoothnessFieldsInfty
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n)
    (boundaryNeighborhood :
      {x : M // x ∈ C.boundaryCenters} ->
        Set (Fin (n + 1) -> Real)) where
  /-- The base form is smooth in all charts. -/
  chartwiseSmooth : ManifoldForm.ChartwiseSmooth I omega
  /-- Boundary smoothness neighborhoods lie in their chart targets. -/
  neighborhood_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryNeighborhood i ⊆
        (extChartAt I (C.boundaryChart i.1)).target
  /-- Boundary smoothness neighborhoods lie in the self-overlap domain. -/
  neighborhood_subset_overlap :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryNeighborhood i ⊆
        ManifoldForm.chartOverlap I (C.boundaryChart i.1) (C.boundaryChart i.1)

namespace CoverIndexedBoundarySmoothnessFieldsInfty

variable [IsManifold I ⊤ M]
variable {boundaryNeighborhood :
  {x : M // x ∈ C.boundaryCenters} ->
    Set (Fin (n + 1) -> Real)}

/-- Constructor from exactly the natural chartwise-smooth inputs. -/
def ofChartwiseSmooth
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (hUtarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryNeighborhood i ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (hUoverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryNeighborhood i ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (C.boundaryChart i.1)) :
    CoverIndexedBoundarySmoothnessFieldsInfty P omega boundaryNeighborhood where
  chartwiseSmooth := homega
  neighborhood_subset_target := hUtarget
  neighborhood_subset_overlap := hUoverlap

/-- Boundary coefficient smoothness generated by the selected smooth partition. -/
theorem coefficient_contDiffOn
    (D : CoverIndexedBoundarySmoothnessFieldsInfty P omega boundaryNeighborhood)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.transitionCoefficientInChart I
        (C.boundaryChart i.1) (C.boundaryChart i.1)
        (P.partition (Sum.inr i))) (boundaryNeighborhood i) :=
  P.boundaryCoeffSmooth_infty i
    (D.neighborhood_subset_target i) (D.neighborhood_subset_overlap i)

/-- Base boundary representative smoothness, downgraded to the partition level. -/
theorem form_contDiffOn
    (D : CoverIndexedBoundarySmoothnessFieldsInfty P omega boundaryNeighborhood)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.transitionPullbackInChart I
        (C.boundaryChart i.1) (C.boundaryChart i.1) omega)
      (boundaryNeighborhood i) :=
  (P.boundaryFormSmooth_of_chartwiseSmooth (omega := omega)
    D.chartwiseSmooth i (D.neighborhood_subset_target i)
    (D.neighborhood_subset_overlap i)).of_le le_top

/-- Localized boundary representative smoothness generated without hand-filled fields. -/
theorem localized_contDiffOn
    (D : CoverIndexedBoundarySmoothnessFieldsInfty P omega boundaryNeighborhood)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.transitionPullbackInChart I
        (C.boundaryChart i.1) (C.boundaryChart i.1)
        (ManifoldForm.localizedForm I (P.partition (Sum.inr i)) omega))
      (boundaryNeighborhood i) :=
  ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
    (I := I) (D.coefficient_contDiffOn i) (D.form_contDiffOn i)

end CoverIndexedBoundarySmoothnessFieldsInfty

/--
Grouped `C^\infty` smoothness input for boundary cover indices.

This is the field shape consumed by the cover-indexed compact-support route:
coefficient smoothness is exactly the level generated by
`SmoothPartitionOfUnity`, and the base-form and localized-form smoothness fields
are derived from this coefficient smoothness plus chartwise smoothness.
-/
structure CoverIndexedBoundarySmoothnessFields
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n)
    (boundaryNeighborhood :
      {x : M // x ∈ C.boundaryCenters} ->
        Set (Fin (n + 1) -> Real)) where
  /-- The base form is smooth in all charts. -/
  chartwiseSmooth : ManifoldForm.ChartwiseSmooth I omega
  /-- Boundary smoothness neighborhoods lie in their chart targets. -/
  neighborhood_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryNeighborhood i ⊆
        (extChartAt I (C.boundaryChart i.1)).target
  /-- Boundary smoothness neighborhoods lie in the self-overlap domain. -/
  neighborhood_subset_overlap :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryNeighborhood i ⊆
        ManifoldForm.chartOverlap I (C.boundaryChart i.1) (C.boundaryChart i.1)
  /-- Project-local smoothness of boundary partition coefficients. -/
  coefficient_contDiffOn :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionCoefficientInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.partition (Sum.inr i))) (boundaryNeighborhood i)

namespace CoverIndexedBoundarySmoothnessFields

variable [IsManifold I ⊤ M]
variable {boundaryNeighborhood :
  {x : M // x ∈ C.boundaryCenters} ->
    Set (Fin (n + 1) -> Real)}

/-- Derived boundary base-form smoothness. -/
theorem form_contDiffOn
    (D : CoverIndexedBoundarySmoothnessFields P omega boundaryNeighborhood)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.transitionPullbackInChart I
        (C.boundaryChart i.1) (C.boundaryChart i.1) omega)
      (boundaryNeighborhood i) :=
  P.boundaryFormSmooth_infty_of_chartwiseSmooth (omega := omega)
    D.chartwiseSmooth i (D.neighborhood_subset_target i)
    (D.neighborhood_subset_overlap i)

/-- Derived localized boundary representative smoothness. -/
theorem localized_contDiffOn
    (D : CoverIndexedBoundarySmoothnessFields P omega boundaryNeighborhood)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.transitionPullbackInChart I
        (C.boundaryChart i.1) (C.boundaryChart i.1)
        (ManifoldForm.localizedForm I (P.partition (Sum.inr i)) omega))
      (boundaryNeighborhood i) :=
  P.boundaryLocalizedFormSmooth_of_contDiffOn_infty (omega := omega) i
    (D.coefficient_contDiffOn i) (D.form_contDiffOn i)

/--
Constructor from exactly the natural chartwise-smooth inputs.
-/
def ofChartwiseSmooth
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (hUtarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryNeighborhood i ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (hUoverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryNeighborhood i ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (C.boundaryChart i.1)) :
    CoverIndexedBoundarySmoothnessFields P omega boundaryNeighborhood where
  chartwiseSmooth := homega
  neighborhood_subset_target := hUtarget
  neighborhood_subset_overlap := hUoverlap
  coefficient_contDiffOn := fun i =>
    P.boundaryCoeffSmooth_infty i (hUtarget i) (hUoverlap i)

/-- Convert the explicit `C^\infty` compatibility package to the main field shape. -/
def ofInfty
    (D : CoverIndexedBoundarySmoothnessFieldsInfty P omega boundaryNeighborhood) :
    CoverIndexedBoundarySmoothnessFields P omega boundaryNeighborhood where
  chartwiseSmooth := D.chartwiseSmooth
  neighborhood_subset_target := D.neighborhood_subset_target
  neighborhood_subset_overlap := D.neighborhood_subset_overlap
  coefficient_contDiffOn := D.coefficient_contDiffOn

/--
Compatibility wrapper for old call sites that used to provide an analytic-top
coefficient upgrade.  The upgrade is no longer needed because the main local
field package consumes `C^\infty` directly.
-/
def ofInfty_of_coefficientUpgrade
    (D : CoverIndexedBoundarySmoothnessFieldsInfty P omega boundaryNeighborhood)
    (_hupgrade :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionCoefficientInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1)
            (P.partition (Sum.inr i))) (boundaryNeighborhood i) ->
        ContDiffOn Real ⊤
          (ManifoldForm.transitionCoefficientInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1)
            (P.partition (Sum.inr i))) (boundaryNeighborhood i)) :
    CoverIndexedBoundarySmoothnessFields P omega boundaryNeighborhood :=
  ofInfty D

end CoverIndexedBoundarySmoothnessFields

namespace SupportControlledCoverIndexedLocalStokesFields

/--
Build the cover-indexed local-fields package from assigned-box boundary fields
and grouped boundary smoothness data.
-/
def ofBoundaryAssignedBoxFieldsAndBoundarySmoothness
    [IsManifold I ⊤ M]
    (interiorCoordSupport :
      {x : M // x ∈ C.interiorCenters} ->
        Set (Fin (n + 1) -> Real))
    (interiorExtendedBox :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        interiorChartExtendedBox I
          (C.interiorChart i.1) (C.interiorChart i.1)
          (P.coverIndexLocalizedForm omega (Sum.inl i))
          (C.interiorLower i.1) (C.interiorUpper i.1))
    (interiorBaseSupport :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.interiorChart i.1) (C.interiorChart i.1) omega) ⊆
          interiorCoordSupport i)
    (interiorCoordMapsToSupport :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        ∀ y ∈ interiorCoordSupport i,
          (extChartAt I (C.interiorChart i.1)).symm y ∈ K)
    (interiorCoordSubsetTarget :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        interiorCoordSupport i ⊆
          (extChartAt I (C.interiorChart i.1)).target)
    (boundaryCoordSupport boundaryNeighborhood :
      {x : M // x ∈ C.boundaryCenters} ->
        Set (Fin (n + 1) -> Real))
    (boundaryAssignedFields :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        SupportControlledSelectedPartition.BoundaryAssignedBoxCoordSupportFields P i omega
          (boundaryCoordSupport i) (boundaryNeighborhood i))
    (boundaryCoordMapsToSupport :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ∀ y ∈ boundaryCoordSupport i,
          (extChartAt I (C.boundaryChart i.1)).symm y ∈ K)
    (boundaryCoordSubsetTarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryCoordSupport i ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (smoothness :
      CoverIndexedBoundarySmoothnessFields P omega boundaryNeighborhood) :
    SupportControlledCoverIndexedLocalStokesFields P omega :=
  ofBoundaryAssignedBoxFields
    (P := P) (ω := omega)
    interiorCoordSupport interiorExtendedBox interiorBaseSupport
    interiorCoordMapsToSupport interiorCoordSubsetTarget
    boundaryCoordSupport boundaryNeighborhood boundaryAssignedFields
    boundaryCoordMapsToSupport boundaryCoordSubsetTarget
    smoothness.coefficient_contDiffOn smoothness.form_contDiffOn

/--
Boundary local Stokes directly from assigned-box fields and grouped smoothness
data, without constructing the full local-fields record.
-/
theorem boundaryLocalBulk_eq_localBoundary_of_assignedBoxFieldsAndBoundarySmoothness
    [IsManifold I ⊤ M]
    (boundaryCoordSupport boundaryNeighborhood :
      {x : M // x ∈ C.boundaryCenters} ->
        Set (Fin (n + 1) -> Real))
    (boundaryAssignedFields :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        SupportControlledSelectedPartition.BoundaryAssignedBoxCoordSupportFields P i omega
          (boundaryCoordSupport i) (boundaryNeighborhood i))
    (smoothness :
      CoverIndexedBoundarySmoothnessFields P omega boundaryNeighborhood)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    P.coverIndexLocalBulkTerm omega (Sum.inr i) =
      P.coverIndexLocalBoundaryTerm omega (Sum.inr i) :=
  boundaryLocalBulk_eq_localBoundary_of_assignedBoxFields
    (P := P) (ω := omega)
    boundaryCoordSupport boundaryNeighborhood boundaryAssignedFields
    smoothness.coefficient_contDiffOn smoothness.form_contDiffOn i

end SupportControlledCoverIndexedLocalStokesFields

end BoundarySmoothnessConstructor

end Stokes

end
