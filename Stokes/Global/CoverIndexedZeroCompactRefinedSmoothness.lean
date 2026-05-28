import Stokes.Global.CoverIndexedBoundarySmoothnessConstructor
import Stokes.Global.CoverIndexedZeroCompactBoxPartitionRefinement

/-!
# Smoothness transport for box-refined boundary pieces

This file supplies the smoothness side of the refined compact-support boundary
route.  The refined coefficients are arbitrary future subpartition
coefficients, so their smoothness is recorded as an honest input.  From that
input and chartwise smoothness of the base form we derive the two fields
consumed by the refined half-space local Stokes theorem.
-/

noncomputable section

set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section GenericSmoothness

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {x0 x1 : M} {rho : M -> Real} {omega : ManifoldForm I M n}
variable {U : Set (Fin (n + 1) -> Real)}

namespace ManifoldForm

/--
Generic coefficient bridge for a chart-overlap neighborhood.

If a scalar coefficient is smooth when written in the source chart, then the
transition-coordinate coefficient is smooth on any set contained in the
source/target chart overlap.  This is the coefficient-side analogue of the
chartwise smoothness transport for forms.
-/
theorem contDiffOn_transitionCoefficientInChart_of_coefficientInChart
    (hrho :
      ContDiffOn Real ⊤ (coefficientInChart I x0 rho) U)
    (hUoverlap : U ⊆ chartOverlap I x0 x1) :
    ContDiffOn Real ⊤
      (transitionCoefficientInChart I x0 x1 rho) U := by
  exact hrho.congr fun y hy =>
    transitionCoefficientInChart_eq_coefficientInChart_of_mem_overlap
      (I := I) (ρ := rho) (y := y) (hUoverlap hy)

/--
Chartwise smoothness of the base form gives smoothness of its transition
pullback on a refined box neighborhood.
-/
theorem contDiffOn_transitionPullbackInChart_of_chartwiseSmooth_refined
    [IsManifold I ⊤ M]
    (homega : ChartwiseSmooth I omega)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ chartOverlap I x0 x1) :
    ContDiffOn Real ⊤
      (transitionPullbackInChart I x0 x1 omega) U :=
  homega.contDiffOn_transitionPullbackInChart_of_chartAPI
    (I := I) x0 x1 hUtarget hUoverlap

/--
Localized refined smoothness from a transition-coordinate coefficient and a
chartwise-smooth base form.
-/
theorem contDiffOn_transitionPullbackInChart_localizedForm_of_refined
    [IsManifold I ⊤ M]
    (hrho :
      ContDiffOn Real ⊤ (transitionCoefficientInChart I x0 x1 rho) U)
    (homega : ChartwiseSmooth I omega)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ chartOverlap I x0 x1) :
    ContDiffOn Real ⊤
      (transitionPullbackInChart I x0 x1
        (localizedForm I rho omega)) U := by
  exact
    contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
      (I := I) hrho
      (contDiffOn_transitionPullbackInChart_of_chartwiseSmooth_refined
        (I := I) (x0 := x0) (x1 := x1) (omega := omega)
        (U := U) homega hUtarget hUoverlap)

/--
Localized refined smoothness from source-chart coefficient smoothness and
chartwise smoothness of the base form.
-/
theorem contDiffOn_transitionPullbackInChart_localizedForm_of_coefficientInChart
    [IsManifold I ⊤ M]
    (hrho :
      ContDiffOn Real ⊤ (coefficientInChart I x0 rho) U)
    (homega : ChartwiseSmooth I omega)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ chartOverlap I x0 x1) :
    ContDiffOn Real ⊤
      (transitionPullbackInChart I x0 x1
        (localizedForm I rho omega)) U := by
  exact
    contDiffOn_transitionPullbackInChart_localizedForm_of_refined
      (I := I) (x0 := x0) (x1 := x1) (rho := rho)
      (omega := omega) (U := U)
      (contDiffOn_transitionCoefficientInChart_of_coefficientInChart
        (I := I) (x0 := x0) (x1 := x1) (rho := rho)
        (U := U) hrho hUoverlap)
      homega hUtarget hUoverlap

end ManifoldForm

end GenericSmoothness

section RefinedFields

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/--
Smoothness data for every refined boundary box.

The coefficient field is intentionally an input: the refined coefficients are
constructed by later partition-refinement work, and no smoothness should be
invented here.  The base-form field is derived from chartwise smoothness plus
target/overlap containment of each refined smoothness neighborhood.
-/
structure CoverIndexedBoundaryBoxRefinedSmoothnessFields
    (D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P omega BoundaryPiece)
    (U :
      CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece ->
        Set (Fin (n + 1) -> Real)) where
  /-- The base form is smooth in all charts. -/
  chartwiseSmooth : ManifoldForm.ChartwiseSmooth I omega
  /-- Refined smoothness neighborhoods lie in the source chart target. -/
  neighborhood_subset_target :
    forall i q, q ∈ D.boundaryPieces i ->
      U i q ⊆ (extChartAt I (D.sourceChart i q)).target
  /-- Refined smoothness neighborhoods lie in the source/target overlap. -/
  neighborhood_subset_overlap :
    forall i q, q ∈ D.boundaryPieces i ->
      U i q ⊆
        ManifoldForm.chartOverlap I (D.sourceChart i q) (D.targetChart i q)
  /-- Smoothness of the refined scalar coefficients in transition coordinates. -/
  coefficient_contDiffOn :
    forall i q, q ∈ D.boundaryPieces i ->
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I
          (D.sourceChart i q) (D.targetChart i q) (D.coefficient i q))
        (U i q)

namespace CoverIndexedBoundaryBoxRefinedSmoothnessFields

variable
  {D :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P omega BoundaryPiece}
  {U :
    CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece ->
      Set (Fin (n + 1) -> Real)}

/-- Build the refined smoothness fields from source-chart coefficient smoothness. -/
def ofCoefficientInChart
    [IsManifold I ⊤ M]
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (hUtarget :
      forall i q, q ∈ D.boundaryPieces i ->
        U i q ⊆ (extChartAt I (D.sourceChart i q)).target)
    (hUoverlap :
      forall i q, q ∈ D.boundaryPieces i ->
        U i q ⊆
          ManifoldForm.chartOverlap I (D.sourceChart i q) (D.targetChart i q))
    (hcoeffInChart :
      forall i q, q ∈ D.boundaryPieces i ->
        ContDiffOn Real ⊤
          (ManifoldForm.coefficientInChart I
            (D.sourceChart i q) (D.coefficient i q))
          (U i q)) :
    CoverIndexedBoundaryBoxRefinedSmoothnessFields D U where
  chartwiseSmooth := homega
  neighborhood_subset_target := hUtarget
  neighborhood_subset_overlap := hUoverlap
  coefficient_contDiffOn := by
    intro i q hq
    exact
      ManifoldForm.contDiffOn_transitionCoefficientInChart_of_coefficientInChart
        (I := I) (x0 := D.sourceChart i q) (x1 := D.targetChart i q)
        (rho := D.coefficient i q) (U := U i q)
        (hcoeffInChart i q hq) (hUoverlap i q hq)

/-- Base transition-pullback smoothness generated for one refined box. -/
theorem form_contDiffOn
    [IsManifold I ⊤ M]
    (S : CoverIndexedBoundaryBoxRefinedSmoothnessFields D U)
    (i : CoverIndexedBoundaryIndex (I := I) C) {q : BoundaryPiece}
    (hq : q ∈ D.boundaryPieces i) :
    ContDiffOn Real ⊤
      (ManifoldForm.transitionPullbackInChart I
        (D.sourceChart i q) (D.targetChart i q) omega)
      (U i q) :=
  ManifoldForm.contDiffOn_transitionPullbackInChart_of_chartwiseSmooth_refined
    (I := I) (x0 := D.sourceChart i q) (x1 := D.targetChart i q)
    (omega := omega) (U := U i q) S.chartwiseSmooth
    (S.neighborhood_subset_target i q hq)
    (S.neighborhood_subset_overlap i q hq)

/-- Localized transition-pullback smoothness generated for one refined box. -/
theorem localized_contDiffOn
    [IsManifold I ⊤ M]
    (S : CoverIndexedBoundaryBoxRefinedSmoothnessFields D U)
    (i : CoverIndexedBoundaryIndex (I := I) C) {q : BoundaryPiece}
    (hq : q ∈ D.boundaryPieces i) :
    ContDiffOn Real ⊤
      (ManifoldForm.transitionPullbackInChart I
        (D.sourceChart i q) (D.targetChart i q)
        (D.localizedForm i q)) (U i q) := by
  exact
    ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_refined
      (I := I) (x0 := D.sourceChart i q) (x1 := D.targetChart i q)
      (rho := D.coefficient i q) (omega := omega) (U := U i q)
      (S.coefficient_contDiffOn i q hq) S.chartwiseSmooth
      (S.neighborhood_subset_target i q hq)
      (S.neighborhood_subset_overlap i q hq)

/-- The `hrhoU` field expected by the refined local Stokes theorem. -/
theorem coefficient_contDiffOn_univ
    (S : CoverIndexedBoundaryBoxRefinedSmoothnessFields D U) :
    forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
      forall q, q ∈ D.boundaryPieces i ->
        ContDiffOn Real ⊤
          (ManifoldForm.transitionCoefficientInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.coefficient i q))
          (U i q) := by
  intro i _hi q hq
  exact S.coefficient_contDiffOn i q hq

/-- The `homegaU` field expected by the refined local Stokes theorem. -/
theorem form_contDiffOn_univ
    [IsManifold I ⊤ M]
    (S : CoverIndexedBoundaryBoxRefinedSmoothnessFields D U) :
    forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
      forall q, q ∈ D.boundaryPieces i ->
        ContDiffOn Real ⊤
          (ManifoldForm.transitionPullbackInChart I
            (D.sourceChart i q) (D.targetChart i q) omega)
          (U i q) := by
  intro i _hi q hq
  exact S.form_contDiffOn i hq

end CoverIndexedBoundaryBoxRefinedSmoothnessFields

namespace CoverIndexedBoundaryBoxRefinedPartition

variable
  (D :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P omega BoundaryPiece)
  {U :
    CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece ->
      Set (Fin (n + 1) -> Real)}

/--
Refined boundary half-space Stokes with smoothness generated from the grouped
refined smoothness fields.
-/
theorem boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_refinedSmoothness
    [IsManifold I ⊤ M]
    (S : CoverIndexedBoundaryBoxRefinedSmoothnessFields D U)
    (hU :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i -> IsOpen (U i q))
    (hUbox :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
          Icc (D.lower i q) (D.upper i q) ⊆ U i q) :
    (Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBulkTerm i q) =
      Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBoundaryTerm i q :=
  D.boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_contDiffOn hU hUbox
    S.coefficient_contDiffOn_univ S.form_contDiffOn_univ

end CoverIndexedBoundaryBoxRefinedPartition

end RefinedFields

end Stokes

end
