import Stokes.Global.CoverIndexedOpenInteriorSmoothnessConstructor

/-!
# Closed-box regularity constructors for refined boundary boxes

This module removes the last small analytic certificate from the natural
compact-support represented Stokes route.  The key point is honest: closed-box
regularity is not a consequence of open-box smoothness alone, but it does
follow from relative `ContDiffOn` of the localized chart representative on the
closed coordinate box.
-/

noncomputable section

set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section ClosedBoxRegularityConstructor

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryBoxRefinedClosedBoxRegularityFields

variable
  (D :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P omega BoundaryPiece)

/--
Build the refined closed-box regularity record from relative smoothness of each
localized chart representative on its closed coordinate box.
-/
def of_localizedContDiffOn_Icc
    (hlocalized :
      ∀ i q, q ∈ D.boundaryPieces i →
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionPullbackInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
          (Icc (D.lower i q) (D.upper i q))) :
    CoverIndexedBoundaryBoxRefinedClosedBoxRegularityFields D where
  continuous_signedCoeff := by
    intro i q hq
    exact
      continuous_signedCoeff_of_contDiffOn_Icc
        (ManifoldForm.transitionPullbackInChart I
          (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
        (D.lower i q) (D.upper i q) (hlocalized i q hq)
  integrable_divergence := by
    intro i q hq
    exact
      integrable_divergence_of_contDiffOn_Icc
        (ManifoldForm.transitionPullbackInChart I
          (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
        (D.lower i q) (D.upper i q) (hlocalized i q hq)

end CoverIndexedBoundaryBoxRefinedClosedBoxRegularityFields

namespace CoverIndexedBoundaryBoxRefinedPartition

variable
  (D :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P omega BoundaryPiece)

/--
Closed-box regularity from chartwise smoothness and transition-coordinate
smoothness of the refined scalar coefficient on each closed box.
-/
def closedBoxRegularityFields_of_chartwiseSmooth
    [IsManifold I ⊤ M]
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (hcoeff :
      ∀ i q, q ∈ D.boundaryPieces i →
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionCoefficientInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.coefficient i q))
          (Icc (D.lower i q) (D.upper i q))) :
    CoverIndexedBoundaryBoxRefinedClosedBoxRegularityFields D :=
  CoverIndexedBoundaryBoxRefinedClosedBoxRegularityFields.of_localizedContDiffOn_Icc
    (I := I) (K := K) (omega := omega) (C := C) (P := P) D
    (by
      intro i q hq
      have htarget :
          Icc (D.lower i q) (D.upper i q) ⊆
            (extChartAt I (D.sourceChart i q)).target :=
        (D.Icc_subset_boundaryChartDomain i q hq).trans
          (boundaryChartDomain_subset_target I (D.sourceChart i q) (D.targetChart i q))
      have hoverlap :
          Icc (D.lower i q) (D.upper i q) ⊆
            ManifoldForm.chartOverlap I (D.sourceChart i q) (D.targetChart i q) :=
        (D.Icc_subset_boundaryChartDomain i q hq).trans
          (boundaryChartDomain_subset_overlap I (D.sourceChart i q) (D.targetChart i q))
      exact
        ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
          (I := I) (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
          (hcoeff i q hq)
          ((homega.contDiffOn_transitionPullbackInChart_of_chartAPI
            (I := I) (D.sourceChart i q) (D.targetChart i q)
            htarget hoverlap).of_le le_top))

/--
Closed-box regularity from source-chart smoothness of the refined scalar
coefficient.  The source/target transition is handled by the overlap part of
the stored box geometry.
-/
def closedBoxRegularityFields_of_coefficientInChart
    [IsManifold I ⊤ M]
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (hcoeff :
      ∀ i q, q ∈ D.boundaryPieces i →
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.coefficientInChart I
            (D.sourceChart i q) (D.coefficient i q))
          (Icc (D.lower i q) (D.upper i q))) :
    CoverIndexedBoundaryBoxRefinedClosedBoxRegularityFields D :=
  D.closedBoxRegularityFields_of_chartwiseSmooth
    (I := I) (K := K) (omega := omega) homega
    (by
      intro i q hq
      have hoverlap :
          Icc (D.lower i q) (D.upper i q) ⊆
            ManifoldForm.chartOverlap I (D.sourceChart i q) (D.targetChart i q) :=
        (D.Icc_subset_boundaryChartDomain i q hq).trans
          (boundaryChartDomain_subset_overlap I (D.sourceChart i q) (D.targetChart i q))
      refine (hcoeff i q hq).congr ?_
      intro y hy
      exact
        ManifoldForm.transitionCoefficientInChart_eq_coefficientInChart_of_mem_overlap
          (I := I) (ρ := D.coefficient i q) (y := y) (hoverlap hy))

end CoverIndexedBoundaryBoxRefinedPartition

end ClosedBoxRegularityConstructor

end Stokes

end
