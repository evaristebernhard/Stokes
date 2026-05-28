import Stokes.Global.CoverIndexedZeroSupportFromGlobal
import Stokes.Global.CoverIndexedZeroCompactBoxPartitionRefinement

/-!
# Zero-extended localized support

This file supplies the support bridge for the intrinsic compact-support route:
the zero-extended localized transition representative is supported where both
the zero-extended base representative and the transition coefficient are
supported.  Combining the zero-support bridge from global compact support with
the refined coefficient support field gives the half-space support statement
used by boundary local Stokes.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section ZeroLocalizedSupport

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {k : Nat}
variable {I : ModelWithCorners Real E H}
variable {x0 x1 : M}
variable {ρ : M → Real}
variable {ω : ManifoldForm I M k}

namespace ManifoldForm

/-- Zero extension commutes with localization in transition coordinates. -/
theorem transitionPullbackInChartZero_localizedForm :
    transitionPullbackInChartZero I x0 x1 (localizedForm I ρ ω) =
      fun y =>
        transitionCoefficientInChart I x0 x1 ρ y •
          transitionPullbackInChartZero I x0 x1 ω y := by
  classical
  funext y
  by_cases hy : y ∈ chartTransitionSource I x0 x1
  · rw [transitionPullbackInChartZero_eq_transitionPullbackInChart_of_mem_source
        (I := I) (x0 := x0) (x1 := x1)
        (ω := localizedForm I ρ ω) hy,
      transitionPullbackInChartZero_eq_transitionPullbackInChart_of_mem_source
        (I := I) (x0 := x0) (x1 := x1) (ω := ω) hy]
    exact transitionPullbackInChart_localizedForm_apply
      (I := I) x0 x1 ρ ω y
  · rw [transitionPullbackInChartZero_eq_zero_of_notMem_source
        (I := I) (x0 := x0) (x1 := x1)
        (ω := localizedForm I ρ ω) hy,
      transitionPullbackInChartZero_eq_zero_of_notMem_source
        (I := I) (x0 := x0) (x1 := x1) (ω := ω) hy]
    simp

/-- The zero-extended localized representative is topologically supported in
the transition coefficient support. -/
theorem transitionPullbackInChartZero_localizedForm_tsupport_subset_coefficient :
    tsupport
        (transitionPullbackInChartZero I x0 x1 (localizedForm I ρ ω)) ⊆
      tsupport (transitionCoefficientInChart I x0 x1 ρ) := by
  rw [transitionPullbackInChartZero_localizedForm]
  exact tsupport_smul_subset_left
    (transitionCoefficientInChart I x0 x1 ρ)
    (transitionPullbackInChartZero I x0 x1 ω)

/-- The zero-extended localized representative is topologically supported in
the zero-extended base representative support. -/
theorem transitionPullbackInChartZero_localizedForm_tsupport_subset_form :
    tsupport
        (transitionPullbackInChartZero I x0 x1 (localizedForm I ρ ω)) ⊆
      tsupport (transitionPullbackInChartZero I x0 x1 ω) := by
  rw [transitionPullbackInChartZero_localizedForm]
  exact tsupport_smul_subset_right
    (transitionCoefficientInChart I x0 x1 ρ)
    (transitionPullbackInChartZero I x0 x1 ω)

/-- If the coefficient support and the zero base support intersect only inside
an assigned half-space support box, then the zero-localized representative is
supported in that box. -/
theorem transitionPullbackInChartZero_localizedForm_tsupport_subset_halfSpaceSupportBox_of_inter
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ρ : M → Real} {ω : ManifoldForm I M k}
    {a b : Fin (n + 1) → Real}
    (hinter :
      tsupport (transitionCoefficientInChart I x0 x1 ρ) ∩
          tsupport (transitionPullbackInChartZero I x0 x1 ω) ⊆
        halfSpaceSupportBox a b) :
    tsupport
        (transitionPullbackInChartZero I x0 x1 (localizedForm I ρ ω)) ⊆
      halfSpaceSupportBox a b := by
  intro y hy
  exact hinter
    ⟨transitionPullbackInChartZero_localizedForm_tsupport_subset_coefficient
        (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω) hy,
      transitionPullbackInChartZero_localizedForm_tsupport_subset_form
        (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω) hy⟩

/-- Coordinate-carrier spelling of the zero-localized support bridge. -/
theorem transitionPullbackInChartZero_localizedForm_tsupport_subset_halfSpaceSupportBox_of_coordSupport
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ρ : M → Real} {ω : ManifoldForm I M k}
    {C : Set (Fin (n + 1) → Real)} {a b : Fin (n + 1) → Real}
    (hbase :
      tsupport (transitionPullbackInChartZero I x0 x1 ω) ⊆ C)
    (hcoeff :
      tsupport (transitionCoefficientInChart I x0 x1 ρ) ∩ C ⊆
        halfSpaceSupportBox a b) :
    tsupport
        (transitionPullbackInChartZero I x0 x1 (localizedForm I ρ ω)) ⊆
      halfSpaceSupportBox a b := by
  refine
    transitionPullbackInChartZero_localizedForm_tsupport_subset_halfSpaceSupportBox_of_inter
      (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
      (a := a) (b := b) ?_
  intro y hy
  exact hcoeff ⟨hy.1, hbase hy.2⟩

end ManifoldForm

end ZeroLocalizedSupport

section ZeroLocalizedSupportFromCompactSupport

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n k : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {x0 x1 : M}
variable {ρ : M → Real}
variable {ω : ManifoldForm I M k}
variable [IsManifold I 1 M]

namespace ManifoldForm

/--
Zero/localized half-space support from global compact support.

The base zero representative is first supported in `chartCoordinateImage I x0 K`
by `support I ω ⊆ K`; the caller then embeds that image into the refined
coordinate carrier where the coefficient support has already been proved.
-/
theorem transitionPullbackInChartZero_localizedForm_tsupport_subset_halfSpaceSupportBox_of_support_subset_K
    {coordSupport : Set (Fin (n + 1) → Real)}
    {a b : Fin (n + 1) → Real}
    (hK : IsCompact K)
    (hsource : K ⊆ (extChartAt I x0).source)
    (hωsupport : support I ω ⊆ K)
    (hcoord :
      chartCoordinateImage I x0 K ⊆ coordSupport)
    (hcoeff :
      tsupport (transitionCoefficientInChart I x0 x1 ρ) ∩ coordSupport ⊆
        halfSpaceSupportBox a b) :
    tsupport
        (transitionPullbackInChartZero I x0 x1 (localizedForm I ρ ω)) ⊆
      halfSpaceSupportBox a b :=
  transitionPullbackInChartZero_localizedForm_tsupport_subset_halfSpaceSupportBox_of_coordSupport
    (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
    (C := coordSupport) (a := a) (b := b)
    ((transitionPullbackInChartZero_tsupport_subset_chartCoordinateImage
      (I := I) (K := K) (x0 := x0) (x1 := x1) (ω := ω)
      hK hsource hωsupport).trans hcoord)
    hcoeff

end ManifoldForm

end ZeroLocalizedSupportFromCompactSupport

section CoverIndexedZeroLocalizedSupport

universe uH uM uB

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type uB}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable [IsManifold I 1 M]

namespace CoverIndexedBoundaryBoxRefinedPartition

variable
  (D : CoverIndexedBoundaryBoxRefinedPartition
    (I := I) (K := K) C P ω BoundaryPiece)

/--
Zero-extended support version of the refined localized support field, derived
from global compact support of the represented form.
-/
theorem zero_localized_tsupport_subset_halfSpaceSupportBox_of_support_subset_K
    (hK : IsCompact K)
    (hsource :
      ∀ i q, q ∈ D.boundaryPieces i →
        K ⊆ (extChartAt I (D.sourceChart i q)).source)
    (hωsupport : ManifoldForm.support I ω ⊆ K)
    (hcoord :
      ∀ i q, q ∈ D.boundaryPieces i →
        chartCoordinateImage I (D.sourceChart i q) K ⊆ D.coordSupport i q)
    (i : CoverIndexedBoundaryIndex (I := I) C) {q : BoundaryPiece}
    (hq : q ∈ D.boundaryPieces i) :
    tsupport
        (ManifoldForm.transitionPullbackInChartZero I
          (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q)) ⊆
      halfSpaceSupportBox (D.lower i q) (D.upper i q) := by
  simpa [localizedForm] using
    ManifoldForm.transitionPullbackInChartZero_localizedForm_tsupport_subset_halfSpaceSupportBox_of_support_subset_K
      (I := I) (K := K)
      (x0 := D.sourceChart i q) (x1 := D.targetChart i q)
      (ρ := D.coefficient i q) (ω := ω)
      (coordSupport := D.coordSupport i q)
      (a := D.lower i q) (b := D.upper i q)
      hK (hsource i q hq) hωsupport (hcoord i q hq)
      (D.coefficient_tsupport_inter_coordSupport_subset_halfSpaceSupportBox i q hq)

/-- Field-level spelling of
`zero_localized_tsupport_subset_halfSpaceSupportBox_of_support_subset_K`. -/
theorem zero_localized_tsupport_subset_halfSpaceSupportBox_of_support_subset_K_all
    (hK : IsCompact K)
    (hsource :
      ∀ i q, q ∈ D.boundaryPieces i →
        K ⊆ (extChartAt I (D.sourceChart i q)).source)
    (hωsupport : ManifoldForm.support I ω ⊆ K)
    (hcoord :
      ∀ i q, q ∈ D.boundaryPieces i →
        chartCoordinateImage I (D.sourceChart i q) K ⊆ D.coordSupport i q) :
    ∀ i, ∀ q, q ∈ D.boundaryPieces i →
      tsupport
          (ManifoldForm.transitionPullbackInChartZero I
            (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q)) ⊆
        halfSpaceSupportBox (D.lower i q) (D.upper i q) := by
  intro i q hq
  exact
    D.zero_localized_tsupport_subset_halfSpaceSupportBox_of_support_subset_K
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      hK hsource hωsupport hcoord i hq

end CoverIndexedBoundaryBoxRefinedPartition

end CoverIndexedZeroLocalizedSupport

end Stokes

end
