import Stokes.Global.CoverIndexedClosedBoxRegularityConstructor
import Stokes.Global.CoverIndexedLocalizedSupportRefinement

/-!
# Regularity constructors for localized refined boundary boxes

This module is the localized-support analogue of the open-interior refined
route.  It turns chartwise smoothness of the base form, smoothness of the
refined scalar coefficient, and honest closed-box regularity into the exact
`HalfSpaceBoxInteriorStokesFields` consumed by the half-space local Stokes
theorem.

The closed-box input is deliberate.  Smoothness on the coordinate open box is
enough for the `extDeriv` bulk-integral bridge, but it does not manufacture
continuity of the signed coefficients on `Icc` or integrability of the
`fderiv`-based coordinate divergence on `Icc`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section LocalizedRefinedRegularity

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

namespace CoverIndexedBoundaryBoxRefinedPartition

variable
  (D :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P omega BoundaryPiece)
  {U :
    CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece ->
      Set (Fin (n + 1) -> Real)}

/--
Interior Stokes fields from the already grouped open-interior refined
smoothness record plus the separate closed-box regularity record.

This is the smallest constructor for the localized route: support is supplied
by the refined partition itself, while regularity is converted to the
bottom-level Euclidean fields.
-/
def interiorFields_of_refinedSmoothness_closedBoxRegularity
    [IsManifold I ⊤ M]
    (S : CoverIndexedBoundaryBoxRefinedSmoothnessFields D U)
    (R : CoverIndexedBoundaryBoxRefinedClosedBoxRegularityFields D)
    (hUopen :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i -> IsOpen (U i q))
    (hOpenBox :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
          halfSpaceBoxOpenInterior (D.lower i q) (D.upper i q) ⊆ U i q) :
    forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
      forall q, q ∈ D.boundaryPieces i ->
        HalfSpaceBoxInteriorStokesFields
          (ManifoldForm.transitionPullbackInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
          (D.lower i q) (D.upper i q) :=
  D.interiorFields_of_openInteriorSmoothness
    (D.openInteriorSmoothnessFields_of_refinedSmoothness S R hUopen hOpenBox)

/--
Open-interior smoothness fields generated from chartwise smoothness, transition
coefficient smoothness on an open-interior neighborhood, and transition
coefficient smoothness on each closed box.
-/
def openInteriorSmoothnessFields_of_chartwiseSmooth_transitionCoefficient_closedBox
    [IsManifold I ⊤ M]
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (hUopen :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i -> IsOpen (U i q))
    (hOpenBox :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
          halfSpaceBoxOpenInterior (D.lower i q) (D.upper i q) ⊆ U i q)
    (hUtarget :
      forall i q, q ∈ D.boundaryPieces i ->
        U i q ⊆ (extChartAt I (D.sourceChart i q)).target)
    (hUoverlap :
      forall i q, q ∈ D.boundaryPieces i ->
        U i q ⊆
          ManifoldForm.chartOverlap I (D.sourceChart i q) (D.targetChart i q))
    (hcoeffU :
      forall i q, q ∈ D.boundaryPieces i ->
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionCoefficientInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.coefficient i q))
          (U i q))
    (hcoeffIcc :
      forall i q, q ∈ D.boundaryPieces i ->
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionCoefficientInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.coefficient i q))
          (Icc (D.lower i q) (D.upper i q))) :
    forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
      forall q, q ∈ D.boundaryPieces i ->
        HalfSpaceBoxOpenInteriorSmoothnessFields
          (ManifoldForm.transitionPullbackInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
          (D.lower i q) (D.upper i q) := by
  let R : CoverIndexedBoundaryBoxRefinedClosedBoxRegularityFields D :=
    D.closedBoxRegularityFields_of_chartwiseSmooth
      (I := I) (K := K) (omega := omega) homega hcoeffIcc
  exact
    D.openInteriorSmoothnessFields_of_chartwiseSmooth
      (I := I) (K := K) (omega := omega)
      homega R hUopen hOpenBox hUtarget hUoverlap hcoeffU

/--
Interior Stokes fields generated from chartwise smoothness, transition
coefficient smoothness on an open-interior neighborhood, and transition
coefficient smoothness on each closed box.
-/
def interiorFields_of_chartwiseSmooth_transitionCoefficient_closedBox
    [IsManifold I ⊤ M]
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (hUopen :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i -> IsOpen (U i q))
    (hOpenBox :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
          halfSpaceBoxOpenInterior (D.lower i q) (D.upper i q) ⊆ U i q)
    (hUtarget :
      forall i q, q ∈ D.boundaryPieces i ->
        U i q ⊆ (extChartAt I (D.sourceChart i q)).target)
    (hUoverlap :
      forall i q, q ∈ D.boundaryPieces i ->
        U i q ⊆
          ManifoldForm.chartOverlap I (D.sourceChart i q) (D.targetChart i q))
    (hcoeffU :
      forall i q, q ∈ D.boundaryPieces i ->
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionCoefficientInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.coefficient i q))
          (U i q))
    (hcoeffIcc :
      forall i q, q ∈ D.boundaryPieces i ->
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionCoefficientInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.coefficient i q))
          (Icc (D.lower i q) (D.upper i q))) :
    forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
      forall q, q ∈ D.boundaryPieces i ->
        HalfSpaceBoxInteriorStokesFields
          (ManifoldForm.transitionPullbackInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
          (D.lower i q) (D.upper i q) :=
  D.interiorFields_of_openInteriorSmoothness
    (D.openInteriorSmoothnessFields_of_chartwiseSmooth_transitionCoefficient_closedBox
      (I := I) (K := K) (omega := omega)
      homega hUopen hOpenBox hUtarget hUoverlap hcoeffU hcoeffIcc)

/--
Interior Stokes fields generated from chartwise smoothness and source-chart
coefficient smoothness.  The stored closed-box geometry of `D` converts the
closed-box source-chart coefficient smoothness into the required transition
closed-box regularity.
-/
def interiorFields_of_chartwiseSmooth_coefficientInChart_closedBox
    [IsManifold I ⊤ M]
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (hUopen :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i -> IsOpen (U i q))
    (hOpenBox :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
          halfSpaceBoxOpenInterior (D.lower i q) (D.upper i q) ⊆ U i q)
    (hUtarget :
      forall i q, q ∈ D.boundaryPieces i ->
        U i q ⊆ (extChartAt I (D.sourceChart i q)).target)
    (hUoverlap :
      forall i q, q ∈ D.boundaryPieces i ->
        U i q ⊆
          ManifoldForm.chartOverlap I (D.sourceChart i q) (D.targetChart i q))
    (hcoeffU :
      forall i q, q ∈ D.boundaryPieces i ->
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.coefficientInChart I
            (D.sourceChart i q) (D.coefficient i q))
          (U i q))
    (hcoeffIcc :
      forall i q, q ∈ D.boundaryPieces i ->
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.coefficientInChart I
            (D.sourceChart i q) (D.coefficient i q))
          (Icc (D.lower i q) (D.upper i q))) :
    forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
      forall q, q ∈ D.boundaryPieces i ->
        HalfSpaceBoxInteriorStokesFields
          (ManifoldForm.transitionPullbackInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
          (D.lower i q) (D.upper i q) := by
  let R : CoverIndexedBoundaryBoxRefinedClosedBoxRegularityFields D :=
    D.closedBoxRegularityFields_of_coefficientInChart
      (I := I) (K := K) (omega := omega) homega hcoeffIcc
  refine
    D.interiorFields_of_openInteriorSmoothness
      (D.openInteriorSmoothnessFields_of_chartwiseSmooth
        (I := I) (K := K) (omega := omega)
        homega R hUopen hOpenBox hUtarget hUoverlap ?_)
  intro i q hq
  exact (hcoeffU i q hq).congr fun y hy =>
    ManifoldForm.transitionCoefficientInChart_eq_coefficientInChart_of_mem_overlap
      (I := I) (ρ := D.coefficient i q) (y := y) (hUoverlap i q hq hy)

/--
Localized-support finite-sum Stokes from grouped refined smoothness plus
closed-box regularity.
-/
theorem localizedRefinedStokes_of_refinedSmoothness_closedBoxRegularity
    [IsManifold I ⊤ M]
    (S : CoverIndexedBoundaryBoxRefinedSmoothnessFields D U)
    (R : CoverIndexedBoundaryBoxRefinedClosedBoxRegularityFields D)
    (hUopen :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i -> IsOpen (U i q))
    (hOpenBox :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
          halfSpaceBoxOpenInterior (D.lower i q) (D.upper i q) ⊆ U i q) :
    (Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBulkTerm i q) =
      Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBoundaryTerm i q := by
  classical
  exact
    D.boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_localizedSupport_interiorFields
      (D.interiorFields_of_refinedSmoothness_closedBoxRegularity
        (I := I) (K := K) (omega := omega)
        S R hUopen hOpenBox)

/--
Localized-support finite-sum Stokes from chartwise smoothness and transition
coefficient smoothness on both the open-interior neighborhood and the closed
box.
-/
theorem localizedRefinedStokes_of_chartwiseSmooth_transitionCoefficient_closedBox
    [IsManifold I ⊤ M]
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (hUopen :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i -> IsOpen (U i q))
    (hOpenBox :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
          halfSpaceBoxOpenInterior (D.lower i q) (D.upper i q) ⊆ U i q)
    (hUtarget :
      forall i q, q ∈ D.boundaryPieces i ->
        U i q ⊆ (extChartAt I (D.sourceChart i q)).target)
    (hUoverlap :
      forall i q, q ∈ D.boundaryPieces i ->
        U i q ⊆
          ManifoldForm.chartOverlap I (D.sourceChart i q) (D.targetChart i q))
    (hcoeffU :
      forall i q, q ∈ D.boundaryPieces i ->
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionCoefficientInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.coefficient i q))
          (U i q))
    (hcoeffIcc :
      forall i q, q ∈ D.boundaryPieces i ->
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionCoefficientInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.coefficient i q))
          (Icc (D.lower i q) (D.upper i q))) :
    (Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBulkTerm i q) =
      Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBoundaryTerm i q := by
  classical
  exact
    D.boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_localizedSupport_interiorFields
      (D.interiorFields_of_chartwiseSmooth_transitionCoefficient_closedBox
        (I := I) (K := K) (omega := omega)
        homega hUopen hOpenBox hUtarget hUoverlap hcoeffU hcoeffIcc)

/--
Localized-support finite-sum Stokes from chartwise smoothness and source-chart
coefficient smoothness on both the open-interior neighborhood and the closed
box.
-/
theorem localizedRefinedStokes_of_chartwiseSmooth_coefficientInChart_closedBox
    [IsManifold I ⊤ M]
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (hUopen :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i -> IsOpen (U i q))
    (hOpenBox :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
          halfSpaceBoxOpenInterior (D.lower i q) (D.upper i q) ⊆ U i q)
    (hUtarget :
      forall i q, q ∈ D.boundaryPieces i ->
        U i q ⊆ (extChartAt I (D.sourceChart i q)).target)
    (hUoverlap :
      forall i q, q ∈ D.boundaryPieces i ->
        U i q ⊆
          ManifoldForm.chartOverlap I (D.sourceChart i q) (D.targetChart i q))
    (hcoeffU :
      forall i q, q ∈ D.boundaryPieces i ->
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.coefficientInChart I
            (D.sourceChart i q) (D.coefficient i q))
          (U i q))
    (hcoeffIcc :
      forall i q, q ∈ D.boundaryPieces i ->
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.coefficientInChart I
            (D.sourceChart i q) (D.coefficient i q))
          (Icc (D.lower i q) (D.upper i q))) :
    (Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBulkTerm i q) =
      Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBoundaryTerm i q := by
  classical
  exact
    D.boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_localizedSupport_interiorFields
      (D.interiorFields_of_chartwiseSmooth_coefficientInChart_closedBox
        (I := I) (K := K) (omega := omega)
        homega hUopen hOpenBox hUtarget hUoverlap hcoeffU hcoeffIcc)

end CoverIndexedBoundaryBoxRefinedPartition

end LocalizedRefinedRegularity

end Stokes

end
