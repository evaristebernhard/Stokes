import Stokes.Global.CoverIndexedOpenInteriorLocalStokes
import Stokes.Global.CoverIndexedZeroCompactRefinedSmoothness

/-!
# Open-interior smoothness constructors for refined boundary boxes

This file is the Agent C layer for the compact-support represented Stokes
route.  It constructs the per-refined-box
`HalfSpaceBoxOpenInteriorSmoothnessFields` package from the refined partition
geometry, chartwise smoothness, coefficient smoothness, and open-box
target/overlap containment.

The only data not generated here is the closed-box regularity consumed by
`CubeStokes.stokes_on_box`: continuity of signed coefficients on `Icc` and
integrability of the coordinate divergence on `Icc`.  Open-interior smoothness
alone does not imply those boundary facts, so they are isolated in the small
`CoverIndexedBoundaryBoxRefinedClosedBoxRegularityFields` record for the
Agent B lemma to eliminate later.
-/

noncomputable section

set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section RefinedOpenInteriorSmoothnessConstructor

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
Closed-box analytic regularity for every refined boundary box.

This is precisely the part not forced by open-interior smoothness.  A later
boundary-regularity constructor should build this record from chartwise
smoothness/relative smoothness on the boundary faces.
-/
structure CoverIndexedBoundaryBoxRefinedClosedBoxRegularityFields
    (D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P omega BoundaryPiece) where
  /-- Signed coordinate coefficients are continuous on each closed refined box. -/
  continuous_signedCoeff :
    forall i q, q ∈ D.boundaryPieces i ->
      forall k : Fin (n + 1),
        ContinuousOn
          (CubeStokes.signedCoeff
            (CubeStokes.toCoordNForm
              (ManifoldForm.transitionPullbackInChart I
                (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q)))
            k)
          (Icc (D.lower i q) (D.upper i q))
  /-- The coordinate divergence integrand is integrable on each closed box. -/
  integrable_divergence :
    forall i q, q ∈ D.boundaryPieces i ->
      IntegrableOn
        (fun x => ∑ k : Fin (n + 1),
          ((-1 : Real) ^ (k : Nat) •
            fderiv Real
              (CubeStokes.toCoordNForm
                (ManifoldForm.transitionPullbackInChart I
                  (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q)) k)
              x) (Pi.single k 1))
        (Icc (D.lower i q) (D.upper i q))

namespace CoverIndexedBoundaryBoxRefinedPartition

variable
  (D :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P omega BoundaryPiece)
  {U :
    CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece ->
      Set (Fin (n + 1) -> Real)}

/--
Build open-interior Stokes fields from an already grouped refined smoothness
record plus the remaining closed-box regularity fields.
-/
def openInteriorSmoothnessFields_of_refinedSmoothness
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
        HalfSpaceBoxOpenInteriorSmoothnessFields
          (ManifoldForm.transitionPullbackInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
          (D.lower i q) (D.upper i q) := by
  intro i hi q hq
  exact
    { le := D.lower_le_upper i q hq
      lower_zero := D.lower_zero i q hq
      U := U i q
      isOpen_U := hUopen i hi q hq
      openInterior_subset_U := hOpenBox i hi q hq
      contDiffOn_openInterior := (S.localized_contDiffOn i hq).of_le le_top
      continuous_signedCoeff := R.continuous_signedCoeff i q hq
      integrable_divergence := R.integrable_divergence i q hq }

/--
Direct constructor from chartwise smoothness, transition-coordinate coefficient
smoothness, and open-box target/overlap containment.

The closed-box regularity record is the exact Agent B dependency: once Agent B
can prove it from boundary relative smoothness, this theorem becomes a fully
automatic per-box constructor for `HalfSpaceBoxOpenInteriorSmoothnessFields`.
-/
def openInteriorSmoothnessFields_of_chartwiseSmooth
    [IsManifold I ⊤ M]
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (R : CoverIndexedBoundaryBoxRefinedClosedBoxRegularityFields D)
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
    (hcoeff :
      forall i q, q ∈ D.boundaryPieces i ->
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionCoefficientInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.coefficient i q))
          (U i q)) :
    forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
      forall q, q ∈ D.boundaryPieces i ->
        HalfSpaceBoxOpenInteriorSmoothnessFields
          (ManifoldForm.transitionPullbackInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
          (D.lower i q) (D.upper i q) := by
  intro i hi q hq
  exact
    { le := D.lower_le_upper i q hq
      lower_zero := D.lower_zero i q hq
      U := U i q
      isOpen_U := hUopen i hi q hq
      openInterior_subset_U := hOpenBox i hi q hq
      contDiffOn_openInterior :=
        ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
          (I := I) (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
          (hcoeff i q hq)
          ((homega.contDiffOn_transitionPullbackInChart_of_chartAPI
            (I := I) (D.sourceChart i q) (D.targetChart i q)
            (hUtarget i q hq) (hUoverlap i q hq)).of_le le_top)
      continuous_signedCoeff := R.continuous_signedCoeff i q hq
      integrable_divergence := R.integrable_divergence i q hq }

/--
Specialization to the coordinate open box itself as the smoothness
neighborhood.
-/
def openInteriorSmoothnessFieldsOnOpenBox_of_chartwiseSmooth
    [IsManifold I ⊤ M]
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (R : CoverIndexedBoundaryBoxRefinedClosedBoxRegularityFields D)
    (hOpenBoxTarget :
      forall i q, q ∈ D.boundaryPieces i ->
        halfSpaceBoxOpenInterior (D.lower i q) (D.upper i q) ⊆
          (extChartAt I (D.sourceChart i q)).target)
    (hOpenBoxOverlap :
      forall i q, q ∈ D.boundaryPieces i ->
        halfSpaceBoxOpenInterior (D.lower i q) (D.upper i q) ⊆
          ManifoldForm.chartOverlap I (D.sourceChart i q) (D.targetChart i q))
    (hcoeff :
      forall i q, q ∈ D.boundaryPieces i ->
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionCoefficientInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.coefficient i q))
          (halfSpaceBoxOpenInterior (D.lower i q) (D.upper i q))) :
    forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
      forall q, q ∈ D.boundaryPieces i ->
        HalfSpaceBoxOpenInteriorSmoothnessFields
          (ManifoldForm.transitionPullbackInChart I
            (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
          (D.lower i q) (D.upper i q) := by
  refine
    D.openInteriorSmoothnessFields_of_chartwiseSmooth
      (U := fun i q => halfSpaceBoxOpenInterior (D.lower i q) (D.upper i q))
      homega R ?_ ?_ hOpenBoxTarget hOpenBoxOverlap hcoeff
  · intro i _hi q _hq
    exact isOpen_pi_Ioo (D.lower i q) (D.upper i q)
  · intro i _hi q _hq
    exact subset_rfl

end CoverIndexedBoundaryBoxRefinedPartition

end RefinedOpenInteriorSmoothnessConstructor

end Stokes

end
