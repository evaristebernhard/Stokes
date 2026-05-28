import Stokes.Global.CoverIndexedIntrinsicRouteConstructor

/-!
# Regularity adapter for the intrinsic selected smooth-refinement route

This file supplies the per-selected-boundary-box `HalfSpaceBoxInteriorStokesFields`
argument expected by
`CoverIndexedZeroCompactRepresentedStokesIntrinsicInput.
hasIntrinsicRoute_of_selectedSmoothRefinement`.

The construction is deliberately local: the selected finite cover provides the
half-space box geometry, while `BoundarySmoothBoxRefinement` provides source
chart smoothness of the generated coefficient in the selected boundary chart.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section IntrinsicSelectedRegularityConstructor

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable [FiniteDimensional Real (Fin (n + 1) → Real)]
variable [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]

namespace CoverIndexedZeroCompactRepresentedStokesIntrinsicInput

variable
    (X :
      CoverIndexedZeroCompactRepresentedStokesIntrinsicInput
        (I := I) (ω := ω) K)

/--
The selected smooth refinement supplies the regularity fields consumed by the
intrinsic selected-refinement route.

The only structural matching hypothesis is that the smooth refinement uses the
same finite pieces as the canonical selected boundary finite cover.  The target
representative is the intrinsic self-chart representative, so no source-chart
matching field from the smooth refinement is needed.
-/
def interiorFieldsOfSelectedSmoothRefinement
    [DecidableEq
      (X.selectedBoundaryPiece (I := I) (K := K) (ω := ω))]
    (S :
      BoundarySmoothBoxRefinement
        (I := I) (K := K)
        (X.selectedCover (I := I) (K := K) (ω := ω))
        (X.selectedPartition (I := I) (K := K) (ω := ω))
        (X.selectedBoundaryPiece (I := I) (K := K) (ω := ω)))
    (boundaryPieces_eq :
      ∀ i : CoverIndexedBoundaryIndex
          (I := I) (X.selectedCover (I := I) (K := K) (ω := ω)),
        S.boundaryPieces i =
          (X.selectedBoundaryFiniteCover
            (I := I) (K := K) (ω := ω)).sigmaBoundaryPieces i) :
    ∀ i,
      i ∈ (Finset.univ :
        Finset (CoverIndexedBoundaryIndex
          (I := I) (X.selectedCover (I := I) (K := K) (ω := ω)))) →
        ∀ q,
          q ∈ (X.selectedBoundaryFiniteCover
            (I := I) (K := K) (ω := ω)).activePieces i →
            HalfSpaceBoxInteriorStokesFields
              (ManifoldForm.transitionPullbackInChart I
                ((X.selectedCover
                  (I := I) (K := K) (ω := ω)).boundaryChart i.1)
                ((X.selectedCover
                  (I := I) (K := K) (ω := ω)).boundaryChart i.1)
                (ManifoldForm.localizedForm I
                  (S.coefficient i ⟨i, q⟩) ω))
              ((X.selectedBoundaryFiniteCover
                (I := I) (K := K) (ω := ω)).lowerCorner i q)
              ((X.selectedBoundaryFiniteCover
                (I := I) (K := K) (ω := ω)).upperCorner i q) := by
  classical
  intro i _hi q hq
  let C0 := X.selectedCover (I := I) (K := K) (ω := ω)
  let F := X.selectedBoundaryFiniteCover (I := I) (K := K) (ω := ω)
  let x0 : M := C0.boundaryChart i.1
  let a : Fin (n + 1) → Real := F.lowerCorner i q
  let b : Fin (n + 1) → Real := F.upperCorner i q
  let ρ : M → Real := S.coefficient i ⟨i, q⟩
  let η :=
    ManifoldForm.transitionPullbackInChart I x0 x0
      (ManifoldForm.localizedForm I ρ ω)
  have hsigma : (⟨i, q⟩ :
      X.selectedBoundaryPiece (I := I) (K := K) (ω := ω)) ∈
        F.sigmaBoundaryPieces i := by
    exact (F.mem_sigmaBoundaryPieces (i := i) (q := ⟨i, q⟩)).mpr
      ⟨rfl, hq⟩
  have hS : (⟨i, q⟩ :
      X.selectedBoundaryPiece (I := I) (K := K) (ω := ω)) ∈
        S.boundaryPieces i := by
    rw [boundaryPieces_eq i]
    exact hsigma
  have hsource :
      Icc a b ⊆ ManifoldForm.chartTransitionSource I x0 x0 := by
    simpa [a, b, x0, C0, F, selectedBoundarySelfChart,
      selectedBoundaryFiniteCoverLower, selectedBoundaryFiniteCoverUpper] using
      X.selectedBoundaryFiniteCover_Icc_subset_chartTransitionSource
        (I := I) (K := K) (ω := ω) hsigma
  have htarget :
      Icc a b ⊆ (extChartAt I x0).target := by
    rw [← boundaryChartDomain_eq_chartTransitionSource (I := I) x0 x0] at hsource
    exact hsource.trans (boundaryChartDomain_subset_target I x0 x0)
  have hoverlap :
      Icc a b ⊆ ManifoldForm.chartOverlap I x0 x0 := by
    rw [← boundaryChartDomain_eq_chartTransitionSource (I := I) x0 x0] at hsource
    exact hsource.trans (boundaryChartDomain_subset_overlap I x0 x0)
  have hopenTarget :
      halfSpaceBoxOpenInterior a b ⊆ (extChartAt I x0).target :=
    (pi_Ioo_subset_Icc a b).trans htarget
  have hopenOverlap :
      halfSpaceBoxOpenInterior a b ⊆ ManifoldForm.chartOverlap I x0 x0 :=
    (pi_Ioo_subset_Icc a b).trans hoverlap
  have hcoeffOpen :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.coefficientInChart I x0 ρ)
        (halfSpaceBoxOpenInterior a b) := by
    simpa [ρ] using
      S.contDiffOn_infty_coefficientInChart
        (I := I) i hS x0 hopenTarget
  have hcoeffIcc :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.coefficientInChart I x0 ρ)
        (Icc a b) := by
    simpa [ρ] using
      S.contDiffOn_infty_coefficientInChart
        (I := I) i hS x0 htarget
  have htransitionCoeffOpen :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionCoefficientInChart I x0 x0 ρ)
        (halfSpaceBoxOpenInterior a b) := by
    exact hcoeffOpen.congr fun y hy =>
      ManifoldForm.transitionCoefficientInChart_eq_coefficientInChart_of_mem_overlap
        (I := I) (ρ := ρ) (y := y) (hopenOverlap hy)
  have htransitionCoeffIcc :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionCoefficientInChart I x0 x0 ρ)
        (Icc a b) := by
    exact hcoeffIcc.congr fun y hy =>
      ManifoldForm.transitionCoefficientInChart_eq_coefficientInChart_of_mem_overlap
        (I := I) (ρ := ρ) (y := y) (hoverlap hy)
  have hbaseOpen :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I x0 x0 ω)
        (halfSpaceBoxOpenInterior a b) :=
    ((X.chartwiseSmooth
      (I := I) (K := K) (ω := ω)).contDiffOn_transitionPullbackInChart_of_chartAPI
        (I := I) x0 x0 hopenTarget hopenOverlap).of_le le_top
  have hbaseIcc :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I x0 x0 ω)
        (Icc a b) :=
    ((X.chartwiseSmooth
      (I := I) (K := K) (ω := ω)).contDiffOn_transitionPullbackInChart_of_chartAPI
        (I := I) x0 x0 htarget hoverlap).of_le le_top
  have hlocalizedOpen :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞) η
        (halfSpaceBoxOpenInterior a b) := by
    exact
      ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
        (I := I)
        htransitionCoeffOpen
        hbaseOpen
  have hlocalizedIcc :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞) η (Icc a b) := by
    exact
      ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
        (I := I)
        htransitionCoeffIcc
        hbaseIcc
  have hopenFields :
      HalfSpaceBoxOpenInteriorSmoothnessFields η a b := {
    le := (F.cover i).lower_le_upper q hq
    lower_zero := (F.cover i).lowerCorner_zero q hq
    U := halfSpaceBoxOpenInterior a b
    isOpen_U := isOpen_pi_Ioo a b
    openInterior_subset_U := subset_rfl
    contDiffOn_openInterior := hlocalizedOpen
    continuous_signedCoeff :=
      continuous_signedCoeff_of_contDiffOn_Icc η a b hlocalizedIcc
    integrable_divergence :=
      integrable_divergence_of_contDiffOn_Icc η a b hlocalizedIcc
  }
  simpa [η, ρ, a, b, x0, C0, F] using
    HalfSpaceBoxInteriorStokesFields.ofOpenInteriorSmoothness hopenFields

end CoverIndexedZeroCompactRepresentedStokesIntrinsicInput

end IntrinsicSelectedRegularityConstructor

end Stokes

end
