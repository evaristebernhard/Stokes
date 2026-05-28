import Stokes.Global.CoverIndexedZeroCompactRawAmbientOpen
import Stokes.Global.CoverIndexedClosedBoxRegularityConstructor

/-!
# Natural raw compact-support represented Stokes adapters

This file removes the large per-box `HalfSpaceBoxOpenInteriorSmoothnessFields`
certificate from the raw selected-cover represented Stokes theorem.

The only remaining analytic package is the small closed-box regularity record:
continuity of the signed coordinate coefficients on each closed source box and
integrability of the coordinate divergence there.  This is the genuine
boundary regularity that cannot be recovered from open-interior smoothness
alone.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section RawSelectedCoverNatural

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable [FiniteDimensional Real (Fin (n + 1) → Real)]
variable [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]

namespace CoverIndexedZeroCompactRepresentedStokesRawInput

variable
    (X :
      CoverIndexedZeroCompactRepresentedStokesRawInput
        (I := I) (K := K) (ω := ω) C)

/--
Raw represented Stokes after generating the open-interior local Stokes fields
from chartwise smoothness and refined coefficient smoothness.

Compared with `representedStokes_openInteriorSmoothness`, callers no longer
provide the per-refined-box `HalfSpaceBoxOpenInteriorSmoothnessFields`.  The
small closed-box regularity record is retained because it is the exact
`fderiv`-boundary regularity not implied by smoothness on the coordinate open
box.
-/
theorem representedStokes_natural_fromAmbientOpen
    (A :
      (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).FiniteCoverAmbientOpenData
          (I := I) (K := K) (C := C)
          (P := X.selectedPartition (I := I) (K := K) (ω := ω)))
    (R :
      CoverIndexedBoundaryBoxRefinedClosedBoxRegularityFields
        (I := I) (K := K) (omega := ω) (C := C)
        (P := X.selectedPartition (I := I) (K := K) (ω := ω))
        (X.refinedPartitionWithGlobalSupportCarrier
          (I := I) (K := K) (ω := ω) A)) :
    X.representedBulkIntegral (I := I) (K := K) (ω := ω) A =
      X.representedBoundaryIntegral (I := I) (K := K) (ω := ω) A := by
  classical
  let D := X.refinedPartitionWithGlobalSupportCarrier
    (I := I) (K := K) (ω := ω) A
  let S := X.smoothRefinementFromAmbientOpenData
    (I := I) (K := K) (ω := ω) A
  refine
    X.representedStokes_openInteriorSmoothness
      (I := I) (K := K) (ω := ω) A ?_
  let hfields :=
    D.openInteriorSmoothnessFieldsOnOpenBox_of_chartwiseSmooth
      (I := I) (K := K) (omega := ω)
      X.base.chartwiseSmooth R ?hOpenBoxTarget ?hOpenBoxOverlap ?hcoeff
  · simpa [D] using hfields
  · intro i q hq
    have hdomain :
        Icc (D.lower i q) (D.upper i q) ⊆
          boundaryChartDomain I (D.sourceChart i q) (D.targetChart i q) :=
      D.Icc_subset_boundaryChartDomain i q hq
    exact
      (pi_Ioo_subset_Icc (D.lower i q) (D.upper i q)).trans
        (hdomain.trans
          (boundaryChartDomain_subset_target I (D.sourceChart i q) (D.targetChart i q)))
  · intro i q hq
    have hdomain :
        Icc (D.lower i q) (D.upper i q) ⊆
          boundaryChartDomain I (D.sourceChart i q) (D.targetChart i q) :=
      D.Icc_subset_boundaryChartDomain i q hq
    exact
      (pi_Ioo_subset_Icc (D.lower i q) (D.upper i q)).trans
        (hdomain.trans
          (boundaryChartDomain_subset_overlap I (D.sourceChart i q) (D.targetChart i q)))
  · intro i q hq
    have htarget :
        halfSpaceBoxOpenInterior (D.lower i q) (D.upper i q) ⊆
          (extChartAt I (D.sourceChart i q)).target := by
      have hdomain :
          Icc (D.lower i q) (D.upper i q) ⊆
            boundaryChartDomain I (D.sourceChart i q) (D.targetChart i q) :=
        D.Icc_subset_boundaryChartDomain i q hq
      exact
        (pi_Ioo_subset_Icc (D.lower i q) (D.upper i q)).trans
          (hdomain.trans
            (boundaryChartDomain_subset_target I (D.sourceChart i q) (D.targetChart i q)))
    have hoverlap :
        halfSpaceBoxOpenInterior (D.lower i q) (D.upper i q) ⊆
          ManifoldForm.chartOverlap I (D.sourceChart i q) (D.targetChart i q) := by
      have hdomain :
          Icc (D.lower i q) (D.upper i q) ⊆
            boundaryChartDomain I (D.sourceChart i q) (D.targetChart i q) :=
        D.Icc_subset_boundaryChartDomain i q hq
      exact
        (pi_Ioo_subset_Icc (D.lower i q) (D.upper i q)).trans
          (hdomain.trans
            (boundaryChartDomain_subset_overlap I (D.sourceChart i q) (D.targetChart i q)))
    have hqS : q ∈ S.boundaryPieces i := by
      simpa [D, S, refinedPartitionWithGlobalSupportCarrier]
        using hq
    have hiq : q.1 = i := by
      let F := (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).finiteHalfSpaceCover
          (I := I) (K := K) (C := C)
      have hqF : q ∈ F.sigmaBoundaryPieces i := by
        simpa [D, F] using hq
      exact (F.mem_sigmaBoundaryPieces.mp hqF).1
    have hqS_owner : q ∈ S.boundaryPieces q.1 := by
      simpa [hiq] using hqS
    have hcoeffInChart :
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.coefficientInChart I (D.sourceChart i q)
            (D.coefficient i q))
          (halfSpaceBoxOpenInterior (D.lower i q) (D.upper i q)) := by
      have hsmooth :
          ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
            (ManifoldForm.coefficientInChart I (D.sourceChart i q)
              (S.coefficient q.1 q))
            (halfSpaceBoxOpenInterior (D.lower i q) (D.upper i q)) :=
        S.contDiffOn_infty_coefficientInChart
          (I := I) q.1 hqS_owner (D.sourceChart i q) htarget
      simpa [D, refinedPartitionWithGlobalSupportCarrier] using hsmooth
    exact hcoeffInChart.congr fun y hy =>
      ManifoldForm.transitionCoefficientInChart_eq_coefficientInChart_of_mem_overlap
        (I := I) (ρ := D.coefficient i q) (y := y) (hoverlap hy)

/--
Closed-box regularity generated for a raw selected cover and a chosen
manifold-side open lift.

This removes the small `R` certificate from the represented theorem: the
localized form is `ContDiffOn` on each closed refined box because the refined
coefficient is generated by the smooth box refinement, the base form is
chartwise smooth, and the stored box geometry places `Icc` inside the self
boundary chart domain.
-/
def closedBoxRegularityFields_fromAmbientOpen
    (A :
      (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).FiniteCoverAmbientOpenData
          (I := I) (K := K) (C := C)
          (P := X.selectedPartition (I := I) (K := K) (ω := ω))) :
    CoverIndexedBoundaryBoxRefinedClosedBoxRegularityFields
      (I := I) (K := K) (omega := ω) (C := C)
      (P := X.selectedPartition (I := I) (K := K) (ω := ω))
      (X.refinedPartitionWithGlobalSupportCarrier
        (I := I) (K := K) (ω := ω) A) := by
  classical
  let D := X.refinedPartitionWithGlobalSupportCarrier
    (I := I) (K := K) (ω := ω) A
  let S := X.smoothRefinementFromAmbientOpenData
    (I := I) (K := K) (ω := ω) A
  refine
    D.closedBoxRegularityFields_of_coefficientInChart
      (I := I) (K := K) (omega := ω)
      X.base.chartwiseSmooth ?_
  intro i q hq
  have htarget :
      Icc (D.lower i q) (D.upper i q) ⊆
        (extChartAt I (D.sourceChart i q)).target := by
    exact
      (D.Icc_subset_boundaryChartDomain i q hq).trans
        (boundaryChartDomain_subset_target I (D.sourceChart i q) (D.targetChart i q))
  have hqS : q ∈ S.boundaryPieces i := by
    simpa [D, S, refinedPartitionWithGlobalSupportCarrier]
      using hq
  have hiq : q.1 = i := by
    let F := (X.generatedFromRaw
      (I := I) (K := K) (ω := ω)).finiteHalfSpaceCover
        (I := I) (K := K) (C := C)
    have hqF : q ∈ F.sigmaBoundaryPieces i := by
      simpa [D, F] using hq
    exact (F.mem_sigmaBoundaryPieces.mp hqF).1
  have hqS_owner : q ∈ S.boundaryPieces q.1 := by
    simpa [hiq] using hqS
  have hsmooth :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.coefficientInChart I (D.sourceChart i q)
          (S.coefficient q.1 q))
        (Icc (D.lower i q) (D.upper i q)) :=
    S.contDiffOn_infty_coefficientInChart
      (I := I) q.1 hqS_owner (D.sourceChart i q) htarget
  cases hiq
  simpa [D, S, refinedPartitionWithGlobalSupportCarrier,
    BoundarySmoothBoxRefinement.toRefinedPartitionOfFiniteHalfSpaceCoverWithGlobalSupportCarrier,
    CoverIndexedBoundaryBoxRefinedPartition.ofManifoldSupportControl] using hsmooth

/--
Raw represented Stokes from a supplied ambient-open lift, with closed-box
regularity generated automatically.
-/
theorem representedStokes_natural_fromAmbientOpen_autoClosedBox
    (A :
      (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).FiniteCoverAmbientOpenData
          (I := I) (K := K) (C := C)
          (P := X.selectedPartition (I := I) (K := K) (ω := ω))) :
    X.representedBulkIntegral (I := I) (K := K) (ω := ω) A =
      X.representedBoundaryIntegral (I := I) (K := K) (ω := ω) A :=
  X.representedStokes_natural_fromAmbientOpen
    (I := I) (K := K) (ω := ω) A
    (X.closedBoxRegularityFields_fromAmbientOpen
      (I := I) (K := K) (ω := ω) A)

/--
Natural selected-cover raw represented Stokes.

This theorem constructs the collar finite cover, the manifold-side open lift,
the smooth refinement, the refined partition, and the open-interior local
Stokes fields internally.  The only remaining input is the small closed-box
regularity record, which is the genuine `fderiv` regularity not forced by
open-interior smoothness.
-/
theorem representedStokes_natural
    (R :
      CoverIndexedBoundaryBoxRefinedClosedBoxRegularityFields
        (I := I) (K := K) (omega := ω) (C := C)
        (P := X.selectedPartition (I := I) (K := K) (ω := ω))
        (X.refinedPartitionWithGlobalSupportCarrier
          (I := I) (K := K) (ω := ω)
          (X.ambientOpenDataOfOpenPartPreimage
            (I := I) (K := K) (ω := ω)))) :
    X.representedBulkIntegral
        (I := I) (K := K) (ω := ω)
        (X.ambientOpenDataOfOpenPartPreimage
          (I := I) (K := K) (ω := ω)) =
      X.representedBoundaryIntegral
        (I := I) (K := K) (ω := ω)
        (X.ambientOpenDataOfOpenPartPreimage
          (I := I) (K := K) (ω := ω)) :=
  X.representedStokes_natural_fromAmbientOpen
    (I := I) (K := K) (ω := ω)
    (X.ambientOpenDataOfOpenPartPreimage
      (I := I) (K := K) (ω := ω))
    R

/--
Natural selected-cover raw represented Stokes with closed-box regularity
generated automatically.
-/
theorem representedStokes_natural_autoClosedBox :
    X.representedBulkIntegral
        (I := I) (K := K) (ω := ω)
        (X.ambientOpenDataOfOpenPartPreimage
          (I := I) (K := K) (ω := ω)) =
      X.representedBoundaryIntegral
        (I := I) (K := K) (ω := ω)
        (X.ambientOpenDataOfOpenPartPreimage
          (I := I) (K := K) (ω := ω)) :=
  X.representedStokes_natural_fromAmbientOpen_autoClosedBox
    (I := I) (K := K) (ω := ω)
    (X.ambientOpenDataOfOpenPartPreimage
      (I := I) (K := K) (ω := ω))

end CoverIndexedZeroCompactRepresentedStokesRawInput

end RawSelectedCoverNatural

end Stokes

end
