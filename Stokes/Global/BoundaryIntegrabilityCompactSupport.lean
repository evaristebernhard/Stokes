import Mathlib.MeasureTheory.Integral.CompactlySupported
import Stokes.BoundaryChart.JacobianCOVBridge

/-!
# Boundary integrability wrappers from compact support and continuity

This file records the small measure-theoretic wrappers needed by the global
boundary assembly layer.  The analytic content is deliberately thin: a
continuous scalar boundary integrand on a lower-zero face box is integrable
because that face box is compact, and a globally continuous compactly supported
scalar boundary integrand is integrable before restriction to any such box.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section BoundaryIntegrabilityCompactSupport

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- The scalar boundary integrand of a transition-pullback chart representative. -/
def boundaryChartTransitionPullbackIntegrand {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) (u : Fin n → Real) : Real :=
  ManifoldForm.transitionPullbackInChart I x0 x1 ω (boundaryInclusion n u)
    (boundaryTangent n)

/--
Any continuous scalar integrand on a lower-zero face box is integrable there.
-/
theorem integrableOn_lowerZeroFaceDomain_of_continuousOn {n : Nat}
    {f : (Fin n → Real) → Real} {a b : Fin (n + 1) → Real}
    (hf : ContinuousOn f (lowerZeroFaceDomain a b)) :
    IntegrableOn f (lowerZeroFaceDomain a b) :=
  hf.integrableOn_compact (isCompact_lowerZeroFaceDomain a b)

/--
A continuous compactly supported scalar integrand is integrable after
restriction to any lower-zero face box.
-/
theorem integrableOn_lowerZeroFaceDomain_of_continuous_hasCompactSupport {n : Nat}
    {f : (Fin n → Real) → Real} {a b : Fin (n + 1) → Real}
    (hf : Continuous f) (hcf : HasCompactSupport f) :
    IntegrableOn f (lowerZeroFaceDomain a b) :=
  (hf.integrable_of_hasCompactSupport hcf).integrableOn

/-- The transition-pullback boundary integrand is continuous on a lower-zero face box
when the ambient chart representative is continuous on the ambient box. -/
theorem boundaryChartTransitionPullbackIntegrand_continuousOn_lowerZeroFaceDomain
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hω :
      ContinuousOn (ManifoldForm.transitionPullbackInChart I x0 x1 ω) (Icc a b)) :
    ContinuousOn (boundaryChartTransitionPullbackIntegrand I x0 x1 ω)
      (lowerZeroFaceDomain a b) := by
  have hincl :
      ContinuousOn (boundaryInclusion n) (lowerZeroFaceDomain a b) := by
    simpa [boundaryTangentInclusion_apply] using
      (boundaryTangentInclusion n).continuous.continuousOn
  have hmaps : MapsTo (boundaryInclusion n) (lowerZeroFaceDomain a b) (Icc a b) := by
    intro u hu
    exact boundaryInclusion_mem_Icc_of_mem_lowerZeroFaceDomain ha0 hle hu
  have hcomp :
      ContinuousOn
        (fun u : Fin n → Real =>
          ManifoldForm.transitionPullbackInChart I x0 x1 ω (boundaryInclusion n u))
        (lowerZeroFaceDomain a b) :=
    hω.comp hincl hmaps
  simpa [boundaryChartTransitionPullbackIntegrand] using
    (ContinuousAlternatingMap.apply Real (Fin (n + 1) → Real) Real
      (boundaryTangent n)).continuous.comp_continuousOn hcomp

/-- Continuous transition-pullback boundary integrands are integrable on a
lower-zero face box. -/
theorem boundaryChartTransitionPullbackIntegrand_integrableOn_of_continuousOn
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hω :
      ContinuousOn (ManifoldForm.transitionPullbackInChart I x0 x1 ω) (Icc a b)) :
    IntegrableOn (boundaryChartTransitionPullbackIntegrand I x0 x1 ω)
      (lowerZeroFaceDomain a b) :=
  integrableOn_lowerZeroFaceDomain_of_continuousOn
    (boundaryChartTransitionPullbackIntegrand_continuousOn_lowerZeroFaceDomain
      I x0 x1 ω ha0 hle hω)

/-- Compact-support version for transition-pullback boundary integrands. -/
theorem boundaryChartTransitionPullbackIntegrand_integrableOn_of_compactSupport
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) {a b : Fin (n + 1) → Real}
    (hf : Continuous (boundaryChartTransitionPullbackIntegrand I x0 x1 ω))
    (hcf : HasCompactSupport (boundaryChartTransitionPullbackIntegrand I x0 x1 ω)) :
    IntegrableOn (boundaryChartTransitionPullbackIntegrand I x0 x1 ω)
      (lowerZeroFaceDomain a b) :=
  integrableOn_lowerZeroFaceDomain_of_continuous_hasCompactSupport hf hcf

/-- Extended boundary boxes make the transition-pullback boundary integrand
integrable on their lower-zero face. -/
theorem boundaryChartTransitionPullbackIntegrand_integrableOn_of_extendedBox
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartExtendedBox I x0 x1 ω a b) :
    IntegrableOn (boundaryChartTransitionPullbackIntegrand I x0 x1 ω)
      (lowerZeroFaceDomain a b) := by
  rcases hbox.exists_smooth_nhds with ⟨U, _hU, hUbox, hωU⟩
  exact boundaryChartTransitionPullbackIntegrand_integrableOn_of_continuousOn
    I x0 x1 ω hbox.selectedBox.ha0 hbox.selectedBox.le
    (hωU.continuousOn.mono hUbox)

/-- The target in-chart boundary integrand is continuous on a lower-zero face box
when the ambient chart representative is continuous on the ambient box. -/
theorem boundaryChartInChartIntegrand_continuousOn_lowerZeroFaceDomain
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x : M) (ω : ManifoldForm I M n) {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hω : ContinuousOn (ManifoldForm.inChart I x ω) (Icc a b)) :
    ContinuousOn (boundaryChartInChartIntegrand I x ω)
      (lowerZeroFaceDomain a b) := by
  have hincl :
      ContinuousOn (boundaryInclusion n) (lowerZeroFaceDomain a b) := by
    simpa [boundaryTangentInclusion_apply] using
      (boundaryTangentInclusion n).continuous.continuousOn
  have hmaps : MapsTo (boundaryInclusion n) (lowerZeroFaceDomain a b) (Icc a b) := by
    intro u hu
    exact boundaryInclusion_mem_Icc_of_mem_lowerZeroFaceDomain ha0 hle hu
  have hcomp :
      ContinuousOn
        (fun u : Fin n → Real => ManifoldForm.inChart I x ω (boundaryInclusion n u))
        (lowerZeroFaceDomain a b) :=
    hω.comp hincl hmaps
  simpa [boundaryChartInChartIntegrand] using
    (ContinuousAlternatingMap.apply Real (Fin (n + 1) → Real) Real
      (boundaryTangent n)).continuous.comp_continuousOn hcomp

/-- Continuous target in-chart boundary integrands are integrable on a
lower-zero face box. -/
theorem boundaryChartInChartIntegrand_integrableOn_of_continuousOn
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x : M) (ω : ManifoldForm I M n) {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hω : ContinuousOn (ManifoldForm.inChart I x ω) (Icc a b)) :
    IntegrableOn (boundaryChartInChartIntegrand I x ω) (lowerZeroFaceDomain a b) :=
  integrableOn_lowerZeroFaceDomain_of_continuousOn
    (boundaryChartInChartIntegrand_continuousOn_lowerZeroFaceDomain
      I x ω ha0 hle hω)

/-- Compact-support version for target in-chart boundary integrands. -/
theorem boundaryChartInChartIntegrand_integrableOn_of_compactSupport
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x : M) (ω : ManifoldForm I M n) {a b : Fin (n + 1) → Real}
    (hf : Continuous (boundaryChartInChartIntegrand I x ω))
    (hcf : HasCompactSupport (boundaryChartInChartIntegrand I x ω)) :
    IntegrableOn (boundaryChartInChartIntegrand I x ω) (lowerZeroFaceDomain a b) :=
  integrableOn_lowerZeroFaceDomain_of_continuous_hasCompactSupport hf hcf

/-- Selected target boxes plus chartwise smoothness make the target in-chart
boundary integrand integrable. -/
theorem boundaryChartInChartIntegrand_integrableOn_of_chartwiseSmooth_selectedBox
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x x' : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hω : ManifoldForm.ChartwiseSmooth I ω)
    (hbox : boundaryChartSelectedBox I x x' ω a b) :
    IntegrableOn (boundaryChartInChartIntegrand I x ω) (lowerZeroFaceDomain a b) := by
  exact boundaryChartInChartIntegrand_integrableOn_of_continuousOn
    I x ω hbox.ha0 hbox.le
    ((hω.contDiffOn_inChart (I := I) x
      (fun y hy =>
        boundaryChartDomain_subset_target I x x' (hbox.Icc_subset_domain hy))).continuousOn)

/-- A continuous Jacobian-weighted COV integrand is integrable on a lower-zero
face box. -/
theorem boundaryChartTransitionJacobianIntegrand_integrableOn_of_continuousOn
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) {a b : Fin (n + 1) → Real}
    (hcont :
      ContinuousOn (boundaryChartTransitionJacobianIntegrand I x0 x1 ω)
        (lowerZeroFaceDomain a b)) :
    IntegrableOn (boundaryChartTransitionJacobianIntegrand I x0 x1 ω)
      (lowerZeroFaceDomain a b) :=
  integrableOn_lowerZeroFaceDomain_of_continuousOn hcont

/-- Compact-support version for the Jacobian-weighted COV integrand. -/
theorem boundaryChartTransitionJacobianIntegrand_integrableOn_of_compactSupport
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) {a b : Fin (n + 1) → Real}
    (hf : Continuous (boundaryChartTransitionJacobianIntegrand I x0 x1 ω))
    (hcf : HasCompactSupport (boundaryChartTransitionJacobianIntegrand I x0 x1 ω)) :
    IntegrableOn (boundaryChartTransitionJacobianIntegrand I x0 x1 ω)
      (lowerZeroFaceDomain a b) :=
  integrableOn_lowerZeroFaceDomain_of_continuous_hasCompactSupport hf hcf

/--
Continuity of the Jacobian factor, the boundary chart transition, and the
target in-chart integrand implies integrability of the Jacobian-weighted COV
integrand on the source lower-zero face box.
-/
theorem boundaryChartTransitionJacobianIntegrand_integrableOn_of_continuous_factors
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    {a b c d : Fin (n + 1) → Real}
    (hjac :
      ContinuousOn (boundaryChartTransitionJacobian I x0 x1)
        (lowerZeroFaceDomain a b))
    (htransition :
      ContinuousOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b))
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (htarget :
      ContinuousOn (boundaryChartInChartIntegrand I x1 ω) (lowerZeroFaceDomain c d)) :
    IntegrableOn (boundaryChartTransitionJacobianIntegrand I x0 x1 ω)
      (lowerZeroFaceDomain a b) := by
  refine boundaryChartTransitionJacobianIntegrand_integrableOn_of_continuousOn
    I x0 x1 ω ?_
  simpa [boundaryChartTransitionJacobianIntegrand] using
    hjac.mul (htarget.comp htransition hmaps)

/--
Boundary local integrability package for a source lower-zero face box and its
target lower-zero face box.
-/
structure BoundaryIntegrabilityData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real) where
  /-- Integrability of the source transition-pullback boundary integrand. -/
  sourceIntegrableOn :
    IntegrableOn (boundaryChartTransitionPullbackIntegrand I x0 x1 ω)
      (lowerZeroFaceDomain a b)
  /-- Integrability of the Jacobian-weighted COV integrand on the source box. -/
  jacobianIntegrableOn :
    IntegrableOn (boundaryChartTransitionJacobianIntegrand I x0 x1 ω)
      (lowerZeroFaceDomain a b)
  /-- Integrability of the target in-chart boundary integrand on the target box. -/
  targetIntegrableOn :
    IntegrableOn (boundaryChartInChartIntegrand I x1 ω) (lowerZeroFaceDomain c d)

namespace BoundaryIntegrabilityData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real}

/-- Projection to source transition-pullback integrability. -/
theorem source_boundary_integrableOn
    (data : BoundaryIntegrabilityData I x0 x1 ω a b c d) :
    IntegrableOn (boundaryChartTransitionPullbackIntegrand I x0 x1 ω)
      (lowerZeroFaceDomain a b) :=
  data.sourceIntegrableOn

/-- Projection to Jacobian-weighted source integrability. -/
theorem jacobian_integrableOn
    (data : BoundaryIntegrabilityData I x0 x1 ω a b c d) :
    IntegrableOn (boundaryChartTransitionJacobianIntegrand I x0 x1 ω)
      (lowerZeroFaceDomain a b) :=
  data.jacobianIntegrableOn

/-- Projection to target in-chart boundary integrability. -/
theorem target_boundary_integrableOn
    (data : BoundaryIntegrabilityData I x0 x1 ω a b c d) :
    IntegrableOn (boundaryChartInChartIntegrand I x1 ω) (lowerZeroFaceDomain c d) :=
  data.targetIntegrableOn

/-- Constructor from already proved continuity of the three scalar integrands. -/
def of_continuousOn
    (hsource :
      ContinuousOn (boundaryChartTransitionPullbackIntegrand I x0 x1 ω)
        (lowerZeroFaceDomain a b))
    (hjacobian :
      ContinuousOn (boundaryChartTransitionJacobianIntegrand I x0 x1 ω)
        (lowerZeroFaceDomain a b))
    (htarget :
      ContinuousOn (boundaryChartInChartIntegrand I x1 ω) (lowerZeroFaceDomain c d)) :
    BoundaryIntegrabilityData I x0 x1 ω a b c d where
  sourceIntegrableOn := integrableOn_lowerZeroFaceDomain_of_continuousOn hsource
  jacobianIntegrableOn := integrableOn_lowerZeroFaceDomain_of_continuousOn hjacobian
  targetIntegrableOn := integrableOn_lowerZeroFaceDomain_of_continuousOn htarget

/-- Constructor from continuous compactly supported scalar integrands. -/
def of_compactSupport
    (hsource :
      Continuous (boundaryChartTransitionPullbackIntegrand I x0 x1 ω))
    (hsourceCompact :
      HasCompactSupport (boundaryChartTransitionPullbackIntegrand I x0 x1 ω))
    (hjacobian :
      Continuous (boundaryChartTransitionJacobianIntegrand I x0 x1 ω))
    (hjacobianCompact :
      HasCompactSupport (boundaryChartTransitionJacobianIntegrand I x0 x1 ω))
    (htarget :
      Continuous (boundaryChartInChartIntegrand I x1 ω))
    (htargetCompact :
      HasCompactSupport (boundaryChartInChartIntegrand I x1 ω)) :
    BoundaryIntegrabilityData I x0 x1 ω a b c d where
  sourceIntegrableOn :=
    boundaryChartTransitionPullbackIntegrand_integrableOn_of_compactSupport
      I x0 x1 ω hsource hsourceCompact
  jacobianIntegrableOn :=
    boundaryChartTransitionJacobianIntegrand_integrableOn_of_compactSupport
      I x0 x1 ω hjacobian hjacobianCompact
  targetIntegrableOn :=
    boundaryChartInChartIntegrand_integrableOn_of_compactSupport
      I x1 ω htarget htargetCompact

/--
Constructor from a selected/extended source box, a selected target box, and
continuity of the tangential Jacobian factor.
-/
def of_extendedBox_chartwiseSmooth_targetBox
    [IsManifold I 1 M]
    {x2 : M}
    (hsource : boundaryChartExtendedBox I x0 x1 ω a b)
    (htarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (hω : ManifoldForm.ChartwiseSmooth I ω)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hjac :
      ContinuousOn (boundaryChartTransitionJacobian I x0 x1)
        (lowerZeroFaceDomain a b)) :
    BoundaryIntegrabilityData I x0 x1 ω a b c d where
  sourceIntegrableOn :=
    boundaryChartTransitionPullbackIntegrand_integrableOn_of_extendedBox hsource
  jacobianIntegrableOn :=
    boundaryChartTransitionJacobianIntegrand_integrableOn_of_continuous_factors
      I x0 x1 ω hjac
      (boundaryChartTransition_continuousOn_of_selectedBox hsource.selectedBox)
      hmaps
      (boundaryChartInChartIntegrand_continuousOn_lowerZeroFaceDomain I x1 ω
        htarget.ha0 htarget.le
        ((hω.contDiffOn_inChart (I := I) x1
          (fun _ hy =>
            boundaryChartDomain_subset_target I x1 x2
              (htarget.Icc_subset_domain hy))).continuousOn))
  targetIntegrableOn :=
    boundaryChartInChartIntegrand_integrableOn_of_chartwiseSmooth_selectedBox
      hω htarget

end BoundaryIntegrabilityData

end BoundaryIntegrabilityCompactSupport

end Stokes

end
