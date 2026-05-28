import Stokes.BoundaryChart.TransitionDerivative

/-!
# Boundary chart Jacobian change-of-variables bridge

This file exposes the thinnest boundary-chart wrapper around mathlib's
Euclidean change-of-variables theorem.  The existing target-box COV statements
in `ChangeOfVariables.lean` already use
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`; here we keep a
setwise image-integral theorem and projection wrappers for the local COV data.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Setwise boundary-chart COV bridge.

The only analytic input is mathlib's
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`; the orientation
hypothesis rewrites its absolute determinant into the oriented tangential
Jacobian used by the boundary Stokes layer.
-/
theorem boundaryChartTransition_image_integral_eq_jacobian_integral_on
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) (s : Set (Fin n → Real))
    (hmeas : MeasurableSet s)
    (hderiv : ∀ u ∈ s,
      HasFDerivWithinAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) s u)
    (hinj : InjOn (boundaryChartTransition I x0 x1) s)
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 s) :
    (∫ v in (boundaryChartTransition I x0 x1) '' s,
        boundaryChartInChartIntegrand I x1 ω v) =
      ∫ u in s, boundaryChartTransitionJacobianIntegrand I x0 x1 ω u := by
  rw [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
    (μ := volume)
    (s := s)
    (f := boundaryChartTransition I x0 x1)
    (f' := boundaryChartTransitionTangentMap I x0 x1)
    hmeas hderiv hinj
    (boundaryChartInChartIntegrand I x1 ω)]
  refine MeasureTheory.setIntegral_congr_fun hmeas ?_
  intro u hu
  change
    |(boundaryChartTransitionTangentMap I x0 x1 u :
        (Fin n → Real) →L[Real] (Fin n → Real)).det| •
        boundaryChartInChartIntegrand I x1 ω (boundaryChartTransition I x0 x1 u) =
      boundaryChartTransitionJacobianIntegrand I x0 x1 ω u
  rw [abs_det_boundaryChartTransitionTangentMap_eq_jacobian_of_orientation
    I x0 x1 horient hu]
  simp [boundaryChartTransitionJacobianIntegrand, smul_eq_mul]

/--
Version using the fieldized derivative bridge from `TransitionDerivative.lean`.
-/
theorem boundaryChartTransition_image_integral_eq_jacobian_integral_of_derivativeData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} (ω : ManifoldForm I M n) {s : Set (Fin n → Real)}
    (hmeas : MeasurableSet s)
    (hderiv : BoundaryChartTransitionDerivativeDataOn I x0 x1 s)
    (hinj : InjOn (boundaryChartTransition I x0 x1) s)
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 s) :
    (∫ v in (boundaryChartTransition I x0 x1) '' s,
        boundaryChartInChartIntegrand I x1 ω v) =
      ∫ u in s, boundaryChartTransitionJacobianIntegrand I x0 x1 ω u :=
  boundaryChartTransition_image_integral_eq_jacobian_integral_on
    I x0 x1 ω s hmeas hderiv.hasFDerivWithinAt hinj horient

namespace BoundaryChartOrientationCovData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b c d : Fin (n + 1) → Real}

/--
Projection from orientation-COV data to the direct image-integral Jacobian COV
identity, before replacing the image by the selected target box.
-/
theorem image_integral_eq_jacobian_integral
    (data : BoundaryChartOrientationCovData I x0 x1 a b c d)
    (ω : ManifoldForm I M n) :
    (∫ v in (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b,
        boundaryChartInChartIntegrand I x1 ω v) =
      ∫ u in lowerZeroFaceDomain a b,
        boundaryChartTransitionJacobianIntegrand I x0 x1 ω u :=
  boundaryChartTransition_image_integral_eq_jacobian_integral_on
    I x0 x1 ω (lowerZeroFaceDomain a b)
    (by simp [lowerZeroFaceDomain, faceDomain])
    data.hasFDerivWithinAt data.injOn data.orientationCompatibleOn

/--
Symmetric reporting form of `image_integral_eq_jacobian_integral`.
-/
theorem jacobian_integral_eq_image_integral
    (data : BoundaryChartOrientationCovData I x0 x1 a b c d)
    (ω : ManifoldForm I M n) :
    (∫ u in lowerZeroFaceDomain a b,
        boundaryChartTransitionJacobianIntegrand I x0 x1 ω u) =
      ∫ v in (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b,
        boundaryChartInChartIntegrand I x1 ω v :=
  (data.image_integral_eq_jacobian_integral ω).symm

end BoundaryChartOrientationCovData

namespace BoundaryChartOrientationCovLocalInverseData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b c d : Fin (n + 1) → Real}

/--
Local-inverse data projected to the direct image-integral Jacobian COV identity.
-/
theorem image_integral_eq_jacobian_integral
    (data : BoundaryChartOrientationCovLocalInverseData I x0 x1 a b c d)
    (ω : ManifoldForm I M n) :
    (∫ v in (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b,
        boundaryChartInChartIntegrand I x1 ω v) =
      ∫ u in lowerZeroFaceDomain a b,
        boundaryChartTransitionJacobianIntegrand I x0 x1 ω u :=
  data.toOrientationCovData.image_integral_eq_jacobian_integral ω

end BoundaryChartOrientationCovLocalInverseData

namespace BoundaryChartSelectedBoxOrientationCovData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real}

/--
Selected-box COV data projected to the direct image-integral Jacobian COV
identity.
-/
theorem image_integral_eq_jacobian_integral [IsManifold I 1 M]
    (data : BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d) :
    (∫ v in (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b,
        boundaryChartInChartIntegrand I x1 ω v) =
      ∫ u in lowerZeroFaceDomain a b,
        boundaryChartTransitionJacobianIntegrand I x0 x1 ω u :=
  data.toOrientationCovData.image_integral_eq_jacobian_integral ω

end BoundaryChartSelectedBoxOrientationCovData

end ManifoldBoundary

end Stokes

end
