import Stokes.BoundaryChart.LocalInverse

/-!
# Boundary chart change of variables

This file was split out of Stokes.HalfSpace as part of the M6.0
module-structure pass.  The theorem statements and proofs are intended to
remain identical to the monolithic version.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- The scalar boundary integrand of a manifold form in a fixed chart. -/
def boundaryChartInChartIntegrand {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 : M) (ω : ManifoldForm I M n) (u : Fin n → Real) : Real :=
  ManifoldForm.inChart I x0 ω (boundaryInclusion n u) (boundaryTangent n)

/-- The Jacobian-weighted target-chart boundary integrand under a chart change. -/
def boundaryChartTransitionJacobianIntegrand {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) (u : Fin n → Real) : Real :=
  boundaryChartTransitionJacobian I x0 x1 u *
    boundaryChartInChartIntegrand I x1 ω (boundaryChartTransition I x0 x1 u)

/--
On an orientation-compatible boundary chart transition, mathlib's absolute
Jacobian is the oriented tangential Jacobian used by the Stokes boundary term.
-/
theorem abs_det_boundaryChartTransitionTangentMap_eq_jacobian_of_orientation {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) {s : Set (Fin n → Real)}
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 s)
    {u : Fin n → Real} (hu : u ∈ s) :
    |(boundaryChartTransitionTangentMap I x0 x1 u :
        (Fin n → Real) →L[Real] (Fin n → Real)).det| =
      boundaryChartTransitionJacobian I x0 x1 u := by
  change
    |LinearMap.det
      (boundaryChartTransitionTangentMap I x0 x1 u :
        (Fin n → Real) →ₗ[Real] (Fin n → Real))| =
      boundaryChartTransitionJacobian I x0 x1 u
  rw [← boundaryChartTransitionMatrix_det_eq_linearMap_det]
  exact abs_of_pos (horient u hu)

/--
Mathlib change-of-variables bridge for boundary chart integrals.

The analytic work is delegated to
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`; the positivity
hypothesis rewrites its absolute Jacobian into our oriented boundary Jacobian.
-/
theorem boundaryChartTransition_image_integral_eq_jacobian_integral_of_changeOfVariables
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b : Fin (n + 1) → Real)
    (hderiv : ∀ u ∈ lowerZeroFaceDomain a b,
      HasFDerivWithinAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u)
        (lowerZeroFaceDomain a b) u)
    (hinj : InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b))
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b)) :
    (∫ v in (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b,
        boundaryChartInChartIntegrand I x1 ω v) =
      ∫ u in lowerZeroFaceDomain a b,
        boundaryChartTransitionJacobianIntegrand I x0 x1 ω u := by
  rw [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
    (μ := volume)
    (s := lowerZeroFaceDomain a b)
    (f := boundaryChartTransition I x0 x1)
    (f' := boundaryChartTransitionTangentMap I x0 x1)
    (by simp [lowerZeroFaceDomain, faceDomain]) hderiv hinj
    (boundaryChartInChartIntegrand I x1 ω)]
  refine MeasureTheory.setIntegral_congr_fun (by simp [lowerZeroFaceDomain, faceDomain]) ?_
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
The target-box version of the boundary chart change-of-variables formula.  This
is the old final field of `boundaryChartOrientedChangeOfVariables`, now derived
from mathlib's change-of-variables theorem plus the image-of-box hypothesis.
-/
theorem boundaryChartTransition_jacobian_integral_eq_inChart_of_changeOfVariables
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hderiv : ∀ u ∈ lowerZeroFaceDomain a b,
      HasFDerivWithinAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u)
        (lowerZeroFaceDomain a b) u)
    (hinj : InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b))
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (himage : (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
      lowerZeroFaceDomain c d) :
    (∫ u in lowerZeroFaceDomain a b,
        boundaryChartTransitionJacobianIntegrand I x0 x1 ω u) =
      halfSpaceBoundaryInChartIntegral I x1 ω c d := by
  rw [← boundaryChartTransition_image_integral_eq_jacobian_integral_of_changeOfVariables
    I x0 x1 ω a b hderiv hinj horient]
  rw [himage]
  rfl

/--
The local oriented change-of-variables package for boundary chart integrals.

This deliberately separates the measure-theoretic change-of-variables theorem
from the form algebra.  The first two fields say the boundary chart transition
is pointwise compatible with the boundary and preserves orientation; the final
field is supplied by mathlib's change-of-variables theorem through
`boundaryChartTransition_jacobian_integral_eq_inChart_of_changeOfVariables`.
-/
def boundaryChartOrientedChangeOfVariables {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real) : Prop :=
  boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) ∧
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) ∧
      (∫ u in lowerZeroFaceDomain a b,
          boundaryChartTransitionJacobianIntegrand I x0 x1 ω u) =
        halfSpaceBoundaryInChartIntegral I x1 ω c d

/--
Construct the oriented boundary chart change-of-variables package from the
pointwise boundary compatibility hypotheses and mathlib's Euclidean
change-of-variables theorem.
-/
theorem boundaryChartOrientedChangeOfVariables_of_changeOfVariables {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hderiv : ∀ u ∈ lowerZeroFaceDomain a b,
      HasFDerivWithinAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u)
        (lowerZeroFaceDomain a b) u)
    (hinj : InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b))
    (himage : (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
      lowerZeroFaceDomain c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  ⟨hcompat, horient,
    boundaryChartTransition_jacobian_integral_eq_inChart_of_changeOfVariables
      I x0 x1 ω a b c d hderiv hinj horient himage⟩

/--
Orientation-API version of the local boundary chart change-of-variables
constructor.  The positive-Jacobian hypothesis is obtained from preservation of
the finite boundary-coordinate orientation frame.
-/
theorem boundaryChartOrientedChangeOfVariables_of_preservesOrientation_changeOfVariables
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (horient : boundaryChartPreservesOrientationOn I x0 x1 (lowerZeroFaceDomain a b))
    (hderiv : ∀ u ∈ lowerZeroFaceDomain a b,
      HasFDerivWithinAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u)
        (lowerZeroFaceDomain a b) u)
    (hinj : InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b))
    (himage : (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
      lowerZeroFaceDomain c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  boundaryChartOrientedChangeOfVariables_of_changeOfVariables I x0 x1 ω a b c d
    hcompat
    (boundaryChartOrientationCompatibleOn_of_preservesOrientationOn I x0 x1 horient)
    hderiv hinj himage

/--
Selected-box version of the oriented boundary chart change-of-variables
constructor: the Frechet-derivative hypothesis is discharged from the chart API.
-/
theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_changeOfVariables
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hinj : InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b))
    (himage : (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
      lowerZeroFaceDomain c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  boundaryChartOrientedChangeOfVariables_of_changeOfVariables I x0 x1 ω a b c d
    hcompat horient
    (boundaryChartTransition_hasFDerivWithinAt_of_selectedBox hbox)
    hinj himage

theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_preservesOrientation_changeOfVariables
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (horient : boundaryChartPreservesOrientationOn I x0 x1 (lowerZeroFaceDomain a b))
    (hinj : InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b))
    (himage : (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
      lowerZeroFaceDomain c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_changeOfVariables
    x0 x1 ω a b c d hbox hcompat
    (boundaryChartOrientationCompatibleOn_of_preservesOrientationOn I x0 x1 horient)
    hinj himage

/--
Selected-box constructor using the natural local box-bijection data.  The
derivative and injectivity hypotheses are supplied by the chart API; the image
of the source boundary box is obtained from `MapsTo` and `SurjOn`.
-/
theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_surjOn_changeOfVariables
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hsurj : SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_changeOfVariables
    x0 x1 ω a b c d hbox hcompat horient
    (boundaryChartTransition_injOn_of_selectedBox_compatibleOn hbox hcompat)
    (boundaryChartTransition_image_eq_lowerZeroFaceDomain_of_mapsTo_surjOn
      I x0 x1 a b c d hmaps hsurj)

theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_preservesOrientation_surjOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (horient : boundaryChartPreservesOrientationOn I x0 x1 (lowerZeroFaceDomain a b))
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hsurj : SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_surjOn_changeOfVariables
    x0 x1 ω a b c d hbox hcompat
    (boundaryChartOrientationCompatibleOn_of_preservesOrientationOn I x0 x1 horient)
    hmaps hsurj

/--
Selected-box constructor from oriented boundary-atlas data and local
surjectivity onto the target boundary box.  The atlas supplies both the
boundary-face compatibility and the positive orientation of the chart change.
-/
theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedAtlas_surjOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hsurj : SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_surjOn_changeOfVariables
    x0 x1 ω a b c d hbox
    (A.transitionCompatibleOn_selectedBox hx0 hx1 hbox)
    (A.orientationCompatibleOn_selectedBox hx0 hx1 hbox)
    hmaps hsurj

/--
Selected-box constructor from oriented boundary-atlas data and packaged local
boundary-box image data.
-/
theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedAtlas_imageData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedAtlas_surjOn
    A hx0 hx1 ω a b c d hbox himage.mapsTo himage.surjOn

theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedAtlas_localInverse
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedAtlas_imageData
    A hx0 hx1 ω a b c d hbox
    (boundaryChartSelectedBoxImageData_of_mapsTo_localInverseData hmaps hlocal)

/--
Selected-box constructor from global oriented-boundary-charted-manifold data and
local surjectivity onto the target boundary box.
-/
theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedManifold_surjOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hsurj : SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_surjOn_changeOfVariables
    x0 x1 ω a b c d hbox
    (boundaryChartTransitionCompatibleOn_selectedBox_of_orientedManifold hbox)
    (boundaryChartOrientationCompatibleOn_selectedBox_of_orientedManifold hbox)
    hmaps hsurj

/--
Selected-box constructor from global oriented-boundary-charted-manifold data and
packaged local boundary-box image data.
-/
theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedManifold_imageData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedManifold_surjOn
    x0 x1 ω a b c d hbox himage.mapsTo himage.surjOn

theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedManifold_localInverse
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedManifold_imageData
    x0 x1 ω a b c d hbox
    (boundaryChartSelectedBoxImageData_of_mapsTo_localInverseData hmaps hlocal)

/-- Selected-box constructor using packaged local boundary-box bijection data. -/
theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_bijOn_changeOfVariables
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hbij : BijOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_changeOfVariables
    x0 x1 ω a b c d hbox hcompat horient hbij.injOn
    (boundaryChartTransition_image_eq_lowerZeroFaceDomain_of_bijOn
      I x0 x1 a b c d hbij)

/--
Selected-box constructor using packaged local boundary-box bijection data and
the orientation-facing frame predicate.
-/
theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_preservesOrientation_bijOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat : boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (horient : boundaryChartPreservesOrientationOn I x0 x1 (lowerZeroFaceDomain a b))
    (hbij : BijOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_bijOn_changeOfVariables
    x0 x1 ω a b c d hbox hcompat
    (boundaryChartOrientationCompatibleOn_of_preservesOrientationOn I x0 x1 horient)
    hbij

/--
Selected-box constructor from oriented boundary-atlas data and packaged local
boundary-box bijection data.
-/
theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedAtlas_bijOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hbij : BijOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_bijOn_changeOfVariables
    x0 x1 ω a b c d hbox
    (A.transitionCompatibleOn_selectedBox hx0 hx1 hbox)
    (A.orientationCompatibleOn_selectedBox hx0 hx1 hbox)
    hbij

/--
Selected-box constructor from global oriented-boundary-charted-manifold data and
packaged local boundary-box bijection data.
-/
theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedManifold_bijOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hbij : BijOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_bijOn_changeOfVariables
    x0 x1 ω a b c d hbox
    (boundaryChartTransitionCompatibleOn_selectedBox_of_orientedManifold hbox)
    (boundaryChartOrientationCompatibleOn_selectedBox_of_orientedManifold hbox)
    hbij

/--
Non-oriented integral-level chart-change formula for the boundary term, assuming
the local oriented change-of-variables package.
-/
theorem halfSpaceBoundaryTransitionFormIntegral_eq_inChart_of_orientedChangeOfVariables
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hchange : boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d) :
    halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b =
      halfSpaceBoundaryInChartIntegral I x1 ω c d := by
  unfold halfSpaceBoundaryTransitionFormIntegral halfSpaceBoundaryFormIntegral
  rw [show
      (∫ u in lowerZeroFaceDomain a b,
          ManifoldForm.transitionPullbackInChart I x0 x1 ω (boundaryInclusion n u)
            (boundaryTangent n)) =
        ∫ u in lowerZeroFaceDomain a b,
          boundaryChartTransitionJacobianIntegrand I x0 x1 ω u from by
    refine MeasureTheory.setIntegral_congr_fun (by simp [lowerZeroFaceDomain, faceDomain]) ?_
    intro u hu
    exact boundaryChartTransition_pointwise_pullback_det
      x0 x1 ω u (hchange.1 u hu).1 (hchange.1 u hu).2]
  exact hchange.2.2

/--
Orientation-compatible chart-change formula for `outwardFirstBoundaryChartIntegral`.
-/
theorem outwardFirstBoundaryChartIntegral_eq_inChart_of_orientedChangeOfVariables
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hchange : boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      outwardFirstBoundaryInChartIntegral I x1 ω c d := by
  rw [outwardFirstBoundaryChartIntegral, outwardFirstBoundaryInChartIntegral,
    halfSpaceBoundaryTransitionFormIntegral_eq_inChart_of_orientedChangeOfVariables
      x0 x1 ω a b c d hchange]

/--
On the boundary face of a selected chart box, the transition-pulled boundary
integral is the same as the `x0` chart representative integral.  This is the
local chart-change compatibility statement before any change-of-variables
between different boundary coordinate boxes is introduced.
-/
theorem halfSpaceBoundaryTransitionFormIntegral_eq_inChart_of_boundaryFace_subset_overlap
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hoverlap : ∀ x ∈ lowerZeroFaceDomain a b,
      boundaryInclusion n x ∈ ManifoldForm.chartOverlap I x0 x1) :
    halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b =
      halfSpaceBoundaryInChartIntegral I x0 ω a b := by
  unfold halfSpaceBoundaryTransitionFormIntegral halfSpaceBoundaryInChartIntegral
    halfSpaceBoundaryFormIntegral
  refine MeasureTheory.setIntegral_congr_fun (by simp [lowerZeroFaceDomain, faceDomain]) ?_
  intro x hx
  simpa using congrArg (fun η => η (boundaryTangent n))
    (ManifoldForm.transitionPullbackInChart_eq_inChart
      (I := I) x0 x1 ω (hoverlap x hx))

theorem outwardFirstBoundaryChartIntegral_eq_inChart_of_boundaryFace_subset_overlap
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hoverlap : ∀ x ∈ lowerZeroFaceDomain a b,
      boundaryInclusion n x ∈ ManifoldForm.chartOverlap I x0 x1) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      outwardFirstBoundaryInChartIntegral I x0 ω a b := by
  rw [outwardFirstBoundaryChartIntegral, outwardFirstBoundaryInChartIntegral,
    halfSpaceBoundaryTransitionFormIntegral_eq_inChart_of_boundaryFace_subset_overlap
      x0 x1 ω a b hoverlap]

/--
Boundary-face chart-change compatibility for two auxiliary charts over the same
boundary chart and boundary box.
-/
def boundaryChartChangeCompatible {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 x2 : M) (a b : Fin (n + 1) → Real) : Prop :=
  (∀ x ∈ lowerZeroFaceDomain a b,
    boundaryInclusion n x ∈ ManifoldForm.chartOverlap I x0 x1) ∧
  (∀ x ∈ lowerZeroFaceDomain a b,
    boundaryInclusion n x ∈ ManifoldForm.chartOverlap I x0 x2)

theorem boundaryChartChangeCompatible.mk_of_selectedBoxes {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 x2 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox1 : boundaryChartSelectedBox I x0 x1 ω a b)
    (hbox2 : boundaryChartSelectedBox I x0 x2 ω a b) :
    boundaryChartChangeCompatible I x0 x1 x2 a b :=
  ⟨hbox1.boundaryFace_subset_overlap, hbox2.boundaryFace_subset_overlap⟩

theorem outwardFirstBoundaryChartIntegral_chartChange_invariant
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hcompat : boundaryChartChangeCompatible I x0 x1 x2 a b) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x0 x2 ω a b := by
  rw [outwardFirstBoundaryChartIntegral_eq_inChart_of_boundaryFace_subset_overlap
      x0 x1 ω a b hcompat.1,
    outwardFirstBoundaryChartIntegral_eq_inChart_of_boundaryFace_subset_overlap
      x0 x2 ω a b hcompat.2]

theorem outwardFirstBoundaryChartIntegral_chartChange_invariant_of_selectedBoxes
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hbox1 : boundaryChartSelectedBox I x0 x1 ω a b)
    (hbox2 : boundaryChartSelectedBox I x0 x2 ω a b) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x0 x2 ω a b :=
  outwardFirstBoundaryChartIntegral_chartChange_invariant x0 x1 x2 ω a b
    (boundaryChartChangeCompatible.mk_of_selectedBoxes hbox1 hbox2)

theorem outwardFirstBoundaryChartIntegral_chartChange_invariant_of_extendedBoxes
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hbox1 : boundaryChartExtendedBox I x0 x1 ω a b)
    (hbox2 : boundaryChartExtendedBox I x0 x2 ω a b) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x0 x2 ω a b :=
  outwardFirstBoundaryChartIntegral_chartChange_invariant_of_selectedBoxes
    x0 x1 x2 ω a b hbox1.selectedBox hbox2.selectedBox

/--
Integral-level boundary chart-change invariance.

The source boundary chart `x0` is changed to the target boundary chart `x1`;
the auxiliary chart `x2` is only used to write the target-side
transition-pullback representative.  The actual change-of-variables work is
packaged in `boundaryChartOrientedChangeOfVariables`.
-/
theorem outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hchange : boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d)
    (hoverlap : ∀ u ∈ lowerZeroFaceDomain c d,
      boundaryInclusion n u ∈ ManifoldForm.chartOverlap I x1 x2) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d := by
  rw [outwardFirstBoundaryChartIntegral_eq_inChart_of_orientedChangeOfVariables
      x0 x1 ω a b c d hchange,
    outwardFirstBoundaryChartIntegral_eq_inChart_of_boundaryFace_subset_overlap
      x1 x2 ω c d hoverlap]

theorem
    outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables_selected
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hchange : boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
  outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables
    x0 x1 x2 ω a b c d hchange hboxTarget.boundaryFace_subset_overlap

theorem
    outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables_extended
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hchange : boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d)
    (hboxTarget : boundaryChartExtendedBox I x1 x2 ω c d) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
  outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables_selected
    x0 x1 x2 ω a b c d hchange hboxTarget.selectedBox

/--
Boundary-chart invariance from oriented boundary-atlas data, selected
source/target boundary boxes, and local surjectivity onto the target boundary
box.  The chart `x2` is only the auxiliary chart used to write the target-side
boundary integral.
-/
theorem outwardFirstBoundaryChartIntegral_invariant_of_orientedAtlas_surjOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartSelectedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hsurj : SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
  outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables_selected
    x0 x1 x2 ω a b c d
    (boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedAtlas_surjOn
      A hx0 hx1 ω a b c d hboxSource hmaps hsurj)
    hboxTarget

/--
Boundary-chart invariance from oriented boundary-atlas data and packaged local
boundary-box image data.
-/
theorem outwardFirstBoundaryChartIntegral_invariant_of_orientedAtlas_imageData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartSelectedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
  outwardFirstBoundaryChartIntegral_invariant_of_orientedAtlas_surjOn
    A hx0 hx1 x2 ω a b c d hboxSource hboxTarget
    himage.mapsTo himage.surjOn

theorem outwardFirstBoundaryChartIntegral_invariant_of_orientedAtlas_localInverse
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartSelectedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
  outwardFirstBoundaryChartIntegral_invariant_of_orientedAtlas_imageData
    A hx0 hx1 x2 ω a b c d hboxSource hboxTarget
    (boundaryChartSelectedBoxImageData_of_mapsTo_localInverseData hmaps hlocal)

/--
Boundary-chart invariance from oriented boundary-atlas data, selected
source/target boundary boxes, and packaged local boundary-box bijection data.
-/
theorem outwardFirstBoundaryChartIntegral_invariant_of_orientedAtlas_bijOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartSelectedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (hbij : BijOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
  outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables_selected
    x0 x1 x2 ω a b c d
    (boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedAtlas_bijOn
      A hx0 hx1 ω a b c d hboxSource hbij)
    hboxTarget

/--
Boundary-chart invariance from global oriented-boundary-charted-manifold data,
selected source/target boundary boxes, and local surjectivity onto the target
boundary box.
-/
theorem outwardFirstBoundaryChartIntegral_invariant_of_orientedManifold_surjOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartSelectedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hsurj : SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
  outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables_selected
    x0 x1 x2 ω a b c d
    (boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedManifold_surjOn
      x0 x1 ω a b c d hboxSource hmaps hsurj)
    hboxTarget

/--
Boundary-chart invariance from global oriented-boundary-charted-manifold data
and packaged local boundary-box image data.
-/
theorem outwardFirstBoundaryChartIntegral_invariant_of_orientedManifold_imageData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartSelectedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
  outwardFirstBoundaryChartIntegral_invariant_of_orientedManifold_surjOn
    x0 x1 x2 ω a b c d hboxSource hboxTarget
    himage.mapsTo himage.surjOn

theorem outwardFirstBoundaryChartIntegral_invariant_of_orientedManifold_localInverse
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartSelectedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
  outwardFirstBoundaryChartIntegral_invariant_of_orientedManifold_imageData
    x0 x1 x2 ω a b c d hboxSource hboxTarget
    (boundaryChartSelectedBoxImageData_of_mapsTo_localInverseData hmaps hlocal)

/--
Boundary-chart invariance from global oriented-boundary-charted-manifold data,
selected source/target boundary boxes, and packaged local boundary-box
bijection data.
-/
theorem outwardFirstBoundaryChartIntegral_invariant_of_orientedManifold_bijOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartSelectedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (hbij : BijOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
  outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables_selected
    x0 x1 x2 ω a b c d
    (boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedManifold_bijOn
      x0 x1 ω a b c d hboxSource hbij)
    hboxTarget

end ManifoldBoundary

end Stokes

end
