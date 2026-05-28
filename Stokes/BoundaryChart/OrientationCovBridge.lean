import Stokes.BoundaryChart.ChangeOfVariables
import Stokes.BoundaryChart.OrientedAtlasBridge

/-!
# Orientation-map data to change-of-variables bridge

This file packages the orientation-map bridge data from
`OrientationBridge.lean` together with the analytic and local image hypotheses
consumed by `boundaryChartOrientedChangeOfVariables`.
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
Image-data form of the bridge from `BoundaryChartOrientationMapDataOn` to the
oriented boundary-chart change-of-variables package.

The orientation-map field is intentionally stronger than the positive-Jacobian
hypothesis used by `ChangeOfVariables.lean`; the projection theorem
`orientationCompatibleOn` forgets down to the exact COV hypothesis.
-/
structure BoundaryChartOrientationCovData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b c d : Fin (n + 1) → Real) where
  /-- Boundary-face and tangential compatibility on the source boundary box. -/
  compatibleOn :
    boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b)
  /-- Mathlib-orientation-facing pointwise data on the source boundary box. -/
  orientationMapDataOn :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b)
  /-- Frechet derivative hypothesis used by mathlib's Euclidean COV theorem. -/
  hasFDerivWithinAt : ∀ u ∈ lowerZeroFaceDomain a b,
    HasFDerivWithinAt (boundaryChartTransition I x0 x1)
      (boundaryChartTransitionTangentMap I x0 x1 u)
      (lowerZeroFaceDomain a b) u
  /-- Injectivity of the boundary coordinate transition on the source box. -/
  injOn :
    InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b)
  /-- Local target-box image data: the source maps onto the chosen target box. -/
  imageData :
    boundaryChartSelectedBoxImageData I x0 x1 a b c d

namespace BoundaryChartOrientationCovData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b c d : Fin (n + 1) → Real}

theorem orientationCompatibleOn
    (data : BoundaryChartOrientationCovData I x0 x1 a b c d) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  boundaryChartOrientationCompatibleOn_of_orientationMapDataOn I x0 x1
    data.orientationMapDataOn

theorem jacobian_pos
    (data : BoundaryChartOrientationCovData I x0 x1 a b c d)
    {u : Fin n → Real} (hu : u ∈ lowerZeroFaceDomain a b) :
    0 < boundaryChartTransitionJacobian I x0 x1 u :=
  (data.orientationMapDataOn u hu).jacobian_pos

theorem image_eq
    (data : BoundaryChartOrientationCovData I x0 x1 a b c d) :
    (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
      lowerZeroFaceDomain c d :=
  boundaryChartTransition_image_eq_lowerZeroFaceDomain_of_mapsTo_surjOn
    I x0 x1 a b c d data.imageData.mapsTo data.imageData.surjOn

/--
Precise projection to the five hypotheses consumed by
`boundaryChartOrientedChangeOfVariables_of_changeOfVariables`.
-/
theorem changeOfVariablesHypotheses
    (data : BoundaryChartOrientationCovData I x0 x1 a b c d) :
    boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) ∧
      boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) ∧
        (∀ u ∈ lowerZeroFaceDomain a b,
          HasFDerivWithinAt (boundaryChartTransition I x0 x1)
            (boundaryChartTransitionTangentMap I x0 x1 u)
            (lowerZeroFaceDomain a b) u) ∧
          InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b) ∧
            (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
              lowerZeroFaceDomain c d :=
  ⟨data.compatibleOn, data.orientationCompatibleOn, data.hasFDerivWithinAt,
    data.injOn, data.image_eq⟩

theorem jacobian_integral_eq_inChart
    (data : BoundaryChartOrientationCovData I x0 x1 a b c d)
    (ω : ManifoldForm I M n) :
    (∫ u in lowerZeroFaceDomain a b,
        boundaryChartTransitionJacobianIntegrand I x0 x1 ω u) =
      halfSpaceBoundaryInChartIntegral I x1 ω c d :=
  boundaryChartTransition_jacobian_integral_eq_inChart_of_changeOfVariables
    I x0 x1 ω a b c d data.hasFDerivWithinAt data.injOn
    data.orientationCompatibleOn data.image_eq

theorem orientedChangeOfVariables
    (data : BoundaryChartOrientationCovData I x0 x1 a b c d)
    (ω : ManifoldForm I M n) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  boundaryChartOrientedChangeOfVariables_of_changeOfVariables
    I x0 x1 ω a b c d data.compatibleOn data.orientationCompatibleOn
    data.hasFDerivWithinAt data.injOn data.image_eq

end BoundaryChartOrientationCovData

/--
Local-inverse form of the bridge.  This keeps the right-inverse data separate
from the compact image/map-to half until it is projected to image data.
-/
structure BoundaryChartOrientationCovLocalInverseData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b c d : Fin (n + 1) → Real) where
  compatibleOn :
    boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b)
  orientationMapDataOn :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b)
  hasFDerivWithinAt : ∀ u ∈ lowerZeroFaceDomain a b,
    HasFDerivWithinAt (boundaryChartTransition I x0 x1)
      (boundaryChartTransitionTangentMap I x0 x1 u)
      (lowerZeroFaceDomain a b) u
  injOn :
    InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b)
  mapsTo :
    MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)
  localInverseData :
    boundaryChartLocalInverseData I x0 x1 a b c d

namespace BoundaryChartOrientationCovLocalInverseData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b c d : Fin (n + 1) → Real}

def imageData
    (data : BoundaryChartOrientationCovLocalInverseData I x0 x1 a b c d) :
    boundaryChartSelectedBoxImageData I x0 x1 a b c d :=
  boundaryChartSelectedBoxImageData_of_mapsTo_localInverseData
    data.mapsTo data.localInverseData

def toOrientationCovData
    (data : BoundaryChartOrientationCovLocalInverseData I x0 x1 a b c d) :
    BoundaryChartOrientationCovData I x0 x1 a b c d where
  compatibleOn := data.compatibleOn
  orientationMapDataOn := data.orientationMapDataOn
  hasFDerivWithinAt := data.hasFDerivWithinAt
  injOn := data.injOn
  imageData := data.imageData

theorem orientationCompatibleOn
    (data : BoundaryChartOrientationCovLocalInverseData I x0 x1 a b c d) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  data.toOrientationCovData.orientationCompatibleOn

theorem changeOfVariablesHypotheses
    (data : BoundaryChartOrientationCovLocalInverseData I x0 x1 a b c d) :
    boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) ∧
      boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) ∧
        (∀ u ∈ lowerZeroFaceDomain a b,
          HasFDerivWithinAt (boundaryChartTransition I x0 x1)
            (boundaryChartTransitionTangentMap I x0 x1 u)
            (lowerZeroFaceDomain a b) u) ∧
          InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b) ∧
            (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
              lowerZeroFaceDomain c d :=
  data.toOrientationCovData.changeOfVariablesHypotheses

theorem orientedChangeOfVariables
    (data : BoundaryChartOrientationCovLocalInverseData I x0 x1 a b c d)
    (ω : ManifoldForm I M n) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  data.toOrientationCovData.orientedChangeOfVariables ω

end BoundaryChartOrientationCovLocalInverseData

/-- Constructor from image data and explicit COV analytic hypotheses. -/
def boundaryChartOrientationCovData_of_imageData {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hdata :
      BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (hderiv : ∀ u ∈ lowerZeroFaceDomain a b,
      HasFDerivWithinAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u)
        (lowerZeroFaceDomain a b) u)
    (hinj : InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b))
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartOrientationCovData I x0 x1 a b c d where
  compatibleOn := hcompat
  orientationMapDataOn := hdata
  hasFDerivWithinAt := hderiv
  injOn := hinj
  imageData := himage

/-- Constructor from local inverse data and explicit COV analytic hypotheses. -/
def boundaryChartOrientationCovData_of_localInverseData {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hdata :
      BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (hderiv : ∀ u ∈ lowerZeroFaceDomain a b,
      HasFDerivWithinAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u)
        (lowerZeroFaceDomain a b) u)
    (hinj : InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b))
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    BoundaryChartOrientationCovData I x0 x1 a b c d :=
  (BoundaryChartOrientationCovLocalInverseData.mk
    hcompat hdata hderiv hinj hmaps hlocal).toOrientationCovData

theorem boundaryChartOrientedChangeOfVariables_of_orientationCovData {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} (ω : ManifoldForm I M n)
    {a b c d : Fin (n + 1) → Real}
    (data : BoundaryChartOrientationCovData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  data.orientedChangeOfVariables ω

theorem boundaryChartOrientedChangeOfVariables_of_orientationMapData_imageData
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hdata :
      BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (hderiv : ∀ u ∈ lowerZeroFaceDomain a b,
      HasFDerivWithinAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u)
        (lowerZeroFaceDomain a b) u)
    (hinj : InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b))
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (boundaryChartOrientationCovData_of_imageData
    hcompat hdata hderiv hinj himage).orientedChangeOfVariables ω

theorem boundaryChartOrientedChangeOfVariables_of_orientationMapData_localInverse
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hdata :
      BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (hderiv : ∀ u ∈ lowerZeroFaceDomain a b,
      HasFDerivWithinAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u)
        (lowerZeroFaceDomain a b) u)
    (hinj : InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b))
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (boundaryChartOrientationCovData_of_localInverseData
    hcompat hdata hderiv hinj hmaps hlocal).orientedChangeOfVariables ω

/--
Selected-box specialization.  The selected box supplies the derivative
hypothesis; compatibility supplies injectivity on the source boundary box.
-/
structure BoundaryChartSelectedBoxOrientationCovData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real) where
  selectedBox :
    boundaryChartSelectedBox I x0 x1 ω a b
  compatibleOn :
    boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b)
  orientationMapDataOn :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b)
  imageData :
    boundaryChartSelectedBoxImageData I x0 x1 a b c d

namespace BoundaryChartSelectedBoxOrientationCovData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real}

def toOrientationCovData [IsManifold I 1 M]
    (data : BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d) :
    BoundaryChartOrientationCovData I x0 x1 a b c d where
  compatibleOn := data.compatibleOn
  orientationMapDataOn := data.orientationMapDataOn
  hasFDerivWithinAt :=
    boundaryChartTransition_hasFDerivWithinAt_of_selectedBox data.selectedBox
  injOn :=
    boundaryChartTransition_injOn_of_selectedBox_compatibleOn
      data.selectedBox data.compatibleOn
  imageData := data.imageData

theorem changeOfVariablesHypotheses [IsManifold I 1 M]
    (data : BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d) :
    boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) ∧
      boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) ∧
        (∀ u ∈ lowerZeroFaceDomain a b,
          HasFDerivWithinAt (boundaryChartTransition I x0 x1)
            (boundaryChartTransitionTangentMap I x0 x1 u)
            (lowerZeroFaceDomain a b) u) ∧
          InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b) ∧
            (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
              lowerZeroFaceDomain c d :=
  data.toOrientationCovData.changeOfVariablesHypotheses

theorem orientedChangeOfVariables [IsManifold I 1 M]
    (data : BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  data.toOrientationCovData.orientedChangeOfVariables ω

def ofOrientedAtlas
    (A : BoundaryChartOrientedAtlas I M)
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d where
  selectedBox := hbox
  compatibleOn := A.transitionCompatibleOn_selectedBox hx0 hx1 hbox
  orientationMapDataOn := A.orientationMapDataOn_selectedBox hx0 hx1 hbox
  imageData := himage

def ofOrientedManifold [BoundaryChartOrientedManifold I M]
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d where
  selectedBox := hbox
  compatibleOn := boundaryChartTransitionCompatibleOn_selectedBox_of_orientedManifold hbox
  orientationMapDataOn :=
    boundaryChartOrientationMapDataOn_selectedBox_of_orientedManifold hbox
  imageData := himage

end BoundaryChartSelectedBoxOrientationCovData

theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_orientationMapData_imageData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hdata :
      BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (BoundaryChartSelectedBoxOrientationCovData.mk
    hbox hcompat hdata himage).orientedChangeOfVariables

theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_orientationMapData_localInverse
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hdata :
      BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  boundaryChartOrientedChangeOfVariables_of_selectedBox_orientationMapData_imageData
    x0 x1 ω a b c d hbox hcompat hdata
    (boundaryChartSelectedBoxImageData_of_mapsTo_localInverseData hmaps hlocal)

theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedAtlas_orientationCov
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (BoundaryChartSelectedBoxOrientationCovData.ofOrientedAtlas
    A hx0 hx1 hbox himage).orientedChangeOfVariables

theorem boundaryChartOrientedChangeOfVariables_of_selectedBox_orientedManifold_orientationCov
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b c d : Fin (n + 1) → Real)
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d :=
  (BoundaryChartSelectedBoxOrientationCovData.ofOrientedManifold
    hbox himage).orientedChangeOfVariables

end ManifoldBoundary

end Stokes

end
