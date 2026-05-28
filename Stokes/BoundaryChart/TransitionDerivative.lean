import Stokes.BoundaryChart.OrientationCovBridge

/-!
# Boundary chart transition derivative bridge

This file packages the Frechet-derivative hypotheses for boundary chart
transitions in the form consumed by the orientation/change-of-variables bridge.
The analytic derivative theorem itself lives in `Basic.lean` and the
selected-box specialization lives in `SelectedBox.lean`; here we only expose
small projection and constructor APIs.
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
Pointwise bridge data from an explicitly supplied Frechet derivative to the
project's tangential derivative of a boundary chart transition.
-/
structure BoundaryChartTransitionDerivativeAt {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (s : Set (Fin n → Real)) (u : Fin n → Real) where
  /-- A Frechet derivative for the boundary-coordinate transition. -/
  fderiv : (Fin n → Real) →L[Real] (Fin n → Real)
  /-- The supplied derivative is the tangential chart-transition map. -/
  fderiv_eq_tangentMap :
    fderiv = boundaryChartTransitionTangentMap I x0 x1 u
  /-- The derivative hypothesis on the chosen source set. -/
  hasFDerivWithinAt :
    HasFDerivWithinAt (boundaryChartTransition I x0 x1) fderiv s u

namespace BoundaryChartTransitionDerivativeAt

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {s : Set (Fin n → Real)} {u : Fin n → Real}

/-- Projection to the derivative hypothesis used by change of variables. -/
theorem hasFDerivWithinAt_tangentMap
    (data : BoundaryChartTransitionDerivativeAt I x0 x1 s u) :
    HasFDerivWithinAt (boundaryChartTransition I x0 x1)
      (boundaryChartTransitionTangentMap I x0 x1 u) s u := by
  simpa [data.fderiv_eq_tangentMap] using data.hasFDerivWithinAt

/-- Constructor when the derivative theorem already produces the tangent map. -/
def ofTangentMap
    (hderiv :
      HasFDerivWithinAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) s u) :
    BoundaryChartTransitionDerivativeAt I x0 x1 s u where
  fderiv := boundaryChartTransitionTangentMap I x0 x1 u
  fderiv_eq_tangentMap := rfl
  hasFDerivWithinAt := hderiv

/--
Constructor from the general boundary-chart transition derivative theorem in
`Basic.lean`.
-/
def ofBoundarySource [IsManifold I 1 M]
    (hsource : ∀ v ∈ s, boundaryInclusion n v ∈ range I)
    (htarget : boundaryInclusion n u ∈ (extChartAt I x0).target)
    (hoverlap : boundaryInclusion n u ∈ ManifoldForm.chartOverlap I x0 x1) :
    BoundaryChartTransitionDerivativeAt I x0 x1 s u :=
  ofTangentMap
    (boundaryChartTransition_hasFDerivWithinAt x0 x1 hsource htarget hoverlap)

end BoundaryChartTransitionDerivativeAt

/--
Setwise derivative bridge data for a boundary chart transition.  It is the
fieldized version of the pointwise derivative hypothesis appearing in
`BoundaryChartOrientationCovData`.
-/
def BoundaryChartTransitionDerivativeDataOn {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (s : Set (Fin n → Real)) :=
  ∀ u ∈ s, BoundaryChartTransitionDerivativeAt I x0 x1 s u

namespace BoundaryChartTransitionDerivativeDataOn

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {s : Set (Fin n → Real)}

/-- Projection to the exact Frechet-derivative family consumed by COV. -/
theorem hasFDerivWithinAt
    (data : BoundaryChartTransitionDerivativeDataOn I x0 x1 s) :
    ∀ u ∈ s,
      HasFDerivWithinAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) s u := by
  intro u hu
  exact (data u hu).hasFDerivWithinAt_tangentMap

/-- Constructor when the tangent-map derivative family is already available. -/
def ofTangentMap
    (hderiv : ∀ u ∈ s,
      HasFDerivWithinAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) s u) :
    BoundaryChartTransitionDerivativeDataOn I x0 x1 s := by
  intro u hu
  exact BoundaryChartTransitionDerivativeAt.ofTangentMap (hderiv u hu)

/-- Constructor from the general boundary-chart transition derivative theorem. -/
def ofBoundarySource [IsManifold I 1 M]
    (hsource : ∀ v ∈ s, boundaryInclusion n v ∈ range I)
    (htarget : ∀ u ∈ s, boundaryInclusion n u ∈ (extChartAt I x0).target)
    (hoverlap : ∀ u ∈ s, boundaryInclusion n u ∈ ManifoldForm.chartOverlap I x0 x1) :
    BoundaryChartTransitionDerivativeDataOn I x0 x1 s := by
  intro u hu
  exact BoundaryChartTransitionDerivativeAt.ofBoundarySource
    hsource (htarget u hu) (hoverlap u hu)

/-- Selected boxes supply derivative bridge data on their lower-zero face. -/
def ofSelectedBox [IsManifold I 1 M]
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartTransitionDerivativeDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  ofTangentMap (boundaryChartTransition_hasFDerivWithinAt_of_selectedBox hbox)

end BoundaryChartTransitionDerivativeDataOn

/-- Selected-box derivative bridge data on the source lower-zero face. -/
def boundaryChartTransitionDerivativeDataOn_of_selectedBox {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H} [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartTransitionDerivativeDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  BoundaryChartTransitionDerivativeDataOn.ofSelectedBox hbox

namespace BoundaryChartOrientationCovData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b c d : Fin (n + 1) → Real}

/-- Forget orientation COV data down to its derivative bridge component. -/
def derivativeData
    (data : BoundaryChartOrientationCovData I x0 x1 a b c d) :
    BoundaryChartTransitionDerivativeDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  BoundaryChartTransitionDerivativeDataOn.ofTangentMap data.hasFDerivWithinAt

end BoundaryChartOrientationCovData

namespace BoundaryChartSelectedBoxOrientationCovData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real}

/-- Selected-box orientation COV data supplies derivative bridge data. -/
def derivativeData [IsManifold I 1 M]
    (data : BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d) :
    BoundaryChartTransitionDerivativeDataOn I x0 x1 (lowerZeroFaceDomain a b) :=
  BoundaryChartTransitionDerivativeDataOn.ofSelectedBox data.selectedBox

end BoundaryChartSelectedBoxOrientationCovData

/-- Constructor for orientation COV data from fieldized derivative data. -/
def boundaryChartOrientationCovData_of_derivativeData_imageData {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (horient :
      BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (hderiv :
      BoundaryChartTransitionDerivativeDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (hinj : InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b))
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartOrientationCovData I x0 x1 a b c d :=
  boundaryChartOrientationCovData_of_imageData
    hcompat horient hderiv.hasFDerivWithinAt hinj himage

/-- Local-inverse constructor for orientation COV data from fieldized derivative data. -/
def boundaryChartOrientationCovData_of_derivativeData_localInverse {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (horient :
      BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (hderiv :
      BoundaryChartTransitionDerivativeDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (hinj : InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b))
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    BoundaryChartOrientationCovData I x0 x1 a b c d :=
  boundaryChartOrientationCovData_of_localInverseData
    hcompat horient hderiv.hasFDerivWithinAt hinj hmaps hlocal

/--
Selected-box orientation COV data from selected-box derivative bridge data and
explicit image data.
-/
def boundaryChartSelectedBoxOrientationCovData_of_derivativeData_imageData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (horient :
      BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (_hderiv :
      BoundaryChartTransitionDerivativeDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d where
  selectedBox := hbox
  compatibleOn := hcompat
  orientationMapDataOn := horient
  imageData := himage

/--
Selected-box orientation COV data where the derivative bridge is discharged by
the selected-box derivative theorem.
-/
def boundaryChartSelectedBoxOrientationCovData_of_selectedBox_imageData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (horient :
      BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d :=
  boundaryChartSelectedBoxOrientationCovData_of_derivativeData_imageData
    hbox hcompat horient
    (BoundaryChartTransitionDerivativeDataOn.ofSelectedBox hbox) himage

/--
Full orientation COV data for a selected box, using the selected-box derivative
projection and compatibility to produce injectivity.
-/
def boundaryChartOrientationCovData_of_selectedBox_derivativeData_imageData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (horient :
      BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (hderiv :
      BoundaryChartTransitionDerivativeDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartOrientationCovData I x0 x1 a b c d :=
  boundaryChartOrientationCovData_of_derivativeData_imageData
    hcompat horient hderiv
    (boundaryChartTransition_injOn_of_selectedBox_compatibleOn hbox hcompat)
    himage

/--
Full orientation COV data for a selected box, with derivative data supplied by
the existing selected-box derivative theorem.
-/
def boundaryChartOrientationCovData_of_selectedBox_imageData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (horient :
      BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartOrientationCovData I x0 x1 a b c d :=
  boundaryChartOrientationCovData_of_selectedBox_derivativeData_imageData
    hbox hcompat horient
    (BoundaryChartTransitionDerivativeDataOn.ofSelectedBox hbox) himage

/--
Full orientation COV data for a selected box and local-inverse image package,
using explicit derivative bridge data.
-/
def boundaryChartOrientationCovData_of_selectedBox_derivativeData_localInverse
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (horient :
      BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (hderiv :
      BoundaryChartTransitionDerivativeDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    BoundaryChartOrientationCovData I x0 x1 a b c d :=
  boundaryChartOrientationCovData_of_derivativeData_localInverse
    hcompat horient hderiv
    (boundaryChartTransition_injOn_of_selectedBox_compatibleOn hbox hcompat)
    hmaps hlocal

/--
Full orientation COV data for a selected box and local-inverse image package,
with derivative data supplied by the existing selected-box derivative theorem.
-/
def boundaryChartOrientationCovData_of_selectedBox_localInverse
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (horient :
      BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b))
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    BoundaryChartOrientationCovData I x0 x1 a b c d :=
  boundaryChartOrientationCovData_of_selectedBox_derivativeData_localInverse
    hbox hcompat horient
    (BoundaryChartTransitionDerivativeDataOn.ofSelectedBox hbox) hmaps hlocal

end ManifoldBoundary

end Stokes

end
