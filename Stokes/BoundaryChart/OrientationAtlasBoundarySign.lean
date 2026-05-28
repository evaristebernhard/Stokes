import Stokes.BoundaryChart.OrientationMathlibBridge

/-!
# Oriented atlas boundary-sign bridge

This file packages the currently available orientation facts in the natural
input shape used by boundary-chart Stokes: an oriented atlas chart pair, a
selected source box, and the outward-first half-space boundary sign convention.

It deliberately stays at the project-local bridge layer.  A future mathlib
oriented-manifold-with-boundary object should first produce one of the bridge
records from `OrientationMathlibBridge.lean`; the constructors below then
forget it to the concrete boundary-chart hypotheses consumed by local Stokes.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u v w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Selected boundary-chart orientation data, expressed with the outward-first
boundary sign convention.

The fields are exactly the project-local facts available from an oriented
boundary atlas on a selected source boundary box.  In particular, the
orientation-map field is stronger than plain Jacobian positivity and can be
forgotten to the COV orientation predicate when needed.
-/
structure BoundaryChartAtlasBoundarySignData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) where
  /-- The selected source box on the boundary chart transition. -/
  selectedBox :
    boundaryChartSelectedBox I x0 x1 ω a b
  /-- Boundary-face and tangential compatibility on the source box. -/
  compatibleOn :
    boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b)
  /-- Orientation-map data for the tangential chart transition. -/
  orientationMapDataOn :
    BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b)
  /-- Equivalent project-local orientation preservation predicate. -/
  preservesOrientationOn :
    boundaryChartPreservesOrientationOn I x0 x1 (lowerZeroFaceDomain a b)

namespace BoundaryChartAtlasBoundarySignData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/-- Forget orientation-map data to the positive tangential Jacobian predicate. -/
theorem orientationCompatibleOn
    (D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  boundaryChartOrientationCompatibleOn_of_orientationMapDataOn I x0 x1
    D.orientationMapDataOn

/-- Pointwise positive Jacobian supplied by the selected oriented atlas data. -/
theorem jacobian_pos
    (D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b)
    {u : Fin n → Real} (hu : u ∈ lowerZeroFaceDomain a b) :
    0 < boundaryChartTransitionJacobian I x0 x1 u :=
  (D.orientationMapDataOn u hu).jacobian_pos

/-- Pointwise positivity of the transported boundary frame orientation sign. -/
theorem coordinateOrientationSign_pos
    (D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b)
    {u : Fin n → Real} (hu : u ∈ lowerZeroFaceDomain a b) :
    0 < coordinateOrientationSign (boundaryChartTransitionFrame I x0 x1 u) :=
  (D.orientationMapDataOn u hu).coordinateOrientationSign_pos

/--
Pointwise mathlib `Orientation.map` compatibility for the tangential boundary
chart transition.
-/
theorem orientation_map_eq
    (D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b)
    {u : Fin n → Real} (hu : u ∈ lowerZeroFaceDomain a b) :
    Orientation.map (Fin n) (D.orientationMapDataOn u hu).tangentEquiv
        (standardBoundaryOrientation n) =
      standardBoundaryOrientation n :=
  (D.orientationMapDataOn u hu).orientation_map_eq

/-- The project half-space boundary sign is the outward-first boundary sign. -/
theorem boundarySign_eq_outwardFirst
    (_D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b) :
    halfSpaceBoundarySign n = outwardFirstBoundaryOrientationSign n :=
  halfSpaceBoundarySign_eq_outwardFirstBoundaryOrientationSign n

/-- Boundary-chart integrals use the same sign as the half-space lower face. -/
theorem outwardFirstBoundaryChartIntegral_eq_boundarySign_mul
    (_D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b :=
  outwardFirstBoundaryChartIntegral_eq_halfSpaceBoundarySign_mul I x0 x1 ω a b

/-- Package image data together with this orientation bridge for boundary COV. -/
def toSelectedBoxOrientationCovData
    (D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b)
    {c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω a b c d where
  selectedBox := D.selectedBox
  compatibleOn := D.compatibleOn
  orientationMapDataOn := D.orientationMapDataOn
  imageData := himage

/-- Projection to the direct COV hypotheses used by local boundary Stokes. -/
theorem changeOfVariablesHypotheses
    [IsManifold I 1 M]
    (D : BoundaryChartAtlasBoundarySignData I x0 x1 ω a b)
    {c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) ∧
      boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) ∧
        (∀ u ∈ lowerZeroFaceDomain a b,
          HasFDerivWithinAt (boundaryChartTransition I x0 x1)
            (boundaryChartTransitionTangentMap I x0 x1 u)
            (lowerZeroFaceDomain a b) u) ∧
          InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b) ∧
            (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
              lowerZeroFaceDomain c d :=
  (D.toSelectedBoxOrientationCovData himage).changeOfVariablesHypotheses

end BoundaryChartAtlasBoundarySignData

namespace BoundaryChartOrientedAtlas

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/--
Natural constructor from project-local oriented-atlas data and a selected
source boundary box.
-/
def selectedBoxBoundarySignData
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b where
  selectedBox := hbox
  compatibleOn := A.transitionCompatibleOn_selectedBox hx0 hx1 hbox
  orientationMapDataOn := A.orientationMapDataOn_selectedBox hx0 hx1 hbox
  preservesOrientationOn := A.preservesOrientationOn_selectedBox hx0 hx1 hbox

theorem selectedBoxBoundarySignData_orientationCompatibleOn
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (A.selectedBoxBoundarySignData hx0 hx1 hbox).orientationCompatibleOn

theorem selectedBoxBoundarySignData_jacobian_pos
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    {u : Fin n → Real} (hu : u ∈ lowerZeroFaceDomain a b) :
    0 < boundaryChartTransitionJacobian I x0 x1 u :=
  (A.selectedBoxBoundarySignData hx0 hx1 hbox).jacobian_pos hu

theorem selectedBoxBoundarySignData_boundarySign_eq
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    halfSpaceBoundarySign n = outwardFirstBoundaryOrientationSign n :=
  (A.selectedBoxBoundarySignData hx0 hx1 hbox).boundarySign_eq_outwardFirst

end BoundaryChartOrientedAtlas

namespace BoundaryChartOrientedManifold

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/-- Natural constructor from global project-local oriented-manifold data. -/
def selectedBoxBoundarySignData
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b where
  selectedBox := hbox
  compatibleOn := boundaryChartTransitionCompatibleOn_selectedBox_of_orientedManifold hbox
  orientationMapDataOn :=
    boundaryChartOrientationMapDataOn_selectedBox_of_orientedManifold hbox
  preservesOrientationOn :=
    boundaryChartPreservesOrientationOn_selectedBox_of_orientedManifold hbox

theorem selectedBoxBoundarySignData_orientationCompatibleOn
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (selectedBoxBoundarySignData (I := I) (M := M) hbox).orientationCompatibleOn

theorem selectedBoxBoundarySignData_jacobian_pos
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    {u : Fin n → Real} (hu : u ∈ lowerZeroFaceDomain a b) :
    0 < boundaryChartTransitionJacobian I x0 x1 u :=
  (selectedBoxBoundarySignData (I := I) (M := M) hbox).jacobian_pos hu

theorem selectedBoxBoundarySignData_boundarySign_eq
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    halfSpaceBoundarySign n = outwardFirstBoundaryOrientationSign n :=
  (selectedBoxBoundarySignData (I := I) (M := M) hbox).boundarySign_eq_outwardFirst

end BoundaryChartOrientedManifold

namespace BoundaryChartMathlibOrientedAtlasBridge

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {𝓞 : Type v}

/--
Constructor from the abstract mathlib-facing oriented-atlas bridge.  This is as
far as the current project can go without a concrete mathlib
oriented-manifold-with-boundary theorem producing the bridge fields.
-/
def selectedBoxBoundarySignData
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ B.toBoundaryChartOrientedAtlas.charts)
    (hx1 : x1 ∈ B.toBoundaryChartOrientedAtlas.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b :=
  B.toBoundaryChartOrientedAtlas.selectedBoxBoundarySignData hx0 hx1 hbox

theorem selectedBoxBoundarySignData_orientationCompatibleOn
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ B.toBoundaryChartOrientedAtlas.charts)
    (hx1 : x1 ∈ B.toBoundaryChartOrientedAtlas.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (B.selectedBoxBoundarySignData hx0 hx1 hbox).orientationCompatibleOn

theorem selectedBoxBoundarySignData_jacobian_pos
    (B : BoundaryChartMathlibOrientedAtlasBridge I M 𝓞) {x0 x1 : M}
    (hx0 : x0 ∈ B.toBoundaryChartOrientedAtlas.charts)
    (hx1 : x1 ∈ B.toBoundaryChartOrientedAtlas.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    {u : Fin n → Real} (hu : u ∈ lowerZeroFaceDomain a b) :
    0 < boundaryChartTransitionJacobian I x0 x1 u :=
  (B.selectedBoxBoundarySignData hx0 hx1 hbox).jacobian_pos hu

end BoundaryChartMathlibOrientedAtlasBridge

namespace BoundaryChartMathlibOrientedManifoldBridge

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {𝓞 : Type v}

/-- Constructor from the abstract mathlib-facing oriented-manifold bridge. -/
def selectedBoxBoundarySignData
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartAtlasBoundarySignData I x0 x1 ω a b :=
  B.toMathlibOrientedAtlasBridge.selectedBoxBoundarySignData
    (mem_univ x0) (mem_univ x1) hbox

theorem selectedBoxBoundarySignData_orientationCompatibleOn
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b) :=
  (B.selectedBoxBoundarySignData hbox).orientationCompatibleOn

theorem selectedBoxBoundarySignData_jacobian_pos
    (B : BoundaryChartMathlibOrientedManifoldBridge I M 𝓞) {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    {u : Fin n → Real} (hu : u ∈ lowerZeroFaceDomain a b) :
    0 < boundaryChartTransitionJacobian I x0 x1 u :=
  (B.selectedBoxBoundarySignData hbox).jacobian_pos hu

end BoundaryChartMathlibOrientedManifoldBridge

end ManifoldBoundary

end Stokes

end
