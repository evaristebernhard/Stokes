import Stokes.BoundaryChart.Orientation
import Mathlib.LinearAlgebra.Orientation

/-!
# Boundary chart orientation bridge

This file connects the project-local boundary-frame orientation predicates with
mathlib's `Orientation.map` API.  The mathematical invertibility of a tangential
chart derivative is kept as explicit data: later chart-specific files can
construct the required linear equivalence when they have the corresponding
inverse-function hypotheses.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- The standard mathlib orientation on boundary coordinates `Fin n → Real`. -/
def standardBoundaryOrientation (n : Nat) :
    Orientation Real (Fin n → Real) (Fin n) :=
  (Pi.basisFun Real (Fin n)).orientation

/--
For the standard boundary-coordinate orientation, `Orientation.map` preserves
orientation exactly when the determinant of the underlying linear equivalence is
positive.
-/
theorem standardBoundaryOrientation_map_eq_iff_det_pos {n : Nat}
    (e : (Fin n → Real) ≃ₗ[Real] (Fin n → Real)) :
    Orientation.map (Fin n) e (standardBoundaryOrientation n) =
        standardBoundaryOrientation n ↔
      0 < LinearMap.det (e : (Fin n → Real) →ₗ[Real] (Fin n → Real)) := by
  simpa [standardBoundaryOrientation] using
    (Module.Basis.orientation_comp_linearEquiv_eq_iff_det_pos
      (e := Pi.basisFun Real (Fin n)) e)

theorem standardBoundaryOrientation_map_eq_of_det_pos {n : Nat}
    (e : (Fin n → Real) ≃ₗ[Real] (Fin n → Real))
    (hdet : 0 < LinearMap.det (e : (Fin n → Real) →ₗ[Real] (Fin n → Real))) :
    Orientation.map (Fin n) e (standardBoundaryOrientation n) =
      standardBoundaryOrientation n :=
  (standardBoundaryOrientation_map_eq_iff_det_pos e).2 hdet

theorem det_pos_of_standardBoundaryOrientation_map_eq {n : Nat}
    (e : (Fin n → Real) ≃ₗ[Real] (Fin n → Real))
    (hmap : Orientation.map (Fin n) e (standardBoundaryOrientation n) =
      standardBoundaryOrientation n) :
    0 < LinearMap.det (e : (Fin n → Real) →ₗ[Real] (Fin n → Real)) :=
  (standardBoundaryOrientation_map_eq_iff_det_pos e).1 hmap

/--
Pointwise bridge data for a boundary chart transition.

The field `tangentEquiv_toLinearMap` says that the supplied linear equivalence
is the linear map already used by the boundary-chart layer.  The two orientation
fields intentionally duplicate equivalent information: downstream constructors
may be easier to build from either a positive determinant or a direct
`Orientation.map` equality.
-/
structure BoundaryChartOrientationMapData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (u : Fin n → Real) where
  /-- The tangential derivative, upgraded to a linear equivalence. -/
  tangentEquiv : (Fin n → Real) ≃ₗ[Real] (Fin n → Real)
  /-- The upgraded equivalence has the same underlying linear map as the chart derivative. -/
  tangentEquiv_toLinearMap :
    (tangentEquiv : (Fin n → Real) →ₗ[Real] (Fin n → Real)) =
      (boundaryChartTransitionTangentMap I x0 x1 u :
        (Fin n → Real) →ₗ[Real] (Fin n → Real))
  /-- The determinant of the tangential map is positive. -/
  det_pos :
    0 < LinearMap.det
      (tangentEquiv : (Fin n → Real) →ₗ[Real] (Fin n → Real))
  /-- The tangential map preserves the standard mathlib orientation. -/
  orientation_map_eq :
    Orientation.map (Fin n) tangentEquiv (standardBoundaryOrientation n) =
      standardBoundaryOrientation n

namespace BoundaryChartOrientationMapData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {u : Fin n → Real}

/-- Constructor from the mathlib `Orientation.map` equality. -/
def ofOrientationMapEq
    (tangentEquiv : (Fin n → Real) ≃ₗ[Real] (Fin n → Real))
    (hlinear :
      (tangentEquiv : (Fin n → Real) →ₗ[Real] (Fin n → Real)) =
        (boundaryChartTransitionTangentMap I x0 x1 u :
          (Fin n → Real) →ₗ[Real] (Fin n → Real)))
    (hmap :
      Orientation.map (Fin n) tangentEquiv (standardBoundaryOrientation n) =
        standardBoundaryOrientation n) :
    BoundaryChartOrientationMapData I x0 x1 u where
  tangentEquiv := tangentEquiv
  tangentEquiv_toLinearMap := hlinear
  det_pos := det_pos_of_standardBoundaryOrientation_map_eq tangentEquiv hmap
  orientation_map_eq := hmap

/-- Constructor from positive determinant of the supplied linear equivalence. -/
def ofDetPos
    (tangentEquiv : (Fin n → Real) ≃ₗ[Real] (Fin n → Real))
    (hlinear :
      (tangentEquiv : (Fin n → Real) →ₗ[Real] (Fin n → Real)) =
        (boundaryChartTransitionTangentMap I x0 x1 u :
          (Fin n → Real) →ₗ[Real] (Fin n → Real)))
    (hdet :
      0 < LinearMap.det
        (tangentEquiv : (Fin n → Real) →ₗ[Real] (Fin n → Real))) :
    BoundaryChartOrientationMapData I x0 x1 u where
  tangentEquiv := tangentEquiv
  tangentEquiv_toLinearMap := hlinear
  det_pos := hdet
  orientation_map_eq := standardBoundaryOrientation_map_eq_of_det_pos tangentEquiv hdet

/--
Construct bridge data from positivity of the project-local tangential
Jacobian.  The linear equivalence is obtained from the nonzero determinant of
the tangential derivative.
-/
def ofJacobianPos
    (hjac : 0 < boundaryChartTransitionJacobian I x0 x1 u) :
    BoundaryChartOrientationMapData I x0 x1 u := by
  let L : (Fin n → Real) →ₗ[Real] (Fin n → Real) :=
    (boundaryChartTransitionTangentMap I x0 x1 u :
      (Fin n → Real) →ₗ[Real] (Fin n → Real))
  have hdet : 0 < LinearMap.det L := by
    simpa [L, boundaryChartTransitionJacobian,
      boundaryChartTransitionMatrix_det_eq_linearMap_det] using hjac
  let tangentEquiv : (Fin n → Real) ≃ₗ[Real] (Fin n → Real) :=
    LinearMap.equivOfDetNeZero L (ne_of_gt hdet)
  have hlinear :
      (tangentEquiv : (Fin n → Real) →ₗ[Real] (Fin n → Real)) =
        (boundaryChartTransitionTangentMap I x0 x1 u :
          (Fin n → Real) →ₗ[Real] (Fin n → Real)) := by
    simp [tangentEquiv, L, LinearMap.equivOfDetNeZero]
  have hdetEquiv :
      0 < LinearMap.det
        (tangentEquiv : (Fin n → Real) →ₗ[Real] (Fin n → Real)) := by
    simpa [hlinear, L] using hdet
  exact ofDetPos tangentEquiv hlinear hdetEquiv

/-- Construct bridge data from positivity of the project-local coordinate frame. -/
def ofCoordinateOrientationSignPos
    (hframe : 0 < coordinateOrientationSign (boundaryChartTransitionFrame I x0 x1 u)) :
    BoundaryChartOrientationMapData I x0 x1 u :=
  ofJacobianPos (I := I) (x0 := x0) (x1 := x1) (u := u) <| by
    simpa [coordinateOrientationSign_boundaryChartTransitionFrame_eq_jacobian]
      using hframe

theorem orientation_map_eq_iff_det_pos
    (data : BoundaryChartOrientationMapData I x0 x1 u) :
    Orientation.map (Fin n) data.tangentEquiv (standardBoundaryOrientation n) =
        standardBoundaryOrientation n ↔
      0 < LinearMap.det
        (data.tangentEquiv : (Fin n → Real) →ₗ[Real] (Fin n → Real)) := by
  exact standardBoundaryOrientation_map_eq_iff_det_pos data.tangentEquiv

theorem jacobian_pos (data : BoundaryChartOrientationMapData I x0 x1 u) :
    0 < boundaryChartTransitionJacobian I x0 x1 u := by
  rw [boundaryChartTransitionJacobian,
    boundaryChartTransitionMatrix_det_eq_linearMap_det]
  simpa [← data.tangentEquiv_toLinearMap] using data.det_pos

theorem coordinateOrientationSign_pos
    (data : BoundaryChartOrientationMapData I x0 x1 u) :
    0 < coordinateOrientationSign (boundaryChartTransitionFrame I x0 x1 u) := by
  simpa [coordinateOrientationSign_boundaryChartTransitionFrame_eq_jacobian]
    using data.jacobian_pos

end BoundaryChartOrientationMapData

/-- Pointwise bridge data on a boundary-coordinate set. -/
def BoundaryChartOrientationMapDataOn {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (s : Set (Fin n → Real)) :=
  ∀ u ∈ s, BoundaryChartOrientationMapData I x0 x1 u

theorem boundaryChartOrientationCompatibleOn_of_orientationMapDataOn {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) {s : Set (Fin n → Real)}
    (hdata : BoundaryChartOrientationMapDataOn I x0 x1 s) :
    boundaryChartOrientationCompatibleOn I x0 x1 s := by
  intro u hu
  exact (hdata u hu).jacobian_pos

theorem boundaryChartPreservesOrientationOn_of_orientationMapDataOn {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) {s : Set (Fin n → Real)}
    (hdata : BoundaryChartOrientationMapDataOn I x0 x1 s) :
    boundaryChartPreservesOrientationOn I x0 x1 s := by
  intro u hu
  exact (hdata u hu).coordinateOrientationSign_pos

def boundaryChartOrientationMapDataOn_of_preservesOrientationOn {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) {s : Set (Fin n → Real)}
    (horient : boundaryChartPreservesOrientationOn I x0 x1 s) :
    BoundaryChartOrientationMapDataOn I x0 x1 s := by
  intro u hu
  exact BoundaryChartOrientationMapData.ofCoordinateOrientationSignPos
    (I := I) (x0 := x0) (x1 := x1) (u := u) (horient u hu)

theorem boundaryChartOrientationCompatibleOn_of_preservesOrientationMapDataOn {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) {s : Set (Fin n → Real)}
    (hdata : BoundaryChartOrientationMapDataOn I x0 x1 s) :
    boundaryChartOrientationCompatibleOn I x0 x1 s :=
  boundaryChartOrientationCompatibleOn_of_preservesOrientationOn I x0 x1
    (boundaryChartPreservesOrientationOn_of_orientationMapDataOn I x0 x1 hdata)

end ManifoldBoundary

end Stokes

end
