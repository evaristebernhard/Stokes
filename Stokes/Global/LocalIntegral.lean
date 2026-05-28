import Stokes.BoundaryChart.Convenience

/-!
# Project-local integral wrappers

This module introduces the project-facing names for the local bulk and boundary
integrals used by the global Stokes assembly layer.  The definitions are thin
wrappers around the boundary-chart half-space API; all analytic content remains
in `Stokes.BoundaryChart.LocalStokes`.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section ProjectLocalIntegral

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Project-local bulk integral over a selected boundary-chart box.

This is only a project-facing alias for the transition-pullback half-space bulk
integral.
-/
def projectLocalBulkIntegral {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Real :=
  halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b

/--
Project-local boundary integral with the outward-normal-first induced boundary
orientation.

This is only a project-facing alias for the boundary-chart integral already
defined in the boundary-chart layer.
-/
def projectLocalBoundaryIntegral {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Real :=
  outwardFirstBoundaryChartIntegral I x0 x1 ω a b

/-- Unfold the project-local boundary wrapper back to the signed half-space term. -/
theorem projectLocalBoundaryIntegral_eq_halfSpaceBoundarySign_mul {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) :
    projectLocalBoundaryIntegral I x0 x1 ω a b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b := by
  simpa [projectLocalBoundaryIntegral] using
    outwardFirstBoundaryChartIntegral_eq_halfSpaceBoundarySign_mul
      I x0 x1 ω a b

/--
Project-local Stokes for one boundary-chart box, obtained directly from the
boundary-chart local Stokes theorem.
-/
theorem projectLocalStokes_of_boundaryChartExtendedBox {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hbox : boundaryChartExtendedBox I x0 x1 ω a b) :
    projectLocalBulkIntegral I x0 x1 ω a b =
      projectLocalBoundaryIntegral I x0 x1 ω a b := by
  simpa [projectLocalBulkIntegral, projectLocalBoundaryIntegral] using
    boundaryChartLocalStokes_transitionPullback_of_extendedBox_outwardFirst
      I x0 x1 ω a b hbox

/--
Project-local Stokes with the boundary term transported to a target boundary
chart using oriented-atlas data and packaged image data.
-/
theorem projectLocalStokes_of_orientedAtlas_imageData {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H} [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartExtendedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    projectLocalBulkIntegral I x0 x1 ω a b =
      projectLocalBoundaryIntegral I x1 x2 ω c d := by
  simpa [projectLocalBulkIntegral, projectLocalBoundaryIntegral] using
    boundaryChartLocalStokes_transitionPullback_of_orientedAtlas_imageData
      A hx0 hx1 x2 ω a b c d hboxSource hboxTarget himage

/--
Project-local Stokes with the boundary term transported to a target boundary
chart using global oriented-boundary-charted-manifold data and packaged image
data.
-/
theorem projectLocalStokes_of_orientedManifold_imageData {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartExtendedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    projectLocalBulkIntegral I x0 x1 ω a b =
      projectLocalBoundaryIntegral I x1 x2 ω c d := by
  simpa [projectLocalBulkIntegral, projectLocalBoundaryIntegral] using
    boundaryChartLocalStokes_transitionPullback_of_orientedManifold_imageData
      x0 x1 x2 ω a b c d hboxSource hboxTarget himage

/--
Purely algebraic finite-sum wrapper: local equality on every active index
implies equality of the corresponding active sums.
-/
theorem sum_projectLocal_eq_of_forall_local {ι R : Type*} [AddCommMonoid R]
    (active : Finset ι) (bulk boundary : ι → R)
    (hlocal : ∀ i ∈ active, bulk i = boundary i) :
    Finset.sum active bulk = Finset.sum active boundary := by
  exact Finset.sum_congr rfl hlocal

/--
Finite-sum project-local Stokes over active boundary-chart boxes with a fixed
form and chart-pair assignment.
-/
theorem sum_projectLocalStokes_of_forall_boundaryChartExtendedBox {ι : Type*}
    {n : Nat} (active : Finset ι)
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : ι → M) (ω : ManifoldForm I M n)
    (a b : ι → Fin (n + 1) → Real)
    (hbox : ∀ i ∈ active, boundaryChartExtendedBox I (x0 i) (x1 i) ω (a i) (b i)) :
    (∑ i ∈ active, projectLocalBulkIntegral I (x0 i) (x1 i) ω (a i) (b i)) =
      ∑ i ∈ active, projectLocalBoundaryIntegral I (x0 i) (x1 i) ω (a i) (b i) := by
  exact Finset.sum_congr rfl fun i hi =>
    projectLocalStokes_of_boundaryChartExtendedBox
      I (x0 i) (x1 i) ω (a i) (b i) (hbox i hi)

end ProjectLocalIntegral

end Stokes

end
