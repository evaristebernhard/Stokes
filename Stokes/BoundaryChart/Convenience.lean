import Stokes.BoundaryChart.LocalStokes

/-!
# Boundary chart convenience API

Thin wrappers that compose the existing local-inverse/image-data constructors
with the boundary-chart local Stokes theorems.
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
Local boundary-chart Stokes from oriented-atlas data, a source extended box, a
target selected box, and explicit local inverse data.  The extra `MapsTo`
hypothesis supplies the compact-image half needed to package image data.
-/
theorem boundaryChartLocalStokes_transitionPullback_of_orientedAtlas_localInverse
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartExtendedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
  boundaryChartLocalStokes_transitionPullback_of_orientedAtlas_imageData
    A hx0 hx1 x2 ω a b c d hboxSource hboxTarget
    (boundaryChartSelectedBoxImageData_of_mapsTo_localInverseData hmaps hlocal)

/--
Local boundary-chart Stokes from oriented-atlas data and the two local
boundary-box selection halves: compact image selection plus a local inverse.
-/
theorem boundaryChartLocalStokes_transitionPullback_of_orientedAtlas_compactImage_localInverse
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartExtendedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (hcompact : boundaryChartCompactImageBoxSelection I x0 x1 a b c d)
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
  boundaryChartLocalStokes_transitionPullback_of_orientedAtlas_imageData
    A hx0 hx1 x2 ω a b c d hboxSource hboxTarget
    (boundaryChartSelectedBoxImageData_of_compactImage_localInverseData
      hcompact hlocal)

/--
Local boundary-chart Stokes from global oriented-boundary-charted-manifold data,
a source extended box, a target selected box, and explicit local inverse data.
The extra `MapsTo` hypothesis supplies the compact-image half needed to package
image data.
-/
theorem boundaryChartLocalStokes_transitionPullback_of_orientedManifold_localInverse
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartExtendedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
  boundaryChartLocalStokes_transitionPullback_of_orientedManifold_imageData
    x0 x1 x2 ω a b c d hboxSource hboxTarget
    (boundaryChartSelectedBoxImageData_of_mapsTo_localInverseData hmaps hlocal)

/--
Local boundary-chart Stokes from global oriented-boundary-charted-manifold data
and the two local boundary-box selection halves: compact image selection plus a
local inverse.
-/
theorem boundaryChartLocalStokes_transitionPullback_of_orientedManifold_compactImage_localInverse
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartExtendedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (hcompact : boundaryChartCompactImageBoxSelection I x0 x1 a b c d)
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
  boundaryChartLocalStokes_transitionPullback_of_orientedManifold_imageData
    x0 x1 x2 ω a b c d hboxSource hboxTarget
    (boundaryChartSelectedBoxImageData_of_compactImage_localInverseData
      hcompact hlocal)

end ManifoldBoundary

end Stokes

end
