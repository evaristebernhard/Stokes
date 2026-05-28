import Stokes.Global.InteriorChart
import Stokes.BoundaryChart.TransitionCompactBox

/-!
# Global chart box-selection projections

The chart-independent compact coordinate-box package lives in
`Stokes.BoundaryChart.TransitionCompactBox`, so the pure boundary-chart layer
does not need to import `Stokes.Global`.  This module adds the global/interior
projections that depend on `interiorChartSelectedBox`.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.unusedFintypeInType false

universe u v w

namespace CompactCoordinateBoxSelection

/--
Turn a boxed compact support set into an interior selected chart box.

The caller supplies the two chart-domain inclusions and the fact that the
transition-pullback support is contained in the boxed compact coordinate set.
-/
theorem interiorChartSelectedBox_of_tsupport_subset
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E] [Preorder E]
    {H : Type v} [TopologicalSpace H]
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    (B : CompactCoordinateBoxSelection E)
    (hsupp : tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ B.K)
    (htarget : Set.Icc B.a B.b ⊆ (extChartAt I x0).target)
    (hoverlap : Set.Icc B.a B.b ⊆ ManifoldForm.chartOverlap I x0 x1) :
    interiorChartSelectedBox I x0 x1 ω B.a B.b :=
  interiorChartSelectedBox.mk_of_subsets B.le htarget hoverlap
    (hsupp.trans B.subset_Icc)

/--
If a boxed coordinate set lies in a half-space support box, the corresponding
form face coefficients satisfy the half-space selected-box support predicate.
-/
theorem boxFaceCoeffTSupportInHalfSpaceBox_of_tsupport_subset_K {n : Nat}
    (B : CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (hsupp : tsupport ω ⊆ B.K)
    (hK : B.K ⊆ halfSpaceSupportBox B.a B.b) :
    boxFaceCoeffTSupportInHalfSpaceBox ω B.a B.b :=
  boxFaceCoeffTSupportInHalfSpaceBox_of_tsupport_subset ω B.a B.b
    (hsupp.trans hK)

end CompactCoordinateBoxSelection

end Stokes

end
