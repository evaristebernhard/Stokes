import Stokes.Global.CoverIndexedCompactSupportNaturalTheorem
import Stokes.Global.CoverIndexedTransitionCoordSupport
import Stokes.Global.ChartCompactImage

/-!
# Transition support from global compact-support data

This file is the support bridge just above the compact-support represented
Stokes endpoint.  It does not introduce a new record.  Instead it supplies
constructors for the existing
`CoverIndexedCompactSupportTransitionSupportData` record from the more
mathematical support facts:

* a source-to-target transition carrier already packaged as
  `CoverIndexedTransitionCoordSupportData`;
* the base `tsupport` itself as the transition carrier;
* the chart-coordinate image of the global compact support set.

The last route also records the honest pointwise obstruction: a
`transitionPullbackInChart` representative is a total function outside the
chart overlap, so global support containment in a chart-coordinate image needs
explicit target/overlap control, or an equivalent local-zero theorem.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section PointwiseSupport

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {k : Nat}
variable {I : ModelWithCorners Real E H}
variable {K : Set M}
variable {x0 x1 : M}
variable {ω : ManifoldForm I M k}

/-- A point in the coordinate image of a source-contained set maps back into
that set under the inverse chart. -/
theorem transitionSupport_chartCoordinateImage_symm_mem_of_subset_source
    (hsource : K ⊆ (extChartAt I x0).source) {y : E}
    (hy : y ∈ chartCoordinateImage I x0 K) :
    (extChartAt I x0).symm y ∈ K := by
  rcases hy with ⟨p, hpK, rfl⟩
  have hp :
      (extChartAt I x0).symm ((extChartAt I x0) p) = p :=
    (extChartAt I x0).left_inv (hsource hpK)
  rw [hp]
  exact hpK

/-- The coordinate image of a set contained in both chart sources is contained
in the source-to-target chart overlap. -/
theorem transitionSupport_chartCoordinateImage_subset_chartOverlap_of_subset_sources
    (hsource0 : K ⊆ (extChartAt I x0).source)
    (hsource1 : K ⊆ (extChartAt I x1).source) :
    chartCoordinateImage I x0 K ⊆ ManifoldForm.chartOverlap I x0 x1 := by
  rintro y ⟨p, hpK, rfl⟩
  have hp :
      (extChartAt I x0).symm ((extChartAt I x0) p) = p :=
    (extChartAt I x0).left_inv (hsource0 hpK)
  change (extChartAt I x0).symm ((extChartAt I x0) p) ∈
    (extChartAt I x1).source
  rw [hp]
  exact hsource1 hpK

variable [IsManifold I 1 M]

/-- On the actual chart overlap, a nonzero transition representative maps back
to a nonzero value of the manifold form. -/
theorem transitionPullbackInChart_support_mapsTo_manifoldSupport_of_mem_overlap
    {y : E}
    (hyoverlap : y ∈ ManifoldForm.chartOverlap I x0 x1)
    (hy :
      y ∈ Function.support
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω)) :
    (extChartAt I x0).symm y ∈ ManifoldForm.support I ω := by
  have hneq_inChart : ManifoldForm.inChart I x0 ω y ≠ 0 := by
    intro hzero
    exact hy (by
      rw [ManifoldForm.transitionPullbackInChart_eq_inChart
        (I := I) x0 x1 ω hyoverlap]
      exact hzero)
  rw [ManifoldForm.mem_support]
  intro hωzero
  apply hneq_inChart
  rw [ManifoldForm.inChart_apply, hωzero]
  ext v
  rfl

/-- Algebraic support version: if the only nonzero transition-representative
points lie in the source chart target and in the source-to-target overlap, then
global form support control gives coordinate-image support control. -/
theorem transitionPullbackInChart_support_subset_chartCoordinateImage_of_support
    (hωK : ManifoldForm.support I ω ⊆ K)
    (hsuppTarget :
      Function.support
          (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
        (extChartAt I x0).target)
    (hsuppOverlap :
      Function.support
          (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
        ManifoldForm.chartOverlap I x0 x1) :
    Function.support
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      chartCoordinateImage I x0 K := by
  intro y hy
  refine ⟨(extChartAt I x0).symm y,
    hωK (transitionPullbackInChart_support_mapsTo_manifoldSupport_of_mem_overlap
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (hsuppOverlap hy) hy), ?_⟩
  exact (extChartAt I x0).right_inv (hsuppTarget hy)

/-- Topological support version, with closedness of the coordinate image made
explicit. -/
theorem transitionPullbackInChart_tsupport_subset_chartCoordinateImage_of_support
    (hclosed : IsClosed (chartCoordinateImage I x0 K))
    (hωK : ManifoldForm.support I ω ⊆ K)
    (hsuppTarget :
      Function.support
          (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
        (extChartAt I x0).target)
    (hsuppOverlap :
      Function.support
          (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
        ManifoldForm.chartOverlap I x0 x1) :
    tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      chartCoordinateImage I x0 K :=
  tsupport_subset_of_support_subset_isClosed hclosed
    (transitionPullbackInChart_support_subset_chartCoordinateImage_of_support
      (I := I) (K := K) (x0 := x0) (x1 := x1) (ω := ω)
      hωK hsuppTarget hsuppOverlap)

/-- Compact-coordinate-image version of the topological support bridge. -/
theorem transitionPullbackInChart_tsupport_subset_chartCoordinateImage_of_support_compact
    [T2Space E]
    (hK : IsCompact K) (hcont : ContinuousOn (extChartAt I x0) K)
    (hωK : ManifoldForm.support I ω ⊆ K)
    (hsuppTarget :
      Function.support
          (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
        (extChartAt I x0).target)
    (hsuppOverlap :
      Function.support
          (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
        ManifoldForm.chartOverlap I x0 x1) :
    tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      chartCoordinateImage I x0 K := by
  exact
    transitionPullbackInChart_tsupport_subset_chartCoordinateImage_of_support
      (I := I) (K := K) (x0 := x0) (x1 := x1) (ω := ω)
      (hclosed :=
        (isCompact_chartCoordinateImage_of_continuousOn
          (I := I) (x := x0) (K := K) hK hcont).isClosed)
      hωK hsuppTarget hsuppOverlap

/-- Source-contained compact version of the topological support bridge. -/
theorem transitionPullbackInChart_tsupport_subset_chartCoordinateImage_of_support_compact_source
    [T2Space E]
    (hK : IsCompact K) (hsource : K ⊆ (extChartAt I x0).source)
    (hωK : ManifoldForm.support I ω ⊆ K)
    (hsuppTarget :
      Function.support
          (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
        (extChartAt I x0).target)
    (hsuppOverlap :
      Function.support
          (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
        ManifoldForm.chartOverlap I x0 x1) :
    tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      chartCoordinateImage I x0 K :=
  transitionPullbackInChart_tsupport_subset_chartCoordinateImage_of_support_compact
    (I := I) (K := K) (x0 := x0) (x1 := x1) (ω := ω)
    hK (continuousOn_extChartAt_of_subset_source (I := I) (x := x0) hsource)
    hωK hsuppTarget hsuppOverlap

end PointwiseSupport

section CoverIndexedTransitionSupport

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedCompactSupportTransitionSupportData

/-- Convert the lower-level transition-coordinate support package into the
compact-support natural endpoint's transition-support package.  The coefficient
field is derived, not copied from an input hypothesis. -/
def ofTransitionCoordSupportData
    (D : CoverIndexedTransitionCoordSupportData (I := I) (K := K) C P ω) :
    CoverIndexedCompactSupportTransitionSupportData (I := I) (K := K) C P ω where
  targetChart := D.targetChart
  transitionCoordSupport := D.transitionCoordSupport
  sourceBox_subset_overlap := D.Icc_subset_overlap
  base_tsupport_subset_transitionCoordSupport := D.base_tsupport_subset
  coeff_tsupport_inter_subset_halfSpaceBox :=
    D.coefficient_tsupport_inter_subset_halfSpaceBox

/-- Use the base transition `tsupport` itself as the transition carrier.  This
removes the carrier containment field and derives the coefficient-box support
from the support-controlled partition. -/
def ofBaseTSupport
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceBox_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i))
    (base_mapsTo_support :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ∀ y ∈
          tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω),
          (extChartAt I (C.boundaryChart i.1)).symm y ∈ K)
    (base_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω) ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (base_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    CoverIndexedCompactSupportTransitionSupportData (I := I) (K := K) C P ω :=
  ofTransitionCoordSupportData
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (CoverIndexedTransitionCoordSupportData.ofBaseTSupport
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      targetChart sourceBox_subset_overlap
      base_mapsTo_support base_subset_target base_subset_overlap)

/-- Use the chart-coordinate image of the global compact support set as the
source-to-target transition carrier.  The remaining base support containment is
the real analytic/geometric input. -/
def ofChartCoordinateImage
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceBox_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i))
    (K_subset_source :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (K_subset_target_source :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (targetChart i)).source)
    (base_tsupport_subset_chartCoordinateImage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω) ⊆
          chartCoordinateImage I (C.boundaryChart i.1) K) :
    CoverIndexedCompactSupportTransitionSupportData (I := I) (K := K) C P ω where
  targetChart := targetChart
  transitionCoordSupport := fun i => chartCoordinateImage I (C.boundaryChart i.1) K
  sourceBox_subset_overlap := sourceBox_subset_overlap
  base_tsupport_subset_transitionCoordSupport :=
    base_tsupport_subset_chartCoordinateImage
  coeff_tsupport_inter_subset_halfSpaceBox := by
    let transitionCoordSupport :
        {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real) :=
      fun i => chartCoordinateImage I (C.boundaryChart i.1) K
    have hcoordK :
        ∀ i : {x : M // x ∈ C.boundaryCenters},
          ∀ y ∈ transitionCoordSupport i,
            (extChartAt I (C.boundaryChart i.1)).symm y ∈ K := by
      intro i y hy
      exact transitionSupport_chartCoordinateImage_symm_mem_of_subset_source
        (I := I) (K := K) (x0 := C.boundaryChart i.1)
        (K_subset_source i) hy
    have hcoordTarget :
        ∀ i : {x : M // x ∈ C.boundaryCenters},
          transitionCoordSupport i ⊆
            (extChartAt I (C.boundaryChart i.1)).target := by
      intro i
      exact chartCoordinateImage_subset_target
        (I := I) (x := C.boundaryChart i.1) (K := K)
        (K_subset_source i)
    have hcoordOverlap :
        ∀ i : {x : M // x ∈ C.boundaryCenters},
          transitionCoordSupport i ⊆
            ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i) := by
      intro i
      exact transitionSupport_chartCoordinateImage_subset_chartOverlap_of_subset_sources
        (I := I) (K := K)
        (x0 := C.boundaryChart i.1) (x1 := targetChart i)
        (K_subset_source i) (K_subset_target_source i)
    intro i
    exact
      P.boundary_transitionCoefficient_inter_transitionCoordSupport_subset_halfSpaceBox
        (I := I) (K := K)
        targetChart transitionCoordSupport
        hcoordK hcoordTarget hcoordOverlap i

-- The support-based constructors use chart compatibility of
-- `transitionPullbackInChart`, hence the mild `C¹` manifold assumption.
variable [IsManifold I 1 M]

/-- Chart-coordinate-image constructor whose base `tsupport` containment is
obtained from ordinary support, closedness of the coordinate image, and the
explicit source target/overlap nonzero-point controls. -/
def ofChartCoordinateImageOfSupport
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceBox_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i))
    (K_subset_source :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (K_subset_target_source :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (targetChart i)).source)
    (chartCoordinateImage_closed :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsClosed (chartCoordinateImage I (C.boundaryChart i.1) K))
    (form_support_subset_K : ManifoldForm.support I ω ⊆ K)
    (base_support_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Function.support
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω) ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (base_support_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Function.support
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    CoverIndexedCompactSupportTransitionSupportData (I := I) (K := K) C P ω :=
  ofChartCoordinateImage
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    targetChart sourceBox_subset_overlap
    K_subset_source K_subset_target_source
    (fun i =>
      transitionPullbackInChart_tsupport_subset_chartCoordinateImage_of_support
        (I := I) (K := K)
        (x0 := C.boundaryChart i.1) (x1 := targetChart i) (ω := ω)
        (chartCoordinateImage_closed i)
        form_support_subset_K
        (base_support_subset_target i)
        (base_support_subset_overlap i))

/-- Compact-source variant of `ofChartCoordinateImageOfSupport`, using compact
coordinate images to discharge closedness. -/
def ofChartCoordinateImageOfSupportCompactSource
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceBox_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i))
    (K_compact : IsCompact K)
    (K_subset_source :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (C.boundaryChart i.1)).source)
    (K_subset_target_source :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (targetChart i)).source)
    (form_support_subset_K : ManifoldForm.support I ω ⊆ K)
    (base_support_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Function.support
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω) ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (base_support_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Function.support
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    CoverIndexedCompactSupportTransitionSupportData (I := I) (K := K) C P ω :=
  ofChartCoordinateImageOfSupport
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    targetChart sourceBox_subset_overlap
    K_subset_source K_subset_target_source
    (fun i =>
      (isCompact_chartCoordinateImage_of_subset_source
        (I := I) (x := C.boundaryChart i.1) (K := K)
        K_compact (K_subset_source i)).isClosed)
    form_support_subset_K
    base_support_subset_target base_support_subset_overlap

end CoverIndexedCompactSupportTransitionSupportData

end CoverIndexedTransitionSupport

end Stokes

end
