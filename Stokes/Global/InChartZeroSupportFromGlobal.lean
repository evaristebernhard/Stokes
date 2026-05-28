import Stokes.ManifoldFormZero
import Stokes.Global.ChartCompactImage
import Stokes.Global.CoverIndexedBoundaryTargetBoxDataConstructor

/-!
# Zero-extended in-chart support from global compact support

This file is the `inChartZero` analogue of the zero-support bridge for
`transitionPullbackInChartZero`.

The point is intentionally small: the zero extension supplies the missing
target-support hypothesis for total chart representatives.  Once a nonzero
coordinate value is known to lie in the chart target, the ordinary chart
inverse maps it back to the manifold-side support of the form.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section InChartZeroSupportFromGlobal

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {k : Nat}
variable {I : ModelWithCorners Real E H}
variable {K : Set M}
variable {x : M}
variable {ω : ManifoldForm I M k}

namespace ManifoldForm

/-- A nonzero zero-extended chart representative lies in its chart target. -/
theorem inChartZero_ne_zero_mem_target {y : E}
    (hy : inChartZero I x ω y ≠ 0) :
    y ∈ (extChartAt I x).target := by
  have hysupp : y ∈ Function.support (inChartZero I x ω) := by
    simpa [Function.mem_support] using hy
  exact inChartZero_support_subset_target (I := I) x ω hysupp

/-- A nonzero zero-extended chart representative is nonzero for the ordinary
chart representative at points where the two agree. -/
theorem inChart_ne_zero_of_inChartZero_ne_zero {y : E}
    (hy : inChartZero I x ω y ≠ 0) :
    inChart I x ω y ≠ 0 := by
  have htarget : y ∈ (extChartAt I x).target :=
    inChartZero_ne_zero_mem_target (I := I) (x := x) (ω := ω) hy
  intro hzero
  apply hy
  rw [inChartZero_eq_inChart_of_mem (I := I) (x0 := x) (ω := ω) htarget]
  exact hzero

/-- Pointwise zero-extension support bridge: nonzero zero in-chart
representatives map back to the global manifold-side support. -/
theorem inChartZero_ne_zero_mapsTo_support {y : E}
    (hy : inChartZero I x ω y ≠ 0) :
    (extChartAt I x).symm y ∈ support I ω := by
  have hinChart : inChart I x ω y ≠ 0 :=
    inChart_ne_zero_of_inChartZero_ne_zero
      (I := I) (x := x) (ω := ω) hy
  rw [mem_support]
  intro hω
  apply hinChart
  unfold inChart
  rw [hω]
  ext v
  rfl

/-- With a global support bound, nonzero zero in-chart representatives map
back into the compact support set. -/
theorem inChartZero_ne_zero_mapsTo_of_support_subset {y : E}
    (hωsupport : support I ω ⊆ K)
    (hy : inChartZero I x ω y ≠ 0) :
    (extChartAt I x).symm y ∈ K :=
  hωsupport
    (inChartZero_ne_zero_mapsTo_support
      (I := I) (x := x) (ω := ω) hy)

/-- Ordinary support of the zero-extended chart representative is contained
in the coordinate image of any manifold-side support bound. -/
theorem inChartZero_support_subset_chartCoordinateImage
    (hωsupport : support I ω ⊆ K) :
    Function.support (inChartZero I x ω) ⊆ chartCoordinateImage I x K := by
  intro y hy
  have hyne : inChartZero I x ω y ≠ 0 := by
    simpa [Function.mem_support] using hy
  have htarget : y ∈ (extChartAt I x).target :=
    inChartZero_support_subset_target (I := I) x ω hy
  refine ⟨(extChartAt I x).symm y,
    inChartZero_ne_zero_mapsTo_of_support_subset
      (I := I) (K := K) (x := x) (ω := ω) hωsupport hyne,
    ?_⟩
  exact (extChartAt I x).right_inv htarget

/-- Closed-coordinate-image version of
`inChartZero_support_subset_chartCoordinateImage`. -/
theorem inChartZero_tsupport_subset_chartCoordinateImage_of_closed
    (hclosed : IsClosed (chartCoordinateImage I x K))
    (hωsupport : support I ω ⊆ K) :
    tsupport (inChartZero I x ω) ⊆ chartCoordinateImage I x K := by
  simpa [tsupport] using
    closure_minimal
      (inChartZero_support_subset_chartCoordinateImage
        (I := I) (K := K) (x := x) (ω := ω) hωsupport)
      hclosed

/-- Compact-source version of the zero-extended in-chart support bridge. -/
theorem inChartZero_tsupport_subset_chartCoordinateImage
    (hK : IsCompact K)
    (hsource : K ⊆ (extChartAt I x).source)
    (hωsupport : support I ω ⊆ K) :
    tsupport (inChartZero I x ω) ⊆ chartCoordinateImage I x K :=
  inChartZero_tsupport_subset_chartCoordinateImage_of_closed
    (I := I) (K := K) (x := x) (ω := ω)
    (isCompact_chartCoordinateImage_of_subset_source
      (I := I) (x := x) hK hsource |>.isClosed)
    hωsupport

end ManifoldForm

end InChartZeroSupportFromGlobal

section CoverIndexedTargetInChartZeroSupport

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryTargetBoxData

variable
  (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω)

/-- The target ambient zero representative is controlled by the global compact
support set in each target chart. -/
abbrev TargetInChartZeroTSupportSubsetCoordinateImageField : Prop :=
  ∀ i : {x : M // x ∈ C.boundaryCenters},
    tsupport
        (ManifoldForm.inChartZero I (D.targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
      chartCoordinateImage I (D.targetChart i) K

/-- Localized cover-indexed target zero representatives inherit coordinate
support from a global support bound on the original form. -/
theorem targetInChartZero_tsupport_subset_chartCoordinateImage_of_globalManifoldSupport
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (D.targetChart i)).source)
    (hωsupport : ManifoldForm.support I ω ⊆ K) :
    D.TargetInChartZeroTSupportSubsetCoordinateImageField := by
  intro i
  refine
    ManifoldForm.inChartZero_tsupport_subset_chartCoordinateImage
      (I := I) (K := K) (x := D.targetChart i)
      (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
      hK (hsource i) ?_
  intro p hp
  exact hωsupport
    (ManifoldForm.localizedForm_support_subset_form_support
      (I := I) (P.partition (Sum.inr i)) ω
      (by
        simpa [SupportControlledSelectedPartition.coverIndexLocalizedForm]
          using hp))

/-- Pointwise access to the field generated by
`targetInChartZero_tsupport_subset_chartCoordinateImage_of_globalManifoldSupport`. -/
theorem targetInChartZero_tsupport_subset_chartCoordinateImage_of_globalManifoldSupport_apply
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (D.targetChart i)).source)
    (hωsupport : ManifoldForm.support I ω ⊆ K)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (ManifoldForm.inChartZero I (D.targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
      chartCoordinateImage I (D.targetChart i) K :=
  D.targetInChartZero_tsupport_subset_chartCoordinateImage_of_globalManifoldSupport
    hK hsource hωsupport i

end CoverIndexedBoundaryTargetBoxData

end CoverIndexedTargetInChartZeroSupport

end Stokes

end
