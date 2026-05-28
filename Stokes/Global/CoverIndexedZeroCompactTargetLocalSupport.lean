import Stokes.Global.CoverIndexedZeroCompactLocalizedTargetSupport

/-!
# Local target support for compact zero representatives

This file supplies the small support-closure bridge needed by the compact
relative Stokes route.  The endpoint consumes a topological-support field

`TargetInChartZeroTSupportSubsetIccField`,

but in chart-box selection arguments the natural output is often only ordinary
support control: every nonzero value of the zero-extended target representative
lies in the selected target box, or first in a coordinate image that lies in the
target box.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BasicTargetLocalSupport

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x : M}
variable {ω : ManifoldForm I M n}
variable {c d : Fin (n + 1) → Real}

namespace ManifoldForm

/-- Ordinary support in a closed target box is enough for topological support
in that target box.  This is the direct local bridge used after a chart-box
selection has proved the pointwise/nonzero support statement. -/
theorem inChartZero_tsupport_subset_Icc_of_support_subset_Icc
    (hsupport : Function.support (inChartZero I x ω) ⊆ Icc c d) :
    tsupport (inChartZero I x ω) ⊆ Icc c d := by
  simpa [tsupport] using
    closure_minimal hsupport (isClosed_Icc : IsClosed (Icc c d))

/-- Pointwise nonzero version of
`inChartZero_tsupport_subset_Icc_of_support_subset_Icc`. -/
theorem inChartZero_tsupport_subset_Icc_of_nonzero_mem_Icc
    (hmem : ∀ y, inChartZero I x ω y ≠ 0 → y ∈ Icc c d) :
    tsupport (inChartZero I x ω) ⊆ Icc c d :=
  inChartZero_tsupport_subset_Icc_of_support_subset_Icc
    (I := I) (x := x) (ω := ω) (c := c) (d := d)
    (by
      intro y hy
      exact hmem y hy)

/-- Ordinary support in a coordinate image, followed by containment of that
coordinate image in a target box, gives the target-box topological support
field.  Notice that this route only uses closedness of the box, not closedness
of the coordinate image. -/
theorem inChartZero_tsupport_subset_Icc_of_support_subset_chartCoordinateImage
    {K : Set M}
    (hsupport :
      Function.support (inChartZero I x ω) ⊆ chartCoordinateImage I x K)
    (hcoord : chartCoordinateImage I x K ⊆ Icc c d) :
    tsupport (inChartZero I x ω) ⊆ Icc c d :=
  inChartZero_tsupport_subset_Icc_of_support_subset_Icc
    (I := I) (x := x) (ω := ω) (c := c) (d := d)
    (hsupport.trans hcoord)

end ManifoldForm

end BasicTargetLocalSupport

section CoverIndexedTargetLocalSupport

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

/-- Ordinary target-box support field for zero-extended localized target
representatives.  This is often what a local chart-box support argument
produces before taking closures. -/
abbrev TargetInChartZeroSupportSubsetIccField : Prop :=
  ∀ i : {x : M // x ∈ C.boundaryCenters},
    Function.support
        (ManifoldForm.inChartZero I (D.targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
      Icc (D.targetLower i) (D.targetUpper i)

/-- Ordinary coordinate-image support field for zero-extended localized target
representatives.  Combined with `TargetChartCoordinateImageSubsetIccField`, it
promotes to the target-box topological support field. -/
abbrev TargetInChartZeroSupportSubsetCoordinateImageField : Prop :=
  ∀ i : {x : M // x ∈ C.boundaryCenters},
    Function.support
        (ManifoldForm.inChartZero I (D.targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
      chartCoordinateImage I (D.targetChart i) K

/-- Promote ordinary target-box support of every localized target zero
representative to the topological-support field consumed by the compact
relative Stokes endpoint. -/
theorem targetInChartZero_tsupport_subset_Icc_of_support_subset_Icc
    (hsupport : D.TargetInChartZeroSupportSubsetIccField) :
    D.TargetInChartZeroTSupportSubsetIccField := by
  intro i
  exact
    ManifoldForm.inChartZero_tsupport_subset_Icc_of_support_subset_Icc
      (I := I) (x := D.targetChart i)
      (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
      (c := D.targetLower i) (d := D.targetUpper i)
      (hsupport i)

/-- Pointwise nonzero constructor for
`TargetInChartZeroTSupportSubsetIccField`. -/
theorem targetInChartZero_tsupport_subset_Icc_of_nonzero_mem_Icc
    (hmem :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ∀ y,
          ManifoldForm.inChartZero I (D.targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i)) y ≠ 0 →
            y ∈ Icc (D.targetLower i) (D.targetUpper i)) :
    D.TargetInChartZeroTSupportSubsetIccField :=
  D.targetInChartZero_tsupport_subset_Icc_of_support_subset_Icc
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (by
      intro i y hy
      exact hmem i y hy)

/-- Promote ordinary coordinate-image support plus target-box containment to
the topological target-box support field.  This avoids asking that the
coordinate image itself be closed; the selected `Icc` box supplies the closed
set used for closure. -/
theorem targetInChartZero_tsupport_subset_Icc_of_support_subset_coordinateImage
    (hsupport : D.TargetInChartZeroSupportSubsetCoordinateImageField)
    (hcoord : D.TargetChartCoordinateImageSubsetIccField) :
    D.TargetInChartZeroTSupportSubsetIccField :=
  D.targetInChartZero_tsupport_subset_Icc_of_support_subset_Icc
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (by
      intro i
      exact (hsupport i).trans (hcoord i))

end CoverIndexedBoundaryTargetBoxData

end CoverIndexedTargetLocalSupport

end Stokes

end
