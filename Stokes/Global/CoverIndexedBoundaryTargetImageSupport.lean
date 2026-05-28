import Stokes.Global.CoverIndexedBoundaryTargetSupportFromImage
import Stokes.Global.CoverIndexedBoundaryTargetBoxDataConstructor

/-!
# Boundary target image support

This file isolates the real target-image support obligation in the
cover-indexed boundary route.

The mathematically honest statement is conditional: a target chart-box image
selection proves that the selected boundary image is closed, so a pointwise
or algebraic support argument can be upgraded to the `tsupport` field consumed
by `CoverIndexedBoundaryTargetSupportFromImageData`.

The unconditional claim that the ambient target representative
`ManifoldForm.inChart I x1 omega` is supported on the boundary image is too
strong in general: it is an ambient form on the half-space chart, not only its
restriction to the boundary face.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BasicImageSupport

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/-- The boundary-coordinate image of a source lower-zero face under a boundary
chart transition. -/
def boundaryChartTransitionBoundaryImage
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b : Fin (n + 1) → Real) :
    Set (Fin n → Real) :=
  (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b

/-- The selected image data says that the boundary-coordinate image is exactly
the selected target lower-zero face. -/
theorem boundaryChartTransitionBoundaryImage_eq_lowerZeroFaceDomain_of_imageData
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartTransitionBoundaryImage I x0 x1 a b =
      lowerZeroFaceDomain c d := by
  apply subset_antisymm
  · rintro y ⟨u, hu, rfl⟩
    exact himage.mapsTo hu
  · intro y hy
    rcases himage.surjOn hy with ⟨u, hu, huy⟩
    exact ⟨u, hu, huy⟩

/-- Ambient version of the preceding equality, after re-embedding boundary
coordinates with `boundaryInclusion`. -/
theorem boundaryChartTransitionAmbientBoundaryImage_eq_boundaryInclusion_image_of_imageData
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartTransitionAmbientBoundaryImage I x0 x1 a b =
      boundaryInclusion n '' lowerZeroFaceDomain c d := by
  change
    boundaryInclusion n ''
        boundaryChartTransitionBoundaryImage I x0 x1 a b =
      boundaryInclusion n '' lowerZeroFaceDomain c d
  rw [
    boundaryChartTransitionBoundaryImage_eq_lowerZeroFaceDomain_of_imageData
      (I := I) himage]

/-- Boundary-coordinate transition images selected by image data are closed. -/
theorem isClosed_boundaryChartTransitionBoundaryImage_of_imageData
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    IsClosed (boundaryChartTransitionBoundaryImage I x0 x1 a b) := by
  rw [boundaryChartTransitionBoundaryImage_eq_lowerZeroFaceDomain_of_imageData
    (I := I) himage]
  exact (isCompact_lowerZeroFaceDomain c d).isClosed

/-- The ambient re-embedded target lower-zero face is compact. -/
theorem isCompact_boundaryInclusion_image_lowerZeroFaceDomain
    (c d : Fin (n + 1) → Real) :
    IsCompact (boundaryInclusion n '' lowerZeroFaceDomain c d) := by
  simpa using
    ((isCompact_lowerZeroFaceDomain c d).image
      (boundaryTangentInclusion n).continuous)

/-- The ambient re-embedded target lower-zero face is closed. -/
theorem isClosed_boundaryInclusion_image_lowerZeroFaceDomain
    (c d : Fin (n + 1) → Real) :
    IsClosed (boundaryInclusion n '' lowerZeroFaceDomain c d) :=
  (isCompact_boundaryInclusion_image_lowerZeroFaceDomain (n := n) c d).isClosed

/-- Ambient transition images selected by image data are closed. -/
theorem isClosed_boundaryChartTransitionAmbientBoundaryImage_of_imageData
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    IsClosed (boundaryChartTransitionAmbientBoundaryImage I x0 x1 a b) := by
  rw [boundaryChartTransitionAmbientBoundaryImage_eq_boundaryInclusion_image_of_imageData
    (I := I) (n := n) himage]
  exact isClosed_boundaryInclusion_image_lowerZeroFaceDomain (n := n) c d

/-- A support containment into a closed set upgrades to topological-support
containment. -/
theorem tsupport_subset_of_support_subset_isClosed
    {α β : Type*} [TopologicalSpace α] [Zero β] {f : α → β} {s : Set α}
    (hs : IsClosed s) (hsupport : Function.support f ⊆ s) :
    tsupport f ⊆ s := by
  change closure (Function.support f) ⊆ s
  exact closure_minimal hsupport hs

/-- Pointwise nonzero membership gives ordinary support containment. -/
theorem support_subset_of_nonzero_mem
    {α β : Type*} [Zero β] {f : α → β} {s : Set α}
    (hmem : ∀ x, f x ≠ 0 → x ∈ s) :
    Function.support f ⊆ s := by
  intro x hx
  exact hmem x hx

/-- Ambient target-chart `support` on the selected boundary image upgrades to
the `tsupport` image field once selected target-image data is available.

This is intentionally conditional: the nonzero/support containment is the real
geometric localization lemma for the ambient representative. -/
theorem inChart_tsupport_subset_boundaryImage_of_support_subset_image
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d)
    (hsupport :
      Function.support (ManifoldForm.inChart I x1 ω) ⊆
        boundaryChartTransitionAmbientBoundaryImage I x0 x1 a b) :
    tsupport (ManifoldForm.inChart I x1 ω) ⊆
      boundaryChartTransitionAmbientBoundaryImage I x0 x1 a b :=
  tsupport_subset_of_support_subset_isClosed
    (isClosed_boundaryChartTransitionAmbientBoundaryImage_of_imageData
      (I := I) (n := n) himage)
    hsupport

/-- Pointwise nonzero version of
`inChart_tsupport_subset_boundaryImage_of_support_subset_image`. -/
theorem inChart_tsupport_subset_boundaryImage_of_nonzero_mem
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d)
    (hmem :
      ∀ y, ManifoldForm.inChart I x1 ω y ≠ 0 →
        y ∈ boundaryChartTransitionAmbientBoundaryImage I x0 x1 a b) :
    tsupport (ManifoldForm.inChart I x1 ω) ⊆
      boundaryChartTransitionAmbientBoundaryImage I x0 x1 a b :=
  inChart_tsupport_subset_boundaryImage_of_support_subset_image
    (I := I) (n := n) himage (support_subset_of_nonzero_mem hmem)

/-- Boundary scalar target-piece support on the boundary-coordinate image
upgrades to topological support.  This is the boundary-face version of the
ambient support bridge, and is often the mathematically natural target. -/
theorem boundaryTargetInChartPieceIntegrand_tsupport_subset_boundaryImage_of_support_subset
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d)
    (hsupport :
      Function.support (boundaryTargetInChartPieceIntegrand I x1 ω) ⊆
        boundaryChartTransitionBoundaryImage I x0 x1 a b) :
    tsupport (boundaryTargetInChartPieceIntegrand I x1 ω) ⊆
      boundaryChartTransitionBoundaryImage I x0 x1 a b :=
  tsupport_subset_of_support_subset_isClosed
    (isClosed_boundaryChartTransitionBoundaryImage_of_imageData
      (I := I) himage)
    hsupport

/-- Pointwise nonzero version for the boundary scalar target piece. -/
theorem boundaryTargetInChartPieceIntegrand_tsupport_subset_boundaryImage_of_nonzero_mem
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d)
    (hmem :
      ∀ u, boundaryTargetInChartPieceIntegrand I x1 ω u ≠ 0 →
        u ∈ boundaryChartTransitionBoundaryImage I x0 x1 a b) :
    tsupport (boundaryTargetInChartPieceIntegrand I x1 ω) ⊆
      boundaryChartTransitionBoundaryImage I x0 x1 a b :=
  boundaryTargetInChartPieceIntegrand_tsupport_subset_boundaryImage_of_support_subset
    (I := I) himage (support_subset_of_nonzero_mem hmem)

end BasicImageSupport

section CoverIndexed

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryTargetBoxData

variable
  (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω)

/-- Ambient target `support` on the selected boundary-transition image upgrades
to the image-support field consumed by
`CoverIndexedBoundaryTargetSupportFromImageData`.

The hypothesis is deliberately explicit: it is the remaining localization
statement saying that the ambient target representative has no nonzero values
away from the source boundary image. -/
theorem targetInChart_tsupport_subset_image_of_support_subset
    (hsupport :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Function.support
            (ManifoldForm.inChart I (D.targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          boundaryChartTransitionAmbientBoundaryImage I
            (C.boundaryChart i.1) (D.targetChart i)
            (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (ManifoldForm.inChart I (D.targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
      boundaryChartTransitionAmbientBoundaryImage I
        (C.boundaryChart i.1) (D.targetChart i)
        (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  inChart_tsupport_subset_boundaryImage_of_support_subset_image
    (I := I) (n := n) (x0 := C.boundaryChart i.1)
    (x1 := D.targetChart i)
    (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
    (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
    (c := D.targetLower i) (d := D.targetUpper i)
    (D.boundaryChartSelectedBoxImageData i) (hsupport i)

/-- Pointwise nonzero form of
`targetInChart_tsupport_subset_image_of_support_subset`. -/
theorem targetInChart_tsupport_subset_image_of_nonzero_mem
    (hmem :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ∀ y,
          ManifoldForm.inChart I (D.targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i)) y ≠ 0 →
            y ∈
              boundaryChartTransitionAmbientBoundaryImage I
                (C.boundaryChart i.1) (D.targetChart i)
                (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (ManifoldForm.inChart I (D.targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
      boundaryChartTransitionAmbientBoundaryImage I
        (C.boundaryChart i.1) (D.targetChart i)
        (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  D.targetInChart_tsupport_subset_image_of_support_subset
    (fun i => support_subset_of_nonzero_mem (hmem i)) i

/-- Construct the existing image-support package from target-box data and the
remaining ambient support localization lemma. -/
def toTargetSupportFromImageData_of_support_subset
    (hsupport :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Function.support
            (ManifoldForm.inChart I (D.targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          boundaryChartTransitionAmbientBoundaryImage I
            (C.boundaryChart i.1) (D.targetChart i)
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedBoundaryTargetSupportFromImageData
      (C := C) P ω D.targetChart D.targetLower D.targetUpper where
  targetLower_zero := D.targetLower_zero
  targetLower_le_upper := D.targetLower_le_targetUpper
  imageData := D.boundaryChartSelectedBoxImageData
  targetInChart_tsupport_subset_image :=
    D.targetInChart_tsupport_subset_image_of_support_subset hsupport

/-- Pointwise nonzero constructor for
`CoverIndexedBoundaryTargetSupportFromImageData`. -/
def toTargetSupportFromImageData_of_nonzero_mem
    (hmem :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ∀ y,
          ManifoldForm.inChart I (D.targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i)) y ≠ 0 →
            y ∈
              boundaryChartTransitionAmbientBoundaryImage I
                (C.boundaryChart i.1) (D.targetChart i)
                (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedBoundaryTargetSupportFromImageData
      (C := C) P ω D.targetChart D.targetLower D.targetUpper :=
  D.toTargetSupportFromImageData_of_support_subset
    (fun i => support_subset_of_nonzero_mem (hmem i))

end CoverIndexedBoundaryTargetBoxData

end CoverIndexed

end Stokes

end
