import Stokes.Global.CoverIndexedBoundaryTargetNaturalConstructor
import Stokes.BoundaryChart.CoverIndexedTargetImageShrink

/-!
# Boundary target support from selected target-image data

This file isolates the genuinely geometric part of the boundary target support
field.  The selected target-image package only controls the image of the
source lower-zero face.  Therefore the image data can push support into the
target `Icc` once an upstream support/localization argument has shown that the
ambient target representative is supported on that boundary-transition image.

The main constructor is `CoverIndexedBoundaryTargetSupportFromImageData`.
It packages that image-support hypothesis together with
`boundaryChartSelectedBoxImageData` and exposes the exact
`targetInChart_tsupport_subset` field consumed by
`CoverIndexedBoundaryTargetSupportContinuityData.ofTargetInChartContDiffOn`.
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

/-- The ambient image of a source lower-zero boundary box under a boundary
chart transition, re-embedded into the full half-space coordinates. -/
def boundaryChartTransitionAmbientBoundaryImage
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b : Fin (n + 1) → Real) :
    Set (Fin (n + 1) → Real) :=
  boundaryInclusion n ''
    ((boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b)

/-- Selected target-image data pushes the full ambient boundary image into the
ambient target coordinate box. -/
theorem boundaryChartTransitionAmbientBoundaryImage_subset_Icc_of_imageData
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hc0 : c 0 = 0) (hcd : c ≤ d)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    boundaryChartTransitionAmbientBoundaryImage I x0 x1 a b ⊆ Icc c d := by
  rintro y ⟨v, hv, rfl⟩
  rcases hv with ⟨u, hu, rfl⟩
  exact boundaryInclusion_mem_Icc_of_mem_lowerZeroFaceDomain hc0 hcd
    (himage.mapsTo hu)

/-- If the target chart representative is supported on the ambient image of the
source lower-zero face, selected target-image data pushes that support into the
target `Icc`. -/
theorem targetInChart_tsupport_subset_Icc_of_tsupport_subset_boundaryImage
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b c d : Fin (n + 1) → Real}
    (hc0 : c 0 = 0) (hcd : c ≤ d)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d)
    (hsupport :
      tsupport (ManifoldForm.inChart I x1 ω) ⊆
        boundaryChartTransitionAmbientBoundaryImage I x0 x1 a b) :
    tsupport (ManifoldForm.inChart I x1 ω) ⊆ Icc c d :=
  hsupport.trans
    (boundaryChartTransitionAmbientBoundaryImage_subset_Icc_of_imageData
      (I := I) hc0 hcd himage)

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
variable {targetChart : {x : M // x ∈ C.boundaryCenters} → M}
variable {targetLower targetUpper :
  {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real}

namespace SupportControlledSelectedPartition

variable (P : SupportControlledSelectedPartition C)

/-- Cover-indexed target-support field from an image-support hypothesis and
selected target-image data.  This is the reusable bridge: upstream localized
support proves `hsupportImage`; this lemma performs the chart-box/image push. -/
theorem boundaryTargetInChart_tsupport_subset_Icc_of_imageSupport
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (targetLower_zero :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i 0 = 0)
    (targetLower_le_upper :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i ≤ targetUpper i)
    (imageData :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBoxImageData I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (targetLower i) (targetUpper i))
    (hsupportImage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          boundaryChartTransitionAmbientBoundaryImage I
            (C.boundaryChart i.1) (targetChart i)
            (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (ManifoldForm.inChart I (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
      Icc (targetLower i) (targetUpper i) :=
  targetInChart_tsupport_subset_Icc_of_tsupport_subset_boundaryImage
    (I := I)
    (x0 := C.boundaryChart i.1) (x1 := targetChart i)
    (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
    (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
    (c := targetLower i) (d := targetUpper i)
    (targetLower_zero i) (targetLower_le_upper i) (imageData i)
    (hsupportImage i)

end SupportControlledSelectedPartition

/-- Natural support data for target boundary chart representatives generated
from selected target-image data.

The non-bookkeeping hypothesis is `targetInChart_tsupport_subset_image`: it is
the localized-support statement saying that the target representative has no
support away from the image of the source boundary box.  The image-data fields
then convert that image statement into the target `Icc` support field. -/
structure CoverIndexedBoundaryTargetSupportFromImageData
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real) where
  /-- Target lower corners lie on the model boundary. -/
  targetLower_zero :
    ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i 0 = 0
  /-- Target boxes are ordered. -/
  targetLower_le_upper :
    ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i ≤ targetUpper i
  /-- Selected target-image data for each boundary cover index. -/
  imageData :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryChartSelectedBoxImageData I
        (C.boundaryChart i.1) (targetChart i)
        (C.boundaryLower i.1) (C.boundaryUpper i.1)
        (targetLower i) (targetUpper i)
  /-- The localized target representative is supported on the image of the
  selected source boundary box. -/
  targetInChart_tsupport_subset_image :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      tsupport
          (ManifoldForm.inChart I (targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
        boundaryChartTransitionAmbientBoundaryImage I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)

namespace CoverIndexedBoundaryTargetSupportFromImageData

variable
  (D :
    CoverIndexedBoundaryTargetSupportFromImageData
      (C := C) P ω targetChart targetLower targetUpper)

include D

/-- The target `Icc` support field consumed by the natural boundary target
constructors. -/
theorem targetInChart_tsupport_subset_Icc
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (ManifoldForm.inChart I (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
      Icc (targetLower i) (targetUpper i) :=
  P.boundaryTargetInChart_tsupport_subset_Icc_of_imageSupport
    (ω := ω) targetChart targetLower targetUpper
    D.targetLower_zero D.targetLower_le_upper D.imageData
    D.targetInChart_tsupport_subset_image i

/-- Add target `ContDiffOn` to produce the ambient target-chart box data used
by `CoverIndexedBoundaryTargetInChartBoxData.toSupportContinuityData`. -/
def toInChartBoxData
    (targetInChart_contDiffOn :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ⊤
          (ManifoldForm.inChart I (targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i)))
          (Icc (targetLower i) (targetUpper i))) :
    CoverIndexedBoundaryTargetInChartBoxData
      (C := C) P ω targetChart targetLower targetUpper where
  targetLower_zero := D.targetLower_zero
  targetLower_le_upper := D.targetLower_le_upper
  targetInChart_contDiffOn := targetInChart_contDiffOn
  targetInChart_tsupport_subset := D.targetInChart_tsupport_subset_Icc

/-- Direct constructor for the existing support/continuity package from
target-image support plus target `ContDiffOn`. -/
def toSupportContinuityData_ofContDiffOn
    (targetInChart_contDiffOn :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ⊤
          (ManifoldForm.inChart I (targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i)))
          (Icc (targetLower i) (targetUpper i))) :
    CoverIndexedBoundaryTargetSupportContinuityData
      (C := C) P ω targetChart targetLower targetUpper :=
  CoverIndexedBoundaryTargetSupportContinuityData.ofTargetInChartContDiffOn
    (C := C) (P := P) (ω := ω)
    (targetChart := targetChart)
    (targetLower := targetLower) (targetUpper := targetUpper)
    D.targetLower_zero D.targetLower_le_upper targetInChart_contDiffOn
    D.targetInChart_tsupport_subset_Icc

/-- `C^\infty` variant matching the chartwise-smooth route. -/
def toSupportContinuityData_ofContDiffOnInfty
    (targetInChart_contDiffOn :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.inChart I (targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i)))
          (Icc (targetLower i) (targetUpper i))) :
    CoverIndexedBoundaryTargetSupportContinuityData
      (C := C) P ω targetChart targetLower targetUpper :=
  CoverIndexedBoundaryTargetSupportContinuityData.ofTargetInChartContDiffOnInfty
    (C := C) (P := P) (ω := ω)
    (targetChart := targetChart)
    (targetLower := targetLower) (targetUpper := targetUpper)
    D.targetLower_zero D.targetLower_le_upper targetInChart_contDiffOn
    D.targetInChart_tsupport_subset_Icc

end CoverIndexedBoundaryTargetSupportFromImageData

end CoverIndexed

end Stokes

end
