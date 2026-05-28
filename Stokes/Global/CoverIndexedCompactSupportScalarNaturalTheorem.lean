import Stokes.Global.CoverIndexedCompactSupportNaturalTheorem

/-!
# Compact-support represented Stokes, scalar boundary support assembly

This file is the scalar-support variant of
`CoverIndexedCompactSupportNaturalTheorem`.

It reuses the same carrier, neighborhood, transition, target-box, and global
integral data, but replaces the ambient target-support hypothesis

`tsupport (ManifoldForm.inChart I targetChart ...) ⊆ boundary image`

with the mathematically natural support hypothesis for the actual scalar
boundary integrand:

`Function.support (boundaryTargetInChartPieceIntegrand I targetChart ...)
  ⊆ boundary image`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportScalarNaturalTheorem

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {μBulk : Measure (Fin (n + 1) → Real)}

/--
Boundary scalar image-support data.

This is the replacement for
`CoverIndexedCompactSupportBoundaryImageSupportData`: it asks only that the
boundary scalar target-piece integrand is supported on the selected boundary
transition image, not that the ambient target representative is supported
there.
-/
structure CoverIndexedCompactSupportBoundaryScalarImageSupportData
    {transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P ω}
    (targetBoxData :
      CoverIndexedCompactSupportTargetBoxData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        transitionSupportData) where
  scalarSupport :
    targetBoxData.targetBox.BoundaryScalarSupportSubsetImageField

/--
Natural represented scalar endpoint input assembled from grouped compact
chart-box data.

The only boundary-support input consumed here is scalar support of the
lower-face integrand.  No ambient `inChart` support upgrade is used.
-/
def compactSupportRepresentedStokesScalarInput
    [IsManifold I ⊤ M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P ω)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodData
        (I := I) (K := K) C P ω)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P ω)
    (targetBoxData :
      CoverIndexedCompactSupportTargetBoxData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        transitionSupportData)
    (boundaryScalarImageSupportData :
      CoverIndexedCompactSupportBoundaryScalarImageSupportData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        targetBoxData)
    (globalBoundaryIntegral :
      CoverIndexedCompactSupportGlobalBoundaryIntegralData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        μBulk targetBoxData) :
    CoverIndexedCompactSupportRepresentedStokesScalarInput
      (I := I) (K := K) (ω := ω) (C := C) (P := P)
      (μBulk := μBulk) where
  localData :=
    carrierData.assignedBoxLocalData neighborhoodData
  measure_eq_volume :=
    globalBoundaryIntegral.measure_eq_volume
  targetBox :=
    targetBoxData.targetBox
  localizedChartwiseSmooth :=
    neighborhoodData.localizedChartwiseSmooth
  targetBox_subset_target :=
    targetBoxData.targetBox_subset_target
  scalarSupport :=
    boundaryScalarImageSupportData.scalarSupport
  globalBoundaryIntegral :=
    globalBoundaryIntegral.globalBoundaryIntegral
  globalBoundaryIntegral_eq_integral :=
    globalBoundaryIntegral.globalBoundaryIntegral_eq_integral

/--
Compact-support represented Stokes from grouped compact chart-box data, using
the scalar boundary support route.

Compared with `compactSupportRepresentedStokes_of_compactChartBoxData`, this
does not assume ambient support of the target `inChart` representative on the
boundary image.  It only assumes support of the scalar lower-face boundary
integrand on that image.
-/
theorem compactSupportRepresentedStokes_of_compactChartBoxData_scalarSupport
    [IsFiniteMeasureOnCompacts μBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P ω)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodData
        (I := I) (K := K) C P ω)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P ω)
    (targetBoxData :
      CoverIndexedCompactSupportTargetBoxData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        transitionSupportData)
    (boundaryScalarImageSupportData :
      CoverIndexedCompactSupportBoundaryScalarImageSupportData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        targetBoxData)
    (globalBoundaryIntegral :
      CoverIndexedCompactSupportGlobalBoundaryIntegralData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        μBulk targetBoxData) :
    ((compactSupportRepresentedStokesScalarInput
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        (μBulk := μBulk)
        carrierData neighborhoodData transitionSupportData targetBoxData
        boundaryScalarImageSupportData globalBoundaryIntegral).assignedSelfBulkInput).globalIntegral =
      globalBoundaryIntegral.globalBoundaryIntegral := by
  let D :=
    compactSupportRepresentedStokesScalarInput
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      (μBulk := μBulk)
      carrierData neighborhoodData transitionSupportData targetBoxData
      boundaryScalarImageSupportData globalBoundaryIntegral
  exact D.representedStokes_globalBoundaryIntegral_of_orientedManifold

end CompactSupportScalarNaturalTheorem

end Stokes

end
