import Stokes.Global.CoverIndexedZeroBoundaryScalarIntegral
import Stokes.Global.CoverIndexedZeroRelativeBoundaryAssemblyInputConstructor
import Stokes.Global.CoverIndexedZeroTargetBoxFromCompact

/-!
# Localized target support for compact zero endpoints

This file isolates the target-support part of the compact zero route.

The older compact-support wrappers used

`∀ i, K ⊆ (extChartAt I (targetChart i)).source`

only to make the coordinate image of `K` closed in every selected target chart.
That is stronger than the local analytic input needed by the zero-boundary
scalar endpoint.  The lemmas below expose two weaker entry points:

* a closedness field for the relevant coordinate images, and
* the direct topological-support field for localized target representatives.

The final wrapper applies the relative-source represented Stokes route from a
local `targetInChartZero_tsupport_subset` field, avoiding the global target
chart-source hypothesis entirely.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BasicLocalizedTargetSupport

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {x : M}
variable {ω : ManifoldForm I M n}
variable {c d : Fin (n + 1) → Real}

namespace ManifoldForm

/-- Closed coordinate image plus a local box containment is enough to get
target-box support for the zero-extended chart representative.  This is the
local version of the older compact-source bridge; it does not mention
`K ⊆ (extChartAt I x).source`. -/
theorem inChartZero_tsupport_subset_Icc_of_closedCoordinateImage
    (hclosed : IsClosed (chartCoordinateImage I x K))
    (hωsupport : support I ω ⊆ K)
    (hcoord : chartCoordinateImage I x K ⊆ Icc c d) :
    tsupport (inChartZero I x ω) ⊆ Icc c d :=
  (inChartZero_tsupport_subset_chartCoordinateImage_of_closed
    (I := I) (K := K) (x := x) (ω := ω) hclosed hωsupport).trans hcoord

end ManifoldForm

end BasicLocalizedTargetSupport

section CoverIndexedLocalizedTargetSupport

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryTargetBoxData

variable
  (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)

/-- The precise closedness field needed to turn ordinary support control into
topological support control for the localized zero target representatives. -/
abbrev TargetChartCoordinateImageClosedField : Prop :=
  ∀ i : {x : M // x ∈ C.boundaryCenters},
    IsClosed (chartCoordinateImage I (D.targetChart i) K)

/-- Audit lemma: the old global target-chart-source hypothesis was sufficient
only because it generated this local closedness field. -/
theorem targetChartCoordinateImageClosedField_of_compact_source
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (D.targetChart i)).source) :
    D.TargetChartCoordinateImageClosedField := by
  intro i
  exact
    (isCompact_chartCoordinateImage_of_subset_source
      (I := I) (x := D.targetChart i) hK (hsource i)).isClosed

/-- Closed coordinate images give the coordinate-image support field for every
localized target zero representative.  This is the localized replacement for
`targetInChartZero_tsupport_subset_chartCoordinateImage_of_globalManifoldSupport`;
it asks for closedness of the selected coordinate images, not that the whole
compact set `K` lies in every target chart source. -/
theorem targetInChartZero_tsupport_subset_chartCoordinateImage_of_closedCoordinateImage
    (hclosed : D.TargetChartCoordinateImageClosedField)
    (hωsupport : ManifoldForm.support I omega ⊆ K) :
    D.TargetInChartZeroTSupportSubsetCoordinateImageField := by
  intro i
  refine
    ManifoldForm.inChartZero_tsupport_subset_chartCoordinateImage_of_closed
      (I := I) (K := K) (x := D.targetChart i)
      (ω := P.coverIndexLocalizedForm omega (Sum.inr i))
      (hclosed i) ?_
  intro p hp
  exact hωsupport
    (ManifoldForm.localizedForm_support_subset_form_support
      (I := I) (P.partition (Sum.inr i)) omega
      (by
        simpa [SupportControlledSelectedPartition.coverIndexLocalizedForm]
          using hp))

/-- Directly promote a localized coordinate-image support field to target-box
support.  This is the smallest reusable theorem for endpoints that already
know the correct local support of each boundary piece. -/
theorem targetInChartZero_tsupport_subset_Icc_of_localCoordinateImageSupport
    (hsupport : D.TargetInChartZeroTSupportSubsetCoordinateImageField)
    (hcoord : D.TargetChartCoordinateImageSubsetIccField) :
    D.TargetInChartZeroTSupportSubsetIccField :=
  D.targetInChartZero_tsupport_subset_Icc_of_chartCoordinateImage_subset
    (I := I) (K := K) (C := C) (P := P) (ω := omega)
    hcoord hsupport

/-- Closed coordinate images plus target-box coordinate containment give the
target `Icc` support field for the localized zero target representatives. -/
theorem targetInChartZero_tsupport_subset_Icc_of_closedCoordinateImage
    (hclosed : D.TargetChartCoordinateImageClosedField)
    (hωsupport : ManifoldForm.support I omega ⊆ K)
    (hcoord : D.TargetChartCoordinateImageSubsetIccField) :
    D.TargetInChartZeroTSupportSubsetIccField :=
  D.targetInChartZero_tsupport_subset_Icc_of_localCoordinateImageSupport
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    (D.targetInChartZero_tsupport_subset_chartCoordinateImage_of_closedCoordinateImage
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      hclosed hωsupport)
    hcoord

/-- Local coordinate-image support is already enough for the zero-boundary
scalar image-support field required by the represented Stokes endpoint. -/
theorem boundaryZeroScalarSupportSubsetImageField_of_localCoordinateImageSupport
    (hsupport : D.TargetInChartZeroTSupportSubsetCoordinateImageField)
    (hcoord : D.TargetChartCoordinateImageSubsetIccField) :
    D.BoundaryZeroScalarSupportSubsetImageField :=
  D.boundaryZeroScalarSupportSubsetImageField_of_targetInChartZero_tsupport_subset_Icc
    (I := I) (K := K) (C := C) (P := P) (ω := omega)
    (D.targetInChartZero_tsupport_subset_Icc_of_localCoordinateImageSupport
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      hsupport hcoord)

/-- Closed coordinate images give the zero-boundary scalar image-support field
without the global target-chart-source hypothesis. -/
theorem boundaryZeroScalarSupportSubsetImageField_of_closedCoordinateImage
    (hclosed : D.TargetChartCoordinateImageClosedField)
    (hωsupport : ManifoldForm.support I omega ⊆ K)
    (hcoord : D.TargetChartCoordinateImageSubsetIccField) :
    D.BoundaryZeroScalarSupportSubsetImageField :=
  D.boundaryZeroScalarSupportSubsetImageField_of_targetInChartZero_tsupport_subset_Icc
    (I := I) (K := K) (C := C) (P := P) (ω := omega)
    (D.targetInChartZero_tsupport_subset_Icc_of_closedCoordinateImage
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      hclosed hωsupport hcoord)

end CoverIndexedBoundaryTargetBoxData

namespace CoverIndexedCompactSupportZeroBoundarySupportData

/-- Boundary-support data from a local coordinate-image support field.  This is
the constructor form that later endpoint wrappers can use to avoid the older
global `hsource` field. -/
def ofLocalCoordinateImageSupport
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (hsupport : targetBox.TargetInChartZeroTSupportSubsetCoordinateImageField)
    (hcoord : targetBox.TargetChartCoordinateImageSubsetIccField)
    (oldScalarSupport_subset_targetFace :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Function.support
            (boundaryTargetInChartPieceIntegrand I (targetBox.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          boundaryTargetInChartPieceSet (n := n)
            (targetBox.targetLower i) (targetBox.targetUpper i))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target) :
    CoverIndexedCompactSupportZeroBoundarySupportData
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      targetBox :=
  ofTargetInChartZeroTSupportSubsetIcc
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    targetBox
    (targetBox.targetInChartZero_tsupport_subset_Icc_of_localCoordinateImageSupport
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      hsupport hcoord)
    oldScalarSupport_subset_targetFace targetBox_subset_target

/-- Boundary-support data from closed coordinate images and local target-box
coordinate containment, still without global target-chart-source containment. -/
def ofClosedCoordinateImage
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (hclosed : targetBox.TargetChartCoordinateImageClosedField)
    (hωsupport : ManifoldForm.support I omega ⊆ K)
    (hcoord : targetBox.TargetChartCoordinateImageSubsetIccField)
    (oldScalarSupport_subset_targetFace :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Function.support
            (boundaryTargetInChartPieceIntegrand I (targetBox.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          boundaryTargetInChartPieceSet (n := n)
            (targetBox.targetLower i) (targetBox.targetUpper i))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target) :
    CoverIndexedCompactSupportZeroBoundarySupportData
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      targetBox :=
  ofTargetInChartZeroTSupportSubsetIcc
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    targetBox
    (targetBox.targetInChartZero_tsupport_subset_Icc_of_closedCoordinateImage
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      hclosed hωsupport hcoord)
    oldScalarSupport_subset_targetFace targetBox_subset_target

end CoverIndexedCompactSupportZeroBoundarySupportData

end CoverIndexedLocalizedTargetSupport

section LocalTargetSupportRelativeEndpoint

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {muBulk : Measure (Fin (n + 1) → Real)}

/-- Relative-source compact-support zero endpoint from a direct local target
support field.

This is the same conclusion as the current compact zero relative endpoint, but
the target-support side no longer asks for
`∀ i, K ⊆ (extChartAt I (targetChart i)).source`.  The caller supplies the
actual local fact used by the boundary scalar argument:
the zero-extended localized target representative has topological support in
the selected target box. -/
theorem compactSupportRepresentedStokesZeroCompact_of_localTargetSupport_relative
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P omega)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (measure_eq_volume :
      muBulk = (volume : Measure (Fin (n + 1) → Real)))
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (sourceNeighborhood :
      CoverIndexedCompactSupportNeighborhoodDataInfty.BoundaryNeighborhoodSubsetTransitionSource
        (I := I) (K := K) neighborhoodData transitionSupportData)
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (targetChart_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        transitionSupportData.targetChart i = targetBox.targetChart i)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target)
    (targetInChartZero_tsupport_subset :
      targetBox.TargetInChartZeroTSupportSubsetIccField)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real))) :
    (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) neighborhoodData measure_eq_volume).globalIntegral =
        globalBoundaryIntegral ∧
      transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        globalBoundaryIntegral := by
  have hzeroScalar :
      targetBox.BoundaryZeroScalarSupportSubsetImageField :=
    targetBox.boundaryZeroScalarSupportSubsetImageField_of_targetInChartZero_tsupport_subset_Icc
      (I := I) (K := K) (C := C) (P := P) (ω := omega)
      targetInChartZero_tsupport_subset
  let sourceTargetAssembly :
      CoverIndexedZeroBoundaryRelativeSourceAssemblyInput
        (I := I) (K := K) C P omega :=
    CoverIndexedZeroBoundaryRelativeSourceAssemblyInput.ofTargetBoxZeroBoundaryIntegral
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      carrierData neighborhoodData transitionSupportData sourceNeighborhood
      targetBox targetChart_eq targetBox_subset_target hzeroScalar
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral
  refine ⟨?_, ?_⟩
  · exact
      compactSupportRepresentedStokesZeroBoundaryScalarInfty_of_orientedManifold
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk)
        carrierData neighborhoodData measure_eq_volume
        targetBox targetBox_subset_target hzeroScalar
        globalBoundaryIntegral globalBoundaryIntegral_eq_integral
  · simpa [sourceTargetAssembly] using
      sourceTargetAssembly.zeroBulkSetIntegralSum_eq_globalBoundaryIntegral
        (I := I) (K := K) (C := C) (P := P) (omega := omega)

/-- Relative-source endpoint from a localized coordinate-image support field
and the selected target-box containment of that coordinate image. -/
theorem compactSupportRepresentedStokesZeroCompact_of_localCoordinateImageSupport_relative
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P omega)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (measure_eq_volume :
      muBulk = (volume : Measure (Fin (n + 1) → Real)))
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (sourceNeighborhood :
      CoverIndexedCompactSupportNeighborhoodDataInfty.BoundaryNeighborhoodSubsetTransitionSource
        (I := I) (K := K) neighborhoodData transitionSupportData)
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (targetChart_eq :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        transitionSupportData.targetChart i = targetBox.targetChart i)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target)
    (targetInChartZero_tsupport_subset_coordinateImage :
      targetBox.TargetInChartZeroTSupportSubsetCoordinateImageField)
    (coordinateImage_subset_targetBox :
      targetBox.TargetChartCoordinateImageSubsetIccField)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real))) :
    (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) neighborhoodData measure_eq_volume).globalIntegral =
        globalBoundaryIntegral ∧
      transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        globalBoundaryIntegral :=
  compactSupportRepresentedStokesZeroCompact_of_localTargetSupport_relative
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    (muBulk := muBulk)
    carrierData neighborhoodData measure_eq_volume transitionSupportData
    sourceNeighborhood targetBox targetChart_eq targetBox_subset_target
    (targetBox.targetInChartZero_tsupport_subset_Icc_of_localCoordinateImageSupport
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      targetInChartZero_tsupport_subset_coordinateImage
      coordinateImage_subset_targetBox)
    globalBoundaryIntegral globalBoundaryIntegral_eq_integral

end LocalTargetSupportRelativeEndpoint

end Stokes

end
