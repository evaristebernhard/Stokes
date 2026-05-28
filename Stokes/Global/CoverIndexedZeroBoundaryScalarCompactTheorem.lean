import Stokes.Global.CoverIndexedZeroBoundaryScalarIntegral
import Stokes.Global.CoverIndexedZeroTargetBoxFromCompact

/-!
# Compact-support endpoint for zero boundary scalar integrals

This file combines the zero-boundary-scalar endpoint with the compact-support
support bridge.  The resulting theorem uses the zero-extended boundary scalar
sum as the boundary integral representative and derives the required zero
scalar support from global compact support plus coordinate-image containment in
the chosen target boxes.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroBoundaryScalarCompactTheorem

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

/-- Compact-support represented Stokes with the boundary side represented by
the zero-extended target scalar finite sum.

This is the compact-support wrapper for
`compactSupportRepresentedStokesZeroBoundaryScalarInfty_of_orientedManifold`:
global support of the manifold form, together with target-chart source
containment and coordinate-image containment in the selected target boxes,
automatically supplies the zero scalar support field.  In particular, this
endpoint does not require the old target scalar face-support hypothesis. -/
theorem compactSupportRepresentedStokesZeroBoundaryScalar_of_globalSupport_coordinateImage
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P omega)
    (neighborhoodDataInfty :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (measure_eq_volume :
      muBulk = (volume : Measure (Fin (n + 1) → Real)))
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target)
    (hK : IsCompact K)
    (hsource :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        K ⊆ (extChartAt I (targetBox.targetChart i)).source)
    (homegaSupport : ManifoldForm.support I omega ⊆ K)
    (coordinateImage_subset_targetBox :
      targetBox.TargetChartCoordinateImageSubsetIccField)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real))) :
    (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) neighborhoodDataInfty measure_eq_volume).globalIntegral =
      globalBoundaryIntegral := by
  exact
    compactSupportRepresentedStokesZeroBoundaryScalarInfty_of_orientedManifold
      (I := I) (K := K) (C := C) (P := P) (ω := omega)
      (μBulk := muBulk)
      carrierData neighborhoodDataInfty measure_eq_volume
      targetBox targetBox_subset_target
      (targetBox.boundaryZeroScalarSupportSubsetImageField_of_globalManifoldSupport
        hK hsource homegaSupport coordinateImage_subset_targetBox)
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral

end CoverIndexedZeroBoundaryScalarCompactTheorem

end Stokes

end
