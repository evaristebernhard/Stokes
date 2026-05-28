import Stokes.Global.CoverIndexedCompactSupportCInftyAssembly
import Stokes.Global.ZeroExtensionBoundaryScalar

/-!
# Natural zero-extension endpoint for represented compact-support Stokes

This file is a thin assembly layer for the zero-extension route.

The endpoint theorem consumes the geometrically natural boundary support datum:
the zero-extended boundary scalar is supported in the selected boundary image.
The old scalar boundary integrand is still the one used by the existing
represented Stokes endpoint, so we keep the minimal bridge hypothesis saying
that its ordinary support lies on the selected target face.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportZeroNaturalTheorem

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

/-- Convert the natural zero-extension boundary support input into the scalar
support field consumed by the represented endpoint. -/
def compactSupportZeroExtensionNaturalScalarSupport
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target)
    (zeroScalarSupport :
      targetBox.BoundaryZeroScalarSupportSubsetImageField)
    (oldScalarSupport_subset_targetFace :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Function.support
            (boundaryTargetInChartPieceIntegrand I (targetBox.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          boundaryTargetInChartPieceSet (n := n)
            (targetBox.targetLower i) (targetBox.targetUpper i)) :
    targetBox.BoundaryScalarSupportSubsetImageField :=
  targetBox.boundaryScalarSupportSubsetImageField_of_zeroScalarSupport_on_targetBox
    zeroScalarSupport oldScalarSupport_subset_targetFace targetBox_subset_target

/-- Natural compact-support represented Stokes theorem for the zero-extension
route.

Compared with `compactSupportRepresentedStokesZeroExtension_of_targetInChartTSupport`,
this theorem no longer asks for ambient target-chart topological support of the
old representative.  Boundary support is supplied by the zero-extended scalar
integrand, then transferred to the old scalar integrand on the selected target
face. -/
theorem compactSupportRepresentedStokesZeroExtension_natural
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
    (zeroScalarSupport :
      targetBox.BoundaryZeroScalarSupportSubsetImageField)
    (oldScalarSupport_subset_targetFace :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Function.support
            (boundaryTargetInChartPieceIntegrand I (targetBox.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          boundaryTargetInChartPieceSet (n := n)
            (targetBox.targetLower i) (targetBox.targetUpper i))
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real))) :
    (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) neighborhoodDataInfty measure_eq_volume).globalIntegral =
      globalBoundaryIntegral := by
  exact
    compactSupportRepresentedStokesScalarInfty_of_orientedManifold
      (I := I) (K := K) (C := C) (P := P) (ω := omega)
      (μBulk := muBulk)
      carrierData neighborhoodDataInfty measure_eq_volume
      targetBox targetBox_subset_target
      (compactSupportZeroExtensionNaturalScalarSupport
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        targetBox targetBox_subset_target zeroScalarSupport
        oldScalarSupport_subset_targetFace)
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral

end CompactSupportZeroNaturalTheorem

end Stokes

end
