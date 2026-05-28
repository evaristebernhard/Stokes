import Stokes.Global.CoverIndexedZeroRelativeSource
import Stokes.Global.CoverIndexedZeroBoundarySourceTargetSum

/-!
# Relative zero-boundary assembly-input constructors

This module is the relative-source analogue of
`CoverIndexedZeroBoundaryAssemblyInputConstructor`.

It builds `CoverIndexedZeroBoundaryRelativeSourceAssemblyInput` from the
target-box zero boundary integral.  Unlike the older ambient-source-open
constructor, the source-side fields are generated from a chosen source
neighborhood and the transition-support package, so no
`IsOpen (ManifoldForm.chartTransitionSource ...)` hypothesis is exposed.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroRelativeBoundaryAssemblyInputConstructor

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedZeroBoundaryRelativeSourceAssemblyInput

/-- Build the relative zero source-target assembly input from a selected
target-box package and the zero target-boundary scalar integral.

The constructor keeps the real local source-neighborhood input, but it does not
ask for ambient openness of the chart-transition source.  It also derives the
zero source-support field from `transitionSupportData` through
`ofSourceNeighborhoodAndTransitionSupport`. -/
def ofTargetBoxZeroBoundaryIntegral
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P omega)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
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
    (zeroScalarSupport :
      targetBox.BoundaryZeroScalarSupportSubsetImageField)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real))) :
    CoverIndexedZeroBoundaryRelativeSourceAssemblyInput
      (I := I) (K := K) C P omega :=
  ofSourceNeighborhoodAndTransitionSupport
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    neighborhoodData transitionSupportData sourceNeighborhood
    globalBoundaryIntegral
    (targetBox.globalBoundaryIntegral_eq_transitionSourceTargetBoundarySum_of_zeroTargetBoundaryIntegral
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      carrierData neighborhoodData transitionSupportData targetChart_eq
      targetBox_subset_target zeroScalarSupport
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral)

end CoverIndexedZeroBoundaryRelativeSourceAssemblyInput

end CoverIndexedZeroRelativeBoundaryAssemblyInputConstructor

end Stokes

end
