import Stokes.Global.CoverIndexedZeroCompactChartTransitionShrink
import Stokes.Global.CoverIndexedZeroCompactInnerOuterBoxSelection
import Stokes.Global.CoverIndexedZeroCompactSelectedNaturalFromTransition
import Stokes.BoundaryChart.SourceShrinkMapsToAuto

/-!
# Cover-indexed preimage shrink for compact zero endpoints

This file is the cover-indexed glue from the honest shrink condition

`Icc source ⊆ sourceOpen ∩ chartTransition ⁻¹' targetOpen`

to the ambient `chartTransition` `MapsTo` field consumed by
`CoverIndexedZeroCompactSelectedNaturalFromTransitionInput`.

The boundary-chart source-shrink API is intentionally imported but not used to
prove the main ambient statement.  Its core field
`BoundaryChartSourceShrinkMapsToData.mapsTo_selectedTarget` controls the
tangential map

`boundaryChartTransition I x0 x1 : (Fin n → Real) → (Fin n → Real)`

on lower-zero boundary faces.  The compact zero endpoint below needs the
ambient map

`ManifoldForm.chartTransition I x0 x1 : (Fin (n + 1) → Real) → ...`

on the whole half-space support box, including points with positive normal
coordinate.  Thus the boundary source-shrink data remains useful for boundary
change-of-variables/local-inverse work, while the present lemmas handle the
ambient half-space shrink.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactPreimageShrink

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

namespace CoverIndexedInnerOuterSourceBoxSelection

variable {targetChart : {x : M // x ∈ C.boundaryCenters} → M}

/--
Cover-indexed preimage-shrink glue.

If the selected source closed box lies in the chosen inner/outer source
neighborhood and in the preimage of an open target neighborhood contained in
the target `Icc`, then the ambient chart transition maps the selected
half-space support box into that target `Icc`.
-/
theorem chartTransition_mapsTo_of_targetOpen_preimage_shrink
    [IsManifold I ⊤ M]
    (sourceShrink :
      CoverIndexedInnerOuterSourceBoxSelection
        (I := I) (K := K) C targetChart)
    (targetOpen :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (targetOpen_open :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (targetOpen i))
    (targetOpen_subset_Icc :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        targetOpen i ⊆ Icc (targetLower i) (targetUpper i))
    (sourceIcc_subset_preimage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          (sourceShrink.sourceNeighborhood i).neighborhood ∩
            (ManifoldForm.chartTransition I
              (C.boundaryChart i.1) (targetChart i)) ⁻¹'
              targetOpen i) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      MapsTo
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (targetChart i))
        (halfSpaceSupportBox (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (Icc (targetLower i) (targetUpper i)) := by
  intro i
  exact
    ManifoldForm.chartTransition_mapsTo_halfSpaceSupportBox_of_open_preimage_shrink
      (I := I) (x0 := C.boundaryChart i.1) (x1 := targetChart i)
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (c := targetLower i) (d := targetUpper i)
      (U := (sourceShrink.sourceNeighborhood i).neighborhood)
      (V := targetOpen i)
      (sourceShrink.sourceNeighborhood i).isOpen_neighborhood
      (sourceShrink.neighborhood_subset_sourceTarget i)
      (sourceShrink.neighborhood_subset_overlap i)
      (targetOpen_open i)
      (targetOpen_subset_Icc i)
      (sourceIcc_subset_preimage i)

/--
Target-box-data spelling of
`chartTransition_mapsTo_of_targetOpen_preimage_shrink`.
-/
theorem chartTransitionMapsToField_of_targetBox_preimage_shrink
    [IsManifold I ⊤ M]
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)
    (sourceShrink :
      CoverIndexedInnerOuterSourceBoxSelection
        (I := I) (K := K) C targetBox.targetChart)
    (targetOpen :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (targetOpen_open :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (targetOpen i))
    (targetOpen_subset_Icc :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        targetOpen i ⊆ Icc (targetBox.targetLower i) (targetBox.targetUpper i))
    (sourceIcc_subset_preimage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          (sourceShrink.sourceNeighborhood i).neighborhood ∩
            (ManifoldForm.chartTransition I
              (C.boundaryChart i.1) (targetBox.targetChart i)) ⁻¹'
              targetOpen i) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      MapsTo
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (targetBox.targetChart i))
        (halfSpaceSupportBox (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (Icc (targetBox.targetLower i) (targetBox.targetUpper i)) :=
  sourceShrink.chartTransition_mapsTo_of_targetOpen_preimage_shrink
    (I := I) (K := K) (C := C)
    (targetChart := targetBox.targetChart)
    targetOpen targetBox.targetLower targetBox.targetUpper
    targetOpen_open targetOpen_subset_Icc sourceIcc_subset_preimage

end CoverIndexedInnerOuterSourceBoxSelection

namespace CoverIndexedBoundaryTargetBoxData

variable
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)

/-- Direct target-zero support field from an inner/outer source shrink and a
target-open preimage shrink. -/
theorem targetInChartZero_tsupport_subset_Icc_of_innerOuter_preimage_shrink
    [IsManifold I ⊤ M]
    (omega_support_subset : ManifoldForm.support I omega ⊆ K)
    (sourceShrink :
      CoverIndexedInnerOuterSourceBoxSelection
        (I := I) (K := K) C targetBox.targetChart)
    (targetOpen :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (targetOpen_open :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (targetOpen i))
    (targetOpen_subset_Icc :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        targetOpen i ⊆ Icc (targetBox.targetLower i) (targetBox.targetUpper i))
    (sourceIcc_subset_preimage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          (sourceShrink.sourceNeighborhood i).neighborhood ∩
            (ManifoldForm.chartTransition I
              (C.boundaryChart i.1) (targetBox.targetChart i)) ⁻¹'
              targetOpen i) :
    targetBox.TargetInChartZeroTSupportSubsetIccField :=
  targetBox.targetInChartZero_tsupport_subset_Icc_of_chartTransition_mapsTo
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    omega_support_subset
    (sourceShrink.chartTransitionMapsToField_of_targetBox_preimage_shrink
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      targetBox targetOpen targetOpen_open targetOpen_subset_Icc
      sourceIcc_subset_preimage)

end CoverIndexedBoundaryTargetBoxData

namespace CoverIndexedZeroCompactRelativeTargetBoxData

variable
    {transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega}
    (targetData :
      CoverIndexedZeroCompactRelativeTargetBoxData
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData)

/-- Relative-target-data spelling of the ambient chart-transition `MapsTo`
field produced by preimage shrink. -/
theorem chartTransitionMapsToField_of_innerOuter_preimage_shrink
    [IsManifold I ⊤ M]
    (sourceShrink :
      CoverIndexedInnerOuterSourceBoxSelection
        (I := I) (K := K) C targetData.targetBox.targetChart)
    (targetOpen :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (targetOpen_open :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (targetOpen i))
    (targetOpen_subset_Icc :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        targetOpen i ⊆
          Icc (targetData.targetBox.targetLower i)
            (targetData.targetBox.targetUpper i))
    (sourceIcc_subset_preimage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          (sourceShrink.sourceNeighborhood i).neighborhood ∩
            (ManifoldForm.chartTransition I
              (C.boundaryChart i.1)
              (targetData.targetBox.targetChart i)) ⁻¹'
              targetOpen i) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      MapsTo
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (targetData.targetBox.targetChart i))
        (halfSpaceSupportBox (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (Icc (targetData.targetBox.targetLower i)
          (targetData.targetBox.targetUpper i)) :=
  sourceShrink.chartTransitionMapsToField_of_targetBox_preimage_shrink
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    targetData.targetBox targetOpen targetOpen_open
    targetOpen_subset_Icc sourceIcc_subset_preimage

end CoverIndexedZeroCompactRelativeTargetBoxData

namespace CoverIndexedZeroCompactSelectedNaturalFromTransitionInput

/-- Constructor for the selected natural endpoint input from an inner/outer
source shrink plus the target-open preimage shrink condition. -/
def ofInnerOuterPreimageShrink
    [IsManifold I ⊤ M]
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
    (transitionNeighborhoods :
      CoverIndexedBoundaryTransitionBoxNeighborhoods
        (I := I) (K := K) C transitionSupportData.targetChart)
    (boundaryNeighborhood_eq :
      neighborhoodData.boundaryNeighborhood =
        transitionNeighborhoods.boundaryNeighborhood)
    (targetData :
      CoverIndexedZeroCompactRelativeTargetBoxData
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData)
    (omega_support_subset : ManifoldForm.support I omega ⊆ K)
    (sourceShrink :
      CoverIndexedInnerOuterSourceBoxSelection
        (I := I) (K := K) C targetData.targetBox.targetChart)
    (targetOpen :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (targetOpen_open :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (targetOpen i))
    (targetOpen_subset_Icc :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        targetOpen i ⊆
          Icc (targetData.targetBox.targetLower i)
            (targetData.targetBox.targetUpper i))
    (sourceIcc_subset_preimage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          (sourceShrink.sourceNeighborhood i).neighborhood ∩
            (ManifoldForm.chartTransition I
              (C.boundaryChart i.1)
              (targetData.targetBox.targetChart i)) ⁻¹'
              targetOpen i) :
    CoverIndexedZeroCompactSelectedNaturalFromTransitionInput
      (I := I) (K := K) C P omega muBulk where
  carrierData := carrierData
  neighborhoodData := neighborhoodData
  measure_eq_volume := measure_eq_volume
  transitionSupportData := transitionSupportData
  transitionNeighborhoods := transitionNeighborhoods
  boundaryNeighborhood_eq := boundaryNeighborhood_eq
  targetData := targetData
  omega_support_subset := omega_support_subset
  chartTransition_mapsTo :=
    targetData.chartTransitionMapsToField_of_innerOuter_preimage_shrink
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      sourceShrink targetOpen targetOpen_open targetOpen_subset_Icc
      sourceIcc_subset_preimage

end CoverIndexedZeroCompactSelectedNaturalFromTransitionInput

end CoverIndexedZeroCompactPreimageShrink

end Stokes

end
