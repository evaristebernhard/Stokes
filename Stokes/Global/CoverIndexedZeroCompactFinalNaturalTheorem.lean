import Stokes.Global.CoverIndexedZeroCompactSelectedNaturalFromTransition
import Stokes.Global.CoverIndexedZeroCompactChartTransitionShrink
import Stokes.Global.CoverIndexedZeroCompactInnerOuterBoxSelection
import Stokes.Global.CoverIndexedZeroCompactGeometryConstructors
import Stokes.BoundaryChart.SourceShrinkMapsToAuto

/-!
# Final natural compact-support endpoint package

This file is only an assembly layer.  It deliberately does not prove new chart
geometry.  Instead it records the final natural inputs in a small number of
theorem-facing structures and routes them to
`CoverIndexedZeroCompactSelectedNaturalFromTransitionInput`.

There are three useful entry points:

* `CoverIndexedZeroCompactFinalNaturalMapsToInput` consumes the honest ambient
  `chartTransition_mapsTo` field required by the selected endpoint.
* `CoverIndexedZeroCompactFinalNaturalPreimageShrinkInput` consumes the
  preimage-shrink field and derives that ambient `MapsTo`.
* `CoverIndexedZeroCompactFinalNaturalSourceShrinkInput` records a cover-indexed
  family of existing source-shrink data.  That data supplies the tangential
  boundary `MapsTo`; the ambient half-space `MapsTo` is still a separate field.

The last point is intentional: the current source-shrink API controls
`boundaryChartTransition` on the lower-zero face, while the compact-support
target-zero support endpoint needs `ManifoldForm.chartTransition` on the whole
`halfSpaceSupportBox`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactFinalNaturalTheorem

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

/--
Common final compact-support data, before choosing how to prove target-box
support.

The source side is stored in the transition-neighborhood form consumed by the
relative endpoint.  `sourceInnerOuter` is optional mathematical bookkeeping for
callers that selected the transition neighborhoods through the
inner/outer-box route; it is not needed by the endpoint theorem itself.
-/
structure CoverIndexedZeroCompactFinalNaturalBaseInput
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n)
    (muBulk : Measure (Fin (n + 1) → Real)) where
  carrierData :
    CoverIndexedCompactSupportCarrierData
      (I := I) (K := K) C P omega
  neighborhoodData :
    CoverIndexedCompactSupportNeighborhoodDataInfty
      (I := I) (K := K) C P omega
  measure_eq_volume :
    muBulk = (volume : Measure (Fin (n + 1) → Real))
  transitionSupportData :
    CoverIndexedCompactSupportTransitionSupportData
      (I := I) (K := K) C P omega
  transitionNeighborhoods :
    CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C transitionSupportData.targetChart
  boundaryNeighborhood_eq :
    neighborhoodData.boundaryNeighborhood =
      transitionNeighborhoods.boundaryNeighborhood
  targetData :
    CoverIndexedZeroCompactRelativeTargetBoxData
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData
  targetNeighborhoods :
    CoverIndexedBoundaryTargetBoxNeighborhoods
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      targetData.targetBox
  omega_support_subset :
    ManifoldForm.support I omega ⊆ K

namespace CoverIndexedZeroCompactFinalNaturalBaseInput

variable
    (D :
      CoverIndexedZeroCompactFinalNaturalBaseInput
        (I := I) (K := K) C P omega muBulk)

/-- The selected boundary target charts of the final package. -/
def targetChart :
    {x : M // x ∈ C.boundaryCenters} → M :=
  D.targetData.targetBox.targetChart

/-- The selected target lower corners of the final package. -/
def targetLower :
    {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real :=
  D.targetData.targetBox.targetLower

/-- The selected target upper corners of the final package. -/
def targetUpper :
    {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real :=
  D.targetData.targetBox.targetUpper

end CoverIndexedZeroCompactFinalNaturalBaseInput

/--
Final natural input whose remaining geometric field is exactly the ambient
chart-transition containment needed by the selected compact endpoint.
-/
structure CoverIndexedZeroCompactFinalNaturalMapsToInput
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n)
    (muBulk : Measure (Fin (n + 1) → Real)) where
  base :
    CoverIndexedZeroCompactFinalNaturalBaseInput
      (I := I) (K := K) C P omega muBulk
  chartTransition_mapsTo :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      MapsTo
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (base.targetData.targetBox.targetChart i))
        (halfSpaceSupportBox (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (Icc (base.targetData.targetBox.targetLower i)
          (base.targetData.targetBox.targetUpper i))

namespace CoverIndexedZeroCompactFinalNaturalMapsToInput

variable
    (D :
      CoverIndexedZeroCompactFinalNaturalMapsToInput
        (I := I) (K := K) C P omega muBulk)

/-- Forget the final bookkeeping and expose the selected endpoint input. -/
def toSelectedNaturalFromTransitionInput :
    CoverIndexedZeroCompactSelectedNaturalFromTransitionInput
      (I := I) (K := K) C P omega muBulk where
  carrierData := D.base.carrierData
  neighborhoodData := D.base.neighborhoodData
  measure_eq_volume := D.base.measure_eq_volume
  transitionSupportData := D.base.transitionSupportData
  transitionNeighborhoods := D.base.transitionNeighborhoods
  boundaryNeighborhood_eq := D.base.boundaryNeighborhood_eq
  targetData := D.base.targetData
  omega_support_subset := D.base.omega_support_subset
  chartTransition_mapsTo := D.chartTransition_mapsTo

/-- The boundary scalar selected by the final natural package. -/
def boundaryIntegral : Real :=
  (D.toSelectedNaturalFromTransitionInput
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)).boundaryIntegral

/--
Represented compact-support Stokes in the final natural input shape, with the
boundary side kept as the packaged scalar.
-/
theorem representedStokes_and_zeroSourceTargetBulkAssembly_eq_integral
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    (D.base.carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) D.base.neighborhoodData
        D.base.measure_eq_volume).globalIntegral =
        D.boundaryIntegral
          (I := I) (K := K) (C := C) (P := P) (omega := omega)
          (muBulk := muBulk) ∧
      D.base.transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        D.boundaryIntegral
          (I := I) (K := K) (C := C) (P := P) (omega := omega)
          (muBulk := muBulk) := by
  simpa [boundaryIntegral, toSelectedNaturalFromTransitionInput] using
    (D.toSelectedNaturalFromTransitionInput
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)).representedStokes_and_zeroSourceTargetBulkAssembly_eq_integral

/-- Integral-facing final natural compact-support represented Stokes theorem. -/
theorem representedStokes_and_zeroSourceTargetBulkAssembly
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    (D.base.carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) D.base.neighborhoodData
        D.base.measure_eq_volume).globalIntegral =
        ∫ y,
          P.coverIndexBoundaryTargetZeroPieceSum
            D.base.targetData.targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real)) ∧
      D.base.transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        ∫ y,
          P.coverIndexBoundaryTargetZeroPieceSum
            D.base.targetData.targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real)) := by
  simpa [boundaryIntegral,
    CoverIndexedZeroCompactSelectedNaturalFromTransitionInput.boundaryIntegral,
    toSelectedNaturalFromTransitionInput] using
    D.representedStokes_and_zeroSourceTargetBulkAssembly_eq_integral
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)

end CoverIndexedZeroCompactFinalNaturalMapsToInput

/--
Final input where the ambient `MapsTo` is produced from a preimage-shrink
statement on the chosen transition neighborhoods.
-/
structure CoverIndexedZeroCompactFinalNaturalPreimageShrinkInput
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n)
    (muBulk : Measure (Fin (n + 1) → Real)) where
  base :
    CoverIndexedZeroCompactFinalNaturalBaseInput
      (I := I) (K := K) C P omega muBulk
  preimage_shrink :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      base.transitionNeighborhoods.boundaryNeighborhood i ⊆
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (base.transitionSupportData.targetChart i)) ⁻¹'
          Icc (base.targetData.targetBox.targetLower i)
            (base.targetData.targetBox.targetUpper i)

namespace CoverIndexedZeroCompactFinalNaturalPreimageShrinkInput

variable
    (D :
      CoverIndexedZeroCompactFinalNaturalPreimageShrinkInput
        (I := I) (K := K) C P omega muBulk)

/-- Ambient chart-transition containment derived from the preimage shrink. -/
def chartTransition_mapsTo :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      MapsTo
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (D.base.targetData.targetBox.targetChart i))
        (halfSpaceSupportBox (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (Icc (D.base.targetData.targetBox.targetLower i)
          (D.base.targetData.targetBox.targetUpper i)) := by
  intro i
  have hmaps :
      MapsTo
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (D.base.transitionSupportData.targetChart i))
        (halfSpaceSupportBox (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (Icc (D.base.targetData.targetBox.targetLower i)
          (D.base.targetData.targetBox.targetUpper i)) :=
    CoverIndexedBoundaryTransitionBoxNeighborhoods.chartTransition_mapsTo_halfSpaceSupportBox_of_boundaryNeighborhood_subset_preimage
      (I := I) (K := K) (C := C)
      (targetChart := D.base.transitionSupportData.targetChart)
      D.base.transitionNeighborhoods
      D.base.targetData.targetBox.targetLower
      D.base.targetData.targetBox.targetUpper
      D.preimage_shrink i
  simpa [D.base.targetData.targetChart_eq i] using hmaps

/-- Convert the preimage-shrink input to the final ambient-`MapsTo` input. -/
def toMapsToInput :
    CoverIndexedZeroCompactFinalNaturalMapsToInput
      (I := I) (K := K) C P omega muBulk where
  base := D.base
  chartTransition_mapsTo :=
    D.chartTransition_mapsTo
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)

/-- Represented compact-support Stokes from preimage shrink. -/
theorem representedStokes_and_zeroSourceTargetBulkAssembly
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    (D.base.carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) D.base.neighborhoodData
        D.base.measure_eq_volume).globalIntegral =
        ∫ y,
          P.coverIndexBoundaryTargetZeroPieceSum
            D.base.targetData.targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real)) ∧
      D.base.transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        ∫ y,
          P.coverIndexBoundaryTargetZeroPieceSum
            D.base.targetData.targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real)) := by
  simpa [toMapsToInput] using
    (D.toMapsToInput
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)).representedStokes_and_zeroSourceTargetBulkAssembly

end CoverIndexedZeroCompactFinalNaturalPreimageShrinkInput

/--
A cover-indexed family of source-shrink maps-to data synchronized with the
currently selected source and target boxes.

This family projects to the tangential boundary `MapsTo`.  It does not by
itself produce the ambient half-space `MapsTo` needed for target-zero support.
-/
structure CoverIndexedBoundarySourceShrinkMapsToFamily
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n)
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega) where
  sourcePoint :
    {x : M // x ∈ C.boundaryCenters} → Fin n → Real
  sourceShrink :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      BoundaryChartSourceShrinkMapsToData I
        (C.boundaryChart i.1) (targetBox.targetChart i)
        (C.boundaryLower i.1) (C.boundaryUpper i.1)
        (targetBox.targetLower i) (targetBox.targetUpper i)
        (sourcePoint i)
  sourceLower_eq_selected :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      (sourceShrink i).sourceLowerCorner = C.boundaryLower i.1
  sourceUpper_eq_selected :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      (sourceShrink i).sourceUpperCorner = C.boundaryUpper i.1

namespace CoverIndexedBoundarySourceShrinkMapsToFamily

variable
    {targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega}

/-- The tangential boundary `MapsTo` supplied by source-shrink data. -/
theorem tangential_mapsTo
    (D :
      CoverIndexedBoundarySourceShrinkMapsToFamily
        (I := I) (K := K) C P omega targetBox) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      MapsTo
        (boundaryChartTransition I
          (C.boundaryChart i.1) (targetBox.targetChart i))
        (lowerZeroFaceDomain (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (lowerZeroFaceDomain (targetBox.targetLower i)
          (targetBox.targetUpper i)) := by
  intro i
  simpa [D.sourceLower_eq_selected i, D.sourceUpper_eq_selected i] using
    (D.sourceShrink i).mapsTo_selectedTarget

end CoverIndexedBoundarySourceShrinkMapsToFamily

/--
Final natural input that records a source-shrink family.

The source-shrink family is useful and theorem-facing, but it is only
tangential.  Therefore this input still contains the missing ambient lift as
`ambient_chartTransition_mapsTo`.
-/
structure CoverIndexedZeroCompactFinalNaturalSourceShrinkInput
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n)
    (muBulk : Measure (Fin (n + 1) → Real)) where
  base :
    CoverIndexedZeroCompactFinalNaturalBaseInput
      (I := I) (K := K) C P omega muBulk
  sourceShrinkFamily :
    CoverIndexedBoundarySourceShrinkMapsToFamily
      (I := I) (K := K) C P omega base.targetData.targetBox
  ambient_chartTransition_mapsTo :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      MapsTo
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (base.targetData.targetBox.targetChart i))
        (halfSpaceSupportBox (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (Icc (base.targetData.targetBox.targetLower i)
          (base.targetData.targetBox.targetUpper i))

namespace CoverIndexedZeroCompactFinalNaturalSourceShrinkInput

variable
    (D :
      CoverIndexedZeroCompactFinalNaturalSourceShrinkInput
        (I := I) (K := K) C P omega muBulk)

/-- Projection of the tangential boundary maps-to data carried by source shrink. -/
theorem tangential_mapsTo :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      MapsTo
        (boundaryChartTransition I
          (C.boundaryChart i.1) (D.base.targetData.targetBox.targetChart i))
        (lowerZeroFaceDomain (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (lowerZeroFaceDomain (D.base.targetData.targetBox.targetLower i)
          (D.base.targetData.targetBox.targetUpper i)) :=
  CoverIndexedBoundarySourceShrinkMapsToFamily.tangential_mapsTo
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    D.sourceShrinkFamily

/-- Convert the source-shrink final input to the ambient-`MapsTo` endpoint. -/
def toMapsToInput :
    CoverIndexedZeroCompactFinalNaturalMapsToInput
      (I := I) (K := K) C P omega muBulk where
  base := D.base
  chartTransition_mapsTo := D.ambient_chartTransition_mapsTo

/-- Represented compact-support Stokes with source-shrink data recorded. -/
theorem representedStokes_and_zeroSourceTargetBulkAssembly
    [IsFiniteMeasureOnCompacts muBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    (D.base.carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := omega)
        (μBulk := muBulk) D.base.neighborhoodData
        D.base.measure_eq_volume).globalIntegral =
        ∫ y,
          P.coverIndexBoundaryTargetZeroPieceSum
            D.base.targetData.targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real)) ∧
      D.base.transitionSupportData.boundaryZeroBulkSetIntegralSum
          (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        ∫ y,
          P.coverIndexBoundaryTargetZeroPieceSum
            D.base.targetData.targetBox.targetChart omega y
          ∂(volume : Measure (Fin n → Real)) := by
  simpa [toMapsToInput] using
    (D.toMapsToInput
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)).representedStokes_and_zeroSourceTargetBulkAssembly

end CoverIndexedZeroCompactFinalNaturalSourceShrinkInput

end CoverIndexedZeroCompactFinalNaturalTheorem

end Stokes

end
