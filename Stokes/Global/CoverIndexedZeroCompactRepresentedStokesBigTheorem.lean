import Stokes.Global.CoverIndexedZeroCompactFinalNaturalTheorem
import Stokes.Global.CoverIndexedZeroCompactPreimageShrink

/-!
# Big compact-support represented Stokes assembly

This file is the theorem-facing assembly layer for the compact-support
represented Stokes milestone.

The main structure,
`CoverIndexedZeroCompactBoundaryAmbientShrinkData`, packages the large
geometric datum still missing from a fully natural theorem:

* the compact-support/partition refinement has already selected boundary
  half-space source boxes;
* each source box has an ambient open neighborhood inside the relevant chart
  target and chart overlap;
* a target open box-neighborhood is chosen inside the selected target `Icc`;
* the selected source `Icc` lies in the preimage of that target open set.

From this datum we derive the honest ambient half-space containment

`MapsTo (ManifoldForm.chartTransition I sourceChart targetChart)
  (halfSpaceSupportBox sourceLower sourceUpper) targetIcc`.

This is deliberately stronger than the existing source-shrink tangential
`MapsTo` on the lower-zero boundary face.  Tangential control is not enough for
the compact-support endpoint, which needs the whole half-space support box.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactRepresentedStokesBigTheorem

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
The large geometric shrink datum needed after compact support has been
refined into finitely many boundary chart boxes.

Mathematically, this packages the step

`compact support → finite box refinement → ambient chart-transition shrink`.

The finite refinement itself is represented by the already-selected cover and
partition data `C` and `P`; this record is the certificate that those selected
source/target boxes have enough ambient room to feed the represented Stokes
endpoint.
-/
structure CoverIndexedZeroCompactBoundaryAmbientShrinkData
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (targetData :
      CoverIndexedZeroCompactRelativeTargetBoxData
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData) where
  sourceShrink :
    CoverIndexedInnerOuterSourceBoxSelection
      (I := I) (K := K) C targetData.targetBox.targetChart
  targetOpen :
    {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real)
  targetOpen_open :
    ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (targetOpen i)
  targetOpen_subset_selectedBox :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      targetOpen i ⊆
        Icc (targetData.targetBox.targetLower i)
          (targetData.targetBox.targetUpper i)
  sourceBox_subset_sourceOpen_preimage_targetOpen :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
        (sourceShrink.sourceNeighborhood i).neighborhood ∩
          (ManifoldForm.chartTransition I
            (C.boundaryChart i.1)
            (targetData.targetBox.targetChart i)) ⁻¹'
            targetOpen i

namespace CoverIndexedZeroCompactBoundaryAmbientShrinkData

variable
    {transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega}
    {targetData :
      CoverIndexedZeroCompactRelativeTargetBoxData
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData}
    (D :
      CoverIndexedZeroCompactBoundaryAmbientShrinkData
        (I := I) (K := K) C P omega transitionSupportData targetData)

/--
The ambient half-space `MapsTo` required by the selected compact endpoint.

This is the precise place where the big shrink datum is consumed.
-/
def chartTransition_mapsTo [IsManifold I ⊤ M] :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      MapsTo
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (targetData.targetBox.targetChart i))
        (halfSpaceSupportBox (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (Icc (targetData.targetBox.targetLower i)
          (targetData.targetBox.targetUpper i)) :=
  targetData.chartTransitionMapsToField_of_innerOuter_preimage_shrink
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    D.sourceShrink D.targetOpen D.targetOpen_open
    D.targetOpen_subset_selectedBox
    D.sourceBox_subset_sourceOpen_preimage_targetOpen

end CoverIndexedZeroCompactBoundaryAmbientShrinkData

/--
Big compact-support represented Stokes input.

This is the intended theorem-facing package: all low-level support, transition,
target-box, and orientation endpoint data are stored in `base`, while the
remaining large mathematical certificate is the boundary ambient shrink data.
-/
structure CoverIndexedZeroCompactRepresentedStokesBigInput
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n)
    (muBulk : Measure (Fin (n + 1) → Real)) where
  base :
    CoverIndexedZeroCompactFinalNaturalBaseInput
      (I := I) (K := K) C P omega muBulk
  boundaryAmbientShrinkData :
    CoverIndexedZeroCompactBoundaryAmbientShrinkData
      (I := I) (K := K) C P omega
      base.transitionSupportData base.targetData

namespace CoverIndexedZeroCompactRepresentedStokesBigInput

variable
    (D :
      CoverIndexedZeroCompactRepresentedStokesBigInput
        (I := I) (K := K) C P omega muBulk)

/-- Convert the big input to the final endpoint input with ambient `MapsTo`. -/
def toFinalNaturalMapsToInput [IsManifold I ⊤ M] :
    CoverIndexedZeroCompactFinalNaturalMapsToInput
      (I := I) (K := K) C P omega muBulk where
  base := D.base
  chartTransition_mapsTo :=
    D.boundaryAmbientShrinkData.chartTransition_mapsTo
      (I := I) (K := K) (C := C) (P := P) (omega := omega)

/--
Compact-support represented Stokes from the big boundary ambient shrink datum.

The theorem no longer exposes the target-zero support field, boundary-box
preimage field, or raw ambient `MapsTo`; all of that is derived from
`boundaryAmbientShrinkData`.
-/
theorem representedStokes_of_boundaryAmbientShrinkData
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
  simpa [toFinalNaturalMapsToInput] using
    (D.toFinalNaturalMapsToInput
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      (muBulk := muBulk)).representedStokes_and_zeroSourceTargetBulkAssembly

end CoverIndexedZeroCompactRepresentedStokesBigInput

end CoverIndexedZeroCompactRepresentedStokesBigTheorem

end Stokes

end
