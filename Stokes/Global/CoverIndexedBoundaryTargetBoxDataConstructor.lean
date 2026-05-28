import Stokes.Global.CoverIndexedBoundaryCOVNaturalConstructor
import Stokes.Global.CoverIndexedBoundaryAESumConstructor
import Stokes.Global.CoverIndexedBoundaryTargetNaturalConstructor
import Stokes.BoundaryChart.TargetImageSelectedBoxAuto

/-!
# Cover-indexed boundary target-box data constructors

This file packages the real target-box data needed by the natural
cover-indexed boundary route.  The central record stores, for every boundary
cover index, a selected source-to-target boundary box together with a
`BoundaryChartTargetBoxSelection`.  Therefore the downstream fields

* `sourceTargetSelectedBox`, and
* `boundaryChartSelectedBoxImageData`

are projections, not fresh assumptions.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedBoundaryTargetBoxDataConstructor

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/--
Boundary target-box data for the cover-indexed route.

For each selected boundary center, `targetImage` is the single-chart package
containing both the selected source-to-target box and the target image box
data.  This is the natural grouped input just above
`CoverIndexedTargetBoundaryMeasureData`.
-/
structure CoverIndexedBoundaryTargetBoxData
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) where
  /-- Target chart for each selected boundary center. -/
  targetChart : {x : M // x ∈ C.boundaryCenters} → M
  /-- Per-index selected source box plus target image-box selection. -/
  targetImage :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      BoundaryChartSelectedBoxTargetImageAutoData I
        (C.boundaryChart i.1) (targetChart i)
        (P.coverIndexLocalizedForm ω (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1)

namespace CoverIndexedBoundaryTargetBoxData

variable
    (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω)

/-- The packaged target-box selection at a boundary cover index. -/
abbrev targetSelection
    (i : {x : M // x ∈ C.boundaryCenters}) :
    BoundaryChartTargetBoxSelection I
      (C.boundaryChart i.1) (D.targetChart i)
      (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  (D.targetImage i).targetBox

/-- Lower target corner selected at a boundary cover index. -/
abbrev targetLower
    (i : {x : M // x ∈ C.boundaryCenters}) :
    Fin (n + 1) → Real :=
  (D.targetImage i).targetLowerCorner

/-- Upper target corner selected at a boundary cover index. -/
abbrev targetUpper
    (i : {x : M // x ∈ C.boundaryCenters}) :
    Fin (n + 1) → Real :=
  (D.targetImage i).targetUpperCorner

/-- The source-to-target selected box is stored in the per-index auto data. -/
theorem sourceTargetSelectedBox
    (i : {x : M // x ∈ C.boundaryCenters}) :
    boundaryChartSelectedBox I
      (C.boundaryChart i.1) (D.targetChart i)
      (P.coverIndexLocalizedForm ω (Sum.inr i))
      (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  (D.targetImage i).selectedBox

/-- The selected target image-data field is projected from the target box. -/
theorem boundaryChartSelectedBoxImageData
    (i : {x : M // x ∈ C.boundaryCenters}) :
    _root_.Stokes.boundaryChartSelectedBoxImageData I
      (C.boundaryChart i.1) (D.targetChart i)
      (C.boundaryLower i.1) (C.boundaryUpper i.1)
      (D.targetLower i) (D.targetUpper i) :=
  (D.targetImage i).imageData

/-- Target lower corners lie on the lower zero face. -/
theorem targetLower_zero
    (i : {x : M // x ∈ C.boundaryCenters}) :
    D.targetLower i 0 = 0 :=
  (D.targetImage i).targetLowerCorner_zero

/-- Target corners are ordered. -/
theorem targetLower_le_targetUpper
    (i : {x : M // x ∈ C.boundaryCenters}) :
    D.targetLower i ≤ D.targetUpper i :=
  (D.targetImage i).targetLower_le_targetUpper

/-- Constructor from the explicit selected source-to-target boxes and packaged
target-box selections. -/
def ofTargetSelection
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (targetSelection :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartTargetBoxSelection I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω where
  targetChart := targetChart
  targetImage := fun i =>
    BoundaryChartSelectedBoxTargetImageAutoData.ofTargetBoxSelection
      (sourceTargetSelectedBox i) (targetSelection i)

/-- Constructor from already materialized single-chart auto data. -/
def ofTargetImage
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetImage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartSelectedBoxTargetImageAutoData I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω where
  targetChart := targetChart
  targetImage := targetImage

/-- Forget target-box data to the indexed target-selection orientation input. -/
def toTargetSelectionInput :
    CoverIndexedBoundaryChartTargetSelectionInput (M := M) I
      {x : M // x ∈ C.boundaryCenters} where
  sourceChart := fun i => C.boundaryChart i.1
  targetChart := D.targetChart
  form := fun i => P.coverIndexLocalizedForm ω (Sum.inr i)
  lower := fun i => C.boundaryLower i.1
  upper := fun i => C.boundaryUpper i.1
  selectedBox := fun i => D.sourceTargetSelectedBox i
  targetSelection := fun i => D.targetSelection i

@[simp]
theorem toTargetSelectionInput_targetChart :
    D.toTargetSelectionInput.targetChart = D.targetChart :=
  rfl

@[simp]
theorem toTargetSelectionInput_targetSelection
    (i : {x : M // x ∈ C.boundaryCenters}) :
    D.toTargetSelectionInput.targetSelection i = D.targetSelection i :=
  rfl

/-- Ambient target-chart data from target-box data plus the two genuine
analytic fields still needed for boundary support/continuity. -/
def toTargetInChartBoxData
    (targetInChart_contDiffOn :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ⊤
          (ManifoldForm.inChart I (D.targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i)))
          (Icc (D.targetLower i) (D.targetUpper i)))
    (targetInChart_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (D.targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          Icc (D.targetLower i) (D.targetUpper i)) :
    CoverIndexedBoundaryTargetInChartBoxData
      (C := C) P ω D.targetChart D.targetLower D.targetUpper where
  targetLower_zero := D.targetLower_zero
  targetLower_le_upper := D.targetLower_le_targetUpper
  targetInChart_contDiffOn := targetInChart_contDiffOn
  targetInChart_tsupport_subset := targetInChart_tsupport_subset

/-- Target support/continuity data from target-box data plus target in-chart
smoothness and support control. -/
def toSupportContinuityData
    (targetInChart_contDiffOn :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ⊤
          (ManifoldForm.inChart I (D.targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i)))
          (Icc (D.targetLower i) (D.targetUpper i)))
    (targetInChart_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (D.targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          Icc (D.targetLower i) (D.targetUpper i)) :
    CoverIndexedBoundaryTargetSupportContinuityData
      (C := C) P ω D.targetChart D.targetLower D.targetUpper :=
  (D.toTargetInChartBoxData
    targetInChart_contDiffOn targetInChart_tsupport_subset).toSupportContinuityData

/-- Build natural target-boundary measure data from an oriented atlas, using
the canonical target-piece-sum boundary representative. -/
def toTargetBoundaryMeasureDataOfOrientedAtlas
    [IsManifold I 1 M]
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      D.targetChart i ∈ A.charts)
    (supportContinuity :
      CoverIndexedBoundaryTargetSupportContinuityData
        (C := C) P ω D.targetChart D.targetLower D.targetUpper)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum D.targetChart ω y
          ∂(volume : Measure (Fin n → Real))) :
    CoverIndexedTargetBoundaryMeasureData (I := I) (K := K) C P ω :=
  CoverIndexedTargetBoundaryMeasureData.ofTargetSelectionOrientedAtlas
    (C := C) (P := P) (ω := ω) (targetChart := D.targetChart)
    localData A (fun i => D.targetSelection i)
    (fun i => D.sourceTargetSelectedBox i)
    hsource htarget
    (P.coverIndexBoundaryTargetPieceSum D.targetChart ω)
    globalIntegral globalIntegral_eq_integral
    supportContinuity.piece_isCompact
    supportContinuity.piece_continuousOn
    supportContinuity.piece_tsupport_subset
    (P.coverIndexBoundaryTargetPieceSum_ae_eq_pieceSum D.targetChart ω)

/-- Build natural target-boundary measure data from oriented-manifold data,
using the canonical target-piece-sum boundary representative. -/
def toTargetBoundaryMeasureDataOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (supportContinuity :
      CoverIndexedBoundaryTargetSupportContinuityData
        (C := C) P ω D.targetChart D.targetLower D.targetUpper)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum D.targetChart ω y
          ∂(volume : Measure (Fin n → Real))) :
    CoverIndexedTargetBoundaryMeasureData (I := I) (K := K) C P ω :=
  CoverIndexedTargetBoundaryMeasureData.ofTargetSelectionOrientedManifold
    (C := C) (P := P) (ω := ω) (targetChart := D.targetChart)
    localData (fun i => D.targetSelection i)
    (fun i => D.sourceTargetSelectedBox i)
    (P.coverIndexBoundaryTargetPieceSum D.targetChart ω)
    globalIntegral globalIntegral_eq_integral
    supportContinuity.piece_isCompact
    supportContinuity.piece_continuousOn
    supportContinuity.piece_tsupport_subset
    (P.coverIndexBoundaryTargetPieceSum_ae_eq_pieceSum D.targetChart ω)

end CoverIndexedBoundaryTargetBoxData

end CoverIndexedBoundaryTargetBoxDataConstructor

end Stokes

end
