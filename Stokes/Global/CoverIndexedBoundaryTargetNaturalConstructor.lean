import Stokes.Global.CoverIndexedBoundarySupportContinuityConstructor

/-!
# Natural target-chart support/continuity constructors

This file removes one more layer of manual boundary target fields in the
cover-indexed compact-support route.  The measure constructors only need
compactness, continuity, and support of the scalar boundary target pieces.
Those are already derivable from the ambient target-chart representative:

* `ContDiffOn`/`ContinuousOn` of `ManifoldForm.inChart` on the ambient target box;
* topological support of that representative contained in the ambient target box.

The constructors here package that natural input and expose two common ways to
produce the smoothness field: directly from chartwise smoothness of localized
pieces, or from an existing self transition-pullback smoothness statement.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedBoundaryTargetNaturalConstructor

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

/-- Target-chart `inChart` smoothness from a self transition-pullback
smoothness statement on the same target box.  This is useful when upstream code
has already built smoothness through the transition-pullback API. -/
theorem boundaryTargetInChart_contDiffOn_of_transitionPullback
    [IsManifold I 1 M]
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (targetBox_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetLower i) (targetUpper i) ⊆
          ManifoldForm.chartOverlap I (targetChart i) (targetChart i))
    (targetTransition_contDiffOn :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ⊤
          (ManifoldForm.transitionPullbackInChart I
            (targetChart i) (targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i)))
          (Icc (targetLower i) (targetUpper i)))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContDiffOn Real ⊤
      (ManifoldForm.inChart I (targetChart i)
        (P.coverIndexLocalizedForm ω (Sum.inr i)))
      (Icc (targetLower i) (targetUpper i)) :=
  ManifoldForm.contDiffOn_inChart_of_transitionPullback
    (I := I) (targetBox_subset_overlap i) (targetTransition_contDiffOn i)

/-- Target-chart `inChart` smoothness from chartwise smoothness of the
localized boundary piece and target-box containment in the chart target. -/
theorem boundaryTargetInChart_contDiffOn_of_localizedChartwiseSmooth
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (localizedChartwiseSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ManifoldForm.ChartwiseSmooth I
          (P.coverIndexLocalizedForm ω (Sum.inr i)))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetLower i) (targetUpper i) ⊆
          (extChartAt I (targetChart i)).target)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContDiffOn Real ⊤
      (ManifoldForm.inChart I (targetChart i)
        (P.coverIndexLocalizedForm ω (Sum.inr i)))
      (Icc (targetLower i) (targetUpper i)) :=
  (localizedChartwiseSmooth i).contDiffOn_inChart
    (I := I) (targetChart i) (targetBox_subset_target i)

end SupportControlledSelectedPartition

/-- Natural ambient target-chart data for the boundary target pieces.

This is one step closer to the mathematical input than
`CoverIndexedBoundaryTargetSupportContinuityData`: continuity is recorded as
smoothness of the ambient `inChart` representative on the target box, while
support is recorded before restricting to the lower-zero boundary face. -/
structure CoverIndexedBoundaryTargetInChartBoxData
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
  /-- Ambient target-chart localized representatives are smooth on target boxes. -/
  targetInChart_contDiffOn :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      ContDiffOn Real ⊤
        (ManifoldForm.inChart I (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i)))
        (Icc (targetLower i) (targetUpper i))
  /-- Ambient target-chart localized representatives are supported in target boxes. -/
  targetInChart_tsupport_subset :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      tsupport
          (ManifoldForm.inChart I (targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
        Icc (targetLower i) (targetUpper i)

namespace CoverIndexedBoundaryTargetInChartBoxData

variable
  (D :
    CoverIndexedBoundaryTargetInChartBoxData
      (C := C) P ω targetChart targetLower targetUpper)

/-- Forget ambient `inChart` smoothness to the support/continuity data consumed
by the boundary target measure constructors. -/
def toSupportContinuityData :
    CoverIndexedBoundaryTargetSupportContinuityData
      (C := C) P ω targetChart targetLower targetUpper where
  targetLower_zero := D.targetLower_zero
  targetLower_le_upper := D.targetLower_le_upper
  targetInChart_continuousOn := fun i =>
    (D.targetInChart_contDiffOn i).continuousOn
  targetInChart_tsupport_subset := D.targetInChart_tsupport_subset

@[simp]
theorem toSupportContinuityData_targetLower_zero
    (i : {x : M // x ∈ C.boundaryCenters}) :
    D.toSupportContinuityData.targetLower_zero i =
      D.targetLower_zero i :=
  rfl

@[simp]
theorem toSupportContinuityData_targetLower_le_upper
    (i : {x : M // x ∈ C.boundaryCenters}) :
    D.toSupportContinuityData.targetLower_le_upper i =
      D.targetLower_le_upper i :=
  rfl

theorem piece_continuousOn
    (D :
      CoverIndexedBoundaryTargetInChartBoxData
        (C := C) P ω targetChart targetLower targetUpper)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContinuousOn
      (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i))
      (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper
        (Sum.inr i)) :=
  CoverIndexedBoundaryTargetSupportContinuityData.piece_continuousOn
    (toSupportContinuityData D) i

theorem piece_tsupport_subset
    (D :
      CoverIndexedBoundaryTargetInChartBoxData
        (C := C) P ω targetChart targetLower targetUpper)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i)) ⊆
      P.coverIndexBoundaryTargetPieceSet targetLower targetUpper
        (Sum.inr i) :=
  CoverIndexedBoundaryTargetSupportContinuityData.piece_tsupport_subset
    (toSupportContinuityData D) i

end CoverIndexedBoundaryTargetInChartBoxData

namespace CoverIndexedBoundaryTargetSupportContinuityData

/-- Constructor from target-box `ContDiffOn` of the ambient `inChart`
representatives. -/
def ofTargetInChartContDiffOn
    (targetLower_zero :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i 0 = 0)
    (targetLower_le_upper :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i ≤ targetUpper i)
    (targetInChart_contDiffOn :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ⊤
          (ManifoldForm.inChart I (targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i)))
          (Icc (targetLower i) (targetUpper i)))
    (targetInChart_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          Icc (targetLower i) (targetUpper i)) :
    CoverIndexedBoundaryTargetSupportContinuityData
      (C := C) P ω targetChart targetLower targetUpper :=
  (CoverIndexedBoundaryTargetInChartBoxData.mk
    targetLower_zero targetLower_le_upper targetInChart_contDiffOn
    targetInChart_tsupport_subset).toSupportContinuityData

/-- `C^\infty` variant matching the smoothness level normally produced by
mathlib's smooth partition API.  The target measure fields only need
continuity, so `C^\infty` smoothness is enough here. -/
def ofTargetInChartContDiffOnInfty
    (targetLower_zero :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i 0 = 0)
    (targetLower_le_upper :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i ≤ targetUpper i)
    (targetInChart_contDiffOn :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.inChart I (targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i)))
          (Icc (targetLower i) (targetUpper i)))
    (targetInChart_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          Icc (targetLower i) (targetUpper i)) :
    CoverIndexedBoundaryTargetSupportContinuityData
      (C := C) P ω targetChart targetLower targetUpper where
  targetLower_zero := targetLower_zero
  targetLower_le_upper := targetLower_le_upper
  targetInChart_continuousOn := fun i =>
    (targetInChart_contDiffOn i).continuousOn
  targetInChart_tsupport_subset := targetInChart_tsupport_subset

/-- Constructor from chartwise smoothness of each localized boundary piece. -/
def ofLocalizedChartwiseSmooth
    (targetLower_zero :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i 0 = 0)
    (targetLower_le_upper :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i ≤ targetUpper i)
    (localizedChartwiseSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ManifoldForm.ChartwiseSmooth I
          (P.coverIndexLocalizedForm ω (Sum.inr i)))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetLower i) (targetUpper i) ⊆
          (extChartAt I (targetChart i)).target)
    (targetInChart_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          Icc (targetLower i) (targetUpper i)) :
    CoverIndexedBoundaryTargetSupportContinuityData
      (C := C) P ω targetChart targetLower targetUpper :=
  ofTargetInChartContDiffOn
    (C := C) (P := P) (ω := ω)
    (targetChart := targetChart)
    (targetLower := targetLower) (targetUpper := targetUpper)
    targetLower_zero targetLower_le_upper
    (P.boundaryTargetInChart_contDiffOn_of_localizedChartwiseSmooth
      targetChart targetLower targetUpper localizedChartwiseSmooth
      targetBox_subset_target)
    targetInChart_tsupport_subset

/-- Constructor from self transition-pullback smoothness on the target box. -/
def ofTargetSelfTransitionPullback
    [IsManifold I 1 M]
    (targetLower_zero :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i 0 = 0)
    (targetLower_le_upper :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i ≤ targetUpper i)
    (targetBox_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetLower i) (targetUpper i) ⊆
          ManifoldForm.chartOverlap I (targetChart i) (targetChart i))
    (targetTransition_contDiffOn :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ⊤
          (ManifoldForm.transitionPullbackInChart I
            (targetChart i) (targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i)))
          (Icc (targetLower i) (targetUpper i)))
    (targetInChart_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          Icc (targetLower i) (targetUpper i)) :
    CoverIndexedBoundaryTargetSupportContinuityData
      (C := C) P ω targetChart targetLower targetUpper :=
  ofTargetInChartContDiffOn
    (C := C) (P := P) (ω := ω)
    (targetChart := targetChart)
    (targetLower := targetLower) (targetUpper := targetUpper)
    targetLower_zero targetLower_le_upper
    (P.boundaryTargetInChart_contDiffOn_of_transitionPullback
      targetChart targetLower targetUpper targetBox_subset_overlap
      targetTransition_contDiffOn)
    targetInChart_tsupport_subset

end CoverIndexedBoundaryTargetSupportContinuityData

end CoverIndexedBoundaryTargetNaturalConstructor

end Stokes

end
