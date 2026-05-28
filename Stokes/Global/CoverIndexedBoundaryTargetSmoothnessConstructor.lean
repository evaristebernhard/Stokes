import Stokes.Global.CoverIndexedBoundaryTargetBoxDataConstructor
import Stokes.Global.CoverIndexedBoundaryTargetSupportFromImage

/-!
# Boundary target-chart smoothness constructors

This file isolates the smoothness half of the target-boundary natural route.
The support half is handled by `CoverIndexedBoundaryTargetSupportFromImage`:
once image support has pushed the ambient target representative into the target
box, the constructors here supply the remaining `C^\infty` `ContDiffOn` field.

The main mathematical step is simple but important: if each localized boundary
piece is chartwise smooth, then its ambient representative in the selected
target chart is smooth on any target box contained in that chart target.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedBoundaryTargetSmoothnessConstructor

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
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

/-- `C^\infty` target-chart smoothness from chartwise smoothness of each
localized boundary piece.

This is the explicit `↑∞` version normally needed by the compact-support
route.  The existing chartwise bridge proves the stronger project-local `⊤`
statement, and we downgrade it to the mathlib smooth-partition level. -/
theorem boundaryTargetInChart_contDiffOn_infty_of_localizedChartwiseSmooth
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
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.inChart I (targetChart i)
        (P.coverIndexLocalizedForm ω (Sum.inr i)))
      (Icc (targetLower i) (targetUpper i)) :=
  (P.boundaryTargetInChart_contDiffOn_of_localizedChartwiseSmooth
    (ω := ω) targetChart targetLower targetUpper
    localizedChartwiseSmooth targetBox_subset_target i).of_le le_top

/-- `C^\infty` target-chart smoothness from a self transition-pullback
smoothness statement on the target overlap.

This is useful for call sites that already constructed smoothness through the
transition-pullback API rather than through global chartwise smoothness of the
localized form. -/
theorem boundaryTargetInChart_contDiffOn_infty_of_transitionPullback
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
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionPullbackInChart I
            (targetChart i) (targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i)))
          (Icc (targetLower i) (targetUpper i)))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.inChart I (targetChart i)
        (P.coverIndexLocalizedForm ω (Sum.inr i)))
      (Icc (targetLower i) (targetUpper i)) :=
  (targetTransition_contDiffOn i).congr
    (fun _ hy =>
      (ManifoldForm.transitionPullbackInChart_eq_inChart
        (I := I) (targetChart i) (targetChart i)
        (P.coverIndexLocalizedForm ω (Sum.inr i))
        (targetBox_subset_overlap i hy)).symm)

end SupportControlledSelectedPartition

namespace CoverIndexedBoundaryTargetSupportContinuityData

/-- Support/continuity data from localized chartwise smoothness at the natural
`C^\infty` level.  The separate support hypothesis is still the real compact
support/image statement. -/
def ofLocalizedChartwiseSmoothInfty
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
  ofTargetInChartContDiffOnInfty
    (C := C) (P := P) (ω := ω)
    (targetChart := targetChart)
    (targetLower := targetLower) (targetUpper := targetUpper)
    targetLower_zero targetLower_le_upper
    (P.boundaryTargetInChart_contDiffOn_infty_of_localizedChartwiseSmooth
      targetChart targetLower targetUpper localizedChartwiseSmooth
      targetBox_subset_target)
    targetInChart_tsupport_subset

end CoverIndexedBoundaryTargetSupportContinuityData

namespace CoverIndexedBoundaryTargetSupportFromImageData

variable
  (D :
    CoverIndexedBoundaryTargetSupportFromImageData
      (C := C) P ω targetChart targetLower targetUpper)

/-- Add localized chartwise smoothness to target-image support data to produce
the support/continuity package consumed by the boundary measure constructors. -/
def toSupportContinuityData_ofLocalizedChartwiseSmooth
    (localizedChartwiseSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ManifoldForm.ChartwiseSmooth I
          (P.coverIndexLocalizedForm ω (Sum.inr i)))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetLower i) (targetUpper i) ⊆
          (extChartAt I (targetChart i)).target) :
    CoverIndexedBoundaryTargetSupportContinuityData
      (C := C) P ω targetChart targetLower targetUpper :=
  D.toSupportContinuityData_ofContDiffOnInfty
    (P.boundaryTargetInChart_contDiffOn_infty_of_localizedChartwiseSmooth
      (ω := ω) targetChart targetLower targetUpper
      localizedChartwiseSmooth targetBox_subset_target)

end CoverIndexedBoundaryTargetSupportFromImageData

namespace CoverIndexedBoundaryTargetBoxData

variable
  (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω)

/-- Target-chart `C^\infty` smoothness for the target boxes stored in
`CoverIndexedBoundaryTargetBoxData`. -/
theorem targetInChart_contDiffOn_infty_of_localizedChartwiseSmooth
    (localizedChartwiseSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ManifoldForm.ChartwiseSmooth I
          (P.coverIndexLocalizedForm ω (Sum.inr i)))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.targetLower i) (D.targetUpper i) ⊆
          (extChartAt I (D.targetChart i)).target)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.inChart I (D.targetChart i)
        (P.coverIndexLocalizedForm ω (Sum.inr i)))
      (Icc (D.targetLower i) (D.targetUpper i)) :=
  P.boundaryTargetInChart_contDiffOn_infty_of_localizedChartwiseSmooth
    (ω := ω) D.targetChart D.targetLower D.targetUpper
    localizedChartwiseSmooth targetBox_subset_target i

/-- The target-image support package associated to the selected target boxes,
leaving only the genuine image-support hypothesis to be proved upstream. -/
def toSupportFromImageData
    (targetInChart_tsupport_subset_image :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (D.targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          boundaryChartTransitionAmbientBoundaryImage I
            (C.boundaryChart i.1) (D.targetChart i)
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedBoundaryTargetSupportFromImageData
      (C := C) P ω D.targetChart D.targetLower D.targetUpper where
  targetLower_zero := D.targetLower_zero
  targetLower_le_upper := D.targetLower_le_targetUpper
  imageData := D.boundaryChartSelectedBoxImageData
  targetInChart_tsupport_subset_image := targetInChart_tsupport_subset_image

/-- Full target support/continuity data from selected target boxes, localized
chartwise smoothness, and the remaining image-support theorem. -/
def toSupportContinuityDataOfLocalizedChartwiseSmooth
    (localizedChartwiseSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ManifoldForm.ChartwiseSmooth I
          (P.coverIndexLocalizedForm ω (Sum.inr i)))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.targetLower i) (D.targetUpper i) ⊆
          (extChartAt I (D.targetChart i)).target)
    (targetInChart_tsupport_subset_image :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (D.targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          boundaryChartTransitionAmbientBoundaryImage I
            (C.boundaryChart i.1) (D.targetChart i)
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedBoundaryTargetSupportContinuityData
      (C := C) P ω D.targetChart D.targetLower D.targetUpper :=
  CoverIndexedBoundaryTargetSupportFromImageData.toSupportContinuityData_ofLocalizedChartwiseSmooth
    (D.toSupportFromImageData targetInChart_tsupport_subset_image)
    localizedChartwiseSmooth targetBox_subset_target

end CoverIndexedBoundaryTargetBoxData

end CoverIndexedBoundaryTargetSmoothnessConstructor

end Stokes

end
