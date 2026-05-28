import Stokes.Global.CoverIndexedBoundarySetIntegralConstructor
import Stokes.Global.BoundaryIntegrabilityCompactSupport

/-!
# Cover-indexed boundary support and continuity constructors

This file removes routine boundary measure fields from the cover-indexed route.
For target boundary boxes, compactness is just compactness of
`lowerZeroFaceDomain`; continuity is inherited from the ambient target chart
representative; and topological support on the ambient target box restricts to
topological support on the lower-zero face.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryTargetSupportContinuity

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/-- Pointwise vanishing off a closed carrier gives topological-support containment. -/
theorem tsupport_subset_of_eq_zero_off_isClosed
    {α : Type*} [TopologicalSpace α] {s : Set α} {f : α → Real}
    (hs : IsClosed s) (hzero : ∀ x, x ∉ s → f x = 0) :
    tsupport f ⊆ s := by
  change closure (Function.support f) ⊆ s
  exact closure_minimal
    (by
      intro x hx
      by_contra hxs
      exact hx (hzero x hxs))
    hs

/-- If an ambient boundary inclusion lies in the ambient box, its tangential
coordinate lies in the lower-zero face domain. -/
theorem mem_lowerZeroFaceDomain_of_boundaryInclusion_mem_Icc
    {a b : Fin (n + 1) → Real} {u : Fin n → Real}
    (hu : boundaryInclusion n u ∈ Icc a b) :
    u ∈ lowerZeroFaceDomain a b := by
  rcases hu with ⟨hlo, hhi⟩
  constructor
  · intro i
    simpa [lowerZeroFaceDomain, faceDomain, Function.comp_def, boundaryInclusion]
      using hlo i.succ
  · intro i
    simpa [lowerZeroFaceDomain, faceDomain, Function.comp_def, boundaryInclusion]
      using hhi i.succ

/-- Target boundary carriers are compact lower-zero face boxes. -/
theorem boundaryTargetInChartPieceSet_isCompact
    (c d : Fin (n + 1) → Real) :
    IsCompact (boundaryTargetInChartPieceSet (n := n) c d) := by
  simpa [boundaryTargetInChartPieceSet] using
    (isCompact_lowerZeroFaceDomain c d : IsCompact (lowerZeroFaceDomain c d))

/-- Target boundary carriers are closed. -/
theorem boundaryTargetInChartPieceSet_isClosed
    (c d : Fin (n + 1) → Real) :
    IsClosed (boundaryTargetInChartPieceSet (n := n) c d) :=
  (boundaryTargetInChartPieceSet_isCompact (n := n) c d).isClosed

/-- Ambient target-chart continuity gives continuity of the signed boundary
integrand on the target lower-zero face. -/
theorem boundaryTargetInChartPieceIntegrand_continuousOn_of_inChart_continuousOn
    (x : M) (ω : ManifoldForm I M n) {c d : Fin (n + 1) → Real}
    (hc0 : c 0 = 0) (hcd : c ≤ d)
    (hω : ContinuousOn (ManifoldForm.inChart I x ω) (Icc c d)) :
    ContinuousOn (boundaryTargetInChartPieceIntegrand I x ω)
      (boundaryTargetInChartPieceSet c d) := by
  have hunsigned :
      ContinuousOn (boundaryChartInChartIntegrand I x ω)
        (lowerZeroFaceDomain c d) :=
    boundaryChartInChartIntegrand_continuousOn_lowerZeroFaceDomain
      I x ω hc0 hcd hω
  change
    ContinuousOn
      (fun u : Fin n → Real =>
        outwardFirstBoundaryOrientationSign n *
          boundaryChartInChartIntegrand I x ω u)
      (lowerZeroFaceDomain c d)
  exact hunsigned.const_mul (outwardFirstBoundaryOrientationSign n)

/-- `ContDiffOn` version of target boundary integrand continuity. -/
theorem boundaryTargetInChartPieceIntegrand_continuousOn_of_inChart_contDiffOn
    (x : M) (ω : ManifoldForm I M n) {c d : Fin (n + 1) → Real}
    (hc0 : c 0 = 0) (hcd : c ≤ d)
    (hω : ContDiffOn Real ⊤ (ManifoldForm.inChart I x ω) (Icc c d)) :
    ContinuousOn (boundaryTargetInChartPieceIntegrand I x ω)
      (boundaryTargetInChartPieceSet c d) :=
  boundaryTargetInChartPieceIntegrand_continuousOn_of_inChart_continuousOn
    (I := I) x ω hc0 hcd hω.continuousOn

/-- If the ambient target-chart representative is supported in the ambient
target box, then the signed boundary scalar is supported in the lower-zero
face target box. -/
theorem boundaryTargetInChartPieceIntegrand_tsupport_subset_of_inChart_tsupport_subset_Icc
    (x : M) (ω : ManifoldForm I M n) {c d : Fin (n + 1) → Real}
    (hω : tsupport (ManifoldForm.inChart I x ω) ⊆ Icc c d) :
    tsupport (boundaryTargetInChartPieceIntegrand I x ω) ⊆
      boundaryTargetInChartPieceSet c d := by
  refine tsupport_subset_of_eq_zero_off_isClosed
    (boundaryTargetInChartPieceSet_isClosed (n := n) c d) ?_
  intro u hu
  have hnotIcc : boundaryInclusion n u ∉ Icc c d := by
    intro hmem
    exact hu
      (by
        simpa [boundaryTargetInChartPieceSet] using
          (mem_lowerZeroFaceDomain_of_boundaryInclusion_mem_Icc
            (n := n) (a := c) (b := d) hmem))
  have hnotTSupport :
      boundaryInclusion n u ∉ tsupport (ManifoldForm.inChart I x ω) := by
    intro hmem
    exact hnotIcc (hω hmem)
  have hnotSupport :
      boundaryInclusion n u ∉
        Function.support (ManifoldForm.inChart I x ω) := by
    intro hmem
    exact hnotTSupport (subset_tsupport (ManifoldForm.inChart I x ω) hmem)
  have hzero : ManifoldForm.inChart I x ω (boundaryInclusion n u) = 0 :=
    Function.notMem_support.mp hnotSupport
  rw [boundaryTargetInChartPieceIntegrand, hzero]
  simp

end BoundaryTargetSupportContinuity

section CoverIndexedBoundarySupportContinuity

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}

namespace SupportControlledSelectedPartition

variable (P : SupportControlledSelectedPartition C)

/-- All cover-indexed target boundary carriers are compact; interior indices use
the empty carrier. -/
theorem coverIndexBoundaryTargetPieceSet_isCompact
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (j : C.CoverIndex) :
    IsCompact (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper j) := by
  rcases j with i | i
  · simp [coverIndexBoundaryTargetPieceSet]
  · simpa [coverIndexBoundaryTargetPieceSet, boundaryTargetInChartPieceSet] using
      (isCompact_lowerZeroFaceDomain (targetLower i) (targetUpper i))

/-- Boundary-index continuity field generated from ambient target-chart
continuity on the target box. -/
theorem coverIndexBoundaryTargetPieceIntegrand_continuousOn_of_inChart_continuousOn
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (targetLower_zero :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i 0 = 0)
    (targetLower_le_upper :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i ≤ targetUpper i)
    (targetInChart_continuousOn :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContinuousOn
          (ManifoldForm.inChart I (targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i)))
          (Icc (targetLower i) (targetUpper i)))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContinuousOn
      (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i))
      (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper (Sum.inr i)) := by
  simpa [coverIndexBoundaryTargetPieceSet, coverIndexBoundaryTargetPieceIntegrand] using
    boundaryTargetInChartPieceIntegrand_continuousOn_of_inChart_continuousOn
      (I := I) (x := targetChart i)
      (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
      (c := targetLower i) (d := targetUpper i)
      (targetLower_zero i) (targetLower_le_upper i)
      (targetInChart_continuousOn i)

/-- `ContDiffOn` version of the cover-indexed target boundary continuity
field. -/
theorem coverIndexBoundaryTargetPieceIntegrand_continuousOn_of_inChart_contDiffOn
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
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
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContinuousOn
      (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i))
      (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper (Sum.inr i)) :=
  P.coverIndexBoundaryTargetPieceIntegrand_continuousOn_of_inChart_continuousOn
    (ω := ω) targetChart targetLower targetUpper targetLower_zero
    targetLower_le_upper (fun i => (targetInChart_contDiffOn i).continuousOn) i

/-- Boundary-index support field generated from ambient target-chart support in
the target box. -/
theorem coverIndexBoundaryTargetPieceIntegrand_tsupport_subset_of_inChart_tsupport_subset_Icc
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (targetInChart_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          Icc (targetLower i) (targetUpper i))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i)) ⊆
      P.coverIndexBoundaryTargetPieceSet targetLower targetUpper (Sum.inr i) := by
  simpa [coverIndexBoundaryTargetPieceSet, coverIndexBoundaryTargetPieceIntegrand] using
    boundaryTargetInChartPieceIntegrand_tsupport_subset_of_inChart_tsupport_subset_Icc
      (I := I) (x := targetChart i)
      (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
      (c := targetLower i) (d := targetUpper i)
      (targetInChart_tsupport_subset i)

/-- All-index continuity field; interior indices are the zero function on the
empty carrier. -/
theorem coverIndexBoundaryTargetPieceIntegrand_continuousOn_all
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (targetLower_zero :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i 0 = 0)
    (targetLower_le_upper :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i ≤ targetUpper i)
    (targetInChart_continuousOn :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContinuousOn
          (ManifoldForm.inChart I (targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i)))
          (Icc (targetLower i) (targetUpper i)))
    (j : C.CoverIndex) :
    ContinuousOn
      (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j)
      (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper j) := by
  rcases j with i | i
  · simp [coverIndexBoundaryTargetPieceSet, coverIndexBoundaryTargetPieceIntegrand]
  · exact
      P.coverIndexBoundaryTargetPieceIntegrand_continuousOn_of_inChart_continuousOn
        (ω := ω) targetChart targetLower targetUpper targetLower_zero
        targetLower_le_upper targetInChart_continuousOn i

/-- All-index support field; interior indices are the zero function on the
empty carrier. -/
theorem coverIndexBoundaryTargetPieceIntegrand_tsupport_subset_all
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (targetInChart_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          Icc (targetLower i) (targetUpper i))
    (j : C.CoverIndex) :
    tsupport (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j) ⊆
      P.coverIndexBoundaryTargetPieceSet targetLower targetUpper j := by
  rcases j with i | i
  · simp [coverIndexBoundaryTargetPieceSet, coverIndexBoundaryTargetPieceIntegrand]
  · exact
      P.coverIndexBoundaryTargetPieceIntegrand_tsupport_subset_of_inChart_tsupport_subset_Icc
        (ω := ω) targetChart targetLower targetUpper
        targetInChart_tsupport_subset i

end SupportControlledSelectedPartition

/-- Grouped natural data producing the compactness, continuity, and support
fields required by target-COV boundary measure constructors. -/
structure CoverIndexedBoundaryTargetSupportContinuityData
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
  /-- Ambient target-chart scalar representatives are continuous on target boxes. -/
  targetInChart_continuousOn :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      ContinuousOn
        (ManifoldForm.inChart I (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i)))
        (Icc (targetLower i) (targetUpper i))
  /-- Ambient target-chart representatives are supported in target boxes. -/
  targetInChart_tsupport_subset :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      tsupport
          (ManifoldForm.inChart I (targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
        Icc (targetLower i) (targetUpper i)

namespace CoverIndexedBoundaryTargetSupportContinuityData

variable {P : SupportControlledSelectedPartition C}
variable {targetChart : {x : M // x ∈ C.boundaryCenters} → M}
variable {targetLower targetUpper :
  {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real}

/-- Compactness field for genuine boundary indices. -/
theorem piece_isCompact
    (D :
      CoverIndexedBoundaryTargetSupportContinuityData
        (C := C) P ω targetChart targetLower targetUpper)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    IsCompact (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper
      (Sum.inr i)) :=
  P.coverIndexBoundaryTargetPieceSet_isCompact targetLower targetUpper (Sum.inr i)

/-- Continuity field for genuine boundary indices. -/
theorem piece_continuousOn
    (D :
      CoverIndexedBoundaryTargetSupportContinuityData
        (C := C) P ω targetChart targetLower targetUpper)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContinuousOn
      (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i))
      (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper (Sum.inr i)) :=
  P.coverIndexBoundaryTargetPieceIntegrand_continuousOn_of_inChart_continuousOn
    (ω := ω) targetChart targetLower targetUpper
    D.targetLower_zero D.targetLower_le_upper
    D.targetInChart_continuousOn i

/-- Topological-support field for genuine boundary indices. -/
theorem piece_tsupport_subset
    (D :
      CoverIndexedBoundaryTargetSupportContinuityData
        (C := C) P ω targetChart targetLower targetUpper)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i)) ⊆
      P.coverIndexBoundaryTargetPieceSet targetLower targetUpper (Sum.inr i) :=
  P.coverIndexBoundaryTargetPieceIntegrand_tsupport_subset_of_inChart_tsupport_subset_Icc
    (ω := ω) targetChart targetLower targetUpper
    D.targetInChart_tsupport_subset i

/-- Compactness field for all cover indices. -/
theorem piece_isCompact_all
    (D :
      CoverIndexedBoundaryTargetSupportContinuityData
        (C := C) P ω targetChart targetLower targetUpper)
    (j : C.CoverIndex) :
    IsCompact (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper j) :=
  P.coverIndexBoundaryTargetPieceSet_isCompact targetLower targetUpper j

/-- Continuity field for all cover indices. -/
theorem piece_continuousOn_all
    (D :
      CoverIndexedBoundaryTargetSupportContinuityData
        (C := C) P ω targetChart targetLower targetUpper)
    (j : C.CoverIndex) :
    ContinuousOn
      (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j)
      (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper j) :=
  P.coverIndexBoundaryTargetPieceIntegrand_continuousOn_all
    (ω := ω) targetChart targetLower targetUpper
    D.targetLower_zero D.targetLower_le_upper
    D.targetInChart_continuousOn j

/-- Topological-support field for all cover indices. -/
theorem piece_tsupport_subset_all
    (D :
      CoverIndexedBoundaryTargetSupportContinuityData
        (C := C) P ω targetChart targetLower targetUpper)
    (j : C.CoverIndex) :
    tsupport (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j) ⊆
      P.coverIndexBoundaryTargetPieceSet targetLower targetUpper j :=
  P.coverIndexBoundaryTargetPieceIntegrand_tsupport_subset_all
    (ω := ω) targetChart targetLower targetUpper
    D.targetInChart_tsupport_subset j

end CoverIndexedBoundaryTargetSupportContinuityData

namespace CoverIndexedResolvedBoundaryFields

variable (P : SupportControlledSelectedPartition C)

/-- Target-COV boundary resolved fields with compactness, continuity, and
support generated by `CoverIndexedBoundaryTargetSupportContinuityData`. -/
def ofTargetCOVPieceSum_supportContinuity
    [IsManifold I 1 M]
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (supportContinuity :
      CoverIndexedBoundaryTargetSupportContinuityData
        (C := C) P ω targetChart targetLower targetUpper)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, boundaryIntegrand y ∂(volume : Measure (Fin n → Real)))
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (hcov :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartOrientedChangeOfVariables I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (targetLower i) (targetUpper i))
    (boundaryIntegrand_ae_eq_pieceSum :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        fun y => ∑ j : C.CoverIndex,
          P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y) :
    CoverIndexedResolvedBoundaryFields
      (C := C) (ω := ω)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) P :=
  CoverIndexedResolvedBoundaryFields.ofTargetCOVPieceSum
    (C := C) (ω := ω) P targetChart targetLower targetUpper
    boundaryIntegrand globalBoundaryIntegral globalBoundaryIntegral_eq_integral
    supportContinuity.piece_isCompact
    supportContinuity.piece_continuousOn
    supportContinuity.piece_tsupport_subset
    sourceSelfSelectedBox sourceTargetSelectedBox hcov
    boundaryIntegrand_ae_eq_pieceSum

/-- Oriented-atlas target boundary resolved fields with automatic compactness,
continuity, and support fields. -/
def ofTargetOrientedAtlasPieceSum_supportContinuity
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (selectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (imageData :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBoxImageData I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (targetLower i) (targetUpper i))
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      targetChart i ∈ A.charts)
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (supportContinuity :
      CoverIndexedBoundaryTargetSupportContinuityData
        (C := C) P ω targetChart targetLower targetUpper)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, boundaryIntegrand y ∂(volume : Measure (Fin n → Real)))
    (boundaryIntegrand_ae_eq_pieceSum :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        fun y => ∑ j : C.CoverIndex,
          P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y) :
    CoverIndexedResolvedBoundaryFields
      (C := C) (ω := ω)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) P :=
  CoverIndexedResolvedBoundaryFields.ofTargetOrientedAtlasPieceSum
    (C := C) (ω := ω) P A targetChart targetLower targetUpper
    selectedBox imageData hsource htarget sourceSelfSelectedBox
    boundaryIntegrand globalBoundaryIntegral globalBoundaryIntegral_eq_integral
    supportContinuity.piece_isCompact
    supportContinuity.piece_continuousOn
    supportContinuity.piece_tsupport_subset
    boundaryIntegrand_ae_eq_pieceSum

/-- Oriented-manifold target boundary resolved fields with automatic compactness,
continuity, and support fields. -/
def ofTargetOrientedManifoldPieceSum_supportContinuity
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (selectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (imageData :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBoxImageData I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (targetLower i) (targetUpper i))
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (supportContinuity :
      CoverIndexedBoundaryTargetSupportContinuityData
        (C := C) P ω targetChart targetLower targetUpper)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, boundaryIntegrand y ∂(volume : Measure (Fin n → Real)))
    (boundaryIntegrand_ae_eq_pieceSum :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        fun y => ∑ j : C.CoverIndex,
          P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y) :
    CoverIndexedResolvedBoundaryFields
      (C := C) (ω := ω)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) P :=
  CoverIndexedResolvedBoundaryFields.ofTargetOrientedManifoldPieceSum
    (C := C) (ω := ω) P targetChart targetLower targetUpper
    selectedBox imageData sourceSelfSelectedBox
    boundaryIntegrand globalBoundaryIntegral globalBoundaryIntegral_eq_integral
    supportContinuity.piece_isCompact
    supportContinuity.piece_continuousOn
    supportContinuity.piece_tsupport_subset
    boundaryIntegrand_ae_eq_pieceSum

end CoverIndexedResolvedBoundaryFields

end CoverIndexedBoundarySupportContinuity

end Stokes

end
