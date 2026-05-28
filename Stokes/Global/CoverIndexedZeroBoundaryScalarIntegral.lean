import Stokes.Global.CoverIndexedCompactSupportCInftyAssembly
import Stokes.Global.CoverIndexedZeroTargetBoxSupport

/-!
# Zero boundary scalar integrals

This file pushes the zero-extension route one step past support transfer.

The existing represented boundary endpoint is phrased with the old target
boundary scalar

`boundaryTargetInChartPieceIntegrand`.

For compact support it is cleaner to use the zero-extended scalar

`boundaryTargetInChartZeroPieceIntegrand`

directly.  On each selected target boundary box the two scalar representatives
agree, because the ambient box lies in the target chart.  Therefore all local
target set integrals produced by boundary chart change of variables can be
rewritten with the zero scalar.  The resulting natural boundary package uses
zero scalar support for its support field and no longer requires the old scalar
support-on-target-face hypothesis.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BasicZeroBoundaryScalarIntegrals

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/-- On a selected target lower face contained in the target chart, the old and
zero-extended boundary scalar representatives agree pointwise. -/
theorem boundaryTargetInChartPieceIntegrand_eq_zeroPieceIntegrand_on_targetPieceSet
    {x : M} {ω : ManifoldForm I M n}
    {c d : Fin (n + 1) → Real}
    (hc0 : c 0 = 0) (hcd : c ≤ d)
    (htargetBox : Icc c d ⊆ (extChartAt I x).target)
    {u : Fin n → Real}
    (hu : u ∈ boundaryTargetInChartPieceSet (n := n) c d) :
    boundaryTargetInChartPieceIntegrand I x ω u =
      boundaryTargetInChartZeroPieceIntegrand I x ω u := by
  have huIcc : boundaryInclusion n u ∈ Icc c d :=
    boundaryInclusion_mem_Icc_of_mem_lowerZeroFaceDomain
      (n := n) (a := c) (b := d) hc0 hcd
      (by simpa [boundaryTargetInChartPieceSet] using hu)
  exact
    (boundaryTargetInChartZeroPieceIntegrand_eq_old_of_boundaryInclusion_mem_target
      (I := I) (x := x) (ω := ω) (u := u)
      (htargetBox huIcc)).symm

/-- The target-face set integral is unchanged if the old boundary scalar is
replaced by its zero-extended version. -/
theorem boundaryTargetInChartPieceIntegrand_setIntegral_eq_zeroPieceIntegrand
    {x : M} {ω : ManifoldForm I M n}
    {c d : Fin (n + 1) → Real}
    (hc0 : c 0 = 0) (hcd : c ≤ d)
    (htargetBox : Icc c d ⊆ (extChartAt I x).target) :
    (∫ u in boundaryTargetInChartPieceSet (n := n) c d,
        boundaryTargetInChartPieceIntegrand I x ω u
          ∂(volume : Measure (Fin n → Real))) =
      ∫ u in boundaryTargetInChartPieceSet (n := n) c d,
        boundaryTargetInChartZeroPieceIntegrand I x ω u
          ∂(volume : Measure (Fin n → Real)) := by
  refine MeasureTheory.setIntegral_congr_fun
    (by simp [boundaryTargetInChartPieceSet, lowerZeroFaceDomain, faceDomain]) ?_
  intro u hu
  exact
    boundaryTargetInChartPieceIntegrand_eq_zeroPieceIntegrand_on_targetPieceSet
      (I := I) (x := x) (ω := ω)
      (c := c) (d := d) hc0 hcd htargetBox hu

/-- Continuity of the zero scalar on a selected target face follows from
continuity of the old scalar there, because the face lies in the target chart. -/
theorem boundaryTargetInChartZeroPieceIntegrand_continuousOn_of_old
    {x : M} {ω : ManifoldForm I M n}
    {c d : Fin (n + 1) → Real}
    (hc0 : c 0 = 0) (hcd : c ≤ d)
    (htargetBox : Icc c d ⊆ (extChartAt I x).target)
    (hold :
      ContinuousOn (boundaryTargetInChartPieceIntegrand I x ω)
        (boundaryTargetInChartPieceSet (n := n) c d)) :
    ContinuousOn (boundaryTargetInChartZeroPieceIntegrand I x ω)
      (boundaryTargetInChartPieceSet (n := n) c d) := by
  refine hold.congr ?_
  intro u hu
  exact
    boundaryTargetInChartPieceIntegrand_eq_zeroPieceIntegrand_on_targetPieceSet
      (I := I) (x := x) (ω := ω)
      (c := c) (d := d) hc0 hcd htargetBox hu |>.symm

/-- Zero scalar support on the selected boundary image gives topological
support inside the selected target lower face. -/
theorem boundaryTargetInChartZeroPieceIntegrand_tsupport_subset_targetPieceSet_of_support_subset
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d)
    (hzeroSupport :
      Function.support (boundaryTargetInChartZeroPieceIntegrand I x1 ω) ⊆
        boundaryChartTransitionBoundaryImage I x0 x1 a b) :
    tsupport (boundaryTargetInChartZeroPieceIntegrand I x1 ω) ⊆
      boundaryTargetInChartPieceSet (n := n) c d := by
  have hboundary :
      tsupport (boundaryTargetInChartZeroPieceIntegrand I x1 ω) ⊆
        boundaryChartTransitionBoundaryImage I x0 x1 a b :=
    boundaryTargetInChartZeroPieceIntegrand_tsupport_subset_boundaryImage_of_support_subset
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) (c := c) (d := d)
      himage hzeroSupport
  have hsubset :
      boundaryChartTransitionBoundaryImage I x0 x1 a b ⊆
        boundaryTargetInChartPieceSet (n := n) c d := by
    rw [boundaryChartTransitionBoundaryImage_eq_lowerZeroFaceDomain_of_imageData
      (I := I) himage]
    simp [boundaryTargetInChartPieceSet]
  exact hboundary.trans hsubset

end BasicZeroBoundaryScalarIntegrals

section CoverIndexedZeroBoundaryScalarIntegrals

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}

namespace SupportControlledSelectedPartition

variable (P : SupportControlledSelectedPartition C)

/-- Target-side boundary scalar pieces built from zero-extended target chart
representatives.  Interior cover indices still contribute the empty/zero
piece. -/
def coverIndexBoundaryTargetZeroPieceIntegrand
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (ω : ManifoldForm I M n) :
    C.CoverIndex → (Fin n → Real) → Real
  | Sum.inl _ => fun _ => 0
  | Sum.inr i => fun u =>
      boundaryTargetInChartZeroPieceIntegrand I (targetChart i)
        (P.coverIndexLocalizedForm ω (Sum.inr i)) u

/-- Canonical zero-extended target-side boundary scalar: the finite sum of
zero-extended target boundary pieces. -/
def coverIndexBoundaryTargetZeroPieceSum
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (ω : ManifoldForm I M n) :
    (Fin n → Real) → Real :=
  fun y =>
    ∑ j : C.CoverIndex,
      P.coverIndexBoundaryTargetZeroPieceIntegrand targetChart ω j y

/-- The zero target-piece sum is definitionally a.e. its finite piece sum. -/
theorem coverIndexBoundaryTargetZeroPieceSum_ae_eq_pieceSum
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (ω : ManifoldForm I M n) :
    P.coverIndexBoundaryTargetZeroPieceSum targetChart ω
      =ᵐ[(volume : Measure (Fin n → Real))]
        fun y =>
          ∑ j : C.CoverIndex,
            P.coverIndexBoundaryTargetZeroPieceIntegrand targetChart ω j y := by
  exact Filter.EventuallyEq.rfl

/-- Per-cover-index target set integral equality between old and zero target
boundary scalar pieces. -/
theorem coverIndexBoundaryTargetPiece_setIntegral_eq_zeroPiece_setIntegral
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (targetLower_zero :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i 0 = 0)
    (targetLower_le_upper :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i ≤ targetUpper i)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetLower i) (targetUpper i) ⊆
          (extChartAt I (targetChart i)).target)
    (j : C.CoverIndex) :
    (∫ y in P.coverIndexBoundaryTargetPieceSet targetLower targetUpper j,
        P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y
          ∂(volume : Measure (Fin n → Real))) =
      ∫ y in P.coverIndexBoundaryTargetPieceSet targetLower targetUpper j,
        P.coverIndexBoundaryTargetZeroPieceIntegrand targetChart ω j y
          ∂(volume : Measure (Fin n → Real)) := by
  rcases j with i | i
  · simp [coverIndexBoundaryTargetPieceSet, coverIndexBoundaryTargetPieceIntegrand,
      coverIndexBoundaryTargetZeroPieceIntegrand]
  · simpa [coverIndexBoundaryTargetPieceSet, coverIndexBoundaryTargetPieceIntegrand,
      coverIndexBoundaryTargetZeroPieceIntegrand] using
      boundaryTargetInChartPieceIntegrand_setIntegral_eq_zeroPieceIntegrand
        (I := I) (x := targetChart i)
        (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
        (c := targetLower i) (d := targetUpper i)
        (targetLower_zero i) (targetLower_le_upper i)
        (targetBox_subset_target i)

/-- Local boundary terms can be represented as target-box set integrals of the
zero-extended target scalar pieces. -/
theorem coverIndexLocalBoundaryTerm_eq_targetZeroSetIntegral_of_orientedCOV
    [IsManifold I 1 M]
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (targetLower_zero :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i 0 = 0)
    (targetLower_le_upper :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, targetLower i ≤ targetUpper i)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetLower i) (targetUpper i) ⊆
          (extChartAt I (targetChart i)).target)
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
    (j : C.CoverIndex) :
    P.coverIndexLocalBoundaryTerm ω j =
      ∫ y in P.coverIndexBoundaryTargetPieceSet targetLower targetUpper j,
        P.coverIndexBoundaryTargetZeroPieceIntegrand targetChart ω j y
          ∂(volume : Measure (Fin n → Real)) := by
  calc
    P.coverIndexLocalBoundaryTerm ω j =
        ∫ y in P.coverIndexBoundaryTargetPieceSet targetLower targetUpper j,
          P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y
            ∂(volume : Measure (Fin n → Real)) := by
      exact
        P.coverIndexLocalBoundaryTerm_eq_targetSetIntegral_of_orientedCOV
          (ω := ω) targetChart targetLower targetUpper
          sourceSelfSelectedBox sourceTargetSelectedBox hcov j
    _ =
        ∫ y in P.coverIndexBoundaryTargetPieceSet targetLower targetUpper j,
          P.coverIndexBoundaryTargetZeroPieceIntegrand targetChart ω j y
            ∂(volume : Measure (Fin n → Real)) := by
      exact
        P.coverIndexBoundaryTargetPiece_setIntegral_eq_zeroPiece_setIntegral
          (ω := ω) targetChart targetLower targetUpper
          targetLower_zero targetLower_le_upper targetBox_subset_target j

end SupportControlledSelectedPartition

namespace CoverIndexedBoundaryTargetBoxData

variable {P : SupportControlledSelectedPartition C}
variable
  (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω)

/-- Zero target boundary pieces are continuous on selected target faces. -/
theorem boundaryZeroPiece_continuousOn_of_localizedChartwiseSmooth
    (localizedChartwiseSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ManifoldForm.ChartwiseSmooth I
          (P.coverIndexLocalizedForm ω (Sum.inr i)))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.targetLower i) (D.targetUpper i) ⊆
          (extChartAt I (D.targetChart i)).target)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ContinuousOn
      (P.coverIndexBoundaryTargetZeroPieceIntegrand D.targetChart ω (Sum.inr i))
      (P.coverIndexBoundaryTargetPieceSet D.targetLower D.targetUpper
        (Sum.inr i)) := by
  have hold :
      ContinuousOn
        (P.coverIndexBoundaryTargetPieceIntegrand D.targetChart ω (Sum.inr i))
        (P.coverIndexBoundaryTargetPieceSet D.targetLower D.targetUpper
          (Sum.inr i)) :=
    D.boundaryPiece_continuousOn_of_localizedChartwiseSmooth
      localizedChartwiseSmooth targetBox_subset_target i
  simpa [SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceSet,
    SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceIntegrand,
    SupportControlledSelectedPartition.coverIndexBoundaryTargetZeroPieceIntegrand] using
    boundaryTargetInChartZeroPieceIntegrand_continuousOn_of_old
      (I := I) (x := D.targetChart i)
      (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
      (c := D.targetLower i) (d := D.targetUpper i)
      (D.targetLower_zero i) (D.targetLower_le_targetUpper i)
      (targetBox_subset_target i)
      (by
        simpa [SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceSet,
          SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceIntegrand] using hold)

/-- Zero scalar image support gives the target-piece support field needed by a
zero-scalar natural boundary package. -/
theorem boundaryZeroPiece_tsupport_subset_of_zeroScalarSupport
    (zeroScalarSupport : D.BoundaryZeroScalarSupportSubsetImageField)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (P.coverIndexBoundaryTargetZeroPieceIntegrand D.targetChart ω (Sum.inr i)) ⊆
      P.coverIndexBoundaryTargetPieceSet D.targetLower D.targetUpper
        (Sum.inr i) := by
  simpa [SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceSet,
    SupportControlledSelectedPartition.coverIndexBoundaryTargetZeroPieceIntegrand] using
    boundaryTargetInChartZeroPieceIntegrand_tsupport_subset_targetPieceSet_of_support_subset
      (I := I)
      (x0 := C.boundaryChart i.1) (x1 := D.targetChart i)
      (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (c := D.targetLower i) (d := D.targetUpper i)
      (D.boundaryChartSelectedBoxImageData i)
      (zeroScalarSupport i)

/-- Natural boundary data whose target-side pieces are the zero-extended
boundary scalar representatives. -/
def toZeroTargetBoundaryNaturalDataOfOrientedManifoldInfty
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (localizedChartwiseSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ManifoldForm.ChartwiseSmooth I
          (P.coverIndexLocalizedForm ω (Sum.inr i)))
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.targetLower i) (D.targetUpper i) ⊆
          (extChartAt I (D.targetChart i)).target)
    (zeroScalarSupport : D.BoundaryZeroScalarSupportSubsetImageField)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum D.targetChart ω y
          ∂(volume : Measure (Fin n → Real))) :
    CoverIndexedNaturalBoundaryData
      (I := I) (K := K) (ω := ω)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) C P where
  integrand := P.coverIndexBoundaryTargetZeroPieceSum D.targetChart ω
  pieceSet :=
    P.coverIndexBoundaryTargetPieceSet D.targetLower D.targetUpper
  pieceIntegrand :=
    P.coverIndexBoundaryTargetZeroPieceIntegrand D.targetChart ω
  globalIntegral := globalBoundaryIntegral
  globalIntegral_eq_integral := globalBoundaryIntegral_eq_integral
  piece_isCompact := by
    intro j
    rcases j with i | i
    · simp [SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceSet]
    · exact
        P.coverIndexBoundaryTargetPieceSet_isCompact
          D.targetLower D.targetUpper (Sum.inr i)
  piece_continuousOn := by
    intro j
    rcases j with i | i
    · simp [SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceSet,
        SupportControlledSelectedPartition.coverIndexBoundaryTargetZeroPieceIntegrand]
    · exact
        D.boundaryZeroPiece_continuousOn_of_localizedChartwiseSmooth
          localizedChartwiseSmooth targetBox_subset_target i
  piece_tsupport_subset := by
    intro j
    rcases j with i | i
    · simp [SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceSet,
        SupportControlledSelectedPartition.coverIndexBoundaryTargetZeroPieceIntegrand]
    · exact
        D.boundaryZeroPiece_tsupport_subset_of_zeroScalarSupport
          zeroScalarSupport i
  localBoundary_eq_setIntegral := by
    let O :=
      P.coverIndexBoundaryChartOrientationInput
        (ω := ω) D.targetChart D.targetLower D.targetUpper
        (fun i => D.sourceTargetSelectedBox i)
        (fun i => (D.targetSelection i).imageData)
    exact
      P.coverIndexLocalBoundaryTerm_eq_targetZeroSetIntegral_of_orientedCOV
        (ω := ω) D.targetChart D.targetLower D.targetUpper
        D.targetLower_zero D.targetLower_le_targetUpper
        targetBox_subset_target
        sourceSelfSelectedBox
        (fun i => D.sourceTargetSelectedBox i)
        (fun i => O.orientedChangeOfVariablesOfOrientedManifold i)
  integrand_ae_eq_pieceSum :=
    P.coverIndexBoundaryTargetZeroPieceSum_ae_eq_pieceSum D.targetChart ω

end CoverIndexedBoundaryTargetBoxData

/-- Assembly from an assigned-self bulk input and an arbitrary natural
boundary package.  This is the generic form needed by the zero-boundary scalar
route, whose boundary pieces are not the old target pieces. -/
theorem representedStokes_ofAssignedSelfBulkNaturalBoundaryInfty
    {P : SupportControlledSelectedPartition C}
    {μBulk : Measure (Fin (n + 1) → Real)}
    [IsFiniteMeasureOnCompacts μBulk]
    (localBulk_eq_localBoundary :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          P.coverIndexLocalBoundaryTerm ω j)
    (bulk : CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk)
    (boundary :
      CoverIndexedNaturalBoundaryData
        (I := I) (K := K) (ω := ω)
        (αBoundary := Fin n → Real)
        (μBoundary := (volume : Measure (Fin n → Real))) C P) :
    bulk.globalIntegral = boundary.globalIntegral := by
  classical
  calc
    bulk.globalIntegral =
        ∑ j : C.CoverIndex, P.coverIndexLocalBulkTerm ω j := by
      simpa using bulk.toClosedCarrierBulkData.globalIntegral_eq_localBulkSum
    _ = ∑ j : C.CoverIndex, P.coverIndexLocalBoundaryTerm ω j := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      exact localBulk_eq_localBoundary j
    _ = boundary.globalIntegral := by
      simpa using boundary.localBoundarySum_eq_globalIntegral

/-- Compact-support represented Stokes with the boundary side represented by
the zero-extended target scalar finite sum.

This theorem removes the old endpoint hypothesis
`oldScalarSupport_subset_targetFace`: zero scalar support supplies the support
field, while equality of old and zero scalars on target boxes supplies the
local set-integral identities used by boundary chart change of variables. -/
theorem compactSupportRepresentedStokesZeroBoundaryScalarInfty_of_orientedManifold
    {P : SupportControlledSelectedPartition C}
    {μBulk : Measure (Fin (n + 1) → Real)}
    [IsFiniteMeasureOnCompacts μBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M]
    (carrierData :
      CoverIndexedCompactSupportCarrierData
        (I := I) (K := K) C P ω)
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P ω)
    (measure_eq_volume :
      μBulk = (volume : Measure (Fin (n + 1) → Real)))
    (targetBox :
      CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω)
    (targetBox_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
          (extChartAt I (targetBox.targetChart i)).target)
    (zeroScalarSupport :
      targetBox.BoundaryZeroScalarSupportSubsetImageField)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetZeroPieceSum targetBox.targetChart ω y
          ∂(volume : Measure (Fin n → Real))) :
    (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        (μBulk := μBulk) neighborhoodData measure_eq_volume).globalIntegral =
      globalBoundaryIntegral := by
  let boundary :=
    targetBox.toZeroTargetBoundaryNaturalDataOfOrientedManifoldInfty
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      (CoverIndexedCompactSupportCarrierData.sourceSelfSelectedBoxInfty
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        carrierData neighborhoodData)
      neighborhoodData.localizedChartwiseSmooth
      targetBox_subset_target zeroScalarSupport
      globalBoundaryIntegral globalBoundaryIntegral_eq_integral
  exact
    representedStokes_ofAssignedSelfBulkNaturalBoundaryInfty
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      (μBulk := μBulk)
      (CoverIndexedCompactSupportCarrierData.localBulk_eq_localBoundaryInfty
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        carrierData neighborhoodData)
      (carrierData.assignedSelfBulkInputInfty
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        (μBulk := μBulk) neighborhoodData measure_eq_volume)
      boundary

end CoverIndexedZeroBoundaryScalarIntegrals

end Stokes

end
