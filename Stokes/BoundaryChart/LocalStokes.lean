import Stokes.BoundaryChart.ChangeOfVariables

/-!
# Boundary chart local Stokes theorem

This file was split out of Stokes.HalfSpace as part of the M6.0
module-structure pass.  The theorem statements and proofs are intended to
remain identical to the monolithic version.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- The bulk integral for a transition-pulled chart representative. -/
def halfSpaceLocalTransitionBulkIntegral {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Real :=
  halfSpaceLocalBulkIntegral (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b

/-- The artificial-face remainder for a transition-pulled chart representative. -/
def halfSpaceLocalTransitionBoundaryRemainder {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Real :=
  halfSpaceLocalBoundaryRemainder (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b

/-- Face coefficient of a transition-pulled chart representative. -/
def halfSpaceTransitionFaceCoeff {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) (i : Fin (n + 1)) :
    (Fin (n + 1) → Real) → Real :=
  boxFormFaceCoeff (ManifoldForm.transitionPullbackInChart I x0 x1 ω) i

/-- Compact-support-in-a-selected-box predicate for a transition-pulled representative. -/
def halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Prop :=
  ∀ i : Fin (n + 1),
    tsupport (halfSpaceTransitionFaceCoeff I x0 x1 ω i) ⊆ halfSpaceSupportBox a b

/--
The transition-pullback chart representative satisfies the coordinate
selected-box predicate as soon as the representative itself is supported in the
selected half-space box.
-/
theorem boxFaceCoeffTSupportInHalfSpaceBox_transitionPullback_of_tsupport_subset
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hsupp : tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      halfSpaceSupportBox a b) :
    boxFaceCoeffTSupportInHalfSpaceBox
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b :=
  boxFaceCoeffTSupportInHalfSpaceBox_of_tsupport_subset
    (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b hsupp

/--
Transition-pullback version of
`boxFaceCoeffTSupportInHalfSpaceBox_of_tsupport_subset`, phrased using the
manifold-boundary face coefficient predicate.
-/
theorem halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox_of_tsupport_subset
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hsupp : tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      halfSpaceSupportBox a b) :
    halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox I x0 x1 ω a b := by
  simpa [halfSpaceTransitionFaceCoeff] using
    (boxFaceCoeffTSupportInHalfSpaceBox_transitionPullback_of_tsupport_subset
      I x0 x1 ω a b hsupp)

/--
Compact chart support for a transition-pullback representative gives a selected
half-space box for all transition face coefficients.
-/
theorem exists_halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox_of_isCompact
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (hK : IsCompact (tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω)))
    (hhalf : tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      upperHalfSpace n) :
    ∃ a b : Fin (n + 1) → Real, a 0 = 0 ∧ a ≤ b ∧
      halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox I x0 x1 ω a b := by
  rcases exists_halfSpaceSupportBox_of_isCompact hK hhalf with
    ⟨a, b, ha0, hle, hsupp⟩
  exact ⟨a, b, ha0, hle,
    halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox_of_tsupport_subset
      I x0 x1 ω a b hsupp⟩

/--
Smoothness of the transition-pullback representative on the model half-space
boundary, using the concrete chart-transition smoothness API from
`ManifoldForm`.
-/
theorem contDiffOn_transitionPullbackInChart_upperHalfSpaceBoundary {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H} [IsManifold I ⊤ M]
    {ω : ManifoldForm I M n} (hω : ManifoldForm.ChartwiseSmooth I ω)
    (x0 x1 : M)
    (htarget : upperHalfSpaceBoundary n ⊆ (extChartAt I x0).target)
    (hoverlap : upperHalfSpaceBoundary n ⊆ ManifoldForm.chartOverlap I x0 x1) :
    ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω)
      (upperHalfSpaceBoundary n) :=
  ManifoldForm.ChartwiseSmooth.contDiffOn_transitionPullbackInChart_of_chartAPI
    (I := I) hω x0 x1 htarget hoverlap

/--
Chartwise smoothness transported to a selected boundary chart box.
-/
theorem contDiffOn_transitionPullbackInChart_halfSpaceBox {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H} [IsManifold I ⊤ M]
    {ω : ManifoldForm I M n} (hω : ManifoldForm.ChartwiseSmooth I ω)
    (x0 x1 : M) {a b : Fin (n + 1) → Real}
    (htarget : Set.Icc a b ⊆ (extChartAt I x0).target)
    (hoverlap : Set.Icc a b ⊆ ManifoldForm.chartOverlap I x0 x1) :
    ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω)
      (Set.Icc a b) :=
  ManifoldForm.ChartwiseSmooth.contDiffOn_transitionPullbackInChart_of_chartAPI
    (I := I) hω x0 x1 htarget hoverlap

/--
The lower `0`-face term for a transition-pulled chart representative is the
half-space boundary-sign integral of the same transition-pulled form.
-/
theorem boxLowerZeroCoordFaceTerm_transitionPullback_eq_halfSpaceBoundaryTransitionFormTerm
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) (ha0 : a 0 = 0) :
    boxLowerZeroCoordFaceTerm
        (CubeStokes.toCoordNForm (ManifoldForm.transitionPullbackInChart I x0 x1 ω)) a b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b := by
  rw [boxLowerZeroCoordFaceTerm_toCoordNForm_eq_halfSpaceBoundaryFormTerm _ _ _ ha0]
  rfl

/--
Local half-space Stokes for a transition-pulled chart representative, with the
non-boundary box faces kept as an explicit remainder.
-/
theorem halfSpaceLocalStokes_transitionPullback_with_remainder
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    (hω : ContDiff Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω)) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      halfSpaceBoundarySign n *
          halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b +
        halfSpaceLocalTransitionBoundaryRemainder I x0 x1 ω a b := by
  exact halfSpaceLocalStokes_with_remainder
    (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b hle ha0 hω

/--
Transition-pullback half-space Stokes after artificial box faces vanish.
-/
theorem halfSpaceLocalStokes_transitionPullback_of_remainder_eq_zero
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    (hω : ContDiff Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω))
    (hrem : halfSpaceLocalTransitionBoundaryRemainder I x0 x1 ω a b = 0) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b := by
  rw [halfSpaceLocalStokes_transitionPullback_with_remainder
    I x0 x1 ω a b hle ha0 hω, hrem, add_zero]

theorem halfSpaceLocalTransitionBoundaryRemainder_eq_zero_of_face_cancellation
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b : Fin (n + 1) → Real)
    (h0 :
      boxUpperFormFaceIntegral (ManifoldForm.transitionPullbackInChart I x0 x1 ω)
        (0 : Fin (n + 1)) a b = 0)
    (hsucc : ∀ i : Fin n,
      upperFaceSign i.succ *
          boxUpperFormFaceIntegral (ManifoldForm.transitionPullbackInChart I x0 x1 ω)
            i.succ a b +
        lowerFaceSign i.succ *
          boxLowerFormFaceIntegral (ManifoldForm.transitionPullbackInChart I x0 x1 ω)
            i.succ a b = 0) :
    halfSpaceLocalTransitionBoundaryRemainder I x0 x1 ω a b = 0 := by
  simpa [halfSpaceLocalTransitionBoundaryRemainder] using
    halfSpaceLocalBoundaryRemainder_eq_zero_of_face_cancellation
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b h0 hsucc

theorem halfSpaceLocalTransitionBoundaryRemainder_eq_zero_of_support_disjoint
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b : Fin (n + 1) → Real)
    (h0 : Disjoint (boxUpperFaceSet (0 : Fin (n + 1)) a b)
      (Function.support (halfSpaceTransitionFaceCoeff I x0 x1 ω (0 : Fin (n + 1)))))
    (hsucc : ∀ i : Fin n,
      Disjoint (boxUpperFaceSet i.succ a b)
          (Function.support (halfSpaceTransitionFaceCoeff I x0 x1 ω i.succ)) ∧
      Disjoint (boxLowerFaceSet i.succ a b)
          (Function.support (halfSpaceTransitionFaceCoeff I x0 x1 ω i.succ))) :
    halfSpaceLocalTransitionBoundaryRemainder I x0 x1 ω a b = 0 := by
  simpa [halfSpaceLocalTransitionBoundaryRemainder, halfSpaceTransitionFaceCoeff] using
    halfSpaceLocalBoundaryRemainder_eq_zero_of_support_disjoint
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b h0 hsucc

theorem halfSpaceLocalTransitionBoundaryRemainder_eq_zero_of_tsupport_disjoint
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b : Fin (n + 1) → Real)
    (h0 : Disjoint (boxUpperFaceSet (0 : Fin (n + 1)) a b)
      (tsupport (halfSpaceTransitionFaceCoeff I x0 x1 ω (0 : Fin (n + 1)))))
    (hsucc : ∀ i : Fin n,
      Disjoint (boxUpperFaceSet i.succ a b)
          (tsupport (halfSpaceTransitionFaceCoeff I x0 x1 ω i.succ)) ∧
      Disjoint (boxLowerFaceSet i.succ a b)
          (tsupport (halfSpaceTransitionFaceCoeff I x0 x1 ω i.succ))) :
    halfSpaceLocalTransitionBoundaryRemainder I x0 x1 ω a b = 0 := by
  simpa [halfSpaceLocalTransitionBoundaryRemainder, halfSpaceTransitionFaceCoeff] using
    halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_disjoint
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b h0 hsucc

theorem halfSpaceLocalTransitionBoundaryRemainder_eq_zero_of_tsupport_subset_halfSpaceSupportBox
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) (a b : Fin (n + 1) → Real)
    (hsupp : halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox I x0 x1 ω a b) :
    halfSpaceLocalTransitionBoundaryRemainder I x0 x1 ω a b = 0 := by
  have hsupp' :
      boxFaceCoeffTSupportInHalfSpaceBox
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b := by
    intro i y hy
    exact hsupp i hy
  simpa [halfSpaceLocalTransitionBoundaryRemainder] using
    halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_subset_halfSpaceSupportBox
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b hsupp'

theorem halfSpaceLocalStokes_transitionPullback_of_face_cancellation
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    (hω : ContDiff Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω))
    (h0 :
      boxUpperFormFaceIntegral (ManifoldForm.transitionPullbackInChart I x0 x1 ω)
        (0 : Fin (n + 1)) a b = 0)
    (hsucc : ∀ i : Fin n,
      upperFaceSign i.succ *
          boxUpperFormFaceIntegral (ManifoldForm.transitionPullbackInChart I x0 x1 ω)
            i.succ a b +
        lowerFaceSign i.succ *
          boxLowerFormFaceIntegral (ManifoldForm.transitionPullbackInChart I x0 x1 ω)
            i.succ a b = 0) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b :=
  halfSpaceLocalStokes_transitionPullback_of_remainder_eq_zero
    I x0 x1 ω a b hle ha0 hω
    (halfSpaceLocalTransitionBoundaryRemainder_eq_zero_of_face_cancellation
      I x0 x1 ω a b h0 hsucc)

theorem halfSpaceLocalStokes_transitionPullback_of_support_disjoint
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    (hω : ContDiff Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω))
    (h0 : Disjoint (boxUpperFaceSet (0 : Fin (n + 1)) a b)
      (Function.support (halfSpaceTransitionFaceCoeff I x0 x1 ω (0 : Fin (n + 1)))))
    (hsucc : ∀ i : Fin n,
      Disjoint (boxUpperFaceSet i.succ a b)
          (Function.support (halfSpaceTransitionFaceCoeff I x0 x1 ω i.succ)) ∧
      Disjoint (boxLowerFaceSet i.succ a b)
          (Function.support (halfSpaceTransitionFaceCoeff I x0 x1 ω i.succ))) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b :=
  halfSpaceLocalStokes_transitionPullback_of_remainder_eq_zero
    I x0 x1 ω a b hle ha0 hω
    (halfSpaceLocalTransitionBoundaryRemainder_eq_zero_of_support_disjoint
      I x0 x1 ω a b h0 hsucc)

theorem halfSpaceLocalStokes_transitionPullback_of_tsupport_disjoint
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    (hω : ContDiff Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω))
    (h0 : Disjoint (boxUpperFaceSet (0 : Fin (n + 1)) a b)
      (tsupport (halfSpaceTransitionFaceCoeff I x0 x1 ω (0 : Fin (n + 1)))))
    (hsucc : ∀ i : Fin n,
      Disjoint (boxUpperFaceSet i.succ a b)
          (tsupport (halfSpaceTransitionFaceCoeff I x0 x1 ω i.succ)) ∧
      Disjoint (boxLowerFaceSet i.succ a b)
          (tsupport (halfSpaceTransitionFaceCoeff I x0 x1 ω i.succ))) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b :=
  halfSpaceLocalStokes_transitionPullback_of_remainder_eq_zero
    I x0 x1 ω a b hle ha0 hω
    (halfSpaceLocalTransitionBoundaryRemainder_eq_zero_of_tsupport_disjoint
      I x0 x1 ω a b h0 hsucc)

/-- Clean compact-support local half-space Stokes for a transition-pulled representative. -/
theorem halfSpaceLocalStokes_transitionPullback_compactSupport
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    (hω : ContDiff Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω))
    (hsupp : halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox I x0 x1 ω a b) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b :=
  halfSpaceLocalStokes_transitionPullback_of_remainder_eq_zero
    I x0 x1 ω a b hle ha0 hω
    (halfSpaceLocalTransitionBoundaryRemainder_eq_zero_of_tsupport_subset_halfSpaceSupportBox
      I x0 x1 ω a b hsupp)

/--
Clean compact-support local half-space Stokes for a transition-pulled
representative, assuming only smoothness on an open neighborhood of the chart
box.
-/
theorem halfSpaceLocalStokes_transitionPullback_compactSupport_of_contDiffOn_isOpen
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hω : ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U)
    (hsupp : halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox I x0 x1 ω a b) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b := by
  have hsupp' :
      boxFaceCoeffTSupportInHalfSpaceBox
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b := by
    intro i y hy
    exact hsupp i hy
  simpa [halfSpaceLocalTransitionBulkIntegral, halfSpaceBoundaryTransitionFormIntegral] using
    halfSpaceLocalStokes_compactSupport_of_contDiffOn_isOpen
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω)
      a b hle ha0 hU hbox hω hsupp'

/-- Alias with the word order used in the roadmap. -/
theorem localHalfSpaceStokes_transitionPullback_compactSupport
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    (hω : ContDiff Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω))
    (hsupp : halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox I x0 x1 ω a b) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b :=
  halfSpaceLocalStokes_transitionPullback_compactSupport
    I x0 x1 ω a b hle ha0 hω hsupp

/-- Alias for the local-smoothness transition-pullback theorem. -/
theorem localHalfSpaceStokes_transitionPullback_compactSupport_of_contDiffOn_isOpen
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hω : ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U)
    (hsupp : halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox I x0 x1 ω a b) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b :=
  halfSpaceLocalStokes_transitionPullback_compactSupport_of_contDiffOn_isOpen
    I x0 x1 ω a b hle ha0 hU hbox hω hsupp

/--
Boundary-chart package for the current local half-space Stokes layer.

The `ChartwiseSmooth` hypothesis gives smoothness of the transition-pullback
representative on an open chart-box neighborhood `U`, and the selected-box
support hypothesis removes the artificial faces.
-/
theorem boundaryChartLocalStokes_transitionPullback_compactSupport
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M]
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U)
    (hchart : ManifoldForm.ChartwiseSmooth I ω)
    (htarget : U ⊆ (extChartAt I x0).target)
    (hoverlap : U ⊆ ManifoldForm.chartOverlap I x0 x1)
    (hsupp : tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      halfSpaceSupportBox a b) :
    ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω)
        U ∧
      boxFaceCoeffTSupportInHalfSpaceBox
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b ∧
      halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox I x0 x1 ω a b ∧
      halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
        halfSpaceBoundarySign n *
          halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b := by
  have hlocal :
      ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω)
        U :=
    ManifoldForm.ChartwiseSmooth.contDiffOn_transitionPullbackInChart_of_chartAPI
      (I := I) hchart x0 x1 htarget hoverlap
  have hcoeffSupport :
      boxFaceCoeffTSupportInHalfSpaceBox
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b :=
    boxFaceCoeffTSupportInHalfSpaceBox_transitionPullback_of_tsupport_subset
      I x0 x1 ω a b hsupp
  have hfaces : halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox I x0 x1 ω a b :=
    halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox_of_tsupport_subset
      I x0 x1 ω a b hsupp
  refine ⟨hlocal, hcoeffSupport, hfaces, ?_⟩
  exact halfSpaceLocalStokes_transitionPullback_compactSupport_of_contDiffOn_isOpen
    I x0 x1 ω a b hle ha0 hU hUbox hlocal hfaces

/--
Equality-only projection of
`boundaryChartLocalStokes_transitionPullback_compactSupport`.
-/
theorem boundaryChartLocalStokes_transitionPullback_compactSupport_eq
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M]
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U)
    (hchart : ManifoldForm.ChartwiseSmooth I ω)
    (htarget : U ⊆ (extChartAt I x0).target)
    (hoverlap : U ⊆ ManifoldForm.chartOverlap I x0 x1)
    (hsupp : tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      halfSpaceSupportBox a b) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b :=
  (boundaryChartLocalStokes_transitionPullback_compactSupport
    (I := I) x0 x1 ω a b hle ha0 hU hUbox hchart htarget hoverlap hsupp).2.2.2

/--
Boundary chart local Stokes from a selected box with an ambient smooth extension
neighborhood.  This is the M4.6 equality-level API: the caller no longer passes
the open neighborhood `U` as a theorem argument.
-/
theorem boundaryChartLocalStokes_transitionPullback_of_extendedBox
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hbox : boundaryChartExtendedBox I x0 x1 ω a b) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b := by
  rcases boundaryChartExtendedBox.exists_smooth_nhds hbox with ⟨U, hU, hUbox, hωU⟩
  have hfaces : halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox I x0 x1 ω a b :=
    halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox_of_tsupport_subset
      I x0 x1 ω a b hbox.selectedBox.tsupport_subset
  exact halfSpaceLocalStokes_transitionPullback_compactSupport_of_contDiffOn_isOpen
    I x0 x1 ω a b hbox.selectedBox.le hbox.selectedBox.ha0 hU hUbox hωU hfaces

/--
Orientation-facing form of the boundary-chart local Stokes theorem: the right
hand side is the boundary integral using the outward-normal-first induced
boundary orientation.
-/
theorem boundaryChartLocalStokes_transitionPullback_of_extendedBox_outwardFirst
    {n : Nat} (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hbox : boundaryChartExtendedBox I x0 x1 ω a b) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x0 x1 ω a b := by
  rw [outwardFirstBoundaryChartIntegral,
    ← halfSpaceBoundarySign_eq_outwardFirstBoundaryOrientationSign]
  exact boundaryChartLocalStokes_transitionPullback_of_extendedBox
    I x0 x1 ω a b hbox

/--
Local boundary-chart Stokes with the boundary term transported to a target
boundary chart box using oriented-atlas data and local surjectivity onto the
target box.

The source `extendedBox` is the analytic input for the current local
half-space Stokes theorem; the target-side input is a selected boundary box.
-/
theorem boundaryChartLocalStokes_transitionPullback_of_orientedAtlas_surjOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartExtendedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hsurj : SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d := by
  calc
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
        outwardFirstBoundaryChartIntegral I x0 x1 ω a b := by
      exact boundaryChartLocalStokes_transitionPullback_of_extendedBox_outwardFirst
        I x0 x1 ω a b hboxSource
    _ = outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
      outwardFirstBoundaryChartIntegral_invariant_of_orientedAtlas_surjOn
        A hx0 hx1 x2 ω a b c d
        hboxSource.selectedBox hboxTarget hmaps hsurj

/--
Local boundary-chart Stokes with the boundary term transported using
oriented-atlas data and packaged local boundary-box image data.
-/
theorem boundaryChartLocalStokes_transitionPullback_of_orientedAtlas_imageData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartExtendedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
  boundaryChartLocalStokes_transitionPullback_of_orientedAtlas_surjOn
    A hx0 hx1 x2 ω a b c d hboxSource hboxTarget
    himage.mapsTo himage.surjOn

/--
Local boundary-chart Stokes with the boundary term transported using
oriented-atlas data and packaged local boundary-box bijection data.
-/
theorem boundaryChartLocalStokes_transitionPullback_of_orientedAtlas_bijOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartExtendedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (hbij : BijOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d := by
  calc
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
        outwardFirstBoundaryChartIntegral I x0 x1 ω a b := by
      exact boundaryChartLocalStokes_transitionPullback_of_extendedBox_outwardFirst
        I x0 x1 ω a b hboxSource
    _ = outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
      outwardFirstBoundaryChartIntegral_invariant_of_orientedAtlas_bijOn
        A hx0 hx1 x2 ω a b c d
        hboxSource.selectedBox hboxTarget hbij

/--
Local boundary-chart Stokes with the boundary term transported to a target
oriented boundary chart box using global oriented-manifold data and local
surjectivity onto the target box.

The source `extendedBox` is the analytic input for the current local
half-space Stokes theorem; the orientation/chart-change input is reduced to a
selected target box plus the image-surjectivity data.
-/
theorem boundaryChartLocalStokes_transitionPullback_of_orientedManifold_surjOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartExtendedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hsurj : SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d := by
  calc
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
        outwardFirstBoundaryChartIntegral I x0 x1 ω a b := by
      exact boundaryChartLocalStokes_transitionPullback_of_extendedBox_outwardFirst
        I x0 x1 ω a b hboxSource
    _ = outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
      outwardFirstBoundaryChartIntegral_invariant_of_orientedManifold_surjOn
        x0 x1 x2 ω a b c d hboxSource.selectedBox hboxTarget hmaps hsurj

/--
Local boundary-chart Stokes with the boundary term transported using global
oriented-boundary-charted-manifold data and packaged local boundary-box image
data.
-/
theorem boundaryChartLocalStokes_transitionPullback_of_orientedManifold_imageData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartExtendedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
  boundaryChartLocalStokes_transitionPullback_of_orientedManifold_surjOn
    x0 x1 x2 ω a b c d hboxSource hboxTarget
    himage.mapsTo himage.surjOn

/--
Local boundary-chart Stokes with the boundary term transported to a target
oriented boundary chart box using global oriented-manifold data and packaged
local boundary-box bijection data.
-/
theorem boundaryChartLocalStokes_transitionPullback_of_orientedManifold_bijOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 x2 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartExtendedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (hbij : BijOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      outwardFirstBoundaryChartIntegral I x1 x2 ω c d := by
  calc
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
        outwardFirstBoundaryChartIntegral I x0 x1 ω a b := by
      exact boundaryChartLocalStokes_transitionPullback_of_extendedBox_outwardFirst
        I x0 x1 ω a b hboxSource
    _ = outwardFirstBoundaryChartIntegral I x1 x2 ω c d :=
      outwardFirstBoundaryChartIntegral_invariant_of_orientedManifold_bijOn
        x0 x1 x2 ω a b c d hboxSource.selectedBox hboxTarget hbij

/--
Boundary chart package from chartwise smoothness plus a selected box with an
ambient smooth extension.  The chartwise hypothesis supplies smoothness on the
natural chart domain; the extension witness supplies the ambient smoothness
needed by the current `extDeriv` box theorem.
-/
theorem boundaryChartLocalStokes_transitionPullback_of_extendedBox_package
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M]
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hchart : ManifoldForm.ChartwiseSmooth I ω)
    (hbox : boundaryChartExtendedBox I x0 x1 ω a b) :
    ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω)
        (boundaryChartDomain I x0 x1) ∧
      boxFaceCoeffTSupportInHalfSpaceBox
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b ∧
      halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox I x0 x1 ω a b ∧
      halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
        halfSpaceBoundarySign n *
          halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b := by
  have hlocal :
      ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω)
        (boundaryChartDomain I x0 x1) :=
    ManifoldForm.ChartwiseSmooth.contDiffOn_transitionPullbackInChart_of_chartAPI
      (I := I) hchart x0 x1
      (boundaryChartDomain_subset_target I x0 x1)
      (boundaryChartDomain_subset_overlap I x0 x1)
  have hcoeffSupport :
      boxFaceCoeffTSupportInHalfSpaceBox
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b :=
    boxFaceCoeffTSupportInHalfSpaceBox_transitionPullback_of_tsupport_subset
      I x0 x1 ω a b hbox.selectedBox.tsupport_subset
  have hfaces : halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox I x0 x1 ω a b :=
    halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox_of_tsupport_subset
      I x0 x1 ω a b hbox.selectedBox.tsupport_subset
  refine ⟨hlocal, hcoeffSupport, hfaces, ?_⟩
  exact boundaryChartLocalStokes_transitionPullback_of_extendedBox
    I x0 x1 ω a b hbox

/--
Package version of
`boundaryChartLocalStokes_transitionPullback_of_extendedBox_outwardFirst`.
-/
theorem boundaryChartLocalStokes_transitionPullback_of_extendedBox_outwardFirst_package
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M]
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hchart : ManifoldForm.ChartwiseSmooth I ω)
    (hbox : boundaryChartExtendedBox I x0 x1 ω a b) :
    ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω)
        (boundaryChartDomain I x0 x1) ∧
      boxFaceCoeffTSupportInHalfSpaceBox
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b ∧
      halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox I x0 x1 ω a b ∧
      halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
        outwardFirstBoundaryChartIntegral I x0 x1 ω a b := by
  rcases boundaryChartLocalStokes_transitionPullback_of_extendedBox_package
      x0 x1 ω a b hchart hbox with
    ⟨hlocal, hcoeffSupport, hfaces, hstokes⟩
  refine ⟨hlocal, hcoeffSupport, hfaces, ?_⟩
  rw [outwardFirstBoundaryChartIntegral,
    ← halfSpaceBoundarySign_eq_outwardFirstBoundaryOrientationSign]
  exact hstokes

end ManifoldBoundary

end Stokes

end
