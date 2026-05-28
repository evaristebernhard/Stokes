import Stokes.HalfSpace.BoundaryIntegral

/-!
# Local Stokes theorem on a half-space box

This file was split out of Stokes.HalfSpace as part of the M6.0
module-structure pass.  The theorem statements and proofs are intended to
remain identical to the monolithic version.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

def standardTopFrame (n : Nat) : Fin (n + 1) → (Fin (n + 1) → Real) :=
  fun j => Pi.single j 1

/-- The box integral of `dω` over a half-space chart box. -/
def halfSpaceLocalBulkIntegral {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) : Real :=
  ∫ x in Icc a b, extDeriv ω x (standardTopFrame n)

/-- The artificial box-face contribution away from the lower `x₀ = 0` face. -/
def halfSpaceLocalBoundaryRemainder {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) : Real :=
  boxRemainingFormFaceTerms ω a b

/--
Box Stokes for a mathlib form that is smooth on an open neighborhood of the
closed box.  This is the local replacement for the global
`CubeStokes.stokes_extDeriv_smooth` hypothesis used by the initial M4 layer.
-/
theorem box_stokes_extDeriv_contDiffOn_isOpen {n : Nat}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hω : ContDiffOn Real ⊤ ω U) :
    (∫ x in Icc a b, extDeriv ω x (standardTopFrame n)) =
      CubeStokes.bdryIntegral (CubeStokes.toCoordNForm ω) a b := by
  have h_ext :
      (∫ x in Icc a b, extDeriv ω x (standardTopFrame n)) =
        CubeStokes.boxIntegral (CubeStokes.extDerivCoord (CubeStokes.toCoordNForm ω)) a b := by
    unfold standardTopFrame CubeStokes.boxIntegral
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun x hx => by
      exact CubeStokes.extDeriv_topCoeff_eq_extDerivCoord ω x
        ((hω.contDiffAt (hU.mem_nhds (hbox hx))).differentiableAt (by simp))
  rw [h_ext]
  refine CubeStokes.stokes_on_box a b hle (CubeStokes.toCoordNForm ω)
    ∅ Set.countable_empty ?_ ?_ ?_
  · intro i
    have hcoeff : ContDiffOn Real ⊤ (CubeStokes.toCoordNForm ω i) U :=
      toCoordNForm_contDiffOn ω hω i
    exact ((continuousOn_const.mul hcoeff.continuousOn).mono hbox : _)
  · intro x hx i
    have hxIcc : x ∈ Icc a b := by
      rcases hx with ⟨hxpi, _⟩
      constructor
      · intro j
        exact (hxpi j (mem_univ j)).1.le
      · intro j
        exact (hxpi j (mem_univ j)).2.le
    have hcoeffAt :
        ContDiffAt Real ⊤ (CubeStokes.toCoordNForm ω i) x :=
      (toCoordNForm_contDiffOn ω hω i).contDiffAt (hU.mem_nhds (hbox hxIcc))
    exact ((hcoeffAt.differentiableAt (by simp)).hasFDerivAt.const_mul
      ((-1 : Real) ^ (i : Nat)))
  · apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply continuousOn_finset_sum
    intro i _
    have hcoeff : ContDiffOn Real ⊤ (CubeStokes.toCoordNForm ω i) U :=
      toCoordNForm_contDiffOn ω hω i
    have hfderiv :
        ContinuousOn (fderiv Real (CubeStokes.toCoordNForm ω i)) U :=
      hcoeff.continuousOn_fderiv_of_isOpen hU (by simp)
    have happly :
        ContinuousOn
          (fun x => fderiv Real (CubeStokes.toCoordNForm ω i) x (Pi.single i 1)) U :=
      (ContinuousLinearMap.apply Real Real (Pi.single i 1)).continuous.comp_continuousOn hfderiv
    exact ((continuousOn_const.mul happly).mono hbox : _)

/--
Box Stokes for a mathlib form that is at least `C¹` on an open neighborhood of
the closed box.  The previous smoothness hypothesis `⊤ : WithTop ℕ∞` is much
stronger than needed; this wrapper is the reusable core for both analytic and
`C^\infty` inputs.
-/
theorem box_stokes_extDeriv_contDiffOn_isOpen_of_one_le {n : Nat}
    {m : WithTop ℕ∞}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hω : ContDiffOn Real m ω U) (hm : (1 : WithTop ℕ∞) ≤ m) :
    (∫ x in Icc a b, extDeriv ω x (standardTopFrame n)) =
      CubeStokes.bdryIntegral (CubeStokes.toCoordNForm ω) a b := by
  have h_ext :
      (∫ x in Icc a b, extDeriv ω x (standardTopFrame n)) =
        CubeStokes.boxIntegral (CubeStokes.extDerivCoord (CubeStokes.toCoordNForm ω)) a b := by
    unfold standardTopFrame CubeStokes.boxIntegral
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun x hx => by
      exact CubeStokes.extDeriv_topCoeff_eq_extDerivCoord ω x
        ((hω.contDiffAt (hU.mem_nhds (hbox hx))).differentiableAt
          (ne_of_gt (lt_of_lt_of_le (by norm_num) hm)))
  rw [h_ext]
  refine CubeStokes.stokes_on_box a b hle (CubeStokes.toCoordNForm ω)
    ∅ Set.countable_empty ?_ ?_ ?_
  · intro i
    have hcoeff : ContDiffOn Real m (CubeStokes.toCoordNForm ω i) U :=
      toCoordNForm_contDiffOn_of_level ω hω i
    exact ((continuousOn_const.mul hcoeff.continuousOn).mono hbox : _)
  · intro x hx i
    have hxIcc : x ∈ Icc a b := by
      rcases hx with ⟨hxpi, _⟩
      constructor
      · intro j
        exact (hxpi j (mem_univ j)).1.le
      · intro j
        exact (hxpi j (mem_univ j)).2.le
    have hcoeffAt :
        ContDiffAt Real m (CubeStokes.toCoordNForm ω i) x :=
      (toCoordNForm_contDiffOn_of_level ω hω i).contDiffAt
        (hU.mem_nhds (hbox hxIcc))
    exact ((hcoeffAt.differentiableAt
      (ne_of_gt (lt_of_lt_of_le (by norm_num) hm))).hasFDerivAt.const_mul
      ((-1 : Real) ^ (i : Nat)))
  · apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply continuousOn_finset_sum
    intro i _
    have hcoeff : ContDiffOn Real m (CubeStokes.toCoordNForm ω i) U :=
      toCoordNForm_contDiffOn_of_level ω hω i
    have hfderiv :
        ContinuousOn (fderiv Real (CubeStokes.toCoordNForm ω i)) U :=
      hcoeff.continuousOn_fderiv_of_isOpen hU hm
    have happly :
        ContinuousOn
          (fun x => fderiv Real (CubeStokes.toCoordNForm ω i) x (Pi.single i 1)) U :=
      (ContinuousLinearMap.apply Real Real (Pi.single i 1)).continuous.comp_continuousOn hfderiv
    exact ((continuousOn_const.mul happly).mono hbox : _)

/-- `C^\infty` version of `box_stokes_extDeriv_contDiffOn_isOpen`. -/
theorem box_stokes_extDeriv_contDiffOn_isOpen_infty {n : Nat}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hω : ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞) ω U) :
    (∫ x in Icc a b, extDeriv ω x (standardTopFrame n)) =
      CubeStokes.bdryIntegral (CubeStokes.toCoordNForm ω) a b :=
  box_stokes_extDeriv_contDiffOn_isOpen_of_one_le
    ω a b hle hU hbox hω (by norm_num)

/--
Local half-space Stokes on a box abutting `{x₀ = 0}`.

The right-hand side separates the true half-space boundary face from the
remaining artificial faces of the auxiliary box.
-/
theorem halfSpaceLocalStokes_with_remainder {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    (hω : ContDiff Real ⊤ ω) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b +
        halfSpaceLocalBoundaryRemainder ω a b := by
  unfold halfSpaceLocalBulkIntegral halfSpaceLocalBoundaryRemainder
  change (∫ x in Icc a b, extDeriv ω x (fun j => Pi.single j 1)) =
    halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b +
      boxRemainingFormFaceTerms ω a b
  rw [CubeStokes.stokes_extDeriv_smooth ω a b hle hω]
  rw [bdryIntegral_eq_lowerZero_add_remaining]
  rw [boxLowerZeroCoordFaceTerm_toCoordNForm_eq_halfSpaceBoundaryFormTerm _ _ _ ha0]
  rw [boxRemainingCoordFaceTerms_toCoordNForm]

/--
Local half-space Stokes with remainder, assuming only smoothness on an open
neighborhood of the chart box.
-/
theorem halfSpaceLocalStokes_with_remainder_of_contDiffOn_isOpen {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hω : ContDiffOn Real ⊤ ω U) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b +
        halfSpaceLocalBoundaryRemainder ω a b := by
  unfold halfSpaceLocalBulkIntegral halfSpaceLocalBoundaryRemainder
  rw [box_stokes_extDeriv_contDiffOn_isOpen ω a b hle hU hbox hω]
  rw [bdryIntegral_eq_lowerZero_add_remaining]
  rw [boxLowerZeroCoordFaceTerm_toCoordNForm_eq_halfSpaceBoundaryFormTerm _ _ _ ha0]
  rw [boxRemainingCoordFaceTerms_toCoordNForm]

/--
`C^\infty` version of
`halfSpaceLocalStokes_with_remainder_of_contDiffOn_isOpen`.
-/
theorem halfSpaceLocalStokes_with_remainder_of_contDiffOn_isOpen_infty {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hω : ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞) ω U) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b +
        halfSpaceLocalBoundaryRemainder ω a b := by
  unfold halfSpaceLocalBulkIntegral halfSpaceLocalBoundaryRemainder
  rw [box_stokes_extDeriv_contDiffOn_isOpen_infty ω a b hle hU hbox hω]
  rw [bdryIntegral_eq_lowerZero_add_remaining]
  rw [boxLowerZeroCoordFaceTerm_toCoordNForm_eq_halfSpaceBoundaryFormTerm _ _ _ ha0]
  rw [boxRemainingCoordFaceTerms_toCoordNForm]

/--
Compact-support/cancellation form of local half-space Stokes: once all
artificial box faces vanish, only the induced half-space boundary term remains.
-/
theorem halfSpaceLocalStokes_of_remainder_eq_zero {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    (hω : ContDiff Real ⊤ ω)
    (hrem : halfSpaceLocalBoundaryRemainder ω a b = 0) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b := by
  rw [halfSpaceLocalStokes_with_remainder ω a b hle ha0 hω, hrem, add_zero]

/--
Local half-space Stokes from local chart-box smoothness and an explicit
vanishing artificial-face remainder.
-/
theorem halfSpaceLocalStokes_of_remainder_eq_zero_of_contDiffOn_isOpen {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hω : ContDiffOn Real ⊤ ω U)
    (hrem : halfSpaceLocalBoundaryRemainder ω a b = 0) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b := by
  rw [halfSpaceLocalStokes_with_remainder_of_contDiffOn_isOpen
    ω a b hle ha0 hU hbox hω, hrem, add_zero]

/--
`C^\infty` version of
`halfSpaceLocalStokes_of_remainder_eq_zero_of_contDiffOn_isOpen`.
-/
theorem halfSpaceLocalStokes_of_remainder_eq_zero_of_contDiffOn_isOpen_infty {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hω : ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞) ω U)
    (hrem : halfSpaceLocalBoundaryRemainder ω a b = 0) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b := by
  rw [halfSpaceLocalStokes_with_remainder_of_contDiffOn_isOpen_infty
    ω a b hle ha0 hU hbox hω, hrem, add_zero]

theorem halfSpaceLocalBoundaryRemainder_eq_zero_of_face_cancellation {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (h0 : boxUpperFormFaceIntegral ω (0 : Fin (n + 1)) a b = 0)
    (hsucc : ∀ i : Fin n,
      upperFaceSign i.succ * boxUpperFormFaceIntegral ω i.succ a b +
        lowerFaceSign i.succ * boxLowerFormFaceIntegral ω i.succ a b = 0) :
    halfSpaceLocalBoundaryRemainder ω a b = 0 := by
  simpa [halfSpaceLocalBoundaryRemainder] using
    boxRemainingFormFaceTerms_eq_zero_of_face_cancellation ω a b h0 hsucc

theorem halfSpaceLocalBoundaryRemainder_eq_zero_of_support_disjoint {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (h0 : Disjoint (boxUpperFaceSet (0 : Fin (n + 1)) a b)
      (Function.support (boxFormFaceCoeff ω (0 : Fin (n + 1)))))
    (hsucc : ∀ i : Fin n,
      Disjoint (boxUpperFaceSet i.succ a b) (Function.support (boxFormFaceCoeff ω i.succ)) ∧
      Disjoint (boxLowerFaceSet i.succ a b) (Function.support (boxFormFaceCoeff ω i.succ))) :
    halfSpaceLocalBoundaryRemainder ω a b = 0 := by
  simpa [halfSpaceLocalBoundaryRemainder] using
    boxRemainingFormFaceTerms_eq_zero_of_support_disjoint ω a b h0 hsucc

/-- The artificial boundary remainder vanishes when the form support misses the
whole artificial boundary of the half-space box. -/
theorem halfSpaceLocalBoundaryRemainder_eq_zero_of_support_disjoint_artificial {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (h : Disjoint (halfSpaceArtificialFaceSet a b) (Function.support ω)) :
    halfSpaceLocalBoundaryRemainder ω a b = 0 := by
  simpa [halfSpaceLocalBoundaryRemainder] using
    boxRemainingFormFaceTerms_eq_zero_of_support_disjoint_artificial ω a b h

theorem halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_disjoint {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (h0 : Disjoint (boxUpperFaceSet (0 : Fin (n + 1)) a b)
      (tsupport (boxFormFaceCoeff ω (0 : Fin (n + 1)))))
    (hsucc : ∀ i : Fin n,
      Disjoint (boxUpperFaceSet i.succ a b) (tsupport (boxFormFaceCoeff ω i.succ)) ∧
      Disjoint (boxLowerFaceSet i.succ a b) (tsupport (boxFormFaceCoeff ω i.succ))) :
    halfSpaceLocalBoundaryRemainder ω a b = 0 := by
  simpa [halfSpaceLocalBoundaryRemainder] using
    boxRemainingFormFaceTerms_eq_zero_of_tsupport_disjoint ω a b h0 hsucc

/-- Topological-support version of artificial-boundary vanishing. -/
theorem halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_disjoint_artificial {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (h : Disjoint (halfSpaceArtificialFaceSet a b) (tsupport ω)) :
    halfSpaceLocalBoundaryRemainder ω a b = 0 := by
  simpa [halfSpaceLocalBoundaryRemainder] using
    boxRemainingFormFaceTerms_eq_zero_of_tsupport_disjoint_artificial ω a b h

theorem halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_subset_halfSpaceSupportBox {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (hsupp : boxFaceCoeffTSupportInHalfSpaceBox ω a b) :
    halfSpaceLocalBoundaryRemainder ω a b = 0 := by
  simpa [halfSpaceLocalBoundaryRemainder] using
    boxRemainingFormFaceTerms_eq_zero_of_tsupport_subset_halfSpaceSupportBox ω a b hsupp

/--
Natural compact-support version of artificial-boundary vanishing.  The input is
the topological support of the form itself, rather than the derived supports of
all coordinate face coefficients.
-/
theorem halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_subset_halfSpaceSupportBox'
    {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (hsupp : tsupport ω ⊆ halfSpaceSupportBox a b) :
    halfSpaceLocalBoundaryRemainder ω a b = 0 := by
  simpa [halfSpaceLocalBoundaryRemainder] using
    boxRemainingFormFaceTerms_eq_zero_of_tsupport_subset_halfSpaceSupportBox' ω a b hsupp

theorem halfSpaceLocalStokes_of_face_cancellation {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    (hω : ContDiff Real ⊤ ω)
    (h0 : boxUpperFormFaceIntegral ω (0 : Fin (n + 1)) a b = 0)
    (hsucc : ∀ i : Fin n,
      upperFaceSign i.succ * boxUpperFormFaceIntegral ω i.succ a b +
        lowerFaceSign i.succ * boxLowerFormFaceIntegral ω i.succ a b = 0) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b :=
  halfSpaceLocalStokes_of_remainder_eq_zero ω a b hle ha0 hω
    (halfSpaceLocalBoundaryRemainder_eq_zero_of_face_cancellation ω a b h0 hsucc)

theorem halfSpaceLocalStokes_of_support_disjoint {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    (hω : ContDiff Real ⊤ ω)
    (h0 : Disjoint (boxUpperFaceSet (0 : Fin (n + 1)) a b)
      (Function.support (boxFormFaceCoeff ω (0 : Fin (n + 1)))))
    (hsucc : ∀ i : Fin n,
      Disjoint (boxUpperFaceSet i.succ a b) (Function.support (boxFormFaceCoeff ω i.succ)) ∧
      Disjoint (boxLowerFaceSet i.succ a b) (Function.support (boxFormFaceCoeff ω i.succ))) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b :=
  halfSpaceLocalStokes_of_remainder_eq_zero ω a b hle ha0 hω
    (halfSpaceLocalBoundaryRemainder_eq_zero_of_support_disjoint ω a b h0 hsucc)

theorem halfSpaceLocalStokes_of_support_disjoint_artificial {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    (hω : ContDiff Real ⊤ ω)
    (h : Disjoint (halfSpaceArtificialFaceSet a b) (Function.support ω)) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b :=
  halfSpaceLocalStokes_of_remainder_eq_zero ω a b hle ha0 hω
    (halfSpaceLocalBoundaryRemainder_eq_zero_of_support_disjoint_artificial ω a b h)

theorem halfSpaceLocalStokes_of_tsupport_disjoint {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    (hω : ContDiff Real ⊤ ω)
    (h0 : Disjoint (boxUpperFaceSet (0 : Fin (n + 1)) a b)
      (tsupport (boxFormFaceCoeff ω (0 : Fin (n + 1)))))
    (hsucc : ∀ i : Fin n,
      Disjoint (boxUpperFaceSet i.succ a b) (tsupport (boxFormFaceCoeff ω i.succ)) ∧
      Disjoint (boxLowerFaceSet i.succ a b) (tsupport (boxFormFaceCoeff ω i.succ))) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b :=
  halfSpaceLocalStokes_of_remainder_eq_zero ω a b hle ha0 hω
    (halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_disjoint ω a b h0 hsucc)

theorem halfSpaceLocalStokes_of_tsupport_disjoint_artificial {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    (hω : ContDiff Real ⊤ ω)
    (h : Disjoint (halfSpaceArtificialFaceSet a b) (tsupport ω)) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b :=
  halfSpaceLocalStokes_of_remainder_eq_zero ω a b hle ha0 hω
    (halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_disjoint_artificial ω a b h)

theorem halfSpaceLocalStokes_of_tsupport_subset_halfSpaceSupportBox' {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    (hω : ContDiff Real ⊤ ω)
    (hsupp : tsupport ω ⊆ halfSpaceSupportBox a b) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b :=
  halfSpaceLocalStokes_of_remainder_eq_zero ω a b hle ha0 hω
    (halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_subset_halfSpaceSupportBox'
      ω a b hsupp)

/--
Clean compact-support local half-space Stokes statement.  The hypothesis
`boxFaceCoeffTSupportInHalfSpaceBox` is the chart-box selection condition:
all face coefficients are supported away from artificial faces, while support
may still meet the true half-space boundary.
-/
theorem halfSpaceLocalStokes_compactSupport {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    (hω : ContDiff Real ⊤ ω)
    (hsupp : boxFaceCoeffTSupportInHalfSpaceBox ω a b) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b :=
  halfSpaceLocalStokes_of_remainder_eq_zero ω a b hle ha0 hω
    (halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_subset_halfSpaceSupportBox
      ω a b hsupp)

/--
Clean compact-support local half-space Stokes from smoothness on an open
neighborhood of the chart box.
-/
theorem halfSpaceLocalStokes_compactSupport_of_contDiffOn_isOpen {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hω : ContDiffOn Real ⊤ ω U)
    (hsupp : boxFaceCoeffTSupportInHalfSpaceBox ω a b) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b :=
  halfSpaceLocalStokes_of_remainder_eq_zero_of_contDiffOn_isOpen
    ω a b hle ha0 hU hbox hω
    (halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_subset_halfSpaceSupportBox
      ω a b hsupp)

/-- `C^\infty` local half-space Stokes on a compact-support box. -/
theorem halfSpaceLocalStokes_compactSupport_of_contDiffOn_isOpen_infty {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hω : ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞) ω U)
    (hsupp : boxFaceCoeffTSupportInHalfSpaceBox ω a b) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b :=
  halfSpaceLocalStokes_of_remainder_eq_zero_of_contDiffOn_isOpen_infty
    ω a b hle ha0 hU hbox hω
    (halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_subset_halfSpaceSupportBox
      ω a b hsupp)

theorem halfSpaceLocalStokes_of_tsupport_subset_halfSpaceSupportBox_contDiffOn'
    {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hω : ContDiffOn Real ⊤ ω U)
    (hsupp : tsupport ω ⊆ halfSpaceSupportBox a b) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b :=
  halfSpaceLocalStokes_of_remainder_eq_zero_of_contDiffOn_isOpen
    ω a b hle ha0 hU hbox hω
    (halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_subset_halfSpaceSupportBox'
      ω a b hsupp)

theorem halfSpaceLocalStokes_of_tsupport_subset_halfSpaceSupportBox_contDiffOn_infty'
    {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hω : ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞) ω U)
    (hsupp : tsupport ω ⊆ halfSpaceSupportBox a b) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b :=
  halfSpaceLocalStokes_of_remainder_eq_zero_of_contDiffOn_isOpen_infty
    ω a b hle ha0 hU hbox hω
    (halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_subset_halfSpaceSupportBox'
      ω a b hsupp)

/--
Existence form of compact-support local half-space Stokes.  A compact
topological support contained in the half-space can be enclosed in a half-space
support box, and that box satisfies the local half-space Stokes identity.
-/
theorem exists_halfSpaceLocalStokesBox_of_isCompact_tsupport_subset_halfSpace
    {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (hω : ContDiff Real ⊤ ω)
    (hK : IsCompact (tsupport ω))
    (hhalf : tsupport ω ⊆ upperHalfSpace n) :
    ∃ a b : Fin (n + 1) → Real,
      a 0 = 0 ∧ a ≤ b ∧
        tsupport ω ⊆ halfSpaceSupportBox a b ∧
          halfSpaceLocalBulkIntegral ω a b =
            halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b := by
  rcases exists_halfSpaceSupportBox_of_isCompact (K := tsupport ω) hK hhalf with
    ⟨a, b, ha0, hle, hsupp⟩
  exact ⟨a, b, ha0, hle, hsupp,
    halfSpaceLocalStokes_of_tsupport_subset_halfSpaceSupportBox'
      ω a b hle ha0 hω hsupp⟩

/--
Compact-set form of local half-space Stokes.  It is often easier upstream to
provide a compact coordinate carrier `K` containing the support than to prove
compactness of `tsupport ω` directly.
-/
theorem exists_halfSpaceLocalStokesBox_of_tsupport_subset_compact_halfSpace
    {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (hω : ContDiff Real ⊤ ω)
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K)
    (hsuppK : tsupport ω ⊆ K)
    (hhalf : K ⊆ upperHalfSpace n) :
    ∃ a b : Fin (n + 1) → Real,
      a 0 = 0 ∧ a ≤ b ∧
        tsupport ω ⊆ halfSpaceSupportBox a b ∧
          halfSpaceLocalBulkIntegral ω a b =
            halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b := by
  rcases exists_halfSpaceSupportBox_of_isCompact (K := K) hK hhalf with
    ⟨a, b, ha0, hle, hKbox⟩
  have hsupp : tsupport ω ⊆ halfSpaceSupportBox a b := hsuppK.trans hKbox
  exact ⟨a, b, ha0, hle, hsupp,
    halfSpaceLocalStokes_of_tsupport_subset_halfSpaceSupportBox'
      ω a b hle ha0 hω hsupp⟩

/-- Alias with the word order used in the roadmap. -/
theorem localHalfSpaceStokes_compactSupport {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    (hω : ContDiff Real ⊤ ω)
    (hsupp : boxFaceCoeffTSupportInHalfSpaceBox ω a b) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b :=
  halfSpaceLocalStokes_compactSupport ω a b hle ha0 hω hsupp

/-- Alias for the local-smoothness compact-support theorem. -/
theorem localHalfSpaceStokes_compactSupport_of_contDiffOn_isOpen {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hω : ContDiffOn Real ⊤ ω U)
    (hsupp : boxFaceCoeffTSupportInHalfSpaceBox ω a b) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b :=
  halfSpaceLocalStokes_compactSupport_of_contDiffOn_isOpen
    ω a b hle ha0 hU hbox hω hsupp

/-- Alias for the `C^\infty` local-smoothness compact-support theorem. -/
theorem localHalfSpaceStokes_compactSupport_of_contDiffOn_isOpen_infty {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (hle : a ≤ b) (ha0 : a 0 = 0)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hω : ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞) ω U)
    (hsupp : boxFaceCoeffTSupportInHalfSpaceBox ω a b) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b :=
  halfSpaceLocalStokes_compactSupport_of_contDiffOn_isOpen_infty
    ω a b hle ha0 hU hbox hω hsupp

end Stokes

end
