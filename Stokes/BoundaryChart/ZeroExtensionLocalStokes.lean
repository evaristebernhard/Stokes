import Stokes.Global.ZeroExtensionBulkEquality
import Stokes.BoundaryChart.LocalStokes

/-!
# Local Stokes wrappers for zero-extended chart representatives

The zero-extension layer is used for support control, while local Stokes still
uses the original smooth chart representative.  This file packages the bridge
between those two roles on a chart box contained in the concrete chart
transition source.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundaryZeroExtension

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- The bulk integral for the zero-extended transition representative. -/
def halfSpaceLocalTransitionZeroBulkIntegral {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Real :=
  halfSpaceLocalBulkIntegral
    (ManifoldForm.transitionPullbackInChartZero I x0 x1 ω) a b

/-- The true boundary-face integral for the zero-extended transition representative. -/
def halfSpaceBoundaryTransitionZeroFormIntegral {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Real :=
  halfSpaceBoundaryFormIntegral
    (ManifoldForm.transitionPullbackInChartZero I x0 x1 ω) a b

/-- The artificial-face remainder for the zero-extended transition representative. -/
def halfSpaceLocalTransitionZeroBoundaryRemainder {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Real :=
  halfSpaceLocalBoundaryRemainder
    (ManifoldForm.transitionPullbackInChartZero I x0 x1 ω) a b

/-- Face coefficient of a zero-extended transition representative. -/
def halfSpaceTransitionZeroFaceCoeff {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) (i : Fin (n + 1)) :
    (Fin (n + 1) → Real) → Real :=
  boxFormFaceCoeff (ManifoldForm.transitionPullbackInChartZero I x0 x1 ω) i

/-- Selected half-space-box support predicate for zero face coefficients. -/
def halfSpaceTransitionZeroFaceCoeffTSupportInHalfSpaceBox {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Prop :=
  ∀ i : Fin (n + 1),
    tsupport (halfSpaceTransitionZeroFaceCoeff I x0 x1 ω i) ⊆
      halfSpaceSupportBox a b

/-- A box-face point belongs to the ambient closed box. -/
theorem boxFaceMap_mem_Icc_of_mem_faceDomain {n : Nat}
    {i : Fin (n + 1)} {a b : Fin (n + 1) → Real} {c : Real}
    {x : Fin n → Real} (hx : x ∈ faceDomain i a b)
    (hc : c ∈ Icc (a i) (b i)) :
    boxFaceMap i c x ∈ Icc a b := by
  simpa [boxFaceMap, faceDomain] using
    (Fin.insertNth_mem_Icc (i := i) (x := c) (p := x)
      (q₁ := a) (q₂ := b)).2 ⟨hc, hx⟩

/-- On any set contained in the transition source, zero and old transition
representatives agree pointwise. -/
theorem transitionPullbackInChartZero_eqOn_transitionPullbackInChart_of_subset
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {U : Set (Fin (n + 1) → Real)}
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    EqOn (ManifoldForm.transitionPullbackInChartZero I x0 x1 ω)
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U := by
  intro y hy
  exact ManifoldForm.transitionPullbackInChartZero_eq_transitionPullbackInChart_of_mem_source
    (I := I) (x0 := x0) (x1 := x1) (ω := ω) (hUsource hy)

/-- If an open chart box lies in the transition source, the zero and old bulk
scalar integrals agree on that box. -/
theorem halfSpaceLocalTransitionZeroBulkIntegral_eq_transitionBulkIntegral_of_box_subset
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real}
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    halfSpaceLocalTransitionZeroBulkIntegral I x0 x1 ω a b =
      halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b := by
  unfold halfSpaceLocalTransitionZeroBulkIntegral halfSpaceLocalTransitionBulkIntegral
    halfSpaceLocalBulkIntegral
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
  intro y hy
  exact zeroTransitionBulkIntegrand_eq_bulkIntegrand_of_isOpen_mem
    (I := I) (x0 := x0) (x1 := x1) (ω := ω) (y := y)
    hU (hbox hy) hUsource

/-- Boundary-face pointwise equality of zero and old transition representatives. -/
theorem transitionPullbackInChartZero_apply_boundaryTangent_eq_transitionPullbackInChart
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {u : Fin n → Real}
    (hu : boundaryInclusion n u ∈ ManifoldForm.chartTransitionSource I x0 x1) :
    ManifoldForm.transitionPullbackInChartZero I x0 x1 ω
        (boundaryInclusion n u) (boundaryTangent n) =
      ManifoldForm.transitionPullbackInChart I x0 x1 ω
        (boundaryInclusion n u) (boundaryTangent n) := by
  rw [ManifoldForm.transitionPullbackInChartZero_eq_transitionPullbackInChart_of_mem_source
    (I := I) (x0 := x0) (x1 := x1) (ω := ω) hu]

/-- On a boundary face contained in the transition source, the zero and old
boundary integrals agree. -/
theorem halfSpaceBoundaryTransitionZeroFormIntegral_eq_transitionFormIntegral_of_face_subset
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real}
    {U : Set (Fin (n + 1) → Real)}
    (hfaceU : ∀ u ∈ lowerZeroFaceDomain a b, boundaryInclusion n u ∈ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    halfSpaceBoundaryTransitionZeroFormIntegral I x0 x1 ω a b =
      halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b := by
  unfold halfSpaceBoundaryTransitionZeroFormIntegral
    halfSpaceBoundaryTransitionFormIntegral halfSpaceBoundaryFormIntegral
  refine MeasureTheory.setIntegral_congr_fun (by simp [lowerZeroFaceDomain, faceDomain]) ?_
  intro u hu
  exact transitionPullbackInChartZero_apply_boundaryTangent_eq_transitionPullbackInChart
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    (hUsource (hfaceU u hu))

/-- Boundary-integral equality from an ambient box containment. -/
theorem halfSpaceBoundaryTransitionZeroFormIntegral_eq_transitionFormIntegral_of_box_subset
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} (hle : a ≤ b) (ha0 : a 0 = 0)
    {U : Set (Fin (n + 1) → Real)}
    (hbox : Icc a b ⊆ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    halfSpaceBoundaryTransitionZeroFormIntegral I x0 x1 ω a b =
      halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b :=
  halfSpaceBoundaryTransitionZeroFormIntegral_eq_transitionFormIntegral_of_face_subset
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    (a := a) (b := b)
    (fun _u hu => hbox (boundaryInclusion_mem_Icc_of_mem_lowerZeroFaceDomain
      (n := n) (a := a) (b := b) ha0 hle hu))
    hUsource

/-- Upper face integral equality for zero and old transition representatives. -/
theorem boxUpperFormFaceIntegral_transitionPullbackZero_eq_transitionPullback_of_face_subset
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} {i : Fin (n + 1)}
    {U : Set (Fin (n + 1) → Real)}
    (hfaceU : ∀ x ∈ faceDomain i a b, boxFaceMap i (b i) x ∈ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    boxUpperFormFaceIntegral
        (ManifoldForm.transitionPullbackInChartZero I x0 x1 ω) i a b =
      boxUpperFormFaceIntegral
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) i a b := by
  unfold boxUpperFormFaceIntegral
  refine MeasureTheory.setIntegral_congr_fun (by simp [faceDomain]) ?_
  intro x hx
  change
    (ManifoldForm.transitionPullbackInChartZero I x0 x1 ω (i.insertNth (b i) x))
        (boxFaceTangentFrame i) =
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω (i.insertNth (b i) x))
        (boxFaceTangentFrame i)
  rw [ManifoldForm.transitionPullbackInChartZero_eq_transitionPullbackInChart_of_mem_source
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    (hUsource (by simpa [boxFaceMap] using hfaceU x hx))]

/-- Lower face integral equality for zero and old transition representatives. -/
theorem boxLowerFormFaceIntegral_transitionPullbackZero_eq_transitionPullback_of_face_subset
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} {i : Fin (n + 1)}
    {U : Set (Fin (n + 1) → Real)}
    (hfaceU : ∀ x ∈ faceDomain i a b, boxFaceMap i (a i) x ∈ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    boxLowerFormFaceIntegral
        (ManifoldForm.transitionPullbackInChartZero I x0 x1 ω) i a b =
      boxLowerFormFaceIntegral
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) i a b := by
  unfold boxLowerFormFaceIntegral
  refine MeasureTheory.setIntegral_congr_fun (by simp [faceDomain]) ?_
  intro x hx
  change
    (ManifoldForm.transitionPullbackInChartZero I x0 x1 ω (i.insertNth (a i) x))
        (boxFaceTangentFrame i) =
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω (i.insertNth (a i) x))
        (boxFaceTangentFrame i)
  rw [ManifoldForm.transitionPullbackInChartZero_eq_transitionPullbackInChart_of_mem_source
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    (hUsource (by simpa [boxFaceMap] using hfaceU x hx))]

/-- Upper face integral equality from an ambient box containment. -/
theorem boxUpperFormFaceIntegral_transitionPullbackZero_eq_transitionPullback_of_box_subset
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} (hle : a ≤ b) {i : Fin (n + 1)}
    {U : Set (Fin (n + 1) → Real)}
    (hbox : Icc a b ⊆ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    boxUpperFormFaceIntegral
        (ManifoldForm.transitionPullbackInChartZero I x0 x1 ω) i a b =
      boxUpperFormFaceIntegral
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) i a b :=
  boxUpperFormFaceIntegral_transitionPullbackZero_eq_transitionPullback_of_face_subset
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    (a := a) (b := b) (i := i)
    (fun _x hx => hbox (boxFaceMap_mem_Icc_of_mem_faceDomain
      (i := i) (a := a) (b := b) (c := b i) hx ⟨hle i, le_rfl⟩))
    hUsource

/-- Lower face integral equality from an ambient box containment. -/
theorem boxLowerFormFaceIntegral_transitionPullbackZero_eq_transitionPullback_of_box_subset
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} (hle : a ≤ b) {i : Fin (n + 1)}
    {U : Set (Fin (n + 1) → Real)}
    (hbox : Icc a b ⊆ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    boxLowerFormFaceIntegral
        (ManifoldForm.transitionPullbackInChartZero I x0 x1 ω) i a b =
      boxLowerFormFaceIntegral
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) i a b :=
  boxLowerFormFaceIntegral_transitionPullbackZero_eq_transitionPullback_of_face_subset
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    (a := a) (b := b) (i := i)
    (fun _x hx => hbox (boxFaceMap_mem_Icc_of_mem_faceDomain
      (i := i) (a := a) (b := b) (c := a i) hx ⟨le_rfl, hle i⟩))
    hUsource

/-- Artificial-face remainder equality from a chart-box containment in the
transition source. -/
theorem halfSpaceLocalTransitionZeroBoundaryRemainder_eq_transitionBoundaryRemainder_of_box_subset
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} (hle : a ≤ b)
    {U : Set (Fin (n + 1) → Real)}
    (hbox : Icc a b ⊆ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    halfSpaceLocalTransitionZeroBoundaryRemainder I x0 x1 ω a b =
      halfSpaceLocalTransitionBoundaryRemainder I x0 x1 ω a b := by
  unfold halfSpaceLocalTransitionZeroBoundaryRemainder
    halfSpaceLocalTransitionBoundaryRemainder halfSpaceLocalBoundaryRemainder
    boxRemainingFormFaceTerms
  rw [boxUpperFormFaceIntegral_transitionPullbackZero_eq_transitionPullback_of_box_subset
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) hle (i := (0 : Fin (n + 1))) hbox hUsource]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [boxUpperFormFaceIntegral_transitionPullbackZero_eq_transitionPullback_of_box_subset
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) hle (i := i.succ) hbox hUsource,
    boxLowerFormFaceIntegral_transitionPullbackZero_eq_transitionPullback_of_box_subset
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) hle (i := i.succ) hbox hUsource]

/-- A zero-support bound kills the old artificial remainder on boxes contained
in the transition source. -/
theorem halfSpaceLocalTransitionBoundaryRemainder_eq_zero_of_zero_tsupport_subset
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} (hle : a ≤ b)
    {U : Set (Fin (n + 1) → Real)}
    (hbox : Icc a b ⊆ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1)
    (hzerosupp :
      tsupport (ManifoldForm.transitionPullbackInChartZero I x0 x1 ω) ⊆
        halfSpaceSupportBox a b) :
    halfSpaceLocalTransitionBoundaryRemainder I x0 x1 ω a b = 0 := by
  have hzeroRem :
      halfSpaceLocalTransitionZeroBoundaryRemainder I x0 x1 ω a b = 0 := by
    simpa [halfSpaceLocalTransitionZeroBoundaryRemainder] using
      halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_subset_halfSpaceSupportBox'
        (ManifoldForm.transitionPullbackInChartZero I x0 x1 ω) a b hzerosupp
  have hremEq :
      halfSpaceLocalTransitionZeroBoundaryRemainder I x0 x1 ω a b =
        halfSpaceLocalTransitionBoundaryRemainder I x0 x1 ω a b :=
    halfSpaceLocalTransitionZeroBoundaryRemainder_eq_transitionBoundaryRemainder_of_box_subset
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) hle hbox hUsource
  exact hremEq ▸ hzeroRem

/-- Local half-space Stokes for the old smooth transition representative, with
artificial faces removed using the zero-extended representative's support. -/
theorem halfSpaceLocalStokes_transitionPullback_of_zero_tsupport_subset_contDiffOn_isOpen
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real} (hle : a ≤ b) (ha0 : a 0 = 0)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1)
    (hω : ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U)
    (hzerosupp :
      tsupport (ManifoldForm.transitionPullbackInChartZero I x0 x1 ω) ⊆
        halfSpaceSupportBox a b) :
    halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b := by
  have hrem :
      halfSpaceLocalTransitionBoundaryRemainder I x0 x1 ω a b = 0 :=
    halfSpaceLocalTransitionBoundaryRemainder_eq_zero_of_zero_tsupport_subset
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (a := a) (b := b) hle hbox hUsource hzerosupp
  have hlocal :
      halfSpaceLocalTransitionBulkIntegral I x0 x1 ω a b =
        halfSpaceBoundarySign n *
            halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b +
          halfSpaceLocalTransitionBoundaryRemainder I x0 x1 ω a b := by
    simpa [halfSpaceLocalTransitionBulkIntegral,
      halfSpaceBoundaryTransitionFormIntegral,
      halfSpaceLocalTransitionBoundaryRemainder] using
      (halfSpaceLocalStokes_with_remainder_of_contDiffOn_isOpen
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b
        hle ha0 hU hbox hω)
  simpa [hrem] using hlocal

end ManifoldBoundaryZeroExtension

end Stokes

end
