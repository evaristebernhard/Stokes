import Stokes.HalfSpace.LocalStokes

/-!
# Boundary chart transitions

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

/-- Boundary coordinates of the ambient chart transition along `{x₀ = 0}`. -/
def boundaryChartTransition {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (u : Fin n → Real) : Fin n → Real :=
  fun i => ManifoldForm.chartTransition I x0 x1 (boundaryInclusion n u) i.succ

@[simp]
theorem boundaryChartTransition_apply {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (u : Fin n → Real) (i : Fin n) :
    boundaryChartTransition I x0 x1 u i =
      ManifoldForm.chartTransition I x0 x1 (boundaryInclusion n u) i.succ :=
  rfl

/-- Tangential derivative of a boundary chart transition, in boundary coordinates. -/
def boundaryChartTransitionTangentMap {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (u : Fin n → Real) :
    (Fin n → Real) →L[Real] (Fin n → Real) :=
  (boundaryTangentProjection n).comp
    ((ManifoldForm.chartTransitionDeriv I x0 x1 (boundaryInclusion n u)).comp
      (boundaryTangentInclusion n))

@[simp]
theorem boundaryChartTransitionTangentMap_apply {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (u v : Fin n → Real) :
    boundaryChartTransitionTangentMap I x0 x1 u v =
      fun i : Fin n =>
        ManifoldForm.chartTransitionDeriv I x0 x1 (boundaryInclusion n u)
          (boundaryInclusion n v) i.succ :=
  rfl

/--
The boundary chart transition has the expected Frechet derivative: the ambient
chart-transition derivative restricted to boundary tangent coordinates.
-/
theorem boundaryChartTransition_hasFDerivWithinAt {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H} [IsManifold I 1 M]
    (x0 x1 : M) {s : Set (Fin n → Real)} {u : Fin n → Real}
    (hsource : ∀ v ∈ s, boundaryInclusion n v ∈ range I)
    (htarget : boundaryInclusion n u ∈ (extChartAt I x0).target)
    (hoverlap : boundaryInclusion n u ∈ ManifoldForm.chartOverlap I x0 x1) :
    HasFDerivWithinAt (boundaryChartTransition I x0 x1)
      (boundaryChartTransitionTangentMap I x0 x1 u) s u := by
  have hsrc :
      boundaryInclusion n u ∈
        ((extChartAt I x0).symm ≫ extChartAt I x1).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    exact ⟨htarget, hoverlap⟩
  have hamb :
      HasFDerivWithinAt (ManifoldForm.chartTransition I x0 x1)
        (ManifoldForm.chartTransitionDeriv I x0 x1 (boundaryInclusion n u))
        (range I) (boundaryInclusion n u) := by
    have hdiff :
        HasFDerivWithinAt (ManifoldForm.chartTransition I x0 x1)
          (fderivWithin Real (ManifoldForm.chartTransition I x0 x1) (range I)
            (boundaryInclusion n u))
          (range I) (boundaryInclusion n u) := by
      simpa [ManifoldForm.chartTransition] using
        ((contDiffWithinAt_ext_coord_change (I := I) (n := (1 : WithTop ℕ∞))
          x1 x0 hsrc).differentiableWithinAt one_ne_zero).hasFDerivWithinAt
    rwa [← ManifoldForm.chartTransitionDeriv_eq_fderivWithin
      (I := I) (x0 := x0) (x1 := x1) htarget hoverlap] at hdiff
  have hincl :
      HasFDerivWithinAt (boundaryInclusion n) (boundaryTangentInclusion n) s u :=
    (boundaryTangentInclusion n).hasFDerivWithinAt
  have hmaps : MapsTo (boundaryInclusion n) s (range I) := by
    intro v hv
    exact hsource v hv
  have hcomp :
      HasFDerivWithinAt
        (boundaryTangentProjection n ∘
          (ManifoldForm.chartTransition I x0 x1 ∘ boundaryInclusion n))
        ((boundaryTangentProjection n).comp
          ((ManifoldForm.chartTransitionDeriv I x0 x1 (boundaryInclusion n u)).comp
            (boundaryTangentInclusion n))) s u :=
    (boundaryTangentProjection n).hasFDerivAt.comp_hasFDerivWithinAt u
      (hamb.comp u hincl hmaps)
  simpa [boundaryChartTransition, boundaryChartTransitionTangentMap,
    Function.comp_def, boundaryTangentProjection_apply] using hcomp

/-- Matrix of the boundary chart transition derivative in standard boundary coordinates. -/
def boundaryChartTransitionMatrix {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (u : Fin n → Real) : Matrix (Fin n) (Fin n) Real :=
  LinearMap.toMatrix'
    (boundaryChartTransitionTangentMap I x0 x1 u :
      (Fin n → Real) →ₗ[Real] (Fin n → Real))

theorem boundaryChartTransitionMatrix_det_eq_linearMap_det {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (u : Fin n → Real) :
    (boundaryChartTransitionMatrix I x0 x1 u).det =
      LinearMap.det
        (boundaryChartTransitionTangentMap I x0 x1 u :
          (Fin n → Real) →ₗ[Real] (Fin n → Real)) :=
  LinearMap.det_toMatrix'
    (boundaryChartTransitionTangentMap I x0 x1 u :
      (Fin n → Real) →ₗ[Real] (Fin n → Real))

/-- Jacobian determinant of the tangential boundary chart transition. -/
def boundaryChartTransitionJacobian {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (u : Fin n → Real) : Real :=
  (boundaryChartTransitionMatrix I x0 x1 u).det

/-- Pointwise assertion that the ambient transition maps the boundary face to the boundary face. -/
def boundaryChartTransitionPreservesBoundaryAt {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (u : Fin n → Real) : Prop :=
  ManifoldForm.chartTransition I x0 x1 (boundaryInclusion n u) =
    boundaryInclusion n (boundaryChartTransition I x0 x1 u)

theorem boundaryChartTransitionPreservesBoundaryAt_of_zero {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (u : Fin n → Real)
    (hzero : ManifoldForm.chartTransition I x0 x1 (boundaryInclusion n u) 0 = 0) :
    boundaryChartTransitionPreservesBoundaryAt I x0 x1 u := by
  unfold boundaryChartTransitionPreservesBoundaryAt
  funext i
  refine Fin.cases ?_ ?_ i
  · simpa [boundaryInclusion] using hzero
  · intro j
    rfl

/--
Pointwise assertion that the ambient transition derivative maps standard
boundary tangent vectors to the tangential derivative encoded by
`boundaryChartTransitionTangentMap`.
-/
def boundaryChartTransitionDerivPreservesTangentAt {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (u : Fin n → Real) : Prop :=
  ∀ j : Fin n,
    ManifoldForm.chartTransitionDeriv I x0 x1 (boundaryInclusion n u)
        (boundaryTangent n j) =
      boundaryTangentInclusion n
        (boundaryChartTransitionTangentMap I x0 x1 u ((Pi.basisFun Real (Fin n)) j))

theorem boundaryChartTransitionDerivPreservesTangentAt_of_normal_zero {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (u : Fin n → Real)
    (hzero : ∀ j : Fin n,
      ManifoldForm.chartTransitionDeriv I x0 x1 (boundaryInclusion n u)
          (boundaryTangent n j) 0 = 0) :
    boundaryChartTransitionDerivPreservesTangentAt I x0 x1 u := by
  intro j
  have htan :
      boundaryTangent n j =
        boundaryInclusion n ((Pi.basisFun Real (Fin n)) j) :=
    (boundaryTangentInclusion_basisFun n j).symm
  funext i
  refine Fin.cases ?_ ?_ i
  · simpa [boundaryTangentInclusion_basisFun] using hzero j
  · intro k
    rw [htan]
    simp [boundaryChartTransitionTangentMap]

/--
Pointwise boundary chart-change formula.  Under the two local boundary
compatibility hypotheses, the boundary integrand of the transition-pulled form
is the target-chart boundary integrand multiplied by the tangential Jacobian.
-/
theorem boundaryChartTransition_pointwise_pullback_det
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (x0 x1 : M) (ω : ManifoldForm I M n) (u : Fin n → Real)
    (hpoint : boundaryChartTransitionPreservesBoundaryAt I x0 x1 u)
    (htangent : boundaryChartTransitionDerivPreservesTangentAt I x0 x1 u) :
    ManifoldForm.transitionPullbackInChart I x0 x1 ω (boundaryInclusion n u)
        (boundaryTangent n) =
      boundaryChartTransitionJacobian I x0 x1 u *
        ManifoldForm.inChart I x1 ω
          (boundaryInclusion n (boundaryChartTransition I x0 x1 u))
          (boundaryTangent n) := by
  change
    ((ManifoldForm.inChart I x1 ω
        (ManifoldForm.chartTransition I x0 x1 (boundaryInclusion n u))).compContinuousLinearMap
        (ManifoldForm.chartTransitionDeriv I x0 x1 (boundaryInclusion n u)))
        (boundaryTangent n) =
      boundaryChartTransitionJacobian I x0 x1 u *
        ManifoldForm.inChart I x1 ω
          (boundaryInclusion n (boundaryChartTransition I x0 x1 u))
          (boundaryTangent n)
  rw [hpoint]
  have htangent_fun :
      (fun j : Fin n =>
        ManifoldForm.chartTransitionDeriv I x0 x1 (boundaryInclusion n u)
          (boundaryTangent n j)) =
        boundaryTangentInclusion n ∘
          boundaryChartTransitionTangentMap I x0 x1 u ∘
            Pi.basisFun Real (Fin n) := by
    funext j
    exact htangent j
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change
    ManifoldForm.inChart I x1 ω
        (boundaryInclusion n (boundaryChartTransition I x0 x1 u))
        (fun j : Fin n =>
          ManifoldForm.chartTransitionDeriv I x0 x1 (boundaryInclusion n u)
            (boundaryTangent n j)) =
      boundaryChartTransitionJacobian I x0 x1 u *
        ManifoldForm.inChart I x1 ω
          (boundaryInclusion n (boundaryChartTransition I x0 x1 u))
          (boundaryTangent n)
  rw [htangent_fun]
  simpa [boundaryChartTransitionJacobian, boundaryChartTransitionMatrix]
    using
      (ambientBoundaryForm_tangentMap_eq_det_mul
        (η := ManifoldForm.inChart I x1 ω
          (boundaryInclusion n (boundaryChartTransition I x0 x1 u)))
        (L := boundaryChartTransitionTangentMap I x0 x1 u))

/--
The natural model-coordinate domain where the transition from chart `x0` to
chart `x1` is meaningful: the `x0` chart target together with the overlap with
the `x1` chart source.
-/
def boundaryChartDomain {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H) (x0 x1 : M) :
    Set (Fin (n + 1) → Real) :=
  (extChartAt I x0).target ∩ ManifoldForm.chartOverlap I x0 x1

/--
The boundary-coordinate part of the natural chart-transition source.

This is the overlap domain on which the transition from the boundary chart at
`x0` to the boundary chart at `x1` is meaningful.
-/
def boundaryChartTransitionBoundarySource {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H) (x0 x1 : M) :
    Set (Fin n → Real) :=
  {u | boundaryInclusion n u ∈ boundaryChartDomain I x0 x1}

@[simp]
theorem mem_boundaryChartTransitionBoundarySource_iff {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H) (x0 x1 : M)
    (u : Fin n → Real) :
    u ∈ boundaryChartTransitionBoundarySource I x0 x1 ↔
      boundaryInclusion n u ∈ boundaryChartDomain I x0 x1 :=
  Iff.rfl

theorem boundaryChartDomain_eq_chartTransitionSource {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H) (x0 x1 : M) :
    boundaryChartDomain I x0 x1 =
      ManifoldForm.chartTransitionSource I x0 x1 := by
  rw [boundaryChartDomain, ManifoldForm.chartTransitionSource_eq]

theorem boundaryChartDomain_subset_target {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H) (x0 x1 : M) :
    boundaryChartDomain I x0 x1 ⊆ (extChartAt I x0).target :=
  inter_subset_left

theorem boundaryChartDomain_subset_overlap {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H) (x0 x1 : M) :
    boundaryChartDomain I x0 x1 ⊆ ManifoldForm.chartOverlap I x0 x1 :=
  inter_subset_right

end ManifoldBoundary

end Stokes

end
