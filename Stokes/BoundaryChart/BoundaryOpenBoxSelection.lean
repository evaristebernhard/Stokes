import Stokes.BoundaryChart.BoundaryBoxSelection

/-!
# Boundary open-box selection

This file isolates the honest open-neighborhood part of boundary chart box
selection.

The tempting global statement

```
K compact, K ⊆ upperHalfSpace n, K ⊆ U, IsOpen U
  ⟹ ∃ a b, a 0 = 0 ∧ K ⊆ halfSpaceSupportBox a b ∧ Set.Icc a b ⊆ U
```

is false for arbitrary `U`: even a single interior point of the half-space may
have a small open neighborhood that does not contain the vertical segment down
to the boundary face forced by `a 0 = 0`.  A disconnected compact set gives
another obstruction to selecting one rectangular box inside a disconnected
open set.

The useful true statements are local boundary-point box selection, and direct
constructors from an already supplied closed-box containment.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section PureHalfSpace

/--
Every ambient neighborhood of a boundary-hyperplane point contains a closed
half-space box based at the true boundary face and having the point in its
support region.

This is the local version of the desired open-box buffer.  The boundary
assumption `x 0 = 0` is essential: for interior points, a box with `a 0 = 0`
also contains the vertical segment down to the boundary.
-/
theorem exists_halfSpaceSupportBox_subset_of_boundary_mem_nhds {n : Nat}
    {U : Set (Fin (n + 1) → Real)} {x : Fin (n + 1) → Real}
    (hx0 : x 0 = 0) (hU : U ∈ 𝓝 x) :
    ∃ a b : Fin (n + 1) → Real,
      a 0 = 0 ∧ a ≤ b ∧ x ∈ halfSpaceSupportBox a b ∧ Set.Icc a b ⊆ U := by
  obtain ⟨ε, hεpos, hεsubset⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  let a : Fin (n + 1) → Real := Fin.cases (0 : Real) (fun i : Fin n => x i.succ - ε)
  let b : Fin (n + 1) → Real := Fin.cases ε (fun i : Fin n => x i.succ + ε)
  refine ⟨a, b, rfl, ?_, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ ?_ j
    · dsimp [a, b]
      exact le_of_lt hεpos
    · intro i
      dsimp [a, b]
      linarith
  · refine ⟨?_, ?_, ?_⟩
    · simp [a, hx0]
    · dsimp [b]
      linarith
    · intro i
      constructor
      · dsimp [a]
        linarith
      · dsimp [b]
        linarith
  · intro z hz
    apply hεsubset
    rw [Metric.mem_closedBall]
    rw [dist_pi_le_iff (le_of_lt hεpos)]
    intro j
    refine Fin.cases ?_ ?_ j
    · rw [Real.dist_eq, abs_sub_le_iff]
      have hz_left : 0 ≤ z 0 := by
        simpa [a] using hz.1 0
      have hz_right : z 0 ≤ ε := by
        simpa [b] using hz.2 0
      constructor <;> linarith
    · intro i
      rw [Real.dist_eq, abs_sub_le_iff]
      have hz_left : x i.succ - ε ≤ z i.succ := by
        simpa [a] using hz.1 i.succ
      have hz_right : z i.succ ≤ x i.succ + ε := by
        simpa [b] using hz.2 i.succ
      constructor <;> linarith

/--
Open-set spelling of
`exists_halfSpaceSupportBox_subset_of_boundary_mem_nhds`.
-/
theorem exists_halfSpaceSupportBox_subset_open_of_boundary_mem {n : Nat}
    {U : Set (Fin (n + 1) → Real)} {x : Fin (n + 1) → Real}
    (hx0 : x 0 = 0) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ a b : Fin (n + 1) → Real,
      a 0 = 0 ∧ a ≤ b ∧ x ∈ halfSpaceSupportBox a b ∧ Set.Icc a b ⊆ U :=
  exists_halfSpaceSupportBox_subset_of_boundary_mem_nhds hx0 (hU.mem_nhds hxU)

end PureHalfSpace

section ManifoldBoundary

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}

/--
Construct boundary compact box-selection data from a concrete half-space box
whose closed ambient box is already known to lie in the boundary chart domain.

This is the mathematically honest replacement for trying to infer a single
global rectangular box from `K ⊆ U` and `IsOpen U` alone.
-/
def boundaryCompactBoxSelectionDataOfBox
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hKbox : K ⊆ halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1) :
    BoundaryCompactBoxSelectionData I x0 x1 ω where
  K := K
  isCompact_K := hK
  tsupport_subset_K := hsupp
  K_subset_upperHalfSpace := hhalf
  a := a
  b := b
  ha0 := ha0
  le := hle
  Icc_subset_domain := hdomain
  K_subset_halfSpaceSupportBox := hKbox

/--
Existential projection of `boundaryCompactBoxSelectionDataOfBox`, preserving
the selected corners definitionally.
-/
theorem exists_boundaryCompactBoxSelectionData_of_isCompact_of_box_subset_domain
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hKbox : K ⊆ halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1) :
    ∃ D : BoundaryCompactBoxSelectionData I x0 x1 ω,
      D.K = K ∧ D.a = a ∧ D.b = b := by
  refine ⟨boundaryCompactBoxSelectionDataOfBox
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    hK hhalf hsupp ha0 hle hKbox hdomain, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl

/--
Concrete-box local Stokes wrapper.  Once a closed box has been selected inside
the boundary chart domain and inside an ambient smoothness neighborhood, the
compact boundary-chart data and the outward-first local Stokes identity are
available without the old universal `hdomain` callback.
-/
theorem exists_boundaryCompactBoxSelectionData_localStokes_of_isCompact_of_box_subset_domain
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hKbox : K ⊆ halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hωU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    ∃ D : BoundaryCompactBoxSelectionData I x0 x1 ω,
      D.K = K ∧ D.a = a ∧ D.b = b ∧
        halfSpaceLocalBulkIntegral
            (ManifoldForm.transitionPullbackInChart I x0 x1 ω) D.a D.b =
          outwardFirstBoundaryChartIntegral I x0 x1 ω D.a D.b := by
  let D : BoundaryCompactBoxSelectionData I x0 x1 ω :=
    boundaryCompactBoxSelectionDataOfBox
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      hK hhalf hsupp ha0 hle hKbox hdomain
  refine ⟨D, rfl, rfl, rfl, ?_⟩
  exact D.localStokes_transitionPullback_of_contDiffOn_isOpen_outwardFirst
    hU hUbox hωU

/--
`C^\infty` version of
`exists_boundaryCompactBoxSelectionData_localStokes_of_isCompact_of_box_subset_domain`.
-/
theorem exists_boundaryCompactBoxSelectionData_localStokes_of_isCompact_of_box_subset_domain_infty
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hKbox : K ⊆ halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hωU :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    ∃ D : BoundaryCompactBoxSelectionData I x0 x1 ω,
      D.K = K ∧ D.a = a ∧ D.b = b ∧
        halfSpaceLocalBulkIntegral
            (ManifoldForm.transitionPullbackInChart I x0 x1 ω) D.a D.b =
          outwardFirstBoundaryChartIntegral I x0 x1 ω D.a D.b := by
  let D : BoundaryCompactBoxSelectionData I x0 x1 ω :=
    boundaryCompactBoxSelectionDataOfBox
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      hK hhalf hsupp ha0 hle hKbox hdomain
  refine ⟨D, rfl, rfl, rfl, ?_⟩
  exact D.localStokes_transitionPullback_of_contDiffOn_isOpen_outwardFirst_infty
    hU hUbox hωU

/--
Same constructor, but with a concrete ambient open set that also supplies the
boundary chart-domain containment.
-/
theorem exists_boundaryCompactBoxSelectionData_localStokes_of_isCompact_of_box_subset_open
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hKbox : K ⊆ halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hωU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    ∃ D : BoundaryCompactBoxSelectionData I x0 x1 ω,
      D.K = K ∧ D.a = a ∧ D.b = b ∧
        halfSpaceLocalBulkIntegral
            (ManifoldForm.transitionPullbackInChart I x0 x1 ω) D.a D.b =
          outwardFirstBoundaryChartIntegral I x0 x1 ω D.a D.b :=
  exists_boundaryCompactBoxSelectionData_localStokes_of_isCompact_of_box_subset_domain
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    hK hhalf hsupp ha0 hle hKbox hdomain hU hUbox hωU

end ManifoldBoundary

end Stokes

end
