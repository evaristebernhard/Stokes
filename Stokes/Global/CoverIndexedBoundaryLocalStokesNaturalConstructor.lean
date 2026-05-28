import Stokes.Global.CoverIndexedNaturalConstructor

/-!
# Natural boundary local-Stokes constructors for the cover-indexed route

This file isolates the boundary half of the local-Stokes handoff.  The useful
mathematical input is the natural compact-support statement for the localized
boundary-chart representative:

`tsupport α ⊆ halfSpaceSupportBox a b`.

Once this is available, the half-space local Stokes theorem gives the
cover-indexed boundary equality

`coverIndexLocalBulkTerm = coverIndexLocalBoundaryTerm`.

The wrappers below deliberately avoid changing the public `CoverIndexed.lean`
entry point.  They are import candidates for the next integration pass.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryLocalStokesNaturalConstructor

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
Project-local boundary Stokes from the natural selected-box support statement.

This is the smallest bridge from the half-space theorem to the project-local
boundary-chart wrappers: if the transition-pullback representative itself is
supported in the selected half-space support box, then the artificial faces
vanish and the local bulk term is the outward-first boundary term.
-/
theorem projectLocalStokes_of_tsupport_subset_halfSpaceSupportBox_infty
    {x0 x1 : M} {η : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hηU :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I x0 x1 η) U)
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 η) ⊆
        halfSpaceSupportBox a b) :
    projectLocalBulkIntegral I x0 x1 η a b =
      projectLocalBoundaryIntegral I x0 x1 η a b := by
  let hbox : boundaryChartSelectedBox I x0 x1 η a b :=
    ⟨ha0, hle, hdomain, hsupp⟩
  rw [projectLocalBulkIntegral, projectLocalBoundaryIntegral,
    halfSpaceLocalTransitionBulkIntegral,
    outwardFirstBoundaryChartIntegral_eq_halfSpaceBoundarySign_mul]
  exact hbox.localStokes_transitionPullback_of_contDiffOn_isOpen_infty hU hUbox hηU

namespace SupportControlledSelectedPartition

/--
Boundary cover-index local Stokes from direct support of the localized
representative in the assigned half-space support box.

This is the cover-indexed form of
`projectLocalStokes_of_tsupport_subset_halfSpaceSupportBox_infty`.
-/
theorem coverIndexBoundaryLocalStokes_of_tsupport_subset_halfSpaceSupportBox_infty
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters})
    {U : Set (Fin (n + 1) → Real)}
    (hU : IsOpen U)
    (hUbox : Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆ U)
    (hlocalizedU :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))) U)
    (hsupp :
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1)
            (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
        halfSpaceSupportBox
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    P.coverIndexLocalBulkTerm ω (Sum.inr i) =
      P.coverIndexLocalBoundaryTerm ω (Sum.inr i) := by
  simpa [SupportControlledSelectedPartition.coverIndexLocalBulkTerm,
    SupportControlledSelectedPartition.coverIndexLocalBoundaryTerm] using
    projectLocalStokes_of_tsupport_subset_halfSpaceSupportBox_infty
      (I := I)
      (x0 := C.boundaryChart i.1) (x1 := C.boundaryChart i.1)
      (η := P.coverIndexLocalizedForm ω (Sum.inr i))
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (C.boundary_lower_zero i.1 i.2)
      (C.boundary_le i.1 i.2)
      (C.boundary_Icc_subset_domain i.1 i.2)
      hU hUbox hlocalizedU hsupp

/--
Finite-sum boundary local Stokes over the selected boundary cover, using
direct support of every localized boundary representative in its assigned
half-space support box.
-/
theorem boundaryCoverIndexLocalBulkSum_eq_localBoundarySum_of_tsupport_subset_halfSpaceSupportBox_infty
    (P : SupportControlledSelectedPartition C)
    (U : {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (hU :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (U i))
    (hUbox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆ U i)
    (hlocalizedU :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionPullbackInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1)
            (P.coverIndexLocalizedForm ω (Sum.inr i))) (U i))
    (hsupp :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    (Finset.sum C.boundaryCoverIndexFinset fun i =>
        P.coverIndexLocalBulkTerm ω (Sum.inr i)) =
      Finset.sum C.boundaryCoverIndexFinset fun i =>
        P.coverIndexLocalBoundaryTerm ω (Sum.inr i) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact
    P.coverIndexBoundaryLocalStokes_of_tsupport_subset_halfSpaceSupportBox_infty
      i (hU i) (hUbox i) (hlocalizedU i) (hsupp i)

/--
Boundary cover-index local Stokes from assigned boundary-box fields and grouped
boundary smoothness.  This is the practical adapter for the current
`CoverIndexedAssignedBoxLocalData` route.
-/
theorem coverIndexBoundaryLocalStokes_of_assignedBoxFields
    [IsManifold I ⊤ M]
    (P : SupportControlledSelectedPartition C)
    (boundaryCoordSupport boundaryNeighborhood :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (boundaryAssignedFields :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryAssignedBoxCoordSupportFields P i ω
          (boundaryCoordSupport i) (boundaryNeighborhood i))
    (smoothness :
      CoverIndexedBoundarySmoothnessFields P ω boundaryNeighborhood)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    P.coverIndexLocalBulkTerm ω (Sum.inr i) =
      P.coverIndexLocalBoundaryTerm ω (Sum.inr i) :=
  SupportControlledCoverIndexedLocalStokesFields.boundaryLocalBulk_eq_localBoundary_of_assignedBoxFieldsAndBoundarySmoothness
      (P := P) (omega := ω)
      boundaryCoordSupport boundaryNeighborhood boundaryAssignedFields
      smoothness i

/--
Finite-sum boundary local Stokes from assigned boundary-box fields and grouped
boundary smoothness.
-/
theorem boundaryCoverIndexLocalBulkSum_eq_localBoundarySum_of_assignedBoxFields
    [IsManifold I ⊤ M]
    (P : SupportControlledSelectedPartition C)
    (boundaryCoordSupport boundaryNeighborhood :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (boundaryAssignedFields :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryAssignedBoxCoordSupportFields P i ω
          (boundaryCoordSupport i) (boundaryNeighborhood i))
    (smoothness :
      CoverIndexedBoundarySmoothnessFields P ω boundaryNeighborhood) :
    (Finset.sum C.boundaryCoverIndexFinset fun i =>
        P.coverIndexLocalBulkTerm ω (Sum.inr i)) =
      Finset.sum C.boundaryCoverIndexFinset fun i =>
        P.coverIndexLocalBoundaryTerm ω (Sum.inr i) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact
    P.coverIndexBoundaryLocalStokes_of_assignedBoxFields
      boundaryCoordSupport boundaryNeighborhood boundaryAssignedFields
      smoothness i

end SupportControlledSelectedPartition

namespace CoverIndexedAssignedBoxLocalData

/--
Boundary part of `CoverIndexedAssignedBoxLocalData.toLocalFields`: each
boundary selected cover index satisfies the local half-space Stokes equality.
-/
theorem boundaryLocalBulk_eq_localBoundary
    [IsManifold I ⊤ M]
    (D : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    P.coverIndexLocalBulkTerm ω (Sum.inr i) =
      P.coverIndexLocalBoundaryTerm ω (Sum.inr i) :=
  P.coverIndexBoundaryLocalStokes_of_assignedBoxFields
    D.boundaryCoordSupport D.boundaryNeighborhood
    D.boundaryAssignedFields D.smoothness i

/--
Finite-sum boundary local Stokes supplied by `CoverIndexedAssignedBoxLocalData`.
This is the grouped boundary field needed before boundary set-integral
reconstruction replaces the local boundary terms by target-chart integrals.
-/
theorem boundaryLocalBulkSum_eq_localBoundarySum
    [IsManifold I ⊤ M]
    (D : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω) :
    (Finset.sum C.boundaryCoverIndexFinset fun i =>
        P.coverIndexLocalBulkTerm ω (Sum.inr i)) =
      Finset.sum C.boundaryCoverIndexFinset fun i =>
        P.coverIndexLocalBoundaryTerm ω (Sum.inr i) :=
  P.boundaryCoverIndexLocalBulkSum_eq_localBoundarySum_of_assignedBoxFields
    D.boundaryCoordSupport D.boundaryNeighborhood
    D.boundaryAssignedFields D.smoothness

end CoverIndexedAssignedBoxLocalData

end BoundaryLocalStokesNaturalConstructor

end Stokes

end
