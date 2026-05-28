import Stokes.Global.CoverIndexedLocalFieldsConstructor
import Stokes.Global.InteriorSupportControlledAssignedBox

/-!
# Interior constructors for cover-indexed local Stokes fields

The cover-indexed local Stokes package has four flat interior inputs:
an extended local box, a coordinate support for the base representative, and
the two chart-coordinate bookkeeping maps.  This file packages those inputs in
the same assigned-box style already used on the boundary side, and exposes the
interior consequences directly.

The main mathematical payoff is the interior half of local Stokes: once an
interior localized piece is supported in its assigned strict coordinate box,
its project-local bulk term is zero, hence it agrees with the cover-indexed
interior boundary term, which is definitionally zero.
-/

noncomputable section

set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section InteriorLocalFieldsConstructor

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {ω : ManifoldForm I M n}

namespace SupportControlledSelectedPartition

/--
Interior assigned-box coordinate-support fields for a support-controlled
cover-indexed partition.

This is the interior analogue of
`BoundaryAssignedBoxCoordSupportFields`, but it carries exactly the data needed
to erase the four flat interior inputs of
`SupportControlledCoverIndexedLocalStokesFields`.
-/
abbrev InteriorAssignedBoxCoordSupportFields
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.interiorCenters})
    (ω : ManifoldForm I M n)
    (coordSupport : Set (Fin (n + 1) → Real)) : Prop :=
  interiorChartExtendedBox I
      (C.interiorChart i.1) (C.interiorChart i.1)
      (P.coverIndexLocalizedForm ω (Sum.inl i))
      (C.interiorLower i.1) (C.interiorUpper i.1) ∧
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (C.interiorChart i.1) (C.interiorChart i.1) ω) ⊆
      coordSupport ∧
      (∀ y ∈ coordSupport,
        (extChartAt I (C.interiorChart i.1)).symm y ∈ K) ∧
        coordSupport ⊆ (extChartAt I (C.interiorChart i.1)).target

/-- Constructor for the interior assigned-box field package. -/
theorem interior_assignedBoxCoordSupportFields
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.interiorCenters})
    {coordSupport : Set (Fin (n + 1) → Real)}
    (hbox :
      interiorChartExtendedBox I
        (C.interiorChart i.1) (C.interiorChart i.1)
        (P.coverIndexLocalizedForm ω (Sum.inl i))
        (C.interiorLower i.1) (C.interiorUpper i.1))
    (hbase :
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.interiorChart i.1) (C.interiorChart i.1) ω) ⊆
        coordSupport)
    (hcoordK :
      ∀ y ∈ coordSupport,
        (extChartAt I (C.interiorChart i.1)).symm y ∈ K)
    (hcoordTarget :
      coordSupport ⊆ (extChartAt I (C.interiorChart i.1)).target) :
    InteriorAssignedBoxCoordSupportFields P i ω coordSupport :=
  ⟨hbox, hbase, hcoordK, hcoordTarget⟩

/--
The localized interior representative is supported in the assigned strict
coordinate box.  The coefficient support part comes from the
support-controlled selected partition.
-/
theorem interiorLocalizedSupportSubset_of_assignedBoxFields
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.interiorCenters})
    {coordSupport : Set (Fin (n + 1) → Real)}
    (hfields : InteriorAssignedBoxCoordSupportFields P i ω coordSupport) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (C.interiorChart i.1) (C.interiorChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inl i))) ⊆
      boxInteriorSupportBox (C.interiorLower i.1) (C.interiorUpper i.1) := by
  rcases hfields with ⟨_hbox, hbase, hcoordK, hcoordTarget⟩
  exact
    ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_interiorBox_of_coordSupport
      (I := I)
      (x0 := C.interiorChart i.1) (x1 := C.interiorChart i.1)
      (ρ := P.partition (Sum.inl i)) (ω := ω)
      (a := C.interiorLower i.1) (b := C.interiorUpper i.1)
      hbase
      (P.interior_transitionCoefficient_inter_coordSupport_subset_box'
        (i := i) (coordSupport := coordSupport) hcoordK hcoordTarget)

/--
Interior cover-indexed pieces have zero local bulk term from the assigned-box
support package.
-/
theorem coverIndexInteriorLocalBulk_eq_zero_of_assignedBoxFields
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.interiorCenters})
    {coordSupport : Set (Fin (n + 1) → Real)}
    (hfields : InteriorAssignedBoxCoordSupportFields P i ω coordSupport) :
    P.coverIndexLocalBulkTerm ω (Sum.inl i) = 0 := by
  rcases hfields with ⟨hbox, hbase, hcoordK, hcoordTarget⟩
  have hsupp :
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.interiorChart i.1) (C.interiorChart i.1)
            (P.coverIndexLocalizedForm ω (Sum.inl i))) ⊆
        boxInteriorSupportBox (C.interiorLower i.1) (C.interiorUpper i.1) :=
    interiorLocalizedSupportSubset_of_assignedBoxFields
      (P := P) (ω := ω) (i := i) (coordSupport := coordSupport)
      ⟨hbox, hbase, hcoordK, hcoordTarget⟩
  simpa [SupportControlledSelectedPartition.coverIndexLocalBulkTerm,
    SupportControlledSelectedPartition.coverIndexLocalizedForm] using
    ManifoldForm.localized_projectInteriorBulkIntegral_eq_zero_of_tsupport_subset_interiorBox
      (I := I) (ω := ω) (ρ := P.partition (Sum.inl i))
      (x0 := C.interiorChart i.1) (x1 := C.interiorChart i.1)
      (a := C.interiorLower i.1) (b := C.interiorUpper i.1)
      hbox hsupp

/--
Interior cover-indexed local Stokes from the assigned-box support package.
The boundary term on an interior cover index is definitionally zero.
-/
theorem coverIndexInteriorLocalBulk_eq_localBoundary_of_assignedBoxFields
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.interiorCenters})
    {coordSupport : Set (Fin (n + 1) → Real)}
    (hfields : InteriorAssignedBoxCoordSupportFields P i ω coordSupport) :
    P.coverIndexLocalBulkTerm ω (Sum.inl i) =
      P.coverIndexLocalBoundaryTerm ω (Sum.inl i) := by
  simpa [SupportControlledSelectedPartition.coverIndexLocalBoundaryTerm] using
    coverIndexInteriorLocalBulk_eq_zero_of_assignedBoxFields
      (P := P) (ω := ω) (i := i) hfields

end SupportControlledSelectedPartition

namespace SupportControlledCoverIndexedLocalStokesFields

variable {P : SupportControlledSelectedPartition C}

/--
Build the full cover-indexed local-fields package when the interior fields are
already packaged as assigned-box coordinate-support fields and the boundary
side is supplied in the boundary assigned-box package.
-/
def ofInteriorAndBoundaryAssignedBoxFields
    (interiorCoordSupport :
      {x : M // x ∈ C.interiorCenters} →
        Set (Fin (n + 1) → Real))
    (interiorAssignedFields :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        SupportControlledSelectedPartition.InteriorAssignedBoxCoordSupportFields
          P i ω (interiorCoordSupport i))
    (boundaryCoordSupport boundaryNeighborhood :
      {x : M // x ∈ C.boundaryCenters} →
        Set (Fin (n + 1) → Real))
    (boundaryAssignedFields :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        SupportControlledSelectedPartition.BoundaryAssignedBoxCoordSupportFields P i ω
          (boundaryCoordSupport i) (boundaryNeighborhood i))
    (boundaryCoordMapsToSupport :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ∀ y ∈ boundaryCoordSupport i,
          (extChartAt I (C.boundaryChart i.1)).symm y ∈ K)
    (boundaryCoordSubsetTarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryCoordSupport i ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (boundaryCoeffSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionCoefficientInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1)
            (P.partition (Sum.inr i))) (boundaryNeighborhood i))
    (boundaryFormSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionPullbackInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1) ω)
          (boundaryNeighborhood i)) :
    SupportControlledCoverIndexedLocalStokesFields P ω :=
  ofBoundaryAssignedBoxFields
    (P := P) (ω := ω)
    interiorCoordSupport
    (fun i => (interiorAssignedFields i).1)
    (fun i => (interiorAssignedFields i).2.1)
    (fun i => (interiorAssignedFields i).2.2.1)
    (fun i => (interiorAssignedFields i).2.2.2)
    boundaryCoordSupport boundaryNeighborhood boundaryAssignedFields
    boundaryCoordMapsToSupport boundaryCoordSubsetTarget
    boundaryCoeffSmooth boundaryFormSmooth

/--
Mixed cover-index local Stokes using packaged interior assigned-box fields and
the existing packaged boundary assigned-box fields.
-/
theorem localBulk_eq_localBoundary_of_interiorAndBoundaryAssignedBoxFields
    (interiorCoordSupport :
      {x : M // x ∈ C.interiorCenters} →
        Set (Fin (n + 1) → Real))
    (interiorAssignedFields :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        SupportControlledSelectedPartition.InteriorAssignedBoxCoordSupportFields
          P i ω (interiorCoordSupport i))
    (boundaryCoordSupport boundaryNeighborhood :
      {x : M // x ∈ C.boundaryCenters} →
        Set (Fin (n + 1) → Real))
    (boundaryAssignedFields :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        SupportControlledSelectedPartition.BoundaryAssignedBoxCoordSupportFields P i ω
          (boundaryCoordSupport i) (boundaryNeighborhood i))
    (boundaryCoeffSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionCoefficientInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1)
            (P.partition (Sum.inr i))) (boundaryNeighborhood i))
    (boundaryFormSmooth :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionPullbackInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1) ω)
          (boundaryNeighborhood i)) :
    ∀ j : C.CoverIndex,
      P.coverIndexLocalBulkTerm ω j =
        P.coverIndexLocalBoundaryTerm ω j := by
  intro j
  rcases j with i | i
  · exact
      SupportControlledSelectedPartition.coverIndexInteriorLocalBulk_eq_localBoundary_of_assignedBoxFields
        (P := P) (ω := ω) (i := i)
        (coordSupport := interiorCoordSupport i)
        (interiorAssignedFields i)
  · exact
      boundaryLocalBulk_eq_localBoundary_of_assignedBoxFields
        (P := P) (ω := ω)
        boundaryCoordSupport boundaryNeighborhood boundaryAssignedFields
        boundaryCoeffSmooth boundaryFormSmooth i

end SupportControlledCoverIndexedLocalStokesFields

end InteriorLocalFieldsConstructor

end Stokes

end
