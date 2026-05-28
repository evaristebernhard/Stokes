import Stokes.Global.CoverIndexedFromSupportControlledCover
import Stokes.Global.BoundarySupportControlledAssignedBox

/-!
# Constructors for cover-indexed local Stokes fields

This file is a small integration layer for the compact-support route.  The
cover-indexed global input currently asks for a
`SupportControlledCoverIndexedLocalStokesFields` package.  Boundary assigned-box
work, however, naturally produces the shorter
`BoundaryAssignedBoxCoordSupportFields` package.

The constructors below bridge those two shapes.  They do not prove new
analysis; they remove repeated field plumbing and expose the pointwise local
Stokes equality from the same assigned-box hypotheses.
-/

noncomputable section

set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section LocalFieldsConstructor

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {ω : ManifoldForm I M n}
variable {P : SupportControlledSelectedPartition C}

namespace SupportControlledCoverIndexedLocalStokesFields

/--
Build the cover-indexed local-fields package when the boundary side has
already been packaged as assigned-box coordinate-support fields.

This removes the repetitive extraction of compactness, half-space containment,
base-support, open-neighborhood, and box-neighborhood fields from every caller
that already uses `BoundaryAssignedBoxCoordSupportFields`.
-/
def ofBoundaryAssignedBoxFields
    (interiorCoordSupport :
      {x : M // x ∈ C.interiorCenters} ->
        Set (Fin (n + 1) -> Real))
    (interiorExtendedBox :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        interiorChartExtendedBox I
          (C.interiorChart i.1) (C.interiorChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inl i))
          (C.interiorLower i.1) (C.interiorUpper i.1))
    (interiorBaseSupport :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.interiorChart i.1) (C.interiorChart i.1) ω) ⊆
          interiorCoordSupport i)
    (interiorCoordMapsToSupport :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        ∀ y ∈ interiorCoordSupport i,
          (extChartAt I (C.interiorChart i.1)).symm y ∈ K)
    (interiorCoordSubsetTarget :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        interiorCoordSupport i ⊆
          (extChartAt I (C.interiorChart i.1)).target)
    (boundaryCoordSupport boundaryNeighborhood :
      {x : M // x ∈ C.boundaryCenters} ->
        Set (Fin (n + 1) -> Real))
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
    SupportControlledCoverIndexedLocalStokesFields P ω where
  interiorCoordSupport := interiorCoordSupport
  interiorExtendedBox := interiorExtendedBox
  interiorBaseSupport := interiorBaseSupport
  interiorCoordMapsToSupport := interiorCoordMapsToSupport
  interiorCoordSubsetTarget := interiorCoordSubsetTarget
  boundaryCoordSupport := boundaryCoordSupport
  boundaryNeighborhood := boundaryNeighborhood
  boundaryCoordCompact := by
    intro i
    rcases boundaryAssignedFields i with
      ⟨hcompact, _hhalf, _hbase, _ha0, _hle, _hcoeff, _hdomain,
        _hopen, _hbox⟩
    exact hcompact
  boundaryCoordSubsetHalfSpace := by
    intro i
    rcases boundaryAssignedFields i with
      ⟨_hcompact, hhalf, _hbase, _ha0, _hle, _hcoeff, _hdomain,
        _hopen, _hbox⟩
    exact hhalf
  boundaryBaseSupport := by
    intro i
    rcases boundaryAssignedFields i with
      ⟨_hcompact, _hhalf, hbase, _ha0, _hle, _hcoeff, _hdomain,
        _hopen, _hbox⟩
    exact hbase
  boundaryCoordMapsToSupport := boundaryCoordMapsToSupport
  boundaryCoordSubsetTarget := boundaryCoordSubsetTarget
  boundaryNeighborhood_open := by
    intro i
    rcases boundaryAssignedFields i with
      ⟨_hcompact, _hhalf, _hbase, _ha0, _hle, _hcoeff, _hdomain,
        hopen, _hbox⟩
    exact hopen
  boundary_Icc_subset_neighborhood := by
    intro i
    rcases boundaryAssignedFields i with
      ⟨_hcompact, _hhalf, _hbase, _ha0, _hle, _hcoeff, _hdomain,
        _hopen, hbox⟩
    exact hbox
  boundaryCoeffSmooth := boundaryCoeffSmooth
  boundaryFormSmooth := boundaryFormSmooth

/--
Pointwise boundary local Stokes directly from assigned-box coordinate-support
fields.  This is the boundary half of `localBulk_eq_localBoundary`, stated
without first constructing the large local-fields package.
-/
theorem boundaryLocalBulk_eq_localBoundary_of_assignedBoxFields
    (boundaryCoordSupport boundaryNeighborhood :
      {x : M // x ∈ C.boundaryCenters} ->
        Set (Fin (n + 1) -> Real))
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
          (boundaryNeighborhood i))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    P.coverIndexLocalBulkTerm ω (Sum.inr i) =
      P.coverIndexLocalBoundaryTerm ω (Sum.inr i) := by
  rcases boundaryAssignedFields i with
    ⟨hcompact, hhalf, hbase, ha0, hle, hcoeff, hdomain, hopen, hbox⟩
  simpa [SupportControlledSelectedPartition.coverIndexLocalBulkTerm,
    SupportControlledSelectedPartition.coverIndexLocalBoundaryTerm,
    SupportControlledSelectedPartition.coverIndexLocalizedForm] using
    boundaryAssignedBox_projectLocalStokes_of_contDiffOn_infty
      (I := I) (omega := ω)
      (x0 := C.boundaryChart i.1) (x1 := C.boundaryChart i.1)
      (rho := P.partition (Sum.inr i))
      hcompact hhalf hbase ha0 hle hcoeff hdomain hopen hbox
      (boundaryCoeffSmooth i) (boundaryFormSmooth i)

/--
Pointwise mixed local Stokes directly from interior assigned-box data and
boundary assigned-box coordinate-support fields.

Compared with requiring a full `SupportControlledCoverIndexedLocalStokesFields`
value, this theorem lets callers provide the boundary side in the compact
assigned-box package shape already produced by
`BoundarySupportControlledAssignedBox`.
-/
theorem localBulk_eq_localBoundary_of_assignedBoxFields
    (interiorCoordSupport :
      {x : M // x ∈ C.interiorCenters} ->
        Set (Fin (n + 1) -> Real))
    (interiorExtendedBox :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        interiorChartExtendedBox I
          (C.interiorChart i.1) (C.interiorChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inl i))
          (C.interiorLower i.1) (C.interiorUpper i.1))
    (interiorBaseSupport :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.interiorChart i.1) (C.interiorChart i.1) ω) ⊆
          interiorCoordSupport i)
    (interiorCoordMapsToSupport :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        ∀ y ∈ interiorCoordSupport i,
          (extChartAt I (C.interiorChart i.1)).symm y ∈ K)
    (interiorCoordSubsetTarget :
      ∀ i : {x : M // x ∈ C.interiorCenters},
        interiorCoordSupport i ⊆
          (extChartAt I (C.interiorChart i.1)).target)
    (boundaryCoordSupport boundaryNeighborhood :
      {x : M // x ∈ C.boundaryCenters} ->
        Set (Fin (n + 1) -> Real))
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
  · have hsupp :
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.interiorChart i.1) (C.interiorChart i.1)
              (P.coverIndexLocalizedForm ω (Sum.inl i))) ⊆
          boxInteriorSupportBox
            (C.interiorLower i.1) (C.interiorUpper i.1) :=
      ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_interiorBox_of_coordSupport
        (I := I)
        (x0 := C.interiorChart i.1) (x1 := C.interiorChart i.1)
        (ρ := P.partition (Sum.inl i)) (ω := ω)
        (a := C.interiorLower i.1) (b := C.interiorUpper i.1)
        (interiorBaseSupport i)
        (P.interior_transitionCoefficient_inter_coordSupport_subset_box'
          (i := i) (coordSupport := interiorCoordSupport i)
          (interiorCoordMapsToSupport i) (interiorCoordSubsetTarget i))
    have hbulk :
        P.coverIndexLocalBulkTerm ω (Sum.inl i) = 0 := by
      simpa [SupportControlledSelectedPartition.coverIndexLocalBulkTerm,
        SupportControlledSelectedPartition.coverIndexLocalizedForm] using
        ManifoldForm.localized_projectInteriorBulkIntegral_eq_zero_of_tsupport_subset_interiorBox
          (I := I) (ω := ω) (ρ := P.partition (Sum.inl i))
          (x0 := C.interiorChart i.1) (x1 := C.interiorChart i.1)
          (a := C.interiorLower i.1) (b := C.interiorUpper i.1)
          (interiorExtendedBox i) hsupp
    simpa [SupportControlledSelectedPartition.coverIndexLocalBoundaryTerm] using hbulk
  · exact
      boundaryLocalBulk_eq_localBoundary_of_assignedBoxFields
        (P := P) (ω := ω)
        boundaryCoordSupport boundaryNeighborhood boundaryAssignedFields
        boundaryCoeffSmooth boundaryFormSmooth i

end SupportControlledCoverIndexedLocalStokesFields

end LocalFieldsConstructor

end Stokes

end
