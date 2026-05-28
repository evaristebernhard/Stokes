import Stokes.Global.SupportControlledSelectedPartition

/-!
# Boundary assigned boxes from support-controlled selected partitions

This file is the boundary analogue of the selected support-control handoff:
it turns the manifold-side support control produced by
`SupportControlledSelectedPartition` into the coordinate-side half-space box
support consumed by `BoundaryAssignedBoxSupport`.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section BoundarySupportControlledAssignedBox

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}

namespace SupportControlledSelectedPartition

/--
Boundary coefficient support bridge for a support-controlled selected
partition.

The support-controlled partition gives support control on the manifold side.
The three chart-coordinate hypotheses are the remaining local bookkeeping:
the coordinate carrier maps back into the compact support set, lies in the
boundary chart target, and the transition coefficient's coordinate support
maps back into the topological support of the selected partition coefficient.
-/
theorem boundary_coefficient_tsupport_subset_halfSpaceBox_of_supportControlledPartition
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters})
    {coordSupport : Set (Fin (n + 1) → Real)}
    (hcoordK :
      ∀ y ∈ coordSupport,
        (extChartAt I (C.boundaryChart i.1)).symm y ∈ K)
    (hcoordTarget :
      coordSupport ⊆ (extChartAt I (C.boundaryChart i.1)).target)
    (htransitionCoeffSupport :
      ∀ y,
        y ∈ tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1)
              (P.partition (Sum.inr i))) →
          (extChartAt I (C.boundaryChart i.1)).symm y ∈
            tsupport (P.partition (Sum.inr i))) :
    tsupport
          (ManifoldForm.transitionCoefficientInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1)
            (P.partition (Sum.inr i))) ∩
        coordSupport ⊆
      halfSpaceSupportBox (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  exact
    P.boundary_transitionCoefficient_inter_coordSupport_subset_box
      i hcoordK hcoordTarget htransitionCoeffSupport

/--
The concrete boundary assigned-box input fields obtained from a
support-controlled selected partition and a boundary cover index.

This proposition is deliberately just the field list consumed by
`exists_boundaryAssignedBoxData_localStokes_of_coordSupport` before the final
smoothness neighborhood hypotheses are supplied.
-/
abbrev BoundaryAssignedBoxCoordSupportFields
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters})
    (ω : ManifoldForm I M n)
    (coordSupport U : Set (Fin (n + 1) → Real)) : Prop :=
  IsCompact coordSupport ∧
    coordSupport ⊆ upperHalfSpace n ∧
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1) ω) ⊆
        coordSupport ∧
        C.boundaryLower i.1 0 = 0 ∧
          C.boundaryLower i.1 ≤ C.boundaryUpper i.1 ∧
            tsupport
                (ManifoldForm.transitionCoefficientInChart I
                  (C.boundaryChart i.1) (C.boundaryChart i.1)
                  (P.partition (Sum.inr i))) ∩
                coordSupport ⊆
              halfSpaceSupportBox
                (C.boundaryLower i.1) (C.boundaryUpper i.1) ∧
              Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
                boundaryChartDomain I (C.boundaryChart i.1) (C.boundaryChart i.1) ∧
                IsOpen U ∧
                  Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆ U

/--
Package the boundary assigned-box fields supplied by the selected cover and
the support-controlled selected partition.

The selected cover contributes the lower-zero convention, order, and boundary
chart-domain containment; the partition contributes the half-space coefficient
support after the chart-coordinate bridge hypotheses are supplied.
-/
theorem boundary_assignedBox_fields_of_supportControlledPartition
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters})
    {ω : ManifoldForm I M n}
    {coordSupport U : Set (Fin (n + 1) → Real)}
    (hKcoord : IsCompact coordSupport)
    (hhalf : coordSupport ⊆ upperHalfSpace n)
    (hbase :
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1) ω) ⊆
        coordSupport)
    (hcoordK :
      ∀ y ∈ coordSupport,
        (extChartAt I (C.boundaryChart i.1)).symm y ∈ K)
    (hcoordTarget :
      coordSupport ⊆ (extChartAt I (C.boundaryChart i.1)).target)
    (htransitionCoeffSupport :
      ∀ y,
        y ∈ tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1)
              (P.partition (Sum.inr i))) →
          (extChartAt I (C.boundaryChart i.1)).symm y ∈
            tsupport (P.partition (Sum.inr i)))
    (hU : IsOpen U)
    (hUbox :
      Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆ U) :
    BoundaryAssignedBoxCoordSupportFields P i ω coordSupport U := by
  refine
    ⟨hKcoord, hhalf, hbase, C.boundary_lower_zero i.1 i.2,
      C.boundary_le i.1 i.2, ?_, C.boundary_Icc_subset_domain i.1 i.2,
      hU, hUbox⟩
  exact
    P.boundary_coefficient_tsupport_subset_halfSpaceBox_of_supportControlledPartition
      i hcoordK hcoordTarget htransitionCoeffSupport

/--
Direct local-Stokes handoff from a support-controlled selected boundary
coefficient to the existing boundary assigned-box constructor.
-/
theorem exists_boundaryAssignedBoxData_localStokes_of_supportControlledPartition
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters})
    {ω : ManifoldForm I M n}
    {coordSupport U : Set (Fin (n + 1) → Real)}
    (hfields : BoundaryAssignedBoxCoordSupportFields P i ω coordSupport U)
    (hρU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.partition (Sum.inr i))) U)
    (hωU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1) ω) U) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (ManifoldForm.localizedForm I (P.partition (Sum.inr i)) ω)) ⊆
        halfSpaceSupportBox
          (C.boundaryLower i.1) (C.boundaryUpper i.1) ∧
      ∃ D :
          BoundaryCompactBoxSelectionData I
            (C.boundaryChart i.1) (C.boundaryChart i.1)
            (ManifoldForm.localizedForm I (P.partition (Sum.inr i)) ω),
        D.K =
            tsupport
              (ManifoldForm.transitionPullbackInChart I
                (C.boundaryChart i.1) (C.boundaryChart i.1)
                (ManifoldForm.localizedForm I (P.partition (Sum.inr i)) ω)) ∧
          D.a = C.boundaryLower i.1 ∧
            D.b = C.boundaryUpper i.1 ∧
              halfSpaceLocalBulkIntegral
                  (ManifoldForm.transitionPullbackInChart I
                    (C.boundaryChart i.1) (C.boundaryChart i.1)
                    (ManifoldForm.localizedForm I
                      (P.partition (Sum.inr i)) ω)) D.a D.b =
                outwardFirstBoundaryChartIntegral I
                  (C.boundaryChart i.1) (C.boundaryChart i.1)
                  (ManifoldForm.localizedForm I (P.partition (Sum.inr i)) ω)
                  D.a D.b := by
  rcases hfields with
    ⟨hKcoord, hhalf, hbase, ha0, hle, hcoeff, hdomain, hU, hUbox⟩
  exact
    exists_boundaryAssignedBoxData_localStokes_of_contDiffOn
      (I := I) (x0 := C.boundaryChart i.1) (x1 := C.boundaryChart i.1)
      (ρ := P.partition (Sum.inr i)) (ω := ω)
      hKcoord hhalf hbase ha0 hle hcoeff hdomain hU hUbox hρU hωU

/--
One-shot version: build the assigned-box fields from the selected partition
and immediately feed them to the boundary local-Stokes constructor.
-/
theorem exists_boundaryAssignedBoxData_localStokes_of_supportControlledPartition'
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters})
    {ω : ManifoldForm I M n}
    {coordSupport U : Set (Fin (n + 1) → Real)}
    (hKcoord : IsCompact coordSupport)
    (hhalf : coordSupport ⊆ upperHalfSpace n)
    (hbase :
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1) ω) ⊆
        coordSupport)
    (hcoordK :
      ∀ y ∈ coordSupport,
        (extChartAt I (C.boundaryChart i.1)).symm y ∈ K)
    (hcoordTarget :
      coordSupport ⊆ (extChartAt I (C.boundaryChart i.1)).target)
    (htransitionCoeffSupport :
      ∀ y,
        y ∈ tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1)
              (P.partition (Sum.inr i))) →
          (extChartAt I (C.boundaryChart i.1)).symm y ∈
            tsupport (P.partition (Sum.inr i)))
    (hU : IsOpen U)
    (hUbox :
      Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆ U)
    (hρU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.partition (Sum.inr i))) U)
    (hωU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1) ω) U) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (ManifoldForm.localizedForm I (P.partition (Sum.inr i)) ω)) ⊆
        halfSpaceSupportBox
          (C.boundaryLower i.1) (C.boundaryUpper i.1) ∧
      ∃ D :
          BoundaryCompactBoxSelectionData I
            (C.boundaryChart i.1) (C.boundaryChart i.1)
            (ManifoldForm.localizedForm I (P.partition (Sum.inr i)) ω),
        D.K =
            tsupport
              (ManifoldForm.transitionPullbackInChart I
                (C.boundaryChart i.1) (C.boundaryChart i.1)
                (ManifoldForm.localizedForm I (P.partition (Sum.inr i)) ω)) ∧
          D.a = C.boundaryLower i.1 ∧
            D.b = C.boundaryUpper i.1 ∧
              halfSpaceLocalBulkIntegral
                  (ManifoldForm.transitionPullbackInChart I
                    (C.boundaryChart i.1) (C.boundaryChart i.1)
                    (ManifoldForm.localizedForm I
                      (P.partition (Sum.inr i)) ω)) D.a D.b =
                outwardFirstBoundaryChartIntegral I
                  (C.boundaryChart i.1) (C.boundaryChart i.1)
                  (ManifoldForm.localizedForm I (P.partition (Sum.inr i)) ω)
                  D.a D.b := by
  exact
    P.exists_boundaryAssignedBoxData_localStokes_of_supportControlledPartition
      i
      (P.boundary_assignedBox_fields_of_supportControlledPartition
        i hKcoord hhalf hbase hcoordK hcoordTarget
        htransitionCoeffSupport hU hUbox)
      hρU hωU

end SupportControlledSelectedPartition

end BoundarySupportControlledAssignedBox

end Stokes

end
