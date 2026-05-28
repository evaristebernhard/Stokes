import Stokes.Global.SupportControlledSelectedPartition
import Stokes.Global.CompactSupportChartCoverSelection
import Stokes.Global.PartitionCompactSupport
import Stokes.Global.CoverIndexedZeroCompactBoxPartitionRefinement

/-!
# Active carriers for selected boundary partition coefficients

This file isolates the real manifold-side carrier attached to one selected
boundary chart coefficient:

`tsupport (P.partition (Sum.inr i)) ∩ K`.

The carrier is compact when `K` is compact.  Its selected boundary chart image
lies in the upper half-space, because the selected cover subordination places
the carrier in the assigned boundary half-space box.  The final lemmas record
the useful zero/non-contribution statement: on `K`, the boundary coefficient
vanishes outside its active carrier.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryActiveCarrier

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}

namespace SupportControlledSelectedPartition

/-- The manifold-side active carrier of a selected boundary partition term. -/
def boundaryActiveCarrier
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters}) : Set M :=
  tsupport (P.partition (Sum.inr i)) ∩ K

/-- The coordinate image of a selected boundary active carrier. -/
def boundaryActiveCoordCarrier
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    Set (Fin (n + 1) → Real) :=
  chartCoordinateImage I (C.boundaryChart i.1) (P.boundaryActiveCarrier i)

@[simp]
theorem mem_boundaryActiveCarrier
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters}) {x : M} :
    x ∈ P.boundaryActiveCarrier i ↔
      x ∈ tsupport (P.partition (Sum.inr i)) ∧ x ∈ K := by
  rfl

theorem boundaryActiveCarrier_subset_tsupport
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    P.boundaryActiveCarrier i ⊆ tsupport (P.partition (Sum.inr i)) :=
  inter_subset_left

theorem boundaryActiveCarrier_subset_K
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    P.boundaryActiveCarrier i ⊆ K :=
  inter_subset_right

/-- Boundary active carriers are compact closed pieces of the compact support set. -/
theorem isCompact_boundaryActiveCarrier
    (P : SupportControlledSelectedPartition C)
    (hK : IsCompact K)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    IsCompact (P.boundaryActiveCarrier i) :=
  hK.inter_left (isClosed_tsupport (P.partition (Sum.inr i)))

/-- The active carrier is contained in the selected boundary chart box neighborhood. -/
theorem boundaryActiveCarrier_subset_assigned
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    P.boundaryActiveCarrier i ⊆
      boundaryChartBoxNeighborhood I (C.boundaryChart i.1)
        (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  P.boundary_tsupport_inter_subset_assigned i

/-- The active carrier lies in the source of its selected boundary chart. -/
theorem boundaryActiveCarrier_subset_chart_source
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    P.boundaryActiveCarrier i ⊆
      (extChartAt I (C.boundaryChart i.1)).source := by
  intro x hx
  exact (P.boundaryActiveCarrier_subset_assigned i hx).1

/-- The selected boundary chart image of the active carrier lies in its half-space box. -/
theorem boundaryActiveCarrier_chart_mem_halfSpaceSupportBox
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters}) {x : M}
    (hx : x ∈ P.boundaryActiveCarrier i) :
    (extChartAt I (C.boundaryChart i.1)) x ∈
      halfSpaceSupportBox (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  (P.boundaryActiveCarrier_subset_assigned i hx).2

/-- The selected boundary chart image of the active carrier lies in the upper half-space. -/
theorem boundaryActiveCarrier_chart_mem_upperHalfSpace
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters}) {x : M}
    (hx : x ∈ P.boundaryActiveCarrier i) :
    (extChartAt I (C.boundaryChart i.1)) x ∈ upperHalfSpace n := by
  have hbox :=
    P.boundaryActiveCarrier_chart_mem_halfSpaceSupportBox (I := I) i hx
  have h0 : C.boundaryLower i.1 0 = 0 :=
    C.boundary_lower_zero i.1 i.2
  simpa [upperHalfSpace, h0] using hbox.1

/-- Coordinate-image form of half-space-box containment for the active carrier. -/
theorem boundaryActiveCoordCarrier_subset_halfSpaceSupportBox
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    P.boundaryActiveCoordCarrier i ⊆
      halfSpaceSupportBox (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  rintro y ⟨x, hx, rfl⟩
  exact P.boundaryActiveCarrier_chart_mem_halfSpaceSupportBox (I := I) i hx

/-- Coordinate-image form of upper-half-space containment for the active carrier. -/
theorem boundaryActiveCoordCarrier_subset_upperHalfSpace
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    P.boundaryActiveCoordCarrier i ⊆ upperHalfSpace n := by
  intro y hy
  have hbox :
      y ∈ halfSpaceSupportBox
        (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
    P.boundaryActiveCoordCarrier_subset_halfSpaceSupportBox (I := I) i hy
  have h0 : C.boundaryLower i.1 0 = 0 :=
    C.boundary_lower_zero i.1 i.2
  simpa [upperHalfSpace, h0] using hbox.1

/-- Compactness of the coordinate image of the active carrier. -/
theorem isCompact_boundaryActiveCoordCarrier
    (P : SupportControlledSelectedPartition C)
    (hK : IsCompact K)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    IsCompact (P.boundaryActiveCoordCarrier i) :=
  isCompact_chartCoordinateImage_of_subset_source
    (I := I) (x := C.boundaryChart i.1)
    (K := P.boundaryActiveCarrier i)
    (P.isCompact_boundaryActiveCarrier hK i)
    (P.boundaryActiveCarrier_subset_chart_source i)

/--
If an arbitrary coordinate carrier maps back into the boundary active carrier,
then it lies in the assigned half-space box.  This is the honest form needed by
later refined carriers: the statement requires both inverse membership in the
active carrier and target membership for the chart inverse.
-/
theorem coordSupport_subset_halfSpaceSupportBox_of_symm_mem_boundaryActiveCarrier
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters})
    {coordSupport : Set (Fin (n + 1) → Real)}
    (hcoordActive :
      ∀ y ∈ coordSupport,
        (extChartAt I (C.boundaryChart i.1)).symm y ∈
          P.boundaryActiveCarrier i)
    (hcoordTarget :
      coordSupport ⊆ (extChartAt I (C.boundaryChart i.1)).target) :
    coordSupport ⊆
      halfSpaceSupportBox (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  intro y hy
  have hbox :
      (extChartAt I (C.boundaryChart i.1))
          ((extChartAt I (C.boundaryChart i.1)).symm y) ∈
        halfSpaceSupportBox (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
    P.boundaryActiveCarrier_chart_mem_halfSpaceSupportBox
      (I := I) i (hcoordActive y hy)
  rwa [(extChartAt I (C.boundaryChart i.1)).right_inv (hcoordTarget hy)] at hbox

/-- Upper-half-space consequence of the honest inverse-carrier criterion. -/
theorem coordSupport_subset_upperHalfSpace_of_symm_mem_boundaryActiveCarrier
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters})
    {coordSupport : Set (Fin (n + 1) → Real)}
    (hcoordActive :
      ∀ y ∈ coordSupport,
        (extChartAt I (C.boundaryChart i.1)).symm y ∈
          P.boundaryActiveCarrier i)
    (hcoordTarget :
      coordSupport ⊆ (extChartAt I (C.boundaryChart i.1)).target) :
    coordSupport ⊆ upperHalfSpace n := by
  intro y hy
  have hbox :
      y ∈ halfSpaceSupportBox
        (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
    P.coordSupport_subset_halfSpaceSupportBox_of_symm_mem_boundaryActiveCarrier
      (I := I) i hcoordActive hcoordTarget hy
  have h0 : C.boundaryLower i.1 0 = 0 :=
    C.boundary_lower_zero i.1 i.2
  simpa [upperHalfSpace, h0] using hbox.1

/-- On `K`, not being in the active carrier is exactly not being in the coefficient `tsupport`. -/
theorem not_mem_tsupport_of_mem_K_not_mem_boundaryActiveCarrier
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters})
    {x : M} (hxK : x ∈ K)
    (hxnot : x ∉ P.boundaryActiveCarrier i) :
    x ∉ tsupport (P.partition (Sum.inr i)) := by
  intro hxt
  exact hxnot ⟨hxt, hxK⟩

/-- On `K`, a boundary partition coefficient vanishes outside its active carrier. -/
theorem partition_eq_zero_of_mem_K_not_mem_boundaryActiveCarrier
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters})
    {x : M} (hxK : x ∈ K)
    (hxnot : x ∉ P.boundaryActiveCarrier i) :
    P.partition (Sum.inr i) x = 0 := by
  by_contra hne
  exact
    P.not_mem_tsupport_of_mem_K_not_mem_boundaryActiveCarrier i hxK hxnot
      (subset_tsupport (P.partition (Sum.inr i)) hne)

/-- Equivalent nonzero form: on `K`, nonzero boundary coefficients live in the active carrier. -/
theorem mem_boundaryActiveCarrier_of_mem_K_partition_ne_zero
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters})
    {x : M} (hxK : x ∈ K)
    (hxne : P.partition (Sum.inr i) x ≠ 0) :
    x ∈ P.boundaryActiveCarrier i :=
  ⟨subset_tsupport (P.partition (Sum.inr i)) hxne, hxK⟩

/-- On `K`, the algebraic support of a boundary coefficient is contained in its active carrier. -/
theorem support_inter_K_subset_boundaryActiveCarrier
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    Function.support (P.partition (Sum.inr i)) ∩ K ⊆
      P.boundaryActiveCarrier i := by
  rintro x ⟨hx, hxK⟩
  exact P.mem_boundaryActiveCarrier_of_mem_K_partition_ne_zero i hxK hx

end SupportControlledSelectedPartition

end BoundaryActiveCarrier

end Stokes

end
