import Stokes.Global.CoverIndexedMeasureFields
import Stokes.Global.CoverIndexedPartitionCore
import Stokes.Global.CoverIndexedBulkReconstruction
import Stokes.Global.CoverIndexedBoundaryReconstruction
import Stokes.Global.CoverIndexedLocalStokes
import Stokes.Global.TransitionCoefficientSupportBridge

/-!
# Cover-indexed inputs from support-controlled chart-box covers

This file is the handoff from the support-controlled compact chart-box cover
route to the cover-indexed core.  It deliberately avoids the older
`SelectedBoxPartitionOfUnity` API: the finite index type is the mixed selected
cover index `C.CoverIndex`.

The main layers are:

* `SupportControlledSelectedPartition.toCoverIndexedLocalData`, exposing the
  active cover indices, partition coefficients, assigned charts, and assigned
  coordinate boxes;
* cover-indexed local bulk/boundary term families attached directly to the
  selected chart boxes;
* `SupportControlledCoverIndexedMeasureInput`, a natural input package whose
  fields are a chart-box cover, a support-controlled partition, local
  smoothness/support data, and scalar measure reconstruction data.  It projects
  to `CoverIndexedMeasureFields`, hence to `CoverIndexedStokesSums`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section LocalProjection

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}

/--
The cover-indexed local data exposed by a support-controlled selected
partition.  The active set is finite, and the chart/box assignments are the
ones carried by the selected compact-support chart-box cover.
-/
structure SupportControlledCoverIndexedLocalData
    (C : CompactSupportChartCoverSelection I K) where
  /-- The active finite cover indices. -/
  active : Finset C.CoverIndex
  /-- Partition coefficients indexed by cover pieces. -/
  partition : C.CoverIndex → M → Real
  /-- The chart assigned to each cover piece. -/
  assignedChart : C.CoverIndex → M
  /-- The lower coordinate corner assigned to each cover piece. -/
  assignedLower : C.CoverIndex → Fin (n + 1) → Real
  /-- The upper coordinate corner assigned to each cover piece. -/
  assignedUpper : C.CoverIndex → Fin (n + 1) → Real
  /-- The assigned coordinate support box. -/
  assignedCoordinateBox : C.CoverIndex → Set (Fin (n + 1) → Real)
  /-- The assigned manifold-side cover set. -/
  assignedCoverSet : C.CoverIndex → Set M
  /-- The partition sums to one on the controlled support set. -/
  sum_eq_one :
    ∀ x ∈ K, (∑ j ∈ active, partition j x) = 1
  /-- Active coefficients are supported, on `K`, in their assigned cover sets. -/
  tsupport_inter_subset_assigned :
    ∀ j, j ∈ active → tsupport (partition j) ∩ K ⊆ assignedCoverSet j

namespace SupportControlledSelectedPartition

variable {C : CompactSupportChartCoverSelection I K}

/--
Projection from the support-controlled selected partition to the finite
cover-indexed local data consumed by the cover-indexed core.
-/
def toCoverIndexedLocalData
    (P : SupportControlledSelectedPartition C) :
    SupportControlledCoverIndexedLocalData C where
  active := Finset.univ
  partition := fun j x => P.partition j x
  assignedChart := C.assignedChart
  assignedLower := C.assignedLower
  assignedUpper := C.assignedUpper
  assignedCoordinateBox := C.assignedCoordinateBox
  assignedCoverSet := C.assignedCoverSet
  sum_eq_one := by
    classical
    intro x hx
    simpa using P.finite_sum_eq_one x hx
  tsupport_inter_subset_assigned := by
    intro j _hj
    exact P.tsupport_inter_subset_assigned j

@[simp]
theorem toCoverIndexedLocalData_active
    (P : SupportControlledSelectedPartition C) :
    P.toCoverIndexedLocalData.active = Finset.univ := rfl

@[simp]
theorem toCoverIndexedLocalData_partition
    (P : SupportControlledSelectedPartition C) (j : C.CoverIndex) (x : M) :
    P.toCoverIndexedLocalData.partition j x = P.partition j x := rfl

@[simp]
theorem toCoverIndexedLocalData_assignedChart
    (P : SupportControlledSelectedPartition C) :
    P.toCoverIndexedLocalData.assignedChart = C.assignedChart := rfl

@[simp]
theorem toCoverIndexedLocalData_assignedCoordinateBox
    (P : SupportControlledSelectedPartition C) :
    P.toCoverIndexedLocalData.assignedCoordinateBox =
      C.assignedCoordinateBox := rfl

end SupportControlledSelectedPartition

end LocalProjection

section LocalTerms

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}

namespace SupportControlledSelectedPartition

/-- The localized form attached to one selected cover index. -/
def coverIndexLocalizedForm
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) (j : C.CoverIndex) :
    ManifoldForm I M n :=
  ManifoldForm.localizedForm I (P.partition j) ω

/--
The cover-indexed local bulk term.  Interior selected boxes use the interior
project-local integral; boundary selected boxes use the half-space
project-local integral.
-/
def coverIndexLocalBulkTerm
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) : C.CoverIndex → Real
  | Sum.inl i =>
      projectInteriorBulkIntegral I
        (C.interiorChart i.1) (C.interiorChart i.1)
        (P.coverIndexLocalizedForm ω (Sum.inl i))
        (C.interiorLower i.1) (C.interiorUpper i.1)
  | Sum.inr i =>
      projectLocalBulkIntegral I
        (C.boundaryChart i.1) (C.boundaryChart i.1)
        (P.coverIndexLocalizedForm ω (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1)

/--
The cover-indexed true-boundary term.  Interior chart boxes contribute no true
boundary term after assigned-box support kills their artificial boundary
faces; boundary chart boxes use the outward-first project-local boundary
integral.
-/
def coverIndexLocalBoundaryTerm
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) : C.CoverIndex → Real
  | Sum.inl _ => 0
  | Sum.inr i =>
      projectLocalBoundaryIntegral I
        (C.boundaryChart i.1) (C.boundaryChart i.1)
        (P.coverIndexLocalizedForm ω (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1)

@[simp]
theorem coverIndexLocalBoundaryTerm_inl
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.interiorCenters}) :
    P.coverIndexLocalBoundaryTerm ω (Sum.inl i) = 0 := rfl

@[simp]
theorem coverIndexLocalBulkTerm_inr
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    P.coverIndexLocalBulkTerm ω (Sum.inr i) =
      projectLocalBulkIntegral I
        (C.boundaryChart i.1) (C.boundaryChart i.1)
        (P.coverIndexLocalizedForm ω (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1) := rfl

@[simp]
theorem coverIndexLocalBoundaryTerm_inr
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    P.coverIndexLocalBoundaryTerm ω (Sum.inr i) =
      projectLocalBoundaryIntegral I
        (C.boundaryChart i.1) (C.boundaryChart i.1)
        (P.coverIndexLocalizedForm ω (Sum.inr i))
        (C.boundaryLower i.1) (C.boundaryUpper i.1) := rfl

end SupportControlledSelectedPartition

/--
Local smoothness and support data for the cover-indexed local-Stokes step.

The support-controlled partition supplies the coefficient support in the
assigned chart boxes; these fields record the remaining local analytic inputs:
coordinate carriers for the base representative, local extended-box/smoothness
facts, and boundary half-space carrier hypotheses.
-/
structure SupportControlledCoverIndexedLocalStokesFields
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) where
  /-- Coordinate support carriers for interior selected cover pieces. -/
  interiorCoordSupport :
    {x : M // x ∈ C.interiorCenters} →
      Set (Fin (n + 1) → Real)
  /-- Interior local box geometry for localized pieces. -/
  interiorExtendedBox :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      interiorChartExtendedBox I
        (C.interiorChart i.1) (C.interiorChart i.1)
        (P.coverIndexLocalizedForm ω (Sum.inl i))
        (C.interiorLower i.1) (C.interiorUpper i.1)
  /-- Base representatives are supported in the chosen interior carriers. -/
  interiorBaseSupport :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.interiorChart i.1) (C.interiorChart i.1) ω) ⊆
        interiorCoordSupport i
  /-- Interior coordinate carriers map back into the compact support set. -/
  interiorCoordMapsToSupport :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      ∀ y ∈ interiorCoordSupport i,
        (extChartAt I (C.interiorChart i.1)).symm y ∈ K
  /-- Interior coordinate carriers lie in the selected chart target. -/
  interiorCoordSubsetTarget :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      interiorCoordSupport i ⊆
        (extChartAt I (C.interiorChart i.1)).target
  /-- Coordinate support carriers for boundary selected cover pieces. -/
  boundaryCoordSupport :
    {x : M // x ∈ C.boundaryCenters} →
      Set (Fin (n + 1) → Real)
  /-- Smoothness neighborhoods for boundary selected cover pieces. -/
  boundaryNeighborhood :
    {x : M // x ∈ C.boundaryCenters} →
      Set (Fin (n + 1) → Real)
  /-- Boundary carriers are compact. -/
  boundaryCoordCompact :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      IsCompact (boundaryCoordSupport i)
  /-- Boundary carriers lie in the upper half-space. -/
  boundaryCoordSubsetHalfSpace :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryCoordSupport i ⊆ upperHalfSpace n
  /-- Base representatives are supported in the chosen boundary carriers. -/
  boundaryBaseSupport :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1) ω) ⊆
        boundaryCoordSupport i
  /-- Boundary coordinate carriers map back into the compact support set. -/
  boundaryCoordMapsToSupport :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      ∀ y ∈ boundaryCoordSupport i,
        (extChartAt I (C.boundaryChart i.1)).symm y ∈ K
  /-- Boundary coordinate carriers lie in the selected chart target. -/
  boundaryCoordSubsetTarget :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryCoordSupport i ⊆
        (extChartAt I (C.boundaryChart i.1)).target
  /-- Boundary smoothness neighborhoods are open. -/
  boundaryNeighborhood_open :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      IsOpen (boundaryNeighborhood i)
  /-- Boundary selected boxes are contained in their smoothness neighborhoods. -/
  boundary_Icc_subset_neighborhood :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
        boundaryNeighborhood i
  /-- Boundary partition coefficients are smooth on the chosen neighborhoods. -/
  boundaryCoeffSmooth :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionCoefficientInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.partition (Sum.inr i))) (boundaryNeighborhood i)
  /-- Boundary base representatives are smooth on the chosen neighborhoods. -/
  boundaryFormSmooth :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1) ω)
        (boundaryNeighborhood i)

namespace SupportControlledCoverIndexedLocalStokesFields

variable {P : SupportControlledSelectedPartition C}

/-- Interior localized representatives are strictly supported in their assigned boxes. -/
theorem interiorLocalizedSupportSubset
    (D : SupportControlledCoverIndexedLocalStokesFields P ω)
    (i : {x : M // x ∈ C.interiorCenters}) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (C.interiorChart i.1) (C.interiorChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inl i))) ⊆
      boxInteriorSupportBox (C.interiorLower i.1) (C.interiorUpper i.1) := by
  exact
    ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_interiorBox_of_coordSupport
      (I := I)
      (x0 := C.interiorChart i.1) (x1 := C.interiorChart i.1)
      (ρ := P.partition (Sum.inl i)) (ω := ω)
      (a := C.interiorLower i.1) (b := C.interiorUpper i.1)
      (D.interiorBaseSupport i)
      (P.interior_transitionCoefficient_inter_coordSupport_subset_box'
        (i := i) (coordSupport := D.interiorCoordSupport i)
        (D.interiorCoordMapsToSupport i)
        (D.interiorCoordSubsetTarget i))

/-- Interior selected cover pieces have zero local bulk term. -/
theorem interiorLocalBulk_eq_zero
    (D : SupportControlledCoverIndexedLocalStokesFields P ω)
    (i : {x : M // x ∈ C.interiorCenters}) :
    P.coverIndexLocalBulkTerm ω (Sum.inl i) = 0 := by
  simpa [SupportControlledSelectedPartition.coverIndexLocalBulkTerm,
    SupportControlledSelectedPartition.coverIndexLocalizedForm] using
    ManifoldForm.localized_projectInteriorBulkIntegral_eq_zero_of_tsupport_subset_interiorBox
      (I := I) (ω := ω) (ρ := P.partition (Sum.inl i))
      (x0 := C.interiorChart i.1) (x1 := C.interiorChart i.1)
      (a := C.interiorLower i.1) (b := C.interiorUpper i.1)
      (D.interiorExtendedBox i) (D.interiorLocalizedSupportSubset i)

/-- Boundary selected cover pieces satisfy the local bulk/boundary Stokes equality. -/
theorem boundaryLocalBulk_eq_localBoundary
    (D : SupportControlledCoverIndexedLocalStokesFields P ω)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    P.coverIndexLocalBulkTerm ω (Sum.inr i) =
      P.coverIndexLocalBoundaryTerm ω (Sum.inr i) := by
  have hcoeff :
      tsupport
          (ManifoldForm.transitionCoefficientInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1)
            (P.partition (Sum.inr i))) ∩ D.boundaryCoordSupport i ⊆
        halfSpaceSupportBox (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
    P.boundary_transitionCoefficient_inter_coordSupport_subset_box'
      (i := i) (coordSupport := D.boundaryCoordSupport i)
      (D.boundaryCoordMapsToSupport i) (D.boundaryCoordSubsetTarget i)
  simpa [SupportControlledSelectedPartition.coverIndexLocalBulkTerm,
    SupportControlledSelectedPartition.coverIndexLocalBoundaryTerm,
    SupportControlledSelectedPartition.coverIndexLocalizedForm] using
    boundaryAssignedBox_projectLocalStokes_of_contDiffOn_infty
      (I := I) (omega := ω)
      (x0 := C.boundaryChart i.1) (x1 := C.boundaryChart i.1)
      (rho := P.partition (Sum.inr i))
      (D.boundaryCoordCompact i)
      (D.boundaryCoordSubsetHalfSpace i)
      (D.boundaryBaseSupport i)
      (C.boundary_lower_zero i.1 i.2)
      (C.boundary_le i.1 i.2)
      hcoeff
      (C.boundary_Icc_subset_domain i.1 i.2)
      (D.boundaryNeighborhood_open i)
      (D.boundary_Icc_subset_neighborhood i)
      (D.boundaryCoeffSmooth i)
      (D.boundaryFormSmooth i)

/-- The concrete local term families satisfy local Stokes on every cover index. -/
theorem localBulk_eq_localBoundary
    (D : SupportControlledCoverIndexedLocalStokesFields P ω) :
    ∀ j : C.CoverIndex,
      P.coverIndexLocalBulkTerm ω j =
        P.coverIndexLocalBoundaryTerm ω j := by
  intro j
  rcases j with i | i
  · simpa [SupportControlledSelectedPartition.coverIndexLocalBoundaryTerm] using
      D.interiorLocalBulk_eq_zero i
  · exact D.boundaryLocalBulk_eq_localBoundary i

/-- Active-set version of the local Stokes equality for `Finset.univ`. -/
theorem localBulk_eq_localBoundary_on_coverIndexFinset
    (D : SupportControlledCoverIndexedLocalStokesFields P ω) :
    ∀ j, j ∈ (Finset.univ : Finset C.CoverIndex) →
      P.coverIndexLocalBulkTerm ω j =
        P.coverIndexLocalBoundaryTerm ω j := by
  intro j _hj
  exact D.localBulk_eq_localBoundary j

end SupportControlledCoverIndexedLocalStokesFields

end LocalTerms

section MeasureInput

universe u w a b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}

variable {αBulk : Type a} [TopologicalSpace αBulk]
variable [MeasurableSpace αBulk] [OpensMeasurableSpace αBulk]
variable [T2Space αBulk]
variable {μBulk : Measure αBulk} [IsFiniteMeasureOnCompacts μBulk]
variable {αBoundary : Type b} [TopologicalSpace αBoundary]
variable [MeasurableSpace αBoundary] [OpensMeasurableSpace αBoundary]
variable [T2Space αBoundary]
variable {μBoundary : Measure αBoundary}
variable [IsFiniteMeasureOnCompacts μBoundary]

/--
Natural support-controlled input package for the cover-indexed core.

The first fields are geometric and local: a selected chart-box cover, a
support-controlled partition on that cover, and the local smoothness/support
data proving the concrete cover-indexed local Stokes equalities.  The remaining
fields are scalar representation and compact-support integrability data for
the global bulk and boundary measure reconstructions.
-/
structure SupportControlledCoverIndexedMeasureInput where
  /-- Finite chart-box cover of the compact support set. -/
  chartBoxCover : CompactSupportChartCoverSelection I K
  /-- Support-controlled smooth partition subordinate to the selected cover. -/
  controlledPartition :
    SupportControlledSelectedPartition chartBoxCover
  /-- Local support and smoothness fields for cover-indexed local Stokes. -/
  localFields :
    SupportControlledCoverIndexedLocalStokesFields
      controlledPartition ω
  /-- Global bulk scalar integrand. -/
  bulkIntegrand : αBulk → Real
  /-- Cover-indexed bulk carrier sets. -/
  bulkPieceSet : chartBoxCover.CoverIndex → Set αBulk
  /-- Cover-indexed bulk scalar representatives. -/
  bulkPieceIntegrand : chartBoxCover.CoverIndex → αBulk → Real
  /-- Represented global bulk integral. -/
  globalBulkIntegral : Real
  /-- The represented bulk integral is the integral of the global integrand. -/
  globalBulkIntegral_eq_integral :
    globalBulkIntegral = ∫ y, bulkIntegrand y ∂μBulk
  /-- Bulk carriers are compact. -/
  bulkPiece_isCompact :
    ∀ j : chartBoxCover.CoverIndex, IsCompact (bulkPieceSet j)
  /-- Bulk scalar representatives are continuous on their carriers. -/
  bulkPiece_continuousOn :
    ∀ j : chartBoxCover.CoverIndex,
      ContinuousOn (bulkPieceIntegrand j) (bulkPieceSet j)
  /-- Bulk scalar representatives have support in their carriers. -/
  bulkPiece_tsupport_subset :
    ∀ j : chartBoxCover.CoverIndex,
      tsupport (bulkPieceIntegrand j) ⊆ bulkPieceSet j
  /-- Concrete local bulk terms are represented by set integrals. -/
  localBulk_eq_setIntegral :
    ∀ j : chartBoxCover.CoverIndex,
      controlledPartition.coverIndexLocalBulkTerm ω j =
        ∫ y in bulkPieceSet j, bulkPieceIntegrand j y ∂μBulk
  /-- A.e. reconstruction of the global bulk scalar integrand. -/
  bulkIntegrand_ae_eq_indicatorSum :
    bulkIntegrand =ᵐ[μBulk]
      fun y => ∑ j : chartBoxCover.CoverIndex,
        (bulkPieceSet j).indicator (bulkPieceIntegrand j) y
  /-- Global boundary scalar integrand. -/
  boundaryIntegrand : αBoundary → Real
  /-- Cover-indexed boundary carrier sets. -/
  boundaryPieceSet : chartBoxCover.CoverIndex → Set αBoundary
  /-- Cover-indexed boundary scalar representatives. -/
  boundaryPieceIntegrand :
    chartBoxCover.CoverIndex → αBoundary → Real
  /-- Represented global boundary integral. -/
  globalBoundaryIntegral : Real
  /-- The represented boundary integral is the integral of the global integrand. -/
  globalBoundaryIntegral_eq_integral :
    globalBoundaryIntegral = ∫ y, boundaryIntegrand y ∂μBoundary
  /-- Boundary carriers are compact. -/
  boundaryPiece_isCompact :
    ∀ j : chartBoxCover.CoverIndex, IsCompact (boundaryPieceSet j)
  /-- Boundary scalar representatives are continuous on their carriers. -/
  boundaryPiece_continuousOn :
    ∀ j : chartBoxCover.CoverIndex,
      ContinuousOn (boundaryPieceIntegrand j) (boundaryPieceSet j)
  /-- Boundary scalar representatives have support in their carriers. -/
  boundaryPiece_tsupport_subset :
    ∀ j : chartBoxCover.CoverIndex,
      tsupport (boundaryPieceIntegrand j) ⊆ boundaryPieceSet j
  /-- Concrete local boundary terms are represented by set integrals. -/
  localBoundary_eq_setIntegral :
    ∀ j : chartBoxCover.CoverIndex,
      controlledPartition.coverIndexLocalBoundaryTerm ω j =
        ∫ y in boundaryPieceSet j, boundaryPieceIntegrand j y ∂μBoundary
  /-- A.e. reconstruction of the global boundary scalar integrand. -/
  boundaryIntegrand_ae_eq_indicatorSum :
    boundaryIntegrand =ᵐ[μBoundary]
      fun y => ∑ j : chartBoxCover.CoverIndex,
        (boundaryPieceSet j).indicator (boundaryPieceIntegrand j) y

namespace SupportControlledCoverIndexedMeasureInput

/-- The canonical active cover set used by the cover-indexed core. -/
def active (D : SupportControlledCoverIndexedMeasureInput
    (I := I) (K := K) (ω := ω)
    (αBulk := αBulk) (μBulk := μBulk)
    (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    Finset D.chartBoxCover.CoverIndex :=
  Finset.univ

@[simp]
theorem mem_active
    (D : SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary))
    (j : D.chartBoxCover.CoverIndex) :
    j ∈ D.active := by
  classical
  simp [active]

/-- Bulk scalar fields projected from the support-controlled input. -/
def bulkSetIntegralFields
    (D : SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    CoverIndexedSetIntegralFields
      (α := αBulk) D.active μBulk
      (D.controlledPartition.coverIndexLocalBulkTerm ω) :=
  CoverIndexedSetIntegralFields.ofTSupportSubsetCompactBoxIndicator
    (μ := μBulk) D.active
    (D.controlledPartition.coverIndexLocalBulkTerm ω)
    D.bulkIntegrand D.bulkPieceSet D.bulkPieceIntegrand
    D.globalBulkIntegral D.globalBulkIntegral_eq_integral
    (fun j _hj => D.bulkPiece_isCompact j)
    (fun j _hj => D.bulkPiece_continuousOn j)
    (fun j _hj => D.bulkPiece_tsupport_subset j)
    (fun j _hj => D.localBulk_eq_setIntegral j)
    (by
      classical
      simpa [active] using D.bulkIntegrand_ae_eq_indicatorSum)

/-- Boundary scalar fields projected from the support-controlled input. -/
def boundarySetIntegralFields
    (D : SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    CoverIndexedSetIntegralFields
      (α := αBoundary) D.active μBoundary
      (D.controlledPartition.coverIndexLocalBoundaryTerm ω) :=
  CoverIndexedSetIntegralFields.ofTSupportSubsetCompactBoxIndicator
    (μ := μBoundary) D.active
    (D.controlledPartition.coverIndexLocalBoundaryTerm ω)
    D.boundaryIntegrand D.boundaryPieceSet D.boundaryPieceIntegrand
    D.globalBoundaryIntegral D.globalBoundaryIntegral_eq_integral
    (fun j _hj => D.boundaryPiece_isCompact j)
    (fun j _hj => D.boundaryPiece_continuousOn j)
    (fun j _hj => D.boundaryPiece_tsupport_subset j)
    (fun j _hj => D.localBoundary_eq_setIntegral j)
    (by
      classical
      simpa [active] using D.boundaryIntegrand_ae_eq_indicatorSum)

/-- Projection to the cover-indexed measure-field package. -/
def toCoverIndexedMeasureFields
    (D : SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    CoverIndexedMeasureFields D.active μBulk μBoundary where
  localBulk := D.controlledPartition.coverIndexLocalBulkTerm ω
  localBoundary := D.controlledPartition.coverIndexLocalBoundaryTerm ω
  bulk := D.bulkSetIntegralFields
  boundary := D.boundarySetIntegralFields
  localBulk_eq_localBoundary := by
    intro j _hj
    exact D.localFields.localBulk_eq_localBoundary j

/-- Projection all the way to the finite cover-indexed algebra core. -/
def toCoverIndexedStokesSums
    (D : SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    CoverIndexedStokesSums D.chartBoxCover.CoverIndex :=
  D.toCoverIndexedMeasureFields.toCoverIndexedStokesSums

/-- Cover-indexed compact-support Stokes from the support-controlled input. -/
theorem stokes
    (D : SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    D.globalBulkIntegral = D.globalBoundaryIntegral := by
  exact D.toCoverIndexedMeasureFields.stokes

end SupportControlledCoverIndexedMeasureInput

end MeasureInput

end Stokes

end
