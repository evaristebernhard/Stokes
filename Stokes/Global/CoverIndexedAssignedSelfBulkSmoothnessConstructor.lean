import Stokes.Global.CoverIndexedBulkAssignedNaturalConstructor
import Stokes.Global.CoverIndexedBulkSupportFromCompact
import Stokes.Global.CoverIndexedBoundarySmoothnessConstructor

/-!
# Assigned-self bulk smoothness constructors

This file closes the easy part of the assigned-self bulk route: the local
assigned-box data already carries the open smoothness neighborhoods needed for
each selected cover index.

There is one small level mismatch worth keeping explicit.  The existing
`CoverIndexedAssignedSelfBulkSmoothnessFields` asks for project-local `⊤`
smoothness, while the smooth partition and boundary constructors naturally
produce `C^\infty`, i.e. `((⊤ : ℕ∞) : WithTop ℕ∞)`.  We therefore expose both:

* a `C^\infty` assigned-self smoothness package generated directly from
  `CoverIndexedAssignedBoxLocalData`;
* a top-level adapter that can feed the pre-existing
  `CoverIndexedAssignedSelfBulkInput.ofSmoothnessFiniteSum` once a caller
  supplies exactly the remaining top-upgrade boundary lemma.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section InftyBulkContinuity

/-- The coordinate exterior-derivative scalar is continuous under `C^\infty`
smoothness on an open neighborhood. -/
theorem extDerivCoord_continuousOn_of_contDiffOn_isOpen_infty {n : Nat}
    {ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real}
    {U s : Set (Fin (n + 1) → Real)}
    (hU : IsOpen U) (hs : s ⊆ U)
    (hω : ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞) ω U) :
    ContinuousOn (CubeStokes.extDerivCoord (CubeStokes.toCoordNForm ω)) s := by
  change ContinuousOn
    (fun x =>
      ∑ i : Fin (n + 1),
        (-1 : Real) ^ (i : Nat) *
          fderiv Real (CubeStokes.toCoordNForm ω i) x (Pi.single i 1)) s
  apply continuousOn_finset_sum
  intro i _hi
  have hcoeff :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (CubeStokes.toCoordNForm ω i) U :=
    toCoordNForm_contDiffOn_of_level ω hω i
  have hfderiv :
      ContinuousOn (fderiv Real (CubeStokes.toCoordNForm ω i)) U :=
    hcoeff.continuousOn_fderiv_of_isOpen hU (by simp)
  have happly :
      ContinuousOn
        (fun x =>
          fderiv Real (CubeStokes.toCoordNForm ω i) x (Pi.single i 1)) U :=
    (ContinuousLinearMap.apply Real Real (Pi.single i 1)).continuous.comp_continuousOn
      hfderiv
  exact ((continuousOn_const.mul happly).mono hs : _)

/-- The top-degree `extDeriv` scalar is continuous under `C^\infty` smoothness
on an open neighborhood. -/
theorem modelBulkIntegrand_continuousOn_of_contDiffOn_isOpen_infty {n : Nat}
    {ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real}
    {U s : Set (Fin (n + 1) → Real)}
    (hU : IsOpen U) (hs : s ⊆ U)
    (hω : ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞) ω U) :
    ContinuousOn (fun y => extDeriv ω y (standardTopFrame n)) s := by
  have hcoord :
      ContinuousOn (CubeStokes.extDerivCoord (CubeStokes.toCoordNForm ω)) s :=
    extDerivCoord_continuousOn_of_contDiffOn_isOpen_infty hU hs hω
  exact hcoord.congr fun y hy => by
    have hyU : y ∈ U := hs hy
    have hdiff : DifferentiableAt Real ω y :=
      (hω.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)
    simpa [standardTopFrame] using
      CubeStokes.extDeriv_topCoeff_eq_extDerivCoord ω y hdiff

/-- Manifold-facing `C^\infty` continuity for the canonical scalar bulk
integrand. -/
theorem bulkIntegrand_continuousOn_of_contDiffOn_isOpen_infty
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {U s : Set (Fin (n + 1) → Real)}
    (hU : IsOpen U) (hs : s ⊆ U)
    (hω :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    ContinuousOn (bulkIntegrand I x0 x1 ω) s := by
  simpa [bulkIntegrand] using
    modelBulkIntegrand_continuousOn_of_contDiffOn_isOpen_infty
      (ω := ManifoldForm.transitionPullbackInChart I x0 x1 ω) hU hs hω

end InftyBulkContinuity

section AssignedSelfBulkSmoothnessConstructor

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {μBulk : Measure (Fin (n + 1) → Real)}
variable [IsFiniteMeasureOnCompacts μBulk]

namespace SupportControlledSelectedPartition

/-- Assigned-chart self-pair smoothness at the natural `C^\infty` level. -/
structure CoverIndexedAssignedSelfBulkSmoothnessFieldsInfty
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) where
  /-- Smoothness neighborhood for each assigned-chart scalar piece. -/
  smoothSet : C.CoverIndex → Set (Fin (n + 1) → Real)
  /-- The smoothness neighborhoods are open. -/
  isOpen_smoothSet :
    ∀ j : C.CoverIndex, IsOpen (smoothSet j)
  /-- Each closed carrier lies in its smoothness neighborhood. -/
  closedCarrier_subset_smoothSet :
    ∀ j : C.CoverIndex, C.coverIndexClosedCarrier j ⊆ smoothSet j
  /-- The localized assigned-chart representative is `C^\infty` on that
  neighborhood. -/
  localized_contDiffOn :
    ∀ j : C.CoverIndex,
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I
          (C.assignedChart j) (C.assignedChart j)
          (P.coverIndexLocalizedForm ω j)) (smoothSet j)

namespace CoverIndexedAssignedSelfBulkSmoothnessFieldsInfty

/-- `C^\infty` assigned-chart smoothness gives the closed-carrier continuity
required by the bulk measure layer. -/
theorem piece_continuousOn_closedCarrier
    {P : SupportControlledSelectedPartition C}
    (D : CoverIndexedAssignedSelfBulkSmoothnessFieldsInfty
      (I := I) (C := C) P ω) :
    ∀ j : C.CoverIndex,
      ContinuousOn
        (P.assignedSelfBulkPieceIntegrand (I := I) ω j)
        (C.coverIndexClosedCarrier j) := by
  intro j
  simpa [SupportControlledSelectedPartition.assignedSelfBulkPieceIntegrand]
    using
      bulkIntegrand_continuousOn_of_contDiffOn_isOpen_infty
        (I := I) (x0 := C.assignedChart j) (x1 := C.assignedChart j)
        (ω := P.coverIndexLocalizedForm ω j)
        (U := D.smoothSet j) (s := C.coverIndexClosedCarrier j)
        (D.isOpen_smoothSet j)
        (D.closedCarrier_subset_smoothSet j)
        (D.localized_contDiffOn j)

/-- Adapter to the older project-local `⊤` field shape, with the level upgrade
kept as the only explicit hypothesis. -/
def toTop
    {P : SupportControlledSelectedPartition C}
    (D : CoverIndexedAssignedSelfBulkSmoothnessFieldsInfty
      (I := I) (C := C) P ω)
    (localized_top :
      ∀ j : C.CoverIndex,
        ContDiffOn Real ⊤
          (ManifoldForm.transitionPullbackInChart I
            (C.assignedChart j) (C.assignedChart j)
            (P.coverIndexLocalizedForm ω j)) (D.smoothSet j)) :
    CoverIndexedAssignedSelfBulkSmoothnessFields
      (I := I) (C := C) P ω where
  smoothSet := D.smoothSet
  isOpen_smoothSet := D.isOpen_smoothSet
  closedCarrier_subset_smoothSet := D.closedCarrier_subset_smoothSet
  localized_contDiffOn := localized_top

end CoverIndexedAssignedSelfBulkSmoothnessFieldsInfty

end SupportControlledSelectedPartition

namespace CoverIndexedAssignedBoxLocalData

private noncomputable abbrev interiorSmoothSet
    (D : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (i : {x : M // x ∈ C.interiorCenters}) :
    Set (Fin (n + 1) → Real) :=
  Classical.choose ((D.interiorAssignedFields i).1.exists_smooth_nhds)

private theorem interiorSmoothSet_spec
    (D : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (i : {x : M // x ∈ C.interiorCenters}) :
    IsOpen (interiorSmoothSet (I := I) (K := K) (C := C) (P := P) (ω := ω) D i) ∧
      Set.Icc (C.interiorLower i.1) (C.interiorUpper i.1) ⊆
        interiorSmoothSet (I := I) (K := K) (C := C) (P := P) (ω := ω) D i ∧
        ContDiffOn Real ⊤
          (ManifoldForm.transitionPullbackInChart I
            (C.interiorChart i.1) (C.interiorChart i.1)
            (P.coverIndexLocalizedForm ω (Sum.inl i)))
          (interiorSmoothSet (I := I) (K := K) (C := C) (P := P) (ω := ω) D i) :=
  Classical.choose_spec ((D.interiorAssignedFields i).1.exists_smooth_nhds)

private theorem boundaryAssigned_isOpen
    (D : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    IsOpen (D.boundaryNeighborhood i) := by
  exact (D.boundaryAssignedFields i).2.2.2.2.2.2.2.1

private theorem boundaryAssigned_Icc_subset
    (D : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
      D.boundaryNeighborhood i := by
  exact (D.boundaryAssignedFields i).2.2.2.2.2.2.2.2

/-- The natural `C^\infty` assigned-self bulk smoothness generated by assigned
box local data. -/
noncomputable def assignedSelfBulkSmoothnessInfty
    [IsManifold I ⊤ M]
    (D : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω) :
    SupportControlledSelectedPartition.CoverIndexedAssignedSelfBulkSmoothnessFieldsInfty
      (I := I) (C := C) P ω where
  smoothSet := fun
    | Sum.inl i => interiorSmoothSet (I := I) (K := K) (C := C) (P := P) (ω := ω) D i
    | Sum.inr i => D.boundaryNeighborhood i
  isOpen_smoothSet := by
    intro j
    rcases j with i | i
    · exact (interiorSmoothSet_spec
        (I := I) (K := K) (C := C) (P := P) (ω := ω) D i).1
    · exact boundaryAssigned_isOpen
        (I := I) (K := K) (C := C) (P := P) (ω := ω) D i
  closedCarrier_subset_smoothSet := by
    intro j
    rcases j with i | i
    · simpa [CompactSupportChartCoverSelection.coverIndexClosedCarrier,
        CompactSupportChartCoverSelection.assignedLower,
        CompactSupportChartCoverSelection.assignedUpper] using
        (interiorSmoothSet_spec
          (I := I) (K := K) (C := C) (P := P) (ω := ω) D i).2.1
    · simpa [CompactSupportChartCoverSelection.coverIndexClosedCarrier,
        CompactSupportChartCoverSelection.assignedLower,
        CompactSupportChartCoverSelection.assignedUpper] using
        boundaryAssigned_Icc_subset
          (I := I) (K := K) (C := C) (P := P) (ω := ω) D i
  localized_contDiffOn := by
    intro j
    rcases j with i | i
    · simpa [CompactSupportChartCoverSelection.assignedChart] using
        ((interiorSmoothSet_spec
          (I := I) (K := K) (C := C) (P := P) (ω := ω) D i).2.2.of_le le_top)
    · simpa [CompactSupportChartCoverSelection.assignedChart,
        SupportControlledSelectedPartition.coverIndexLocalizedForm] using
        D.smoothness.localized_contDiffOn i

/-- Project-local `⊤` assigned-self bulk smoothness from assigned local data,
assuming only the boundary localized representatives have been upgraded from
the natural `C^\infty` level to project-local `⊤`. -/
noncomputable def assignedSelfBulkSmoothness
    [IsManifold I ⊤ M]
    (D : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (boundaryLocalized_top :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ⊤
          (ManifoldForm.transitionPullbackInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1)
            (P.coverIndexLocalizedForm ω (Sum.inr i)))
          (D.boundaryNeighborhood i)) :
    SupportControlledSelectedPartition.CoverIndexedAssignedSelfBulkSmoothnessFields
      (I := I) (C := C) P ω where
  smoothSet := fun
    | Sum.inl i => interiorSmoothSet (I := I) (K := K) (C := C) (P := P) (ω := ω) D i
    | Sum.inr i => D.boundaryNeighborhood i
  isOpen_smoothSet := by
    intro j
    rcases j with i | i
    · exact (interiorSmoothSet_spec
        (I := I) (K := K) (C := C) (P := P) (ω := ω) D i).1
    · exact boundaryAssigned_isOpen
        (I := I) (K := K) (C := C) (P := P) (ω := ω) D i
  closedCarrier_subset_smoothSet := by
    intro j
    rcases j with i | i
    · simpa [CompactSupportChartCoverSelection.coverIndexClosedCarrier,
        CompactSupportChartCoverSelection.assignedLower,
        CompactSupportChartCoverSelection.assignedUpper] using
        (interiorSmoothSet_spec
          (I := I) (K := K) (C := C) (P := P) (ω := ω) D i).2.1
    · simpa [CompactSupportChartCoverSelection.coverIndexClosedCarrier,
        CompactSupportChartCoverSelection.assignedLower,
        CompactSupportChartCoverSelection.assignedUpper] using
        boundaryAssigned_Icc_subset
          (I := I) (K := K) (C := C) (P := P) (ω := ω) D i
  localized_contDiffOn := by
    intro j
    rcases j with i | i
    · simpa [CompactSupportChartCoverSelection.assignedChart] using
        (interiorSmoothSet_spec
          (I := I) (K := K) (C := C) (P := P) (ω := ω) D i).2.2
    · simpa [CompactSupportChartCoverSelection.assignedChart] using
        boundaryLocalized_top i

end CoverIndexedAssignedBoxLocalData

namespace CoverIndexedAssignedSelfBulkInput

/-- Direct finite-sum assigned-self bulk input from assigned-box local data at
the natural `C^\infty` level.  This bypasses the older project-local `⊤`
smoothness field by proving the scalar bulk continuity directly from `C^\infty`
smoothness. -/
noncomputable def ofLocalDataInftyFiniteSum
    [IsManifold I ⊤ M]
    (measure_eq_volume :
      μBulk = (volume : Measure (Fin (n + 1) → Real)))
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω) :
    CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk where
  integrand := P.assignedSelfBulkIntegrand (I := I) ω
  globalIntegral :=
    ∫ y, P.assignedSelfBulkIntegrand (I := I) ω y ∂μBulk
  globalIntegral_eq_integral := rfl
  measure_eq_volume := measure_eq_volume
  piece_continuousOn_closedCarrier :=
    (localData.assignedSelfBulkSmoothnessInfty
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      ).piece_continuousOn_closedCarrier
  piece_tsupport_subset_assigned :=
    localData.bulkIntegrand_tsupport_subset_assignedCoordinateBox_self
  integrand_ae_eq_pieceSum :=
    P.assignedSelfBulkIntegrand_ae_eq_pieceSum (I := I) ω μBulk

/-- Finite-sum assigned-self bulk input through the existing
`ofSmoothnessFiniteSum` constructor.  The only remaining hypothesis is the
boundary `C^\infty`-to-project-local-`⊤` localized smoothness upgrade. -/
noncomputable def ofLocalDataTopFiniteSum
    [IsManifold I ⊤ M]
    (measure_eq_volume :
      μBulk = (volume : Measure (Fin (n + 1) → Real)))
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (boundaryLocalized_top :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ⊤
          (ManifoldForm.transitionPullbackInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1)
            (P.coverIndexLocalizedForm ω (Sum.inr i)))
          (localData.boundaryNeighborhood i)) :
    CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk :=
  CoverIndexedAssignedSelfBulkInput.ofSmoothnessFiniteSum
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (μBulk := μBulk)
    measure_eq_volume
    (localData.assignedSelfBulkSmoothness
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      boundaryLocalized_top)
    localData.bulkIntegrand_tsupport_subset_assignedCoordinateBox_self

end CoverIndexedAssignedSelfBulkInput

namespace SupportControlledSelectedPartition

/-- Closed-carrier assigned-self bulk data generated directly from assigned-box
local data at the natural `C^\infty` level. -/
noncomputable def assignedSelfClosedCarrierBulkData_of_localDataInfty
    [IsManifold I ⊤ M]
    (P : SupportControlledSelectedPartition C)
    (measure_eq_volume :
      μBulk = (volume : Measure (Fin (n + 1) → Real)))
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω) :
    CoverIndexedClosedCarrierBulkData
      (I := I) (K := K) (μBulk := μBulk) C P ω :=
  (CoverIndexedAssignedSelfBulkInput.ofLocalDataInftyFiniteSum
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (μBulk := μBulk) measure_eq_volume localData).toClosedCarrierBulkData

/-- Resolved assigned-self bulk fields generated directly from assigned-box
local data at the natural `C^\infty` level. -/
noncomputable def assignedSelfResolvedBulkFields_of_localDataInfty
    [IsManifold I ⊤ M]
    (P : SupportControlledSelectedPartition C)
    (measure_eq_volume :
      μBulk = (volume : Measure (Fin (n + 1) → Real)))
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω) :
    CoverIndexedResolvedBulkFields
      (C := C) (ω := ω)
      (αBulk := Fin (n + 1) → Real) (μBulk := μBulk) P :=
  (P.assignedSelfClosedCarrierBulkData_of_localDataInfty
    (I := I) (K := K) (ω := ω) (μBulk := μBulk)
    measure_eq_volume localData).toResolvedBulkFields

end SupportControlledSelectedPartition

end AssignedSelfBulkSmoothnessConstructor

end Stokes

end
