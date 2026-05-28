import Stokes.Global.CoverIndexedNaturalConstructor
import Stokes.Global.CoverIndexedFromSupportControlledCover
import Stokes.Global.CoverIndexedClosedCarrier

/-!
# Assigned local data from compact-support chart-box choices

This file is the compact-support chart-box handoff for the represented Stokes
route.  It does not choose the compact coordinate carriers itself; instead it
records the exact local facts produced by such a choice and proves that they
fill `CoverIndexedAssignedBoxLocalData`.

The main reduction is mathematical rather than cosmetic:

* interior localized pieces get their selected-box support from the
  support-controlled partition coefficient together with the base coordinate
  carrier;
* boundary localized pieces get the half-space coefficient support from the
  same support-controlled bridge;
* smoothness fields are generated from `ChartwiseSmooth` and the smooth
  partition coefficients on chart-target neighborhoods.

Thus the remaining real chart-box-selection obligations are the compact
coordinate carriers, their containment in chart targets, and open smoothness
neighborhoods around the selected closed boxes.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section LocalDataFromCompactSupport

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {omega : ManifoldForm I M n}

namespace ManifoldForm

/-- A self chart overlap is automatic from membership in the chart target. -/
theorem mem_chartOverlap_self_of_mem_target
    {x : M} {y : Fin (n + 1) -> Real}
    (hy : y ∈ (extChartAt I x).target) :
    y ∈ chartOverlap I x x :=
  (extChartAt I x).map_target hy

/-- Set-level version of `mem_chartOverlap_self_of_mem_target`. -/
theorem subset_chartOverlap_self_of_subset_target
    {x : M} {U : Set (Fin (n + 1) -> Real)}
    (hU : U ⊆ (extChartAt I x).target) :
    U ⊆ chartOverlap I x x := fun y hy =>
  mem_chartOverlap_self_of_mem_target (I := I) (x := x) (y := y) (hU hy)

end ManifoldForm

namespace SupportControlledSelectedPartition

/-- Interior partition coefficients are smooth in their assigned self chart. -/
theorem interiorCoeffSmooth_infty
    [IsManifold I ⊤ M]
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.interiorCenters})
    {U : Set (Fin (n + 1) -> Real)}
    (hUtarget : U ⊆ (extChartAt I (C.interiorChart i.1)).target) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.transitionCoefficientInChart I
        (C.interiorChart i.1) (C.interiorChart i.1)
        (P.partition (Sum.inl i))) U := by
  exact
    ManifoldForm.contDiffOn_transitionCoefficientInChart_smoothPartition_indexed
      (I := I) P.partition (C.interiorChart i.1) (C.interiorChart i.1)
      (Sum.inl i) hUtarget
      (ManifoldForm.subset_chartOverlap_self_of_subset_target
        (I := I) (x := C.interiorChart i.1) hUtarget)

/-- Interior base-form chart representative smoothness from chartwise smoothness. -/
theorem interiorFormSmooth_infty_of_chartwiseSmooth
    [IsManifold I ⊤ M]
    (_P : SupportControlledSelectedPartition C)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (i : {x : M // x ∈ C.interiorCenters})
    {U : Set (Fin (n + 1) -> Real)}
    (hUtarget : U ⊆ (extChartAt I (C.interiorChart i.1)).target) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.transitionPullbackInChart I
        (C.interiorChart i.1) (C.interiorChart i.1) omega) U :=
  (homega.contDiffOn_transitionPullbackInChart_of_chartAPI
    (I := I) (C.interiorChart i.1) (C.interiorChart i.1)
    hUtarget
    (ManifoldForm.subset_chartOverlap_self_of_subset_target
      (I := I) (x := C.interiorChart i.1) hUtarget)).of_le le_top

/-- Interior localized representative smoothness from the natural inputs. -/
theorem interiorLocalizedFormSmooth_infty_of_smoothPartition
    [IsManifold I ⊤ M]
    (P : SupportControlledSelectedPartition C)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (i : {x : M // x ∈ C.interiorCenters})
    {U : Set (Fin (n + 1) -> Real)}
    (hUtarget : U ⊆ (extChartAt I (C.interiorChart i.1)).target) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.transitionPullbackInChart I
        (C.interiorChart i.1) (C.interiorChart i.1)
        (ManifoldForm.localizedForm I (P.partition (Sum.inl i)) omega)) U :=
  ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
    (I := I)
    (P.interiorCoeffSmooth_infty i hUtarget)
    (P.interiorFormSmooth_infty_of_chartwiseSmooth (omega := omega)
      homega i hUtarget)

end SupportControlledSelectedPartition

/--
Interior chart-box data left after compact-support selection.

The support-controlled partition supplies the coefficient support in the
selected manifold-side box.  The fields below are the remaining coordinate
carrier and smooth-neighborhood facts.  From them we derive the full interior
assigned-box package.
-/
structure CoverIndexedInteriorLocalDataFromCompactSupport
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n) where
  /-- Coordinate carriers for the base chart representatives. -/
  coordSupport :
    {x : M // x ∈ C.interiorCenters} ->
      Set (Fin (n + 1) -> Real)
  /-- Smoothness neighborhoods for the localized representatives. -/
  neighborhood :
    {x : M // x ∈ C.interiorCenters} ->
      Set (Fin (n + 1) -> Real)
  /-- The base representative is supported in the chosen coordinate carrier. -/
  base_tsupport_subset :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.interiorChart i.1) (C.interiorChart i.1) omega) ⊆
        coordSupport i
  /-- Coordinate carriers map back into the compact support set. -/
  coord_mapsTo_support :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      ∀ y ∈ coordSupport i,
        (extChartAt I (C.interiorChart i.1)).symm y ∈ K
  /-- Coordinate carriers lie in the selected chart target. -/
  coord_subset_target :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      coordSupport i ⊆
        (extChartAt I (C.interiorChart i.1)).target
  /-- Smoothness neighborhoods are open. -/
  neighborhood_open :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      IsOpen (neighborhood i)
  /-- The selected closed box lies in the smoothness neighborhood. -/
  Icc_subset_neighborhood :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      Set.Icc (C.interiorLower i.1) (C.interiorUpper i.1) ⊆
        neighborhood i
  /-- Smoothness neighborhoods lie in the source chart target. -/
  neighborhood_subset_target :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      neighborhood i ⊆
        (extChartAt I (C.interiorChart i.1)).target
  /--
  Legacy project-local smoothness for the localized interior representative.

  The natural smooth-partition data gives the `C^\infty` theorem
  `interiorLocalizedFormSmooth_infty_of_smoothPartition`; the current
  `interiorChartExtendedBox` API still asks for `ContDiffOn Real ⊤`.
  This field is therefore the minimal remaining smoothness-upgrade input on
  the interior side.
  -/
  localized_contDiffOn_top :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I
          (C.interiorChart i.1) (C.interiorChart i.1)
          (P.coverIndexLocalizedForm omega (Sum.inl i)))
        (neighborhood i)

namespace CoverIndexedInteriorLocalDataFromCompactSupport

/-- Localized interior representatives are supported in the strict assigned box. -/
theorem localized_tsupport_subset_interiorBox
    (D : CoverIndexedInteriorLocalDataFromCompactSupport C P omega)
    (i : {x : M // x ∈ C.interiorCenters}) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (C.interiorChart i.1) (C.interiorChart i.1)
          (P.coverIndexLocalizedForm omega (Sum.inl i))) ⊆
      boxInteriorSupportBox (C.interiorLower i.1) (C.interiorUpper i.1) := by
  simpa [SupportControlledSelectedPartition.coverIndexLocalizedForm] using
    ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_interiorBox_of_coordSupport
      (I := I)
      (x0 := C.interiorChart i.1) (x1 := C.interiorChart i.1)
      (ρ := P.partition (Sum.inl i)) (ω := omega)
      (a := C.interiorLower i.1) (b := C.interiorUpper i.1)
      (D.base_tsupport_subset i)
      (P.interior_transitionCoefficient_inter_coordSupport_subset_box'
        (i := i) (coordSupport := D.coordSupport i)
        (D.coord_mapsTo_support i) (D.coord_subset_target i))

/-- Localized interior representatives are supported in the selected closed box. -/
theorem localized_tsupport_subset_Icc
    (D : CoverIndexedInteriorLocalDataFromCompactSupport C P omega)
    (i : {x : M // x ∈ C.interiorCenters}) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (C.interiorChart i.1) (C.interiorChart i.1)
          (P.coverIndexLocalizedForm omega (Sum.inl i))) ⊆
      Set.Icc (C.interiorLower i.1) (C.interiorUpper i.1) :=
  (D.localized_tsupport_subset_interiorBox i).trans
    (CompactSupportChartCoverSelection.boxInteriorSupportBox_subset_Icc
      (a := C.interiorLower i.1) (b := C.interiorUpper i.1))

/-- The selected interior box for a localized cover piece. -/
theorem selectedBox
    (D : CoverIndexedInteriorLocalDataFromCompactSupport C P omega)
    (i : {x : M // x ∈ C.interiorCenters}) :
    interiorChartSelectedBox I
      (C.interiorChart i.1) (C.interiorChart i.1)
      (P.coverIndexLocalizedForm omega (Sum.inl i))
      (C.interiorLower i.1) (C.interiorUpper i.1) := by
  have hdomain := C.interior_Icc_subset_domain i.1 i.2
  exact
    interiorChartSelectedBox.mk_of_subsets
      (C.interior_le i.1 i.2)
      (fun y hy => (hdomain hy).1)
      (fun y hy => (hdomain hy).2)
      (D.localized_tsupport_subset_Icc i)

/-- The extended interior box generated from compact-support local data. -/
def extendedBox
    [IsManifold I ⊤ M]
    (D : CoverIndexedInteriorLocalDataFromCompactSupport C P omega)
    (_homega : ManifoldForm.ChartwiseSmooth I omega)
    (i : {x : M // x ∈ C.interiorCenters}) :
    interiorChartExtendedBox I
      (C.interiorChart i.1) (C.interiorChart i.1)
      (P.coverIndexLocalizedForm omega (Sum.inl i))
      (C.interiorLower i.1) (C.interiorUpper i.1) :=
  interiorChartExtendedBox.mk
    (D.selectedBox i)
    (D.neighborhood_open i)
    (D.Icc_subset_neighborhood i)
    (D.localized_contDiffOn_top i)

/-- Interior assigned-box fields produced by the compact-support local data. -/
def assignedFields
    [IsManifold I ⊤ M]
    (D : CoverIndexedInteriorLocalDataFromCompactSupport C P omega)
    (homega : ManifoldForm.ChartwiseSmooth I omega) :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      SupportControlledSelectedPartition.InteriorAssignedBoxCoordSupportFields
        P i omega (D.coordSupport i) :=
  fun i =>
    ⟨D.extendedBox homega i, D.base_tsupport_subset i,
      D.coord_mapsTo_support i, D.coord_subset_target i⟩

end CoverIndexedInteriorLocalDataFromCompactSupport

/--
Boundary chart-box data left after compact-support selection.

The coefficient half-space support is derived from the support-controlled
partition.  The fields here are exactly the remaining base-support, compact
carrier, half-space, target, and open-neighborhood obligations.
-/
structure CoverIndexedBoundaryLocalDataFromCompactSupport
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n) where
  /-- Coordinate carriers for boundary base chart representatives. -/
  coordSupport :
    {x : M // x ∈ C.boundaryCenters} ->
      Set (Fin (n + 1) -> Real)
  /-- Smoothness neighborhoods for boundary local Stokes. -/
  neighborhood :
    {x : M // x ∈ C.boundaryCenters} ->
      Set (Fin (n + 1) -> Real)
  /-- Boundary coordinate carriers are compact. -/
  coord_compact :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      IsCompact (coordSupport i)
  /-- Boundary coordinate carriers lie in the upper half-space. -/
  coord_subset_halfSpace :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      coordSupport i ⊆ upperHalfSpace n
  /-- The base boundary representative is supported in the chosen carrier. -/
  base_tsupport_subset :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1) omega) ⊆
        coordSupport i
  /-- Boundary coordinate carriers map back into the compact support set. -/
  coord_mapsTo_support :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      ∀ y ∈ coordSupport i,
        (extChartAt I (C.boundaryChart i.1)).symm y ∈ K
  /-- Boundary coordinate carriers lie in the selected chart target. -/
  coord_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      coordSupport i ⊆
        (extChartAt I (C.boundaryChart i.1)).target
  /-- Boundary smoothness neighborhoods are open. -/
  neighborhood_open :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      IsOpen (neighborhood i)
  /-- The selected closed boundary box lies in the smoothness neighborhood. -/
  Icc_subset_neighborhood :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
        neighborhood i
  /-- Boundary smoothness neighborhoods lie in the source chart target. -/
  neighborhood_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      neighborhood i ⊆
        (extChartAt I (C.boundaryChart i.1)).target

namespace CoverIndexedBoundaryLocalDataFromCompactSupport

/-- Boundary smoothness neighborhoods lie in the self-overlap domain. -/
theorem neighborhood_subset_overlap
    (D : CoverIndexedBoundaryLocalDataFromCompactSupport C P omega)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    D.neighborhood i ⊆
      ManifoldForm.chartOverlap I (C.boundaryChart i.1) (C.boundaryChart i.1) :=
  ManifoldForm.subset_chartOverlap_self_of_subset_target
    (I := I) (x := C.boundaryChart i.1) (D.neighborhood_subset_target i)

/-- Boundary assigned-box fields produced by the compact-support local data. -/
def assignedFields
    (D : CoverIndexedBoundaryLocalDataFromCompactSupport C P omega) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      SupportControlledSelectedPartition.BoundaryAssignedBoxCoordSupportFields
        P i omega (D.coordSupport i) (D.neighborhood i) :=
  fun i =>
    ⟨D.coord_compact i, D.coord_subset_halfSpace i,
      D.base_tsupport_subset i, C.boundary_lower_zero i.1 i.2,
      C.boundary_le i.1 i.2,
      P.boundary_transitionCoefficient_inter_coordSupport_subset_box'
        (i := i) (coordSupport := D.coordSupport i)
        (D.coord_mapsTo_support i) (D.coord_subset_target i),
      C.boundary_Icc_subset_domain i.1 i.2,
      D.neighborhood_open i, D.Icc_subset_neighborhood i⟩

/-- Boundary smoothness fields generated from chartwise smoothness. -/
def smoothnessFields
    [IsManifold I ⊤ M]
    (D : CoverIndexedBoundaryLocalDataFromCompactSupport C P omega)
    (homega : ManifoldForm.ChartwiseSmooth I omega) :
    CoverIndexedBoundarySmoothnessFields P omega D.neighborhood :=
  CoverIndexedBoundarySmoothnessFields.ofChartwiseSmooth
    (P := P) (omega := omega)
    homega D.neighborhood_subset_target D.neighborhood_subset_overlap

end CoverIndexedBoundaryLocalDataFromCompactSupport

/--
Grouped compact-support local-data input.

This is the natural constructor target: compact support and chart-box selection
should produce the two grouped carrier packages plus chartwise smoothness.
-/
structure CoverIndexedLocalDataFromCompactSupport
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n) where
  interior : CoverIndexedInteriorLocalDataFromCompactSupport C P omega
  boundary : CoverIndexedBoundaryLocalDataFromCompactSupport C P omega
  chartwiseSmooth : ManifoldForm.ChartwiseSmooth I omega

namespace CoverIndexedLocalDataFromCompactSupport

/-- Convert grouped compact-support local data into the endpoint local-data record. -/
def toAssignedBoxLocalData
    [IsManifold I ⊤ M]
    (D : CoverIndexedLocalDataFromCompactSupport C P omega) :
    CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P omega :=
  CoverIndexedAssignedBoxLocalData.ofChartwiseSmooth
    (I := I) (K := K) (C := C) (P := P) (ω := omega)
    D.interior.coordSupport
    (D.interior.assignedFields D.chartwiseSmooth)
    D.boundary.coordSupport
    D.boundary.neighborhood
    D.boundary.assignedFields
    D.boundary.coord_mapsTo_support
    D.boundary.coord_subset_target
    D.chartwiseSmooth
    D.boundary.neighborhood_subset_target
    D.boundary.neighborhood_subset_overlap

@[simp]
theorem toAssignedBoxLocalData_interiorCoordSupport
    [IsManifold I ⊤ M]
    (D : CoverIndexedLocalDataFromCompactSupport C P omega) :
    D.toAssignedBoxLocalData.interiorCoordSupport =
      D.interior.coordSupport :=
  by
    unfold toAssignedBoxLocalData CoverIndexedAssignedBoxLocalData.ofChartwiseSmooth
    rfl

@[simp]
theorem toAssignedBoxLocalData_boundaryCoordSupport
    [IsManifold I ⊤ M]
    (D : CoverIndexedLocalDataFromCompactSupport C P omega) :
    D.toAssignedBoxLocalData.boundaryCoordSupport =
      D.boundary.coordSupport :=
  by
    unfold toAssignedBoxLocalData CoverIndexedAssignedBoxLocalData.ofChartwiseSmooth
    rfl

@[simp]
theorem toAssignedBoxLocalData_boundaryNeighborhood
    [IsManifold I ⊤ M]
    (D : CoverIndexedLocalDataFromCompactSupport C P omega) :
    D.toAssignedBoxLocalData.boundaryNeighborhood =
      D.boundary.neighborhood :=
  by
    unfold toAssignedBoxLocalData CoverIndexedAssignedBoxLocalData.ofChartwiseSmooth
    rfl

/-- Direct local-Stokes fields generated from compact-support local data. -/
def toLocalFields
    [IsManifold I ⊤ M]
    (D : CoverIndexedLocalDataFromCompactSupport C P omega) :
    SupportControlledCoverIndexedLocalStokesFields P omega :=
  D.toAssignedBoxLocalData.toLocalFields

/-- Local bulk and boundary terms agree for every selected index. -/
theorem localBulk_eq_localBoundary
    [IsManifold I ⊤ M]
    (D : CoverIndexedLocalDataFromCompactSupport C P omega) :
    ∀ j : C.CoverIndex,
      P.coverIndexLocalBulkTerm omega j =
        P.coverIndexLocalBoundaryTerm omega j :=
  D.toAssignedBoxLocalData.localBulk_eq_localBoundary

end CoverIndexedLocalDataFromCompactSupport

end LocalDataFromCompactSupport

end Stokes

end
