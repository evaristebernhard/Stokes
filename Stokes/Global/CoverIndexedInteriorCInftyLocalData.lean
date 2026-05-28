import Stokes.Global.CoverIndexedLocalDataFromCompactSupport

/-!
# C-infinity interior local data for cover-indexed Stokes

The legacy interior local-data route stores
`ContDiffOn Real ⊤ ... U`, where `⊤` is the top element of `WithTop ℕ∞`.
The natural smooth partition/chartwise-smooth inputs only produce
`ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞) ... U`.

These are not the same hypothesis: the first one is project-local top
smoothness, while the second is the usual `C^\infty` level.  This file therefore
does not provide a fake upgrade.  Instead it adds the C-infinity version of the
interior extended-box/local-Stokes bridge and packages compact-support interior
local data without the legacy `localized_contDiffOn_top` field.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section InteriorCInftyLocalData

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E] [Preorder E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
C-infinity version of `interiorChartExtendedBox`.

This is the natural smoothness level produced by smooth partitions of unity and
chartwise-smooth forms.  It deliberately keeps a separate name because
`ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)` cannot be upgraded to
`ContDiffOn Real ⊤` in general.
-/
def interiorChartExtendedBoxInfty
    (I : ModelWithCorners Real E H) (x0 x1 : M) (ω : ManifoldForm I M k)
    (a b : E) : Prop :=
  interiorChartSelectedBox I x0 x1 ω a b ∧
    ∃ U : Set E,
      IsOpen U ∧ Set.Icc a b ⊆ U ∧
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U

namespace interiorChartExtendedBoxInfty

theorem mk
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    {a b : E} (hselected : interiorChartSelectedBox I x0 x1 ω a b)
    {U : Set E} (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U)
    (hωU :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    interiorChartExtendedBoxInfty I x0 x1 ω a b :=
  ⟨hselected, ⟨U, hU, hUbox, hωU⟩⟩

theorem mk_of_subsets
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    {a b : E} (hle : a ≤ b)
    (htarget : Set.Icc a b ⊆ (extChartAt I x0).target)
    (hoverlap : Set.Icc a b ⊆ ManifoldForm.chartOverlap I x0 x1)
    (hsupp : tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      Set.Icc a b)
    {U : Set E} (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U)
    (hωU :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    interiorChartExtendedBoxInfty I x0 x1 ω a b :=
  mk (interiorChartSelectedBox.mk_of_subsets hle htarget hoverlap hsupp)
    hU hUbox hωU

theorem selectedBox
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    {a b : E} (hbox : interiorChartExtendedBoxInfty I x0 x1 ω a b) :
    interiorChartSelectedBox I x0 x1 ω a b :=
  hbox.1

theorem exists_smooth_nhds
    {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}
    {a b : E} (hbox : interiorChartExtendedBoxInfty I x0 x1 ω a b) :
    ∃ U : Set E,
      IsOpen U ∧ Set.Icc a b ⊆ U ∧
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U :=
  hbox.2

end interiorChartExtendedBoxInfty

section FinCoordinate

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/-- Interior local Stokes using the natural `C^\infty` smoothness level. -/
theorem projectInteriorLocalStokes_of_extendedBoxInfty
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hbox : interiorChartExtendedBoxInfty I x0 x1 ω a b) :
    projectInteriorBulkIntegral I x0 x1 ω a b =
      projectInteriorBoundaryIntegral I x0 x1 ω a b := by
  rcases hbox.exists_smooth_nhds with ⟨U, hU, hUbox, hωU⟩
  simpa [projectInteriorBulkIntegral, projectInteriorBoundaryIntegral, bdryIntegral,
    halfSpaceLocalBulkIntegral] using
    box_stokes_extDeriv_contDiffOn_isOpen_infty
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω)
      a b hbox.selectedBox.le hU hUbox hωU

/--
If an interior chart representative is strictly supported inside a C-infinity
extended box, its project-local bulk term vanishes.
-/
theorem projectInteriorBulkIntegral_eq_zero_of_tsupport_subset_interiorBox_infty
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hbox : interiorChartExtendedBoxInfty I x0 x1 ω a b)
    (hsupp : tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      boxInteriorSupportBox a b) :
    projectInteriorBulkIntegral I x0 x1 ω a b = 0 := by
  calc
    projectInteriorBulkIntegral I x0 x1 ω a b =
        projectInteriorBoundaryIntegral I x0 x1 ω a b :=
      projectInteriorLocalStokes_of_extendedBoxInfty I x0 x1 ω a b hbox
    _ = 0 :=
      projectInteriorBoundaryIntegral_eq_zero_of_tsupport_subset_interiorBox
        I x0 x1 ω a b hsupp

namespace ManifoldForm

/-- Localized project-local bulk vanishing from C-infinity interior box data. -/
theorem localized_projectInteriorBulkIntegral_eq_zero_of_tsupport_subset_interiorBox_infty
    {ρ : M → Real} {x0 x1 : M} {a b : Fin (n + 1) → Real}
    (hbox :
      interiorChartExtendedBoxInfty I x0 x1 (localizedForm I ρ ω) a b)
    (hsupp :
      tsupport
          (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
        boxInteriorSupportBox a b) :
    projectInteriorBulkIntegral I x0 x1 (localizedForm I ρ ω) a b = 0 :=
  projectInteriorBulkIntegral_eq_zero_of_tsupport_subset_interiorBox_infty
    I x0 x1 (localizedForm I ρ ω) a b hbox hsupp

end ManifoldForm

end FinCoordinate

end InteriorCInftyLocalData

section CoverIndexedInteriorCInfty

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {omega : ManifoldForm I M n}

namespace SupportControlledSelectedPartition

/--
Interior assigned-box fields at the natural C-infinity smoothness level.

This mirrors `InteriorAssignedBoxCoordSupportFields`, but replaces the legacy
`interiorChartExtendedBox` by `interiorChartExtendedBoxInfty`.
-/
abbrev InteriorAssignedBoxCoordSupportFieldsInfty
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.interiorCenters})
    (ω : ManifoldForm I M n)
    (coordSupport : Set (Fin (n + 1) → Real)) : Prop :=
  interiorChartExtendedBoxInfty I
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

/-- Constructor for the C-infinity interior assigned-box field package. -/
theorem interior_assignedBoxCoordSupportFieldsInfty
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.interiorCenters})
    {coordSupport : Set (Fin (n + 1) → Real)}
    (hbox :
      interiorChartExtendedBoxInfty I
        (C.interiorChart i.1) (C.interiorChart i.1)
        (P.coverIndexLocalizedForm omega (Sum.inl i))
        (C.interiorLower i.1) (C.interiorUpper i.1))
    (hbase :
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.interiorChart i.1) (C.interiorChart i.1) omega) ⊆
        coordSupport)
    (hcoordK :
      ∀ y ∈ coordSupport,
        (extChartAt I (C.interiorChart i.1)).symm y ∈ K)
    (hcoordTarget :
      coordSupport ⊆ (extChartAt I (C.interiorChart i.1)).target) :
    InteriorAssignedBoxCoordSupportFieldsInfty P i omega coordSupport :=
  ⟨hbox, hbase, hcoordK, hcoordTarget⟩

/-- Localized interior representatives are strictly supported from C∞ fields. -/
theorem interiorLocalizedSupportSubset_of_assignedBoxFieldsInfty
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.interiorCenters})
    {coordSupport : Set (Fin (n + 1) → Real)}
    (hfields : InteriorAssignedBoxCoordSupportFieldsInfty P i omega coordSupport) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (C.interiorChart i.1) (C.interiorChart i.1)
          (P.coverIndexLocalizedForm omega (Sum.inl i))) ⊆
      boxInteriorSupportBox (C.interiorLower i.1) (C.interiorUpper i.1) := by
  rcases hfields with ⟨_hbox, hbase, hcoordK, hcoordTarget⟩
  exact
    ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_interiorBox_of_coordSupport
      (I := I)
      (x0 := C.interiorChart i.1) (x1 := C.interiorChart i.1)
      (ρ := P.partition (Sum.inl i)) (ω := omega)
      (a := C.interiorLower i.1) (b := C.interiorUpper i.1)
      hbase
      (P.interior_transitionCoefficient_inter_coordSupport_subset_box'
        (i := i) (coordSupport := coordSupport) hcoordK hcoordTarget)

/-- Interior cover-indexed pieces have zero local bulk term from C∞ fields. -/
theorem coverIndexInteriorLocalBulk_eq_zero_of_assignedBoxFieldsInfty
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.interiorCenters})
    {coordSupport : Set (Fin (n + 1) → Real)}
    (hfields : InteriorAssignedBoxCoordSupportFieldsInfty P i omega coordSupport) :
    P.coverIndexLocalBulkTerm omega (Sum.inl i) = 0 := by
  rcases hfields with ⟨hbox, hbase, hcoordK, hcoordTarget⟩
  have hsupp :
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.interiorChart i.1) (C.interiorChart i.1)
            (P.coverIndexLocalizedForm omega (Sum.inl i))) ⊆
        boxInteriorSupportBox (C.interiorLower i.1) (C.interiorUpper i.1) := by
    exact
      interiorLocalizedSupportSubset_of_assignedBoxFieldsInfty
        (P := P) (omega := omega) (i := i) (coordSupport := coordSupport)
        ⟨hbox, hbase, hcoordK, hcoordTarget⟩
  simpa [SupportControlledSelectedPartition.coverIndexLocalBulkTerm,
    SupportControlledSelectedPartition.coverIndexLocalizedForm] using
    ManifoldForm.localized_projectInteriorBulkIntegral_eq_zero_of_tsupport_subset_interiorBox_infty
      (I := I) (ω := omega) (ρ := P.partition (Sum.inl i))
      (x0 := C.interiorChart i.1) (x1 := C.interiorChart i.1)
      (a := C.interiorLower i.1) (b := C.interiorUpper i.1)
      hbox hsupp

/--
Interior cover-indexed local Stokes from C∞ assigned-box fields.
The interior boundary term is definitionally zero.
-/
theorem coverIndexInteriorLocalBulk_eq_localBoundary_of_assignedBoxFieldsInfty
    (P : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.interiorCenters})
    {coordSupport : Set (Fin (n + 1) → Real)}
    (hfields : InteriorAssignedBoxCoordSupportFieldsInfty P i omega coordSupport) :
    P.coverIndexLocalBulkTerm omega (Sum.inl i) =
      P.coverIndexLocalBoundaryTerm omega (Sum.inl i) := by
  simpa [SupportControlledSelectedPartition.coverIndexLocalBoundaryTerm] using
    coverIndexInteriorLocalBulk_eq_zero_of_assignedBoxFieldsInfty
      (P := P) (omega := omega) (i := i) hfields

end SupportControlledSelectedPartition

/--
Interior chart-box data produced by compact-support selection at the natural
C-infinity smoothness level.

Compared with `CoverIndexedInteriorLocalDataFromCompactSupport`, this structure
does not contain `localized_contDiffOn_top`.
-/
structure CoverIndexedInteriorLocalDataFromCompactSupportInfty
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n) where
  coordSupport :
    {x : M // x ∈ C.interiorCenters} →
      Set (Fin (n + 1) → Real)
  neighborhood :
    {x : M // x ∈ C.interiorCenters} →
      Set (Fin (n + 1) → Real)
  base_tsupport_subset :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.interiorChart i.1) (C.interiorChart i.1) omega) ⊆
        coordSupport i
  coord_mapsTo_support :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      ∀ y ∈ coordSupport i,
        (extChartAt I (C.interiorChart i.1)).symm y ∈ K
  coord_subset_target :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      coordSupport i ⊆
        (extChartAt I (C.interiorChart i.1)).target
  neighborhood_open :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      IsOpen (neighborhood i)
  Icc_subset_neighborhood :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      Set.Icc (C.interiorLower i.1) (C.interiorUpper i.1) ⊆
        neighborhood i
  neighborhood_subset_target :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      neighborhood i ⊆
        (extChartAt I (C.interiorChart i.1)).target

namespace CoverIndexedInteriorLocalDataFromCompactSupportInfty

/-- Localized interior representatives are supported in the strict assigned box. -/
theorem localized_tsupport_subset_interiorBox
    (D : CoverIndexedInteriorLocalDataFromCompactSupportInfty C P omega)
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
    (D : CoverIndexedInteriorLocalDataFromCompactSupportInfty C P omega)
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
    (D : CoverIndexedInteriorLocalDataFromCompactSupportInfty C P omega)
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

/-- Natural C∞ smoothness of the localized interior representative. -/
theorem localized_contDiffOn_infty
    [IsManifold I ⊤ M]
    (D : CoverIndexedInteriorLocalDataFromCompactSupportInfty C P omega)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (i : {x : M // x ∈ C.interiorCenters}) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.transitionPullbackInChart I
        (C.interiorChart i.1) (C.interiorChart i.1)
        (P.coverIndexLocalizedForm omega (Sum.inl i)))
      (D.neighborhood i) := by
  simpa [SupportControlledSelectedPartition.coverIndexLocalizedForm] using
    P.interiorLocalizedFormSmooth_infty_of_smoothPartition
      (omega := omega) homega i (D.neighborhood_subset_target i)

/-- The C∞ extended interior box generated from compact-support local data. -/
def extendedBoxInfty
    [IsManifold I ⊤ M]
    (D : CoverIndexedInteriorLocalDataFromCompactSupportInfty C P omega)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (i : {x : M // x ∈ C.interiorCenters}) :
    interiorChartExtendedBoxInfty I
      (C.interiorChart i.1) (C.interiorChart i.1)
      (P.coverIndexLocalizedForm omega (Sum.inl i))
      (C.interiorLower i.1) (C.interiorUpper i.1) :=
  interiorChartExtendedBoxInfty.mk
    (D.selectedBox i)
    (D.neighborhood_open i)
    (D.Icc_subset_neighborhood i)
    (D.localized_contDiffOn_infty homega i)

/-- C∞ interior assigned-box fields produced by compact-support local data. -/
def assignedFieldsInfty
    [IsManifold I ⊤ M]
    (D : CoverIndexedInteriorLocalDataFromCompactSupportInfty C P omega)
    (homega : ManifoldForm.ChartwiseSmooth I omega) :
    ∀ i : {x : M // x ∈ C.interiorCenters},
      SupportControlledSelectedPartition.InteriorAssignedBoxCoordSupportFieldsInfty
        P i omega (D.coordSupport i) :=
  fun i =>
    ⟨D.extendedBoxInfty homega i, D.base_tsupport_subset i,
      D.coord_mapsTo_support i, D.coord_subset_target i⟩

/-- Interior local bulk vanishes from compact-support C∞ local data. -/
theorem coverIndexInteriorLocalBulk_eq_zero
    [IsManifold I ⊤ M]
    (D : CoverIndexedInteriorLocalDataFromCompactSupportInfty C P omega)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (i : {x : M // x ∈ C.interiorCenters}) :
    P.coverIndexLocalBulkTerm omega (Sum.inl i) = 0 :=
  SupportControlledSelectedPartition.coverIndexInteriorLocalBulk_eq_zero_of_assignedBoxFieldsInfty
    (P := P) (omega := omega) (i := i)
    (coordSupport := D.coordSupport i)
    (D.assignedFieldsInfty homega i)

/-- Interior local bulk equals the definitionally zero interior boundary term. -/
theorem coverIndexInteriorLocalBulk_eq_localBoundary
    [IsManifold I ⊤ M]
    (D : CoverIndexedInteriorLocalDataFromCompactSupportInfty C P omega)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (i : {x : M // x ∈ C.interiorCenters}) :
    P.coverIndexLocalBulkTerm omega (Sum.inl i) =
      P.coverIndexLocalBoundaryTerm omega (Sum.inl i) :=
  SupportControlledSelectedPartition.coverIndexInteriorLocalBulk_eq_localBoundary_of_assignedBoxFieldsInfty
    (P := P) (omega := omega) (i := i)
    (coordSupport := D.coordSupport i)
    (D.assignedFieldsInfty homega i)

/--
Exact residual type needed only when callers must target the legacy
`CoverIndexedInteriorLocalDataFromCompactSupport` record.
-/
abbrev TopSmoothnessUpgrade
    (D : CoverIndexedInteriorLocalDataFromCompactSupportInfty C P omega) : Prop :=
  ∀ i : {x : M // x ∈ C.interiorCenters},
    ContDiffOn Real ⊤
      (ManifoldForm.transitionPullbackInChart I
        (C.interiorChart i.1) (C.interiorChart i.1)
        (P.coverIndexLocalizedForm omega (Sum.inl i)))
      (D.neighborhood i)

/--
Adapter to the legacy local-data record.  This is intentionally the only place
where the old project-local top smoothness hypothesis appears in this file.
-/
def toLegacy
    (D : CoverIndexedInteriorLocalDataFromCompactSupportInfty C P omega)
    (htop : D.TopSmoothnessUpgrade) :
    CoverIndexedInteriorLocalDataFromCompactSupport C P omega where
  coordSupport := D.coordSupport
  neighborhood := D.neighborhood
  base_tsupport_subset := D.base_tsupport_subset
  coord_mapsTo_support := D.coord_mapsTo_support
  coord_subset_target := D.coord_subset_target
  neighborhood_open := D.neighborhood_open
  Icc_subset_neighborhood := D.Icc_subset_neighborhood
  neighborhood_subset_target := D.neighborhood_subset_target
  localized_contDiffOn_top := htop

end CoverIndexedInteriorLocalDataFromCompactSupportInfty

end CoverIndexedInteriorCInfty

end Stokes

end
