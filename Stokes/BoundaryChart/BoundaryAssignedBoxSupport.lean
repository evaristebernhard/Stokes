import Stokes.BoundaryChart.BoundaryFiniteBoxLocalStokes
import Stokes.Global.FiniteBoxCoverPartition

/-!
# Boundary assigned half-space boxes for localized pieces

This file supplies the boundary analogue of the finite-box support lemma used
for interior pieces.  It is intentionally conditional: a future subordinate
partition construction should provide the coefficient support-control
hypothesis, and the compact chart-cover selection should provide the compact
coordinate carrier and the selected half-space box.

The main point is mathematical rather than structural:

* if the base boundary representative is supported in a coordinate carrier `C`,
* and the partition coefficient is supported inside the assigned half-space
  box on that carrier,

then the localized boundary representative is supported in that half-space
box.  With compactness, half-space containment, domain containment, and local
smoothness, this immediately produces the existing boundary compact box data
and the outward-first local Stokes identity.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

open ManifoldForm

section CoreSupport

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n k : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {ρ : M → Real}
variable {ω : ManifoldForm I M k}
variable {a b : Fin (n + 1) → Real}

namespace ManifoldForm

/--
If the coefficient support and the base representative support intersect only
inside an assigned half-space support box, then the localized representative is
supported in that same half-space box.
-/
theorem transitionPullbackInChart_localizedForm_tsupport_subset_halfSpaceSupportBox_of_inter
    (hinter :
      tsupport (transitionCoefficientInChart I x0 x1 ρ) ∩
          tsupport (transitionPullbackInChart I x0 x1 ω) ⊆
        halfSpaceSupportBox a b) :
    tsupport (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
      halfSpaceSupportBox a b := by
  intro y hy
  exact hinter
    ⟨transitionPullbackInChart_localizedForm_tsupport_subset_coefficient
        (I := I) x0 x1 ρ ω hy,
      transitionPullbackInChart_localizedForm_tsupport_subset_form
        (I := I) x0 x1 ρ ω hy⟩

/--
Coordinate-carrier spelling.  This is the shape expected from the compact
chart-cover/refined-partition step: the base representative is carried by `C`,
and the coefficient is subordinate to the assigned half-space box on `C`.
-/
theorem transitionPullbackInChart_localizedForm_tsupport_subset_halfSpaceSupportBox_of_coordSupport
    {C : Set (Fin (n + 1) → Real)}
    (hbase : tsupport (transitionPullbackInChart I x0 x1 ω) ⊆ C)
    (hcoeff :
      tsupport (transitionCoefficientInChart I x0 x1 ρ) ∩ C ⊆
        halfSpaceSupportBox a b) :
    tsupport (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
      halfSpaceSupportBox a b := by
  refine
    transitionPullbackInChart_localizedForm_tsupport_subset_halfSpaceSupportBox_of_inter
      (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
      (a := a) (b := b) ?_
  intro y hy
  exact hcoeff ⟨hy.1, hbase hy.2⟩

/--
Chart-image spelling for later compact-support globalization.
-/
theorem transitionPullbackInChart_localizedForm_tsupport_subset_halfSpaceSupportBox_of_chartImage
    {K : Set M}
    (hbase :
      tsupport (transitionPullbackInChart I x0 x1 ω) ⊆
        chartCoordinateImage I x0 K)
    (hcoeff :
      tsupport (transitionCoefficientInChart I x0 x1 ρ) ∩
          chartCoordinateImage I x0 K ⊆
        halfSpaceSupportBox a b) :
    tsupport (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
      halfSpaceSupportBox a b :=
  transitionPullbackInChart_localizedForm_tsupport_subset_halfSpaceSupportBox_of_coordSupport
    (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
    (a := a) (b := b) hbase hcoeff

end ManifoldForm

end CoreSupport

section BoundaryLocalStokes

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {ρ : M → Real}
variable {ω : ManifoldForm I M n}

/--
Assigned-box boundary local Stokes from coordinate-carrier support control.

The hypotheses are the conditional output expected from the compact-support
globalization step:

* `K` is the compact coordinate carrier for the boundary localized piece;
* `K` lies in the ambient upper half-space;
* the base representative is supported in `K`;
* the partition coefficient is supported, on `K`, in the assigned half-space
  support box.

The conclusion both records the localized representative support containment
and returns the existing compact box data with the outward-first local Stokes
identity.
-/
theorem exists_boundaryAssignedBoxData_localStokes_of_coordSupport
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hbase :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hcoeff :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ∩ K ⊆
        halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hlocalizedU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) U) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) ⊆
        halfSpaceSupportBox a b ∧
      ∃ D :
          BoundaryCompactBoxSelectionData I x0 x1
            (ManifoldForm.localizedForm I ρ ω),
        D.K =
            tsupport
              (ManifoldForm.transitionPullbackInChart I x0 x1
                (ManifoldForm.localizedForm I ρ ω)) ∧
          D.a = a ∧ D.b = b ∧
          halfSpaceLocalBulkIntegral
              (ManifoldForm.transitionPullbackInChart I x0 x1
                (ManifoldForm.localizedForm I ρ ω)) D.a D.b =
            outwardFirstBoundaryChartIntegral I x0 x1
              (ManifoldForm.localizedForm I ρ ω) D.a D.b := by
  have hsuppBox :
      tsupport
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω)) ⊆
        halfSpaceSupportBox a b :=
    transitionPullbackInChart_localizedForm_tsupport_subset_halfSpaceSupportBox_of_coordSupport
        (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
        (a := a) (b := b) hbase hcoeff
  have hsuppK :
      tsupport
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω)) ⊆ K :=
    (ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_form
      (I := I) x0 x1 ρ ω).trans hbase
  have hKloc :
      IsCompact
        (tsupport
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω))) :=
    isCompact_tsupport_of_subset_isCompact hK hsuppK
  have hhalfloc :
      tsupport
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω)) ⊆
        upperHalfSpace n :=
    hsuppK.trans hhalf
  exact
    ⟨hsuppBox,
      exists_boundaryLocalizedBoxData_localStokes_of_box_subset_domain
        (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
        hKloc hhalfloc (Subset.refl _) ha0 hle hsuppBox hdomain hU hUbox
        hlocalizedU⟩

/--
`C^\infty` version of
`exists_boundaryAssignedBoxData_localStokes_of_coordSupport`.
-/
theorem exists_boundaryAssignedBoxData_localStokes_of_coordSupport_infty
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hbase :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hcoeff :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ∩ K ⊆
        halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hlocalizedU :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) U) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) ⊆
        halfSpaceSupportBox a b ∧
      ∃ D :
          BoundaryCompactBoxSelectionData I x0 x1
            (ManifoldForm.localizedForm I ρ ω),
        D.K =
            tsupport
              (ManifoldForm.transitionPullbackInChart I x0 x1
                (ManifoldForm.localizedForm I ρ ω)) ∧
          D.a = a ∧ D.b = b ∧
          halfSpaceLocalBulkIntegral
              (ManifoldForm.transitionPullbackInChart I x0 x1
                (ManifoldForm.localizedForm I ρ ω)) D.a D.b =
            outwardFirstBoundaryChartIntegral I x0 x1
              (ManifoldForm.localizedForm I ρ ω) D.a D.b := by
  have hsuppBox :
      tsupport
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω)) ⊆
        halfSpaceSupportBox a b :=
    transitionPullbackInChart_localizedForm_tsupport_subset_halfSpaceSupportBox_of_coordSupport
        (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
        (a := a) (b := b) hbase hcoeff
  have hsuppK :
      tsupport
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω)) ⊆ K :=
    (ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_form
      (I := I) x0 x1 ρ ω).trans hbase
  have hKloc :
      IsCompact
        (tsupport
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω))) :=
    isCompact_tsupport_of_subset_isCompact hK hsuppK
  have hhalfloc :
      tsupport
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω)) ⊆
        upperHalfSpace n :=
    hsuppK.trans hhalf
  exact
    ⟨hsuppBox,
      exists_boundaryLocalizedBoxData_localStokes_of_box_subset_domain_infty
        (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
        hKloc hhalfloc (Subset.refl _) ha0 hle hsuppBox hdomain hU hUbox
        hlocalizedU⟩

/--
Variant deriving localized smoothness from coefficient and base representative
smoothness on the same open box-neighborhood.
-/
theorem exists_boundaryAssignedBoxData_localStokes_of_contDiffOn
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hbase :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hcoeff :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ∩ K ⊆
        halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hρU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) U)
    (hωU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) ⊆
        halfSpaceSupportBox a b ∧
      ∃ D :
          BoundaryCompactBoxSelectionData I x0 x1
            (ManifoldForm.localizedForm I ρ ω),
        D.K =
            tsupport
              (ManifoldForm.transitionPullbackInChart I x0 x1
                (ManifoldForm.localizedForm I ρ ω)) ∧
          D.a = a ∧ D.b = b ∧
          halfSpaceLocalBulkIntegral
              (ManifoldForm.transitionPullbackInChart I x0 x1
                (ManifoldForm.localizedForm I ρ ω)) D.a D.b =
            outwardFirstBoundaryChartIntegral I x0 x1
              (ManifoldForm.localizedForm I ρ ω) D.a D.b := by
  exact
    exists_boundaryAssignedBoxData_localStokes_of_coordSupport
      (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
      hK hhalf hbase ha0 hle hcoeff hdomain hU hUbox
      (ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
        (I := I) hρU hωU)

/--
`C^\infty` version of
`exists_boundaryAssignedBoxData_localStokes_of_contDiffOn`.
-/
theorem exists_boundaryAssignedBoxData_localStokes_of_contDiffOn_infty
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hbase :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hcoeff :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ∩ K ⊆
        halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hρU :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) U)
    (hωU :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) ⊆
        halfSpaceSupportBox a b ∧
      ∃ D :
          BoundaryCompactBoxSelectionData I x0 x1
            (ManifoldForm.localizedForm I ρ ω),
        D.K =
            tsupport
              (ManifoldForm.transitionPullbackInChart I x0 x1
                (ManifoldForm.localizedForm I ρ ω)) ∧
          D.a = a ∧ D.b = b ∧
          halfSpaceLocalBulkIntegral
              (ManifoldForm.transitionPullbackInChart I x0 x1
                (ManifoldForm.localizedForm I ρ ω)) D.a D.b =
            outwardFirstBoundaryChartIntegral I x0 x1
              (ManifoldForm.localizedForm I ρ ω) D.a D.b := by
  exact
    exists_boundaryAssignedBoxData_localStokes_of_coordSupport_infty
      (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
      hK hhalf hbase ha0 hle hcoeff hdomain hU hUbox
      (ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
        (I := I) hρU hωU)

/--
Chartwise-smooth spelling for the later compact-support theorem.  The only
remaining analytic input about the partition is smoothness of its transition
coefficient on the chosen open neighborhood.
-/
theorem exists_boundaryAssignedBoxData_localStokes_of_chartwiseSmooth
    [IsManifold I ⊤ M]
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hbase :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hcoeff :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ∩ K ⊆
        halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hρU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) U)
    (hω : ManifoldForm.ChartwiseSmooth I ω)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I x0 x1) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) ⊆
        halfSpaceSupportBox a b ∧
      ∃ D :
          BoundaryCompactBoxSelectionData I x0 x1
            (ManifoldForm.localizedForm I ρ ω),
        D.K =
            tsupport
              (ManifoldForm.transitionPullbackInChart I x0 x1
                (ManifoldForm.localizedForm I ρ ω)) ∧
          D.a = a ∧ D.b = b ∧
          halfSpaceLocalBulkIntegral
              (ManifoldForm.transitionPullbackInChart I x0 x1
                (ManifoldForm.localizedForm I ρ ω)) D.a D.b =
            outwardFirstBoundaryChartIntegral I x0 x1
              (ManifoldForm.localizedForm I ρ ω) D.a D.b := by
  exact
    exists_boundaryAssignedBoxData_localStokes_of_contDiffOn
      (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
      hK hhalf hbase ha0 hle hcoeff hdomain hU hUbox hρU
      (hω.contDiffOn_transitionPullbackInChart_of_chartAPI
        (I := I) x0 x1 hUtarget hUoverlap)

end BoundaryLocalStokes

section SelectedPartition

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

namespace SelectedBoxPartitionOfUnity

/--
Selected-partition wrapper for boundary assigned half-space boxes.  This is a
thin specialization of the core support theorem to the self-transition chart
used by active selected partitions.
-/
theorem localized_transitionPullback_tsupport_subset_halfSpaceSupportBox_of_coordSupport
    (P : SelectedBoxPartitionOfUnity I ω)
    {coordSupport : M → Set (Fin (n + 1) → Real)}
    {lower upper : M → Fin (n + 1) → Real}
    (hbase :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          coordSupport i)
    (hcoeff :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionCoefficientInChart I i i (P.partition i)) ∩
            coordSupport i ⊆
          halfSpaceSupportBox (lower i) (upper i))
    {i : M} (hi : i ∈ P.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      halfSpaceSupportBox (lower i) (upper i) :=
  transitionPullbackInChart_localizedForm_tsupport_subset_halfSpaceSupportBox_of_coordSupport
      (I := I) (x0 := i) (x1 := i) (ρ := P.partition i) (ω := ω)
      (a := lower i) (b := upper i) (hbase i hi) (hcoeff i hi)

end SelectedBoxPartitionOfUnity

end SelectedPartition

end Stokes

end
