import Stokes.Global.CoverIndexedZeroConstructors
import Stokes.Global.ZeroExtensionBulkEquality

/-!
# Cover-indexed zero-extension bulk measure constructors

The zero-extension layer gives support control for chart representatives, while
the local Stokes and measure layers still use the old smooth representative.
This file packages the bulk scalar comparison needed by the measure layer:
on a selected source box which has an open neighborhood inside the concrete
chart-transition source, the zero-extended bulk scalar and the old bulk scalar
agree pointwise, a.e. on the restricted measure, and hence have the same
set integral.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section GenericZeroBulkMeasure

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {ω : ManifoldForm I M n}

/-- Pointwise equality on a set contained in an open transition-source
neighborhood.  This is the generic bridge used by the cover-indexed source-box
lemmas below. -/
theorem zeroTransitionBulkIntegrand_eqOn_bulkIntegrand_of_subset_open_source
    {s U : Set (Fin (n + 1) → Real)}
    (hUopen : IsOpen U) (hsU : s ⊆ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    EqOn (zeroTransitionBulkIntegrand I x0 x1 ω)
      (bulkIntegrand I x0 x1 ω) s := by
  intro y hy
  exact
    zeroTransitionBulkIntegrand_eq_bulkIntegrand_of_isOpen_mem
      (I := I) (x0 := x0) (x1 := x1) (ω := ω) (y := y)
      hUopen (hsU hy) hUsource

/-- Restricted-measure a.e. equality from the pointwise source-neighborhood
comparison. -/
theorem zeroTransitionBulkIntegrand_ae_eq_bulkIntegrand_restrict_of_subset_open_source
    {μ : Measure (Fin (n + 1) → Real)}
    {s U : Set (Fin (n + 1) → Real)}
    (hsmeas : MeasurableSet s)
    (hUopen : IsOpen U) (hsU : s ⊆ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    zeroTransitionBulkIntegrand I x0 x1 ω =ᵐ[μ.restrict s]
      bulkIntegrand I x0 x1 ω := by
  filter_upwards [ae_restrict_mem hsmeas] with y hy
  exact
    zeroTransitionBulkIntegrand_eqOn_bulkIntegrand_of_subset_open_source
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      hUopen hsU hUsource hy

/-- Set-integral equality on any measurable set contained in an open
transition-source neighborhood. -/
theorem zeroTransitionBulkIntegrand_setIntegral_eq_bulkIntegrand_of_subset_open_source
    {μ : Measure (Fin (n + 1) → Real)}
    {s U : Set (Fin (n + 1) → Real)}
    (hsmeas : MeasurableSet s)
    (hUopen : IsOpen U) (hsU : s ⊆ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    (∫ y in s, zeroTransitionBulkIntegrand I x0 x1 ω y ∂μ) =
      ∫ y in s, bulkIntegrand I x0 x1 ω y ∂μ := by
  exact
    integral_congr_ae
      (zeroTransitionBulkIntegrand_ae_eq_bulkIntegrand_restrict_of_subset_open_source
        (I := I) (x0 := x0) (x1 := x1) (ω := ω)
        (μ := μ) hsmeas hUopen hsU hUsource)

/-- Closed-box pointwise equality, in the shape most source-box callers use. -/
theorem zeroTransitionBulkIntegrand_eqOn_Icc_bulkIntegrand_of_open_source
    {a b : Fin (n + 1) → Real} {U : Set (Fin (n + 1) → Real)}
    (hUopen : IsOpen U) (hIccU : Icc a b ⊆ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    EqOn (zeroTransitionBulkIntegrand I x0 x1 ω)
      (bulkIntegrand I x0 x1 ω) (Icc a b) :=
  zeroTransitionBulkIntegrand_eqOn_bulkIntegrand_of_subset_open_source
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    hUopen hIccU hUsource

/-- Restricted-measure a.e. equality on a closed coordinate box. -/
theorem zeroTransitionBulkIntegrand_ae_eq_bulkIntegrand_restrict_Icc_of_open_source
    {μ : Measure (Fin (n + 1) → Real)}
    {a b : Fin (n + 1) → Real} {U : Set (Fin (n + 1) → Real)}
    (hUopen : IsOpen U) (hIccU : Icc a b ⊆ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    zeroTransitionBulkIntegrand I x0 x1 ω =ᵐ[μ.restrict (Icc a b)]
      bulkIntegrand I x0 x1 ω :=
  zeroTransitionBulkIntegrand_ae_eq_bulkIntegrand_restrict_of_subset_open_source
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    (μ := μ) measurableSet_Icc hUopen hIccU hUsource

/-- Set-integral equality over a closed coordinate box. -/
theorem zeroTransitionBulkIntegrand_setIntegral_Icc_eq_bulkIntegrand_of_open_source
    {μ : Measure (Fin (n + 1) → Real)}
    {a b : Fin (n + 1) → Real} {U : Set (Fin (n + 1) → Real)}
    (hUopen : IsOpen U) (hIccU : Icc a b ⊆ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1) :
    (∫ y in Icc a b, zeroTransitionBulkIntegrand I x0 x1 ω y ∂μ) =
      ∫ y in Icc a b, bulkIntegrand I x0 x1 ω y ∂μ :=
  zeroTransitionBulkIntegrand_setIntegral_eq_bulkIntegrand_of_subset_open_source
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    (μ := μ) measurableSet_Icc hUopen hIccU hUsource

/-- Transfer a recorded local integral from the zero-extended scalar to the old
scalar on the same closed source box. -/
theorem localTerm_eq_old_bulk_setIntegral_Icc_of_zero_bulk_setIntegral
    {μ : Measure (Fin (n + 1) → Real)}
    {a b : Fin (n + 1) → Real} {U : Set (Fin (n + 1) → Real)}
    {localTerm : Real}
    (hUopen : IsOpen U) (hIccU : Icc a b ⊆ U)
    (hUsource : U ⊆ ManifoldForm.chartTransitionSource I x0 x1)
    (hzero :
      localTerm =
        ∫ y in Icc a b,
          zeroTransitionBulkIntegrand I x0 x1 ω y ∂μ) :
    localTerm =
      ∫ y in Icc a b, bulkIntegrand I x0 x1 ω y ∂μ :=
  hzero.trans
    (zeroTransitionBulkIntegrand_setIntegral_Icc_eq_bulkIntegrand_of_open_source
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      (μ := μ) hUopen hIccU hUsource)

end GenericZeroBulkMeasure

section CoverIndexedZeroBulkMeasure

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {ω : ManifoldForm I M n}

namespace CoverIndexedCompactSupportNeighborhoodData

variable
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodData
        (I := I) (K := K) C P ω)

include neighborhoodData

/-- Interior source boxes have an open neighborhood inside the self transition
source. -/
theorem interior_neighborhood_subset_chartTransitionSource
    (i : {x : M // x ∈ C.interiorCenters}) :
    neighborhoodData.interiorNeighborhood i ⊆
      ManifoldForm.chartTransitionSource I
        (C.interiorChart i.1) (C.interiorChart i.1) := by
  intro y hy
  rw [ManifoldForm.chartTransitionSource_eq]
  exact
    ⟨neighborhoodData.interior_neighborhood_subset_target i hy,
      ManifoldForm.subset_chartOverlap_self_of_subset_target
        (I := I) (x := C.interiorChart i.1)
        (neighborhoodData.interior_neighborhood_subset_target i) hy⟩

/-- Interior selected source boxes lie in the self transition source. -/
theorem interior_sourceBox_subset_chartTransitionSource
    (i : {x : M // x ∈ C.interiorCenters}) :
    Icc (C.interiorLower i.1) (C.interiorUpper i.1) ⊆
      ManifoldForm.chartTransitionSource I
        (C.interiorChart i.1) (C.interiorChart i.1) :=
  (CoverIndexedCompactSupportNeighborhoodData.interior_Icc_subset_neighborhood
      neighborhoodData i).trans
    (CoverIndexedCompactSupportNeighborhoodData.interior_neighborhood_subset_chartTransitionSource
      neighborhoodData i)

/-- On an interior selected source box, the zero-extended assigned-self bulk
scalar agrees pointwise with the old assigned-self bulk scalar. -/
theorem interior_zeroBulk_eqOn_oldBulk_sourceBox
    (i : {x : M // x ∈ C.interiorCenters}) :
    EqOn
      (zeroTransitionBulkIntegrand I
        (C.interiorChart i.1) (C.interiorChart i.1)
        (P.coverIndexLocalizedForm ω (Sum.inl i)))
      (bulkIntegrand I
        (C.interiorChart i.1) (C.interiorChart i.1)
        (P.coverIndexLocalizedForm ω (Sum.inl i)))
      (Icc (C.interiorLower i.1) (C.interiorUpper i.1)) :=
  zeroTransitionBulkIntegrand_eqOn_Icc_bulkIntegrand_of_open_source
    (I := I)
    (x0 := C.interiorChart i.1) (x1 := C.interiorChart i.1)
    (ω := P.coverIndexLocalizedForm ω (Sum.inl i))
    (a := C.interiorLower i.1) (b := C.interiorUpper i.1)
    (U :=
      CoverIndexedCompactSupportNeighborhoodData.interiorNeighborhood
        neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.interior_neighborhood_open
      neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.interior_Icc_subset_neighborhood
      neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.interior_neighborhood_subset_chartTransitionSource
      neighborhoodData i)

/-- A.e. version of `interior_zeroBulk_eqOn_oldBulk_sourceBox`. -/
theorem interior_zeroBulk_ae_eq_oldBulk_restrict_sourceBox
    {μ : Measure (Fin (n + 1) → Real)}
    (i : {x : M // x ∈ C.interiorCenters}) :
    zeroTransitionBulkIntegrand I
        (C.interiorChart i.1) (C.interiorChart i.1)
        (P.coverIndexLocalizedForm ω (Sum.inl i)) =ᵐ[
          μ.restrict (Icc (C.interiorLower i.1) (C.interiorUpper i.1))]
      bulkIntegrand I
        (C.interiorChart i.1) (C.interiorChart i.1)
        (P.coverIndexLocalizedForm ω (Sum.inl i)) :=
  zeroTransitionBulkIntegrand_ae_eq_bulkIntegrand_restrict_Icc_of_open_source
    (I := I)
    (x0 := C.interiorChart i.1) (x1 := C.interiorChart i.1)
    (ω := P.coverIndexLocalizedForm ω (Sum.inl i))
    (μ := μ)
    (a := C.interiorLower i.1) (b := C.interiorUpper i.1)
    (U :=
      CoverIndexedCompactSupportNeighborhoodData.interiorNeighborhood
        neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.interior_neighborhood_open
      neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.interior_Icc_subset_neighborhood
      neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.interior_neighborhood_subset_chartTransitionSource
      neighborhoodData i)

/-- Set-integral version of `interior_zeroBulk_eqOn_oldBulk_sourceBox`. -/
theorem interior_zeroBulk_setIntegral_eq_oldBulk_sourceBox
    {μ : Measure (Fin (n + 1) → Real)}
    (i : {x : M // x ∈ C.interiorCenters}) :
    (∫ y in Icc (C.interiorLower i.1) (C.interiorUpper i.1),
        zeroTransitionBulkIntegrand I
          (C.interiorChart i.1) (C.interiorChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inl i)) y ∂μ) =
      ∫ y in Icc (C.interiorLower i.1) (C.interiorUpper i.1),
        bulkIntegrand I
          (C.interiorChart i.1) (C.interiorChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inl i)) y ∂μ :=
  zeroTransitionBulkIntegrand_setIntegral_Icc_eq_bulkIntegrand_of_open_source
    (I := I)
    (x0 := C.interiorChart i.1) (x1 := C.interiorChart i.1)
    (ω := P.coverIndexLocalizedForm ω (Sum.inl i))
    (μ := μ)
    (a := C.interiorLower i.1) (b := C.interiorUpper i.1)
    (U :=
      CoverIndexedCompactSupportNeighborhoodData.interiorNeighborhood
        neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.interior_neighborhood_open
      neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.interior_Icc_subset_neighborhood
      neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.interior_neighborhood_subset_chartTransitionSource
      neighborhoodData i)

/-- Transfer an interior local source-box integral from the zero scalar to the
old scalar. -/
theorem interior_localTerm_eq_oldBulk_setIntegral_sourceBox_of_zeroBulk
    {μ : Measure (Fin (n + 1) → Real)}
    {localTerm : Real}
    (i : {x : M // x ∈ C.interiorCenters})
    (hzero :
      localTerm =
        ∫ y in Icc (C.interiorLower i.1) (C.interiorUpper i.1),
          zeroTransitionBulkIntegrand I
            (C.interiorChart i.1) (C.interiorChart i.1)
            (P.coverIndexLocalizedForm ω (Sum.inl i)) y ∂μ) :
    localTerm =
      ∫ y in Icc (C.interiorLower i.1) (C.interiorUpper i.1),
        bulkIntegrand I
          (C.interiorChart i.1) (C.interiorChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inl i)) y ∂μ :=
  hzero.trans
    (CoverIndexedCompactSupportNeighborhoodData.interior_zeroBulk_setIntegral_eq_oldBulk_sourceBox
      neighborhoodData
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      (μ := μ) i)

/-- Boundary neighborhoods lie in the self transition source.  This is the
assigned-self analogue of the source-target boundary lemma below. -/
theorem boundary_self_neighborhood_subset_chartTransitionSource
    (i : {x : M // x ∈ C.boundaryCenters}) :
    neighborhoodData.boundaryNeighborhood i ⊆
      ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (C.boundaryChart i.1) := by
  intro y hy
  rw [ManifoldForm.chartTransitionSource_eq]
  exact
    ⟨neighborhoodData.boundary_neighborhood_subset_target i hy,
      ManifoldForm.subset_chartOverlap_self_of_subset_target
        (I := I) (x := C.boundaryChart i.1)
        (neighborhoodData.boundary_neighborhood_subset_target i) hy⟩

/-- On a boundary selected source box, the assigned-self zero bulk scalar agrees
with the old assigned-self bulk scalar. -/
theorem boundary_self_zeroBulk_eqOn_oldBulk_sourceBox
    (i : {x : M // x ∈ C.boundaryCenters}) :
    EqOn
      (zeroTransitionBulkIntegrand I
        (C.boundaryChart i.1) (C.boundaryChart i.1)
        (P.coverIndexLocalizedForm ω (Sum.inr i)))
      (bulkIntegrand I
        (C.boundaryChart i.1) (C.boundaryChart i.1)
        (P.coverIndexLocalizedForm ω (Sum.inr i)))
      (Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :=
  zeroTransitionBulkIntegrand_eqOn_Icc_bulkIntegrand_of_open_source
    (I := I)
    (x0 := C.boundaryChart i.1) (x1 := C.boundaryChart i.1)
    (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
    (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
    (U :=
      CoverIndexedCompactSupportNeighborhoodData.boundaryNeighborhood
        neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.boundary_neighborhood_open
      neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.boundary_Icc_subset_neighborhood
      neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.boundary_self_neighborhood_subset_chartTransitionSource
      neighborhoodData i)

/-- A.e. version of `boundary_self_zeroBulk_eqOn_oldBulk_sourceBox`. -/
theorem boundary_self_zeroBulk_ae_eq_oldBulk_restrict_sourceBox
    {μ : Measure (Fin (n + 1) → Real)}
    (i : {x : M // x ∈ C.boundaryCenters}) :
    zeroTransitionBulkIntegrand I
        (C.boundaryChart i.1) (C.boundaryChart i.1)
        (P.coverIndexLocalizedForm ω (Sum.inr i)) =ᵐ[
          μ.restrict (Icc (C.boundaryLower i.1) (C.boundaryUpper i.1))]
      bulkIntegrand I
        (C.boundaryChart i.1) (C.boundaryChart i.1)
        (P.coverIndexLocalizedForm ω (Sum.inr i)) :=
  zeroTransitionBulkIntegrand_ae_eq_bulkIntegrand_restrict_Icc_of_open_source
    (I := I)
    (x0 := C.boundaryChart i.1) (x1 := C.boundaryChart i.1)
    (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
    (μ := μ)
    (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
    (U :=
      CoverIndexedCompactSupportNeighborhoodData.boundaryNeighborhood
        neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.boundary_neighborhood_open
      neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.boundary_Icc_subset_neighborhood
      neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.boundary_self_neighborhood_subset_chartTransitionSource
      neighborhoodData i)

/-- Set-integral version of `boundary_self_zeroBulk_eqOn_oldBulk_sourceBox`. -/
theorem boundary_self_zeroBulk_setIntegral_eq_oldBulk_sourceBox
    {μ : Measure (Fin (n + 1) → Real)}
    (i : {x : M // x ∈ C.boundaryCenters}) :
    (∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
        zeroTransitionBulkIntegrand I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i)) y ∂μ) =
      ∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
        bulkIntegrand I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i)) y ∂μ :=
  zeroTransitionBulkIntegrand_setIntegral_Icc_eq_bulkIntegrand_of_open_source
    (I := I)
    (x0 := C.boundaryChart i.1) (x1 := C.boundaryChart i.1)
    (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
    (μ := μ)
    (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
    (U :=
      CoverIndexedCompactSupportNeighborhoodData.boundaryNeighborhood
        neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.boundary_neighborhood_open
      neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.boundary_Icc_subset_neighborhood
      neighborhoodData i)
    (CoverIndexedCompactSupportNeighborhoodData.boundary_self_neighborhood_subset_chartTransitionSource
      neighborhoodData i)

/-- Transfer a boundary assigned-self local source-box integral from the zero
scalar to the old scalar. -/
theorem boundary_self_localTerm_eq_oldBulk_setIntegral_sourceBox_of_zeroBulk
    {μ : Measure (Fin (n + 1) → Real)}
    {localTerm : Real}
    (i : {x : M // x ∈ C.boundaryCenters})
    (hzero :
      localTerm =
        ∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
          zeroTransitionBulkIntegrand I
            (C.boundaryChart i.1) (C.boundaryChart i.1)
            (P.coverIndexLocalizedForm ω (Sum.inr i)) y ∂μ) :
    localTerm =
      ∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
        bulkIntegrand I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i)) y ∂μ :=
  hzero.trans
    (CoverIndexedCompactSupportNeighborhoodData.boundary_self_zeroBulk_setIntegral_eq_oldBulk_sourceBox
      neighborhoodData
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      (μ := μ) i)

end CoverIndexedCompactSupportNeighborhoodData

namespace CoverIndexedCompactSupportTransitionSupportData

variable
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodData
        (I := I) (K := K) C P ω)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P ω)

/-- Extra open-neighborhood hypothesis needed for the source-target boundary
bulk derivative comparison.  The existing transition-support record gives
`Icc ⊆ overlap`; derivative equality needs an actual neighborhood contained in
the concrete transition source. -/
abbrev BoundaryNeighborhoodSubsetTransitionSource : Prop :=
  ∀ i : {x : M // x ∈ C.boundaryCenters},
    neighborhoodData.boundaryNeighborhood i ⊆
      ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)

/-- Boundary source-target pointwise equality on the selected source box. -/
theorem boundary_zeroBulk_eqOn_oldBulk_sourceBox
    (hsource : BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (C := C) (neighborhoodData := neighborhoodData)
      transitionSupportData)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    EqOn
      (zeroTransitionBulkIntegrand I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)
        (P.coverIndexLocalizedForm ω (Sum.inr i)))
      (bulkIntegrand I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)
        (P.coverIndexLocalizedForm ω (Sum.inr i)))
      (Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)) :=
  zeroTransitionBulkIntegrand_eqOn_Icc_bulkIntegrand_of_open_source
    (I := I)
    (x0 := C.boundaryChart i.1)
    (x1 := transitionSupportData.targetChart i)
    (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
    (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
    (U := neighborhoodData.boundaryNeighborhood i)
    (neighborhoodData.boundary_neighborhood_open i)
    (neighborhoodData.boundary_Icc_subset_neighborhood i)
    (hsource i)

/-- Boundary source-target a.e. equality on the selected source box. -/
theorem boundary_zeroBulk_ae_eq_oldBulk_restrict_sourceBox
    {μ : Measure (Fin (n + 1) → Real)}
    (hsource : BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (C := C) (neighborhoodData := neighborhoodData)
      transitionSupportData)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    zeroTransitionBulkIntegrand I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)
        (P.coverIndexLocalizedForm ω (Sum.inr i)) =ᵐ[
          μ.restrict (Icc (C.boundaryLower i.1) (C.boundaryUpper i.1))]
      bulkIntegrand I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i)
        (P.coverIndexLocalizedForm ω (Sum.inr i)) :=
  zeroTransitionBulkIntegrand_ae_eq_bulkIntegrand_restrict_Icc_of_open_source
    (I := I)
    (x0 := C.boundaryChart i.1)
    (x1 := transitionSupportData.targetChart i)
    (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
    (μ := μ)
    (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
    (U := neighborhoodData.boundaryNeighborhood i)
    (neighborhoodData.boundary_neighborhood_open i)
    (neighborhoodData.boundary_Icc_subset_neighborhood i)
    (hsource i)

/-- Boundary source-target set-integral equality over the selected source box. -/
theorem boundary_zeroBulk_setIntegral_eq_oldBulk_sourceBox
    {μ : Measure (Fin (n + 1) → Real)}
    (hsource : BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (C := C) (neighborhoodData := neighborhoodData)
      transitionSupportData)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    (∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
        zeroTransitionBulkIntegrand I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i)) y ∂μ) =
      ∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
        bulkIntegrand I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i)) y ∂μ :=
  zeroTransitionBulkIntegrand_setIntegral_Icc_eq_bulkIntegrand_of_open_source
    (I := I)
    (x0 := C.boundaryChart i.1)
    (x1 := transitionSupportData.targetChart i)
    (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
    (μ := μ)
    (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
    (U := neighborhoodData.boundaryNeighborhood i)
    (neighborhoodData.boundary_neighborhood_open i)
    (neighborhoodData.boundary_Icc_subset_neighborhood i)
    (hsource i)

/-- Transfer a boundary source-target local integral from the zero scalar to
the old scalar on the selected source box. -/
theorem boundary_localTerm_eq_oldBulk_setIntegral_sourceBox_of_zeroBulk
    {μ : Measure (Fin (n + 1) → Real)}
    {localTerm : Real}
    (hsource : BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (C := C) (neighborhoodData := neighborhoodData)
      transitionSupportData)
    (i : {x : M // x ∈ C.boundaryCenters})
    (hzero :
      localTerm =
        ∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
          zeroTransitionBulkIntegrand I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i)) y ∂μ) :
    localTerm =
      ∫ y in Icc (C.boundaryLower i.1) (C.boundaryUpper i.1),
        bulkIntegrand I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i)) y ∂μ :=
  hzero.trans
    (transitionSupportData.boundary_zeroBulk_setIntegral_eq_oldBulk_sourceBox
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      (neighborhoodData := neighborhoodData) (μ := μ) hsource i)

end CoverIndexedCompactSupportTransitionSupportData

end CoverIndexedZeroBulkMeasure

end Stokes

end
