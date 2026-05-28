import Stokes.Global.CoverIndexedBulkNaturalConstructor

/-!
# Cover-indexed bulk a.e. differentiability constructors

The represented compact-support route uses one a.e. differentiability field on
the bulk side, only to reconstruct the global scalar bulk integrand from the
finite sum of localized pieces.  Geometrically this field should come from the
same chartwise smoothness neighborhoods that already produce bulk continuity.

This file packages that reduction.  The key hypothesis is intentionally
measure-theoretic: each smoothness neighborhood must contain `μ`-a.e. point.
For the eventual compact-support route this is the precise place where a
global measure-domain statement, or a per-index assigned-chart redesign, must
enter.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section GenericDifferentiabilityAE

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
  [MeasurableSpace E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace Real F]
variable {m : WithTop ℕ∞}
variable {μ : Measure E}

/--
If a function is `C^m` on an open set and that open set contains a.e. point,
then the function is differentiable a.e.
-/
theorem eventually_differentiableAt_of_contDiffOn_isOpen_ae_mem
    {f : E → F} {U : Set E}
    (hU : IsOpen U)
    (hmem : ∀ᶠ y in ae μ, y ∈ U)
    (hf : ContDiffOn Real m f U)
    (hm : m ≠ 0) :
    ∀ᶠ y in ae μ, DifferentiableAt Real f y := by
  filter_upwards [hmem] with y hy
  exact (hf.contDiffAt (hU.mem_nhds hy)).differentiableAt hm

/-- Global `ContDiffOn` on `univ` gives differentiability a.e. for any measure. -/
theorem eventually_differentiableAt_of_contDiffOn_univ
    {f : E → F}
    (hf : ContDiffOn Real m f univ)
    (hm : m ≠ 0) :
    ∀ᶠ y in ae μ, DifferentiableAt Real f y := by
  exact
    eventually_differentiableAt_of_contDiffOn_isOpen_ae_mem
      (μ := μ) isOpen_univ (Eventually.of_forall fun _ => mem_univ _)
      hf hm

/-- `C^\infty` on `univ` gives differentiability a.e. for any measure. -/
theorem eventually_differentiableAt_of_contDiffOn_univ_infty
    {f : E → F}
    (hf : ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞) f univ) :
    ∀ᶠ y in ae μ, DifferentiableAt Real f y :=
  eventually_differentiableAt_of_contDiffOn_univ (μ := μ) hf (by simp)

end GenericDifferentiabilityAE

section CoverIndexedBulkDifferentiabilityAE

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

/-- The exact a.e. differentiability field consumed by coordinate bulk data. -/
abbrev CoverIndexedBulkDifferentiabilityAEField
    (sourceChart targetChart : M) : Prop :=
  ∀ᶠ y in ae μBulk,
    ∀ j : C.CoverIndex,
      DifferentiableAt Real
        (ManifoldForm.transitionPullbackInChart I sourceChart targetChart
          (P.coverIndexLocalizedForm ω j)) y

/--
Generate the cover-indexed bulk differentiability-a.e. field from smoothness on
open sets that contain a.e. point.
-/
theorem coverIndex_piece_differentiable_ae_of_contDiffOn_isOpen_ae_mem
    {m : WithTop ℕ∞}
    (sourceChart targetChart : M)
    (smoothSet : C.CoverIndex → Set (Fin (n + 1) → Real))
    (isOpen_smoothSet :
      ∀ j : C.CoverIndex, IsOpen (smoothSet j))
    (ae_mem_smoothSet :
      ∀ j : C.CoverIndex,
        ∀ᶠ y in ae μBulk, y ∈ smoothSet j)
    (localized_contDiffOn :
      ∀ j : C.CoverIndex,
        ContDiffOn Real m
          (ManifoldForm.transitionPullbackInChart I sourceChart targetChart
            (P.coverIndexLocalizedForm ω j)) (smoothSet j))
    (hm : m ≠ 0) :
    CoverIndexedBulkDifferentiabilityAEField
      (I := I) (K := K) (ω := ω) (C := C) (P := P) (μBulk := μBulk)
      sourceChart targetChart := by
  classical
  have hdiff_j :
      ∀ j : C.CoverIndex,
        ∀ᶠ y in ae μBulk,
          DifferentiableAt Real
            (ManifoldForm.transitionPullbackInChart I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j)) y := by
    intro j
    exact
      eventually_differentiableAt_of_contDiffOn_isOpen_ae_mem
        (μ := μBulk)
        (isOpen_smoothSet j) (ae_mem_smoothSet j)
        (localized_contDiffOn j) hm
  have hfinite :
      ∀ᶠ y in ae μBulk,
        ∀ j ∈ (Finset.univ : Finset C.CoverIndex),
          DifferentiableAt Real
            (ManifoldForm.transitionPullbackInChart I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j)) y := by
    rw [Filter.eventually_all_finset]
    intro j _hj
    exact hdiff_j j
  filter_upwards [hfinite] with y hy
  intro j
  exact hy j (Finset.mem_univ j)

/-- `C^\infty` version of `coverIndex_piece_differentiable_ae_of_contDiffOn_isOpen_ae_mem`. -/
theorem coverIndex_piece_differentiable_ae_of_contDiffOn_isOpen_ae_mem_infty
    (sourceChart targetChart : M)
    (smoothSet : C.CoverIndex → Set (Fin (n + 1) → Real))
    (isOpen_smoothSet :
      ∀ j : C.CoverIndex, IsOpen (smoothSet j))
    (ae_mem_smoothSet :
      ∀ j : C.CoverIndex,
        ∀ᶠ y in ae μBulk, y ∈ smoothSet j)
    (localized_contDiffOn :
      ∀ j : C.CoverIndex,
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.transitionPullbackInChart I sourceChart targetChart
            (P.coverIndexLocalizedForm ω j)) (smoothSet j)) :
    CoverIndexedBulkDifferentiabilityAEField
      (I := I) (K := K) (ω := ω) (C := C) (P := P) (μBulk := μBulk)
      sourceChart targetChart :=
  coverIndex_piece_differentiable_ae_of_contDiffOn_isOpen_ae_mem
    (I := I) (K := K) (ω := ω) (C := C) (P := P) (μBulk := μBulk)
    sourceChart targetChart smoothSet isOpen_smoothSet ae_mem_smoothSet
    localized_contDiffOn (by simp)

/--
Generate the bulk differentiability-a.e. field from chartwise smooth localized
forms, on explicitly chosen open working sets.
-/
theorem coverIndex_piece_differentiable_ae_of_localizedChartwiseSmooth
    [IsManifold I ⊤ M]
    (sourceChart targetChart : M)
    (smoothSet : C.CoverIndex → Set (Fin (n + 1) → Real))
    (isOpen_smoothSet :
      ∀ j : C.CoverIndex, IsOpen (smoothSet j))
    (ae_mem_smoothSet :
      ∀ j : C.CoverIndex,
        ∀ᶠ y in ae μBulk, y ∈ smoothSet j)
    (smoothSet_subset_sourceTarget :
      ∀ j : C.CoverIndex,
        smoothSet j ⊆ (extChartAt I sourceChart).target)
    (smoothSet_subset_overlap :
      ∀ j : C.CoverIndex,
        smoothSet j ⊆ ManifoldForm.chartOverlap I sourceChart targetChart)
    (localizedChartwiseSmooth :
      ∀ j : C.CoverIndex,
        ManifoldForm.ChartwiseSmooth I (P.coverIndexLocalizedForm ω j)) :
    CoverIndexedBulkDifferentiabilityAEField
      (I := I) (K := K) (ω := ω) (C := C) (P := P) (μBulk := μBulk)
      sourceChart targetChart :=
  coverIndex_piece_differentiable_ae_of_contDiffOn_isOpen_ae_mem
    (I := I) (K := K) (ω := ω) (C := C) (P := P) (μBulk := μBulk)
    sourceChart targetChart smoothSet isOpen_smoothSet ae_mem_smoothSet
    (fun j =>
      (localizedChartwiseSmooth j).contDiffOn_transitionPullbackInChart_of_chartAPI
        (I := I) sourceChart targetChart
        (smoothSet_subset_sourceTarget j) (smoothSet_subset_overlap j))
    (by simp)

namespace SupportControlledSelectedPartition

namespace CoverIndexedBulkSmoothnessFields

/--
The bulk smoothness package already carries open smoothness neighborhoods.
Once those neighborhoods are known to contain a.e. point, it supplies the exact
`piece_differentiable_ae` field required by `CoverIndexedCoordinateBulkData`.
-/
theorem piece_differentiable_ae_of_ae_mem
    {sourceChart targetChart : M}
    (D : CoverIndexedBulkSmoothnessFields (C := C) P ω sourceChart targetChart)
    (ae_mem_smoothSet :
      ∀ j : C.CoverIndex,
        ∀ᶠ y in ae μBulk, y ∈ D.smoothSet j) :
    CoverIndexedBulkDifferentiabilityAEField
      (I := I) (K := K) (ω := ω) (C := C) (P := P) (μBulk := μBulk)
      sourceChart targetChart :=
  coverIndex_piece_differentiable_ae_of_contDiffOn_isOpen_ae_mem
    (I := I) (K := K) (ω := ω) (C := C) (P := P) (μBulk := μBulk)
    sourceChart targetChart D.smoothSet D.isOpen_smoothSet
    ae_mem_smoothSet D.localized_contDiffOn (by simp)

end CoverIndexedBulkSmoothnessFields

end SupportControlledSelectedPartition

namespace CoverIndexedCoordinateBulkData

/--
Coordinate bulk data from bulk smoothness plus an a.e.-domain statement for the
smoothness neighborhoods.  This eliminates the manual `piece_differentiable_ae`
field whenever the selected coordinate domains are known to contain a.e. point.
-/
def ofBulkSmoothnessAEDomain
    (sourceChart targetChart : M)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, bulkIntegrand I sourceChart targetChart ω y ∂μBulk)
    (formSupport_subset : ManifoldForm.support I ω ⊆ K)
    (smooth :
      SupportControlledSelectedPartition.CoverIndexedBulkSmoothnessFields
        (C := C) P ω sourceChart targetChart)
    (ae_mem_smoothSet :
      ∀ j : C.CoverIndex,
        ∀ᶠ y in ae μBulk, y ∈ smooth.smoothSet j)
    (piece_tsupport_subset_assigned :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I sourceChart targetChart
                (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_assigned :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in C.assignedCoordinateBox j,
            bulkIntegrand I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j) y ∂μBulk) :
    CoverIndexedCoordinateBulkData
      (I := I) (K := K) C P ω μBulk :=
  CoverIndexedCoordinateBulkData.ofBulkSmoothness
    (C := C) (P := P) (ω := ω) (μBulk := μBulk)
    sourceChart targetChart globalIntegral globalIntegral_eq_integral
    formSupport_subset smooth piece_tsupport_subset_assigned
    localBulk_eq_setIntegral_assigned
    (smooth.piece_differentiable_ae_of_ae_mem
      (I := I) (K := K) (ω := ω) (C := C) (P := P) (μBulk := μBulk)
      ae_mem_smoothSet)

end CoverIndexedCoordinateBulkData

namespace SupportControlledSelectedPartition

/--
Canonical coordinate bulk data from natural bulk smoothness and a.e. coverage
of the smoothness neighborhoods.
-/
def coordinateBulkData_of_bulkSmoothnessAEDomain
    (P : SupportControlledSelectedPartition C)
    (sourceChart targetChart : M)
    (globalBulkIntegral : Real)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral =
        ∫ y, bulkIntegrand I sourceChart targetChart ω y ∂μBulk)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (smooth :
      CoverIndexedBulkSmoothnessFields (C := C) P ω sourceChart targetChart)
    (ae_mem_smoothSet :
      ∀ j : C.CoverIndex,
        ∀ᶠ y in ae μBulk, y ∈ smooth.smoothSet j)
    (piece_tsupport_subset_assigned :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I sourceChart targetChart
                (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_assigned :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in C.assignedCoordinateBox j,
            bulkIntegrand I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j) y ∂μBulk) :
    CoverIndexedCoordinateBulkData
      (I := I) (K := K) C P ω μBulk :=
  CoverIndexedCoordinateBulkData.ofBulkSmoothnessAEDomain
    (C := C) (P := P) (ω := ω) (μBulk := μBulk)
    sourceChart targetChart globalBulkIntegral
    globalBulkIntegral_eq_integral hωsupp smooth ae_mem_smoothSet
    piece_tsupport_subset_assigned localBulk_eq_setIntegral_assigned

/--
Closed-carrier bulk data from natural bulk smoothness and a.e. coverage of the
smoothness neighborhoods.
-/
def coordinateClosedCarrierBulkData_of_bulkSmoothnessAEDomain
    [IsFiniteMeasureOnCompacts μBulk]
    (P : SupportControlledSelectedPartition C)
    (sourceChart targetChart : M)
    (globalBulkIntegral : Real)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral =
        ∫ y, bulkIntegrand I sourceChart targetChart ω y ∂μBulk)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (smooth :
      CoverIndexedBulkSmoothnessFields (C := C) P ω sourceChart targetChart)
    (ae_mem_smoothSet :
      ∀ j : C.CoverIndex,
        ∀ᶠ y in ae μBulk, y ∈ smooth.smoothSet j)
    (piece_tsupport_subset_assigned :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I sourceChart targetChart
                (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_assigned :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in C.assignedCoordinateBox j,
            bulkIntegrand I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j) y ∂μBulk) :
    CoverIndexedClosedCarrierBulkData
      (I := I) (K := K) (μBulk := μBulk) C P ω :=
  (P.coordinateBulkData_of_bulkSmoothnessAEDomain
    (ω := ω) (μBulk := μBulk)
    sourceChart targetChart globalBulkIntegral
    globalBulkIntegral_eq_integral hωsupp smooth ae_mem_smoothSet
    piece_tsupport_subset_assigned localBulk_eq_setIntegral_assigned
    ).toClosedCarrierBulkData

/--
Resolved bulk fields from natural bulk smoothness and a.e. coverage of the
smoothness neighborhoods.
-/
def coordinateResolvedBulkFields_of_bulkSmoothnessAEDomain
    [IsFiniteMeasureOnCompacts μBulk]
    (P : SupportControlledSelectedPartition C)
    (sourceChart targetChart : M)
    (globalBulkIntegral : Real)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral =
        ∫ y, bulkIntegrand I sourceChart targetChart ω y ∂μBulk)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (smooth :
      CoverIndexedBulkSmoothnessFields (C := C) P ω sourceChart targetChart)
    (ae_mem_smoothSet :
      ∀ j : C.CoverIndex,
        ∀ᶠ y in ae μBulk, y ∈ smooth.smoothSet j)
    (piece_tsupport_subset_assigned :
      ∀ j : C.CoverIndex,
        tsupport
            (fun y =>
              bulkIntegrand I sourceChart targetChart
                (P.coverIndexLocalizedForm ω j) y) ⊆
          C.assignedCoordinateBox j)
    (localBulk_eq_setIntegral_assigned :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in C.assignedCoordinateBox j,
            bulkIntegrand I sourceChart targetChart
              (P.coverIndexLocalizedForm ω j) y ∂μBulk) :
    CoverIndexedResolvedBulkFields
      (C := C) (ω := ω)
      (αBulk := Fin (n + 1) → Real) (μBulk := μBulk) P :=
  (P.coordinateClosedCarrierBulkData_of_bulkSmoothnessAEDomain
    (ω := ω) (μBulk := μBulk)
    sourceChart targetChart globalBulkIntegral
    globalBulkIntegral_eq_integral hωsupp smooth ae_mem_smoothSet
    piece_tsupport_subset_assigned localBulk_eq_setIntegral_assigned
    ).toResolvedBulkFields

end SupportControlledSelectedPartition

end CoverIndexedBulkDifferentiabilityAE

end Stokes

end
