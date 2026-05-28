import Stokes.Global.InteriorChart
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Global partition packages with selected chart boxes

This module is a small bookkeeping layer for the future global Stokes
decomposition.  It packages a smooth partition of unity, a compact support set
`K`, a finite set of chart indices active over `K`, and one selected interior
chart box for each active index.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section GlobalPartition

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E] [Preorder E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
A smooth partition of unity together with a finite family of selected chart
boxes sufficient for a compact support set `K`.

The field `active_of_mem_fintsupport` is the finite-activity statement used by
later global integration sums: at every point of `K`, every partition term whose
topological support contains the point has an index in `active`.
-/
structure SelectedBoxPartitionOfUnity
    (I : ModelWithCorners Real E H) (ω : ManifoldForm I M k) where
  /-- The smooth partition of unity used to localize the global form. -/
  partition : SmoothPartitionOfUnity M I M univ
  /-- The compact support set on which the global decomposition is controlled. -/
  K : Set M
  /-- Compactness of the support set. -/
  isCompact_K : IsCompact K
  /-- The finite set of chart indices needed over `K`. -/
  active : Finset M
  /-- Every partition term topologically active at a point of `K` is in `active`. -/
  active_of_mem_fintsupport :
    ∀ ⦃x : M⦄, x ∈ K → partition.fintsupport x ⊆ active
  /-- Lower corner of the selected coordinate box for each chart index. -/
  lower : M → E
  /-- Upper corner of the selected coordinate box for each chart index. -/
  upper : M → E
  /-- Selected extended chart boxes for all active chart indices. -/
  box :
    ∀ i ∈ active, interiorChartExtendedBox I i i ω (lower i) (upper i)

namespace SelectedBoxPartitionOfUnity

variable {I : ModelWithCorners Real E H} {ω : ManifoldForm I M k}

theorem isCompact (P : SelectedBoxPartitionOfUnity I ω) :
    IsCompact P.K :=
  P.isCompact_K

theorem mem_active_of_mem_fintsupport
    (P : SelectedBoxPartitionOfUnity I ω) {x i : M}
    (hx : x ∈ P.K) (hi : i ∈ P.partition.fintsupport x) :
    i ∈ P.active :=
  P.active_of_mem_fintsupport hx hi

theorem mem_active_of_mem_tsupport
    (P : SelectedBoxPartitionOfUnity I ω) {x i : M}
    (hx : x ∈ P.K) (hi : x ∈ tsupport (P.partition i)) :
    i ∈ P.active :=
  P.mem_active_of_mem_fintsupport hx
    ((SmoothPartitionOfUnity.mem_fintsupport_iff P.partition x i).mpr hi)

theorem extendedBox
    (P : SelectedBoxPartitionOfUnity I ω) {i : M} (hi : i ∈ P.active) :
    interiorChartExtendedBox I i i ω (P.lower i) (P.upper i) :=
  P.box i hi

theorem selectedBox
    (P : SelectedBoxPartitionOfUnity I ω) {i : M} (hi : i ∈ P.active) :
    interiorChartSelectedBox I i i ω (P.lower i) (P.upper i) :=
  (P.extendedBox hi).selectedBox

theorem le
    (P : SelectedBoxPartitionOfUnity I ω) {i : M} (hi : i ∈ P.active) :
    P.lower i ≤ P.upper i :=
  (P.selectedBox hi).le

theorem Icc_subset_domain
    (P : SelectedBoxPartitionOfUnity I ω) {i : M} (hi : i ∈ P.active) :
    Set.Icc (P.lower i) (P.upper i) ⊆ interiorChartDomain I i i :=
  (P.selectedBox hi).Icc_subset_domain

theorem tsupport_subset_Icc
    (P : SelectedBoxPartitionOfUnity I ω) {i : M} (hi : i ∈ P.active) :
    tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
      Set.Icc (P.lower i) (P.upper i) :=
  (P.selectedBox hi).tsupport_subset

theorem exists_smooth_nhds
    (P : SelectedBoxPartitionOfUnity I ω) {i : M} (hi : i ∈ P.active) :
    ∃ U : Set E,
      IsOpen U ∧ Set.Icc (P.lower i) (P.upper i) ⊆ U ∧
        ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I i i ω) U :=
  (P.extendedBox hi).exists_smooth_nhds

/--
Constructor from already selected extended boxes.  This keeps downstream files
independent of the concrete structure-field order.
-/
def mkOfBoxes
    (ρ : SmoothPartitionOfUnity M I M univ)
    (K : Set M) (hK : IsCompact K)
    (active : Finset M)
    (hactive : ∀ ⦃x : M⦄, x ∈ K → ρ.fintsupport x ⊆ active)
    (lower upper : M → E)
    (hbox :
      ∀ i ∈ active, interiorChartExtendedBox I i i ω (lower i) (upper i)) :
    SelectedBoxPartitionOfUnity I ω where
  partition := ρ
  K := K
  isCompact_K := hK
  active := active
  active_of_mem_fintsupport := hactive
  lower := lower
  upper := upper
  box := hbox

/--
Constructor from the subset-style hypotheses used by
`interiorChartExtendedBox.mk_of_subsets`.
-/
def mkOfSubsets
    (ρ : SmoothPartitionOfUnity M I M univ)
    (K : Set M) (hK : IsCompact K)
    (active : Finset M)
    (hactive : ∀ ⦃x : M⦄, x ∈ K → ρ.fintsupport x ⊆ active)
    (lower upper : M → E)
    (hle : ∀ i ∈ active, lower i ≤ upper i)
    (htarget :
      ∀ i ∈ active, Set.Icc (lower i) (upper i) ⊆ (extChartAt I i).target)
    (hoverlap :
      ∀ i ∈ active, Set.Icc (lower i) (upper i) ⊆ ManifoldForm.chartOverlap I i i)
    (hsupp :
      ∀ i ∈ active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          Set.Icc (lower i) (upper i))
    (U : M → Set E)
    (hUopen : ∀ i ∈ active, IsOpen (U i))
    (hUbox : ∀ i ∈ active, Set.Icc (lower i) (upper i) ⊆ U i)
    (hωU :
      ∀ i ∈ active,
        ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I i i ω) (U i)) :
    SelectedBoxPartitionOfUnity I ω :=
  mkOfBoxes ρ K hK active hactive lower upper fun i hi =>
    interiorChartExtendedBox.mk_of_subsets
      (hle i hi) (htarget i hi) (hoverlap i hi) (hsupp i hi)
      (hUopen i hi) (hUbox i hi) (hωU i hi)

end SelectedBoxPartitionOfUnity

end GlobalPartition

section SmoothPartitionExistence

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Mathlib's smooth partition-of-unity theorem specialized to chart sources.  This
does not choose boxes; it is the upstream existence ingredient that can later be
combined with compactness and local box-selection lemmas.
-/
theorem exists_smoothPartitionOfUnity_subordinate_chartAt_source
    (I : ModelWithCorners Real E H)
    [FiniteDimensional Real E] [IsManifold I ⊤ M] [T2Space M]
    [SigmaCompactSpace M] :
    ∃ ρ : SmoothPartitionOfUnity M I M univ,
      ρ.IsSubordinate (fun x => (chartAt H x).source) :=
  SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M

end SmoothPartitionExistence

end Stokes

end
