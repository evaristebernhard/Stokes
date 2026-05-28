import Stokes.Global.Partition
import Mathlib.Topology.Compactness.LocallyFinite

/-!
# Finite-active partition data on compact supports

This module isolates the compactness step in the global Stokes decomposition:
for a smooth partition of unity, only finitely many topological supports meet a
fixed compact support set.  The resulting finite active set is packaged without
choosing chart boxes, so later files can consume it before the local box
selection layer is available.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section FiniteActive

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
The chart indices whose partition term has topological support meeting `K`.
For compact `K`, this set is finite by local finiteness of topological supports.
-/
def finiteActiveSupportSet
    {I : ModelWithCorners Real E H}
    (ρ : SmoothPartitionOfUnity M I M univ) (K : Set M) : Set M :=
  {i | (tsupport (ρ i) ∩ K).Nonempty}

/--
Only finitely many topological supports of a smooth partition of unity meet a
compact set.
-/
theorem finiteActiveSupportSet_finite
    {I : ModelWithCorners Real E H}
    (ρ : SmoothPartitionOfUnity M I M univ)
    {K : Set M} (hK : IsCompact K) :
    (finiteActiveSupportSet ρ K).Finite :=
  ρ.toPartitionOfUnity.locallyFinite_tsupport.finite_nonempty_inter_compact hK

/--
A smooth partition of unity together with a compact support set and a finite
set of partition indices active on that compact set.

The field `active_of_mem_fintsupport` is intentionally a subset statement: it
allows later constructions to enlarge `active` when chart boxes or boundary
bookkeeping need extra indices.
-/
structure FiniteActiveOnCompact
    (I : ModelWithCorners Real E H) where
  /-- The smooth partition of unity used to localize global data. -/
  partition : SmoothPartitionOfUnity M I M univ
  /-- The compact support set on which finite activity is controlled. -/
  K : Set M
  /-- Compactness of the controlled support set. -/
  isCompact_K : IsCompact K
  /-- A finite set of chart/partition indices active over `K`. -/
  active : Finset M
  /-- Every partition term topologically active at a point of `K` lies in `active`. -/
  active_of_mem_fintsupport :
    ∀ ⦃x : M⦄, x ∈ K → partition.fintsupport x ⊆ active

namespace FiniteActiveOnCompact

variable {I : ModelWithCorners Real E H}

theorem isCompact (P : FiniteActiveOnCompact (M := M) I) :
    IsCompact P.K :=
  P.isCompact_K

theorem fintsupport_subset_active
    (P : FiniteActiveOnCompact (M := M) I) {x : M} (hx : x ∈ P.K) :
    P.partition.fintsupport x ⊆ P.active :=
  P.active_of_mem_fintsupport hx

theorem mem_active_of_mem_fintsupport
    (P : FiniteActiveOnCompact (M := M) I) {x i : M}
    (hx : x ∈ P.K) (hi : i ∈ P.partition.fintsupport x) :
    i ∈ P.active :=
  P.fintsupport_subset_active hx hi

theorem mem_active_of_mem_tsupport
    (P : FiniteActiveOnCompact (M := M) I) {x i : M}
    (hx : x ∈ P.K) (hi : x ∈ tsupport (P.partition i)) :
    i ∈ P.active :=
  P.mem_active_of_mem_fintsupport hx
    ((SmoothPartitionOfUnity.mem_fintsupport_iff P.partition x i).mpr hi)

theorem mem_active_of_tsupport_inter_K
    (P : FiniteActiveOnCompact (M := M) I) {i : M}
    (hi : (tsupport (P.partition i) ∩ P.K).Nonempty) :
    i ∈ P.active := by
  rcases hi with ⟨x, hxi, hxK⟩
  exact P.mem_active_of_mem_tsupport hxK hxi

theorem finiteActiveSupportSet_subset_active
    (P : FiniteActiveOnCompact (M := M) I) :
    finiteActiveSupportSet P.partition P.K ⊆ P.active := by
  intro i hi
  exact P.mem_active_of_tsupport_inter_K hi

/--
Constructor from an already chosen finite active set.  This keeps downstream
files independent of the concrete structure-field order.
-/
def mkOfActive
    (ρ : SmoothPartitionOfUnity M I M univ)
    (K : Set M) (hK : IsCompact K)
    (active : Finset M)
    (hactive : ∀ ⦃x : M⦄, x ∈ K → ρ.fintsupport x ⊆ active) :
    FiniteActiveOnCompact (M := M) I where
  partition := ρ
  K := K
  isCompact_K := hK
  active := active
  active_of_mem_fintsupport := hactive

/--
Canonical finite-active package associated to a compact set: `active` consists
exactly of those indices whose topological support meets `K`.
-/
def ofCompact
    (ρ : SmoothPartitionOfUnity M I M univ)
    (K : Set M) (hK : IsCompact K) :
    FiniteActiveOnCompact (M := M) I where
  partition := ρ
  K := K
  isCompact_K := hK
  active := (finiteActiveSupportSet_finite ρ hK).toFinset
  active_of_mem_fintsupport := by
    intro x hx i hi
    have hxi : x ∈ tsupport (ρ i) :=
      (SmoothPartitionOfUnity.mem_fintsupport_iff ρ x i).mp hi
    exact (Set.Finite.mem_toFinset _).mpr ⟨x, hxi, hx⟩

@[simp]
theorem ofCompact_partition
    (ρ : SmoothPartitionOfUnity M I M univ)
    (K : Set M) (hK : IsCompact K) :
    (ofCompact ρ K hK).partition = ρ :=
  rfl

@[simp]
theorem ofCompact_K
    (ρ : SmoothPartitionOfUnity M I M univ)
    (K : Set M) (hK : IsCompact K) :
    (ofCompact ρ K hK).K = K :=
  rfl

theorem mem_active_ofCompact_iff
    (ρ : SmoothPartitionOfUnity M I M univ)
    {K : Set M} (hK : IsCompact K) {i : M} :
    i ∈ (ofCompact ρ K hK).active ↔
      (tsupport (ρ i) ∩ K).Nonempty :=
  Set.Finite.mem_toFinset _

/--
Existence form of the compact finite-active construction.
-/
theorem exists_ofCompact
    (ρ : SmoothPartitionOfUnity M I M univ)
    (K : Set M) (hK : IsCompact K) :
    ∃ P : FiniteActiveOnCompact (M := M) I, P.partition = ρ ∧ P.K = K :=
  ⟨ofCompact ρ K hK, rfl, rfl⟩

section SelectedBoxes

variable [Preorder E]
variable {ω : ManifoldForm I M k}

/--
Add selected interior chart boxes to a finite-active package, producing the
existing global partition wrapper.
-/
def toSelectedBoxPartitionOfUnity
    (P : FiniteActiveOnCompact (M := M) I)
    (lower upper : M → E)
    (hbox :
      ∀ i ∈ P.active, interiorChartExtendedBox I i i ω (lower i) (upper i)) :
    SelectedBoxPartitionOfUnity I ω :=
  SelectedBoxPartitionOfUnity.mkOfBoxes P.partition P.K P.isCompact_K P.active
    P.active_of_mem_fintsupport lower upper hbox

/--
Variant of `toSelectedBoxPartitionOfUnity` using subset-style box hypotheses.
-/
def toSelectedBoxPartitionOfUnityOfSubsets
    (P : FiniteActiveOnCompact (M := M) I)
    (lower upper : M → E)
    (hle : ∀ i ∈ P.active, lower i ≤ upper i)
    (htarget :
      ∀ i ∈ P.active, Set.Icc (lower i) (upper i) ⊆ (extChartAt I i).target)
    (hoverlap :
      ∀ i ∈ P.active, Set.Icc (lower i) (upper i) ⊆ ManifoldForm.chartOverlap I i i)
    (hsupp :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          Set.Icc (lower i) (upper i))
    (U : M → Set E)
    (hUopen : ∀ i ∈ P.active, IsOpen (U i))
    (hUbox : ∀ i ∈ P.active, Set.Icc (lower i) (upper i) ⊆ U i)
    (hωU :
      ∀ i ∈ P.active,
        ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I i i ω) (U i)) :
    SelectedBoxPartitionOfUnity I ω :=
  SelectedBoxPartitionOfUnity.mkOfSubsets P.partition P.K P.isCompact_K P.active
    P.active_of_mem_fintsupport lower upper hle htarget hoverlap
    hsupp U hUopen hUbox hωU

end SelectedBoxes

end FiniteActiveOnCompact

namespace SelectedBoxPartitionOfUnity

variable [Preorder E]
variable {I : ModelWithCorners Real E H} {ω : ManifoldForm I M k}

/--
Forget the selected boxes, retaining only the finite-active compact-support
data.
-/
def toFiniteActiveOnCompact
    (P : SelectedBoxPartitionOfUnity I ω) :
    FiniteActiveOnCompact (M := M) I :=
  FiniteActiveOnCompact.mkOfActive P.partition P.K P.isCompact_K P.active
    P.active_of_mem_fintsupport

@[simp]
theorem toFiniteActiveOnCompact_partition
    (P : SelectedBoxPartitionOfUnity I ω) :
    P.toFiniteActiveOnCompact.partition = P.partition :=
  rfl

@[simp]
theorem toFiniteActiveOnCompact_K
    (P : SelectedBoxPartitionOfUnity I ω) :
    P.toFiniteActiveOnCompact.K = P.K :=
  rfl

@[simp]
theorem toFiniteActiveOnCompact_active
    (P : SelectedBoxPartitionOfUnity I ω) :
    P.toFiniteActiveOnCompact.active = P.active :=
  rfl

end SelectedBoxPartitionOfUnity

end FiniteActive

end Stokes

end
