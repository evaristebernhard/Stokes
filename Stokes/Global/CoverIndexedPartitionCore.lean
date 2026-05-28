import Stokes.Global.PartitionFormSumIdentity
import Stokes.Global.PartitionExtDerivSumIdentity
import Stokes.Global.SupportControlledSelectedPartition

/-!
# Cover-indexed partition reconstruction core

This file records the finite-cover-indexed partition identities used by the
compact-support globalization route.  The point is to work directly with an
arbitrary finite active cover index set `active : Finset ι`, rather than routing
through the older `SelectedBoxPartitionOfUnity : M` package.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedPointwise

universe uι uE uH uM

variable {ι : Type uι}
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}

/--
Finite-cover-indexed pointwise reconstruction of a manifold form from its
partition-localized pieces on a controlled set `K`.
-/
theorem coverIndexed_sum_localizedForm_eq_on
    (active : Finset ι) (ρ : ι → M → Real)
    (ω : ManifoldForm I M k) {K : Set M}
    (hsum : ∀ x ∈ K, (∑ i ∈ active, ρ i x) = 1) :
    ∀ x ∈ K,
      (∑ i ∈ active, ManifoldForm.localizedForm I (ρ i) ω x) = ω x := by
  exact ManifoldForm.sum_localizedForm_eq_on
    (I := I) active ρ ω hsum

/--
Fintype-indexed version of `coverIndexed_sum_localizedForm_eq_on`, using all
indices.
-/
theorem coverIndexed_univ_sum_localizedForm_eq_on
    [Fintype ι] (ρ : ι → M → Real)
    (ω : ManifoldForm I M k) {K : Set M}
    (hsum : ∀ x ∈ K, (∑ i : ι, ρ i x) = 1) :
    ∀ x ∈ K,
      (∑ i : ι, ManifoldForm.localizedForm I (ρ i) ω x) = ω x := by
  classical
  simpa using
    coverIndexed_sum_localizedForm_eq_on
      (I := I) (active := (Finset.univ : Finset ι)) ρ ω hsum

end CoverIndexedPointwise

section CoverIndexedExtDeriv

universe uι uE uH uM

variable {ι : Type uι}
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}

/--
Finite-cover-indexed chartwise exterior-derivative reconstruction, oriented as
the global derivative equaling the finite sum of localized derivatives.
-/
theorem coverIndexed_extDeriv_eq_sum_localized_of_support_subset
    (active : Finset ι) (ρ : ι → M → Real)
    (ω : ManifoldForm I M k) {K : Set M}
    (hsum : ∀ x ∈ K, (∑ i ∈ active, ρ i x) = 1)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (x0 x1 : M) (y : E)
    (hdiff :
      ∀ i ∈ active,
        DifferentiableAt Real
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (ρ i) ω)) y) :
    extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y =
      ∑ i ∈ active,
        extDeriv
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (ρ i) ω)) y := by
  exact
    extDeriv_transitionPullbackInChart_eq_sum_localized_of_coeff_sum_eq_one_on_support
      (I := I) active ρ ω hsum hωsupp x0 x1 y hdiff

/--
Finite-cover-indexed chartwise exterior-derivative reconstruction, oriented as
the localized finite sum equaling the global derivative.
-/
theorem coverIndexed_sum_extDeriv_localized_eq_extDeriv_of_support_subset
    (active : Finset ι) (ρ : ι → M → Real)
    (ω : ManifoldForm I M k) {K : Set M}
    (hsum : ∀ x ∈ K, (∑ i ∈ active, ρ i x) = 1)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (x0 x1 : M) (y : E)
    (hdiff :
      ∀ i ∈ active,
        DifferentiableAt Real
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (ρ i) ω)) y) :
    (∑ i ∈ active,
        extDeriv
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (ρ i) ω)) y) =
      extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y := by
  exact
    sum_extDeriv_localized_eq_extDeriv_of_coeff_sum_eq_one_on_support
      (I := I) active ρ ω hsum hωsupp x0 x1 y hdiff

end CoverIndexedExtDeriv

section CoverIndexedBulk

universe uι uH uM

variable {ι : Type uι}
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/--
Finite-cover-indexed scalar bulk-integrand reconstruction induced by the
chartwise exterior-derivative identity.
-/
theorem coverIndexed_bulkIntegrand_eq_sum_localized_of_support_subset
    (active : Finset ι) (ρ : ι → M → Real)
    (ω : ManifoldForm I M n) {K : Set M}
    (hsum : ∀ x ∈ K, (∑ i ∈ active, ρ i x) = 1)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (x0 x1 : M) (y : Fin (n + 1) → Real)
    (hdiff :
      ∀ i ∈ active,
        DifferentiableAt Real
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (ρ i) ω)) y) :
    bulkIntegrand I x0 x1 ω y =
      ∑ i ∈ active,
        bulkIntegrand I x0 x1
          (ManifoldForm.localizedForm I (ρ i) ω) y := by
  exact
    bulkIntegrand_eq_sum_localized_bulkIntegrand_of_coeff_sum_eq_one_on_support
      (I := I) active ρ ω hsum hωsupp x0 x1 y hdiff

/-- A.e. version of the finite-cover-indexed bulk-integrand reconstruction. -/
theorem coverIndexed_bulkIntegrand_ae_eq_sum_localized_of_support_subset
    (active : Finset ι) (ρ : ι → M → Real)
    (ω : ManifoldForm I M n) {K : Set M}
    (hsum : ∀ x ∈ K, (∑ i ∈ active, ρ i x) = 1)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (measure : Measure (Fin (n + 1) → Real)) (x0 x1 : M)
    (hdiff :
      ∀ᶠ y in ae measure,
        ∀ i ∈ active,
          DifferentiableAt Real
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (ManifoldForm.localizedForm I (ρ i) ω)) y) :
    bulkIntegrand I x0 x1 ω =ᵐ[measure]
      fun y =>
        ∑ i ∈ active,
          bulkIntegrand I x0 x1
            (ManifoldForm.localizedForm I (ρ i) ω) y := by
  exact
    bulkIntegrand_ae_eq_sum_localized_bulkIntegrand_of_coeff_sum_eq_one_on_support
      (I := I) active ρ ω hsum hωsupp measure x0 x1 hdiff

end CoverIndexedBulk

section SubtypeWrappers

universe uι uE uH uM

variable {ι : Type uι}
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}

namespace SmoothPartitionOfUnity

/--
Subtype-indexed partition reconstruction for the finite subtype `{i // i ∈ s}`.
-/
theorem coverIndexed_subtype_sum_localizedForm_eq_on
    {s : Finset ι} {K : Set M}
    (ρ : SmoothPartitionOfUnity {i // i ∈ s} I M K)
    (ω : ManifoldForm I M k) :
    ∀ x ∈ K,
      (∑ i : {i // i ∈ s},
          ManifoldForm.localizedForm I (fun y => ρ i y) ω x) = ω x := by
  classical
  exact
    coverIndexed_univ_sum_localizedForm_eq_on
      (I := I) (ρ := fun i y => ρ i y) ω
      (by
        intro x hx
        simpa [finsum_eq_sum_of_fintype] using
          (sum_eq_one_on_supportSet (I := I) ρ x hx))

/--
Subtype-indexed exterior-derivative reconstruction for the finite subtype
`{i // i ∈ s}`.
-/
theorem coverIndexed_subtype_extDeriv_eq_sum_localized_of_support_subset
    {s : Finset ι} {K : Set M}
    (ρ : SmoothPartitionOfUnity {i // i ∈ s} I M K)
    (ω : ManifoldForm I M k)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (x0 x1 : M) (y : E)
    (hdiff :
      ∀ i : {i // i ∈ s},
        DifferentiableAt Real
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (fun z => ρ i z) ω)) y) :
    extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y =
      ∑ i : {i // i ∈ s},
        extDeriv
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (fun z => ρ i z) ω)) y := by
  classical
  exact
    _root_.Stokes.coverIndexed_extDeriv_eq_sum_localized_of_support_subset
      (I := I) (active := (Finset.univ : Finset {i // i ∈ s}))
      (ρ := fun i z => ρ i z) ω
      (by
        intro x hx
        simpa [finsum_eq_sum_of_fintype] using
          (sum_eq_one_on_supportSet (I := I) ρ x hx))
      hωsupp x0 x1 y
      (by
        intro i _hi
        exact hdiff i)

end SmoothPartitionOfUnity

end SubtypeWrappers

section SubtypeBulkWrappers

universe uι uH uM

variable {ι : Type uι}
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

namespace SmoothPartitionOfUnity

/--
Subtype-indexed bulk-integrand reconstruction for the finite subtype
`{i // i ∈ s}`.
-/
theorem coverIndexed_subtype_bulkIntegrand_eq_sum_localized_of_support_subset
    {s : Finset ι} {K : Set M}
    (ρ : SmoothPartitionOfUnity {i // i ∈ s} I M K)
    (ω : ManifoldForm I M n)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (x0 x1 : M) (y : Fin (n + 1) → Real)
    (hdiff :
      ∀ i : {i // i ∈ s},
        DifferentiableAt Real
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (fun z => ρ i z) ω)) y) :
    bulkIntegrand I x0 x1 ω y =
      ∑ i : {i // i ∈ s},
        bulkIntegrand I x0 x1
          (ManifoldForm.localizedForm I (fun z => ρ i z) ω) y := by
  classical
  exact
    _root_.Stokes.coverIndexed_bulkIntegrand_eq_sum_localized_of_support_subset
      (I := I) (active := (Finset.univ : Finset {i // i ∈ s}))
      (ρ := fun i z => ρ i z) ω
      (by
        intro x hx
        simpa [finsum_eq_sum_of_fintype] using
          (sum_eq_one_on_supportSet (I := I) ρ x hx))
      hωsupp x0 x1 y
      (by
        intro i _hi
        exact hdiff i)

end SmoothPartitionOfUnity

end SubtypeBulkWrappers

section SupportControlledSelectedPartitionWrappers

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}

namespace SupportControlledSelectedPartition

/--
CoverIndex-indexed reconstruction for a support-controlled selected partition.
-/
theorem coverIndexed_sum_localizedForm_eq_on
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) :
    ∀ x ∈ K,
      (∑ j : C.CoverIndex,
          ManifoldForm.localizedForm I (fun y => P.partition j y) ω x) =
        ω x := by
  classical
  exact
    coverIndexed_univ_sum_localizedForm_eq_on
      (I := I) (ρ := fun j y => P.partition j y) ω
      P.finite_sum_eq_one

/--
CoverIndex-indexed exterior-derivative reconstruction for a
support-controlled selected partition.
-/
theorem coverIndexed_extDeriv_eq_sum_localized_of_support_subset
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (x0 x1 : M) (y : Fin (n + 1) → Real)
    (hdiff :
      ∀ j : C.CoverIndex,
        DifferentiableAt Real
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (fun z => P.partition j z) ω)) y) :
    extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y =
      ∑ j : C.CoverIndex,
        extDeriv
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (fun z => P.partition j z) ω)) y := by
  classical
  exact
    _root_.Stokes.coverIndexed_extDeriv_eq_sum_localized_of_support_subset
      (I := I) (active := (Finset.univ : Finset C.CoverIndex))
      (ρ := fun j z => P.partition j z) ω
      P.finite_sum_eq_one hωsupp x0 x1 y
      (by
        intro j _hj
        exact hdiff j)

/--
CoverIndex-indexed bulk-integrand reconstruction for a support-controlled
selected partition.
-/
theorem coverIndexed_bulkIntegrand_eq_sum_localized_of_support_subset
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (x0 x1 : M) (y : Fin (n + 1) → Real)
    (hdiff :
      ∀ j : C.CoverIndex,
        DifferentiableAt Real
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (fun z => P.partition j z) ω)) y) :
    bulkIntegrand I x0 x1 ω y =
      ∑ j : C.CoverIndex,
        bulkIntegrand I x0 x1
          (ManifoldForm.localizedForm I (fun z => P.partition j z) ω) y := by
  classical
  exact
    _root_.Stokes.coverIndexed_bulkIntegrand_eq_sum_localized_of_support_subset
      (I := I) (active := (Finset.univ : Finset C.CoverIndex))
      (ρ := fun j z => P.partition j z) ω
      P.finite_sum_eq_one hωsupp x0 x1 y
      (by
        intro j _hj
        exact hdiff j)

end SupportControlledSelectedPartition

end SupportControlledSelectedPartitionWrappers

end Stokes

end
