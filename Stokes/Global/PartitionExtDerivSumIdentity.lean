import Stokes.Global.BulkIntegrandAE

/-!
# Exterior derivative of a partition-localized finite sum

This file isolates the algebraic L5 step for the compact-support route:
once a finite localized sum agrees locally with the original form, the
exterior derivative of the original form is the finite sum of the exterior
derivatives of the localized pieces.

The proof deliberately avoids a product rule for `d(ρ • ω)`.  The localized
pieces are already the summands of `localizedFormSum`; we only use:

* `extDeriv` commutes with finite sums of differentiable chart representatives;
* `extDeriv` is local under `EventuallyEq`;
* `∑ ρᵢ = 1` on a support set containing `support ω` gives global equality of
  the localized sum with `ω`.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section ModelSumIdentity

universe u v w c

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}
variable {Chart : Type c}

/--
If the chart representative of the localized finite sum is eventually equal to
the chart representative of `ω`, then the sum of the chartwise exterior
derivatives of the localized pieces equals the chartwise exterior derivative of
`ω`.
-/
theorem sum_extDeriv_transitionPullbackInChart_localizedForm_eq_extDeriv_of_eventuallyEq
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M k) (x0 x1 : M) (y : E)
    (heq :
      ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I active coefficient ω) =ᶠ[𝓝 y]
        ManifoldForm.transitionPullbackInChart I x0 x1 ω)
    (hdiff :
      ∀ i ∈ active,
        DifferentiableAt Real
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω)) y) :
    (Finset.sum active fun i =>
        extDeriv
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω)) y) =
      extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y := by
  have hsum :=
    extDeriv_transitionPullbackInChart_localizedFormSum
      (I := I) active coefficient ω x0 x1 y hdiff
  calc
    (Finset.sum active fun i =>
        extDeriv
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω)) y)
        = extDeriv
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (localizedFormSum I active coefficient ω)) y := hsum.symm
    _ = extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y :=
        heq.extDeriv_eq

/--
Reverse-orientation version of
`sum_extDeriv_transitionPullbackInChart_localizedForm_eq_extDeriv_of_eventuallyEq`.
-/
theorem extDeriv_transitionPullbackInChart_eq_sum_localized_of_eventuallyEq
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M k) (x0 x1 : M) (y : E)
    (heq :
      ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I active coefficient ω) =ᶠ[𝓝 y]
        ManifoldForm.transitionPullbackInChart I x0 x1 ω)
    (hdiff :
      ∀ i ∈ active,
        DifferentiableAt Real
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω)) y) :
    extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y =
      Finset.sum active fun i =>
        extDeriv
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω)) y := by
  exact
    (sum_extDeriv_transitionPullbackInChart_localizedForm_eq_extDeriv_of_eventuallyEq
      (I := I) active coefficient ω x0 x1 y heq hdiff).symm

/--
Support-set version of the partition exterior-derivative identity.

The hypotheses are the natural compact-support ones: the coefficients sum to
`1` on a support set `K`, and the algebraic support of `ω` is contained in `K`.
The conclusion is global in chart coordinates because outside `K` both `ω` and
the finite localized sum vanish.
-/
theorem sum_extDeriv_localized_eq_extDeriv_of_coeff_sum_eq_one_on_support
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M k) {K : Set M}
    (hsum : ∀ x ∈ K, (Finset.sum active fun i => coefficient i x) = 1)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (x0 x1 : M) (y : E)
    (hdiff :
      ∀ i ∈ active,
        DifferentiableAt Real
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω)) y) :
    (Finset.sum active fun i =>
        extDeriv
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω)) y) =
      extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y := by
  let D :=
    LocalizedFormEventuallyEqData.ofCoeffSumEqOneOn
      (I := I) (ω := ω) active coefficient K hsum hωsupp
  exact
    sum_extDeriv_transitionPullbackInChart_localizedForm_eq_extDeriv_of_eventuallyEq
      (I := I) active coefficient ω x0 x1 y
      (D.transitionPullbackInChart_eventuallyEq_self x0 x1 y) hdiff

/-- Reverse form of the support-set partition exterior-derivative identity. -/
theorem extDeriv_transitionPullbackInChart_eq_sum_localized_of_coeff_sum_eq_one_on_support
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M k) {K : Set M}
    (hsum : ∀ x ∈ K, (Finset.sum active fun i => coefficient i x) = 1)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (x0 x1 : M) (y : E)
    (hdiff :
      ∀ i ∈ active,
        DifferentiableAt Real
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω)) y) :
    extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y =
      Finset.sum active fun i =>
        extDeriv
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω)) y := by
  exact
    (sum_extDeriv_localized_eq_extDeriv_of_coeff_sum_eq_one_on_support
      (I := I) active coefficient ω hsum hωsupp x0 x1 y hdiff).symm

end ModelSumIdentity

section SelectedPartition

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E] [Preorder E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}
variable {ω : ManifoldForm I M k}

namespace SelectedBoxPartitionOfUnity

/--
Selected-partition version of the chartwise exterior-derivative finite-sum
identity.
-/
theorem extDeriv_transitionPullbackInChart_eq_sum_localized_of_support_subset
    (P : SelectedBoxPartitionOfUnity I ω)
    (hωsupp : ManifoldForm.support I ω ⊆ P.K)
    (x0 x1 : M) (y : E)
    (hdiff :
      ∀ i ∈ P.active,
        DifferentiableAt Real
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (fun z => P.partition i z) ω)) y) :
    extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y =
      Finset.sum P.active fun i =>
        extDeriv
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (fun z => P.partition i z) ω)) y := by
  exact
    extDeriv_transitionPullbackInChart_eq_sum_localized_of_coeff_sum_eq_one_on_support
      (I := I) P.active (fun i z => P.partition i z) ω
      P.coeff_sum_eq_one_on hωsupp x0 x1 y hdiff

/--
The same selected-partition identity, oriented as a finite sum equaling the
global chartwise exterior derivative.
-/
theorem sum_extDeriv_transitionPullbackInChart_localizedForm_eq_extDeriv_of_support_subset
    (P : SelectedBoxPartitionOfUnity I ω)
    (hωsupp : ManifoldForm.support I ω ⊆ P.K)
    (x0 x1 : M) (y : E)
    (hdiff :
      ∀ i ∈ P.active,
        DifferentiableAt Real
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (fun z => P.partition i z) ω)) y) :
    (Finset.sum P.active fun i =>
        extDeriv
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (fun z => P.partition i z) ω)) y) =
      extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y := by
  exact
    (P.extDeriv_transitionPullbackInChart_eq_sum_localized_of_support_subset
      hωsupp x0 x1 y hdiff).symm

end SelectedBoxPartitionOfUnity

end SelectedPartition

section BulkScalar

universe u w c

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/--
Top-frame scalar version of the support-set identity, in the shape used by
bulk integrand reconstruction.
-/
theorem bulkIntegrand_eq_sum_localized_bulkIntegrand_of_coeff_sum_eq_one_on_support
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M n) {K : Set M}
    (hsum : ∀ x ∈ K, (Finset.sum active fun i => coefficient i x) = 1)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (x0 x1 : M) (y : Fin (n + 1) → Real)
    (hdiff :
      ∀ i ∈ active,
        DifferentiableAt Real
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω)) y) :
    bulkIntegrand I x0 x1 ω y =
      Finset.sum active fun i =>
        bulkIntegrand I x0 x1
          (ManifoldForm.localizedForm I (coefficient i) ω) y := by
  have h :=
    extDeriv_transitionPullbackInChart_eq_sum_localized_of_coeff_sum_eq_one_on_support
      (I := I) active coefficient ω hsum hωsupp x0 x1 y hdiff
  simpa [bulkIntegrand] using
    congrArg (fun η => η (standardTopFrame n)) h

/-- A.e. version of the scalar bulk-integrand finite-sum identity. -/
theorem bulkIntegrand_ae_eq_sum_localized_bulkIntegrand_of_coeff_sum_eq_one_on_support
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M n) {K : Set M}
    (hsum : ∀ x ∈ K, (Finset.sum active fun i => coefficient i x) = 1)
    (hωsupp : ManifoldForm.support I ω ⊆ K)
    (measure : Measure (Fin (n + 1) → Real)) (x0 x1 : M)
    (hdiff :
      ∀ᶠ y in ae measure,
        ∀ i ∈ active,
          DifferentiableAt Real
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (ManifoldForm.localizedForm I (coefficient i) ω)) y) :
    bulkIntegrand I x0 x1 ω =ᵐ[measure]
      fun y =>
        Finset.sum active fun i =>
          bulkIntegrand I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω) y := by
  exact hdiff.mono fun y hy =>
    bulkIntegrand_eq_sum_localized_bulkIntegrand_of_coeff_sum_eq_one_on_support
      (I := I) active coefficient ω hsum hωsupp x0 x1 y hy

end BulkScalar

end Stokes

end
