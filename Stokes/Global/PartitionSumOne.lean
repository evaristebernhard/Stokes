import Stokes.Global.FiniteActive
import Stokes.Global.Reconstruction

/-!
# Partition-of-unity coefficient sums on finite active sets

This file bridges mathlib's pointwise `SmoothPartitionOfUnity` sum-one API to
the project-local compact finite-active packages used by reconstruction.
-/

noncomputable section

open Set
open scoped BigOperators Manifold Topology

namespace Stokes

section PartitionSumOne

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}

namespace SmoothPartitionOfUnity

/--
On a partition of unity indexed over `univ`, the pointwise `finsupport` carries
the full coefficient sum.
-/
theorem sum_finsupport_univ
    (ρ : SmoothPartitionOfUnity M I M (Set.univ : Set M)) (x : M) :
    ∑ i ∈ ρ.finsupport x, ρ i x = 1 :=
  ρ.sum_finsupport x (Set.mem_univ x)

/--
Any finite set containing the pointwise `finsupport` has coefficient sum `1`.
-/
theorem sum_eq_one_of_finsupport_subset
    (ρ : SmoothPartitionOfUnity M I M (Set.univ : Set M))
    {active : Finset M} {x : M}
    (hactive : ρ.finsupport x ⊆ active) :
    ∑ i ∈ active, ρ i x = 1 :=
  ρ.sum_finsupport' x (Set.mem_univ x) hactive

/--
Any finite set containing the pointwise topological support contains enough
indices for the coefficient sum to be `1`.
-/
theorem sum_eq_one_of_fintsupport_subset
    (ρ : SmoothPartitionOfUnity M I M (Set.univ : Set M))
    {active : Finset M} {x : M}
    (hactive : ρ.fintsupport x ⊆ active) :
    ∑ i ∈ active, ρ i x = 1 :=
  sum_eq_one_of_finsupport_subset ρ
    ((ρ.finsupport_subset_fintsupport x).trans hactive)

end SmoothPartitionOfUnity

namespace FiniteActiveOnCompact

/--
The finite active set of a compact package has coefficient sum `1` at every
point of the controlled compact set.
-/
theorem coeff_sum_eq_one_on
    (P : FiniteActiveOnCompact (M := M) I) :
    ∀ x ∈ P.K, ∑ i ∈ P.active, P.partition i x = 1 := by
  intro x hx
  exact SmoothPartitionOfUnity.sum_eq_one_of_fintsupport_subset P.partition
    (P.fintsupport_subset_active hx)

/--
Pointwise reconstruction of a form from the compact finite-active localized
sum.
-/
theorem localizedFormSum_apply_eq_self_on
    (P : FiniteActiveOnCompact (M := M) I)
    (ω : ManifoldForm I M k) {x : M} (hx : x ∈ P.K) :
    localizedFormSum I P.active (fun i y => P.partition i y) ω x = ω x :=
  Stokes.localizedFormSum_apply_eq_self_on
    P.active (fun i y => P.partition i y) ω P.coeff_sum_eq_one_on hx

/--
Set-wise reconstruction of a form from the compact finite-active localized sum.
-/
theorem localizedFormSum_eqOn
    (P : FiniteActiveOnCompact (M := M) I)
    (ω : ManifoldForm I M k) :
    ∀ x ∈ P.K,
      localizedFormSum I P.active (fun i y => P.partition i y) ω x = ω x := by
  intro x hx
  exact P.localizedFormSum_apply_eq_self_on ω hx

end FiniteActiveOnCompact

namespace SelectedBoxPartitionOfUnity

variable [Preorder E]
variable {ω : ManifoldForm I M k}

/--
The selected-box package inherits the compact finite-active coefficient sum.
-/
theorem coeff_sum_eq_one_on
    (P : SelectedBoxPartitionOfUnity I ω) :
    ∀ x ∈ P.K, ∑ i ∈ P.active, P.partition i x = 1 :=
  P.toFiniteActiveOnCompact.coeff_sum_eq_one_on

/--
Pointwise reconstruction for the selected-box package, in the shape expected by
the reconstruction layer.
-/
theorem localizedFormSum_apply_eq_self_on
    (P : SelectedBoxPartitionOfUnity I ω) {x : M} (hx : x ∈ P.K) :
    localizedFormSum I P.active (fun i y => P.partition i y) ω x = ω x :=
  Stokes.localizedFormSum_apply_eq_self_on
    P.active (fun i y => P.partition i y) ω P.coeff_sum_eq_one_on hx

/--
Set-wise reconstruction for the selected-box package.
-/
theorem localizedFormSum_eqOn
    (P : SelectedBoxPartitionOfUnity I ω) :
    ∀ x ∈ P.K,
      localizedFormSum I P.active (fun i y => P.partition i y) ω x = ω x := by
  intro x hx
  exact P.localizedFormSum_apply_eq_self_on hx

end SelectedBoxPartitionOfUnity

end PartitionSumOne

end Stokes

end
