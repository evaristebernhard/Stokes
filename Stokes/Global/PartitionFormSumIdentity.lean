import Stokes.Global.PartitionSumOne

/-!
# Finite partition identities for localized manifold forms

This file records the pointwise and a.e. algebraic identities behind the
partition-of-unity reconstruction step.  The statements are deliberately about
the honest finite sum of localized forms, so measure-localization files can use
them without unfolding the `localizedFormSum` abbreviation by hand.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

universe u v w c

section DirectFiniteSum

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}
variable {Chart : Type c}

namespace ManifoldForm

/-- At one point, the raw finite sum of localized forms is scalar
multiplication by the coefficient sum at that point. -/
theorem sum_localizedForm_apply_eq_coeff_sum_smul
    (s : Finset Chart) (rho : Chart -> M -> Real)
    (omega : ManifoldForm I M k) (x : M) :
    (Finset.sum s fun i => ManifoldForm.localizedForm I (rho i) omega x) =
      (Finset.sum s fun i => rho i x) • omega x := by
  simpa [localizedFormSum] using
    (Stokes.localizedFormSum_apply_eq_coeff_sum_smul
      (I := I) (active := s) (ρ := rho) (ω := omega) x)

/-- Raw pointwise finite-sum reconstruction from a coefficient sum equal to
`1` at the chosen point. -/
theorem sum_localizedForm_apply_eq_self_of_coeff_sum_eq_one
    (s : Finset Chart) (rho : Chart -> M -> Real)
    (omega : ManifoldForm I M k) {x : M}
    (hsum : (Finset.sum s fun i => rho i x) = 1) :
    (Finset.sum s fun i => ManifoldForm.localizedForm I (rho i) omega x) =
      omega x := by
  simpa [localizedFormSum] using
    (Stokes.localizedFormSum_apply_eq_self_of_coeff_sum_eq_one
      (I := I) (active := s) (ρ := rho) (ω := omega) hsum)

/-- Reconstruction on a set `K`, in the direct raw finite-sum shape. -/
theorem sum_localizedForm_eq_on
    (s : Finset Chart) (rho : Chart -> M -> Real)
    (omega : ManifoldForm I M k) {K : Set M}
    (hsum : ∀ x ∈ K, (Finset.sum s fun i => rho i x) = 1) :
    ∀ x ∈ K,
      (Finset.sum s fun i => ManifoldForm.localizedForm I (rho i) omega x) =
        omega x := by
  intro x hx
  exact sum_localizedForm_apply_eq_self_of_coeff_sum_eq_one
    (I := I) s rho omega (hsum x hx)

/-- A support-restricted alias for `sum_localizedForm_eq_on`, useful when
`K` is the compact support set carried by a global Stokes package. -/
theorem sum_localizedForm_eq_on_supportSet
    (s : Finset Chart) (rho : Chart -> M -> Real)
    (omega : ManifoldForm I M k) (supportSet : Set M)
    (hsum : ∀ x ∈ supportSet, (Finset.sum s fun i => rho i x) = 1) :
    ∀ x ∈ supportSet,
      (Finset.sum s fun i => ManifoldForm.localizedForm I (rho i) omega x) =
        omega x :=
  sum_localizedForm_eq_on (I := I) s rho omega hsum

/-- A.e. finite-sum reconstruction from an a.e. coefficient-sum identity. -/
theorem sum_localizedForm_ae_eq_self_of_coeff_sum_eq_one_ae
    (s : Finset Chart) (rho : Chart -> M -> Real)
    (omega : ManifoldForm I M k) [MeasurableSpace M] {mu : Measure M}
    (hsum : ∀ᵐ x ∂mu, (Finset.sum s fun i => rho i x) = 1) :
    ∀ᵐ x ∂mu,
      (Finset.sum s fun i => ManifoldForm.localizedForm I (rho i) omega x) =
        omega x :=
  hsum.mono fun _x hx =>
    sum_localizedForm_apply_eq_self_of_coeff_sum_eq_one
      (I := I) s rho omega hx

/-- A.e. reconstruction on a measure carried by a controlled set `K`. -/
theorem sum_localizedForm_ae_eq_self_of_ae_mem
    (s : Finset Chart) (rho : Chart -> M -> Real)
    (omega : ManifoldForm I M k) [MeasurableSpace M] {K : Set M} {mu : Measure M}
    (hmuK : ∀ᵐ x ∂mu, x ∈ K)
    (hsum : ∀ x ∈ K, (Finset.sum s fun i => rho i x) = 1) :
    ∀ᵐ x ∂mu,
      (Finset.sum s fun i => ManifoldForm.localizedForm I (rho i) omega x) =
        omega x :=
  hmuK.mono fun x hx =>
    sum_localizedForm_apply_eq_self_of_coeff_sum_eq_one
      (I := I) s rho omega (hsum x hx)

end ManifoldForm

end DirectFiniteSum

section FiniteActivePackages

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}

namespace FiniteActiveOnCompact

/-- Direct raw finite-sum reconstruction for a compact finite-active
partition package. -/
theorem sum_localizedForm_eq_on
    (P : FiniteActiveOnCompact (M := M) I) (omega : ManifoldForm I M k) :
    ∀ x ∈ P.K,
      (Finset.sum P.active fun i =>
          ManifoldForm.localizedForm I (fun y => P.partition i y) omega x) =
        omega x := by
  exact ManifoldForm.sum_localizedForm_eq_on
    (I := I) P.active (fun i y => P.partition i y) omega
    P.coeff_sum_eq_one_on

/-- Pointwise direct reconstruction for a finite-active package. -/
theorem sum_localizedForm_apply_eq_self_on
    (P : FiniteActiveOnCompact (M := M) I) (omega : ManifoldForm I M k)
    {x : M} (hx : x ∈ P.K) :
    (Finset.sum P.active fun i =>
        ManifoldForm.localizedForm I (fun y => P.partition i y) omega x) =
      omega x :=
  P.sum_localizedForm_eq_on omega x hx

/-- A.e. direct reconstruction for measures carried by the compact finite
active support set. -/
theorem sum_localizedForm_ae_eq_self_of_ae_mem
    (P : FiniteActiveOnCompact (M := M) I) (omega : ManifoldForm I M k)
    [MeasurableSpace M] {mu : Measure M} (hmuK : ∀ᵐ x ∂mu, x ∈ P.K) :
    ∀ᵐ x ∂mu,
      (Finset.sum P.active fun i =>
          ManifoldForm.localizedForm I (fun y => P.partition i y) omega x) =
        omega x :=
  ManifoldForm.sum_localizedForm_ae_eq_self_of_ae_mem
    (I := I) P.active (fun i y => P.partition i y) omega hmuK
    P.coeff_sum_eq_one_on

end FiniteActiveOnCompact

namespace SelectedBoxPartitionOfUnity

variable [Preorder E]
variable {omega : ManifoldForm I M k}

/-- Direct raw finite-sum reconstruction for a selected-box partition
package. -/
theorem sum_localizedForm_eq_on
    (P : SelectedBoxPartitionOfUnity I omega) :
    ∀ x ∈ P.K,
      (Finset.sum P.active fun i =>
          ManifoldForm.localizedForm I (fun y => P.partition i y) omega x) =
        omega x := by
  exact ManifoldForm.sum_localizedForm_eq_on
    (I := I) P.active (fun i y => P.partition i y) omega
    P.coeff_sum_eq_one_on

/-- Pointwise direct reconstruction for a selected-box package. -/
theorem sum_localizedForm_apply_eq_self_on
    (P : SelectedBoxPartitionOfUnity I omega) {x : M} (hx : x ∈ P.K) :
    (Finset.sum P.active fun i =>
        ManifoldForm.localizedForm I (fun y => P.partition i y) omega x) =
      omega x :=
  P.sum_localizedForm_eq_on x hx

/-- A.e. direct reconstruction for measures carried by the selected compact
support set. -/
theorem sum_localizedForm_ae_eq_self_of_ae_mem
    (P : SelectedBoxPartitionOfUnity I omega)
    [MeasurableSpace M] {mu : Measure M} (hmuK : ∀ᵐ x ∂mu, x ∈ P.K) :
    ∀ᵐ x ∂mu,
      (Finset.sum P.active fun i =>
          ManifoldForm.localizedForm I (fun y => P.partition i y) omega x) =
        omega x :=
  ManifoldForm.sum_localizedForm_ae_eq_self_of_ae_mem
    (I := I) P.active (fun i y => P.partition i y) omega hmuK
    P.coeff_sum_eq_one_on

end SelectedBoxPartitionOfUnity

end FiniteActivePackages

end Stokes

end
