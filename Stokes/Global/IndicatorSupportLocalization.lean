import Stokes.Global.SupportFiniteSum
import Stokes.Global.InteriorBoundarySupportZero
import Stokes.Global.CoefficientBoxSupport
import Stokes.Global.MeasureIntegralLocalization

/-!
# Indicator localization from support control

This file turns the support facts produced by the local box-selection layer into
pointwise and almost-everywhere equalities with indicator-localized integrands.
It stays purely at the set/function/finite-sum level: no integral definition is
used here.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace Stokes

universe u v w

section BasicIndicatorLocalization

variable {X : Type u} {A : Type v} [Zero A]
variable {s : Set X} {f : X → A}

/-- If a function vanishes off `s`, then inserting the indicator of `s` changes nothing. -/
theorem indicator_eq_self_of_eq_zero_off
    (hzero : ∀ x, x ∉ s → f x = 0) :
    s.indicator f = f := by
  exact Set.indicator_eq_self.mpr fun x hx => by
    by_contra hxs
    exact hx (hzero x hxs)

/-- Support-containment version of `indicator_eq_self_of_eq_zero_off`. -/
theorem indicator_eq_self_of_support_subset
    (hsupp : Function.support f ⊆ s) :
    s.indicator f = f := by
  exact Set.indicator_eq_self.mpr hsupp

/-- Pointwise symmetric version of `indicator_eq_self_of_eq_zero_off`. -/
theorem eq_indicator_of_eq_zero_off
    (hzero : ∀ x, x ∉ s → f x = 0) :
    f = s.indicator f :=
  (indicator_eq_self_of_eq_zero_off hzero).symm

/-- Pointwise symmetric support-containment version. -/
theorem eq_indicator_of_support_subset
    (hsupp : Function.support f ⊆ s) :
    f = s.indicator f :=
  (indicator_eq_self_of_support_subset hsupp).symm

variable [MeasurableSpace X] {μ : Measure X}

/-- AE version: a function vanishing off `s` is AE equal to its indicator localization. -/
theorem indicator_ae_eq_self_of_eq_zero_off
    (hzero : ∀ x, x ∉ s → f x = 0) :
    s.indicator f =ᵐ[μ] f := by
  exact ae_of_all μ fun x => congrFun (indicator_eq_self_of_eq_zero_off hzero) x

/-- AE support-containment version of `indicator_eq_self_of_eq_zero_off`. -/
theorem indicator_ae_eq_self_of_support_subset
    (hsupp : Function.support f ⊆ s) :
    s.indicator f =ᵐ[μ] f := by
  exact ae_of_all μ fun x => congrFun (indicator_eq_self_of_support_subset hsupp) x

/-- Symmetric AE version, convenient when the unlocalized function is the source term. -/
theorem ae_eq_indicator_of_eq_zero_off
    (hzero : ∀ x, x ∉ s → f x = 0) :
    f =ᵐ[μ] s.indicator f :=
  (indicator_ae_eq_self_of_eq_zero_off (μ := μ) hzero).symm

/-- Symmetric AE support-containment version. -/
theorem ae_eq_indicator_of_support_subset
    (hsupp : Function.support f ⊆ s) :
    f =ᵐ[μ] s.indicator f :=
  (indicator_ae_eq_self_of_support_subset (μ := μ) hsupp).symm

end BasicIndicatorLocalization

section FiniteIndicatorLocalization

variable {ι : Type u} {X : Type v} {A : Type w}
variable [AddCommMonoid A]
variable (active : Finset ι) (K : ι → Set X) (f : ι → X → A)

/-- Pointwise finite-sum localization from termwise vanishing off the chosen sets. -/
theorem indicator_finset_sum_eq_sum_of_eq_zero_off
    (hzero : ∀ i, i ∈ active → ∀ x, x ∉ K i → f i x = 0) :
    (Finset.sum active fun i => (K i).indicator (f i)) =
      Finset.sum active f := by
  funext x
  simpa [Finset.sum_apply] using
    (Finset.sum_congr rfl fun i hi =>
      congrFun (indicator_eq_self_of_eq_zero_off (s := K i) (f := f i)
        (hzero i hi)) x)

/-- Pointwise finite-sum localization from termwise support containment. -/
theorem indicator_finset_sum_eq_sum_of_support_subset
    (hsupp : ∀ i, i ∈ active → Function.support (f i) ⊆ K i) :
    (Finset.sum active fun i => (K i).indicator (f i)) =
      Finset.sum active f := by
  funext x
  simpa [Finset.sum_apply] using
    congrFun
      (finset_sum_eq_finset_sum_indicator_of_support_subset
        (active := active) (s := K) (localTerm := f) hsupp).symm x

/-- Pointwise finite-sum localization from termwise support containment,
with the unlocalized sum on the left. -/
theorem finset_sum_eq_indicator_sum_of_support_subset
    (hsupp : ∀ i, i ∈ active → Function.support (f i) ⊆ K i) :
    (Finset.sum active f) =
      Finset.sum active fun i => (K i).indicator (f i) := by
  funext x
  simpa [Finset.sum_apply] using
    congrFun
      (finset_sum_eq_finset_sum_indicator_of_support_subset
        (active := active) (s := K) (localTerm := f) hsupp) x

variable [MeasurableSpace X] {μ : Measure X}

/-- AE finite-sum localization from termwise vanishing off the chosen sets. -/
theorem indicator_finset_sum_ae_eq_sum_of_eq_zero_off
    (hzero : ∀ i, i ∈ active → ∀ x, x ∉ K i → f i x = 0) :
    (Finset.sum active fun i => (K i).indicator (f i)) =ᵐ[μ]
      Finset.sum active f := by
  exact ae_of_all μ fun x =>
    congrFun (indicator_finset_sum_eq_sum_of_eq_zero_off active K f hzero) x

/-- AE finite-sum localization from termwise support containment. -/
theorem indicator_finset_sum_ae_eq_sum_of_support_subset
    (hsupp : ∀ i, i ∈ active → Function.support (f i) ⊆ K i) :
    (Finset.sum active fun i => (K i).indicator (f i)) =ᵐ[μ]
      Finset.sum active f := by
  exact ae_of_all μ fun x =>
    congrFun (indicator_finset_sum_eq_sum_of_support_subset active K f hsupp) x

/-- Symmetric AE finite-sum localization from termwise vanishing off the chosen sets. -/
theorem finset_sum_ae_eq_indicator_sum_of_eq_zero_off
    (hzero : ∀ i, i ∈ active → ∀ x, x ∉ K i → f i x = 0) :
    (Finset.sum active f) =ᵐ[μ]
      Finset.sum active fun i => (K i).indicator (f i) :=
  (indicator_finset_sum_ae_eq_sum_of_eq_zero_off
    (μ := μ) active K f hzero).symm

/-- Symmetric AE finite-sum localization from termwise support containment. -/
theorem finset_sum_ae_eq_indicator_sum_of_support_subset
    (hsupp : ∀ i, i ∈ active → Function.support (f i) ⊆ K i) :
    (Finset.sum active f) =ᵐ[μ]
      Finset.sum active fun i => (K i).indicator (f i) :=
  ae_of_all μ fun x =>
    congrFun (finset_sum_eq_indicator_sum_of_support_subset active K f hsupp) x

end FiniteIndicatorLocalization

section CommonSupportLocalization

variable {ι : Type u} {X : Type v} {A : Type w}
variable [AddCommMonoid A]
variable (active : Finset ι) (K : Set X) (f : ι → X → A)

/-- A common indicator distributes over a finite sum of functions. -/
theorem indicator_finset_sum_eq_finset_sum_indicator :
    K.indicator (Finset.sum active f) =
      Finset.sum active fun i => K.indicator (f i) := by
  funext x
  by_cases hx : x ∈ K
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- If every summand is supported in a common set, then the whole sum is its common indicator. -/
theorem common_indicator_finset_sum_eq_sum_of_support_subset
    (hsupp : ∀ i, i ∈ active → Function.support (f i) ⊆ K) :
    K.indicator (Finset.sum active f) = Finset.sum active f := by
  rw [indicator_finset_sum_eq_finset_sum_indicator active K f]
  exact indicator_finset_sum_eq_sum_of_support_subset active (fun _ => K) f hsupp

variable [MeasurableSpace X] {μ : Measure X}

/-- AE common-box localization of a finite sum from support containment of each summand. -/
theorem common_indicator_finset_sum_ae_eq_sum_of_support_subset
    (hsupp : ∀ i, i ∈ active → Function.support (f i) ⊆ K) :
    K.indicator (Finset.sum active f) =ᵐ[μ] Finset.sum active f := by
  exact ae_of_all μ fun x =>
    congrFun (common_indicator_finset_sum_eq_sum_of_support_subset active K f hsupp) x

/-- Symmetric AE common-box localization of a finite sum. -/
theorem finset_sum_ae_eq_common_indicator_of_support_subset
    (hsupp : ∀ i, i ∈ active → Function.support (f i) ⊆ K) :
    (Finset.sum active f) =ᵐ[μ] K.indicator (Finset.sum active f) :=
  (common_indicator_finset_sum_ae_eq_sum_of_support_subset
    (μ := μ) active K f hsupp).symm

end CommonSupportLocalization

section BoxIndicatorLocalization

variable {X : Type u} [Preorder X] {A : Type v} [Zero A]
variable {a b : X} {f : X → A}

/-- Box alias: vanishing off `Set.Icc a b` gives indicator localization. -/
theorem Icc_indicator_eq_self_of_eq_zero_off
    (hzero : ∀ x, x ∉ Set.Icc a b → f x = 0) :
    (Set.Icc a b).indicator f = f :=
  indicator_eq_self_of_eq_zero_off hzero

/-- Box alias: support in `Set.Icc a b` gives indicator localization. -/
theorem Icc_indicator_eq_self_of_support_subset
    (hsupp : Function.support f ⊆ Set.Icc a b) :
    (Set.Icc a b).indicator f = f :=
  indicator_eq_self_of_support_subset hsupp

/-- Box alias: support in `Set.Icc a b` gives pointwise indicator localization. -/
theorem Icc_eq_indicator_of_support_subset
    (hsupp : Function.support f ⊆ Set.Icc a b) :
    f = (Set.Icc a b).indicator f :=
  eq_indicator_of_support_subset hsupp

variable [MeasurableSpace X] {μ : Measure X}

/-- AE box alias: vanishing off `Set.Icc a b` gives indicator localization. -/
theorem Icc_indicator_ae_eq_self_of_eq_zero_off
    (hzero : ∀ x, x ∉ Set.Icc a b → f x = 0) :
    (Set.Icc a b).indicator f =ᵐ[μ] f :=
  indicator_ae_eq_self_of_eq_zero_off (μ := μ) hzero

/-- AE box alias: support in `Set.Icc a b` gives indicator localization. -/
theorem Icc_indicator_ae_eq_self_of_support_subset
    (hsupp : Function.support f ⊆ Set.Icc a b) :
    (Set.Icc a b).indicator f =ᵐ[μ] f :=
  indicator_ae_eq_self_of_support_subset (μ := μ) hsupp

end BoxIndicatorLocalization

section BoxFiniteIndicatorLocalization

variable {ι : Type u} {X : Type v} {A : Type w}
variable [Preorder X] [AddCommMonoid A]
variable (active : Finset ι) (a b : ι → X) (f : ι → X → A)

/-- Box-family finite-sum localization from termwise vanishing off the selected boxes. -/
theorem Icc_indicator_finset_sum_ae_eq_sum_of_eq_zero_off
    [MeasurableSpace X] {μ : Measure X}
    (hzero : ∀ i, i ∈ active → ∀ x, x ∉ Set.Icc (a i) (b i) → f i x = 0) :
    (Finset.sum active fun i => (Set.Icc (a i) (b i)).indicator (f i)) =ᵐ[μ]
      Finset.sum active f :=
  indicator_finset_sum_ae_eq_sum_of_eq_zero_off
    (μ := μ) active (fun i => Set.Icc (a i) (b i)) f hzero

/-- Box-family finite-sum localization from termwise support containment in selected boxes. -/
theorem Icc_indicator_finset_sum_ae_eq_sum_of_support_subset
    [MeasurableSpace X] {μ : Measure X}
    (hsupp : ∀ i, i ∈ active → Function.support (f i) ⊆ Set.Icc (a i) (b i)) :
    (Finset.sum active fun i => (Set.Icc (a i) (b i)).indicator (f i)) =ᵐ[μ]
      Finset.sum active f :=
  indicator_finset_sum_ae_eq_sum_of_support_subset
    (μ := μ) active (fun i => Set.Icc (a i) (b i)) f hsupp

/-- Pointwise box-family finite-sum localization from termwise support containment. -/
theorem finset_sum_eq_Icc_indicator_sum_of_support_subset
    (hsupp : ∀ i, i ∈ active → Function.support (f i) ⊆ Set.Icc (a i) (b i)) :
    (Finset.sum active f) =
      Finset.sum active fun i => (Set.Icc (a i) (b i)).indicator (f i) :=
  finset_sum_eq_indicator_sum_of_support_subset
    active (fun i => Set.Icc (a i) (b i)) f hsupp

/-- Symmetric AE box-family localization from termwise support containment. -/
theorem finset_sum_ae_eq_Icc_indicator_sum_of_support_subset
    [MeasurableSpace X] {μ : Measure X}
    (hsupp : ∀ i, i ∈ active → Function.support (f i) ⊆ Set.Icc (a i) (b i)) :
    (Finset.sum active f) =ᵐ[μ]
      Finset.sum active fun i => (Set.Icc (a i) (b i)).indicator (f i) :=
  (Icc_indicator_finset_sum_ae_eq_sum_of_support_subset
    (μ := μ) active a b f hsupp).symm

end BoxFiniteIndicatorLocalization

end Stokes

end
