import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Measure-level finite-sum localization

This file contains pure measure-theoretic localization lemmas for Bochner
integrals.  The statements are intentionally independent of the Stokes
geometry layer: a global integrand is reconstructed from finitely many local
terms, either already written with indicators or known to have support inside
the chosen measurable localization sets.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Stokes

universe u v w

section FiniteSupportLocalization

variable {α : Type u} {ι : Type v} {E : Type w}
variable [AddCommMonoid E]

/-- A finite sum of terms supported in their localization sets is pointwise the
same finite sum after inserting the corresponding indicators. -/
theorem finset_sum_eq_finset_sum_indicator_of_support_subset
    (active : Finset ι) (s : ι → Set α) (localTerm : ι → α → E)
    (hsupp : ∀ i ∈ active, Function.support (localTerm i) ⊆ s i) :
    (fun x => ∑ i ∈ active, localTerm i x) =
      fun x => ∑ i ∈ active, (s i).indicator (localTerm i) x := by
  funext x
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hx : x ∈ s i
  · rw [indicator_of_mem hx]
  · have hzero : localTerm i x = 0 := by
      by_contra hne
      exact hx (hsupp i hi hne)
    rw [indicator_of_notMem hx, hzero]

end FiniteSupportLocalization

section MeasureIntegralLocalization

variable {α : Type u} {ι : Type v} {E : Type w}
variable [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ : Measure α}

/-- If a global integrand is almost everywhere a finite sum of localized
indicator terms, then its integral is the finite sum of the corresponding set
integrals. -/
theorem integral_eq_finset_sum_setIntegral_of_ae_eq_sum_indicator
    (active : Finset ι) (s : ι → Set α) (localTerm : ι → α → E)
    (F : α → E)
    (hs : ∀ i ∈ active, MeasurableSet (s i))
    (hlocal_int : ∀ i ∈ active, IntegrableOn (localTerm i) (s i) μ)
    (hF :
      F =ᵐ[μ] fun x => ∑ i ∈ active, (s i).indicator (localTerm i) x) :
    ∫ x, F x ∂μ = ∑ i ∈ active, ∫ x in s i, localTerm i x ∂μ := by
  calc
    ∫ x, F x ∂μ =
        ∫ x, ∑ i ∈ active, (s i).indicator (localTerm i) x ∂μ :=
      integral_congr_ae hF
    _ = ∑ i ∈ active, ∫ x, (s i).indicator (localTerm i) x ∂μ := by
      exact integral_finset_sum active fun i hi =>
        (hlocal_int i hi).integrable_indicator (hs i hi)
    _ = ∑ i ∈ active, ∫ x in s i, localTerm i x ∂μ := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [integral_indicator (hs i hi)]

/-- If a global integrand is almost everywhere a finite sum of local terms, and
each local term is supported in its measurable localization set, then the
global integral is the finite sum of the local set integrals. -/
theorem integral_eq_finset_sum_setIntegral_of_support_subset
    (active : Finset ι) (s : ι → Set α) (localTerm : ι → α → E)
    (F : α → E)
    (hs : ∀ i ∈ active, MeasurableSet (s i))
    (hlocal_int : ∀ i ∈ active, IntegrableOn (localTerm i) (s i) μ)
    (hF : F =ᵐ[μ] fun x => ∑ i ∈ active, localTerm i x)
    (hsupp : ∀ i ∈ active, Function.support (localTerm i) ⊆ s i) :
    ∫ x, F x ∂μ = ∑ i ∈ active, ∫ x in s i, localTerm i x ∂μ := by
  refine integral_eq_finset_sum_setIntegral_of_ae_eq_sum_indicator
    (μ := μ) active s localTerm F hs hlocal_int ?_
  exact hF.trans <|
    Filter.Eventually.of_forall
      (congrFun
        (finset_sum_eq_finset_sum_indicator_of_support_subset
          active s localTerm hsupp))

end MeasureIntegralLocalization

end Stokes
