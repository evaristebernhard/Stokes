import Stokes.Global.LocalizedSupport
import Stokes.Global.PartitionSumOne
import Mathlib.Topology.Algebra.Support

/-!
# Support control for finite localized sums

This file isolates the elementary finite-sum support bookkeeping used by the
global Stokes localization layer.  The algebraic support statements are proved
directly.  The chartwise `tsupport` package keeps the closedness of the chosen
finite union as an explicit field, while also providing constructors for the
common case where each term support is already closed.
-/

noncomputable section

open Set
open scoped BigOperators Manifold Topology

namespace Stokes

universe u v w c

section FiniteSumSupport

variable {ι : Type u} {X : Type v}

/-- If every term of a finite sum is supported in `K i`, then the sum is
supported in the finite union of the `K i`. -/
theorem support_finset_sum_subset_iUnion {A : Type w} [AddCommMonoid A]
    (active : Finset ι) (f : ι → X → A) (K : ι → Set X)
    (hsupp : ∀ i ∈ active, Function.support (f i) ⊆ K i) :
    Function.support (Finset.sum active f) ⊆
      ⋃ i ∈ active, K i := by
  intro x hx
  by_contra hxunion
  have hzero : ∀ i ∈ active, f i x = 0 := by
    intro i hi
    by_contra hix
    exact hxunion <| by
      exact mem_iUnion.mpr
        ⟨i, mem_iUnion.mpr ⟨hi, hsupp i hi hix⟩⟩
  exact hx (by simpa [Finset.sum_apply] using Finset.sum_eq_zero hzero)

/-- Common-support version of `support_finset_sum_subset_iUnion`. -/
theorem support_finset_sum_subset {A : Type w} [AddCommMonoid A]
    (active : Finset ι) (f : ι → X → A) (K : Set X)
    (hsupp : ∀ i ∈ active, Function.support (f i) ⊆ K) :
    Function.support (Finset.sum active f) ⊆ K := by
  intro x hx
  by_contra hxK
  have hzero : ∀ i ∈ active, f i x = 0 := by
    intro i hi
    by_contra hix
    exact hxK (hsupp i hi hix)
  exact hx (by simpa [Finset.sum_apply] using Finset.sum_eq_zero hzero)

/-- Dependent-family version, for objects such as manifold forms whose target
fiber depends on the base point. -/
theorem dependent_support_finset_sum_subset_iUnion
    {F : X → Type w} [∀ x, AddCommMonoid (F x)]
    (active : Finset ι) (f : ι → ∀ x, F x) (K : ι → Set X)
    (hsupp : ∀ i ∈ active, {x | f i x ≠ 0} ⊆ K i) :
    {x | (Finset.sum active fun i => f i x) ≠ 0} ⊆
      ⋃ i ∈ active, K i := by
  intro x hx
  by_contra hxunion
  have hzero : ∀ i ∈ active, f i x = 0 := by
    intro i hi
    by_contra hix
    exact hxunion <| by
      exact mem_iUnion.mpr
        ⟨i, mem_iUnion.mpr ⟨hi, hsupp i hi hix⟩⟩
  exact hx (Finset.sum_eq_zero hzero)

/-- Common-support dependent-family version. -/
theorem dependent_support_finset_sum_subset
    {F : X → Type w} [∀ x, AddCommMonoid (F x)]
    (active : Finset ι) (f : ι → ∀ x, F x) (K : Set X)
    (hsupp : ∀ i ∈ active, {x | f i x ≠ 0} ⊆ K) :
    {x | (Finset.sum active fun i => f i x) ≠ 0} ⊆ K := by
  intro x hx
  by_contra hxK
  have hzero : ∀ i ∈ active, f i x = 0 := by
    intro i hi
    by_contra hix
    exact hxK (hsupp i hi hix)
  exact hx (Finset.sum_eq_zero hzero)

variable [TopologicalSpace X]

/-- Topological-support finite-union control, with closedness of the chosen
finite union supplied explicitly. -/
theorem tsupport_finset_sum_subset_iUnion_of_isClosed {A : Type w}
    [AddCommMonoid A] (active : Finset ι) (f : ι → X → A)
    (K : ι → Set X)
    (hsupp : ∀ i ∈ active, tsupport (f i) ⊆ K i)
    (hclosed : IsClosed (⋃ i ∈ active, K i)) :
    tsupport (Finset.sum active f) ⊆
      ⋃ i ∈ active, K i := by
  change closure (Function.support (Finset.sum active f)) ⊆
    ⋃ i ∈ active, K i
  exact closure_minimal
    (support_finset_sum_subset_iUnion active f K fun i hi =>
      (subset_tsupport (f i)).trans (hsupp i hi))
    hclosed

/-- Topological-support finite-union control when every chosen term support set
is closed. -/
theorem tsupport_finset_sum_subset_iUnion {A : Type w} [AddCommMonoid A]
    (active : Finset ι) (f : ι → X → A) (K : ι → Set X)
    (hsupp : ∀ i ∈ active, tsupport (f i) ⊆ K i)
    (hclosed : ∀ i ∈ active, IsClosed (K i)) :
    tsupport (Finset.sum active f) ⊆
      ⋃ i ∈ active, K i :=
  tsupport_finset_sum_subset_iUnion_of_isClosed active f K hsupp
    (isClosed_biUnion_finset hclosed)

/-- Common closed-support version for topological support of a finite sum. -/
theorem tsupport_finset_sum_subset_of_isClosed {A : Type w}
    [AddCommMonoid A] (active : Finset ι) (f : ι → X → A)
    (K : Set X) (hclosed : IsClosed K)
    (hsupp : ∀ i ∈ active, tsupport (f i) ⊆ K) :
    tsupport (Finset.sum active f) ⊆ K := by
  change closure (Function.support (Finset.sum active f)) ⊆ K
  exact closure_minimal
    (support_finset_sum_subset active f K fun i hi =>
      (subset_tsupport (f i)).trans (hsupp i hi))
    hclosed

end FiniteSumSupport

section LocalizedFormSums

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}

/-- Support of a finite localized form sum is contained in the finite union of
term support controls. -/
theorem localizedFormSum_support_subset_iUnion {Chart : Type c}
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M k) (K : Chart → Set M)
    (hsupp :
      ∀ i ∈ active,
        ManifoldForm.support I (ManifoldForm.localizedForm I (coefficient i) ω) ⊆
          K i) :
    ManifoldForm.support I (localizedFormSum I active coefficient ω) ⊆
      ⋃ i ∈ active, K i := by
  simpa [ManifoldForm.support, localizedFormSum] using
    dependent_support_finset_sum_subset_iUnion active
      (fun i => ManifoldForm.localizedForm I (coefficient i) ω) K hsupp

/-- Common-support version for finite localized form sums. -/
theorem localizedFormSum_support_subset {Chart : Type c}
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M k) (K : Set M)
    (hsupp :
      ∀ i ∈ active,
        ManifoldForm.support I (ManifoldForm.localizedForm I (coefficient i) ω) ⊆
          K) :
    ManifoldForm.support I (localizedFormSum I active coefficient ω) ⊆ K := by
  simpa [ManifoldForm.support, localizedFormSum] using
    dependent_support_finset_sum_subset active
      (fun i => ManifoldForm.localizedForm I (coefficient i) ω) K hsupp

/-- The localized finite sum can only be supported where at least one active
coefficient is supported. -/
theorem localizedFormSum_support_subset_coefficient_iUnion {Chart : Type c}
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M k) :
    ManifoldForm.support I (localizedFormSum I active coefficient ω) ⊆
      ⋃ i ∈ active, Function.support (coefficient i) :=
  localizedFormSum_support_subset_iUnion active coefficient ω
    (fun i => Function.support (coefficient i))
    fun i _hi =>
      ManifoldForm.localizedForm_support_subset_coefficient_support (I := I)
        (coefficient i) ω

/-- The localized finite sum can only be supported where the original form is
supported. -/
theorem localizedFormSum_support_subset_form_support {Chart : Type c}
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M k) :
    ManifoldForm.support I (localizedFormSum I active coefficient ω) ⊆
      ManifoldForm.support I ω :=
  localizedFormSum_support_subset active coefficient ω (ManifoldForm.support I ω)
    fun i _hi =>
      ManifoldForm.localizedForm_support_subset_form_support (I := I)
        (coefficient i) ω

/-- Algebraic transition-support control for a finite localized form sum in
chart coordinates. -/
theorem transitionPullbackInChart_localizedFormSum_support_subset_iUnion
    {Chart : Type c} (active : Finset Chart)
    (coefficient : Chart → M → Real) (ω : ManifoldForm I M k)
    (x0 x1 : M) (K : Chart → Set E)
    (hsupp :
      ∀ i ∈ active,
        Function.support
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (ManifoldForm.localizedForm I (coefficient i) ω)) ⊆
          K i) :
    Function.support
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I active coefficient ω)) ⊆
      ⋃ i ∈ active, K i := by
  have hrepr :
      ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I active coefficient ω) =
        Finset.sum active fun i =>
          ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω) := by
    funext y
    ext v
    simp only [localizedFormSum, ManifoldForm.transitionPullbackInChart,
      ManifoldForm.inChart, Finset.sum_apply, ManifoldForm.localizedForm,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [ContinuousAlternatingMap.sum_apply]
    rw [ContinuousAlternatingMap.sum_apply]
    simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rfl
  rw [hrepr]
  exact support_finset_sum_subset_iUnion active
    (fun i =>
      ManifoldForm.transitionPullbackInChart I x0 x1
        (ManifoldForm.localizedForm I (coefficient i) ω))
    K hsupp

/-- Topological transition-support control for a finite localized form sum in
chart coordinates, with closedness of the selected finite union supplied as an
explicit hypothesis. -/
theorem transitionPullbackInChart_localizedFormSum_tsupport_subset_iUnion_of_isClosed
    {Chart : Type c} (active : Finset Chart)
    (coefficient : Chart → M → Real) (ω : ManifoldForm I M k)
    (x0 x1 : M) (K : Chart → Set E)
    (hsupp :
      ∀ i ∈ active,
        tsupport
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (ManifoldForm.localizedForm I (coefficient i) ω)) ⊆
          K i)
    (hclosed : IsClosed (⋃ i ∈ active, K i)) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I active coefficient ω)) ⊆
      ⋃ i ∈ active, K i := by
  have hrepr :
      ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I active coefficient ω) =
        Finset.sum active fun i =>
          ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω) := by
    funext y
    ext v
    simp only [localizedFormSum, ManifoldForm.transitionPullbackInChart,
      ManifoldForm.inChart, Finset.sum_apply, ManifoldForm.localizedForm,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [ContinuousAlternatingMap.sum_apply]
    rw [ContinuousAlternatingMap.sum_apply]
    simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rfl
  rw [hrepr]
  exact tsupport_finset_sum_subset_iUnion_of_isClosed active
    (fun i =>
      ManifoldForm.transitionPullbackInChart I x0 x1
        (ManifoldForm.localizedForm I (coefficient i) ω))
    K hsupp hclosed

/-- Topological transition-support control when every selected term support is
closed. -/
theorem transitionPullbackInChart_localizedFormSum_tsupport_subset_iUnion
    {Chart : Type c} (active : Finset Chart)
    (coefficient : Chart → M → Real) (ω : ManifoldForm I M k)
    (x0 x1 : M) (K : Chart → Set E)
    (hsupp :
      ∀ i ∈ active,
        tsupport
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (ManifoldForm.localizedForm I (coefficient i) ω)) ⊆
          K i)
    (hclosed : ∀ i ∈ active, IsClosed (K i)) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I active coefficient ω)) ⊆
      ⋃ i ∈ active, K i :=
  transitionPullbackInChart_localizedFormSum_tsupport_subset_iUnion_of_isClosed
    active coefficient ω x0 x1 K hsupp (isClosed_biUnion_finset hclosed)

/-- Common closed-support version of topological transition-support control for
a finite localized form sum in chart coordinates. -/
theorem transitionPullbackInChart_localizedFormSum_tsupport_subset_of_isClosed
    {Chart : Type c} (active : Finset Chart)
    (coefficient : Chart → M → Real) (ω : ManifoldForm I M k)
    (x0 x1 : M) (K : Set E) (hclosed : IsClosed K)
    (hsupp :
      ∀ i ∈ active,
        tsupport
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (ManifoldForm.localizedForm I (coefficient i) ω)) ⊆
          K) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I active coefficient ω)) ⊆ K := by
  have hrepr :
      ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I active coefficient ω) =
        Finset.sum active fun i =>
          ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω) := by
    funext y
    ext v
    simp only [localizedFormSum, ManifoldForm.transitionPullbackInChart,
      ManifoldForm.inChart, Finset.sum_apply, ManifoldForm.localizedForm,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [ContinuousAlternatingMap.sum_apply]
    rw [ContinuousAlternatingMap.sum_apply]
    simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rfl
  rw [hrepr]
  exact tsupport_finset_sum_subset_of_isClosed active
    (fun i =>
      ManifoldForm.transitionPullbackInChart I x0 x1
        (ManifoldForm.localizedForm I (coefficient i) ω))
    K hclosed hsupp

/-- The transition representative of a localized finite sum is supported in the
finite union of the transition-coordinate coefficient supports. -/
theorem transitionPullbackInChart_localizedFormSum_tsupport_subset_coefficient_iUnion
    {Chart : Type c} (active : Finset Chart)
    (coefficient : Chart → M → Real) (ω : ManifoldForm I M k)
    (x0 x1 : M) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I active coefficient ω)) ⊆
      ⋃ i ∈ active,
        tsupport
          (ManifoldForm.transitionCoefficientInChart I x0 x1 (coefficient i)) :=
  transitionPullbackInChart_localizedFormSum_tsupport_subset_iUnion
    active coefficient ω x0 x1
    (fun i =>
      tsupport
        (ManifoldForm.transitionCoefficientInChart I x0 x1 (coefficient i)))
    (fun i _hi =>
      ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_coefficient
        (I := I) x0 x1 (coefficient i) ω)
    (fun i _hi => isClosed_tsupport
      (ManifoldForm.transitionCoefficientInChart I x0 x1 (coefficient i)))

/-- The transition representative of a localized finite sum is supported in the
topological support of the base transition representative. -/
theorem transitionPullbackInChart_localizedFormSum_tsupport_subset_form
    {Chart : Type c} (active : Finset Chart)
    (coefficient : Chart → M → Real) (ω : ManifoldForm I M k)
    (x0 x1 : M) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I active coefficient ω)) ⊆
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) :=
  transitionPullbackInChart_localizedFormSum_tsupport_subset_of_isClosed
    active coefficient ω x0 x1
    (tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω))
    (isClosed_tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω))
    (fun i _hi =>
      ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_form
        (I := I) x0 x1 (coefficient i) ω)

end LocalizedFormSums

section SupportWrappers

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}

/-- Support-control data for the algebraic support of a finite localized
manifold-form sum. -/
structure LocalizedFormSumSupportControl {Chart : Type c}
    (I : ModelWithCorners Real E H) (active : Finset Chart)
    (coefficient : Chart → M → Real) (ω : ManifoldForm I M k) where
  /-- Chosen support set for each localized summand. -/
  termSupport : Chart → Set M
  /-- Each active localized summand is supported in its chosen set. -/
  localized_support_subset :
    ∀ i ∈ active,
      ManifoldForm.support I (ManifoldForm.localizedForm I (coefficient i) ω) ⊆
        termSupport i

namespace LocalizedFormSumSupportControl

variable {Chart : Type c} {active : Finset Chart}
variable {coefficient : Chart → M → Real} {ω : ManifoldForm I M k}

/-- The finite union controlling the localized sum. -/
def supportUnion
    (C : LocalizedFormSumSupportControl I active coefficient ω) : Set M :=
  ⋃ i ∈ active, C.termSupport i

/-- The localized finite sum is supported in the packaged finite union. -/
theorem localizedFormSum_support_subset_supportUnion
    (C : LocalizedFormSumSupportControl I active coefficient ω) :
    ManifoldForm.support I (localizedFormSum I active coefficient ω) ⊆
      C.supportUnion :=
  localizedFormSum_support_subset_iUnion active coefficient ω C.termSupport
    C.localized_support_subset

/-- Constructor for the common case where all summands are supported in one
set. -/
def ofCommonSupport (K : Set M)
    (hsupp :
      ∀ i ∈ active,
        ManifoldForm.support I (ManifoldForm.localizedForm I (coefficient i) ω) ⊆
          K) :
    LocalizedFormSumSupportControl I active coefficient ω where
  termSupport := fun _ => K
  localized_support_subset := hsupp

/-- Projection from the common-support constructor. -/
theorem localizedFormSum_support_subset_ofCommonSupport {K : Set M}
    (hsupp :
      ∀ i ∈ active,
        ManifoldForm.support I (ManifoldForm.localizedForm I (coefficient i) ω) ⊆
          K) :
    ManifoldForm.support I (localizedFormSum I active coefficient ω) ⊆ K :=
  localizedFormSum_support_subset active coefficient ω K hsupp

end LocalizedFormSumSupportControl

/-- Chartwise topological-support control for the transition representative of
a finite localized form sum.

The closedness of `supportUnion` is a field so callers can use arbitrary
closed finite unions without reproving closure facts at every use site.
-/
structure TransitionLocalizedFormSumTSupportControl {Chart : Type c}
    (I : ModelWithCorners Real E H) (x0 x1 : M)
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M k) where
  /-- Chosen model-space topological support set for each localized summand. -/
  termSupport : Chart → Set E
  /-- The chosen finite support union is closed. -/
  isClosed_supportUnion : IsClosed (⋃ i ∈ active, termSupport i)
  /-- Each active localized transition representative is supported in its
  chosen model-space set. -/
  localized_tsupport_subset :
    ∀ i ∈ active,
      tsupport
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω)) ⊆
        termSupport i

namespace TransitionLocalizedFormSumTSupportControl

variable {Chart : Type c} {x0 x1 : M} {active : Finset Chart}
variable {coefficient : Chart → M → Real} {ω : ManifoldForm I M k}

/-- The closed finite union controlling the transition representative. -/
def supportUnion
    (C :
      TransitionLocalizedFormSumTSupportControl I x0 x1 active coefficient ω) :
    Set E :=
  ⋃ i ∈ active, C.termSupport i

/-- The transition representative of the localized finite sum is supported in
the packaged closed finite union. -/
theorem localizedFormSum_tsupport_subset_supportUnion
    (C :
      TransitionLocalizedFormSumTSupportControl I x0 x1 active coefficient ω) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I active coefficient ω)) ⊆
      C.supportUnion :=
  transitionPullbackInChart_localizedFormSum_tsupport_subset_iUnion_of_isClosed
    active coefficient ω x0 x1 C.termSupport C.localized_tsupport_subset
    C.isClosed_supportUnion

/-- Constructor when every chosen term support set is closed. -/
def ofClosedTermSupports (termSupport : Chart → Set E)
    (hclosed : ∀ i ∈ active, IsClosed (termSupport i))
    (hsupp :
      ∀ i ∈ active,
        tsupport
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (ManifoldForm.localizedForm I (coefficient i) ω)) ⊆
          termSupport i) :
    TransitionLocalizedFormSumTSupportControl I x0 x1 active coefficient ω where
  termSupport := termSupport
  isClosed_supportUnion := isClosed_biUnion_finset hclosed
  localized_tsupport_subset := hsupp

/-- Constructor for the common case where all localized transition
representatives are supported in one closed set. -/
def ofCommonClosedSupport (K : Set E) (hclosed : IsClosed K)
    (hsupp :
      ∀ i ∈ active,
        tsupport
            (ManifoldForm.transitionPullbackInChart I x0 x1
              (ManifoldForm.localizedForm I (coefficient i) ω)) ⊆
          K) :
    TransitionLocalizedFormSumTSupportControl I x0 x1 active coefficient ω where
  termSupport := fun _ => K
  isClosed_supportUnion := by
    simpa using isClosed_biUnion_finset (s := active) (f := fun _ : Chart => K)
      (fun i hi => hclosed)
  localized_tsupport_subset := hsupp

end TransitionLocalizedFormSumTSupportControl

end SupportWrappers

end Stokes

end
