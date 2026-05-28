import Stokes.Global.SupportFiniteSum
import Stokes.Global.ReconstructionWrappers
import Stokes.Global.ExtDerivReconstruction

/-!
# Eventually-local reconstruction of partition-localized forms

This file strengthens the pointwise-on-support reconstruction API for finite
partition-localized sums.  If the localized sum reconstructs the form on a set
containing the algebraic support of the original form, then the support control
for localized finite sums makes the reconstruction global, hence local in every
neighborhood.  The resulting package supplies the chartwise `extDeriv`
reconstruction input used by the global assembly layer.
-/

noncomputable section

open Set Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section LocalizedEventually

universe u v w c

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}

/--
If a finite localized sum reconstructs `ω` on a set containing the algebraic
support of `ω`, then it reconstructs `ω` at every point.

Outside the chosen support set, `ω` vanishes.  The finite localized sum also
vanishes there because its algebraic support is contained in the algebraic
support of `ω`.
-/
theorem localizedFormSum_apply_eq_self_of_eq_on_of_form_support_subset
    {Chart : Type c} (active : Finset Chart)
    (coefficient : Chart → M → Real) (ω : ManifoldForm I M k) {K : Set M}
    (hlocalized :
      ∀ x ∈ K, localizedFormSum I active coefficient ω x = ω x)
    (hωsupp : ManifoldForm.support I ω ⊆ K) (x : M) :
    localizedFormSum I active coefficient ω x = ω x := by
  by_cases hxK : x ∈ K
  · exact hlocalized x hxK
  · have hω_zero : ω x = 0 := by
      by_contra hxω
      exact hxK (hωsupp hxω)
    have hsum_zero : localizedFormSum I active coefficient ω x = 0 := by
      by_contra hxsum
      exact hxK
        (hωsupp
          (localizedFormSum_support_subset_form_support
            (I := I) active coefficient ω hxsum))
    rw [hsum_zero, hω_zero]

/-- Function-extensional form of
`localizedFormSum_apply_eq_self_of_eq_on_of_form_support_subset`. -/
theorem localizedFormSum_eq_self_of_eq_on_of_form_support_subset
    {Chart : Type c} (active : Finset Chart)
    (coefficient : Chart → M → Real) (ω : ManifoldForm I M k) {K : Set M}
    (hlocalized :
      ∀ x ∈ K, localizedFormSum I active coefficient ω x = ω x)
    (hωsupp : ManifoldForm.support I ω ⊆ K) :
    localizedFormSum I active coefficient ω = ω := by
  funext x
  exact localizedFormSum_apply_eq_self_of_eq_on_of_form_support_subset
    active coefficient ω hlocalized hωsupp x

/-- Neighborhood-local form of support-based localized reconstruction. -/
theorem localizedFormSum_eventually_eq_self_of_eq_on_of_form_support_subset
    {Chart : Type c} (active : Finset Chart)
    (coefficient : Chart → M → Real) (ω : ManifoldForm I M k) {K : Set M}
    (hlocalized :
      ∀ x ∈ K, localizedFormSum I active coefficient ω x = ω x)
    (hωsupp : ManifoldForm.support I ω ⊆ K) (x : M) :
    ∀ᶠ y in 𝓝 x, localizedFormSum I active coefficient ω y = ω y :=
  Filter.Eventually.of_forall fun y =>
    localizedFormSum_apply_eq_self_of_eq_on_of_form_support_subset
      active coefficient ω hlocalized hωsupp y

/--
Eventually-local reconstruction data for a finite partition-localized form sum.

The stored equality is only required on `supportSet`.  The support field then
promotes it to an equality in every neighborhood, and therefore to chartwise
`extDeriv` reconstruction.
-/
structure LocalizedFormEventuallyEqData
    (I : ModelWithCorners Real E H) (ω : ManifoldForm I M k)
    (Chart : Type c) where
  /-- Finite partition/chart labels used in the localized sum. -/
  activeCharts : Finset Chart
  /-- Scalar coefficients for the localized forms. -/
  coefficient : Chart → M → Real
  /-- Set carrying the partition sum-one reconstruction, typically a compact support. -/
  supportSet : Set M
  /-- Pointwise reconstruction on the support set. -/
  localizedFormSum_eq_self_on :
    ∀ x ∈ supportSet, localizedFormSum I activeCharts coefficient ω x = ω x
  /-- The original form is algebraically supported in `supportSet`. -/
  form_support_subset_supportSet : ManifoldForm.support I ω ⊆ supportSet

namespace LocalizedFormEventuallyEqData

variable {Chart : Type c} {ω : ManifoldForm I M k}

/-- Constructor from a coefficient sum-one theorem on a support set. -/
def ofCoeffSumEqOneOn
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (K : Set M)
    (hsum : ∀ x ∈ K, (Finset.sum active fun i => coefficient i x) = 1)
    (hωsupp : ManifoldForm.support I ω ⊆ K) :
    LocalizedFormEventuallyEqData I ω Chart where
  activeCharts := active
  coefficient := coefficient
  supportSet := K
  localizedFormSum_eq_self_on :=
    localizedFormSum_eqOn_of_coeff_sum_eq_one_on active coefficient ω hsum
  form_support_subset_supportSet := hωsupp

/-- Constructor from the existing pointwise reconstruction-field package. -/
def ofReconstructionFields
    (D : LocalizedFormReconstructionFields I ω Chart)
    (hωsupp : ManifoldForm.support I ω ⊆ D.supportSet) :
    LocalizedFormEventuallyEqData I ω Chart where
  activeCharts := D.activeCharts
  coefficient := D.coefficient
  supportSet := D.supportSet
  localizedFormSum_eq_self_on := D.localizedFormSum_eq_self_on
  form_support_subset_supportSet := hωsupp

/-- Pointwise reconstruction at every point. -/
theorem localizedFormSum_apply_eq_self
    (D : LocalizedFormEventuallyEqData I ω Chart) (x : M) :
    localizedFormSum I D.activeCharts D.coefficient ω x = ω x :=
  localizedFormSum_apply_eq_self_of_eq_on_of_form_support_subset
    D.activeCharts D.coefficient ω D.localizedFormSum_eq_self_on
    D.form_support_subset_supportSet x

/-- Function-extensional reconstruction of the original form. -/
theorem localizedFormSum_eq_self
    (D : LocalizedFormEventuallyEqData I ω Chart) :
    localizedFormSum I D.activeCharts D.coefficient ω = ω := by
  funext x
  exact D.localizedFormSum_apply_eq_self x

/-- Neighborhood-local reconstruction at every manifold point. -/
theorem localizedFormSum_eventually_eq_self
    (D : LocalizedFormEventuallyEqData I ω Chart) (x : M) :
    ∀ᶠ y in 𝓝 x, localizedFormSum I D.activeCharts D.coefficient ω y = ω y :=
  Filter.Eventually.of_forall fun y => D.localizedFormSum_apply_eq_self y

/-- Chart representative equality induced by the manifold-form reconstruction. -/
theorem transitionPullbackInChart_eq_self
    (D : LocalizedFormEventuallyEqData I ω Chart) (x0 x1 : M) :
    ManifoldForm.transitionPullbackInChart I x0 x1
        (localizedFormSum I D.activeCharts D.coefficient ω) =
      ManifoldForm.transitionPullbackInChart I x0 x1 ω := by
  rw [D.localizedFormSum_eq_self]

/--
Neighborhood-local equality of chart representatives.  This is the direct
input shape for mathlib's `Filter.EventuallyEq.extDeriv_eq`.
-/
theorem transitionPullbackInChart_eventuallyEq_self
    (D : LocalizedFormEventuallyEqData I ω Chart) (x0 x1 : M) (y : E) :
    ManifoldForm.transitionPullbackInChart I x0 x1
        (localizedFormSum I D.activeCharts D.coefficient ω) =ᶠ[𝓝 y]
      ManifoldForm.transitionPullbackInChart I x0 x1 ω :=
  (D.transitionPullbackInChart_eq_self x0 x1).eventuallyEq

/-- Chartwise exterior-derivative reconstruction supplied by eventual equality. -/
theorem extDeriv_transitionPullbackInChart_eq_self
    (D : LocalizedFormEventuallyEqData I ω Chart) (x0 x1 : M) (y : E) :
    extDeriv
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (localizedFormSum I D.activeCharts D.coefficient ω)) y =
      extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y :=
  (D.transitionPullbackInChart_eventuallyEq_self x0 x1 y).extDeriv_eq

/--
The chartwise `extDeriv` field expected by
`ExtDerivPartitionReconstructionData.ofPartitionReconstructionData`.
-/
theorem chartwiseExtDeriv_eq_global
    (D : LocalizedFormEventuallyEqData I ω Chart) :
    ∀ x0 x1 y,
      extDeriv
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (localizedFormSum I D.activeCharts D.coefficient ω)) y =
        extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) y := by
  intro x0 x1 y
  exact D.extDeriv_transitionPullbackInChart_eq_self x0 x1 y

end LocalizedFormEventuallyEqData

namespace FiniteActiveOnCompact

/-- Compact finite-active partition data plus support containment gives
eventually-local reconstruction data. -/
def toLocalizedFormEventuallyEqData
    (P : FiniteActiveOnCompact (M := M) I) (ω : ManifoldForm I M k)
    (hωsupp : ManifoldForm.support I ω ⊆ P.K) :
    LocalizedFormEventuallyEqData I ω M where
  activeCharts := P.active
  coefficient := fun i y => P.partition i y
  supportSet := P.K
  localizedFormSum_eq_self_on := P.localizedFormSum_eqOn ω
  form_support_subset_supportSet := hωsupp

end FiniteActiveOnCompact

namespace SelectedBoxPartitionOfUnity

variable [Preorder E]
variable {ω : ManifoldForm I M k}

/-- Selected-box partition data plus support containment gives
eventually-local reconstruction data. -/
def toLocalizedFormEventuallyEqData
    (P : SelectedBoxPartitionOfUnity I ω)
    (hωsupp : ManifoldForm.support I ω ⊆ P.K) :
    LocalizedFormEventuallyEqData I ω M where
  activeCharts := P.active
  coefficient := fun i y => P.partition i y
  supportSet := P.K
  localizedFormSum_eq_self_on := P.localizedFormSum_eqOn
  form_support_subset_supportSet := hωsupp

end SelectedBoxPartitionOfUnity

end LocalizedEventually

section ExtDerivInputWrappers

universe u v w c i b

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}
variable {ω : ManifoldForm I M k}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}

namespace LocalizedFormEventuallyEqData

/--
Package a localized eventually-equality proof as the exterior-derivative
reconstruction augmentation of an existing partition reconstruction package.
-/
def toExtDerivPartitionReconstructionData
    (D : LocalizedFormEventuallyEqData I ω Chart)
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (hactive : R.activeCharts = D.activeCharts) :
    ExtDerivPartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece :=
  ExtDerivPartitionReconstructionData.ofPartitionReconstructionData
    R D.coefficient (by
      intro x0 x1 y
      rw [hactive]
      exact D.extDeriv_transitionPullbackInChart_eq_self x0 x1 y)

end LocalizedFormEventuallyEqData

namespace PartitionReconstructionData

/--
Wrapper with the reconstruction package as the primary receiver.  The
`hactive` hypothesis records that the eventually-equality data was built for
the same finite active set.
-/
def toExtDerivPartitionReconstructionDataOfLocalizedEventuallyEq
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (D : LocalizedFormEventuallyEqData I ω Chart)
    (hactive : R.activeCharts = D.activeCharts) :
    ExtDerivPartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece :=
  D.toExtDerivPartitionReconstructionData R hactive

end PartitionReconstructionData

end ExtDerivInputWrappers

end Stokes

end
