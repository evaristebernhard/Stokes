import Stokes.Global.ChartwiseSmoothToLocal

/-!
# Compact-support integrability wrappers

This file isolates the basic measure-theoretic input used by the global
assembly layer: continuous real-valued integrands on compact coordinate boxes
are integrable on those boxes, and compactly supported continuous integrands
are globally integrable.

The wrappers are intentionally generic.  Stokes-specific projections at the
end merely expose the same integrability facts for the existing local
smoothness data packages.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

universe u v w

section GenericCompact

variable {X : Type u} [MeasurableSpace X] [TopologicalSpace X]
variable [OpensMeasurableSpace X] [T2Space X]
variable {F : Type v} [NormedAddCommGroup F]
variable {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

/-- A continuous function on a compact set is integrable on that set. -/
theorem integrableOn_of_continuousOn_isCompact {K : Set X} {f : X → F}
    (hK : IsCompact K) (hf : ContinuousOn f K) :
    IntegrableOn f K μ :=
  ContinuousOn.integrableOn_compact hK hf

/--
If a continuous-on-`K` function is algebraically supported in compact `K`, then
it is integrable on the ambient space.
-/
theorem integrable_of_continuousOn_isCompact_support_subset {K : Set X}
    {f : X → F} (hK : IsCompact K) (hf : ContinuousOn f K)
    (hsupp : Function.support f ⊆ K) :
    Integrable f μ := by
  classical
  have hIntOn : IntegrableOn f K μ :=
    integrableOn_of_continuousOn_isCompact (μ := μ) hK hf
  have hInd : Integrable (K.indicator f) μ :=
    (integrable_indicator_iff hK.measurableSet).2 hIntOn
  refine hInd.congr (Filter.Eventually.of_forall ?_)
  intro x
  by_cases hx : x ∈ K
  · exact Set.indicator_of_mem hx f
  · have hxzero : f x = 0 := by
      exact Function.notMem_support.mp fun hxsupp => hx (hsupp hxsupp)
    rw [Set.indicator_of_notMem hx, hxzero]

/--
Topological-support version of
`integrable_of_continuousOn_isCompact_support_subset`.
-/
theorem integrable_of_continuousOn_isCompact_tsupport_subset {K : Set X}
    {f : X → F} (hK : IsCompact K) (hf : ContinuousOn f K)
    (htsupp : tsupport f ⊆ K) :
    Integrable f μ :=
  integrable_of_continuousOn_isCompact_support_subset (μ := μ) hK hf
    ((subset_tsupport f).trans htsupp)

end GenericCompact

section CompactSupportData

variable {X : Type u} [TopologicalSpace X]
variable {F : Type v} [NormedAddCommGroup F]

/--
Compact-support integrability data for an ambient function.

The support set is explicit so callers can use a selected coordinate support
set or chart box instead of relying on automation to discover compact support.
-/
structure CompactSupportIntegrabilityData (f : X → F) where
  /-- Compact set carrying the algebraic support of the integrand. -/
  supportSet : Set X
  /-- The support carrier is compact. -/
  isCompact_supportSet : IsCompact supportSet
  /-- The integrand is continuous on the support carrier. -/
  continuousOn_supportSet : ContinuousOn f supportSet
  /-- The integrand vanishes outside the support carrier. -/
  support_subset_supportSet : Function.support f ⊆ supportSet

namespace CompactSupportIntegrabilityData

variable {f : X → F}

/-- Constructor from explicit compact support and continuity data. -/
def of (K : Set X) (hK : IsCompact K) (hf : ContinuousOn f K)
    (hsupp : Function.support f ⊆ K) :
    CompactSupportIntegrabilityData f where
  supportSet := K
  isCompact_supportSet := hK
  continuousOn_supportSet := hf
  support_subset_supportSet := hsupp

/-- Constructor from topological-support containment in a compact set. -/
def ofTSupportSubset (K : Set X) (hK : IsCompact K)
    (hf : ContinuousOn f K) (htsupp : tsupport f ⊆ K) :
    CompactSupportIntegrabilityData f where
  supportSet := K
  isCompact_supportSet := hK
  continuousOn_supportSet := hf
  support_subset_supportSet := (subset_tsupport f).trans htsupp

section Measure

variable [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
variable {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

/-- The recorded compact support set gives integrability on that set. -/
theorem integrableOn_supportSet (D : CompactSupportIntegrabilityData f) :
    IntegrableOn f D.supportSet μ :=
  integrableOn_of_continuousOn_isCompact (μ := μ)
    D.isCompact_supportSet D.continuousOn_supportSet

/-- The recorded compact support and continuity data give global integrability. -/
theorem integrable (D : CompactSupportIntegrabilityData f) :
    Integrable f μ :=
  integrable_of_continuousOn_isCompact_support_subset (μ := μ)
    D.isCompact_supportSet D.continuousOn_supportSet D.support_subset_supportSet

/-- A globally integrable compactly supported function is integrable on every set. -/
theorem integrableOn (D : CompactSupportIntegrabilityData f) (s : Set X) :
    IntegrableOn f s μ :=
  D.integrable.integrableOn

end Measure

end CompactSupportIntegrabilityData

end CompactSupportData

section ContDiffWrappers

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable [MeasurableSpace E] [OpensMeasurableSpace E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace Real F]
variable {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
variable {m : WithTop ℕ∞}

/-- `ContDiffOn` on a compact set implies integrability on that set. -/
theorem integrableOn_of_contDiffOn_isCompact {K : Set E} {f : E → F}
    (hK : IsCompact K) (hf : ContDiffOn Real m f K) :
    IntegrableOn f K μ :=
  integrableOn_of_continuousOn_isCompact (μ := μ) hK hf.continuousOn

/--
Compact-support version of `integrableOn_of_contDiffOn_isCompact`, using
algebraic support containment.
-/
theorem integrable_of_contDiffOn_isCompact_support_subset {K : Set E}
    {f : E → F} (hK : IsCompact K) (hf : ContDiffOn Real m f K)
    (hsupp : Function.support f ⊆ K) :
    Integrable f μ :=
  integrable_of_continuousOn_isCompact_support_subset (μ := μ) hK
    hf.continuousOn hsupp

/--
Compact-support version of `integrableOn_of_contDiffOn_isCompact`, using
topological support containment.
-/
theorem integrable_of_contDiffOn_isCompact_tsupport_subset {K : Set E}
    {f : E → F} (hK : IsCompact K) (hf : ContDiffOn Real m f K)
    (htsupp : tsupport f ⊆ K) :
    Integrable f μ :=
  integrable_of_continuousOn_isCompact_tsupport_subset (μ := μ) hK
    hf.continuousOn htsupp

namespace CompactSupportIntegrabilityData

variable {f : E → F}

/-- Constructor from compact support and `ContDiffOn` on the support set. -/
def ofContDiffOn (K : Set E) (hK : IsCompact K)
    (hf : ContDiffOn Real m f K) (hsupp : Function.support f ⊆ K) :
    CompactSupportIntegrabilityData f :=
  of K hK hf.continuousOn hsupp

/-- Constructor from topological support and `ContDiffOn` on the support set. -/
def ofContDiffOnTSupportSubset (K : Set E) (hK : IsCompact K)
    (hf : ContDiffOn Real m f K) (htsupp : tsupport f ⊆ K) :
    CompactSupportIntegrabilityData f :=
  ofTSupportSubset K hK hf.continuousOn htsupp

end CompactSupportIntegrabilityData

end ContDiffWrappers

section Boxes

variable {ι : Type u} [Fintype ι]

/--
Primary box wrapper: a real-valued integrand continuous on a compact coordinate
box is integrable on that box.
-/
theorem integrableOn_Icc_real_of_continuousOn
    {a b : ι → Real} {f : (ι → Real) → Real}
    (hf : ContinuousOn f (Icc a b)) :
    IntegrableOn f (Icc a b) :=
  integrableOn_of_continuousOn_isCompact (μ := volume) isCompact_Icc hf

/-- `ContDiffOn` version of `integrableOn_Icc_real_of_continuousOn`. -/
theorem integrableOn_Icc_real_of_contDiffOn {m : WithTop ℕ∞}
    {a b : ι → Real} {f : (ι → Real) → Real}
    (hf : ContDiffOn Real m f (Icc a b)) :
    IntegrableOn f (Icc a b) :=
  integrableOn_Icc_real_of_continuousOn hf.continuousOn

/-- Normed-space-valued variant of the compact coordinate-box wrapper. -/
theorem integrableOn_Icc_of_continuousOn {F : Type v} [NormedAddCommGroup F]
    {a b : ι → Real} {f : (ι → Real) → F}
    (hf : ContinuousOn f (Icc a b)) :
    IntegrableOn f (Icc a b) :=
  integrableOn_of_continuousOn_isCompact (μ := volume) isCompact_Icc hf

/-- Normed-space-valued `ContDiffOn` coordinate-box wrapper. -/
theorem integrableOn_Icc_of_contDiffOn {F : Type v}
    [NormedAddCommGroup F] [NormedSpace Real F] {m : WithTop ℕ∞}
    {a b : ι → Real} {f : (ι → Real) → F}
    (hf : ContDiffOn Real m f (Icc a b)) :
    IntegrableOn f (Icc a b) :=
  integrableOn_Icc_of_continuousOn hf.continuousOn

end Boxes

section LocalSmoothnessProjections

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ρ : M → Real} {ω : ManifoldForm I M n}
variable {U : Set (Fin (n + 1) → Real)}
variable {a b : Fin (n + 1) → Real}

namespace LocalizedSmoothnessData

/--
The localized transition-pullback representative recorded by
`LocalizedSmoothnessData` is integrable on any closed box contained in its
smoothness set.
-/
theorem integrableOn_Icc
    (D : LocalizedSmoothnessData I x0 x1 ρ ω U)
    (hbox : Icc a b ⊆ U) :
    IntegrableOn
      (ManifoldForm.transitionPullbackInChart I x0 x1
        (ManifoldForm.localizedForm I ρ ω))
      (Icc a b) :=
  integrableOn_Icc_of_contDiffOn (m := (⊤ : WithTop ℕ∞))
    (D.localized_contDiffOn.mono hbox)

end LocalizedSmoothnessData

namespace ChartwiseSmoothLocalBoxData

/--
The transition-pullback representative in a chartwise-smooth local box is
integrable on the recorded coordinate box.
-/
theorem transitionPullback_integrableOn [IsManifold I ⊤ M]
    (D : ChartwiseSmoothLocalBoxData I ω) :
    IntegrableOn
      (ManifoldForm.transitionPullbackInChart I D.sourceChart D.targetChart ω)
      (Icc D.lowerCorner D.upperCorner) :=
  integrableOn_Icc_of_contDiffOn (m := (⊤ : WithTop ℕ∞))
    (D.transitionPullback_contDiffOn.mono D.Icc_subset_smoothSet)

end ChartwiseSmoothLocalBoxData

namespace LocalizedChartwiseSmoothLocalBoxData

/--
The localized transition-pullback representative in a localized
chartwise-smooth local box is integrable on the recorded coordinate box.
-/
theorem transitionPullback_integrableOn [IsManifold I ⊤ M]
    (D : LocalizedChartwiseSmoothLocalBoxData I ω ρ) :
    IntegrableOn
      (ManifoldForm.transitionPullbackInChart I D.sourceChart D.targetChart
        (ManifoldForm.localizedForm I ρ ω))
      (Icc D.lowerCorner D.upperCorner) :=
  integrableOn_Icc_of_contDiffOn (m := (⊤ : WithTop ℕ∞))
    (D.transitionPullback_contDiffOn.mono D.Icc_subset_smoothSet)

end LocalizedChartwiseSmoothLocalBoxData

end LocalSmoothnessProjections

end Stokes

end
