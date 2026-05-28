import Stokes.ManifoldFormZero

/-!
# Support transfer for zero-extended transition representatives

This file records the local support fact behind the zero-extension route:
extending a transition representative by zero cannot enlarge its algebraic or
topological support.  The statement is deliberately independent of the
cover-indexed Stokes assembly.

This is the useful direction for half-space boxes.  Those boxes have strict
inequalities on the artificial faces, so they are not closed carriers; the
proof must use

```
tsupport (zeroOutside s f) ⊆ tsupport f
```

rather than a closed-carrier upgrade from ordinary support.
-/

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace Stokes

universe u v w

section ZeroOutsideSupport

variable {X A : Type*} [Zero A]

/-- Extending by zero cannot create ordinary support outside the original
ordinary support. -/
theorem support_zeroOutside_subset_support {s : Set X} {f : X → A} :
    Function.support (zeroOutside s f) ⊆ Function.support f := by
  classical
  intro x hx
  rw [Function.mem_support] at hx ⊢
  by_cases hxs : x ∈ s
  · simpa [zeroOutside, hxs] using hx
  · exact False.elim (hx (zeroOutside_eq_zero_of_notMem hxs))

/-- The ordinary support of a zero extension is contained in the extension set
and in the ordinary support of the original function. -/
theorem support_zeroOutside_subset_inter_support {s : Set X} {f : X → A} :
    Function.support (zeroOutside s f) ⊆ s ∩ Function.support f := by
  intro x hx
  exact ⟨support_zeroOutside_subset (s := s) (f := f) hx,
    support_zeroOutside_subset_support (s := s) (f := f) hx⟩

variable [TopologicalSpace X]

/-- Extending by zero cannot enlarge topological support. -/
theorem tsupport_zeroOutside_subset_tsupport {s : Set X} {f : X → A} :
    tsupport (zeroOutside s f) ⊆ tsupport f := by
  simpa [tsupport] using
    closure_mono (support_zeroOutside_subset_support (s := s) (f := f))

/-- The topological support of a zero extension is contained in the closure of
the extension set. -/
theorem tsupport_zeroOutside_subset_closure {s : Set X} {f : X → A} :
    tsupport (zeroOutside s f) ⊆ closure s := by
  simpa [tsupport] using
    closure_mono (support_zeroOutside_subset (s := s) (f := f))

/-- Carrier-transfer spelling: any topological support bound for the original
function is inherited by its zero extension, without requiring the carrier to
be closed. -/
theorem tsupport_zeroOutside_subset_of_tsupport_subset {s S : Set X}
    {f : X → A} (hsupp : tsupport f ⊆ S) :
    tsupport (zeroOutside s f) ⊆ S :=
  tsupport_zeroOutside_subset_tsupport.trans hsupp

end ZeroOutsideSupport

namespace ManifoldForm

section TransitionSupport

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H}
variable {k : Nat}
variable {x0 x1 : M}
variable {ω : ManifoldForm I M k}

/-- A nonzero zero-extended transition representative is nonzero for the old
transition representative. -/
theorem transitionPullbackInChart_ne_zero_of_transitionPullbackInChartZero_ne_zero
    {y : E}
    (hy : transitionPullbackInChartZero I x0 x1 ω y ≠ 0) :
    transitionPullbackInChart I x0 x1 ω y ≠ 0 :=
  support_zeroOutside_subset_support
    (s := chartTransitionSource I x0 x1)
    (f := transitionPullbackInChart I x0 x1 ω)
    (by simpa [Function.mem_support] using hy)

/-- Ordinary support of the zero transition representative lies in the ordinary
support of the old transition representative. -/
theorem transitionPullbackInChartZero_support_subset_transition_support :
    Function.support (transitionPullbackInChartZero I x0 x1 ω) ⊆
      Function.support (transitionPullbackInChart I x0 x1 ω) :=
  support_zeroOutside_subset_support
    (s := chartTransitionSource I x0 x1)
    (f := transitionPullbackInChart I x0 x1 ω)

/-- Ordinary support of the zero transition representative lies in the
transition source and in the old ordinary support. -/
theorem transitionPullbackInChartZero_support_subset_source_inter_transition_support :
    Function.support (transitionPullbackInChartZero I x0 x1 ω) ⊆
      chartTransitionSource I x0 x1 ∩
        Function.support (transitionPullbackInChart I x0 x1 ω) :=
  support_zeroOutside_subset_inter_support
    (s := chartTransitionSource I x0 x1)
    (f := transitionPullbackInChart I x0 x1 ω)

/-- Topological support of the zero transition representative is contained in
the old transition representative's topological support.  This is the key
half-space support transfer: no closedness of the target carrier is required. -/
theorem transitionPullbackInChartZero_tsupport_subset_transition_tsupport :
    tsupport (transitionPullbackInChartZero I x0 x1 ω) ⊆
      tsupport (transitionPullbackInChart I x0 x1 ω) :=
  tsupport_zeroOutside_subset_tsupport
    (s := chartTransitionSource I x0 x1)
    (f := transitionPullbackInChart I x0 x1 ω)

/-- Any old transition topological-support bound is inherited by the
zero-extended transition representative. -/
theorem transitionPullbackInChartZero_tsupport_subset_of_transition_tsupport_subset
    {S : Set E}
    (hsupport : tsupport (transitionPullbackInChart I x0 x1 ω) ⊆ S) :
    tsupport (transitionPullbackInChartZero I x0 x1 ω) ⊆ S :=
  transitionPullbackInChartZero_tsupport_subset_transition_tsupport.trans hsupport

/-- The zero transition representative is topologically supported in the
closure of the concrete transition source. -/
theorem transitionPullbackInChartZero_tsupport_subset_closure_source :
    tsupport (transitionPullbackInChartZero I x0 x1 ω) ⊆
      closure (chartTransitionSource I x0 x1) :=
  tsupport_zeroOutside_subset_closure
    (s := chartTransitionSource I x0 x1)
    (f := transitionPullbackInChart I x0 x1 ω)

end TransitionSupport

end ManifoldForm

end Stokes

end
