import Stokes.Global.InteriorAssignedBoxSupport

/-!
# Compact-support assigned-box support fields

This module keeps the small assigned-box support handoff used by the current
global route without importing the older gap-audit file.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section AssignedBoxFeed

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/--
The selected-partition fields consumed by the interior assigned-box support
handoff: base chart-coordinate support plus coefficient support in that
coordinate carrier.
-/
abbrev InteriorAssignedBoxFields
    (P : SelectedBoxPartitionOfUnity I omega)
    (coordSupport : M -> Set (Fin (n + 1) -> Real)) : Prop :=
  (∀ i, i ∈ P.active ->
      tsupport (ManifoldForm.transitionPullbackInChart I i i omega) ⊆
        coordSupport i) ∧
    (∀ i, i ∈ P.active ->
      tsupport
          (ManifoldForm.transitionCoefficientInChart I i i (P.partition i)) ∩
          coordSupport i ⊆
        boxInteriorSupportBox (P.lower i) (P.upper i))

theorem interiorAssignedBox_from_fields
    (P : SelectedBoxPartitionOfUnity I omega)
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (h : InteriorAssignedBoxFields P coordSupport)
    {i : M} (hi : i ∈ P.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) omega)) ⊆
      boxInteriorSupportBox (P.lower i) (P.upper i) :=
  P.localized_tsupport_subset_selectedInteriorBox_of_coordSupport
    (omega := omega) h.1 h.2 hi

end AssignedBoxFeed

end Stokes

end
