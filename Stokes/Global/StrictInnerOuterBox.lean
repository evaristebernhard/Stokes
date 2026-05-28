import Stokes.Global.CompactSupportStrictBuffer
import Stokes.Global.CompactActiveBoxes

/-!
# Strict inner/outer coordinate-box selection

This file contains the pure coordinate geometry needed before the current
compact-support buffer layer: a compact coordinate support can be put in a
closed inner box, and that inner box can be placed with a strict margin inside a
larger outer box.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section SingleCompactSet

/--
A compact coordinate support together with an inner closed box and an outer
strict box containing that inner box.
-/
structure StrictInnerOuterBoxSelection {n : Nat}
    (K : Set (Fin (n + 1) → Real)) where
  /-- Lower corner of the inner closed box. -/
  innerLower : Fin (n + 1) → Real
  /-- Upper corner of the inner closed box. -/
  innerUpper : Fin (n + 1) → Real
  /-- Lower corner of the outer strict box. -/
  outerLower : Fin (n + 1) → Real
  /-- Upper corner of the outer strict box. -/
  outerUpper : Fin (n + 1) → Real
  /-- The inner box is ordered coordinatewise. -/
  inner_le_upper : innerLower ≤ innerUpper
  /-- The outer box is ordered coordinatewise. -/
  outer_le_upper : outerLower ≤ outerUpper
  /-- The compact coordinate support lies in the inner closed box. -/
  K_subset_innerIcc : K ⊆ Set.Icc innerLower innerUpper
  /-- The whole inner closed box lies strictly inside the outer box. -/
  innerIcc_subset_outerInterior :
    Set.Icc innerLower innerUpper ⊆ boxInteriorSupportBox outerLower outerUpper

namespace StrictInnerOuterBoxSelection

variable {n : Nat} {K : Set (Fin (n + 1) → Real)}

/-- Constructor from explicit strict coordinate margins. -/
def ofMargins
    (c d a b : Fin (n + 1) → Real)
    (hcd : c ≤ d) (hab : a ≤ b)
    (hK : K ⊆ Set.Icc c d)
    (hleft : ∀ i : Fin (n + 1), a i < c i)
    (hright : ∀ i : Fin (n + 1), d i < b i) :
    StrictInnerOuterBoxSelection K where
  innerLower := c
  innerUpper := d
  outerLower := a
  outerUpper := b
  inner_le_upper := hcd
  outer_le_upper := hab
  K_subset_innerIcc := hK
  innerIcc_subset_outerInterior :=
    Icc_subset_boxInteriorSupportBox hleft hright

/-- The selected compact set also lies in the outer strict box. -/
theorem K_subset_outerInterior (D : StrictInnerOuterBoxSelection K) :
    K ⊆ boxInteriorSupportBox D.outerLower D.outerUpper :=
  D.K_subset_innerIcc.trans D.innerIcc_subset_outerInterior

/-- The selected inner closed box is contained in the outer strict box. -/
theorem inner_subset_outerInterior (D : StrictInnerOuterBoxSelection K) :
    Set.Icc D.innerLower D.innerUpper ⊆
      boxInteriorSupportBox D.outerLower D.outerUpper :=
  D.innerIcc_subset_outerInterior

end StrictInnerOuterBoxSelection

/--
Every compact coordinate support admits an inner closed box and an outer strict
box, with both boxes ordered coordinatewise.
-/
theorem exists_innerOuterBoxes_of_isCompact {n : Nat}
    {K : Set (Fin (n + 1) → Real)} (hK : IsCompact K) :
    ∃ c d a b : Fin (n + 1) → Real,
      c ≤ d ∧ a ≤ b ∧ K ⊆ Set.Icc c d ∧
        Set.Icc c d ⊆ boxInteriorSupportBox a b := by
  rcases exists_Icc_subset_of_isCompact_fin hK with ⟨c, d, hcd, hKcd⟩
  let a : Fin (n + 1) → Real := fun i => c i - 1
  let b : Fin (n + 1) → Real := fun i => d i + 1
  refine ⟨c, d, a, b, hcd, ?_, hKcd, ?_⟩
  · intro i
    dsimp [a, b]
    have h := hcd i
    linarith
  · exact Icc_subset_boxInteriorSupportBox
      (a := a) (b := b) (c := c) (d := d)
      (by
        intro i
        dsimp [a]
        linarith)
      (by
        intro i
        dsimp [b]
        linarith)

/--
Margin-strengthened version of `exists_innerOuterBoxes_of_isCompact`.
-/
theorem exists_innerOuterBoxes_with_margins_of_isCompact {n : Nat}
    {K : Set (Fin (n + 1) → Real)} (hK : IsCompact K) :
    ∃ c d a b : Fin (n + 1) → Real,
      c ≤ d ∧ a ≤ b ∧ K ⊆ Set.Icc c d ∧
        (∀ i : Fin (n + 1), a i < c i) ∧
        (∀ i : Fin (n + 1), d i < b i) ∧
        Set.Icc c d ⊆ boxInteriorSupportBox a b := by
  rcases exists_Icc_subset_of_isCompact_fin hK with ⟨c, d, hcd, hKcd⟩
  let a : Fin (n + 1) → Real := fun i => c i - 1
  let b : Fin (n + 1) → Real := fun i => d i + 1
  have hab : a ≤ b := by
    intro i
    dsimp [a, b]
    have h := hcd i
    linarith
  have hleft : ∀ i : Fin (n + 1), a i < c i := by
    intro i
    dsimp [a]
    linarith
  have hright : ∀ i : Fin (n + 1), d i < b i := by
    intro i
    dsimp [b]
    linarith
  exact ⟨c, d, a, b, hcd, hab, hKcd, hleft, hright,
    Icc_subset_boxInteriorSupportBox hleft hright⟩

/-- Existence spelling for APIs that prefer existential selections. -/
theorem exists_strictInnerOuterBoxSelection_of_isCompact {n : Nat}
    {K : Set (Fin (n + 1) → Real)} (hK : IsCompact K) :
    ∃ _ : StrictInnerOuterBoxSelection K, True := by
  rcases exists_innerOuterBoxes_with_margins_of_isCompact hK with
    ⟨c, d, a, b, hcd, hab, hKcd, hleft, hright, _hinnerOuter⟩
  exact ⟨StrictInnerOuterBoxSelection.ofMargins c d a b hcd hab hKcd hleft hright,
    trivial⟩

/-- Pack the compact-set theorem as a reusable selection structure. -/
def strictInnerOuterBoxSelectionOfCompact {n : Nat}
    {K : Set (Fin (n + 1) → Real)} (hK : IsCompact K) :
    StrictInnerOuterBoxSelection K :=
  Classical.choose (exists_strictInnerOuterBoxSelection_of_isCompact hK)

end SingleCompactSet

section ActiveFinite

universe u v w

/--
Simultaneous inner/outer box choices over a finite active family of compact
coordinate supports.
-/
structure ActiveStrictInnerOuterBoxSelections {n : Nat} {α : Type u}
    (active : Finset α)
    (coordSupport : α → Set (Fin (n + 1) → Real)) where
  /-- Lower corners of the inner closed boxes. -/
  innerLower : α → Fin (n + 1) → Real
  /-- Upper corners of the inner closed boxes. -/
  innerUpper : α → Fin (n + 1) → Real
  /-- Lower corners of the outer strict boxes. -/
  outerLower : α → Fin (n + 1) → Real
  /-- Upper corners of the outer strict boxes. -/
  outerUpper : α → Fin (n + 1) → Real
  /-- Active inner boxes are ordered coordinatewise. -/
  inner_le_upper :
    ∀ i, i ∈ active → innerLower i ≤ innerUpper i
  /-- Active outer boxes are ordered coordinatewise. -/
  outer_le_upper :
    ∀ i, i ∈ active → outerLower i ≤ outerUpper i
  /-- Each active compact coordinate support lies in its inner closed box. -/
  coordSupport_subset_innerIcc :
    ∀ i, i ∈ active →
      coordSupport i ⊆ Set.Icc (innerLower i) (innerUpper i)
  /-- Each active inner closed box lies strictly inside its outer box. -/
  innerIcc_subset_outerInterior :
    ∀ i, i ∈ active →
      Set.Icc (innerLower i) (innerUpper i) ⊆
        boxInteriorSupportBox (outerLower i) (outerUpper i)

namespace ActiveStrictInnerOuterBoxSelections

variable {n : Nat} {α : Type u}
variable {active : Finset α}
variable {coordSupport : α → Set (Fin (n + 1) → Real)}

/-- Active coordinate supports also lie in their selected outer strict boxes. -/
theorem coordSupport_subset_outerInterior
    (D : ActiveStrictInnerOuterBoxSelections active coordSupport)
    {i : α} (hi : i ∈ active) :
    coordSupport i ⊆ boxInteriorSupportBox (D.outerLower i) (D.outerUpper i) :=
  (D.coordSupport_subset_innerIcc i hi).trans
    (D.innerIcc_subset_outerInterior i hi)

/--
Build simultaneous active selections from compactness of every active
coordinate support.  Inactive indices use the zero box as harmless fallback
data because all guarantees are active-indexed.
-/
def ofCompact
    (hcompact : ∀ i, i ∈ active → IsCompact (coordSupport i)) :
    ActiveStrictInnerOuterBoxSelections active coordSupport := by
  classical
  let selected (i : α) (hi : i ∈ active) :
      StrictInnerOuterBoxSelection (coordSupport i) :=
    strictInnerOuterBoxSelectionOfCompact (hcompact i hi)
  let innerLower : α → Fin (n + 1) → Real := fun i =>
    if hi : i ∈ active then (selected i hi).innerLower else 0
  let innerUpper : α → Fin (n + 1) → Real := fun i =>
    if hi : i ∈ active then (selected i hi).innerUpper else 0
  let outerLower : α → Fin (n + 1) → Real := fun i =>
    if hi : i ∈ active then (selected i hi).outerLower else 0
  let outerUpper : α → Fin (n + 1) → Real := fun i =>
    if hi : i ∈ active then (selected i hi).outerUpper else 0
  refine
    { innerLower := innerLower
      innerUpper := innerUpper
      outerLower := outerLower
      outerUpper := outerUpper
      inner_le_upper := ?_
      outer_le_upper := ?_
      coordSupport_subset_innerIcc := ?_
      innerIcc_subset_outerInterior := ?_ }
  · intro i hi
    simpa [innerLower, innerUpper, hi, selected] using
      (selected i hi).inner_le_upper
  · intro i hi
    simpa [outerLower, outerUpper, hi, selected] using
      (selected i hi).outer_le_upper
  · intro i hi
    simpa [innerLower, innerUpper, hi, selected] using
      (selected i hi).K_subset_innerIcc
  · intro i hi
    simpa [innerLower, innerUpper, outerLower, outerUpper, hi, selected] using
      (selected i hi).innerIcc_subset_outerInterior

end ActiveStrictInnerOuterBoxSelections

/-- Existence spelling of simultaneous active inner/outer selections. -/
theorem exists_activeStrictInnerOuterBoxSelections_of_isCompact
    {n : Nat} {α : Type u} {active : Finset α}
    {coordSupport : α → Set (Fin (n + 1) → Real)}
    (hcompact : ∀ i, i ∈ active → IsCompact (coordSupport i)) :
    ∃ _ : ActiveStrictInnerOuterBoxSelections active coordSupport, True :=
  ⟨ActiveStrictInnerOuterBoxSelections.ofCompact hcompact, trivial⟩

/--
Finite-active package wrapper for the same active-family selection theorem.
-/
theorem exists_finiteActiveStrictInnerOuterBoxSelections_of_isCompact
    {n : Nat}
    {H : Type v} [TopologicalSpace H]
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    (P : FiniteActiveOnCompact (M := M) I)
    (coordSupport : M → Set (Fin (n + 1) → Real))
    (hcompact : ∀ i, i ∈ P.active → IsCompact (coordSupport i)) :
    ∃ _ : ActiveStrictInnerOuterBoxSelections P.active coordSupport, True :=
  exists_activeStrictInnerOuterBoxSelections_of_isCompact hcompact

end ActiveFinite

end Stokes

end
