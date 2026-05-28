import Stokes.Global.InteriorBoundarySupportZero

/-!
# Compact-open coordinate box selection

This file isolates the honest geometric replacement for the tempting but false
single-box statement

`K` compact, `K ⊆ U`, `U` open `⇒ ∃ a b, K ⊆ boxInteriorSupportBox a b ∧ Set.Icc a b ⊆ U`.

That statement is false for disconnected open sets: two points in two disjoint
open balls generally cannot be enclosed by one axis-aligned closed box still
contained in the union.  The true local tool is pointwise box selection, and
compactness upgrades it to a finite box cover.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section InteriorOpenBoxes

/--
Every neighborhood of a finite real-coordinate point contains a closed
coordinate box around the point, and the point lies in the corresponding strict
interior support box.

The selected closed box is centered at `x` with a small uniform coordinate
radius obtained from a closed metric ball contained in the given neighborhood.
-/
theorem exists_boxInteriorSupportBox_mem_nhds_subset_of_mem_nhds {n : Nat}
    {U : Set (Fin (n + 1) → Real)} {x : Fin (n + 1) → Real}
    (hU : U ∈ 𝓝 x) :
    ∃ a b : Fin (n + 1) → Real,
      a ≤ b ∧
        x ∈ boxInteriorSupportBox a b ∧
          boxInteriorSupportBox a b ∈ 𝓝 x ∧
            Set.Icc a b ⊆ U := by
  obtain ⟨ε, hεpos, hεsubset⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  let δ : Real := ε / 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    linarith
  let a : Fin (n + 1) → Real := fun i => x i - δ
  let b : Fin (n + 1) → Real := fun i => x i + δ
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp [a, b]
    linarith
  · intro i
    constructor <;> dsimp [a, b] <;> linarith
  · refine mem_of_superset (Metric.ball_mem_nhds x hδpos) ?_
    intro y hy i
    have hcoord : dist (y i) (x i) < δ := by
      rw [Metric.mem_ball] at hy
      rw [dist_pi_lt_iff hδpos] at hy
      exact hy i
    rw [Real.dist_eq, abs_sub_lt_iff] at hcoord
    constructor
    · dsimp [a]
      linarith
    · dsimp [b]
      linarith
  · intro y hy
    apply hεsubset
    rw [Metric.mem_closedBall]
    rw [dist_pi_le_iff (le_of_lt hεpos)]
    intro i
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor
    · have hyi : y i ≤ x i + δ := by
        simpa [b] using hy.2 i
      dsimp [δ] at hyi ⊢
      linarith
    · have hyi : x i - δ ≤ y i := by
        simpa [a] using hy.1 i
      dsimp [δ] at hyi ⊢
      linarith

/--
Point version specialized to open sets.

If `x ∈ U` and `U` is open, there is a strict coordinate support box around
`x` whose closed box is contained in `U`.
-/
theorem exists_boxInteriorSupportBox_subset_open_of_mem {n : Nat}
    {U : Set (Fin (n + 1) → Real)} {x : Fin (n + 1) → Real}
    (hxU : x ∈ U) (hUopen : IsOpen U) :
    ∃ a b : Fin (n + 1) → Real,
      a ≤ b ∧ x ∈ boxInteriorSupportBox a b ∧ Set.Icc a b ⊆ U := by
  obtain ⟨a, b, hle, hxbox, _hboxnhds, hIcc⟩ :=
    exists_boxInteriorSupportBox_mem_nhds_subset_of_mem_nhds
      (n := n) (x := x) (hUopen.mem_nhds hxU)
  exact ⟨a, b, hle, hxbox, hIcc⟩

/--
Finite compact-open box cover in finite real coordinates.

For a compact set `K` contained in an open set `U`, finitely many strict
coordinate boxes cover `K`, and each associated closed box lies inside `U`.
This is the correct compact-open replacement for the false single-box version.
-/
theorem exists_finite_boxInteriorSupportBox_cover_subset_open_of_isCompact
    {n : Nat} {K U : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hKU : K ⊆ U) (hUopen : IsOpen U) :
    ∃ centers : Finset (Fin (n + 1) → Real),
      (∀ x ∈ centers, x ∈ K) ∧
        ∃ lower upper : (Fin (n + 1) → Real) → Fin (n + 1) → Real,
          (∀ x ∈ centers,
            lower x ≤ upper x ∧
              x ∈ boxInteriorSupportBox (lower x) (upper x) ∧
                Set.Icc (lower x) (upper x) ⊆ U) ∧
            K ⊆ ⋃ x ∈ centers, boxInteriorSupportBox (lower x) (upper x) := by
  classical
  have hpoint :
      ∀ x ∈ K,
        ∃ a b : Fin (n + 1) → Real,
          a ≤ b ∧
            x ∈ boxInteriorSupportBox a b ∧
              boxInteriorSupportBox a b ∈ 𝓝 x ∧
                Set.Icc a b ⊆ U := by
    intro x hx
    exact exists_boxInteriorSupportBox_mem_nhds_subset_of_mem_nhds
      (n := n) (x := x) (hUopen.mem_nhds (hKU hx))
  choose lower upper hle hxbox hboxnhds hIcc using hpoint
  let lower' : (Fin (n + 1) → Real) → Fin (n + 1) → Real :=
    fun x => if hx : x ∈ K then lower x hx else x
  let upper' : (Fin (n + 1) → Real) → Fin (n + 1) → Real :=
    fun x => if hx : x ∈ K then upper x hx else x
  have hle' : ∀ x ∈ K, lower' x ≤ upper' x := by
    intro x hx
    simpa [lower', upper', hx] using hle x hx
  have hxbox' : ∀ x ∈ K, x ∈ boxInteriorSupportBox (lower' x) (upper' x) := by
    intro x hx
    simpa [lower', upper', hx] using hxbox x hx
  have hboxnhds' :
      ∀ x ∈ K, boxInteriorSupportBox (lower' x) (upper' x) ∈ 𝓝 x := by
    intro x hx
    simpa [lower', upper', hx] using hboxnhds x hx
  have hIcc' : ∀ x ∈ K, Set.Icc (lower' x) (upper' x) ⊆ U := by
    intro x hx
    simpa [lower', upper', hx] using hIcc x hx
  obtain ⟨centers, hcentersK, hcover⟩ :=
    hK.elim_nhds_subcover
      (fun x => boxInteriorSupportBox (lower' x) (upper' x))
      (fun x hx => hboxnhds' x hx)
  refine ⟨centers, hcentersK, lower', upper', ?_, hcover⟩
  intro x hx
  have hxK : x ∈ K := hcentersK x hx
  exact ⟨hle' x hxK, hxbox' x hxK, hIcc' x hxK⟩

/--
Finite compact-open box cover for a compact topological support.

This is the support-shaped version used by local compact-support Stokes
arguments before choosing a partition subordinate to the finitely many boxes.
-/
theorem exists_finite_boxInteriorSupportBox_cover_subset_open_of_compact_tsupport
    {n : Nat} {β : Type*} [Zero β]
    (ω : (Fin (n + 1) → Real) → β)
    {U : Set (Fin (n + 1) → Real)}
    (hcompact : IsCompact (tsupport ω))
    (hsuppU : tsupport ω ⊆ U) (hUopen : IsOpen U) :
    ∃ centers : Finset (Fin (n + 1) → Real),
      (∀ x ∈ centers, x ∈ tsupport ω) ∧
        ∃ lower upper : (Fin (n + 1) → Real) → Fin (n + 1) → Real,
          (∀ x ∈ centers,
            lower x ≤ upper x ∧
              x ∈ boxInteriorSupportBox (lower x) (upper x) ∧
                Set.Icc (lower x) (upper x) ⊆ U) ∧
            tsupport ω ⊆ ⋃ x ∈ centers, boxInteriorSupportBox (lower x) (upper x) :=
  exists_finite_boxInteriorSupportBox_cover_subset_open_of_isCompact
    (K := tsupport ω) hcompact hsuppU hUopen

end InteriorOpenBoxes

end Stokes

end
