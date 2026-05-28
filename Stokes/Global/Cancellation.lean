import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Stokes.Global.Assembly
import Stokes.Global.Theorem

/-!
# Artificial interior-boundary cancellation packages

This file isolates the purely algebraic cancellation input used by the global
Stokes assembly skeletons.  The geometric layer should provide either
pointwise-vanishing artificial boundary terms or a fixed-point-free pairing of
opposite artificial faces; this module turns those data into the finite-sum
field expected by `GlobalStokesAssemblyData` and `GlobalStokesData`.
-/

noncomputable section

open scoped BigOperators

namespace Stokes

section Algebra

variable {α β : Type*}

/--
If every term in a finite sum is zero, then the finite sum is zero.

This is a project-local spelling of `Finset.sum_eq_zero` for cancellation
packages.
-/
theorem sum_eq_zero_of_forall_eq_zero [AddCommMonoid β]
    (s : Finset α) (f : α → β) (hzero : ∀ a, a ∈ s → f a = 0) :
    (Finset.sum s fun a => f a) = 0 :=
  Finset.sum_eq_zero hzero

/--
Cancellation by a membership-dependent involution on a finite index set.

The hypothesis `hfixed` allows fixed points exactly when their term is already
zero, matching the common "paired opposite faces plus zero leftovers" pattern.
-/
theorem sum_pair_cancel [AddCommGroup β]
    (s : Finset α) (f : α → β)
    (pair : ∀ a, a ∈ s → α)
    (hcancel : ∀ a ha, f a + f (pair a ha) = 0)
    (hfixed : ∀ a ha, f a ≠ 0 → pair a ha ≠ a)
    (hpair_mem : ∀ a ha, pair a ha ∈ s)
    (hpair_invol : ∀ a ha, pair (pair a ha) (hpair_mem a ha) = a) :
    (Finset.sum s fun a => f a) = 0 :=
  Finset.sum_involution pair hcancel hfixed hpair_mem hpair_invol

/--
Cancellation by an ordinary involution preserving a finite index set.
-/
theorem sum_pair_cancel_of_involution [AddCommGroup β]
    (s : Finset α) (f : α → β) (pair : α → α)
    (hcancel : ∀ a, a ∈ s → f a + f (pair a) = 0)
    (hfixed : ∀ a, a ∈ s → f a ≠ 0 → pair a ≠ a)
    (hpair_mem : ∀ a, a ∈ s → pair a ∈ s)
    (hpair_invol : ∀ a, a ∈ s → pair (pair a) = a) :
    (Finset.sum s fun a => f a) = 0 :=
  sum_pair_cancel s f (fun a _ => pair a)
    (fun a ha => hcancel a ha)
    (fun a ha => hfixed a ha)
    (fun a ha => hpair_mem a ha)
    (fun a ha => hpair_invol a ha)

end Algebra

section InteriorBoundary

variable {Chart InteriorPiece : Type*}

/--
The flattened finite index set of active interior pieces.

An element is a chart label together with one of the interior pieces assigned
to that chart.
-/
def artificialBoundaryIndexSet
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece) :
    Finset (Σ _ : Chart, InteriorPiece) :=
  activeCharts.sigma interiorPieces

/--
The nested chart/piece artificial-boundary sum equals the sum over the flattened
sigma index set.
-/
theorem interiorBoundary_sum_eq_indexSet_sum
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real) :
    (Finset.sum activeCharts fun x =>
        Finset.sum (interiorPieces x) fun p => interiorBoundaryTerm x p) =
      Finset.sum (artificialBoundaryIndexSet activeCharts interiorPieces) fun qp =>
        interiorBoundaryTerm qp.1 qp.2 := by
  simpa [artificialBoundaryIndexSet] using
    (Finset.sum_sigma' activeCharts interiorPieces
      (fun x p => interiorBoundaryTerm x p))

/--
Pointwise-zero artificial boundary terms cancel in the nested chart/piece sum.
-/
theorem interiorBoundary_sum_eq_zero_of_forall_eq_zero
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (hzero :
      ∀ x, x ∈ activeCharts →
        ∀ p, p ∈ interiorPieces x →
          interiorBoundaryTerm x p = 0) :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun p => interiorBoundaryTerm x p) = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro p hp
  exact hzero x hx p hp

/--
Pairwise-opposite artificial boundary terms cancel in the nested chart/piece
sum after flattening to the sigma index set.
-/
theorem interiorBoundary_sum_eq_zero_of_pair_cancel
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (pair :
      ∀ qp, qp ∈ artificialBoundaryIndexSet activeCharts interiorPieces →
        Σ _ : Chart, InteriorPiece)
    (hcancel :
      ∀ qp hqp,
        interiorBoundaryTerm qp.1 qp.2 +
          interiorBoundaryTerm (pair qp hqp).1 (pair qp hqp).2 = 0)
    (hfixed :
      ∀ qp hqp,
        interiorBoundaryTerm qp.1 qp.2 ≠ 0 → pair qp hqp ≠ qp)
    (hpair_mem :
      ∀ qp hqp, pair qp hqp ∈ artificialBoundaryIndexSet activeCharts interiorPieces)
    (hpair_invol :
      ∀ qp hqp, pair (pair qp hqp) (hpair_mem qp hqp) = qp) :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun p => interiorBoundaryTerm x p) = 0 := by
  rw [interiorBoundary_sum_eq_indexSet_sum]
  exact sum_pair_cancel (artificialBoundaryIndexSet activeCharts interiorPieces)
    (fun qp => interiorBoundaryTerm qp.1 qp.2) pair hcancel hfixed hpair_mem
    hpair_invol

/--
Data package for artificial boundary cancellation of interior chart pieces.

This records exactly the finite-sum field needed by the global assembly
packages.  Geometric modules can construct it from support separation, from
face pairings, or from a mixture of zero terms and opposite pairs.
-/
structure ArtificialBoundaryCancellationData
    (Chart InteriorPiece : Type*) where
  /-- Finite chart labels whose interior pieces contribute artificial faces. -/
  activeCharts : Finset Chart
  /-- Interior pieces assigned to each chart. -/
  interiorPieces : Chart → Finset InteriorPiece
  /-- Artificial boundary contribution of an interior piece. -/
  interiorBoundaryTerm : Chart → InteriorPiece → Real
  /-- The recorded cancellation equality. -/
  cancellation :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun p => interiorBoundaryTerm x p) = 0

namespace ArtificialBoundaryCancellationData

/-- The cancellation equality, exposed with the same shape as the global fields. -/
theorem to_interiorBoundaryCancellation
    (C : ArtificialBoundaryCancellationData Chart InteriorPiece) :
    (Finset.sum C.activeCharts fun x =>
      Finset.sum (C.interiorPieces x) fun p => C.interiorBoundaryTerm x p) = 0 :=
  C.cancellation

/-- Build a cancellation package from pointwise-zero artificial terms. -/
def of_forall_eq_zero
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (hzero :
      ∀ x, x ∈ activeCharts →
        ∀ p, p ∈ interiorPieces x →
          interiorBoundaryTerm x p = 0) :
    ArtificialBoundaryCancellationData Chart InteriorPiece where
  activeCharts := activeCharts
  interiorPieces := interiorPieces
  interiorBoundaryTerm := interiorBoundaryTerm
  cancellation :=
    interiorBoundary_sum_eq_zero_of_forall_eq_zero activeCharts interiorPieces
      interiorBoundaryTerm hzero

/-- Build a cancellation package from a finite pairing of opposite terms. -/
def of_pair_cancel
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (pair :
      ∀ qp, qp ∈ artificialBoundaryIndexSet activeCharts interiorPieces →
        Σ _ : Chart, InteriorPiece)
    (hcancel :
      ∀ qp hqp,
        interiorBoundaryTerm qp.1 qp.2 +
          interiorBoundaryTerm (pair qp hqp).1 (pair qp hqp).2 = 0)
    (hfixed :
      ∀ qp hqp,
        interiorBoundaryTerm qp.1 qp.2 ≠ 0 → pair qp hqp ≠ qp)
    (hpair_mem :
      ∀ qp hqp, pair qp hqp ∈ artificialBoundaryIndexSet activeCharts interiorPieces)
    (hpair_invol :
      ∀ qp hqp, pair (pair qp hqp) (hpair_mem qp hqp) = qp) :
    ArtificialBoundaryCancellationData Chart InteriorPiece where
  activeCharts := activeCharts
  interiorPieces := interiorPieces
  interiorBoundaryTerm := interiorBoundaryTerm
  cancellation :=
    interiorBoundary_sum_eq_zero_of_pair_cancel activeCharts interiorPieces
      interiorBoundaryTerm pair hcancel hfixed hpair_mem hpair_invol

end ArtificialBoundaryCancellationData

namespace GlobalStokesAssemblyData

variable {BoundaryPiece : Type*}

/--
Wrapper with the exact target shape of
`GlobalStokesAssemblyData.interiorBoundaryCancellation`.
-/
theorem interiorBoundaryCancellation_of_cancellationData
    (C : ArtificialBoundaryCancellationData Chart InteriorPiece) :
    (Finset.sum C.activeCharts fun x =>
      Finset.sum (C.interiorPieces x) fun p => C.interiorBoundaryTerm x p) = 0 :=
  C.to_interiorBoundaryCancellation

/--
Pointwise-zero wrapper with the exact target shape of
`GlobalStokesAssemblyData.interiorBoundaryCancellation`.
-/
theorem interiorBoundaryCancellation_of_forall_eq_zero
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (hzero :
      ∀ x, x ∈ activeCharts →
        ∀ p, p ∈ interiorPieces x →
          interiorBoundaryTerm x p = 0) :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun p => interiorBoundaryTerm x p) = 0 :=
  interiorBoundary_sum_eq_zero_of_forall_eq_zero activeCharts interiorPieces
    interiorBoundaryTerm hzero

/--
Pairing wrapper with the exact target shape of
`GlobalStokesAssemblyData.interiorBoundaryCancellation`.
-/
theorem interiorBoundaryCancellation_of_pair_cancel
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (pair :
      ∀ qp, qp ∈ artificialBoundaryIndexSet activeCharts interiorPieces →
        Σ _ : Chart, InteriorPiece)
    (hcancel :
      ∀ qp hqp,
        interiorBoundaryTerm qp.1 qp.2 +
          interiorBoundaryTerm (pair qp hqp).1 (pair qp hqp).2 = 0)
    (hfixed :
      ∀ qp hqp,
        interiorBoundaryTerm qp.1 qp.2 ≠ 0 → pair qp hqp ≠ qp)
    (hpair_mem :
      ∀ qp hqp, pair qp hqp ∈ artificialBoundaryIndexSet activeCharts interiorPieces)
    (hpair_invol :
      ∀ qp hqp, pair (pair qp hqp) (hpair_mem qp hqp) = qp) :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun p => interiorBoundaryTerm x p) = 0 :=
  interiorBoundary_sum_eq_zero_of_pair_cancel activeCharts interiorPieces
    interiorBoundaryTerm pair hcancel hfixed hpair_mem hpair_invol

end GlobalStokesAssemblyData

namespace GlobalStokesData

/--
Wrapper with the exact target shape of
`GlobalStokesData.interiorBoundaryCancellation`.
-/
theorem interiorBoundaryCancellation_of_cancellationData
    (C : ArtificialBoundaryCancellationData Chart InteriorPiece) :
    (Finset.sum C.activeCharts fun x =>
      Finset.sum (C.interiorPieces x) fun p => C.interiorBoundaryTerm x p) = 0 :=
  C.to_interiorBoundaryCancellation

/--
Pointwise-zero wrapper with the exact target shape of
`GlobalStokesData.interiorBoundaryCancellation`.
-/
theorem interiorBoundaryCancellation_of_forall_eq_zero
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (hzero :
      ∀ x, x ∈ activeCharts →
        ∀ p, p ∈ interiorPieces x →
          interiorBoundaryTerm x p = 0) :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun p => interiorBoundaryTerm x p) = 0 :=
  interiorBoundary_sum_eq_zero_of_forall_eq_zero activeCharts interiorPieces
    interiorBoundaryTerm hzero

/--
Pairing wrapper with the exact target shape of
`GlobalStokesData.interiorBoundaryCancellation`.
-/
theorem interiorBoundaryCancellation_of_pair_cancel
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (pair :
      ∀ qp, qp ∈ artificialBoundaryIndexSet activeCharts interiorPieces →
        Σ _ : Chart, InteriorPiece)
    (hcancel :
      ∀ qp hqp,
        interiorBoundaryTerm qp.1 qp.2 +
          interiorBoundaryTerm (pair qp hqp).1 (pair qp hqp).2 = 0)
    (hfixed :
      ∀ qp hqp,
        interiorBoundaryTerm qp.1 qp.2 ≠ 0 → pair qp hqp ≠ qp)
    (hpair_mem :
      ∀ qp hqp, pair qp hqp ∈ artificialBoundaryIndexSet activeCharts interiorPieces)
    (hpair_invol :
      ∀ qp hqp, pair (pair qp hqp) (hpair_mem qp hqp) = qp) :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun p => interiorBoundaryTerm x p) = 0 :=
  interiorBoundary_sum_eq_zero_of_pair_cancel activeCharts interiorPieces
    interiorBoundaryTerm pair hcancel hfixed hpair_mem hpair_invol

end GlobalStokesData

end InteriorBoundary

end Stokes

end
