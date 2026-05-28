import Stokes.Global.LocalizedInteriorPieces
import Stokes.Global.MixedGlobalConstructor

/-!
# Localized interior piece families for the mixed constructor

This file adapts `LocalizedInteriorPieces` to the interior package expected by
the mixed global constructor.  A localized piece carries the form
`ManifoldForm.localizedForm I (ρ i) ω`, so it does not fit the fixed-form
`InteriorLocalStokesData I ω` package.  The mixed constructor only needs the
recorded real-valued local terms and their equality, so the adapter uses the
localized active index as the chart label and a singleton `Unit` local-piece
fiber.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section InteriorPieceFamilyConstructor

universe u w c

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type c}

/--
Input for viewing a localized interior family as a mixed-constructor interior
family.

The adapter is intentionally minimal: each active localized index becomes one
mixed chart label, and the local-piece fiber over that label is the singleton
type `Unit`.
-/
structure LocalizedInteriorMixedInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n) where
  /-- The finite localized interior family to expose to the mixed constructor. -/
  pieces : LocalizedInteriorPieces (ι := ι) I ω

namespace LocalizedInteriorMixedInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/-- Mixed chart labels are the active localized indices. -/
def activeCharts (D : LocalizedInteriorMixedInput (ι := ι) I ω) : Finset ι :=
  D.pieces.active

/-- Each localized index contributes exactly one mixed local piece. -/
def interiorPieces (_D : LocalizedInteriorMixedInput (ι := ι) I ω) :
    ι → Finset Unit :=
  fun _ => {()}

/-- Mixed bulk term induced by the localized project-local bulk term. -/
def interiorBulkTerm (D : LocalizedInteriorMixedInput (ι := ι) I ω) :
    ι → Unit → Real :=
  fun i _ => D.pieces.bulkTerm i

/-- Mixed artificial-boundary term induced by the localized project-local term. -/
def interiorBoundaryTerm (D : LocalizedInteriorMixedInput (ι := ι) I ω) :
    ι → Unit → Real :=
  fun i _ => D.pieces.artificialBoundaryTerm i

@[simp]
theorem activeCharts_eq (D : LocalizedInteriorMixedInput (ι := ι) I ω) :
    D.activeCharts = D.pieces.active :=
  rfl

@[simp]
theorem interiorPieces_eq
    (D : LocalizedInteriorMixedInput (ι := ι) I ω) (i : ι) :
    D.interiorPieces i = {()} :=
  rfl

@[simp]
theorem interiorBulkTerm_unit
    (D : LocalizedInteriorMixedInput (ι := ι) I ω) (i : ι) (q : Unit) :
    D.interiorBulkTerm i q = D.pieces.bulkTerm i := by
  cases q
  rfl

@[simp]
theorem interiorBoundaryTerm_unit
    (D : LocalizedInteriorMixedInput (ι := ι) I ω) (i : ι) (q : Unit) :
    D.interiorBoundaryTerm i q = D.pieces.artificialBoundaryTerm i := by
  cases q
  rfl

/--
The localized interior family as the `MixedInteriorPackage` required by the
mixed global constructor.
-/
def toMixedInteriorPackage
    (D : LocalizedInteriorMixedInput (ι := ι) I ω) :
    MixedInteriorPackage I ω ι Unit
      D.activeCharts D.interiorPieces
      D.interiorBulkTerm D.interiorBoundaryTerm where
  localStokes := by
    intro i hi q _hq
    cases q
    exact D.pieces.localProjectEquality i (by simpa using hi)

/--
The local finite-sum equality supplied by the localized interior mixed package.
-/
theorem localFiniteSum
    (D : LocalizedInteriorMixedInput (ι := ι) I ω) :
    (Finset.sum D.activeCharts fun i =>
        Finset.sum (D.interiorPieces i) fun q => D.interiorBulkTerm i q) =
      Finset.sum D.activeCharts fun i =>
        Finset.sum (D.interiorPieces i) fun q => D.interiorBoundaryTerm i q := by
  exact GlobalStokesData.sum_localPieces D.activeCharts D.interiorPieces
    D.interiorBulkTerm D.interiorBoundaryTerm
    D.toMixedInteriorPackage.localStokes

/--
The mixed singleton-fiber finite sum is the original localized finite sum.
-/
theorem localFiniteSum_eq_localized
    (D : LocalizedInteriorMixedInput (ι := ι) I ω) :
    (Finset.sum D.activeCharts fun i =>
        Finset.sum (D.interiorPieces i) fun q => D.interiorBulkTerm i q) =
      Finset.sum D.pieces.active fun i => D.pieces.bulkTerm i := by
  simp [activeCharts, interiorPieces, interiorBulkTerm]

/--
The mixed singleton-fiber artificial-boundary sum is the original localized
artificial-boundary finite sum.
-/
theorem localBoundaryFiniteSum_eq_localized
    (D : LocalizedInteriorMixedInput (ι := ι) I ω) :
    (Finset.sum D.activeCharts fun i =>
        Finset.sum (D.interiorPieces i) fun q => D.interiorBoundaryTerm i q) =
      Finset.sum D.pieces.active fun i => D.pieces.artificialBoundaryTerm i := by
  simp [activeCharts, interiorPieces, interiorBoundaryTerm]

end LocalizedInteriorMixedInput

namespace LocalizedInteriorPieces

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/-- Minimal mixed-constructor input associated to a localized interior family. -/
def toMixedInput (D : LocalizedInteriorPieces (ι := ι) I ω) :
    LocalizedInteriorMixedInput (ι := ι) I ω where
  pieces := D

/--
View localized interior pieces as the interior package expected by
`MixedGlobalStokesData`.
-/
def toMixedInteriorPackage (D : LocalizedInteriorPieces (ι := ι) I ω) :
    MixedInteriorPackage I ω ι Unit
      D.toMixedInput.activeCharts D.toMixedInput.interiorPieces
      D.toMixedInput.interiorBulkTerm D.toMixedInput.interiorBoundaryTerm :=
  D.toMixedInput.toMixedInteriorPackage

/--
Localized interior local Stokes, in the chart-indexed finite-sum shape used by
the mixed constructor.
-/
theorem mixedLocalFiniteSum (D : LocalizedInteriorPieces (ι := ι) I ω) :
    (Finset.sum D.toMixedInput.activeCharts fun i =>
        Finset.sum (D.toMixedInput.interiorPieces i) fun q =>
          D.toMixedInput.interiorBulkTerm i q) =
      Finset.sum D.toMixedInput.activeCharts fun i =>
        Finset.sum (D.toMixedInput.interiorPieces i) fun q =>
          D.toMixedInput.interiorBoundaryTerm i q :=
  D.toMixedInput.localFiniteSum

end LocalizedInteriorPieces

end InteriorPieceFamilyConstructor

end Stokes

end
