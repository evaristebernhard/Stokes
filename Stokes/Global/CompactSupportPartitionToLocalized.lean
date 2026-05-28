import Stokes.Global.LocalizedInteriorConstructors

/-!
# Compact-support partitions to localized interior M8 fields

This file is a thin entry-point layer for the localized-interior part of M8.
It gives downstream compact-support constructors a natural place to hand in the
actual localized pieces, then projects the already existing
`LocalizedInteriorM8Fields` package.

There is no new analytic proof here: the genuine local Stokes equality still
comes from the supplied `LocalizedInteriorPiece` objects.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportPartitionToLocalized

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Natural selected-partition input for localized interior data.

The only substantive field is the family of localized pieces.  Each piece
already carries the local extended-box data from which project-local Stokes is
derived; this wrapper only fixes the coefficient family to be the selected
partition.
-/
structure SelectedPartitionLocalizedInteriorInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (P : SelectedBoxPartitionOfUnity I omega) where
  /-- Localized interior piece attached to every chart label. -/
  piece :
    forall i : M,
      LocalizedInteriorPiece I omega (fun j x => P.partition j x) i

namespace SelectedPartitionLocalizedInteriorInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {P : SelectedBoxPartitionOfUnity I omega}

/-- Forget the input wrapper and expose the localized interior family. -/
def toLocalizedInteriorPieces
    (D : SelectedPartitionLocalizedInteriorInput I omega P) :
    LocalizedInteriorPieces (ι := M) I omega :=
  P.toLocalizedInteriorPieces D.piece

/-- Project the selected-partition localized input to the M8-facing fields. -/
def toLocalizedInteriorM8Fields
    (D : SelectedPartitionLocalizedInteriorInput I omega P) :
    LocalizedInteriorM8Fields I omega P :=
  P.toLocalizedInteriorM8Fields D.piece

@[simp]
theorem toLocalizedInteriorM8Fields_localizedInterior
    (D : SelectedPartitionLocalizedInteriorInput I omega P) :
    D.toLocalizedInteriorM8Fields.localizedInterior =
      D.toLocalizedInteriorPieces :=
  rfl

@[simp]
theorem toLocalizedInteriorM8Fields_active
    (D : SelectedPartitionLocalizedInteriorInput I omega P) :
    D.toLocalizedInteriorM8Fields.localizedInterior.active = P.active :=
  rfl

@[simp]
theorem toLocalizedInteriorM8Fields_coefficient
    (D : SelectedPartitionLocalizedInteriorInput I omega P) :
    D.toLocalizedInteriorM8Fields.localizedInterior.coefficient =
      fun j x => P.partition j x :=
  rfl

/--
Projection of local project-Stokes in the selected active-set shape.

This theorem is intentionally only a projection: the local equality itself is
provided by each supplied `LocalizedInteriorPiece`.
-/
theorem localProjectEquality
    (D : SelectedPartitionLocalizedInteriorInput I omega P) :
    forall i, i ∈ P.active ->
      D.toLocalizedInteriorM8Fields.localizedInterior.bulkTerm i =
        D.toLocalizedInteriorM8Fields.localizedInterior.artificialBoundaryTerm i :=
  D.toLocalizedInteriorM8Fields.localProjectEquality

@[simp]
theorem toLocalizedInteriorPieces_active
    (D : SelectedPartitionLocalizedInteriorInput I omega P) :
    D.toLocalizedInteriorPieces.active = P.active :=
  rfl

@[simp]
theorem toLocalizedInteriorPieces_coefficient
    (D : SelectedPartitionLocalizedInteriorInput I omega P) :
    D.toLocalizedInteriorPieces.coefficient =
      fun j x => P.partition j x :=
  rfl

end SelectedPartitionLocalizedInteriorInput

/--
Compact-active selected boxes plus explicit localized pieces.

This is the compact-support-facing spelling of the selected-partition input:
the selected partition is the one canonically produced by
`CompactActiveExtendedBoxData.toSelectedBoxPartitionOfUnity`.
-/
structure CompactSupportPartitionLocalizedInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (D : CompactActiveExtendedBoxData I omega) where
  /-- Localized interior piece attached to every chart label. -/
  piece :
    forall i : M,
      LocalizedInteriorPiece I omega
        (fun j x => D.toSelectedBoxPartitionOfUnity.partition j x) i

namespace CompactSupportPartitionLocalizedInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {D : CompactActiveExtendedBoxData I omega}

/-- The selected partition canonically associated to the compact-active data. -/
def selectedPartition
    (_L : CompactSupportPartitionLocalizedInput I omega D) :
    SelectedBoxPartitionOfUnity I omega :=
  D.toSelectedBoxPartitionOfUnity

/-- Repackage compact-active localized pieces as selected-partition input. -/
def toSelectedPartitionInput
    (L : CompactSupportPartitionLocalizedInput I omega D) :
    SelectedPartitionLocalizedInteriorInput I omega
      D.toSelectedBoxPartitionOfUnity where
  piece := L.piece

/-- Localized pieces over the compact-active selected partition. -/
def toLocalizedInteriorPieces
    (L : CompactSupportPartitionLocalizedInput I omega D) :
    LocalizedInteriorPieces (ι := M) I omega :=
  L.toSelectedPartitionInput.toLocalizedInteriorPieces

/-- M8-facing localized interior fields over the compact-active selected partition. -/
def toLocalizedInteriorM8Fields
    (L : CompactSupportPartitionLocalizedInput I omega D) :
    LocalizedInteriorM8Fields I omega D.toSelectedBoxPartitionOfUnity :=
  L.toSelectedPartitionInput.toLocalizedInteriorM8Fields

@[simp]
theorem toSelectedPartitionInput_piece
    (L : CompactSupportPartitionLocalizedInput I omega D) :
    L.toSelectedPartitionInput.piece = L.piece :=
  rfl

@[simp]
theorem toLocalizedInteriorM8Fields_localizedInterior
    (L : CompactSupportPartitionLocalizedInput I omega D) :
    L.toLocalizedInteriorM8Fields.localizedInterior =
      L.toLocalizedInteriorPieces :=
  rfl

@[simp]
theorem toLocalizedInteriorM8Fields_active
    (L : CompactSupportPartitionLocalizedInput I omega D) :
    L.toLocalizedInteriorM8Fields.localizedInterior.active =
      D.toSelectedBoxPartitionOfUnity.active :=
  rfl

@[simp]
theorem toLocalizedInteriorM8Fields_coefficient
    (L : CompactSupportPartitionLocalizedInput I omega D) :
    L.toLocalizedInteriorM8Fields.localizedInterior.coefficient =
      fun j x => D.toSelectedBoxPartitionOfUnity.partition j x :=
  rfl

@[simp]
theorem toLocalizedInteriorM8Fields_active_finiteActive
    (L : CompactSupportPartitionLocalizedInput I omega D) :
    L.toLocalizedInteriorM8Fields.localizedInterior.active =
      D.boxData.finiteActive.active :=
  rfl

@[simp]
theorem toLocalizedInteriorM8Fields_coefficient_finiteActive
    (L : CompactSupportPartitionLocalizedInput I omega D) :
    L.toLocalizedInteriorM8Fields.localizedInterior.coefficient =
      fun j x => D.boxData.finiteActive.partition j x :=
  rfl

/--
Projection of local project-Stokes for compact-active selected boxes.

The proof is inherited from the explicit localized pieces, while compact
support only selects the active chart set and coefficient family.
-/
theorem localProjectEquality
    (L : CompactSupportPartitionLocalizedInput I omega D) :
    forall i, i ∈ D.toSelectedBoxPartitionOfUnity.active ->
      L.toLocalizedInteriorM8Fields.localizedInterior.bulkTerm i =
        L.toLocalizedInteriorM8Fields.localizedInterior.artificialBoundaryTerm i :=
  L.toLocalizedInteriorM8Fields.localProjectEquality

/-- The same local project-Stokes projection with the finite-active set exposed. -/
theorem localProjectEquality_finiteActive
    (L : CompactSupportPartitionLocalizedInput I omega D) :
    forall i, i ∈ D.boxData.finiteActive.active ->
      L.toLocalizedInteriorM8Fields.localizedInterior.bulkTerm i =
        L.toLocalizedInteriorM8Fields.localizedInterior.artificialBoundaryTerm i := by
  intro i hi
  exact L.localProjectEquality i (by simpa using hi)

end CompactSupportPartitionLocalizedInput

namespace SelectedBoxPartitionOfUnity

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/-- Natural constructor spelling for selected-partition localized M8 fields. -/
def toLocalizedInteriorInput
    (P : SelectedBoxPartitionOfUnity I omega)
    (piece :
      forall i : M,
        LocalizedInteriorPiece I omega (fun j x => P.partition j x) i) :
    SelectedPartitionLocalizedInteriorInput I omega P where
  piece := piece

@[simp]
theorem toLocalizedInteriorInput_piece
    (P : SelectedBoxPartitionOfUnity I omega)
    (piece :
      forall i : M,
        LocalizedInteriorPiece I omega (fun j x => P.partition j x) i) :
    (P.toLocalizedInteriorInput piece).piece = piece :=
  rfl

@[simp]
theorem toLocalizedInteriorInput_toLocalizedInteriorM8Fields
    (P : SelectedBoxPartitionOfUnity I omega)
    (piece :
      forall i : M,
        LocalizedInteriorPiece I omega (fun j x => P.partition j x) i) :
    (P.toLocalizedInteriorInput piece).toLocalizedInteriorM8Fields =
      P.toLocalizedInteriorM8Fields piece :=
  rfl

end SelectedBoxPartitionOfUnity

namespace CompactActiveExtendedBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/-- Natural constructor spelling from compact-active boxes to localized input. -/
def toCompactSupportPartitionLocalizedInput
    (D : CompactActiveExtendedBoxData I omega)
    (piece :
      forall i : M,
        LocalizedInteriorPiece I omega
          (fun j x => D.toSelectedBoxPartitionOfUnity.partition j x) i) :
    CompactSupportPartitionLocalizedInput I omega D where
  piece := piece

@[simp]
theorem toCompactSupportPartitionLocalizedInput_piece
    (D : CompactActiveExtendedBoxData I omega)
    (piece :
      forall i : M,
        LocalizedInteriorPiece I omega
          (fun j x => D.toSelectedBoxPartitionOfUnity.partition j x) i) :
    (D.toCompactSupportPartitionLocalizedInput piece).piece = piece :=
  rfl

@[simp]
theorem toCompactSupportPartitionLocalizedInput_toLocalizedInteriorM8Fields
    (D : CompactActiveExtendedBoxData I omega)
    (piece :
      forall i : M,
        LocalizedInteriorPiece I omega
          (fun j x => D.toSelectedBoxPartitionOfUnity.partition j x) i) :
    (D.toCompactSupportPartitionLocalizedInput piece).toLocalizedInteriorM8Fields =
      D.toSelectedBoxPartitionOfUnity.toLocalizedInteriorM8Fields piece :=
  rfl

end CompactActiveExtendedBoxData

end CompactSupportPartitionToLocalized

end Stokes

end
