import Stokes.Global.LocalizedInteriorPieces
import Stokes.Global.CompactActiveBoxes

/-!
# Constructors for localized interior pieces

This file isolates the small constructor/projection layer that turns a selected
partition into the localized interior package consumed by the M8/global
bookkeeping.  The analytic localized pieces are still supplied explicitly; this
module only records the stable field equalities needed downstream.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section LocalizedInteriorConstructors

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
The M8-facing interior alignment fields for a selected partition.

This record deliberately keeps the analytic construction of each localized
piece as an input.  Its job is only to expose the active set, coefficient family,
and local project-Stokes equality in the exact selected-partition shape.
-/
structure LocalizedInteriorM8Fields {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (P : SelectedBoxPartitionOfUnity I ω) where
  /-- Localized partition-of-unity interior pieces. -/
  localizedInterior : LocalizedInteriorPieces (ι := M) I ω
  /-- The localized active set is the selected partition active set. -/
  localized_active : localizedInterior.active = P.active
  /-- The localized coefficients are the selected partition coefficients. -/
  localized_coefficient :
    localizedInterior.coefficient = fun i x => P.partition i x

namespace LocalizedInteriorM8Fields

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {P : SelectedBoxPartitionOfUnity I ω}

@[simp]
theorem active_eq (D : LocalizedInteriorM8Fields I ω P) :
    D.localizedInterior.active = P.active :=
  D.localized_active

@[simp]
theorem coefficient_eq (D : LocalizedInteriorM8Fields I ω P) :
    D.localizedInterior.coefficient = fun i x => P.partition i x :=
  D.localized_coefficient

/-- Pointwise coefficient projection in the selected-partition shape. -/
theorem coefficient_apply (D : LocalizedInteriorM8Fields I ω P) (i : M) :
    D.localizedInterior.coefficient i = fun x => P.partition i x :=
  congrFun D.localized_coefficient i

/-- Membership in the selected active set as membership in the localized family. -/
theorem mem_localized_active
    (D : LocalizedInteriorM8Fields I ω P) {i : M} (hi : i ∈ P.active) :
    i ∈ D.localizedInterior.active := by
  simpa [D.localized_active] using hi

/--
Local project-Stokes equality indexed by the selected partition active set.

This is the projection M8 needs before expanding the singleton local-piece
fiber.
-/
theorem localProjectEquality
    (D : LocalizedInteriorM8Fields I ω P) :
    ∀ i, i ∈ P.active →
      D.localizedInterior.bulkTerm i =
        D.localizedInterior.artificialBoundaryTerm i := by
  intro i hi
  exact D.localizedInterior.localProjectEquality i (D.mem_localized_active hi)

/-- Singleton interior-piece family used by M8/global mixed constructors. -/
def interiorPieces (_D : LocalizedInteriorM8Fields I ω P) : M → Finset Unit :=
  fun _ => {()}

/-- Localized bulk term in singleton-piece form. -/
def interiorBulkTerm (D : LocalizedInteriorM8Fields I ω P) : M → Unit → Real :=
  fun i _ => D.localizedInterior.bulkTerm i

/-- Localized artificial-boundary term in singleton-piece form. -/
def interiorBoundaryTerm (D : LocalizedInteriorM8Fields I ω P) : M → Unit → Real :=
  fun i _ => D.localizedInterior.artificialBoundaryTerm i

@[simp]
theorem interiorPieces_eq
    (D : LocalizedInteriorM8Fields I ω P) (i : M) :
    D.interiorPieces i = ({()} : Finset Unit) :=
  rfl

@[simp]
theorem interiorBulkTerm_unit
    (D : LocalizedInteriorM8Fields I ω P) (i : M) (q : Unit) :
    D.interiorBulkTerm i q = D.localizedInterior.bulkTerm i := by
  cases q
  rfl

@[simp]
theorem interiorBoundaryTerm_unit
    (D : LocalizedInteriorM8Fields I ω P) (i : M) (q : Unit) :
    D.interiorBoundaryTerm i q =
      D.localizedInterior.artificialBoundaryTerm i := by
  cases q
  rfl

end LocalizedInteriorM8Fields

namespace SelectedBoxPartitionOfUnity

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/--
Build localized interior pieces indexed by a selected partition, once the
analytic localized piece for each coefficient has been supplied.
-/
def toLocalizedInteriorPieces
    (P : SelectedBoxPartitionOfUnity I ω)
    (piece :
      ∀ i : M,
        LocalizedInteriorPiece I ω (fun j x => P.partition j x) i) :
    LocalizedInteriorPieces (ι := M) I ω where
  active := P.active
  coefficient := fun j x => P.partition j x
  piece := piece

@[simp]
theorem toLocalizedInteriorPieces_active
    (P : SelectedBoxPartitionOfUnity I ω)
    (piece :
      ∀ i : M,
        LocalizedInteriorPiece I ω (fun j x => P.partition j x) i) :
    (P.toLocalizedInteriorPieces piece).active = P.active :=
  rfl

@[simp]
theorem toLocalizedInteriorPieces_coefficient
    (P : SelectedBoxPartitionOfUnity I ω)
    (piece :
      ∀ i : M,
        LocalizedInteriorPiece I ω (fun j x => P.partition j x) i) :
    (P.toLocalizedInteriorPieces piece).coefficient =
      fun j x => P.partition j x :=
  rfl

/--
Selected-partition constructor for the M8-facing localized interior fields.
-/
def toLocalizedInteriorM8Fields
    (P : SelectedBoxPartitionOfUnity I ω)
    (piece :
      ∀ i : M,
        LocalizedInteriorPiece I ω (fun j x => P.partition j x) i) :
    LocalizedInteriorM8Fields I ω P where
  localizedInterior := P.toLocalizedInteriorPieces piece
  localized_active := rfl
  localized_coefficient := rfl

@[simp]
theorem toLocalizedInteriorM8Fields_localizedInterior
    (P : SelectedBoxPartitionOfUnity I ω)
    (piece :
      ∀ i : M,
        LocalizedInteriorPiece I ω (fun j x => P.partition j x) i) :
    (P.toLocalizedInteriorM8Fields piece).localizedInterior =
      P.toLocalizedInteriorPieces piece :=
  rfl

@[simp]
theorem toLocalizedInteriorM8Fields_active
    (P : SelectedBoxPartitionOfUnity I ω)
    (piece :
      ∀ i : M,
        LocalizedInteriorPiece I ω (fun j x => P.partition j x) i) :
    (P.toLocalizedInteriorM8Fields piece).localizedInterior.active =
      P.active :=
  rfl

@[simp]
theorem toLocalizedInteriorM8Fields_coefficient
    (P : SelectedBoxPartitionOfUnity I ω)
    (piece :
      ∀ i : M,
        LocalizedInteriorPiece I ω (fun j x => P.partition j x) i) :
    (P.toLocalizedInteriorM8Fields piece).localizedInterior.coefficient =
      fun j x => P.partition j x :=
  rfl

theorem toLocalizedInteriorM8Fields_localProjectEquality
    (P : SelectedBoxPartitionOfUnity I ω)
    (piece :
      ∀ i : M,
        LocalizedInteriorPiece I ω (fun j x => P.partition j x) i) :
    ∀ i, i ∈ P.active →
      (P.toLocalizedInteriorM8Fields piece).localizedInterior.bulkTerm i =
        (P.toLocalizedInteriorM8Fields piece).localizedInterior.artificialBoundaryTerm i :=
  (P.toLocalizedInteriorM8Fields piece).localProjectEquality

end SelectedBoxPartitionOfUnity

namespace LocalizedInteriorM8Fields

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {P : SelectedBoxPartitionOfUnity I ω}

/--
Constructor from an already built localized family and the two selected
partition alignment equalities.
-/
def ofLocalizedInteriorPieces
    (localizedInterior : LocalizedInteriorPieces (ι := M) I ω)
    (localized_active : localizedInterior.active = P.active)
    (localized_coefficient :
      localizedInterior.coefficient = fun i x => P.partition i x) :
    LocalizedInteriorM8Fields I ω P where
  localizedInterior := localizedInterior
  localized_active := localized_active
  localized_coefficient := localized_coefficient

@[simp]
theorem ofLocalizedInteriorPieces_localizedInterior
    (localizedInterior : LocalizedInteriorPieces (ι := M) I ω)
    (localized_active : localizedInterior.active = P.active)
    (localized_coefficient :
      localizedInterior.coefficient = fun i x => P.partition i x) :
    (ofLocalizedInteriorPieces (P := P) localizedInterior
      localized_active localized_coefficient).localizedInterior =
      localizedInterior :=
  rfl

end LocalizedInteriorM8Fields

namespace CompactActiveExtendedBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/--
Compact-active selected-box data as M8-facing localized interior fields.

The localized analytic pieces remain explicit; the selected partition is the
one already produced by `toSelectedBoxPartitionOfUnity`.
-/
def toLocalizedInteriorM8Fields
    (D : CompactActiveExtendedBoxData I ω)
    (piece :
      ∀ i : M,
        LocalizedInteriorPiece I ω
          (fun j x => D.boxData.finiteActive.partition j x) i) :
    LocalizedInteriorM8Fields I ω D.toSelectedBoxPartitionOfUnity where
  localizedInterior :=
    { active := D.boxData.finiteActive.active
      coefficient := fun j x => D.boxData.finiteActive.partition j x
      piece := piece }
  localized_active := rfl
  localized_coefficient := rfl

@[simp]
theorem toLocalizedInteriorM8Fields_active
    (D : CompactActiveExtendedBoxData I ω)
    (piece :
      ∀ i : M,
        LocalizedInteriorPiece I ω
          (fun j x => D.boxData.finiteActive.partition j x) i) :
    (D.toLocalizedInteriorM8Fields piece).localizedInterior.active =
      D.toSelectedBoxPartitionOfUnity.active :=
  rfl

@[simp]
theorem toLocalizedInteriorM8Fields_coefficient
    (D : CompactActiveExtendedBoxData I ω)
    (piece :
      ∀ i : M,
        LocalizedInteriorPiece I ω
          (fun j x => D.boxData.finiteActive.partition j x) i) :
    (D.toLocalizedInteriorM8Fields piece).localizedInterior.coefficient =
      fun j x => D.toSelectedBoxPartitionOfUnity.partition j x :=
  rfl

end CompactActiveExtendedBoxData

end LocalizedInteriorConstructors

end Stokes

end
