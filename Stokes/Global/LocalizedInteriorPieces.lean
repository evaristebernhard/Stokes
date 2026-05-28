import Stokes.Global.LocalizedSupport
import Stokes.Global.InteriorLocalStokes

/-!
# Localized interior Stokes pieces

This file packages one partition-of-unity localized interior chart piece, then
adds a finite-sum wrapper over active indices.  The analytic inputs stay
explicit: coefficient support control comes from `LocalizedSupportControl`, and
smoothness is the ambient neighborhood field required by
`interiorChartExtendedBox`.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section LocalizedInteriorPieces

universe u w c

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type c}

/--
One active partition-of-unity interior piece.

The type is parameterized by the active index `i`.  The coefficient of this
piece is therefore definitionally `ρ i`, and the localized form is the canonical
pointwise form `ManifoldForm.localizedForm I (ρ i) ω`.
-/
structure LocalizedInteriorPiece {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n) (ρ : ι → M → Real) (i : ι) where
  /-- Source chart for the transition-pulled representative. -/
  sourceChart : M
  /-- Comparison chart for the transition-pulled representative. -/
  targetChart : M
  /-- Lower corner of the selected coordinate box. -/
  lowerCorner : Fin (n + 1) → Real
  /-- Upper corner of the selected coordinate box. -/
  upperCorner : Fin (n + 1) → Real
  /-- Coefficient support control for the localized form `ρ i • ω`. -/
  supportControl :
    LocalizedSupportControl I sourceChart targetChart (ρ i) ω lowerCorner upperCorner
  /-- Ambient smooth extension of the localized chart representative near the box. -/
  smoothNeighborhood :
    ∃ U : Set (Fin (n + 1) → Real),
      IsOpen U ∧ Set.Icc lowerCorner upperCorner ⊆ U ∧
        ContDiffOn Real ⊤
          (ManifoldForm.transitionPullbackInChart I sourceChart targetChart
            (ManifoldForm.localizedForm I (ρ i) ω)) U

namespace LocalizedInteriorPiece

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n} {ρ : ι → M → Real} {i : ι}

/-- The coefficient attached to this active index. -/
def coefficient (_D : LocalizedInteriorPiece I ω ρ i) : M → Real :=
  ρ i

/-- The canonical localized form attached to this active index. -/
def localizedForm (_D : LocalizedInteriorPiece I ω ρ i) : ManifoldForm I M n :=
  ManifoldForm.localizedForm I (ρ i) ω

@[simp]
theorem coefficient_eq (_D : LocalizedInteriorPiece I ω ρ i) :
    _D.coefficient = ρ i :=
  rfl

@[simp]
theorem localizedForm_eq (_D : LocalizedInteriorPiece I ω ρ i) :
    _D.localizedForm = ManifoldForm.localizedForm I (ρ i) ω :=
  rfl

/-- The support-control field as `LocalizedFormData`. -/
def localizedFormData (D : LocalizedInteriorPiece I ω ρ i) :
    LocalizedFormData I D.sourceChart D.targetChart ω D.lowerCorner D.upperCorner :=
  D.supportControl.toLocalizedFormData

/-- The selected-box part for the localized form. -/
theorem selectedBox (D : LocalizedInteriorPiece I ω ρ i) :
    interiorChartSelectedBox I D.sourceChart D.targetChart D.localizedForm
      D.lowerCorner D.upperCorner :=
  D.supportControl.interiorChartSelectedBox

/--
Construct the localized extended box from support control and the recorded
ambient smoothness neighborhood.
-/
def extendedBox (D : LocalizedInteriorPiece I ω ρ i) :
    interiorChartExtendedBox I D.sourceChart D.targetChart D.localizedForm
      D.lowerCorner D.upperCorner := by
  rcases D.smoothNeighborhood with ⟨U, hU, hUbox, hωU⟩
  exact interiorChartExtendedBox.mk D.selectedBox hU hUbox hωU

/-- The localized form's `InteriorLocalStokesData` package. -/
def localStokesData (D : LocalizedInteriorPiece I ω ρ i) :
    InteriorLocalStokesData I D.localizedForm :=
  InteriorLocalStokesData.ofExtendedBox D.sourceChart D.targetChart
    D.lowerCorner D.upperCorner D.extendedBox

/-- Project-local Stokes for the localized interior piece. -/
theorem projectLocalEquality (D : LocalizedInteriorPiece I ω ρ i) :
    projectInteriorBulkIntegral I D.sourceChart D.targetChart D.localizedForm
        D.lowerCorner D.upperCorner =
      projectInteriorBoundaryIntegral I D.sourceChart D.targetChart D.localizedForm
        D.lowerCorner D.upperCorner :=
  projectInteriorLocalStokes_of_extendedBox I D.sourceChart D.targetChart
    D.localizedForm D.lowerCorner D.upperCorner D.extendedBox

/-- Recorded local Stokes equality inside the derived data package. -/
theorem data_bulk_eq_boundary (D : LocalizedInteriorPiece I ω ρ i) :
    D.localStokesData.bulkTerm = D.localStokesData.artificialBoundaryTerm :=
  D.localStokesData.localEquality

end LocalizedInteriorPiece

/--
Build the localized extended box directly from coefficient support control and
one smooth-neighborhood witness.
-/
def interiorChartExtendedBox_of_localizedSupportControl {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n} {ρ : M → Real}
    {x0 x1 : M} {a b : Fin (n + 1) → Real}
    (C : LocalizedSupportControl I x0 x1 ρ ω a b)
    {U : Set (Fin (n + 1) → Real)}
    (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U)
    (hωU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) U) :
    interiorChartExtendedBox I x0 x1 (ManifoldForm.localizedForm I ρ ω) a b :=
  interiorChartExtendedBox.mk C.interiorChartSelectedBox hU hUbox hωU

/--
Build the localized `InteriorLocalStokesData` directly from coefficient support
control and one smooth-neighborhood witness.
-/
def interiorLocalStokesData_of_localizedSupportControl {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n} {ρ : M → Real}
    {x0 x1 : M} {a b : Fin (n + 1) → Real}
    (C : LocalizedSupportControl I x0 x1 ρ ω a b)
    {U : Set (Fin (n + 1) → Real)}
    (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U)
    (hωU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) U) :
    InteriorLocalStokesData I (ManifoldForm.localizedForm I ρ ω) :=
  InteriorLocalStokesData.ofExtendedBox x0 x1 a b
    (interiorChartExtendedBox_of_localizedSupportControl C hU hUbox hωU)

/--
Finite active family of localized interior pieces.

The active index set and coefficient family are recorded together, so the
`i`-th package always uses the coefficient `coefficient i`.
-/
structure LocalizedInteriorPieces {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n) where
  /-- Finite set of active partition-of-unity indices. -/
  active : Finset ι
  /-- Partition-of-unity coefficient family. -/
  coefficient : ι → M → Real
  /-- Localized interior data assigned to each index. -/
  piece : ∀ i : ι, LocalizedInteriorPiece I ω coefficient i

namespace LocalizedInteriorPieces

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/-- Bulk term of the localized interior piece indexed by `i`. -/
def bulkTerm (D : LocalizedInteriorPieces (ι := ι) I ω) (i : ι) : Real :=
  let P := D.piece i
  projectInteriorBulkIntegral I P.sourceChart P.targetChart P.localizedForm
    P.lowerCorner P.upperCorner

/-- Artificial boundary term of the localized interior piece indexed by `i`. -/
def artificialBoundaryTerm (D : LocalizedInteriorPieces (ι := ι) I ω) (i : ι) : Real :=
  let P := D.piece i
  projectInteriorBoundaryIntegral I P.sourceChart P.targetChart P.localizedForm
    P.lowerCorner P.upperCorner

/-- The localized `InteriorLocalStokesData` package for index `i`. -/
def localStokesData (D : LocalizedInteriorPieces (ι := ι) I ω) (i : ι) :
    InteriorLocalStokesData I (D.piece i).localizedForm :=
  (D.piece i).localStokesData

/-- Local Stokes for every active localized interior piece. -/
theorem localProjectEquality (D : LocalizedInteriorPieces (ι := ι) I ω) :
    ∀ i, i ∈ D.active → bulkTerm D i = artificialBoundaryTerm D i := by
  intro i _hi
  exact (D.piece i).projectLocalEquality

/--
Finite-sum wrapper: active localized interior pieces satisfy the summed local
Stokes equality.
-/
theorem sum_projectInterior_eq_artificialBoundary
    (D : LocalizedInteriorPieces (ι := ι) I ω) :
    (∑ i ∈ D.active, bulkTerm D i) =
      ∑ i ∈ D.active, artificialBoundaryTerm D i := by
  exact sum_projectInterior_eq_of_forall_local D.active (bulkTerm D)
    (artificialBoundaryTerm D) D.localProjectEquality

/-- The same finite-sum wrapper written directly in terms of each derived data package. -/
theorem sum_localStokesData_terms
    (D : LocalizedInteriorPieces (ι := ι) I ω) :
    (∑ i ∈ D.active, (D.localStokesData i).bulkTerm) =
      ∑ i ∈ D.active, (D.localStokesData i).artificialBoundaryTerm := by
  exact Finset.sum_congr rfl fun i _hi => (D.localStokesData i).localEquality

end LocalizedInteriorPieces

end LocalizedInteriorPieces

end Stokes

end
