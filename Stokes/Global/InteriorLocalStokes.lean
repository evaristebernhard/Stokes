import Stokes.Global.InteriorChart
import Stokes.Box

/-!
# Interior chart local Stokes skeleton

This module supplies project-local wrappers for interior chart boxes.  The
boundary-side term here is the full auxiliary coordinate-box boundary term; it
is an artificial boundary contribution that later global assembly layers should
cancel across interior pieces, not a genuine manifold-boundary integral.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section InteriorLocalStokes

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Project-local bulk integral over an interior chart coordinate box.

This is the integral of `dω` for the transition-pulled chart representative over
the selected auxiliary box.
-/
def projectInteriorBulkIntegral {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Real :=
  ∫ x in Icc a b,
    extDeriv (ManifoldForm.transitionPullbackInChart I x0 x1 ω) x
      (standardTopFrame n)

/--
Project-local artificial boundary integral for an interior chart coordinate
box.

This is the full Euclidean box boundary term.  Since an interior chart piece is
not meant to contribute to the true manifold boundary, this term is deliberately
kept as an artificial boundary contribution for later cancellation.
-/
def projectInteriorBoundaryIntegral {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Real :=
  bdryIntegral
    (CubeStokes.toCoordNForm (ManifoldForm.transitionPullbackInChart I x0 x1 ω))
    a b

/-- Unfold the interior artificial-boundary wrapper to the box boundary term. -/
theorem projectInteriorBoundaryIntegral_eq_bdryIntegral {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) :
    projectInteriorBoundaryIntegral I x0 x1 ω a b =
      bdryIntegral
        (CubeStokes.toCoordNForm
          (ManifoldForm.transitionPullbackInChart I x0 x1 ω)) a b := by
  rfl

/--
Interior-chart local Stokes for one extended box.

The analytic input is exactly the ambient smooth extension recorded by
`interiorChartExtendedBox`; the right-hand side is the artificial coordinate-box
boundary term.
-/
theorem projectInteriorLocalStokes_of_extendedBox {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hbox : interiorChartExtendedBox I x0 x1 ω a b) :
    projectInteriorBulkIntegral I x0 x1 ω a b =
      projectInteriorBoundaryIntegral I x0 x1 ω a b := by
  rcases hbox.exists_smooth_nhds with ⟨U, hU, hUbox, hωU⟩
  simpa [projectInteriorBulkIntegral, projectInteriorBoundaryIntegral, bdryIntegral,
    halfSpaceLocalBulkIntegral] using
    box_stokes_extDeriv_contDiffOn_isOpen
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω)
      a b hbox.selectedBox.le hU hUbox hωU

/--
Data package for one interior local Stokes piece.

The `bulkTerm` and `artificialBoundaryTerm` fields allow later assembly code to
carry named real-valued terms while recording that they are the project-local
wrappers for the selected extended box.
-/
structure InteriorLocalStokesData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n) where
  /-- Source chart for the transition-pulled representative. -/
  sourceChart : M
  /-- Comparison chart for the transition-pulled representative. -/
  targetChart : M
  /-- Lower corner of the selected coordinate box. -/
  lowerCorner : Fin (n + 1) → Real
  /-- Upper corner of the selected coordinate box. -/
  upperCorner : Fin (n + 1) → Real
  /-- Selected interior chart box with an ambient smooth extension. -/
  extendedBox :
    interiorChartExtendedBox I sourceChart targetChart ω lowerCorner upperCorner
  /-- Recorded bulk term for this local piece. -/
  bulkTerm : Real
  /-- Recorded artificial coordinate-box boundary term for this local piece. -/
  artificialBoundaryTerm : Real
  /-- The recorded bulk term is the project-local wrapper. -/
  bulkTerm_eq_project :
    bulkTerm =
      projectInteriorBulkIntegral I sourceChart targetChart ω lowerCorner upperCorner
  /-- The recorded artificial boundary term is the project-local wrapper. -/
  artificialBoundaryTerm_eq_project :
    artificialBoundaryTerm =
      projectInteriorBoundaryIntegral I sourceChart targetChart ω lowerCorner upperCorner
  /-- The recorded local Stokes equality. -/
  localEquality : bulkTerm = artificialBoundaryTerm

namespace InteriorLocalStokesData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/-- The selected-box projection of an interior local Stokes data package. -/
theorem selectedBox (D : InteriorLocalStokesData I ω) :
    interiorChartSelectedBox I D.sourceChart D.targetChart ω
      D.lowerCorner D.upperCorner :=
  D.extendedBox.selectedBox

/-- Constructor using the proved local box Stokes theorem. -/
def ofExtendedBox
    (x0 x1 : M) (a b : Fin (n + 1) → Real)
    (hbox : interiorChartExtendedBox I x0 x1 ω a b) :
    InteriorLocalStokesData I ω where
  sourceChart := x0
  targetChart := x1
  lowerCorner := a
  upperCorner := b
  extendedBox := hbox
  bulkTerm := projectInteriorBulkIntegral I x0 x1 ω a b
  artificialBoundaryTerm := projectInteriorBoundaryIntegral I x0 x1 ω a b
  bulkTerm_eq_project := rfl
  artificialBoundaryTerm_eq_project := rfl
  localEquality := projectInteriorLocalStokes_of_extendedBox I x0 x1 ω a b hbox

/-- The project-local wrappers satisfy local Stokes for the recorded box. -/
theorem projectLocalEquality (D : InteriorLocalStokesData I ω) :
    projectInteriorBulkIntegral I D.sourceChart D.targetChart ω
        D.lowerCorner D.upperCorner =
      projectInteriorBoundaryIntegral I D.sourceChart D.targetChart ω
        D.lowerCorner D.upperCorner :=
  projectInteriorLocalStokes_of_extendedBox I D.sourceChart D.targetChart ω
    D.lowerCorner D.upperCorner D.extendedBox

/-- Recover the recorded local equality. -/
theorem bulkTerm_eq_artificialBoundaryTerm (D : InteriorLocalStokesData I ω) :
    D.bulkTerm = D.artificialBoundaryTerm :=
  D.localEquality

end InteriorLocalStokesData

/--
Purely algebraic finite-sum wrapper: local equality on every active interior
piece implies equality of the corresponding active sums.
-/
theorem sum_projectInterior_eq_of_forall_local {ι R : Type*} [AddCommMonoid R]
    (active : Finset ι) (bulk boundary : ι → R)
    (hlocal : ∀ i ∈ active, bulk i = boundary i) :
    Finset.sum active bulk = Finset.sum active boundary := by
  exact Finset.sum_congr rfl hlocal

/--
Finite-sum interior local Stokes over active interior-chart boxes with a fixed
form and chart-pair assignment.
-/
theorem sum_projectInteriorLocalStokes_of_forall_interiorChartExtendedBox
    {ι : Type*} {n : Nat} (active : Finset ι)
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : ι → M) (ω : ManifoldForm I M n)
    (a b : ι → Fin (n + 1) → Real)
    (hbox :
      ∀ i ∈ active, interiorChartExtendedBox I (x0 i) (x1 i) ω (a i) (b i)) :
    (∑ i ∈ active, projectInteriorBulkIntegral I (x0 i) (x1 i) ω (a i) (b i)) =
      ∑ i ∈ active,
        projectInteriorBoundaryIntegral I (x0 i) (x1 i) ω (a i) (b i) := by
  exact Finset.sum_congr rfl fun i hi =>
    projectInteriorLocalStokes_of_extendedBox
      I (x0 i) (x1 i) ω (a i) (b i) (hbox i hi)

/-- Finite-sum equality for recorded interior local Stokes data packages. -/
theorem sum_interiorLocalStokesData
    {ι : Type*} {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    (active : Finset ι) (D : ι → InteriorLocalStokesData I ω) :
    (∑ i ∈ active, (D i).bulkTerm) =
      ∑ i ∈ active, (D i).artificialBoundaryTerm := by
  exact Finset.sum_congr rfl fun i _ => (D i).localEquality

end InteriorLocalStokes

end Stokes

end
