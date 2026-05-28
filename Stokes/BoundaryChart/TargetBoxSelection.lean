import Stokes.BoundaryChart.TransitionCompactBox

/-!
# Boundary target box selection

This file is a thin selection layer for target boundary boxes.  It keeps the
analytic inputs explicit, but packages the common result: compact image control
plus local inverse data gives the `boundaryChartSelectedBoxImageData` needed by
boundary chart-change wrappers.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- Tangential lower corner induced by an ambient lower-zero-face box corner. -/
def boundaryFaceLowerCorner {n : Nat} (c : Fin (n + 1) → Real) : Fin n → Real :=
  fun i => c i.succ

/-- Tangential upper corner induced by an ambient lower-zero-face box corner. -/
def boundaryFaceUpperCorner {n : Nat} (d : Fin (n + 1) → Real) : Fin n → Real :=
  fun i => d i.succ

@[simp]
theorem boundaryFaceLowerCorner_apply {n : Nat} (c : Fin (n + 1) → Real)
    (i : Fin n) :
    boundaryFaceLowerCorner c i = c i.succ :=
  rfl

@[simp]
theorem boundaryFaceUpperCorner_apply {n : Nat} (d : Fin (n + 1) → Real)
    (i : Fin n) :
    boundaryFaceUpperCorner d i = d i.succ :=
  rfl

/-- A lower-zero-face domain is just the tangential `Icc` of its ambient corners. -/
theorem lowerZeroFaceDomain_eq_Icc_boundaryFaceCorners {n : Nat}
    (c d : Fin (n + 1) → Real) :
    lowerZeroFaceDomain c d =
      Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d) := by
  rw [lowerZeroFaceDomain, faceDomain, Fin.succAbove_zero]
  rfl

/-- Build an ambient lower-zero lower corner from tangential lower bounds. -/
def lowerZeroTargetLowerCorner {n : Nat} (c : Fin n → Real) :
    Fin (n + 1) → Real :=
  Fin.cases (0 : Real) c

/-- Build an ambient lower-zero upper corner from tangential upper bounds. -/
def lowerZeroTargetUpperCorner {n : Nat} (d : Fin n → Real) :
    Fin (n + 1) → Real :=
  Fin.cases (0 : Real) d

@[simp]
theorem lowerZeroTargetLowerCorner_zero {n : Nat} (c : Fin n → Real) :
    lowerZeroTargetLowerCorner c 0 = 0 :=
  rfl

theorem lowerZeroTargetCorners_le {n : Nat} {c d : Fin n → Real}
    (hle : c ≤ d) :
    lowerZeroTargetLowerCorner c ≤ lowerZeroTargetUpperCorner d := by
  intro i
  refine Fin.cases ?_ ?_ i
  · exact le_rfl
  · intro j
    exact hle j

@[simp]
theorem boundaryFaceLowerCorner_lowerZeroTargetLowerCorner {n : Nat}
    (c : Fin n → Real) :
    boundaryFaceLowerCorner (lowerZeroTargetLowerCorner c) = c := by
  funext i
  rfl

@[simp]
theorem boundaryFaceUpperCorner_lowerZeroTargetUpperCorner {n : Nat}
    (d : Fin n → Real) :
    boundaryFaceUpperCorner (lowerZeroTargetUpperCorner d) = d := by
  funext i
  rfl

@[simp]
theorem lowerZeroFaceDomain_lowerZeroTargetCorners {n : Nat}
    (c d : Fin n → Real) :
    lowerZeroFaceDomain (lowerZeroTargetLowerCorner c) (lowerZeroTargetUpperCorner d) =
      Set.Icc c d := by
  simp [lowerZeroFaceDomain_eq_Icc_boundaryFaceCorners]

/--
Convert the chart-independent coordinate-image selection predicate into the
boundary-chart compact-image selection predicate for a chosen ambient target
box.
-/
theorem boundaryChartCompactImageBoxSelection_of_compactCoordinateImageBoxSelection
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hcompact : compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    boundaryChartCompactImageBoxSelection I x0 x1 a b c d := by
  change (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ⊆
    Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)
  exact hcompact

/--
The same conversion when the target box is selected first in tangential
coordinates and then lifted to an ambient lower-zero-face box.
-/
theorem boundaryChartCompactImageBoxSelection_of_tangent_compactCoordinateImageBoxSelection
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {c d : Fin n → Real}
    (hcompact : compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) c d) :
    boundaryChartCompactImageBoxSelection I x0 x1 a b
      (lowerZeroTargetLowerCorner c) (lowerZeroTargetUpperCorner d) := by
  simpa using
    (boundaryChartCompactImageBoxSelection_of_compactCoordinateImageBoxSelection
      (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
      (c := lowerZeroTargetLowerCorner c) (d := lowerZeroTargetUpperCorner d)
      hcompact)

/--
Selected target boundary box data for a fixed source boundary box.

The compact-image field gives the `MapsTo` half of image data, and the local
inverse field gives the `SurjOn` half.
-/
structure BoundaryChartTargetBoxSelection {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b : Fin (n + 1) → Real) where
  /-- Lower corner of the selected target boundary box. -/
  lowerCorner : Fin (n + 1) → Real
  /-- Upper corner of the selected target boundary box. -/
  upperCorner : Fin (n + 1) → Real
  /-- The target lower corner lies on the lower zero face. -/
  lowerCorner_zero : lowerCorner 0 = 0
  /-- Coordinatewise ordering of target box corners. -/
  lower_le_upper : lowerCorner ≤ upperCorner
  /-- Compact image control for the source boundary box. -/
  compactImage :
    boundaryChartCompactImageBoxSelection I x0 x1 a b lowerCorner upperCorner
  /-- Local right-inverse data on the selected target boundary box. -/
  localInverse :
    boundaryChartLocalInverseData I x0 x1 a b lowerCorner upperCorner

namespace BoundaryChartTargetBoxSelection

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real}

/-- Package target-box selection data as the image data consumed downstream. -/
theorem imageData (D : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    boundaryChartSelectedBoxImageData I x0 x1 a b D.lowerCorner D.upperCorner :=
  boundaryChartSelectedBoxImageData_of_compactImage_localInverseData
    D.compactImage D.localInverse

/-- Constructor from the two existing boundary chart-box selection halves. -/
def mkOfCompactImageLocalInverseData
    (c d : Fin (n + 1) → Real) (hc0 : c 0 = 0) (hle : c ≤ d)
    (hcompact : boundaryChartCompactImageBoxSelection I x0 x1 a b c d)
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    BoundaryChartTargetBoxSelection I x0 x1 a b where
  lowerCorner := c
  upperCorner := d
  lowerCorner_zero := hc0
  lower_le_upper := hle
  compactImage := hcompact
  localInverse := hlocal

/--
Constructor from a chart-independent coordinate-image box selection plus local
inverse data on the corresponding ambient target box.
-/
def mkOfCompactCoordinateImageBoxSelection
    (c d : Fin (n + 1) → Real) (hc0 : c 0 = 0) (hle : c ≤ d)
    (hcompact : compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d))
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    BoundaryChartTargetBoxSelection I x0 x1 a b :=
  mkOfCompactImageLocalInverseData c d hc0 hle
    (boundaryChartCompactImageBoxSelection_of_compactCoordinateImageBoxSelection hcompact)
    hlocal

/--
Constructor from tangential compact coordinate bounds lifted to a lower-zero
ambient target box.
-/
def mkOfTangentCompactCoordinateImageBoxSelection
    (c d : Fin n → Real) (hle : c ≤ d)
    (hcompact : compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) c d)
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b
      (lowerZeroTargetLowerCorner c) (lowerZeroTargetUpperCorner d)) :
    BoundaryChartTargetBoxSelection I x0 x1 a b :=
  mkOfCompactImageLocalInverseData
    (lowerZeroTargetLowerCorner c) (lowerZeroTargetUpperCorner d)
    (lowerZeroTargetLowerCorner_zero c) (lowerZeroTargetCorners_le hle)
    (boundaryChartCompactImageBoxSelection_of_tangent_compactCoordinateImageBoxSelection
      hcompact)
    hlocal

end BoundaryChartTargetBoxSelection

/--
Compact-coordinate image control required for whichever target box is produced
by a local inverse selection theorem.

This is intentionally explicit: the inverse-function step can select a small
target box, while compact image containment for exactly that target is a
separate geometric input.
-/
def boundaryChartCompactCoordinateImageForLocalInverseTargets {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b : Fin (n + 1) → Real) (y : Fin n → Real) : Prop :=
  ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
    y ∈ lowerZeroFaceDomain c d →
      boundaryChartLocalInverseData I x0 x1 a b c d →
        compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
          (lowerZeroFaceDomain a b) (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)

/--
Turn any local-inverse existence theorem, plus explicit compact-coordinate
image control for the target it selects, into packaged target-box image data.
-/
theorem exists_boundaryChartTargetBoxSelection_of_exists_localInverseData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (hlocal :
      ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
        y ∈ lowerZeroFaceDomain c d ∧
          boundaryChartLocalInverseData I x0 x1 a b c d)
    (hcompact :
      boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y) :
    ∃ D : BoundaryChartTargetBoxSelection I x0 x1 a b,
      y ∈ lowerZeroFaceDomain D.lowerCorner D.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b D.lowerCorner D.upperCorner := by
  rcases hlocal with ⟨c, d, hc0, hle, hy, hlocalData⟩
  let D : BoundaryChartTargetBoxSelection I x0 x1 a b :=
    BoundaryChartTargetBoxSelection.mkOfCompactCoordinateImageBoxSelection
      c d hc0 hle (hcompact c d hc0 hle hy hlocalData) hlocalData
  exact ⟨D, hy, D.imageData⟩

/--
Select target-box image data from a selected source box and explicit compact
image control for the local-inverse target chosen by the oriented transition
theorem.
-/
theorem exists_boundaryChartTargetBoxSelection_of_selectedBox_orient
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hu : u ∈ lowerZeroFaceDomain a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hcompact :
      boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b
        (boundaryChartTransition I x0 x1 u)) :
    ∃ D : BoundaryChartTargetBoxSelection I x0 x1 a b,
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain D.lowerCorner D.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b D.lowerCorner D.upperCorner :=
  exists_boundaryChartTargetBoxSelection_of_exists_localInverseData
    (exists_boundaryChartLocalInverseData_of_selectedBox_orient
      hbox horient hu hsource)
    hcompact

/-- Oriented-atlas wrapper for target-box image-data selection. -/
theorem exists_boundaryChartTargetBoxSelection_of_selectedBox_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hu : u ∈ lowerZeroFaceDomain a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hcompact :
      boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b
        (boundaryChartTransition I x0 x1 u)) :
    ∃ D : BoundaryChartTargetBoxSelection I x0 x1 a b,
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain D.lowerCorner D.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b D.lowerCorner D.upperCorner :=
  exists_boundaryChartTargetBoxSelection_of_exists_localInverseData
    (exists_boundaryChartLocalInverseData_of_selectedBox_orientedAtlas
      A hx0 hx1 hbox hu hsource)
    hcompact

/-- Oriented-boundary-manifold wrapper for target-box image-data selection. -/
theorem exists_boundaryChartTargetBoxSelection_of_selectedBox_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M] [BoundaryChartOrientedManifold I M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hu : u ∈ lowerZeroFaceDomain a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hcompact :
      boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b
        (boundaryChartTransition I x0 x1 u)) :
    ∃ D : BoundaryChartTargetBoxSelection I x0 x1 a b,
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain D.lowerCorner D.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b D.lowerCorner D.upperCorner :=
  exists_boundaryChartTargetBoxSelection_of_exists_localInverseData
    (exists_boundaryChartLocalInverseData_of_selectedBox_orientedManifold
      hbox hu hsource)
    hcompact

/--
Compact-image target-box selection from an actually compact coordinate image,
with local inverse data supplied for the selected compact-coordinate box.
-/
theorem exists_boundaryChartTargetBoxSelection_of_isCompact_image_localInverseData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real}
    (hK : IsCompact
      ((boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b))
    (hlocal :
      ∀ c d : Fin n → Real, c ≤ d →
        compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
          (lowerZeroFaceDomain a b) c d →
          boundaryChartLocalInverseData I x0 x1 a b
            (lowerZeroTargetLowerCorner c) (lowerZeroTargetUpperCorner d)) :
    ∃ D : BoundaryChartTargetBoxSelection I x0 x1 a b,
      boundaryChartSelectedBoxImageData I x0 x1 a b D.lowerCorner D.upperCorner := by
  rcases exists_compactCoordinateImageBoxSelection_of_isCompact_image
      (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b) hK with
    ⟨c, d, hle, hcompact⟩
  let D : BoundaryChartTargetBoxSelection I x0 x1 a b :=
    BoundaryChartTargetBoxSelection.mkOfTangentCompactCoordinateImageBoxSelection
      c d hle hcompact (hlocal c d hle hcompact)
  exact ⟨D, D.imageData⟩

end ManifoldBoundary

end Stokes

end
