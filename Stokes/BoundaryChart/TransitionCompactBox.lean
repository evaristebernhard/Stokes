import Stokes.BoundaryChart.OrientationCovBridge

/-!
# Boundary chart transition compact target boxes

This file keeps the compact coordinate-box and target-image bookkeeping on the
pure boundary-chart side of the development.  The inverse-function/local
openness step supplies local right-inverse data for a small target boundary box;
the separate compact-image field records the remaining geometric containment
needed to turn that local target into image data for change of variables.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.unusedFintypeInType false

universe u v w

/--
A compact coordinate set together with a closed coordinate box containing it.

The order is intentionally abstract: the existence theorem below specializes
the package to finite real coordinate spaces `ι → Real`, while downstream chart
APIs can reuse the projections for any ordered coordinate model.
-/
structure CompactCoordinateBoxSelection (E : Type u) [TopologicalSpace E] [Preorder E] where
  /-- The compact coordinate set being boxed. -/
  K : Set E
  /-- Compactness of the coordinate set. -/
  isCompact_K : IsCompact K
  /-- Lower corner of the selected coordinate box. -/
  a : E
  /-- Upper corner of the selected coordinate box. -/
  b : E
  /-- Coordinatewise order of the selected box corners. -/
  le : a ≤ b
  /-- The compact set lies in the selected closed coordinate box. -/
  subset_Icc : K ⊆ Set.Icc a b

namespace CompactCoordinateBoxSelection

variable {E : Type u} [TopologicalSpace E] [Preorder E]

/-- Constructor from an explicit compact set and containing closed box. -/
def of_subset (K : Set E) (hK : IsCompact K) (a b : E) (hle : a ≤ b)
    (hsubset : K ⊆ Set.Icc a b) : CompactCoordinateBoxSelection E where
  K := K
  isCompact_K := hK
  a := a
  b := b
  le := hle
  subset_Icc := hsubset

theorem isCompact (B : CompactCoordinateBoxSelection E) : IsCompact B.K :=
  B.isCompact_K

theorem mem_Icc (B : CompactCoordinateBoxSelection E) {x : E} (hx : x ∈ B.K) :
    x ∈ Set.Icc B.a B.b :=
  B.subset_Icc hx

theorem lower_le_of_mem (B : CompactCoordinateBoxSelection E) {x : E}
    (hx : x ∈ B.K) : B.a ≤ x :=
  (B.mem_Icc hx).1

theorem le_upper_of_mem (B : CompactCoordinateBoxSelection E) {x : E}
    (hx : x ∈ B.K) : x ≤ B.b :=
  (B.mem_Icc hx).2

end CompactCoordinateBoxSelection

section PiReal

variable {ι : Type u} [Fintype ι]

/-- Every coordinate of a finite real coordinate vector is bounded by its sup norm. -/
theorem piReal_coord_norm_le_norm (x : ι → Real) (i : ι) :
    ‖x i‖ ≤ ‖x‖ := by
  rw [Pi.norm_def]
  exact NNReal.coe_le_coe.mpr
    (Finset.le_sup (f := fun j : ι => ‖x j‖₊) (Finset.mem_univ i))

/--
Compact subsets of a finite real coordinate space fit into a closed coordinate
box.
-/
theorem exists_Icc_subset_of_isCompact_piReal
    {K : Set (ι → Real)} (hK : IsCompact K) :
    ∃ a b : ι → Real, a ≤ b ∧ K ⊆ Set.Icc a b := by
  obtain ⟨R, _hRpos, hR⟩ := hK.isBounded.exists_pos_norm_le
  let a : ι → Real := fun _ => -(R + 1)
  let b : ι → Real := fun _ => R + 1
  refine ⟨a, b, ?_, ?_⟩
  · intro i
    dsimp [a, b]
    linarith
  · intro x hx
    have hxnorm : ‖x‖ ≤ R := hR x hx
    have hcoord_le : ∀ i : ι, x i ≤ R := by
      intro i
      exact (le_abs_self (x i)).trans ((piReal_coord_norm_le_norm x i).trans hxnorm)
    have hcoord_ge : ∀ i : ι, -R ≤ x i := by
      intro i
      have habs : |x i| ≤ R := by
        simpa [Real.norm_eq_abs] using (piReal_coord_norm_le_norm x i).trans hxnorm
      exact (neg_le_neg habs).trans (neg_abs_le (x i))
    constructor
    · intro i
      have hxi := hcoord_ge i
      dsimp [a]
      linarith
    · intro i
      have hxi := hcoord_le i
      dsimp [b]
      linarith

/--
Pack the preceding theorem as `CompactCoordinateBoxSelection` for finite real
coordinate spaces.
-/
theorem exists_compactCoordinateBoxSelection_piReal
    {K : Set (ι → Real)} (hK : IsCompact K) :
    ∃ B : CompactCoordinateBoxSelection (ι → Real), B.K = K := by
  rcases exists_Icc_subset_of_isCompact_piReal hK with ⟨a, b, hle, hsubset⟩
  exact ⟨CompactCoordinateBoxSelection.of_subset K hK a b hle hsubset, rfl⟩

/-- `Fin n → Real` spelling of `exists_Icc_subset_of_isCompact_piReal`. -/
theorem exists_Icc_subset_of_isCompact_fin
    {n : Nat} {K : Set (Fin n → Real)} (hK : IsCompact K) :
    ∃ a b : Fin n → Real, a ≤ b ∧ K ⊆ Set.Icc a b :=
  exists_Icc_subset_of_isCompact_piReal hK

/-- `Fin n → Real` spelling of `exists_compactCoordinateBoxSelection_piReal`. -/
theorem exists_compactCoordinateBoxSelection_fin
    {n : Nat} {K : Set (Fin n → Real)} (hK : IsCompact K) :
    ∃ B : CompactCoordinateBoxSelection (Fin n → Real), B.K = K :=
  exists_compactCoordinateBoxSelection_piReal hK

/--
The compact-image predicate for coordinate maps: the image of a set is contained
in a selected coordinate box.
-/
def compactCoordinateImageBoxSelection {α : Type v} (φ : α → ι → Real)
    (s : Set α) (a b : ι → Real) : Prop :=
  φ '' s ⊆ Set.Icc a b

namespace compactCoordinateImageBoxSelection

variable {α : Type v} {φ : α → ι → Real} {s : Set α} {a b : ι → Real}

omit [Fintype ι] in
theorem mapsTo (h : compactCoordinateImageBoxSelection φ s a b) :
    MapsTo φ s (Set.Icc a b) := by
  intro x hx
  exact h ⟨x, hx, rfl⟩

end compactCoordinateImageBoxSelection

/--
If a coordinate image is compact, it can be placed in a selected coordinate box.
-/
theorem exists_compactCoordinateImageBoxSelection_of_isCompact_image
    {α : Type v} (φ : α → ι → Real) (s : Set α)
    (hK : IsCompact (φ '' s)) :
    ∃ a b : ι → Real, a ≤ b ∧ compactCoordinateImageBoxSelection φ s a b := by
  rcases exists_Icc_subset_of_isCompact_piReal hK with ⟨a, b, hle, hsubset⟩
  exact ⟨a, b, hle, hsubset⟩

/--
Continuous coordinate images of compact sets can be placed in a selected
coordinate box.
-/
theorem exists_compactCoordinateImageBoxSelection_of_continuousOn
    {α : Type v} [TopologicalSpace α] {φ : α → ι → Real} {s : Set α}
    (hs : IsCompact s) (hφ : ContinuousOn φ s) :
    ∃ a b : ι → Real, a ≤ b ∧ compactCoordinateImageBoxSelection φ s a b :=
  exists_compactCoordinateImageBoxSelection_of_isCompact_image φ s
    (hs.image_of_continuousOn hφ)

end PiReal

section ManifoldBoundary

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Selected target boundary-box data for a boundary chart transition.

The local-openness/IFT side supplies `localInverse`; the `compactImage` field is
the remaining target-box containment: the image of the whole source boundary box
must land in the same selected target box.
-/
structure BoundaryChartTransitionCompactBoxData {n : Nat}
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
  /-- The full source boundary-box image lies in the selected target box. -/
  compactImage :
    boundaryChartCompactImageBoxSelection I x0 x1 a b lowerCorner upperCorner
  /-- Local right-inverse data on the selected target box. -/
  localInverse :
    boundaryChartLocalInverseData I x0 x1 a b lowerCorner upperCorner

namespace BoundaryChartTransitionCompactBoxData

variable {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real}

/-- Package transition compact-box data as image data consumed downstream. -/
theorem imageData (D : BoundaryChartTransitionCompactBoxData I x0 x1 a b) :
    boundaryChartSelectedBoxImageData I x0 x1 a b D.lowerCorner D.upperCorner :=
  boundaryChartSelectedBoxImageData_of_compactImage_localInverseData
    D.compactImage D.localInverse

/-- Constructor from compact image containment and local inverse data. -/
def mkOfCompactImageLocalInverseData
    (c d : Fin (n + 1) → Real) (hc0 : c 0 = 0) (hle : c ≤ d)
    (hcompact : boundaryChartCompactImageBoxSelection I x0 x1 a b c d)
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    BoundaryChartTransitionCompactBoxData I x0 x1 a b where
  lowerCorner := c
  upperCorner := d
  lowerCorner_zero := hc0
  lower_le_upper := hle
  compactImage := hcompact
  localInverse := hlocal

/--
Projection to the selected-box orientation/COV package once the orientation-map
and compatibility data are available.
-/
def toSelectedBoxOrientationCovData
    (D : BoundaryChartTransitionCompactBoxData I x0 x1 a b)
    {ω : ManifoldForm I M n}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcompat :
      boundaryChartTransitionCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hdata :
      BoundaryChartOrientationMapDataOn I x0 x1 (lowerZeroFaceDomain a b)) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω
      a b D.lowerCorner D.upperCorner where
  selectedBox := hbox
  compatibleOn := hcompat
  orientationMapDataOn := hdata
  imageData := D.imageData

/-- Oriented-atlas specialization of `toSelectedBoxOrientationCovData`. -/
def toSelectedBoxOrientationCovDataOfOrientedAtlas
    (D : BoundaryChartTransitionCompactBoxData I x0 x1 a b)
    (A : BoundaryChartOrientedAtlas I M) (hx0 : x0 ∈ A.charts)
    (hx1 : x1 ∈ A.charts) {ω : ManifoldForm I M n}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω
      a b D.lowerCorner D.upperCorner :=
  BoundaryChartSelectedBoxOrientationCovData.ofOrientedAtlas
    A hx0 hx1 hbox D.imageData

/-- Oriented-manifold specialization of `toSelectedBoxOrientationCovData`. -/
def toSelectedBoxOrientationCovDataOfOrientedManifold
    [BoundaryChartOrientedManifold I M]
    (D : BoundaryChartTransitionCompactBoxData I x0 x1 a b)
    {ω : ManifoldForm I M n}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω
      a b D.lowerCorner D.upperCorner :=
  BoundaryChartSelectedBoxOrientationCovData.ofOrientedManifold hbox D.imageData

end BoundaryChartTransitionCompactBoxData

/--
Compact-image containment required for whichever target box is produced by a
local inverse selection theorem.

This is the intentional remaining field after the inverse-function/local
openness step: the selected target box is locally covered by the source image,
but a separate containment hypothesis is needed to make the whole source-box
image land in that same target box.
-/
def boundaryChartCompactImageForLocalInverseTargets {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b : Fin (n + 1) → Real) (y : Fin n → Real) : Prop :=
  ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
    y ∈ lowerZeroFaceDomain c d →
      boundaryChartLocalInverseData I x0 x1 a b c d →
        boundaryChartCompactImageBoxSelection I x0 x1 a b c d

/--
Turn any local-inverse existence theorem, plus explicit compact-image control
for the target it selects, into transition compact-box data.
-/
theorem exists_boundaryChartTransitionCompactBoxData_of_exists_localInverseData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (hlocal :
      ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
        y ∈ lowerZeroFaceDomain c d ∧
          boundaryChartLocalInverseData I x0 x1 a b c d)
    (hcompact :
      boundaryChartCompactImageForLocalInverseTargets I x0 x1 a b y) :
    ∃ D : BoundaryChartTransitionCompactBoxData I x0 x1 a b,
      y ∈ lowerZeroFaceDomain D.lowerCorner D.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b D.lowerCorner D.upperCorner := by
  rcases hlocal with ⟨c, d, hc0, hle, hy, hlocalData⟩
  let D : BoundaryChartTransitionCompactBoxData I x0 x1 a b :=
    BoundaryChartTransitionCompactBoxData.mkOfCompactImageLocalInverseData
      c d hc0 hle (hcompact c d hc0 hle hy hlocalData) hlocalData
  exact ⟨D, hy, D.imageData⟩

/--
Selected-box specialization from explicit orientation compatibility.
-/
theorem exists_boundaryChartTransitionCompactBoxData_of_selectedBox_orient
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hu : u ∈ lowerZeroFaceDomain a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hcompact :
      boundaryChartCompactImageForLocalInverseTargets I x0 x1 a b
        (boundaryChartTransition I x0 x1 u)) :
    ∃ D : BoundaryChartTransitionCompactBoxData I x0 x1 a b,
      boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain D.lowerCorner D.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b D.lowerCorner D.upperCorner :=
  exists_boundaryChartTransitionCompactBoxData_of_exists_localInverseData
    (exists_boundaryChartLocalInverseData_of_selectedBox_orient
      hbox horient hu hsource)
    hcompact

/-- Oriented-atlas wrapper for transition compact-box selection. -/
theorem exists_boundaryChartTransitionCompactBoxData_of_selectedBox_orientedAtlas
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
      boundaryChartCompactImageForLocalInverseTargets I x0 x1 a b
        (boundaryChartTransition I x0 x1 u)) :
    ∃ D : BoundaryChartTransitionCompactBoxData I x0 x1 a b,
      boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain D.lowerCorner D.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b D.lowerCorner D.upperCorner :=
  exists_boundaryChartTransitionCompactBoxData_of_exists_localInverseData
    (exists_boundaryChartLocalInverseData_of_selectedBox_orientedAtlas
      A hx0 hx1 hbox hu hsource)
    hcompact

/-- Oriented-manifold wrapper for transition compact-box selection. -/
theorem exists_boundaryChartTransitionCompactBoxData_of_selectedBox_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M] [BoundaryChartOrientedManifold I M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hu : u ∈ lowerZeroFaceDomain a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hcompact :
      boundaryChartCompactImageForLocalInverseTargets I x0 x1 a b
        (boundaryChartTransition I x0 x1 u)) :
    ∃ D : BoundaryChartTransitionCompactBoxData I x0 x1 a b,
      boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain D.lowerCorner D.upperCorner ∧
        boundaryChartSelectedBoxImageData I x0 x1 a b D.lowerCorner D.upperCorner :=
  exists_boundaryChartTransitionCompactBoxData_of_exists_localInverseData
    (exists_boundaryChartLocalInverseData_of_selectedBox_orientedManifold
      hbox hu hsource)
    hcompact

/--
Oriented-atlas wrapper producing the orientation/COV data package for the
selected target box.
-/
theorem exists_boundaryChartSelectedBoxOrientationCovData_of_selectedBox_orientedAtlas
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
      boundaryChartCompactImageForLocalInverseTargets I x0 x1 a b
        (boundaryChartTransition I x0 x1 u)) :
    ∃ D : BoundaryChartTransitionCompactBoxData I x0 x1 a b,
      ∃ _covData : BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω
          a b D.lowerCorner D.upperCorner,
        boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain D.lowerCorner D.upperCorner := by
  rcases exists_boundaryChartTransitionCompactBoxData_of_selectedBox_orientedAtlas
      A hx0 hx1 hbox hu hsource hcompact with
    ⟨D, hy, _himage⟩
  exact ⟨D, D.toSelectedBoxOrientationCovDataOfOrientedAtlas A hx0 hx1 hbox, hy⟩

/--
Oriented-manifold wrapper producing the orientation/COV data package for the
selected target box.
-/
theorem exists_boundaryChartSelectedBoxOrientationCovData_of_selectedBox_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M] [BoundaryChartOrientedManifold I M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hu : u ∈ lowerZeroFaceDomain a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hcompact :
      boundaryChartCompactImageForLocalInverseTargets I x0 x1 a b
        (boundaryChartTransition I x0 x1 u)) :
    ∃ D : BoundaryChartTransitionCompactBoxData I x0 x1 a b,
      ∃ _covData : BoundaryChartSelectedBoxOrientationCovData I x0 x1 ω
          a b D.lowerCorner D.upperCorner,
        boundaryChartTransition I x0 x1 u ∈
          lowerZeroFaceDomain D.lowerCorner D.upperCorner := by
  rcases exists_boundaryChartTransitionCompactBoxData_of_selectedBox_orientedManifold
      hbox hu hsource hcompact with
    ⟨D, hy, _himage⟩
  exact ⟨D, D.toSelectedBoxOrientationCovDataOfOrientedManifold hbox, hy⟩

end ManifoldBoundary

end Stokes

end
