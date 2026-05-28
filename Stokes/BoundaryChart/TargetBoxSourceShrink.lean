import Stokes.BoundaryChart.TargetBoxCompactImage

/-!
# Source-shrink route for boundary target boxes

`TargetBoxCompactImage` isolates a genuine obstruction: a small target box
chosen by local openness is usually too small to contain the image of the
original source box.  This file records the alternative route that should be
used downstream: once a target box is fixed as a neighborhood of the target
point, continuity lets us shrink the source box so its image lands in that
target box.

The remaining nontrivial field is then honest and geometric: the local inverse
for the target box must land in the same shrunken source box, not merely in the
old larger source box.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section ManifoldBoundary

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- Coordinatewise tangential bounds imply inclusion of lower-zero face boxes. -/
theorem lowerZeroFaceDomain_subset_of_tangent_bounds {n : Nat}
    {a b a' b' : Fin (n + 1) → Real}
    (hleft : ∀ i : Fin n, a i.succ ≤ a' i.succ)
    (hright : ∀ i : Fin n, b' i.succ ≤ b i.succ) :
    lowerZeroFaceDomain a' b' ⊆ lowerZeroFaceDomain a b := by
  intro x hx
  rw [lowerZeroFaceDomain, faceDomain] at hx ⊢
  constructor
  · intro i
    have hi : (a ∘ Fin.succAbove (0 : Fin (n + 1))) i ≤
        (a' ∘ Fin.succAbove (0 : Fin (n + 1))) i := by
      simpa [Function.comp_def] using hleft i
    exact hi.trans (hx.1 i)
  · intro i
    have hi : (b' ∘ Fin.succAbove (0 : Fin (n + 1))) i ≤
        (b ∘ Fin.succAbove (0 : Fin (n + 1))) i := by
      simpa [Function.comp_def] using hright i
    exact (hx.2 i).trans hi

/-- A `MapsTo` statement is exactly the compact-image half for boundary boxes. -/
theorem boundaryChartCompactImageBoxSelection_of_mapsTo {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    boundaryChartCompactImageBoxSelection I x0 x1 a b c d := by
  rintro _ ⟨u, hu, rfl⟩
  exact hmaps hu

/-- Compact-image containment restricts to smaller source boxes. -/
theorem boundaryChartCompactImageBoxSelection_mono_source {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b a' b' c d : Fin (n + 1) → Real}
    (hsource : lowerZeroFaceDomain a' b' ⊆ lowerZeroFaceDomain a b)
    (hcompact : boundaryChartCompactImageBoxSelection I x0 x1 a b c d) :
    boundaryChartCompactImageBoxSelection I x0 x1 a' b' c d := by
  rintro _ ⟨u, hu, rfl⟩
  exact hcompact ⟨u, hsource hu, rfl⟩

/-- Local inverse data persists when the source box is enlarged. -/
theorem boundaryChartLocalInverseData.mono_source {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b a' b' c d : Fin (n + 1) → Real}
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d)
    (hsource : lowerZeroFaceDomain a b ⊆ lowerZeroFaceDomain a' b') :
    boundaryChartLocalInverseData I x0 x1 a' b' c d := by
  rcases hlocal with ⟨g, hmap, hright⟩
  exact ⟨g, fun y hy => hsource (hmap hy), hright⟩

/--
Data produced by the source-shrink route for fixed target corners.

It says that the source lower-zero box has been shrunk inside the original
source box and maps into the fixed target box.  To obtain full target-box image
data, one still needs a local inverse whose values land in this shrunken source
box.
-/
structure BoundaryChartSourceShrinkMapsToData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b c d : Fin (n + 1) → Real) (u : Fin n → Real) where
  /-- Lower corner of the shrunken source box. -/
  sourceLowerCorner : Fin (n + 1) → Real
  /-- Upper corner of the shrunken source box. -/
  sourceUpperCorner : Fin (n + 1) → Real
  /-- Boundary convention for the shrunken source box. -/
  sourceLowerCorner_zero : sourceLowerCorner 0 = 0
  /-- Coordinatewise ordering of the shrunken source box. -/
  sourceLower_le_sourceUpper : sourceLowerCorner ≤ sourceUpperCorner
  /-- The source point remains in the shrunken source box. -/
  sourcePoint_mem : u ∈ lowerZeroFaceDomain sourceLowerCorner sourceUpperCorner
  /-- The shrunken source box lies in the original source box. -/
  sourceSubset_original :
    lowerZeroFaceDomain sourceLowerCorner sourceUpperCorner ⊆ lowerZeroFaceDomain a b
  /-- The shrunken source box maps into the fixed target box. -/
  mapsTo_target :
    MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain sourceLowerCorner sourceUpperCorner)
      (lowerZeroFaceDomain c d)

namespace BoundaryChartSourceShrinkMapsToData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b c d : Fin (n + 1) → Real} {u : Fin n → Real}

/-- The maps-to field as compact-image containment for the shrunken source. -/
theorem compactImage
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u) :
    boundaryChartCompactImageBoxSelection I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner c d :=
  boundaryChartCompactImageBoxSelection_of_mapsTo D.mapsTo_target

/-- If the target has a local inverse landing in the shrunken source, package a target box. -/
def targetBoxSelection
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u)
    (hc0 : c 0 = 0) (hle : c ≤ d)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d) :
    BoundaryChartTargetBoxSelection I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner :=
  BoundaryChartTargetBoxSelection.mkOfCompactImageLocalInverseData
    c d hc0 hle D.compactImage hlocal

/-- Full image data for the shrunken source box once the local inverse lands there. -/
theorem imageData
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u)
    (hc0 : c 0 = 0) (hle : c ≤ d)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d) :
    boundaryChartSelectedBoxImageData I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner c d :=
  (D.targetBoxSelection hc0 hle hlocal).imageData

end BoundaryChartSourceShrinkMapsToData

/--
Continuity chooses a shrunken source lower-zero box whose image lands in a fixed
target lower-zero box, while staying inside the original source box.

This is the formal core of the recommended source-shrink route.  Notice that it
only proves the `MapsTo`/compact-image half.  Surjectivity still requires local
inverse data into the same shrunken source box.
-/
theorem nonempty_boundaryChartSourceShrinkMapsToData_of_continuousAt {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real} {u : Fin n → Real}
    (hcont : ContinuousAt (boundaryChartTransition I x0 x1) u)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (htarget :
      lowerZeroFaceDomain c d ∈ 𝓝 (boundaryChartTransition I x0 x1 u)) :
    Nonempty (BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u) := by
  have hpre :
      (boundaryChartTransition I x0 x1) ⁻¹' lowerZeroFaceDomain c d ∈ 𝓝 u :=
    hcont htarget
  have hinter :
      ((boundaryChartTransition I x0 x1) ⁻¹' lowerZeroFaceDomain c d ∩
          lowerZeroFaceDomain a b) ∈ 𝓝 u :=
    inter_mem hpre hsource
  rcases exists_lowerZeroFaceDomain_subset_of_mem_nhds hinter with
    ⟨a', b', ha0, hle, hu, hsubset⟩
  refine ⟨
    { sourceLowerCorner := a'
      sourceUpperCorner := b'
      sourceLowerCorner_zero := ha0
      sourceLower_le_sourceUpper := hle
      sourcePoint_mem := hu
      sourceSubset_original := ?_
      mapsTo_target := ?_ }⟩
  · intro z hz
    exact (hsubset hz).2
  · intro z hz
    exact (hsubset hz).1

/--
The source-shrink route with the remaining local-inverse landing condition
made explicit.
-/
structure BoundaryChartSourceShrinkTargetBoxData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b c d : Fin (n + 1) → Real) (u : Fin n → Real)
    extends BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u where
  /-- Boundary convention for the target box. -/
  targetLowerCorner_zero : c 0 = 0
  /-- Coordinatewise ordering of the target box. -/
  targetLower_le_targetUpper : c ≤ d
  /-- The local inverse must land in the shrunken source box. -/
  localInverse :
    boundaryChartLocalInverseData I x0 x1 sourceLowerCorner sourceUpperCorner c d

namespace BoundaryChartSourceShrinkTargetBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b c d : Fin (n + 1) → Real} {u : Fin n → Real}

/-- Package source-shrink data as the standard selected target-box record. -/
def targetBoxSelection
    (D : BoundaryChartSourceShrinkTargetBoxData I x0 x1 a b c d u) :
    BoundaryChartTargetBoxSelection I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner :=
  D.toBoundaryChartSourceShrinkMapsToData.targetBoxSelection
    D.targetLowerCorner_zero D.targetLower_le_targetUpper D.localInverse

/-- Full boundary selected-box image data for the shrunken source box. -/
theorem imageData
    (D : BoundaryChartSourceShrinkTargetBoxData I x0 x1 a b c d u) :
    boundaryChartSelectedBoxImageData I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner c d :=
  D.targetBoxSelection.imageData

end BoundaryChartSourceShrinkTargetBoxData

/--
The alternative "large target box" route: choose a target box containing the
compact image and then prove local-inverse data on that same, possibly large,
box.

This is useful as a comparison point, but in applications the local-inverse
field is usually the difficult part: a compact-image bounding box need not lie
inside the local image supplied by the inverse function theorem.
-/
structure BoundaryChartCompactImageTargetBoxRoute {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b : Fin (n + 1) → Real) where
  /-- Compactness of the full source-box image. -/
  isCompact_image :
    IsCompact ((boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b)
  /-- Local inverse data for whichever compact-image bounding box is selected. -/
  localInverseForCompactBox :
    ∀ c d : Fin n → Real, c ≤ d →
      compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
        (lowerZeroFaceDomain a b) c d →
        boundaryChartLocalInverseData I x0 x1 a b
          (lowerZeroTargetLowerCorner c) (lowerZeroTargetUpperCorner d)

namespace BoundaryChartCompactImageTargetBoxRoute

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real}

/-- Materialize the compact-image target-box route using the existing constructor. -/
theorem exists_targetBoxSelection
    (R : BoundaryChartCompactImageTargetBoxRoute I x0 x1 a b) :
    ∃ D : BoundaryChartTargetBoxSelection I x0 x1 a b,
      boundaryChartSelectedBoxImageData I x0 x1 a b
        D.lowerCorner D.upperCorner :=
  exists_boundaryChartTargetBoxSelection_of_isCompact_image_localInverseData
    R.isCompact_image R.localInverseForCompactBox

end BoundaryChartCompactImageTargetBoxRoute

end ManifoldBoundary

end Stokes

end
