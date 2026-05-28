import Stokes.BoundaryChart.TargetBoxSourceShrink

/-!
# Inverse half for source-shrink target boxes

`TargetBoxSourceShrink` proves the compact-image half of the source-shrink
route: after a target box is fixed, continuity can shrink the source box so
that its image lands in the target box.

This file isolates the complementary inverse half.  A visible local inverse
which is continuous at the target point lets us shrink the target box so that
the inverse lands in a prescribed shrunken source box.  The remaining
`MapsTo`/compact-image half for that newly selected target box is kept as an
explicit field by `BoundaryChartSourceShrinkInverseTargetBoxData`.
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

/--
Neighborhood small-box selection, with the selected lower-zero box itself
recorded as a neighborhood of the center.

The older `exists_lowerZeroFaceDomain_subset_of_mem_nhds` is enough for many
one-shot local-openness arguments.  For inverse shrinking it is useful to keep
the selected target box as a reusable neighborhood.
-/
theorem exists_lowerZeroFaceDomain_mem_nhds_subset_of_mem_nhds {n : Nat}
    {U : Set (Fin n → Real)} {y : Fin n → Real} (hU : U ∈ 𝓝 y) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      y ∈ lowerZeroFaceDomain c d ∧
        lowerZeroFaceDomain c d ∈ 𝓝 y ∧
          lowerZeroFaceDomain c d ⊆ U := by
  obtain ⟨ε, hεpos, hεsubset⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  let c : Fin (n + 1) → Real := Fin.cases (0 : Real) (fun i : Fin n => y i - ε)
  let d : Fin (n + 1) → Real := Fin.cases (0 : Real) (fun i : Fin n => y i + ε)
  refine ⟨c, d, rfl, ?_, ?_, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ ?_ j
    · dsimp [c, d]
      exact le_rfl
    · intro i
      dsimp [c, d]
      linarith
  · rw [lowerZeroFaceDomain, faceDomain]
    constructor
    · intro i
      dsimp [c, Function.comp_def]
      linarith
    · intro i
      dsimp [d, Function.comp_def]
      linarith
  · apply lowerZeroFaceDomain_mem_nhds_of_lt
    · intro i
      dsimp [c]
      linarith
    · intro i
      dsimp [d]
      linarith
  · intro z hz
    apply hεsubset
    rw [Metric.mem_closedBall]
    rw [dist_pi_le_iff (le_of_lt hεpos)]
    intro i
    rw [Real.dist_eq, abs_sub_le_iff]
    rw [lowerZeroFaceDomain, faceDomain] at hz
    have hleft := hz.1 i
    have hright := hz.2 i
    constructor
    · have hzi : z i ≤ y i + ε := by
        simpa [d, Function.comp_def] using hright
      linarith
    · have hzi : y i - ε ≤ z i := by
        simpa [c, Function.comp_def] using hleft
      linarith

/-- Local inverse data restricts to smaller target boxes. -/
theorem boundaryChartLocalInverseData.mono_target {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d c' d' : Fin (n + 1) → Real}
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d)
    (htarget : lowerZeroFaceDomain c' d' ⊆ lowerZeroFaceDomain c d) :
    boundaryChartLocalInverseData I x0 x1 a b c' d' := by
  rcases hlocal with ⟨g, hmap, hright⟩
  exact ⟨g, fun y hy => hmap (htarget hy),
    fun y hy => hright y (htarget hy)⟩

/--
Local inverse data is monotone in the two directions needed for box shrinking:
the source box may be enlarged and the target box may be shrunk.
-/
theorem boundaryChartLocalInverseData.mono_source_target {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b a' b' c d c' d' : Fin (n + 1) → Real}
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d)
    (hsource : lowerZeroFaceDomain a b ⊆ lowerZeroFaceDomain a' b')
    (htarget : lowerZeroFaceDomain c' d' ⊆ lowerZeroFaceDomain c d) :
    boundaryChartLocalInverseData I x0 x1 a' b' c' d' := by
  rcases hlocal with ⟨g, hmap, hright⟩
  exact ⟨g, fun y hy => hsource (hmap (htarget hy)),
    fun y hy => hright y (htarget hy)⟩

/--
A local inverse with a named inverse function and continuity at the target
point.

The existing `boundaryChartLocalInverseData` intentionally hides the inverse
function behind an existential.  Target-side shrinking needs to mention
continuity of that function, so this small constructor-facing record exposes
exactly the extra data.
-/
structure BoundaryChartContinuousLocalInverseData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b c d : Fin (n + 1) → Real) (y : Fin n → Real) where
  /-- The chosen local right inverse on the target box. -/
  invFun : (Fin n → Real) → (Fin n → Real)
  /-- The inverse lands in the current source box on the current target box. -/
  mapsTo_source :
    MapsTo invFun (lowerZeroFaceDomain c d) (lowerZeroFaceDomain a b)
  /-- Right-inverse identity on the current target box. -/
  right_inv :
    ∀ z ∈ lowerZeroFaceDomain c d,
      boundaryChartTransition I x0 x1 (invFun z) = z
  /-- Continuity of the chosen inverse at the target point to be shrunk around. -/
  continuousAt_invFun : ContinuousAt invFun y

namespace BoundaryChartContinuousLocalInverseData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b c d : Fin (n + 1) → Real} {y : Fin n → Real}

/-- Forget the named continuous inverse down to the existing local-inverse API. -/
def toLocalInverseData
    (G : BoundaryChartContinuousLocalInverseData I x0 x1 a b c d y) :
    boundaryChartLocalInverseData I x0 x1 a b c d :=
  ⟨G.invFun, G.mapsTo_source, G.right_inv⟩

/--
Shrink the target box so that the named local inverse lands in a prescribed
source neighborhood.

This is the inverse half of the source-shrink route.  The theorem does not
claim that the shrunken source maps into the newly selected target box; that is
the independent compact-image/`MapsTo` half packaged below.
-/
theorem exists_targetShrinkLocalInverseData
    (G : BoundaryChartContinuousLocalInverseData I x0 x1 a b c d y)
    {a' b' : Fin (n + 1) → Real}
    (hsource :
      lowerZeroFaceDomain a' b' ∈ 𝓝 (G.invFun y))
    (htarget : lowerZeroFaceDomain c d ∈ 𝓝 y) :
    ∃ c' d' : Fin (n + 1) → Real, c' 0 = 0 ∧ c' ≤ d' ∧
      y ∈ lowerZeroFaceDomain c' d' ∧
        lowerZeroFaceDomain c' d' ∈ 𝓝 y ∧
          lowerZeroFaceDomain c' d' ⊆ lowerZeroFaceDomain c d ∧
            boundaryChartLocalInverseData I x0 x1 a' b' c' d' := by
  have hpre :
      G.invFun ⁻¹' lowerZeroFaceDomain a' b' ∈ 𝓝 y :=
    G.continuousAt_invFun hsource
  have hinter :
      (G.invFun ⁻¹' lowerZeroFaceDomain a' b' ∩
          lowerZeroFaceDomain c d) ∈ 𝓝 y :=
    inter_mem hpre htarget
  rcases exists_lowerZeroFaceDomain_mem_nhds_subset_of_mem_nhds hinter with
    ⟨c', d', hc0, hle, hy, hnhds, hsubset⟩
  refine ⟨c', d', hc0, hle, hy, hnhds, ?_, ?_⟩
  · intro z hz
    exact (hsubset hz).2
  · exact ⟨G.invFun, fun z hz => (hsubset hz).1,
      fun z hz => G.right_inv z ((hsubset hz).2)⟩

end BoundaryChartContinuousLocalInverseData

namespace BoundaryChartSourceShrinkMapsToData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b c d : Fin (n + 1) → Real} {u : Fin n → Real}

/--
Upgrade source-shrink `MapsTo` data to the full source-shrink target-box record
once the inverse half is known for the same shrunken source and target box.
-/
def toTargetBoxData
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u)
    (hc0 : c 0 = 0) (hle : c ≤ d)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d) :
    BoundaryChartSourceShrinkTargetBoxData I x0 x1 a b c d u where
  toBoundaryChartSourceShrinkMapsToData := D
  targetLowerCorner_zero := hc0
  targetLower_le_targetUpper := hle
  localInverse := hlocal

end BoundaryChartSourceShrinkMapsToData

/--
Completed source-shrink inverse target-box data.

The record is deliberately small and explicit.  It stores the source-shrink
`MapsTo` half for the selected smaller target box, the inverse half into that
same shrunken source, and audit fields saying the selected target box lies
inside an ambient target box and contains the target point.
-/
structure BoundaryChartSourceShrinkInverseTargetBoxData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M)
    (a b c d e f : Fin (n + 1) → Real) (u y : Fin n → Real)
    extends BoundaryChartSourceShrinkMapsToData I x0 x1 a b e f u where
  /-- Boundary convention for the selected target box. -/
  targetLowerCorner_zero : e 0 = 0
  /-- Coordinatewise ordering of the selected target box. -/
  targetLower_le_targetUpper : e ≤ f
  /-- The target point lies in the selected target box. -/
  targetPoint_mem : y ∈ lowerZeroFaceDomain e f
  /-- The selected target box is a shrink of the ambient target box. -/
  targetSubset_original : lowerZeroFaceDomain e f ⊆ lowerZeroFaceDomain c d
  /-- Local inverse data into the same shrunken source box. -/
  localInverse :
    boundaryChartLocalInverseData I x0 x1 sourceLowerCorner sourceUpperCorner e f

namespace BoundaryChartSourceShrinkInverseTargetBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {a b c d e f : Fin (n + 1) → Real} {u y : Fin n → Real}

/-- Constructor spelling with the remaining fields explicit. -/
def mkOfMapsToLocalInverse
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b e f u)
    (he0 : e 0 = 0) (hle : e ≤ f)
    (hy : y ∈ lowerZeroFaceDomain e f)
    (hsubset : lowerZeroFaceDomain e f ⊆ lowerZeroFaceDomain c d)
    (hlocal :
      boundaryChartLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner e f) :
    BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y where
  toBoundaryChartSourceShrinkMapsToData := D
  targetLowerCorner_zero := he0
  targetLower_le_targetUpper := hle
  targetPoint_mem := hy
  targetSubset_original := hsubset
  localInverse := hlocal

/-- Forget the audit fields to the existing source-shrink target-box data. -/
def toSourceShrinkTargetBoxData
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y) :
    BoundaryChartSourceShrinkTargetBoxData I x0 x1 a b e f u :=
  D.toBoundaryChartSourceShrinkMapsToData.toTargetBoxData
    D.targetLowerCorner_zero D.targetLower_le_targetUpper D.localInverse

/-- Package the selected target as the standard target-box selection. -/
def targetBoxSelection
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y) :
    BoundaryChartTargetBoxSelection I x0 x1 D.sourceLowerCorner D.sourceUpperCorner :=
  D.toSourceShrinkTargetBoxData.targetBoxSelection

/-- Full selected-box image data for the selected source and target boxes. -/
theorem imageData
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y) :
    boundaryChartSelectedBoxImageData I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner e f :=
  D.toSourceShrinkTargetBoxData.imageData

end BoundaryChartSourceShrinkInverseTargetBoxData

end ManifoldBoundary

end Stokes

end
