import Stokes.BoundaryChart.TransitionCompactBox

/-!
# Boundary chart compact-image covers

This file upgrades the single-source-box compact-image bookkeeping in
`TransitionCompactBox` to a finite family of compact source boxes.  The
geometry that chooses the family is intentionally kept as fields: later layers
can prove those fields from compactness, local openness, or a chart-specific
construction without forcing this pure boundary-chart module to import global
partition data.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section ManifoldBoundary

universe u w p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
A finite family of lower-zero source boxes covering one larger lower-zero
source box.

The source boxes are lower-zero boxes in boundary coordinates.  Each member is
compact because `lowerZeroFaceDomain` is compact; this structure records only
the finite cover and the corner conventions needed downstream.
-/
structure BoundaryChartCompactSourceBoxCover {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b : Fin (n + 1) → Real) (Piece : Type p) where
  /-- Finite family labels used by the cover. -/
  activePieces : Finset Piece
  /-- Lower corner of each source sub-box. -/
  sourceLowerCorner : Piece → Fin (n + 1) → Real
  /-- Upper corner of each source sub-box. -/
  sourceUpperCorner : Piece → Fin (n + 1) → Real
  /-- Each active source lower corner lies on the lower zero face. -/
  sourceLowerCorner_zero :
    ∀ q, q ∈ activePieces → sourceLowerCorner q 0 = 0
  /-- Each active source box has ordered corners. -/
  sourceLower_le_sourceUpper :
    ∀ q, q ∈ activePieces → sourceLowerCorner q ≤ sourceUpperCorner q
  /-- The original source lower-zero box is covered by the active source sub-boxes. -/
  sourceCover :
    lowerZeroFaceDomain a b ⊆
      ⋃ q : {q // q ∈ activePieces},
        lowerZeroFaceDomain (sourceLowerCorner q.1) (sourceUpperCorner q.1)

namespace BoundaryChartCompactSourceBoxCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/-- Constructor spelling with all geometric cover fields explicit. -/
def of
    (activePieces : Finset Piece)
    (sourceLowerCorner sourceUpperCorner : Piece → Fin (n + 1) → Real)
    (sourceLowerCorner_zero :
      ∀ q, q ∈ activePieces → sourceLowerCorner q 0 = 0)
    (sourceLower_le_sourceUpper :
      ∀ q, q ∈ activePieces → sourceLowerCorner q ≤ sourceUpperCorner q)
    (sourceCover :
      lowerZeroFaceDomain a b ⊆
        ⋃ q : {q // q ∈ activePieces},
          lowerZeroFaceDomain (sourceLowerCorner q.1) (sourceUpperCorner q.1)) :
    BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece where
  activePieces := activePieces
  sourceLowerCorner := sourceLowerCorner
  sourceUpperCorner := sourceUpperCorner
  sourceLowerCorner_zero := sourceLowerCorner_zero
  sourceLower_le_sourceUpper := sourceLower_le_sourceUpper
  sourceCover := sourceCover

/-- The source lower-zero domain of one family member. -/
def sourceDomain
    (C : BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece) (q : Piece) :
    Set (Fin n → Real) :=
  lowerZeroFaceDomain (C.sourceLowerCorner q) (C.sourceUpperCorner q)

/-- Active source family members are compact. -/
theorem isCompact_sourceDomain
    (C : BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece)
    (q : Piece) :
    IsCompact (C.sourceDomain q) := by
  exact isCompact_lowerZeroFaceDomain (C.sourceLowerCorner q) (C.sourceUpperCorner q)

/-- Every point of the original source box lies in some active source sub-box. -/
theorem exists_active_sourceDomain_mem
    (C : BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece)
    {u : Fin n → Real} (hu : u ∈ lowerZeroFaceDomain a b) :
    ∃ q : Piece, ∃ _ : q ∈ C.activePieces, u ∈ C.sourceDomain q := by
  rcases Set.mem_iUnion.mp (C.sourceCover hu) with ⟨q, hqmem⟩
  exact ⟨q.1, q.2, hqmem⟩

end BoundaryChartCompactSourceBoxCover

/--
A finite compact-image cover for boundary chart transitions.

Each active source sub-box maps into its corresponding target lower-zero box,
and each target box has local right-inverse data back into that same source
sub-box.  The optional `targetPoint` field records the point around which a
local inverse was selected; it is useful when this family is produced from the
single-point predicate `boundaryChartCompactImageForLocalInverseTargets`.
-/
structure BoundaryChartCompactImageCover {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b : Fin (n + 1) → Real) (Piece : Type p)
    extends BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece where
  /-- The point in the target image around which the active target box was selected. -/
  targetPoint : Piece → Fin n → Real
  /-- Lower corner of each target lower-zero box. -/
  targetLowerCorner : Piece → Fin (n + 1) → Real
  /-- Upper corner of each target lower-zero box. -/
  targetUpperCorner : Piece → Fin (n + 1) → Real
  /-- Each active target lower corner lies on the lower zero face. -/
  targetLowerCorner_zero :
    ∀ q, q ∈ activePieces → targetLowerCorner q 0 = 0
  /-- Each active target box has ordered corners. -/
  targetLower_le_targetUpper :
    ∀ q, q ∈ activePieces → targetLowerCorner q ≤ targetUpperCorner q
  /-- The selected target point lies in its active target box. -/
  targetPoint_mem :
    ∀ q, q ∈ activePieces →
      targetPoint q ∈ lowerZeroFaceDomain (targetLowerCorner q) (targetUpperCorner q)
  /-- The active source sub-box image lands in its selected target box. -/
  compactImage :
    ∀ q, q ∈ activePieces →
      boundaryChartCompactImageBoxSelection I x0 x1
        (sourceLowerCorner q) (sourceUpperCorner q)
        (targetLowerCorner q) (targetUpperCorner q)
  /-- The selected target box has a local right inverse into the same source sub-box. -/
  localInverse :
    ∀ q, q ∈ activePieces →
      boundaryChartLocalInverseData I x0 x1
        (sourceLowerCorner q) (sourceUpperCorner q)
        (targetLowerCorner q) (targetUpperCorner q)

namespace BoundaryChartCompactImageCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
Constructor from an explicit compact source-box cover and per-piece target
image/local-inverse data.
-/
def mkOfCompactImageLocalInverseData
    (sourceCover : BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece)
    (targetPoint : Piece → Fin n → Real)
    (targetLowerCorner targetUpperCorner : Piece → Fin (n + 1) → Real)
    (targetLowerCorner_zero :
      ∀ q, q ∈ sourceCover.activePieces → targetLowerCorner q 0 = 0)
    (targetLower_le_targetUpper :
      ∀ q, q ∈ sourceCover.activePieces → targetLowerCorner q ≤ targetUpperCorner q)
    (targetPoint_mem :
      ∀ q, q ∈ sourceCover.activePieces →
        targetPoint q ∈ lowerZeroFaceDomain (targetLowerCorner q) (targetUpperCorner q))
    (compactImage :
      ∀ q, q ∈ sourceCover.activePieces →
        boundaryChartCompactImageBoxSelection I x0 x1
          (sourceCover.sourceLowerCorner q) (sourceCover.sourceUpperCorner q)
          (targetLowerCorner q) (targetUpperCorner q))
    (localInverse :
      ∀ q, q ∈ sourceCover.activePieces →
        boundaryChartLocalInverseData I x0 x1
          (sourceCover.sourceLowerCorner q) (sourceCover.sourceUpperCorner q)
          (targetLowerCorner q) (targetUpperCorner q)) :
    BoundaryChartCompactImageCover I x0 x1 a b Piece where
  toBoundaryChartCompactSourceBoxCover := sourceCover
  targetPoint := targetPoint
  targetLowerCorner := targetLowerCorner
  targetUpperCorner := targetUpperCorner
  targetLowerCorner_zero := targetLowerCorner_zero
  targetLower_le_targetUpper := targetLower_le_targetUpper
  targetPoint_mem := targetPoint_mem
  compactImage := compactImage
  localInverse := localInverse

/-- The source lower-zero domain of one family member. -/
def sourceDomain
    (C : BoundaryChartCompactImageCover I x0 x1 a b Piece) (q : Piece) :
    Set (Fin n → Real) :=
  lowerZeroFaceDomain (C.sourceLowerCorner q) (C.sourceUpperCorner q)

/-- The target lower-zero domain of one family member. -/
def targetDomain
    (C : BoundaryChartCompactImageCover I x0 x1 a b Piece) (q : Piece) :
    Set (Fin n → Real) :=
  lowerZeroFaceDomain (C.targetLowerCorner q) (C.targetUpperCorner q)

/-- Active source family members are compact. -/
theorem isCompact_sourceDomain
    (C : BoundaryChartCompactImageCover I x0 x1 a b Piece)
    (q : Piece) :
    IsCompact (C.sourceDomain q) := by
  exact isCompact_lowerZeroFaceDomain (C.sourceLowerCorner q) (C.sourceUpperCorner q)

/-- Every point of the original source box lies in some active source sub-box. -/
theorem exists_active_sourceDomain_mem
    (C : BoundaryChartCompactImageCover I x0 x1 a b Piece)
    {u : Fin n → Real} (hu : u ∈ lowerZeroFaceDomain a b) :
    ∃ q : Piece, ∃ _ : q ∈ C.activePieces, u ∈ C.sourceDomain q := by
  rcases Set.mem_iUnion.mp (C.sourceCover hu) with ⟨q, hqmem⟩
  exact ⟨q.1, q.2, hqmem⟩

/--
Each active compact-image cover member gives the existing single-box transition
compact-box package.
-/
def transitionCompactBoxData
    (C : BoundaryChartCompactImageCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    BoundaryChartTransitionCompactBoxData I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) :=
  BoundaryChartTransitionCompactBoxData.mkOfCompactImageLocalInverseData
    (C.targetLowerCorner q) (C.targetUpperCorner q)
    (C.targetLowerCorner_zero q hq) (C.targetLower_le_targetUpper q hq)
    (C.compactImage q hq) (C.localInverse q hq)

/-- Image-data projection for one active cover member. -/
theorem imageData
    (C : BoundaryChartCompactImageCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    boundaryChartSelectedBoxImageData I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)
      (C.targetLowerCorner q) (C.targetUpperCorner q) :=
  (C.transitionCompactBoxData q hq).imageData

/-- Map-to projection for one active cover member. -/
theorem mapsTo
    (C : BoundaryChartCompactImageCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    MapsTo (boundaryChartTransition I x0 x1)
      (C.sourceDomain q) (C.targetDomain q) := by
  exact (C.compactImage q hq).mapsTo

/-- Surjectivity projection for one active cover member. -/
theorem surjOn
    (C : BoundaryChartCompactImageCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    SurjOn (boundaryChartTransition I x0 x1)
      (C.sourceDomain q) (C.targetDomain q) := by
  exact (C.localInverse q hq).surjOn

/--
The old single-point compact-image hypothesis can be applied piecewise to
build the compact-image field required by an active family member.
-/
theorem compactImage_of_forLocalInverseTargets
    (C : BoundaryChartCompactImageCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces)
    (hcompact :
      boundaryChartCompactImageForLocalInverseTargets I x0 x1
        (C.sourceLowerCorner q) (C.sourceUpperCorner q) (C.targetPoint q)) :
    boundaryChartCompactImageBoxSelection I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)
      (C.targetLowerCorner q) (C.targetUpperCorner q) :=
  hcompact (C.targetLowerCorner q) (C.targetUpperCorner q)
    (C.targetLowerCorner_zero q hq) (C.targetLower_le_targetUpper q hq)
    (C.targetPoint_mem q hq) (C.localInverse q hq)

end BoundaryChartCompactImageCover

/--
Fieldized geometric input for producing a compact-image cover from local
inverse target boxes.

The fields `targetPoint_mem` and `localInverse` are the local-openness/IFT
output for each active source sub-box.  The field
`compactImageForLocalInverseTargets` is exactly the old single-point compact
image condition, but indexed over the finite compact source cover.
-/
structure BoundaryChartCompactImageForLocalInverseTargetCover {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b : Fin (n + 1) → Real) (Piece : Type p)
    extends BoundaryChartCompactSourceBoxCover I x0 x1 a b Piece where
  /-- Point in the target image around which the local inverse target is selected. -/
  targetPoint : Piece → Fin n → Real
  /-- Lower corner of the selected local-inverse target box. -/
  targetLowerCorner : Piece → Fin (n + 1) → Real
  /-- Upper corner of the selected local-inverse target box. -/
  targetUpperCorner : Piece → Fin (n + 1) → Real
  /-- Lower-zero convention for the selected local-inverse target box. -/
  targetLowerCorner_zero :
    ∀ q, q ∈ activePieces → targetLowerCorner q 0 = 0
  /-- Ordered target corners for the selected local-inverse target box. -/
  targetLower_le_targetUpper :
    ∀ q, q ∈ activePieces → targetLowerCorner q ≤ targetUpperCorner q
  /-- The selected target point lies in its local-inverse target box. -/
  targetPoint_mem :
    ∀ q, q ∈ activePieces →
      targetPoint q ∈ lowerZeroFaceDomain (targetLowerCorner q) (targetUpperCorner q)
  /-- Local right-inverse data for the active source sub-box and target box. -/
  localInverse :
    ∀ q, q ∈ activePieces →
      boundaryChartLocalInverseData I x0 x1
        (sourceLowerCorner q) (sourceUpperCorner q)
        (targetLowerCorner q) (targetUpperCorner q)
  /-- Compact-image control for whichever active local-inverse target box is selected. -/
  compactImageForLocalInverseTargets :
    ∀ q, q ∈ activePieces →
      boundaryChartCompactImageForLocalInverseTargets I x0 x1
        (sourceLowerCorner q) (sourceUpperCorner q) (targetPoint q)

namespace BoundaryChartCompactImageForLocalInverseTargetCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
Materialize the compact-image cover by applying the old single-point predicate
on each active member of the compact source-box cover.
-/
def toCompactImageCover
    (C : BoundaryChartCompactImageForLocalInverseTargetCover I x0 x1 a b Piece) :
    BoundaryChartCompactImageCover I x0 x1 a b Piece where
  toBoundaryChartCompactSourceBoxCover := C.toBoundaryChartCompactSourceBoxCover
  targetPoint := C.targetPoint
  targetLowerCorner := C.targetLowerCorner
  targetUpperCorner := C.targetUpperCorner
  targetLowerCorner_zero := C.targetLowerCorner_zero
  targetLower_le_targetUpper := C.targetLower_le_targetUpper
  targetPoint_mem := C.targetPoint_mem
  compactImage := fun q hq =>
    C.compactImageForLocalInverseTargets q hq
      (C.targetLowerCorner q) (C.targetUpperCorner q)
      (C.targetLowerCorner_zero q hq) (C.targetLower_le_targetUpper q hq)
      (C.targetPoint_mem q hq) (C.localInverse q hq)
  localInverse := C.localInverse

/-- Constructor to the existing transition compact-box package for one active piece. -/
def transitionCompactBoxData
    (C : BoundaryChartCompactImageForLocalInverseTargetCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    BoundaryChartTransitionCompactBoxData I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) :=
  (C.toCompactImageCover).transitionCompactBoxData q hq

/-- Image-data projection for one active piece after materializing compact image control. -/
theorem imageData
    (C : BoundaryChartCompactImageForLocalInverseTargetCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces) :
    boundaryChartSelectedBoxImageData I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q)
      (C.targetLowerCorner q) (C.targetUpperCorner q) :=
  (C.transitionCompactBoxData q hq).imageData

end BoundaryChartCompactImageForLocalInverseTargetCover

end ManifoldBoundary

end Stokes

end
