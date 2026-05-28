import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Stokes.BoundaryChart.TargetBoxSourceShrinkInverse

/-!
# Source-shrink target boxes from local homeomorphism / IFT data

This file is the IFT-facing constructor layer for the source-shrink route.

The earlier modules already contain the two halves:

* `BoundaryChartSourceShrinkMapsToData`: the shrunken source box maps into the
  selected target box.
* `BoundaryChartContinuousLocalInverseData`: a named continuous local inverse
  on the selected target box.

Here we add natural constructors that package those fields as
`BoundaryChartSourceShrinkInverseTargetBoxData`, and a minimal
`OpenPartialHomeomorph`-facing record for callers that have selected compatible
source and target boxes from local inverse / IFT data.
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

namespace BoundaryChartSourceShrinkMapsToData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {a b c d e f : Fin (n + 1) → Real} {u y : Fin n → Real}

/--
Upgrade source-shrink `MapsTo` data using the named continuous-local-inverse
API.

This is the direct bridge from the two already-selected local pieces to the
completed source-shrink inverse target-box record.  The continuity field is not
needed by the downstream image-data proof, but keeping the input in
`BoundaryChartContinuousLocalInverseData` form lets IFT/local-homeomorphism
callers reuse the same package.
-/
def toInverseTargetBoxDataOfContinuousLocalInverse
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b e f u)
    (he0 : e 0 = 0) (hle : e ≤ f)
    (hy : y ∈ lowerZeroFaceDomain e f)
    (hsubset : lowerZeroFaceDomain e f ⊆ lowerZeroFaceDomain c d)
    (G :
      BoundaryChartContinuousLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner e f y) :
    BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y :=
  BoundaryChartSourceShrinkInverseTargetBoxData.mkOfMapsToLocalInverse
    D he0 hle hy hsubset G.toLocalInverseData

/-- Image data produced by source-shrink maps-to data and a continuous local inverse. -/
theorem imageData_of_continuousLocalInverse
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b e f u)
    (he0 : e 0 = 0) (hle : e ≤ f)
    (hy : y ∈ lowerZeroFaceDomain e f)
    (hsubset : lowerZeroFaceDomain e f ⊆ lowerZeroFaceDomain c d)
    (G :
      BoundaryChartContinuousLocalInverseData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner e f y) :
    boundaryChartSelectedBoxImageData I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner e f :=
  (D.toInverseTargetBoxDataOfContinuousLocalInverse
    he0 hle hy hsubset G).imageData

end BoundaryChartSourceShrinkMapsToData

/--
Minimal synchronized source/target box data supplied by a local
homeomorphism/IFT construction.

The selected source box is already shrunk inside the original source box, and
the selected target box is already shrunk inside the ambient target box.  The
record keeps the exact fields needed downstream:

* a local homeomorphism whose inverse is used as the local right inverse,
* source-to-target `MapsTo` for the boundary chart transition,
* inverse `MapsTo` back into the same shrunken source box,
* equality of the local homeomorphism with the boundary chart transition on
  that source box.

The neighborhood fields are audit data for callers produced from IFT; the
image-data projection itself only needs the two maps-to fields and the right
inverse supplied by the local homeomorphism.
-/
structure BoundaryChartSourceShrinkOpenPartialHomeomorphData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b c d : Fin (n + 1) → Real) (u y : Fin n → Real) where
  /-- Lower corner of the selected shrunken source box. -/
  sourceLowerCorner : Fin (n + 1) → Real
  /-- Upper corner of the selected shrunken source box. -/
  sourceUpperCorner : Fin (n + 1) → Real
  /-- Lower corner of the selected shrunken target box. -/
  targetLowerCorner : Fin (n + 1) → Real
  /-- Upper corner of the selected shrunken target box. -/
  targetUpperCorner : Fin (n + 1) → Real
  /-- Boundary convention for the selected source box. -/
  sourceLowerCorner_zero : sourceLowerCorner 0 = 0
  /-- Coordinatewise ordering for the selected source box. -/
  sourceLower_le_sourceUpper : sourceLowerCorner ≤ sourceUpperCorner
  /-- Boundary convention for the selected target box. -/
  targetLowerCorner_zero : targetLowerCorner 0 = 0
  /-- Coordinatewise ordering for the selected target box. -/
  targetLower_le_targetUpper : targetLowerCorner ≤ targetUpperCorner
  /-- The source point remains in the selected source box. -/
  sourcePoint_mem : u ∈ lowerZeroFaceDomain sourceLowerCorner sourceUpperCorner
  /-- The target point lies in the selected target box. -/
  targetPoint_mem : y ∈ lowerZeroFaceDomain targetLowerCorner targetUpperCorner
  /-- The selected source box lies in the original source box. -/
  sourceSubset_original :
    lowerZeroFaceDomain sourceLowerCorner sourceUpperCorner ⊆ lowerZeroFaceDomain a b
  /-- The selected target box lies in the ambient target box. -/
  targetSubset_original :
    lowerZeroFaceDomain targetLowerCorner targetUpperCorner ⊆ lowerZeroFaceDomain c d
  /-- The selected source box is a neighborhood of the source point. -/
  source_mem_nhds :
    lowerZeroFaceDomain sourceLowerCorner sourceUpperCorner ∈ 𝓝 u
  /-- The selected target box is a neighborhood of the target point. -/
  target_mem_nhds :
    lowerZeroFaceDomain targetLowerCorner targetUpperCorner ∈ 𝓝 y
  /-- Local homeomorphism supplied by the local inverse / IFT step. -/
  localHomeomorph : OpenPartialHomeomorph (Fin n → Real) (Fin n → Real)
  /-- The selected source box lies in the source of the local homeomorphism. -/
  sourceBox_subset_localSource :
    lowerZeroFaceDomain sourceLowerCorner sourceUpperCorner ⊆ localHomeomorph.source
  /-- The selected target box lies in the target of the local homeomorphism. -/
  targetBox_subset_localTarget :
    lowerZeroFaceDomain targetLowerCorner targetUpperCorner ⊆ localHomeomorph.target
  /-- On the selected source box, the local homeomorphism is the chart transition. -/
  localHomeomorph_eq_transition :
    ∀ z ∈ lowerZeroFaceDomain sourceLowerCorner sourceUpperCorner,
      boundaryChartTransition I x0 x1 z = localHomeomorph z
  /-- The selected source box maps into the selected target box. -/
  mapsTo_target :
    MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain sourceLowerCorner sourceUpperCorner)
      (lowerZeroFaceDomain targetLowerCorner targetUpperCorner)
  /-- The local inverse maps the selected target box back into the selected source box. -/
  inverse_mapsTo_source :
    MapsTo localHomeomorph.symm
      (lowerZeroFaceDomain targetLowerCorner targetUpperCorner)
      (lowerZeroFaceDomain sourceLowerCorner sourceUpperCorner)

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {a b c d : Fin (n + 1) → Real} {u y : Fin n → Real}

/-- The local homeomorphism is continuous at the selected source point. -/
theorem continuousAt_localHomeomorph
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y) :
    ContinuousAt D.localHomeomorph u :=
  D.localHomeomorph.continuousAt
    (D.sourceBox_subset_localSource D.sourcePoint_mem)

/-- The inverse local homeomorphism is continuous at the selected target point. -/
theorem continuousAt_inverse
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y) :
    ContinuousAt D.localHomeomorph.symm y :=
  D.localHomeomorph.continuousAt_symm
    (D.targetBox_subset_localTarget D.targetPoint_mem)

/-- The maps-to half as the existing source-shrink record. -/
def toMapsToData
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y) :
    BoundaryChartSourceShrinkMapsToData I x0 x1 a b
      D.targetLowerCorner D.targetUpperCorner u where
  sourceLowerCorner := D.sourceLowerCorner
  sourceUpperCorner := D.sourceUpperCorner
  sourceLowerCorner_zero := D.sourceLowerCorner_zero
  sourceLower_le_sourceUpper := D.sourceLower_le_sourceUpper
  sourcePoint_mem := D.sourcePoint_mem
  sourceSubset_original := D.sourceSubset_original
  mapsTo_target := D.mapsTo_target

/-- The local homeomorphism inverse as the named continuous-local-inverse record. -/
def toContinuousLocalInverseData
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y) :
    BoundaryChartContinuousLocalInverseData I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner
      D.targetLowerCorner D.targetUpperCorner y where
  invFun := D.localHomeomorph.symm
  mapsTo_source := D.inverse_mapsTo_source
  right_inv := by
    intro z hz
    have hsrc :
        D.localHomeomorph.symm z ∈
          lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner :=
      D.inverse_mapsTo_source hz
    have htarget : z ∈ D.localHomeomorph.target :=
      D.targetBox_subset_localTarget hz
    calc
      boundaryChartTransition I x0 x1 (D.localHomeomorph.symm z)
          = D.localHomeomorph (D.localHomeomorph.symm z) :=
        D.localHomeomorph_eq_transition (D.localHomeomorph.symm z) hsrc
      _ = z := D.localHomeomorph.right_inv htarget
  continuousAt_invFun := D.continuousAt_inverse

/-- Forget the synchronized local-homeomorphism data to completed target-box data. -/
def toInverseTargetBoxData
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y) :
    BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d
      D.targetLowerCorner D.targetUpperCorner u y :=
  D.toMapsToData.toInverseTargetBoxDataOfContinuousLocalInverse
    D.targetLowerCorner_zero D.targetLower_le_targetUpper
    D.targetPoint_mem D.targetSubset_original D.toContinuousLocalInverseData

/-- Standard target-box selection obtained from synchronized local-homeomorphism data. -/
def targetBoxSelection
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y) :
    BoundaryChartTargetBoxSelection I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner :=
  D.toInverseTargetBoxData.targetBoxSelection

/-- Downstream selected-box image data obtained from synchronized local-homeomorphism data. -/
theorem imageData
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y) :
    boundaryChartSelectedBoxImageData I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner
      D.targetLowerCorner D.targetUpperCorner :=
  D.toInverseTargetBoxData.imageData

/-- Maps-to projection of the produced image data. -/
theorem imageData_mapsTo
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y) :
    MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner)
      (lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner) :=
  D.imageData.mapsTo

/-- Surjectivity projection of the produced image data. -/
theorem imageData_surjOn
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y) :
    SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner)
      (lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner) :=
  D.imageData.surjOn

end BoundaryChartSourceShrinkOpenPartialHomeomorphData

end ManifoldBoundary

end Stokes

end
