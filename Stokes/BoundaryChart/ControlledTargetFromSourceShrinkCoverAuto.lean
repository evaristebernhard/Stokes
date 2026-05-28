import Stokes.BoundaryChart.ControlledTargetNoContainmentAuto
import Stokes.BoundaryChart.SourceShrinkSelectedCOVFromShrinkAuto

/-!
# Controlled targets from source-shrink covers

This file is a small composition layer for the source-shrink route.  The lower
files already prove the real geometry:

* source-shrink local-homeomorphism data gives selected target boxes;
* ambient/later-target shrink data gives selected-image-box containment;
* local-openness or IFT cover data gives the source-image neighborhood.

The declarations below expose those ingredients directly as controlled target
selection constructors, so callers do not have to repeatedly materialize the
same target-box selections or restate the same tangent-bound callbacks.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section ManifoldBoundary

universe u w p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace BoundaryChartSourceShrinkInverseTargetBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {omega : ManifoldForm I M n}
variable {a b c d e f : Fin (n + 1) → Real} {u y : Fin n → Real}

/--
Completed source-shrink inverse-target data plus ambient later-target shrink
data produces a controlled target inside any chosen target-side neighborhood.

This is the local-openness controlled-target analogue of the selected-COV
wrappers in `SourceShrinkSelectedCOVFromShrinkAuto`.
-/
theorem exists_controlledTargetBoxSelectionOfAmbientShrink
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 omega
        D.sourceLowerCorner D.sourceUpperCorner)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d y)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 y)
    (himage :
      (boundaryChartTransition I x0 x1) ''
          lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner ∈ 𝓝 y) :
    ∃ c' d' : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 D.sourceLowerCorner D.sourceUpperCorner c' d' y U,
        C.laterLowerCorner = c' ∧ C.laterUpperCorner = d' :=
  (D.toSelectedImageBoxContainmentOfAmbientShrink hbox shrink).exists_controlledTargetBoxSelection_of_localOpenness
    hU himage

/--
Tangent-bound spelling of
`exists_controlledTargetBoxSelectionOfAmbientShrink` for completed
source-shrink inverse-target data.
-/
theorem exists_controlledTargetBoxSelectionOfAmbientTangentBounds
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 omega
        D.sourceLowerCorner D.sourceUpperCorner)
    (hlower :
      ∀ c' d' : Fin (n + 1) → Real, c' 0 = 0 → c' ≤ d' →
        y ∈ lowerZeroFaceDomain c' d' →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner c' d' →
            ∀ i : Fin n, c' i.succ ≤ c i.succ)
    (hupper :
      ∀ c' d' : Fin (n + 1) → Real, c' 0 = 0 → c' ≤ d' →
        y ∈ lowerZeroFaceDomain c' d' →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner c' d' →
            ∀ i : Fin n, d i.succ ≤ d' i.succ)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 y)
    (himage :
      (boundaryChartTransition I x0 x1) ''
          lowerZeroFaceDomain D.sourceLowerCorner D.sourceUpperCorner ∈ 𝓝 y) :
    ∃ c' d' : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 D.sourceLowerCorner D.sourceUpperCorner c' d' y U,
        C.laterLowerCorner = c' ∧ C.laterUpperCorner = d' :=
  (D.toSelectedImageBoxContainmentOfAmbientTangentBounds hbox hlower hupper).exists_controlledTargetBoxSelection_of_localOpenness
    hU himage

end BoundaryChartSourceShrinkInverseTargetBoxData

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {omega : ManifoldForm I M n}
variable {a b c d : Fin (n + 1) → Real} {u y : Fin n → Real}

/--
Open-partial-homeomorphism source-shrink data can be used as a controlled
target inside any target-side set containing its selected target box.
-/
theorem exists_controlledTargetBoxSelectionInSet
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    {U : Set (Fin n → Real)}
    (hsubset :
      lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ⊆ U) :
    ∃ e f : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 D.sourceLowerCorner D.sourceUpperCorner e f y U,
        C.laterLowerCorner = e ∧ C.laterUpperCorner = f := by
  refine ⟨D.targetLowerCorner, D.targetUpperCorner,
    D.toControlledTargetBoxSelectionSelf hsubset, ?_, ?_⟩
  · rfl
  · rfl

/--
Open-partial-homeomorphism source-shrink data plus ambient later-target shrink
data produces a controlled target in any prescribed neighborhood of the target
point.  The source-image neighborhood is derived from the source-shrink record.
-/
theorem exists_controlledTargetBoxSelectionOfAmbientShrink
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 omega
        D.sourceLowerCorner D.sourceUpperCorner)
    (shrink :
      BoundaryChartLaterTargetShrinkData I x0 x1
        D.sourceLowerCorner D.sourceUpperCorner c d y)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 y) :
    ∃ e f : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 D.sourceLowerCorner D.sourceUpperCorner e f y U,
        C.laterLowerCorner = e ∧ C.laterUpperCorner = f :=
  (D.toSelectedImageBoxContainmentOfAmbientShrink hbox shrink).exists_controlledTargetBoxSelection_of_localOpenness
    hU D.sourceImage_mem_nhds_targetPoint

/--
Tangent-bound spelling of
`exists_controlledTargetBoxSelectionOfAmbientShrink` for
open-partial-homeomorphism source-shrink data.
-/
theorem exists_controlledTargetBoxSelectionOfAmbientTangentBounds
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hbox :
      boundaryChartSelectedBox I x0 x1 omega
        D.sourceLowerCorner D.sourceUpperCorner)
    (hlower :
      ∀ c' d' : Fin (n + 1) → Real, c' 0 = 0 → c' ≤ d' →
        y ∈ lowerZeroFaceDomain c' d' →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner c' d' →
            ∀ i : Fin n, c' i.succ ≤ c i.succ)
    (hupper :
      ∀ c' d' : Fin (n + 1) → Real, c' 0 = 0 → c' ≤ d' →
        y ∈ lowerZeroFaceDomain c' d' →
          boundaryChartLocalInverseData I x0 x1
            D.sourceLowerCorner D.sourceUpperCorner c' d' →
            ∀ i : Fin n, d i.succ ≤ d' i.succ)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 y) :
    ∃ e f : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 D.sourceLowerCorner D.sourceUpperCorner e f y U,
        C.laterLowerCorner = e ∧ C.laterUpperCorner = f :=
  (D.toSelectedImageBoxContainmentOfAmbientTangentBounds hbox hlower hupper).exists_controlledTargetBoxSelection_of_localOpenness
    hU D.sourceImage_mem_nhds_targetPoint

end BoundaryChartSourceShrinkOpenPartialHomeomorphData

namespace BoundaryChartLocalOpennessTargetCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
One local-openness target-cover member gives a controlled target directly from
tangent bounds, without callers materializing `C.toTargetBoxSelection`.
-/
theorem exists_controlledTargetBoxSelectionOfTangentBounds
    (C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ C.activePieces)
    (hlower :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        C.targetPoint q ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1
            (C.sourceLowerCorner q) (C.sourceUpperCorner q) c d →
            ∀ i : Fin n, c i.succ ≤ C.targetLowerCorner q i.succ)
    (hupper :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        C.targetPoint q ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1
            (C.sourceLowerCorner q) (C.sourceUpperCorner q) c d →
            ∀ i : Fin n, C.targetUpperCorner q i.succ ≤ d i.succ)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ D : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 (C.sourceLowerCorner q) (C.sourceUpperCorner q)
            c d (C.targetPoint q) U,
        D.laterLowerCorner = c ∧ D.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_localOpenness_targetBoxTangentBounds
    (I := I) (x0 := x0) (x1 := x1)
    (a := C.sourceLowerCorner q) (b := C.sourceUpperCorner q)
    (y := C.targetPoint q) (U := U)
    (C.toTargetBoxSelection q hq) hlower hupper hU (C.image_mem_nhds q hq)

end BoundaryChartLocalOpennessTargetCover

namespace BoundaryChartLocalOpennessTargetCoverLaterShrinkData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}
variable {C : BoundaryChartLocalOpennessTargetCover I x0 x1 a b Piece}

/--
Cover-level later-target shrink data gives the active local-openness
controlled target without exposing the per-piece shrink projection.
-/
theorem exists_controlledTargetBoxSelection
    (S : BoundaryChartLocalOpennessTargetCoverLaterShrinkData C)
    (q : Piece) (hq : q ∈ C.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (C.targetPoint q)) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ D : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 (C.sourceLowerCorner q) (C.sourceUpperCorner q)
            c d (C.targetPoint q) U,
        D.laterLowerCorner = c ∧ D.laterUpperCorner = d :=
  C.exists_controlledTargetBoxSelectionOfShrink
    q hq (S.laterTargetShrink q hq) hU

end BoundaryChartLocalOpennessTargetCoverLaterShrinkData

namespace BoundaryChartIFTTargetCoverData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
One IFT target-cover member gives a controlled target directly from tangent
bounds, reusing the IFT fields stored in the cover.
-/
theorem exists_controlledTargetBoxSelectionOfTangentBounds
    (D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces)
    (hlower :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        D.targetPoint q ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1
            (D.sourceLowerCorner q) (D.sourceUpperCorner q) c d →
            ∀ i : Fin n, c i.succ ≤ D.targetLowerCorner q i.succ)
    (hupper :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        D.targetPoint q ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1
            (D.sourceLowerCorner q) (D.sourceUpperCorner q) c d →
            ∀ i : Fin n, D.targetUpperCorner q i.succ ≤ d i.succ)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 (D.sourceLowerCorner q) (D.sourceUpperCorner q)
            c d (D.targetPoint q) U,
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d := by
  simpa [BoundaryChartIFTTargetCoverData.targetPoint] using
    exists_controlledTargetBoxSelection_of_IFT_targetBoxTangentBounds
      (I := I) (x0 := x0) (x1 := x1)
      (a := D.sourceLowerCorner q) (b := D.sourceUpperCorner q)
      (u := D.sourcePoint q) (U := U)
      (D.toTargetBoxSelection q hq) hU
      (D.source_mem_nhds q hq)
      (D.hasStrictFDerivAt q hq)
      (D.tangentMap_surjective q hq)
      hlower hupper

end BoundaryChartIFTTargetCoverData

namespace BoundaryChartIFTTargetCoverLaterShrinkData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}
variable {D : BoundaryChartIFTTargetCoverData I x0 x1 a b Piece}

/--
Cover-level later-target shrink data gives the active IFT controlled target
without exposing the per-piece shrink projection.
-/
theorem exists_controlledTargetBoxSelectionOfShrinkPackage
    (S : BoundaryChartIFTTargetCoverLaterShrinkData D)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 (D.sourceLowerCorner q) (D.sourceUpperCorner q)
            c d (D.targetPoint q) U,
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d :=
  S.exists_controlledTargetBoxSelection q hq hU

end BoundaryChartIFTTargetCoverLaterShrinkData

end ManifoldBoundary

end Stokes

end
